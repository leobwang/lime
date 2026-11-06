//! The clock verbs of tm-spec-v1.md §9: `wake`, `arrive`, `start`, `done`,
//! `extend`, `stop`, `break`, `interrupt`, `resume`, `pause`, `energy`,
//! `idle`.
//!
//! # API overview
//!
//! One keystroke changes one fact (§9): each verb makes the byte-faithful
//! line edit §4.1 allows, updates the matching `state.json` field (§10.2) and
//! appends the matching §10.1 event — in that order, all inside a
//! [`super::undo::Recorder`] so `tm undo` can put every part of it back.
//!
//! * [`wake`] — `wake{slept_min,onset_min}`, stamped at the wake time; starts
//!   a new day in `state.json`.
//! * [`arrive`] — §8.1's window and budget (calendar sync first when
//!   `sync_on_arrive`), `arrive{loc,window,budget}`, then a replan; the block
//!   starts are kept in `.tm/arrival_plan.json` for §12.1's ghost row.
//! * [`start`] / [`done`] / [`extend`] / [`stop`] — the block machine; the
//!   energy report is `--energy N`, or asked on a terminal.
//! * [`take_break`] — starts a break, or ends the running one and logs it
//!   with its actual length (so does the next `start`, `done` or `stop`).
//! * [`interrupt`] / [`resume`] / [`pause`] / [`energy`] / [`idle`] — §9's
//!   remaining rows. A non-zero energy δ replans (§8.5).
//!
//! Every one of them also writes §4.3's human trace: one `HH:MM …` line in
//! the day file's `## Log`, and — for `wake` and `arrive` — the runtime front
//! matter (see [`super::dayfile`]).

use std::collections::BTreeSet;
use std::io::{self, BufRead, IsTerminal, Write};

use chrono::{DateTime, FixedOffset};
use serde::Serialize;

use tm_core::energy::{self, Features};
use tm_core::horizon::MIN_REMAINING_MIN;
use tm_core::log::{self, Event, HeldBreak};
use tm_core::model::{parse_time, Dur, Horizon, Id, Recur, State};
use tm_core::recur;
use tm_core::store::{ActiveBlock, BreakState, InterruptState, Store};

use super::ctx::{Ctx, Globals, ARRIVAL_PLAN_PATH};
use super::out::{emit, fmt_time, CliError};
use super::planning;
use super::undo::Recorder;

/// `HH:MM` — `tm_core::dayplan::fmt_clock` under this file's own name (AGENTS
/// §5.3, W-23: a byte-for-byte copy of it stood here).
use tm_core::dayplan::fmt_clock as hhmm;

/// The unit a tool-written `est:` uses: whole blocks when the minutes divide
/// evenly (§9's "est: += 1b"), else the compact `Nm`/`Nh`/`NhMm` form. Mirrors
/// the private `est_dur` of `horizon.rs`, so a `tm stop` and a day close write
/// the same text.
fn est_dur(minutes: u32, block_min: u32) -> Dur {
    if block_min > 0 && minutes > 0 && minutes.is_multiple_of(block_min) {
        Dur::blocks(minutes / block_min, block_min)
    } else {
        Dur::canonical(minutes)
    }
}

/// **The running block's estimate, written by the kernel's `est` op** — the
/// owner's **D62** (README gaps 2926 and 2928), parity **P54**.
///
/// `tm extend`, `tm stop` and `tm done --partial` used to write
/// `line.set_token("est", …)` themselves: an `est:` token BESIDE a leading
/// estimate, so `- [>] 2 30m Insurance claim … ^a1` became `… 30m … est:1b
/// ^a1` — two estimates on one line, the row printing one and the planner
/// reading the other, which is D56's founding bug on three more verbs. D56's
/// one-estimate rule reaches them now through the ONE path `tm edit est=`
/// takes: the kernel's `est` op (`Boundary.estAsWritten`, written by
/// `Field.setRemaining`), carrying the value AS TYPED — the verb's own spelling,
/// [`est_dur`] (whole blocks when they divide, else the compact form) — and the
/// block length its `b` means. So a leading estimate that is the slot is
/// rewritten in place (`30m` → `1b`) and gains no token; a line whose slot is an
/// `est:` token, or that carries no estimate, gets the token in canonical
/// minutes, D49's settled rendering — the bytes `tm edit est=` writes there.
///
/// A value past the host's `u32` is not spelled by [`est_dur`] (it cannot hold
/// it): it is sent in minutes and the kernel refuses it by name (`badValue
/// est`, gap 2929) — the one reader decides, and nothing has been written yet.
///
/// Returns the line as the kernel wrote it, parsed, so a verb that also moves
/// the box (`stop`, `done --partial`) edits the kernel's bytes and never a
/// stale copy — writing the pre-edit line back over them would undo the
/// estimate, so an answer without the line is an error, not a fallback. The box
/// is §4.1 positional surgery the wire does not carry, and it is the only part
/// of those lines the host still writes.
fn write_estimate(
    ctx: &Ctx,
    verb: &str,
    id: &Id,
    minutes: u64,
) -> Result<tm_core::grammar::ItemLine, CliError> {
    let block_min = ctx.block_min();
    let value = match u32::try_from(minutes) {
        Ok(m) => est_dur(m, block_min).to_string(),
        Err(_) => format!("{minutes}m"),
    };
    let applied = super::kernel_bridge::apply(
        ctx,
        verb,
        &[super::kernel_bridge::Cmd::Est {
            id: id.to_string(),
            value,
            block_min,
        }],
    )?;
    applied
        .line_of(id.as_str())
        .and_then(|(_, text)| tm_core::grammar::ItemLine::parse(&text).ok())
        .ok_or_else(|| {
            CliError::msg(format!(
                "the kernel wrote {}'s estimate but its answer carries no such line",
                id.token()
            ))
        })
}

/// Parse a duration argument (`20m`, `1b`, `1h30m`).
fn dur(arg: &str, block_min: u32) -> Result<Dur, CliError> {
    Ok(Dur::parse(arg, block_min)?)
}

/// Ask for an energy report on a terminal; `None` when stdin is not one.
fn ask_energy(pred: u8) -> Option<u8> {
    if !io::stdin().is_terminal() {
        return None;
    }
    print!("energy 0-5 (predicted {pred}, Enter to skip): ");
    let _ = io::stdout().flush();
    let mut line = String::new();
    io::stdin().lock().read_line(&mut line).ok()?;
    line.trim().parse::<u8>().ok().filter(|v| *v <= 5)
}

/// Minutes of working time since the last break *ended* (§8.5's
/// `since_break` feature, §10.1's `start{since_break_min}`).
///
/// `break.t` is when the break *began* — the entry is appended when it ends,
/// with `actual_min` set (log.rs's convention) — so the end is `t +
/// actual_min`. With no break yet today the gap is measured from the day's
/// first `start` instead: zero would read as "a break has just ended" after
/// five hours of unbroken work.
fn since_break_min(ctx: &Ctx) -> u32 {
    let since = ctx.replay.seam(ctx.today).and_then(|s| s.since_break);
    // A break that is still running (started, not yet ended) is itself the
    // most recent boundary: nothing has been worked since it began — at the
    // ONE reading of its start (`Ctx::running_break`, P73: the evening's after
    // midnight, never tonight's).
    if let Some(began) = ctx.running_break() {
        return (ctx.now_tz - began).num_minutes().clamp(0, 24 * 60) as u32;
    }
    match since {
        Some(t) => (ctx.now - t).num_minutes().clamp(0, 24 * 60) as u32,
        None => 0,
    }
}

/// "no such item", the error every id argument shares.
fn missing(id: &Id) -> CliError {
    CliError::NotFound(id.clone())
}

/// Append one line to the day file's `## Log` at `now` (§4.3) — the human
/// half of the §10.1 event the verb has just written.
fn day_note(ctx: &Ctx, text: impl Into<String>) -> Result<(), CliError> {
    super::dayfile::note(ctx, ctx.today, ctx.now_tz.time(), &text.into())
}

/// True for a line that carries no state and is never rewritten: §4.3's
/// `routines.md` and `optional.md`, whose occurrences live in the log as
/// §10.1 `routine`/`skip` events. Writing `[x]` into one would end the
/// recurrence for good (§5.1: "a recurring item never changes its line").
pub(super) fn is_stateless(item: &tm_core::model::Item) -> bool {
    matches!(item.horizon, Horizon::Routine | Horizon::Optional)
}

/// The instance key of a stateless line at `at`, for §10.1's
/// `routine{inst}`: `now`'s instance, or — for a block a `tm done --at` ends
/// earlier (D79) — the instance of the day it ended on.
fn instance_key(ctx: &Ctx, item: &tm_core::model::Item, at: DateTime<chrono_tz::Tz>) -> String {
    recur::today_instances([item], at.date_naive(), at.naive_local(), &ctx.replay, &ctx.cfg)
        .first()
        .map(|(i, _)| i.key.to_string())
        .unwrap_or_else(|| at.date_naive().to_string())
}

/// The features of the instant `at` (§8.5): `now` for `tm start`, the instant
/// `tm energy --at` names otherwise. Hours since wake count from the wake that
/// had happened by `at` ([`Ctx::woke_before`], P79), and the night slept and
/// the blocks done are `at`'s day's — today's, except for a report the owner's
/// D86 dates yesterday (README gap 4260, parity P82), which reads yesterday's.
fn features(ctx: &Ctx, at: DateTime<chrono_tz::Tz>) -> Features {
    let day = at.date_naive();
    Features::at(at, ctx.woke_before(at), ctx.loc())
        .with_slept(ctx.slept_on(day))
        .with_progress(ctx.replay.blocks_done(day), since_break_min(ctx))
}

/// End the running break NOW, appending its §10.1 `break` event with the
/// actual length and un-pausing the block the break paused (§10.2's
/// `active.paused`) — and only that block: one a `tm pause` held before the
/// break stays paused (P84). Returns the minutes it lasted.
fn end_break(ctx: &mut Ctx) -> Result<Option<u32>, CliError> {
    let now = ctx.now_tz;
    end_break_at(ctx, now)
}

/// [`end_break`] at `end` — `now`, or the end a `tm stop --at`/`tm done --at`
/// states for the block (D79: the stop is at `end` in every respect, so a
/// break running then is over then too). The break began at the ONE reading
/// of its start (`Ctx::running_break`) — since the owner's **D105** (parity
/// P100) the instant its `break_start` was logged at, so the `break` line this
/// writes is stamped at exactly that instant and the replay pairs the two;
/// for a break a binary before D105 began, the cache's clock read as P73 reads
/// it — the evening's after midnight, where fork 4748911 read the cache's
/// clock on today's date and logged a break begun before midnight TONIGHT with
/// `actual_min: 0` (README gap 3820); a break with no `started` began at `end`.
/// **Every verb that ends a break ends it here** (D97's class: `tm break`,
/// `tm start`, `tm stop`, `tm done`, `tm interrupt`, `tm resume`), so the line
/// that ends the running break has one writer.
///
/// **A break that BEGAN after `end` is not ended by it** (W-51 repair track H, the W-50 repair
/// critic's first finding): an end stated before `now` can precede the break's start — a `tm
/// stop --at`, or the stop §6.3's close writes at a block's last logged activity (the owner's D130)
/// — and so can `now` itself: any verb that ends a break (`tm start`, `tm interrupt`, `tm done`, `tm
/// resume`, `tm stop`) run with a `--now` before a logged running break's start skips ending it,
/// which agrees with D129's reading of a running break as ending at the first `start` stamped after
/// it (the W-51 repair's correction, README gap 5613: this paragraph named only the first two). A
/// break the cache alone holds (begun by a binary before D105) is placed by D81 at the
/// latest instant at or before `now` with its clock, which can fall days after that stop. Ending it
/// there wrote a `break` line stamped AFTER the stop that ended it, with `actual_min: 0`, and the
/// break was never logged as D133 says. The break runs on, and the verb's housekeeping logs it
/// (D133) or the next verb that ends it at an instant after its start ends it.
fn end_break_at(ctx: &mut Ctx, end: DateTime<chrono_tz::Tz>) -> Result<Option<u32>, CliError> {
    let start_dt = ctx.running_break().unwrap_or(end);
    if start_dt > end {
        return Ok(None);
    }
    let Some(br) = ctx.state.break_.take() else {
        return Ok(None);
    };
    let actual = (end - start_dt).num_minutes().max(0) as u32;
    // The break paused the block (§9); ending it un-pauses — unless an
    // interruption is also running and owns the pause, or a typed `tm pause`
    // held the block before the break began. The log holds no line for the
    // running break, so its reading of the timer IS the one before the break
    // (`ctx::logged_pause`, the derivation D42 rebuilds the cache by), and a
    // break leaves it as it found it: the owner's D87, parity P84, README gaps
    // 4243 and 4332. Fork 4748911 un-paused unconditionally, so the next `tm
    // pause` logged a second `pause` the replay read as nothing — the block
    // running to the cache and to `tm stop`, held to the replay's credit.
    let held = ctx.state.active.as_ref().and_then(|a| {
        ctx.replay
            .open_block
            .as_ref()
            .filter(|b| b.id == a.id.as_str())
            .map(|b| super::ctx::logged_pause(&ctx.replay, b))
    });
    if ctx.state.interrupt.is_none() {
        if let Some(a) = ctx.state.active.as_mut() {
            a.paused = held.unwrap_or(false);
        }
    }
    let entry = log::LogEntry::new(
        start_dt.fixed_offset(),
        Event::Break {
            planned_min: br.planned_min,
            actual_min: Some(actual),
            r#where: br.place.clone(),
        },
    );
    ctx.append_entry(&entry)?;
    // **The owner's D114** (README gap 5014, stage 6 W-48 track K, parity
    // P115): a calendar wall that ended while this break ran had its `unpause`
    // held — a break running since before a wall's end holds the block
    // (`WallTimer.breakHolds`), so a block is never working and on break at
    // once — and the break's end is when it is written, by whichever verb
    // ends the break, as of the end it ends at. With the break's line logged
    // and none running, the kernel's wall rule answers that unpause
    // (`WallTimer.writes`); with no wall ended inside the break it answers
    // nothing.
    if ctx.state.active.is_some() && stop_the_timer_at_walls(ctx, end)? {
        ctx.reload()?;
    }
    Ok(Some(actual))
}

/// The break `.tm/state.json` holds running, as the instant it began — the ONE
/// reading, `Ctx::running_break` (the latest instant at or before `now` with
/// the cached clock: the campaign's D81 call on README gap 3820, parity P73),
/// with its offset, for the readers that take one: the worked minutes, D61's
/// walls request, the week cut's and `tm pause`'s. Until W-41 it was the clock
/// on TODAY's date, so after local midnight a break begun before it began in
/// the future and none of it was netted out of the block.
fn running_break_at(ctx: &Ctx) -> Option<DateTime<FixedOffset>> {
    ctx.running_break().map(|t| t.fixed_offset())
}

/// **Minutes actually worked on the running block, as a verb LOGS them** — the
/// one host reading, [`log::Replay::running_worked_min`] (README gap 2920,
/// W-35 repair): the wall clock since the block's start net of its pauses,
/// interruptions and breaks, the break `state.json` still holds running
/// included. `tm done` (and `--partial`) and `tm stop` call this; `tm now`'s
/// header and the TUI's timer show the same rule ([`shown_worked_min`],
/// [`log::Replay::shown_worked_min`]), so no surface keeps a reading of its
/// own.
///
/// **The start is the log's** — the owner's **D75** (README gap 3715, parity
/// **P65**): the instant of the open block's own `start` line, never
/// `.tm/state.json`'s `active.started`. That field is a bare `HH:MM`, and fork
/// 4748911 (and this function until W-40, through `ctx.at(a.started)` at its
/// three callers) put it on TODAY's date: after local midnight the start was
/// tonight's, in the future, so `tm done` logged `actual_min: 0` for a block
/// worked across midnight and `tm now` read `0m` (gap 3625). This function
/// takes no start any more, so the cache's clock cannot be handed to it.
///
/// `None` with nothing running, and — unreachable after D42's reconcile, which
/// makes `.tm/state.json`'s running block the log's — when the log holds no
/// open block for it; never a number then.
pub(crate) fn worked_min(ctx: &Ctx) -> Option<u32> {
    worked_min_at(ctx, ctx.now)
}

/// [`worked_min`] as of `end`: the minutes worked up to the end a `tm stop
/// --at`/`tm done --at` states (the owner's D79) — the same one reading, every
/// span clipped to `[start, end]`, so the night after a forgotten block's end
/// is not counted as worked.
fn worked_min_at(ctx: &Ctx, end: DateTime<FixedOffset>) -> Option<u32> {
    tm_core::planwire::running_worked_min(&ctx.state, &ctx.replay, ctx.cfg.tz, ctx.now_tz, ctx.today, end)
}

/// **What `tm now` shows for the running block** — [`log::Replay::shown_worked_min`],
/// the rule the TUI's timer calls too: the log's reading (D75), and the
/// cache's clock on the date the cache gives it only where the log holds no
/// open block for it, which D42's reconcile at load makes unreachable here.
pub(crate) fn shown_worked_min(ctx: &Ctx, active: &ActiveBlock) -> u32 {
    let clock = tm_core::capacity::local_dt(
        ctx.cfg.tz,
        ctx.state.date.unwrap_or(ctx.today),
        active.started,
    );
    ctx.replay.shown_worked_min(
        active.id.as_str(),
        ctx.today,
        clock.fixed_offset(),
        ctx.now,
        running_break_at(ctx),
    )
}

/// **The running block's start, as the log has it** — the instant of its own
/// `start` line ([`log::OpenBlock::started`]), local: what `tm now` prints
/// beside the minutes [`worked_min`] counts from it, and what D76's refusal of
/// `tm wake` names. `None` with nothing running, or when the log holds no open
/// block for `.tm/state.json`'s (unreachable after D42's reconcile).
pub(crate) fn running_start(ctx: &Ctx) -> Option<DateTime<chrono_tz::Tz>> {
    let active = ctx.state.active.as_ref()?;
    ctx.replay
        .open_block
        .as_ref()
        .filter(|b| b.id == active.id.as_str())
        .map(|b| b.started.with_timezone(&ctx.cfg.tz))
}

/// The error `tm done` and `tm stop` give when `.tm/state.json` names a running
/// block the log holds no `start` for — unreachable after D42's reconcile, and
/// never answered with a zero (D75: a wrong `actual_min` in the log is the
/// silent-wrong-answer class).
fn no_logged_start(id: &Id) -> CliError {
    CliError::msg(format!(
        "{} is running in .tm/state.json but .tm/log.jsonl holds no `start` for it, so its \
         worked minutes cannot be read (D75)",
        id.token()
    ))
}

/// An instant as a verb names it: `HH:MM` on today's date, with the date on
/// any other (`2026-09-08 23:40`) — D76's refusal's spelling, shared.
fn when(ctx: &Ctx, t: DateTime<chrono_tz::Tz>) -> String {
    if t.date_naive() == ctx.today {
        hhmm(t)
    } else {
        format!("{} {}", t.date_naive(), hhmm(t))
    }
}

/// **The end a `tm stop --at HH:MM` or `tm done --at HH:MM` states for the
/// running block** — the owner's **D79** (README gap 3823), W-41 track T.
///
/// The clock is read by the ONE time parser, `tm energy --at`'s and `tm arrive
/// --at`'s ([`parse_time`]), and placed at the LATEST instant at or before
/// `now` with that clock ([`tm_core::capacity::latest_at_or_before`]) — D75's
/// rule where the user, and not the log, supplies the instant — so `--at 23:40`
/// typed at 07:05 is last night's. An end is a time the block ran through, so
/// it is never after `now` (by that construction), and three ends are refused
/// by name, before anything is written:
///
/// * one **before the block's start** — the log's own instant (D75's
///   `running_start`), so `--at 17:00` typed at 16:30 names yesterday's 17:00
///   and is refused when the block began today;
/// * one **before a timer mark the log already holds for the block** — a
///   `pause`, `unpause`, `interrupt` or `resume` stamped after it says the
///   block was still running (or paused) then, and a `stop` stamped before
///   such a mark would make the replay's machine bank the stretch up to the
///   mark (it reads the log in file order, `Replay.lean` C3) while the minutes
///   this verb logs stop at the end: two readings of one block;
/// * one **before the start of a break `.tm/state.json` holds running** —
///   `tm break` paused the block after the end, by the cache's account.
///
/// D61's meeting marks are not among them by construction: the verb loads
/// without them (`Ctx::load_without_wall_marks`) and runs them at this end.
fn stated_end(ctx: &Ctx, active: &ActiveBlock, at: &str) -> Result<DateTime<chrono_tz::Tz>, CliError> {
    let clock = parse_time(at)?;
    let end = tm_core::capacity::latest_at_or_before(ctx.cfg.tz, ctx.now_tz, clock);
    let start = running_start(ctx).ok_or_else(|| no_logged_start(&active.id))?;
    if end < start {
        return Err(CliError::msg(format!(
            "`--at {at}` names {}, the latest {at} at or before now, which is before {} began \
             ({}) — the end of a block falls between its start and now; nothing was written",
            when(ctx, end),
            active.id.token(),
            when(ctx, start)
        )));
    }
    if let Some((tag, t)) = timer_mark_after(ctx, active, start, end) {
        let t = t.with_timezone(&ctx.cfg.tz);
        return Err(CliError::msg(format!(
            "the log already holds `{tag}` for {} at {}, after the end you gave ({}) — by the \
             log's account the block was still running then (a calendar wall's pause is logged \
             by the first verb after the wall begins); give an end at or after {}; nothing was \
             written",
            active.id.token(),
            when(ctx, t),
            when(ctx, end),
            hhmm(t)
        )));
    }
    if let Some(began) = ctx.running_break().filter(|b| *b > end) {
        return Err(CliError::msg(format!(
            "a break has been running since {}, after the end you gave ({}) — it paused {} \
             then; end the break first (`tm break`), or give an end at or after {}; nothing \
             was written",
            when(ctx, began),
            when(ctx, end),
            active.id.token(),
            hhmm(began)
        )));
    }
    Ok(end)
}

/// The first timer mark the log holds for the running block that is stamped
/// after `end`: a surviving `pause` or `unpause` of it, or an `interrupt` or
/// `resume` (the marks the replay's machine reads for the open block), at or
/// after its own `start` row ([`log::Replay::start_row`]; every row in scope
/// when the scope does not reach it). Each tag is asked of [`Event`] rather
/// than spelled a second time (AGENTS §5.3).
fn timer_mark_after(
    ctx: &Ctx,
    active: &ActiveBlock,
    start: DateTime<chrono_tz::Tz>,
    end: DateTime<chrono_tz::Tz>,
) -> Option<(String, DateTime<FixedOffset>)> {
    let tag = |e: Event| e.name().to_string();
    let own = [tag(Event::Pause { id: String::new() }), tag(Event::Unpause { id: String::new() })];
    let any = [tag(Event::Interrupt { id: None }), tag(Event::Resume { lost_min: 0, dropped: Vec::new() })];
    let rows = ctx.replay.view();
    let from = ctx
        .replay
        .start_row(Some(active.id.as_str()), start.fixed_offset())
        .unwrap_or(0);
    rows[from..]
        .iter()
        .filter(|r| !r.cancelled && r.t > end)
        .find(|r| {
            any.contains(&r.tag) || (own.contains(&r.tag) && r.id.as_deref() == Some(active.id.as_str()))
        })
        .map(|r| (r.tag.clone(), r.t))
}

/// **A calendar wall that starts while a block is running STOPS THE TIMER** —
/// the owner's **D61** (README gaps 2805 and 2932), parity **P53** — **decided
/// by the kernel** since W-37 (README gap **3139**), and **said** since the
/// owner's **D65** (parity **P56**).
///
/// §9's Interruption row makes an ad-hoc wall pause the Active block, and D57
/// (3) made a wall on `now` do the same in the kernel — but only as a state of
/// the day AT `now`: the log recorded nothing, so once the meeting ended a
/// replan drew the worked stretch across it, and the minutes `tm now` prints
/// and `tm done` logs ([`log::Replay::active_worked_min`]) counted the meeting
/// as work (driven by the W-35 auditor: `56m of 30m` over a 17:10–17:50 call).
///
/// **What is written.** The log's existing events, never a new kind: a
/// `pause{id}` stamped at the wall's start and an `unpause{id}` stamped at its
/// end — so the replay's open block banks the stretch before the meeting and
/// runs again from its end (`Planner.a_logged_wall_pause_is_no_worked_time`),
/// the host's worked minutes net the pair out like any pause, and the day
/// draws the meeting as its Wall row alone (D65, `Planner.a_paused_row_lies_under_no_wall`).
///
/// **Who decides — the kernel, over its own reading of the calendar.** Until
/// W-37 this function read the day's walls through `Ctx::walls_on` (fork
/// `Ctx::walls_on`) and ran the rule itself: a second reader of the walls
/// beside the kernel's `Look.wallsOn`, deciding one day (AGENTS §5.3), and a
/// rule no Lean statement named. Now it asks: one request — the tree, the zone,
/// the log section the capacity request sends (the process checkpoint and the
/// tail, D24's seam), `now`, `blockMin`, and the `emit` section's walls form
/// with the instant and the running break `.tm/state.json` holds (the one fact
/// the log does not carry) — and the kernel answers the lines to append, in
/// order, each with its span and walls (`WallTimer.writes`, whose laws are
/// `WallTimer.a_wall_that_starts_while_a_block_runs_stops_its_timer` and the
/// four ways it writes nothing), rendered by its one writer (D16). This
/// function appends exactly those bytes; it reads no wall.
///
/// **When.** No process runs continuously, so the pause is written the way
/// §6.3's automatic close catches up: by the housekeeping of the first verb
/// that runs after the wall BEGAN, and the unpause by the first one after it
/// ENDED; a verb run after the wall ended writes both, in order. The call is
/// made only while a block is open — with none there is no timer to stop.
///
/// **Said (D65).** A pause the user did not type is announced: one line on
/// stderr naming the block, the wall and the span (`paused ^t4 for Meeting w/
/// host 12:50–13:50`), and each written mark gets the day file's journal line
/// a typed `tm pause` writes, at the mark's own time.
///
/// **A tree the kernel will not load** cannot be asked about its walls: the
/// refusal is printed by name and nothing is written — the automatic close's
/// rule — and the verb goes on. A kernel fault fails the verb.
///
/// **As of `at`** (W-41 track T) — the walls form's `at`, so a wall that begins
/// after it is not the block's and an unpause is written only for a wall that
/// ended by then: `now` for the housekeeping of every verb (`Ctx::load`), and
/// the end a `tm stop --at`/`tm done --at` states for the verb that ends the
/// block earlier (the owner's D79), which loads without this housekeeping
/// (`Ctx::load_without_wall_marks`) and runs it at that end, so its own load
/// never logs a meeting the block it is ending never ran through.
///
/// Returns whether it wrote anything, so the caller reloads the replay.
pub(crate) fn stop_the_timer_at_walls(ctx: &mut Ctx, at: DateTime<chrono_tz::Tz>) -> Result<bool, CliError> {
    let Some(active) = ctx.state.active.clone() else {
        return Ok(false);
    };
    let marks = match ask_the_walls(ctx, running_break_at(ctx), at) {
        Ok(answer) => answer.marks,
        Err(CliError::Kernel(issue)) if !issue.is_fault() => {
            if !super::kernel_bridge::capturing_kernel_stderr() {
                eprintln!(
                    "tm: the meeting pause (D61) was not checked, so nothing was written; it is \
                     checked again on the next command. {}",
                    issue.message
                );
            }
            return Ok(false);
        }
        Err(e) => return Err(e),
    };
    let Some(last) = marks.last() else {
        return Ok(false);
    };
    let paused = last.pause;
    for m in &marks {
        ctx.append_line(&m.line)?;
        // The mark's OWN date (README gap 3334): a meeting that crosses
        // midnight is paused on the evening it began, and its journal line
        // belongs in that day's file, not in the file of the day the verb ran.
        super::dayfile::note_underneath(
            ctx,
            m.at.date_naive(),
            m.at.time(),
            &timer_note(m.pause, &active.id),
            Some((&active.id, m.pause)),
        )?;
        if m.pause {
            say_wall_pause(ctx, &active.id, &m.walls, m.from, m.to);
        }
    }
    // The cache reads the stops the kernel holds, never the last mark alone
    // (the owner's D118, README gap 5030): a wall's `unpause` ends the wall's
    // pause and no other stop — an interruption still open, or a break still
    // running, holds the block (D117, D114) — as `ctx::derived_state` reads it.
    let interrupted = ctx.state.interrupt.is_some();
    let on_break = ctx.state.break_.is_some();
    if let Some(a) = ctx.state.active.as_mut() {
        a.paused = paused || interrupted || on_break;
    }
    ctx.save_state()?;
    Ok(true)
}

/// One mark the kernel says the day's walls write (the `emit` walls form's
/// answer): whether it is the pause or the unpause, its stamp and the span it
/// belongs to (local), the walls the span joins, and the exact line to append.
struct WallMark {
    pause: bool,
    at: DateTime<chrono_tz::Tz>,
    from: DateTime<chrono_tz::Tz>,
    to: DateTime<chrono_tz::Tz>,
    walls: Vec<Id>,
    line: String,
}

/// A joined wall span, local, and the walls it joins.
struct WallSpan {
    from: DateTime<chrono_tz::Tz>,
    to: DateTime<chrono_tz::Tz>,
    walls: Vec<Id>,
}

/// **What the kernel answers about the day's walls**: the marks to append, in
/// order, and the meeting the running block is paused for now, if its pause is
/// still the last word on the timer (`WallTimer.pausedFor`) — what `tm pause`
/// names when it resumes the timer inside a meeting (D66, README gap 3048).
struct WallsAnswer {
    marks: Vec<WallMark>,
    paused_for: Option<WallSpan>,
}

/// **Ask the kernel what the day's walls write** (README gap 3139): the request
/// [`stop_the_timer_at_walls`] describes, and its answer decoded — every key
/// named, a missing or mistyped one a named fault and never a guess.
fn ask_the_walls(
    ctx: &Ctx,
    running_break: Option<DateTime<FixedOffset>>,
    at: DateTime<chrono_tz::Tz>,
) -> Result<WallsAnswer, CliError> {
    let (resp, stderr) = call_the_walls(ctx, running_break, at, None)?;
    let fault = |what: &str| {
        CliError::Kernel(super::kernel_bridge::fault_issue(
            &format!("walls response: {what}"),
            &stderr,
        ))
    };
    let entries = resp["ok"]["emit"]["marks"]
        .as_array()
        .ok_or_else(|| fault("no `ok.emit.marks` array"))?;
    let tz = ctx.cfg.tz;
    let stamp = |v: &serde_json::Value, key: &str| -> Result<DateTime<chrono_tz::Tz>, CliError> {
        v[key]
            .as_str()
            .and_then(|s| DateTime::parse_from_rfc3339(s).ok())
            .map(|t| t.with_timezone(&tz))
            .ok_or_else(|| fault(&format!("an entry's `{key}` is not a stamp")))
    };
    let walls_of = |v: &serde_json::Value| -> Result<Vec<Id>, CliError> {
        v["walls"]
            .as_array()
            .ok_or_else(|| fault("a `walls` is not an array"))?
            .iter()
            .map(|w| w.as_str().map(Id::new).ok_or_else(|| fault("a wall is not an id")))
            .collect()
    };
    let mut out = Vec::with_capacity(entries.len());
    for e in entries {
        let pause = match e["ev"].as_str() {
            Some("pause") => true,
            Some("unpause") => false,
            _ => return Err(fault("an entry's `ev` is neither pause nor unpause")),
        };
        if e["id"].as_str() != ctx.state.active.as_ref().map(|a| a.id.as_str()) {
            return Err(fault("an entry names a block that is not the running one"));
        }
        let walls = walls_of(e)?;
        let line = e["line"]
            .as_str()
            .ok_or_else(|| fault("an entry's `line` is not a string"))?
            .to_string();
        out.push(WallMark {
            pause,
            at: stamp(e, "at")?,
            from: stamp(e, "from")?,
            to: stamp(e, "to")?,
            walls,
            line,
        });
    }
    let pf = &resp["ok"]["emit"]["pausedFor"];
    let paused_for = if pf.is_null() {
        None
    } else {
        Some(WallSpan { from: stamp(pf, "from")?, to: stamp(pf, "to")?, walls: walls_of(pf)? })
    };
    Ok(WallsAnswer { marks: out, paused_for })
}

/// **The `emit` section's walls form, asked** — the one request both of its
/// readers build (README gap 3139; W-39 track T, gaps 3432 and 3528): D61's
/// housekeeping asks what the day's walls write ([`ask_the_walls`]), and the
/// week grid asks the same form for a week's cut of its Pauses ([`week_cut`]).
/// With a `week` the `log` section carries the week's sealed day records
/// (`kernel_log::week_log_section`), so the kernel's answer holds every day of
/// it; without one the request is byte for byte what W-37 sent.
fn call_the_walls(
    ctx: &Ctx,
    running_break: Option<DateTime<FixedOffset>>,
    at: DateTime<chrono_tz::Tz>,
    week: Option<tm_core::model::IsoWeek>,
) -> Result<(serde_json::Value, String), CliError> {
    // The plan directory and the log as every request from this context reads them
    // (`Ctx::reading`, `Ctx::log_now`): with a close the TUI holds in memory past midnight, what
    // `tm plan` reads after its own (the owner's D91).
    let docs = super::kernel_bridge::text_docs(ctx.reading()?.store())?;
    let cache = ctx.store.root().join(".tm/cache/replay");
    let tz_wire = super::tz_table::wire_for(Some(&cache), ctx.cfg.tz);
    let bytes = ctx.log_now()?;
    let now_day = super::kernel_log::day_of(ctx.today);
    let dates = week.map(|w| w.dates());
    let log = match dates.as_ref().and_then(|d| d.first().zip(d.last())) {
        None => super::kernel_log::capacity_log_section(ctx.store.root(), &bytes, &tz_wire, now_day),
        Some((first, last)) => super::kernel_log::week_log_section(
            ctx.store.root(),
            &bytes,
            &tz_wire,
            now_day,
            super::kernel_log::day_of(*first),
            super::kernel_log::day_of(*last),
        ),
    }
    .map_err(super::ctx::genesis_error)?;
    // The one encoder of the walls object (README gap 3955).
    let walls = tm_core::planwire::walls_json(
        at.fixed_offset(),
        running_break,
        dates.as_ref().and_then(|d| d.first()).copied(),
    );
    let rest = serde_json::json!({
        "docs": docs,
        "now": ctx.today.to_string(),
        "blockMin": ctx.block_min(),
        "tz": tz_wire,
        "emit": {"walls": walls},
    })
    .to_string();
    // The `log` section is spliced as text, as the capacity request splices it: its checkpoint
    // is read in build order (`Seal.readCkptFields`), which a `serde_json::Value` would sort.
    let request = format!("{{\"log\":{log},{}", &rest[1..]);
    super::kernel_bridge::call_text(&request)
}

/// **The kernel's cut of `week`'s Pauses, for the heat grid** (README gaps
/// 3432 and 3528; `GridCut.lean`): the walls form asked with a `week`, its
/// `ok.emit.cut` decoded — every key named, a missing or mistyped one a named
/// fault and never a guess. **Every Pause of the week the host's replay holds
/// must have its cut**: a Pause the answer does not name is refused by name,
/// never drawn whole, because the host keeps no cut of its own to fall back on
/// (AGENTS §5.3). It is a refusal and not a fault: the one way it happens is
/// the log changing between the verb's read of it and this call's (§1.3's
/// other writers), and the TUI keeps its last cut on a refusal where a fault
/// would end it.
pub(crate) fn week_cut(
    ctx: &Ctx,
    week: tm_core::model::IsoWeek,
) -> Result<tm_core::review::PauseCut, CliError> {
    let (resp, stderr) = call_the_walls(ctx, running_break_at(ctx), ctx.now_tz, Some(week))?;
    let days: Vec<(chrono::NaiveDate, &[log::LogSegment])> = week
        .dates()
        .into_iter()
        .filter_map(|d| ctx.replay.day(d).map(|r| (d, r.segments.as_slice())))
        .collect();
    read_week_cut(&resp, &stderr, ctx.cfg.tz, &days)
}

/// [`week_cut`]'s reading of the kernel's answer, apart from the call, so the
/// two ways it refuses can be shown to (the tests below). `days` is the week's
/// days the host's replay holds, each with its segments.
fn read_week_cut(
    resp: &serde_json::Value,
    stderr: &str,
    tz: chrono_tz::Tz,
    days: &[(chrono::NaiveDate, &[log::LogSegment])],
) -> Result<tm_core::review::PauseCut, CliError> {
    let fault = |what: &str| {
        CliError::Kernel(super::kernel_bridge::fault_issue(
            &format!("week cut response: {what}"),
            stderr,
        ))
    };
    // The one decoder of `ok.emit.cut` (README gap 3955); a defect in it is a fault.
    let cut = tm_core::planwire::read_week_cut(resp, tz).map_err(|e| fault(&e))?;
    for (date, segments) in days {
        let date = *date;
        for seg in segments.iter() {
            if matches!(seg.kind, log::SegmentKind::Pause { .. }) && cut.pieces_of(date, seg).is_none() {
                return Err(CliError::msg(format!(
                    "the kernel's cut of the week names no cut for the pause {}–{} of {date} — the \
                     kernel's replay and this verb's reading of the log disagree about that pause \
                     (the log may have changed between the two reads; run it again, and if it \
                     persists this is a bug in tm)",
                    log::fmt_timestamp(&seg.start),
                    log::fmt_timestamp(&seg.end)
                )));
            }
        }
    }
    Ok(cut)
}

/// **The day file's journal line of a timer mark** — `pause ^id` or `unpause
/// ^id`, what a typed [`pause`] writes and what the owner's D65 has D61's
/// automatic pair write too. One spelling for both writers (AGENTS §5.3).
fn timer_note(paused: bool, id: &Id) -> String {
    format!("{} {}", if paused { "pause" } else { "unpause" }, id.token())
}

/// **The line that SAYS a wall paused the running block** — the owner's D65
/// (parity P56, README gap 3141): `paused ^t4 for Standup 12:50–13:50`, on
/// stderr beside the verb's own output, naming the block, the wall (every wall
/// a joined span holds) and the span the timer was stopped over. A pause
/// written by housekeeping and never mentioned is the silent-wrong-answer
/// class: a user who skipped the meeting could not know the minutes had been
/// netted out. Nothing is printed while the TUI holds the terminal.
fn say_wall_pause(
    ctx: &Ctx,
    block: &Id,
    walls: &[Id],
    lo: DateTime<chrono_tz::Tz>,
    hi: DateTime<chrono_tz::Tz>,
) {
    super::kernel_bridge::notice(wall_pause_line(ctx, block, walls, lo, hi));
}

/// [`say_wall_pause`]'s text: `paused ^t4 for` and [`meeting_text`].
fn wall_pause_line(
    ctx: &Ctx,
    block: &Id,
    walls: &[Id],
    lo: DateTime<chrono_tz::Tz>,
    hi: DateTime<chrono_tz::Tz>,
) -> String {
    format!("paused {} for {}", block.token(), meeting_text(ctx, walls, lo, hi))
}

/// **A meeting, as the user reads it**: the wall's title (its key when the tree
/// holds no such item), several walls a joined span holds joined by `, `, and
/// the span in local `HH:MM` — `Meeting w/ host 12:50–13:50`. The one spelling
/// of a meeting in D65's notice and D66's `tm pause` message.
fn meeting_text(
    ctx: &Ctx,
    walls: &[Id],
    lo: DateTime<chrono_tz::Tz>,
    hi: DateTime<chrono_tz::Tz>,
) -> String {
    let titles: Vec<String> = walls
        .iter()
        .map(|w| ctx.tree.get(w).map_or_else(|| w.to_string(), |i| i.title.clone()))
        .collect();
    format!("{} {}–{}", titles.join(", "), hhmm(lo), hhmm(hi))
}

/// `tm wake --json`.
#[derive(Debug, Serialize)]
pub struct WakeOut {
    /// The date the day belongs to.
    pub date: String,
    /// `HH:MM`.
    pub wake: String,
    /// Minutes slept.
    pub slept_min: u32,
    /// Minutes to fall asleep.
    pub onset_min: Option<u32>,
}

/// `tm wake [HH:MM] [--slept 8h10m] [--onset 25m]`.
pub fn wake(g: &Globals, args: &super::WakeArgs) -> Result<i32, CliError> {
    // Without D61's wall marks (W-41 track T): a wake never runs beside a block
    // (D76, below), so they have nothing to write when it succeeds, and when it
    // is refused they would log the morning's meetings into the block its own
    // message says to end with `--at` — refusing that `--at` in turn.
    let mut ctx = Ctx::load_without_wall_marks(g)?;
    // **The owner's D76 (README gap 3725, parity P66): `tm wake` while a block
    // is still running is REFUSED BY NAME**, before the gate, the undo recorder
    // and every write. The wake cleared `active` in `.tm/state.json` while the
    // log held nothing that ended the block, so the next verb's reconcile (D42)
    // read the block back as running — a verb that did not do what it said.
    // Ending the block at the wake would write a duration nobody stated (the
    // night counted as work), so the user says how it ended: `tm stop` or
    // `tm done`, as D71 has `tm resume` end an interruption first. The running
    // block is `.tm/state.json`'s as the reconcile leaves it — the log's open
    // block, paused or not — read as every other verb reads it, and its start
    // is the log's own (`running_start`, D75).
    if let Some(active) = ctx.state.active.as_ref() {
        return Err(CliError::msg(wake_over_a_running_block(&ctx, active)));
    }
    // **And over every other running state a wake would clear** — the
    // campaign's D81 call on README gap 3824 (parity P74): an interruption the
    // log holds open (the one reading `tm start` and the rebuild take,
    // `ctx::open_interruption`; the cache's is D42's copy of it) and a break
    // `.tm/state.json` holds running (`Ctx::running_break`, P73). The wake
    // cleared both while the log held the interruption open, so the next verb's
    // reconcile read it back (the cache still `null`) and a later `tm resume`
    // logged the night as lost; the running break, being host-only, was lost
    // with no line. The user says how each ended, as D76 has them say how a
    // block did.
    if let Some(open) = super::ctx::open_interruption(&ctx.replay) {
        return Err(CliError::msg(wake_over_an_open_interruption(&ctx, open)));
    }
    // The RECORD is what a wake would clear, so the record is what is asked
    // (the W-41 repair, README gap 4141): a cached break whose `started` is
    // null — a hand edit; `tm break` always sets it — has no instant
    // (`Ctx::running_break` is `None`) and was cleared here with no line.
    if ctx.state.break_.is_some() {
        let since = ctx.running_break().map(|b| format!(" since {}", when(&ctx, b))).unwrap_or_default();
        return Err(CliError::msg(format!(
            "a break is still running{since} — end it (`tm break`) before `tm wake`; the wake \
             was not recorded"
        )));
    }
    super::kernel_bridge::gate(&ctx, "wake")?;
    let rec = Recorder::start(&ctx, "wake")?;
    let time = match &args.time {
        Some(t) => parse_time(t)?,
        None => ctx.now_tz.time(),
    };
    let block_min = ctx.block_min();
    let slept_min = match &args.slept {
        Some(s) => dur(s, block_min)?.as_minutes(),
        None => 0,
    };
    let onset_min = match &args.onset {
        Some(s) => Some(dur(s, block_min)?.as_minutes()),
        None => None,
    };

    // A new day: the window, the budget and everything running are gone.
    ctx.state.date = Some(ctx.today);
    ctx.state.wake = Some(time);
    ctx.state.arrival = None;
    ctx.state.window = None;
    ctx.state.budget = None;
    ctx.state.active = None;
    ctx.state.break_ = None;
    ctx.state.interrupt = None;
    ctx.save_state()?;

    let entry = log::LogEntry::new(
        ctx.at(time).fixed_offset(),
        Event::Wake {
            slept_min,
            onset_min,
        },
    );
    ctx.append_entry(&entry)?;
    ctx.reload()?;

    // §4.3: the day file's front matter carries the wake time and the sleep,
    // and `## Log` its first line.
    let slept = super::out::fmt_dur(slept_min);
    let mut front = vec![("wake", fmt_time(time))];
    if slept_min > 0 {
        front.push(("slept", slept.clone()));
    }
    super::dayfile::front(&ctx, ctx.today, &front)?;
    super::dayfile::note(
        &ctx,
        ctx.today,
        time,
        &format!(
            "wake slept={slept}{}",
            onset_min.map(|o| format!(" onset={o}m")).unwrap_or_default()
        ),
    )?;
    rec.finish(&ctx, format!("wake {}", fmt_time(time)))?;

    let out = WakeOut {
        date: ctx.today.to_string(),
        wake: fmt_time(time),
        slept_min,
        onset_min,
    };
    emit(
        ctx.json,
        || {
            format!(
                "wake {} · slept {}m{}",
                out.wake,
                out.slept_min,
                out.onset_min
                    .map(|o| format!(" · onset {o}m"))
                    .unwrap_or_default()
            )
        },
        &out,
    )?;
    Ok(0)
}

/// **D76's refusal, in words** (README gap 3725): the running block, when it
/// began — the log's own instant, with its date when that is not today's — and
/// the two verbs that end it. Paused or not, it is running until one of them
/// says how it ended.
///
/// **It names `--at`** (the owner's D79): a block forgotten overnight ends when
/// it ended — `tm stop --at 23:40` — and the night is not counted as worked.
fn wake_over_a_running_block(ctx: &Ctx, active: &ActiveBlock) -> String {
    let since = match running_start(ctx) {
        Some(t) => format!(" since {}", when(ctx, t)),
        None => format!(" since {}", active.started.format("%H:%M")),
    };
    format!(
        "{} is still running{since} — stop it (`tm stop`) or finish it (`tm done`) before \
         `tm wake`, with `--at HH:MM` for when it ended if that was earlier; the wake was not \
         recorded",
        active.id.token()
    )
}

/// **Gap 3824's refusal over an open interruption, in words**: when it began
/// (the log's own instant, dated when not today's) and the verb that ends it.
fn wake_over_an_open_interruption(ctx: &Ctx, open: &tm_core::log::Interruption) -> String {
    let since = open
        .start
        .map(|t| format!(" since {}", when(ctx, t.with_timezone(&ctx.cfg.tz))))
        .unwrap_or_default();
    format!(
        "an interruption is still open{since} — end it (`tm resume`) before `tm wake`; the wake \
         was not recorded"
    )
}

/// `tm arrive --json`.
#[derive(Debug, Serialize)]
pub struct ArriveOut {
    /// The date.
    pub date: String,
    /// Where you are.
    pub loc: String,
    /// `HH:MM`.
    pub arrival: String,
    /// `[start, end]` (§8.1).
    pub window: [String; 2],
    /// Block budget (§8.1).
    pub budget: u32,
    /// Calendar files the sync wrote (§15).
    pub synced: Vec<String>,
    /// Anything that went wrong without failing the verb.
    pub warnings: Vec<String>,
    /// The plan the arrival produced.
    pub plan_hash: String,
    /// The block starts recorded for §12.1's ghost row.
    pub plan_at_arrival: Vec<ArrivalBlock>,
}

/// One block start as it stood at arrival.
#[derive(Clone, Debug, Serialize, serde::Deserialize)]
pub struct ArrivalBlock {
    /// `HH:MM`.
    pub start: String,
    /// The item.
    pub id: Option<String>,
}

/// `.tm/arrival_plan.json`.
#[derive(Clone, Debug, Serialize, serde::Deserialize)]
pub struct ArrivalPlan {
    /// The day.
    pub date: String,
    /// The plan hash at arrival.
    pub hash: String,
    /// The planned block starts.
    pub blocks: Vec<ArrivalBlock>,
}

/// **The pre-flight the three verbs that write before they plan owe** (gap
/// 115). `arrive`, `resume` and `energy` write `state.json` and the log
/// *before* the planning call that sends the tree to the kernel, so until this
/// a tree the kernel refuses was found only *after* the write. Driven at
/// `89ead46` on a `plan-basic` copy whose `^m1` carries a typo'd `@parent`:
/// `arrive` exited 1 having appended its `arrive` line *and* written
/// `state.json`; `energy 3` exited 1 having appended its `energy` line; and
/// `resume` exited 1 having cleared the interruption out of `state.json` —
/// losing it outright, since no log line recorded it either.
///
/// [`super::kernel_capacity::check_plan`] covers the *configured* values
/// (parity P26). This adds the **tree**, through
/// [`super::kernel_bridge::gate`] — the one shared write gate the owner's D35
/// makes every host-only write path ask (gap 584). It used to ask
/// `kernel_bridge::apply(ctx, &[])`, which is the same question through the
/// machine that ends in a write step: a request with no commands changes
/// nothing, but a document the kernel *renormalises* differs from the one sent
/// and would have been written back by a pre-flight. The gate goes to
/// `kernel_bridge::call` directly and cannot write at all.
fn preflight(ctx: &Ctx, verb: &str) -> Result<(), CliError> {
    super::kernel_capacity::check_plan(ctx)?;
    super::kernel_bridge::gate(ctx, verb)?;
    Ok(())
}

/// `tm arrive [lounge|home|<name>]`.
pub fn arrive(g: &Globals, args: &super::ArriveArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    preflight(&ctx, "arrive")?;
    let rec = Recorder::start(&ctx, "arrive")?;
    let loc = args
        .loc
        .clone()
        .or_else(|| ctx.state.loc.clone())
        .unwrap_or_else(|| "lounge".to_string());
    let at = match &args.at {
        Some(t) => parse_time(t)?,
        None => ctx.now_tz.time(),
    };

    // §15: sync the calendar first, so the walls are in the window.
    let mut warnings = Vec::new();
    let mut synced = Vec::new();
    if ctx.cfg.calendar.sync_on_arrive && !ctx.cfg.calendar.ics_urls.is_empty() {
        match super::lifecycle::sync_calendar(&ctx) {
            Ok(r) => {
                synced = r.files;
                warnings.extend(r.warnings);
                ctx.reload()?;
            }
            Err(e) => warnings.push(format!("calendar sync failed: {e}")),
        }
    }

    // **One definition of §8.1's window, shared with D42's rebuild** (the
    // owner's **D45**, AGENTS §5.3): `Ctx::arrival_window` is what writes the
    // cache here and what derives it back from the log when the cache is
    // gone, so the two cannot disagree about a day with two arrivals — and
    // since W-47 it is the KERNEL's window (README gap 4746, parity P113): the
    // day's own request over the state this arrival stores, so the window the
    // day is planned by after an arrive is the kernel's reading of its walls.
    let (window, budget) = ctx.arrival_window(at)?;
    ctx.state.date = Some(ctx.today);
    ctx.state.arrival = Some(at);
    ctx.state.loc = Some(loc.clone());
    ctx.state.window = Some(window);
    ctx.state.budget = Some(budget);
    ctx.save_state()?;

    // **`arrive.t` IS the arrival** — `tm_core::log`'s own event convention
    // ("`wake.t` is the wake time; `arrive.t` the arrival; `start.t` the block
    // start"), which `tm wake` above has always honoured and this verb did not:
    // it stamped [`Ctx::now`], so a retro `tm arrive --at 07:00` run at 13:00
    // wrote a header reading 13:00 and left the arrival only inside
    // `window[0]`. Two readings of one fact (AGENTS §5.3), and the one that
    // moved was the reader's: D42's rebuild takes the header for the arrival,
    // so deleting `.tm/state.json` moved `arrival` and `window` to an instant
    // in neither the cache nor the payload (README gap 1305).
    //
    // Without `--at` this is the same instant to the second — `at` is
    // `ctx.now_tz.time()` and `Ctx::at` puts it back on today's date in the
    // same zone — so the only bytes that move are a retro or future `--at`'s,
    // which move to what the convention says they must be.
    let entry = log::LogEntry::new(
        ctx.at(at).fixed_offset(),
        Event::Arrive {
            loc: loc.clone(),
            window: [fmt_time(window.0), fmt_time(window.1)],
            budget,
        },
    );
    ctx.append_entry(&entry)?;
    ctx.reload()?;

    // The plan, and the ghost row §12.1 draws from it.
    let (plan, prios) = planning::build(&ctx, false)?;
    planning::write_plan(&mut ctx, &plan, &prios)?;
    let blocks: Vec<ArrivalBlock> = plan
        .segments
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                tm_core::dayplan::SegKind::Block | tm_core::dayplan::SegKind::Batch(_)
            )
        })
        .map(|s| ArrivalBlock {
            start: hhmm(s.start),
            id: s.item.as_ref().map(|i| i.to_string()),
        })
        .collect();
    let arrival_plan = ArrivalPlan {
        date: ctx.today.to_string(),
        hash: plan.hash(),
        blocks: blocks.clone(),
    };
    ctx.store
        .write_file(ARRIVAL_PLAN_PATH, &serde_json::to_string_pretty(&arrival_plan)?)?;
    ctx.reload()?;

    // §4.3's runtime front matter, and the arrival in `## Log`.
    super::dayfile::front(
        &ctx,
        ctx.today,
        &[
            ("loc", loc.clone()),
            ("window", format!("{}..{}", fmt_time(window.0), fmt_time(window.1))),
            ("budget", budget.to_string()),
        ],
    )?;
    super::dayfile::note(&ctx, ctx.today, at, &format!("arrive {loc}"))?;
    rec.finish(&ctx, format!("arrive {loc} {}", fmt_time(at)))?;

    let out = ArriveOut {
        date: ctx.today.to_string(),
        loc,
        arrival: fmt_time(at),
        window: [fmt_time(window.0), fmt_time(window.1)],
        budget,
        synced,
        warnings,
        plan_hash: plan.hash(),
        plan_at_arrival: blocks,
    };
    emit(
        ctx.json,
        || {
            let mut s = format!(
                "arrive {} {} · window {}–{} · budget {} blocks",
                out.loc, out.arrival, out.window[0], out.window[1], out.budget
            );
            for w in &out.warnings {
                s.push_str(&format!("\n! {w}"));
            }
            s
        },
        &out,
    )?;
    Ok(0)
}

/// `tm start --json`.
#[derive(Debug, Serialize)]
pub struct StartOut {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// `HH:MM`.
    pub started: String,
    /// Predicted energy (§8.5).
    pub pred: u8,
    /// Reported energy, if given.
    pub rep: Option<u8>,
    /// Planned minutes (`est × multiplier`).
    pub est_min: u32,
    /// The duration multiplier used.
    pub multiplier: f64,
    /// Hours since wake.
    pub hsw: f64,
    /// **The break this verb ended first** — `tm break`'s own report of its ending, `action`
    /// `ended` (the owner's **D101**, README gap 4551, parity **P102**: D97's one rule reaching
    /// the terminal and `--json`, as `tm interrupt` and `tm resume` carry it); absent when no
    /// break was running.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub break_ended: Option<BreakOut>,
}

/// `tm start ^id`.
pub fn start(g: &Globals, args: &super::StartArgs) -> Result<i32, CliError> {
    // `--energy` is §8.5's reported level, the same 0–5 scale `tm energy`
    // takes — and `tm energy 9` says so. Filtering an out-of-range value away
    // here instead asked for the energy again on a terminal and recorded
    // nothing off one, which is the report the user typed thrown away without
    // a word. Checked before the tree is loaded: nothing else runs.
    if let Some(level) = args.energy.filter(|v| *v > 5) {
        return Err(CliError::msg(format!("--energy is 0–5, not {level}")));
    }
    let mut ctx = Ctx::load(g, true)?;
    let id = Ctx::key(&args.id);
    let item = ctx.item(&id)?.clone();
    if let Some(a) = &ctx.state.active {
        if a.id != id {
            return Err(CliError::msg(format!(
                "{} is running — `tm done`, `tm stop` or `tm extend` first",
                a.id.token()
            )));
        }
        // **The block already running is CONTINUED, not restarted** — the owner's **D107**
        // (README gap 4892, parity **P110**): a running break ends, through the one body every
        // verb that ends a break runs (`end_break_first`, with `tm break`'s journal line, D97),
        // and nothing else is logged. Nothing at all is written when no break runs, so the write
        // gate (D35) and the undo recorder are asked only then ([`say_already_running`]).
        let break_ended = if ctx.state.break_.is_some() {
            super::kernel_bridge::gate(&ctx, "start")?;
            let rec = Recorder::start(&ctx, "start")?;
            let mut ended = end_break_first(&mut ctx)?;
            ctx.save_state()?;
            ctx.reload()?;
            if let Some(b) = ended.as_mut() {
                note_break_ended(&ctx, b, ctx.now_tz)?;
            }
            rec.finish(&ctx, format!("start {} · already running · break ended", id.token()))?;
            ended
        } else {
            None
        };
        return say_already_running(&ctx, &id, &item, args.energy, break_ended);
    }
    super::kernel_bridge::gate(&ctx, "start")?;
    let rec = Recorder::start(&ctx, "start")?;
    let replay_before = ctx.replay.clone();
    // **A running break ends first, and says so** — `tm break`'s line and its journal line
    // (the owner's D97, README gap 4391, parity P95): the one body every verb that ends a
    // break runs. Fork 4748911 ended it here too and wrote no journal line.
    let mut ended_break = end_break_first(&mut ctx)?;

    let mut f = features(&ctx, ctx.now_tz);
    if ended_break.is_some() {
        // The break this very command closed is not in `ctx.replay` yet.
        f.since_break_min = 0;
    }
    let pred = energy::predict(&ctx.model, &ctx.cfg, &f);
    let rep = args.energy.or_else(|| ask_energy(pred));
    // §8.5's planned minutes, through the ONE function that computes them:
    // D42's rebuild of `.tm/state.json` puts the same number back when the
    // cache is gone, and a second copy of this arithmetic here would be the
    // AGENTS §5.3 defect that rebuild exists to stop having an instance of.
    let (est_min, multiplier) = ctx.planned_block(&id);

    // §5.1/§4.3: a routine or optional line has no state and never changes —
    // its occurrences live in the log, not in the file.
    if !is_stateless(&item) {
        let mut line = ctx.line(&id)?;
        line.set_state(State::Active)?;
        ctx.write_line(&id, &line)?;
    }

    ctx.state.active = Some(ActiveBlock {
        id: id.clone(),
        started: ctx.now_tz.time(),
        est_min,
        // **Paused while an interruption runs** (the campaign's D69 call on
        // README gap 3283, parity P60): `tm start` does not end an
        // interruption, and the rebuild of `.tm/state.json` from the log pauses
        // the open block for the open interruption — so the cache writes what
        // the rebuild derives, and deleting it moves nothing. `tm resume`
        // unpauses it, as it unpauses a block `tm interrupt` paused.
        paused: super::ctx::open_interruption(&ctx.replay).is_some(),
    });
    // The verb's own line says so too (README gap 3525): `tm now` said
    // `· paused` while the line `tm start` printed said only `▶`.
    let paused = ctx.state.active.as_ref().is_some_and(|a| a.paused);
    ctx.state.date = Some(ctx.today);
    ctx.save_state()?;

    ctx.append_event(Event::Start {
        id: id.to_string(),
        pred,
        rep,
        hsw: f.hsw,
        slept_min: ctx.slept_min().unwrap_or(0),
        loc: ctx.state.loc.clone().unwrap_or_else(|| "lounge".to_string()),
        blocks_done: ctx.replay.blocks_done(ctx.today),
        since_break_min: f.since_break_min,
    })?;
    ctx.reload()?;
    if let Some(b) = ended_break.as_mut() {
        note_break_ended(&ctx, b, ctx.now_tz)?;
    }
    day_note(
        &ctx,
        format!(
            "start {} pred={pred}{}",
            id.token(),
            rep.map(|r| format!(" rep={r}")).unwrap_or_default()
        ),
    )?;
    correct_netted_estimates(&mut ctx, &replay_before, "start")?;
    rec.finish(&ctx, format!("start {}", id.token()))?;

    let out = StartOut {
        id: id.clone(),
        title: item.title.clone(),
        started: hhmm(ctx.now_tz),
        pred,
        rep,
        est_min,
        multiplier,
        hsw: f.hsw,
        break_ended: ended_break,
    };
    emit(
        ctx.json,
        || {
            said_after_break(out.break_ended.as_ref(), format!(
                "▶ {} {} · {} · pred {}{}{}",
                out.id.token(),
                out.title,
                out.started,
                out.pred,
                out.rep.map(|r| format!(" rep {r}")).unwrap_or_default(),
                if paused { " · paused: an interruption is open (`tm resume` starts the timer)" } else { "" }
            ))
        },
        &out,
    )?;
    Ok(0)
}

/// One estimate [`correct_netted_estimates`] rewrote (the owner's D126).
#[derive(Debug, Clone, Serialize)]
pub struct EstCorrected {
    /// The item.
    pub id: Id,
    /// The minutes its line's estimate read before this verb.
    pub from_min: u32,
    /// The minutes it reads now: what its closing verb would have written with the minutes the log now counts.
    pub to_min: u32,
}

/// The tags of the lines that can be logged after a block's `stop` and stamped inside it, changing the minutes it
/// counts — a late `start` (D115), a `break` or its running start (D100, D129, D137), an interruption (D119).
pub(crate) const LATE_MARKS: &[&str] = &["start", "break", "break_start", "interrupt", "resume"];

/// **D126's one reading of a stopped block's estimate** — what [`correct_netted_estimates`] writes and what `tm check`'s
/// stale-estimate warning compares the line with (`lifecycle::stale_estimates`), so the verb and the check cannot
/// disagree about one line (AGENTS §5.3).
#[derive(Debug, Clone)]
pub(crate) struct D126Reading {
    /// The view index of the `stop` (or partial `done`) that wrote the remainder.
    pub closing: usize,
    /// The remainder that verb wrote: the line's estimate, or the `from` of the first D126 correction since.
    pub written: u32,
    /// The block's minutes as the closing verb's author counted them: the replay of the log up to it, a
    /// `break_start` still running there taken out (that verb ends a running break first, D97, so a running one is
    /// a line it never saw — a sync's).
    pub at_close: u32,
    /// The minutes the whole log counts now.
    pub now: u32,
    /// What the closing verb would have written with `now`: `written + (at_close − now)`, never below the floor
    /// `tm stop` itself writes ([`MIN_REMAINING_MIN`]).
    pub expected: u32,
}

/// The replay of the log's lines `1..=last` with line `drop` left out, through the replay that writes nothing.
fn replay_of_prefix(ctx: &Ctx, last: u64, drop: Option<u64>) -> Option<tm_core::log::Replay> {
    let bytes = ctx.log_now().ok()?;
    let mut prefix: Vec<u8> = Vec::new();
    for (n, l) in bytes.split(|b| *b == b'\n').enumerate() {
        let line = n as u64 + 1;
        if line > last {
            break;
        }
        if Some(line) == drop {
            continue;
        }
        prefix.extend_from_slice(l);
        prefix.push(b'\n');
    }
    let tz = Ctx::tz_wire(&ctx.store, &ctx.cfg);
    super::kernel_log::replay_unsealed(
        ctx.store.root(),
        &prefix,
        ctx.cfg.tz,
        &tz,
        ctx.today,
        super::kernel_log::Scope::Hot,
    )
    .ok()
    .flatten()
    .map(|r| r.replay)
}

/// One log line's own JSON, by its 1-based line.
fn log_line_json(ctx: &Ctx, line: u64) -> Option<serde_json::Value> {
    let bytes = ctx.log_now().ok()?;
    let raw = bytes.split(|b| *b == b'\n').nth(line.checked_sub(1)? as usize)?;
    serde_json::from_slice(raw).ok()
}

/// `"35m"` (what a D126 correction's `edit` logs) as minutes.
fn minutes_of(v: &serde_json::Value) -> Option<u32> {
    v.as_str()?.strip_suffix('m')?.parse().ok()
}

/// `written + (at_close − now)`, floored where `tm stop` floors (D126's reading: the remainder the closing verb would
/// have written had it counted `now` minutes).
fn d126_expected(written: u32, at_close: u32, now: u32) -> u32 {
    if at_close == now {
        return written;
    }
    let raw = i64::from(written) + i64::from(at_close) - i64::from(now);
    u32::try_from(raw.max(i64::from(MIN_REMAINING_MIN))).unwrap_or(u32::MAX)
}

/// **D126's reading of `key`**, when its estimate is still the one its closing `stop` (or partial `done`) wrote:
/// the item's last logged lines are that verb's and, after it, only `edit`s that are D126 corrections — an `est` edit
/// logged straight after a late mark, rewriting the then estimate to exactly what this reading gave there — or edits of
/// another field. Any other line of the item (a typed `tm edit est=`, an `extend`, a later block) makes the estimate
/// the user's, and `None` is answered. The line's openness is the caller's to check.
pub(crate) fn d126_reading(ctx: &Ctx, key: &str) -> Option<D126Reading> {
    let view = ctx.replay.view();
    let rows: Vec<usize> = (0..view.len())
        .filter(|&i| !view[i].cancelled && view[i].id.as_deref() == Some(key))
        .collect();
    let mut k = rows.len();
    while k > 0 && view[rows[k - 1]].tag == "edit" {
        k -= 1;
    }
    let closing = *rows.get(k.checked_sub(1)?)?;
    if view[closing].tag != "stop" && view[closing].tag != "done" {
        return None;
    }
    let edits: Vec<(usize, serde_json::Value)> = rows[k..]
        .iter()
        .filter_map(|&j| log_line_json(ctx, view[j].line).map(|v| (j, v)))
        .filter(|(_, v)| v["field"].as_str() == Some("est"))
        .collect();
    let id = Id::new(key);
    let written = match edits.first() {
        Some((_, v)) => minutes_of(&v["from"])?,
        None => ctx.tree.remaining(&id)?,
    };
    // The running `break_start` at the closing line, if any: the closing verb ends a running break before it logs
    // itself (D97), so one still running there is a line its author never saw.
    let mut open_break = None;
    for r in view[..=closing].iter().filter(|r| !r.cancelled) {
        match r.tag.as_str() {
            "break_start" => open_break = Some(r.line),
            "break" => open_break = None,
            _ => {}
        }
    }
    let at_close = replay_of_prefix(ctx, view[closing].line, open_break)?.block_minutes(key);
    let mut chain = written;
    for (j, v) in &edits {
        let after_mark = view[..*j]
            .iter()
            .rev()
            .find(|r| !r.cancelled && r.tag != "edit")
            .is_some_and(|r| LATE_MARKS.contains(&r.tag.as_str()));
        let then = replay_of_prefix(ctx, view[*j].line, None)?.block_minutes(key);
        let to = minutes_of(&v["to"])?;
        if !after_mark || minutes_of(&v["from"]) != Some(chain) || to != d126_expected(written, at_close, then) {
            return None;
        }
        chain = to;
    }
    let now = ctx.replay.block_minutes(key);
    Some(D126Reading { closing, written, at_close, now, expected: d126_expected(written, at_close, now) })
}

/// **A late mark that changes a stopped or partly done block's minutes corrects the `est:` its closing verb wrote** —
/// the owner's **D126** (W-49 track L; the W-48 recheck's fourth finding; parity **P125**), in both directions since
/// the W-51 repair (the critic's blocker, README gap 5610). `tm stop` (and `tm done --partial`) writes the remainder —
/// the estimate less the minutes worked — and a line logged after it and stamped inside its block changes the minutes
/// the replay counts: a late `start` (D115), a `break`'s running start (D100, D129, README gap 5180) or an
/// interruption's `resume` (D119) nets the block, and the running break's own `break` line gives back what its running
/// took outside the break's span (D137). The verb that logs such a line compares the replay before and after it, and
/// every item whose minutes MOVED, whose estimate is still its closing verb's ([`d126_reading`]), and whose line is
/// open gets the remainder that verb would have written with the minutes the log now counts — through the one estimate
/// writer (D56, D62: `write_estimate`), logged as an `edit`. Until the W-51 repair only minutes that FELL were
/// corrected, so a give-back left the netted estimate standing (`35m` over a block the log counted at fifty minutes,
/// and `tm check` silent). A late line no verb wrote (a sync, a hand edit) is named by `tm check` instead
/// (`lifecycle::stale_estimates`), over the same reading.
fn correct_netted_estimates(
    ctx: &mut Ctx,
    before: &tm_core::log::Replay,
    verb: &str,
) -> Result<Vec<EstCorrected>, CliError> {
    let mut out = Vec::new();
    let moved: Vec<String> = before
        .items
        .keys()
        .chain(ctx.replay.items.keys())
        .filter(|k| before.block_minutes(k) != ctx.replay.block_minutes(k))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    for key in moved {
        let id = Id::new(&key);
        let Some(item) = ctx.tree.get(&id) else { continue };
        if is_stateless(item) || item.state.is_closed() {
            continue;
        }
        let Some(reading) = d126_reading(ctx, &key) else { continue };
        let Some(from) = ctx.tree.remaining(&id) else { continue };
        let to = reading.expected;
        if to == from {
            continue;
        }
        let line = write_estimate(ctx, verb, &id, u64::from(to))?;
        ctx.write_line(&id, &line)?;
        // The correction is a fact the log holds, as a typed `tm edit est=` is: `tm check`'s half of D126 reads it
        // as a correction (`d126_reading`), so the estimate stays the closing verb's for every later mark.
        ctx.append_event(Event::Edit {
            id: id.to_string(),
            field: "est".to_string(),
            from: format!("{from}m"),
            to: format!("{to}m"),
        })?;
        out.push(EstCorrected { id, from_min: from, to_min: to });
    }
    if !out.is_empty() {
        ctx.reload()?;
        for c in &out {
            super::kernel_bridge::notice(format!(
                "{}'s estimate is now {}m (was {}m): this line changed the minutes the log counts for the block its \
                 `stop` closed, and the remainder reads them as the log now does (D126).",
                c.id.token(),
                c.to_min,
                c.from_min,
            ));
        }
    }
    Ok(out)
}

/// `tm start --json` on the block already running (the owner's **D107**, parity **P110**).
#[derive(Debug, Serialize)]
pub struct ContinueOut {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// Always `true`: the block was already running, and nothing but the end of a running break
    /// was logged.
    pub already_running: bool,
    /// When it started, as the log has it (D75) — `HH:MM`, dated when not today's.
    pub started: String,
    /// Planned minutes (`.tm/state.json`'s, as `tm now` reads them).
    pub est_min: u32,
    /// The timer is paused — by a `tm pause` before the break, or an open interruption.
    pub paused: bool,
    /// The `--energy` report given, which a continuation does not record (it logs no `start`);
    /// absent when none was given.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub energy_not_recorded: Option<u8>,
    /// **The break this verb ended** — `tm break`'s own report of its ending (D97, D101), as a
    /// `tm start` that starts a block carries it; absent when no break was running.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub break_ended: Option<BreakOut>,
}

/// **What `tm start ^id` says on the block already running** — the owner's **D107** (README gap
/// 4892, parity **P110**): `^id is already running since HH:MM`, after `tm break`'s clause when the
/// verb ended a running break (D101), and in `--json` [`ContinueOut`].
///
/// Fork 4748911 logged a second `start` and restarted `.tm/state.json`'s clock: the replay closed
/// the first stretch at it, so `tm review day` and the drawn rows counted both stretches while `tm
/// stop` and `tm done` computed from the second start and wrote `est:` less only that stretch —
/// resuming after a break wrote `30m left` where 60 minutes were worked, a silently wrong estimate
/// in the user's file. The block keeps its one `start` now, so every reader counts one block.
///
/// A typed `tm pause` before the break, or an open interruption, keeps the block paused, as ending
/// a break leaves it (P84), and the line says so; an `--energy` report is not recorded (no `start`
/// is logged) and the line says that too, naming the verb that records one.
fn say_already_running(
    ctx: &Ctx,
    id: &Id,
    item: &tm_core::model::Item,
    energy: Option<u8>,
    break_ended: Option<BreakOut>,
) -> Result<i32, CliError> {
    let Some(active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    // The log's start (D75); the cache's clock only where the log holds no open block for it,
    // which D42's reconcile at load makes unreachable — `tm now`'s reading of the same start.
    let started = running_start(ctx)
        .map(|t| when(ctx, t))
        .unwrap_or_else(|| active.started.format("%H:%M").to_string());
    let out = ContinueOut {
        id: id.clone(),
        title: item.title.clone(),
        already_running: true,
        started,
        est_min: active.est_min,
        paused: active.paused,
        energy_not_recorded: energy,
        break_ended,
    };
    let interrupted = super::ctx::open_interruption(&ctx.replay).is_some();
    emit(
        ctx.json,
        || {
            let paused = match (out.paused, interrupted) {
                (false, _) => "",
                (true, true) => " · paused: an interruption is open (`tm resume` starts the timer)",
                (true, false) => " · paused (`tm pause` starts the timer)",
            };
            let energy = out
                .energy_not_recorded
                .map(|e| format!(" · --energy {e} not recorded: no `start` is logged (`tm energy {e}` reports it)"))
                .unwrap_or_default();
            said_after_break(
                out.break_ended.as_ref(),
                format!("{} is already running since {}{paused}{energy}", out.id.token(), out.started),
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm done --json`.
#[derive(Debug, Serialize)]
pub struct DoneOut {
    /// The item.
    pub id: Id,
    /// Its title.
    pub title: String,
    /// Planned minutes.
    pub est_min: u32,
    /// Minutes worked (0 for a retro done).
    pub actual_min: u32,
    /// The block is done, the item is not.
    pub partial: bool,
    /// The state the line now carries.
    pub state: String,
    /// The remaining estimate written back, when partial.
    pub remaining_min: Option<u32>,
    /// The end `--at` stated (D79), `HH:MM`, dated when not today's. Absent
    /// otherwise: the block ended now.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ended: Option<String>,
    /// **The break this verb ended first** — `tm break`'s own report of its ending, `action`
    /// `ended` (the owner's **D101**, README gap 4551, parity **P102**: D97's one rule reaching
    /// the terminal and `--json`, as `tm interrupt` and `tm resume` carry it); absent when no
    /// break was running.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub break_ended: Option<BreakOut>,
    /// **The item's line was settled and left as it stands** (the owner's **D135**, README gap 5505,
    /// parity **P131**: D132's rule for `tm done` and `--partial`): no box set, no remainder written,
    /// no line reopened; `state` is the settled glyph's word. Absent otherwise.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub settled: bool,
}

/// `tm done [--partial] [--at HH:MM] [^id]`.
pub fn done(g: &Globals, args: &super::DoneArgs) -> Result<i32, CliError> {
    // §10.1's `went` is 1, 2 or 3 (§8.5). Filtering anything else away left
    // the two records of one `done` disagreeing: the `## Log` note in the day
    // file printed `went=7` while `.tm/log.jsonl` recorded no `went` at all,
    // and §8.5 never saw the report. Checked before the tree is loaded.
    if let Some(went) = args.went.filter(|w| !(1..=3).contains(w)) {
        return Err(CliError::msg(format!(
            "--went is 1 fine, 2 hard or 3 collapsed (§8.5), not {went}"
        )));
    }
    // D79: a stated end loads without D61's wall marks, which run at that end
    // once it is checked (`stated_end`).
    let mut ctx = match args.at {
        Some(_) => Ctx::load_without_wall_marks(g)?,
        None => Ctx::load(g, true)?,
    };
    let active = ctx.state.active.clone();
    let (id, retro) = match (&args.id, &active) {
        (Some(arg), Some(a)) => {
            let id = Ctx::key(arg);
            let retro = id != a.id;
            (id, retro)
        }
        (Some(arg), None) => (Ctx::key(arg), true),
        (None, Some(a)) => (a.id.clone(), false),
        (None, None) => return Err(CliError::msg("nothing is running (`tm done ^id` for a retro done)")),
    };
    // `--at` ends the RUNNING block (D79); a retro done has no timing (§13).
    if let (Some(at), true) = (&args.at, retro) {
        return Err(CliError::msg(format!(
            "`--at {at}` says when the running block ended, and {} is not running — `tm done {}` \
             with no block of its own is a retro done, which takes no time (§13); nothing was \
             written",
            id.token(),
            id.token()
        )));
    }
    // An ambiguous title is refused before anything is logged (W-16 repair,
    // gap 576): this verb looks the argument up in the tree directly rather
    // than through `Ctx::item`, so it needs the refusal by name.
    ctx.refuse_ambiguous_title(&id)?;
    // §1.3: the other two writers may have removed the line while the block
    // ran. That must not wedge the block machine, so a missing item only
    // costs the line edit, not the event and not the state change.
    let item = match ctx.tree.get(&id) {
        Some(i) => Some(i.clone()),
        None if retro => return Err(missing(&id)),
        None => None,
    };
    // **D140** (the W-51 critic's second finding, parity **P135**): a retro `tm done ^id` — one that
    // ends no block — on a SETTLED line (`[~]`, `[x]`) is refused by name, before anything is
    // written: no line, no log line, no journal. Until the W-51 repair it set `[x]` on a dropped line
    // inside a week a close had already taken, the closed-file edit D132 and D135 exist to prevent,
    // by the one natural verb they left. A user who wants a dropped item marked done edits the line.
    if let Some(item) = item.as_ref().filter(|i| retro && is_settled(i)) {
        return Err(settled_retro_done(&ctx, &id, item));
    }
    // **D79**: the stated end, checked, and D61's marks up to it; `None`
    // without `--at`, when the block ends now.
    let stated = match (&args.at, &active) {
        (Some(at), Some(a)) => {
            let end = stated_end(&ctx, a, at)?;
            if stop_the_timer_at_walls(&mut ctx, end)? {
                ctx.reload()?;
            }
            Some(end)
        }
        _ => None,
    };
    let end = stated.unwrap_or(ctx.now_tz);
    super::kernel_bridge::gate(&ctx, "done")?;
    let rec = Recorder::start(&ctx, "done")?;

    let (est_min, actual_min) = if retro {
        (ctx.tree.remaining(&id).unwrap_or(0), 0)
    } else {
        let a = active.as_ref().expect("an active block");
        // D75 (parity P65): the worked minutes count from the log's own
        // `start` — and, with D79's `--at`, up to the end it states.
        let worked = match stated {
            Some(e) => worked_min_at(&ctx, e.fixed_offset()),
            None => worked_min(&ctx),
        };
        (a.est_min, worked.ok_or_else(|| no_logged_start(&a.id))?)
    };
    let stateless = item.as_ref().is_some_and(is_stateless);
    // **D135** (README gap 5505, parity **P131**): D132's rule reaches `tm done` and `tm done
    // --partial` — a block whose item is SETTLED (`[~]`, `[x]`) logs its event and leaves the line
    // exactly as it stands: no box set, no remainder written, no line reopened, inside a closed
    // period or not. Fork 4748911 (and this verb until the W-51 repair) set `[x]` on a dropped line,
    // and `--partial` reopened it as `[ ] 5m`. A retro `tm done ^id` ends no block, so it is outside
    // D135 — and since the owner's D140 (P135) one on a settled line is refused above, by name.
    let settled = !retro && item.as_ref().is_some_and(is_settled);
    // **D62**: a partial's remainder is written by the kernel's `est` op FIRST —
    // before the break is ended or the box is moved — so a refusal (a value
    // past the host's width) leaves nothing written at all.
    let mut remaining_min = None;
    let mut written = None;
    if args.partial && item.is_some() && !stateless && !settled {
        let left = ctx
            .tree
            .remaining(&id)
            .unwrap_or(est_min)
            .saturating_sub(actual_min)
            .max(MIN_REMAINING_MIN);
        written = Some(write_estimate(&ctx, "done", &id, u64::from(left))?);
        remaining_min = Some(left);
    }
    // A running break ends at the block's end, through the one body every verb that ends a
    // break runs, and says so in the journal below (the owner's D97, parity P95).
    let mut ended_break = end_break_first_at(&mut ctx, end)?;

    if let Some(item) = item.as_ref().filter(|_| !stateless && !settled) {
        let mut line = match written {
            Some(line) => line,
            None => ctx.line(&id)?,
        };
        if args.partial {
            line.set_state(State::Todo)?;
        } else if matches!(item.recur, Recur::OnEvent { .. }) {
            // §5.1: an on-event item goes to `[?]` with `waiting:<the day it
            // was done>` — today's, or the day a stated end falls on.
            recur::on_done_waiting(item, end.date_naive()).apply(&mut line)?;
        } else {
            line.set_state(State::Done)?;
        }
        ctx.write_line(&id, &line)?;
    }

    if !retro {
        ctx.state.active = None;
    }
    ctx.save_state()?;

    // §10.1: a routine or optional occurrence is a `routine` event, not a
    // `done` — a `done{id}` would mark the recurring item finished for good.
    // **D79**: stamped at the stated end — the log holds that instant, so the
    // replay, the day records, the durations §8.5 fits and `tm log` all read
    // the block as ending there (`log_the_end`).
    let event = match item.as_ref().filter(|_| stateless) {
        Some(item) => Event::Routine {
            item: id.to_string(),
            inst: instance_key(&ctx, item, end),
            status: "done".to_string(),
            actual_min: Some(actual_min),
        },
        None => Event::Done {
            id: id.to_string(),
            est_min,
            actual_min,
            went: args.went,
            tags: ctx.tree.tags_effective(&id),
            // §3.1's default when the line itself is gone.
            ci: item.as_ref().map(|i| i.ci).unwrap_or(3),
            partial: args.partial,
        },
    };
    log_the_end(&ctx, stated, event)?;
    ctx.reload()?;
    if let Some(b) = ended_break.as_mut() {
        note_break_ended(&ctx, b, end)?;
    }
    note_the_end(
        &ctx,
        stated,
        format!(
            "done {} {}m/{}m{}{}",
            id.token(),
            actual_min,
            est_min,
            args.went.map(|w| format!(" went={w}")).unwrap_or_default(),
            // D136 (parity P132): the journal says the line is settled and names no minutes left.
            if settled { SETTLED_NOTE } else { "" }
        ),
    )?;
    rec.finish(&ctx, format!("done {}", id.token()))?;

    let state = ctx
        .tree
        .get(&id)
        .map(|i| i.state.as_str().to_string())
        .unwrap_or_else(|| State::Done.as_str().to_string());
    let out = DoneOut {
        id: id.clone(),
        title: item.map(|i| i.title).unwrap_or_default(),
        est_min,
        actual_min,
        partial: args.partial,
        state,
        remaining_min,
        ended: stated.map(|e| when(&ctx, e)),
        break_ended: ended_break,
        settled,
    };
    emit(
        ctx.json,
        || {
            said_after_break(out.break_ended.as_ref(), format!(
                "✓ {} {} · {}m/{}m{}{}",
                out.id.token(),
                out.title,
                out.actual_min,
                out.est_min,
                out.remaining_min
                    .map(|r| format!(" · {r}m left"))
                    .unwrap_or_default(),
                out.ended.as_ref().map(|e| format!(" · ended {e}")).unwrap_or_default()
                    + if out.settled {
                        // D135: nothing was written to the line.
                        " · its line is settled and left as it stands (D135)"
                    } else {
                        ""
                    }
            ))
        },
        &out,
    )?;
    Ok(0)
}

/// **Log the event that ends the running block** — stamped at `now`, or at
/// the end a `tm stop --at`/`tm done --at` states (the owner's **D79**: the
/// log holds THAT instant, D75's clock). It is appended after any line logged
/// since — the log is append-only — and every reader takes it so: the kernel's
/// replay reads the log in file order and dates each entry by its own stamp
/// (`Replay.lean` C2, C3), so the block's span, its minutes, its day record,
/// the durations §8.5 fits and `tm log`'s rows (file order, each with its
/// stamp) are the ones an in-time `stop` or `done` at that instant gives
/// (`tm/tests/cli_end_at.rs`); `Log.linesIncreasing` is a law about LINE
/// numbers, which still increase. `stated_end` refuses the ends a later line
/// contradicts, so no timer mark of the block follows its end in time.
fn log_the_end(ctx: &Ctx, stated: Option<DateTime<chrono_tz::Tz>>, event: Event) -> Result<(), CliError> {
    match stated {
        Some(end) => ctx.append_entry(&log::LogEntry::new(end.fixed_offset(), event)),
        None => ctx.append_event(event),
    }
}

/// The day file's `## Log` line of the verb that ends the block — at `now` in
/// today's file, or at a stated end in the file of the day it falls on.
fn note_the_end(ctx: &Ctx, stated: Option<DateTime<chrono_tz::Tz>>, text: String) -> Result<(), CliError> {
    match stated {
        Some(end) => super::dayfile::note(ctx, end.date_naive(), end.time(), &text),
        None => day_note(ctx, text),
    }
}

/// `tm extend --json`.
#[derive(Debug, Serialize)]
pub struct ExtendOut {
    /// The item.
    pub id: Id,
    /// Minutes added.
    pub by_min: u32,
    /// The block's new planned length.
    pub est_min: u32,
}

/// `tm extend [1b]`.
pub fn extend(g: &Globals, args: &super::ExtendArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let Some(active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    super::kernel_bridge::gate(&ctx, "extend")?;
    let rec = Recorder::start(&ctx, "extend")?;
    let block_min = ctx.block_min();
    let by = match &args.by {
        Some(s) => dur(s, block_min)?.as_minutes(),
        None => block_min,
    };
    let id = active.id.clone();
    // §1.3: a line the other writers removed costs the estimate's rewrite, not
    // the block. **D62**: the kernel's `est` op writes it — one estimate on the
    // line, the value as typed (`write_estimate`) — and the sum is taken wide,
    // so a remainder near the host's `u32` is refused by name rather than
    // wrapped.
    if ctx.tree.get(&id).is_some_and(|i| !is_stateless(i)) {
        let remaining = ctx.tree.remaining(&id).unwrap_or(0);
        write_estimate(&ctx, "extend", &id, u64::from(remaining) + u64::from(by))?;
    }

    let est_min = active.est_min.saturating_add(by);
    ctx.state.active = Some(ActiveBlock { est_min, ..active });
    ctx.save_state()?;
    ctx.append_event(Event::Extend {
        id: id.to_string(),
        by_min: by,
    })?;
    ctx.reload()?;
    day_note(&ctx, format!("extend {} +{by}m", id.token()))?;
    rec.finish(&ctx, format!("extend {} +{by}m", id.token()))?;

    let out = ExtendOut {
        id: id.clone(),
        by_min: by,
        est_min,
    };
    emit(
        ctx.json,
        || format!("+{}m on {} · now {}m", out.by_min, out.id.token(), out.est_min),
        &out,
    )?;
    Ok(0)
}

/// `tm stop --json`.
#[derive(Debug, Serialize)]
pub struct StopOut {
    /// The item.
    pub id: Id,
    /// Minutes worked.
    pub worked_min: u32,
    /// The remaining estimate written back.
    pub remaining_min: u32,
    /// The end `--at` stated (D79), `HH:MM`, dated when not today's. Absent
    /// otherwise: the block ended now.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub ended: Option<String>,
    /// **The break this verb ended first** — `tm break`'s own report of its ending, `action`
    /// `ended` (the owner's **D101**, README gap 4551, parity **P102**: D97's one rule reaching
    /// the terminal and `--json`, as `tm interrupt` and `tm resume` carry it); absent when no
    /// break was running.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub break_ended: Option<BreakOut>,
    /// **The item's line was settled and left as it stands** (the owner's **D132**, README gap 5471,
    /// parity **P129**): no remainder was written and no box reopened; `remaining_min` is the
    /// remainder the stop would have written. Absent otherwise.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub settled: bool,
}

/// `tm stop [--at HH:MM]`.
pub fn stop(g: &Globals, args: &super::StopArgs) -> Result<i32, CliError> {
    // D79: a stated end loads without D61's wall marks, which run at that end
    // once it is checked (`stated_end`).
    let mut ctx = match args.at {
        Some(_) => Ctx::load_without_wall_marks(g)?,
        None => Ctx::load(g, true)?,
    };
    let Some(active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    // **D79**: the stated end, checked, and D61's marks up to it; `None`
    // without `--at`, when the block ends now.
    let stated = match &args.at {
        Some(at) => {
            let end = stated_end(&ctx, &active, at)?;
            if stop_the_timer_at_walls(&mut ctx, end)? {
                ctx.reload()?;
            }
            Some(end)
        }
        None => None,
    };
    super::kernel_bridge::gate(&ctx, "stop")?;
    let rec = Recorder::start(&ctx, "stop")?;
    let out = end_the_block(&mut ctx, &active, stated, "stop", false)?;
    rec.finish(&ctx, format!("stop {}", out.id.token()))?;
    emit(
        ctx.json,
        || {
            said_after_break(out.break_ended.as_ref(), format!(
                "stopped {} after {}m · {}{}",
                out.id.token(),
                out.worked_min,
                if out.settled {
                    // D132: nothing was written to the line.
                    "its line is settled and left as it stands (D132)".to_string()
                } else {
                    format!("{}m left", out.remaining_min)
                },
                out.ended.as_ref().map(|e| format!(" · ended {e}")).unwrap_or_default()
            ))
        },
        &out,
    )?;
    Ok(0)
}

/// **The journal's words for a block ended on a settled line** — the owner's **D136** (README gap
/// 5540, parity **P132**): the line holds no remainder (D132, D135), so the journal names none.
const SETTLED_NOTE: &str = " · line settled, left as it stands";

/// **Whether `item`'s line is SETTLED** — dropped (`[~]`) or done (`[x]`): the lines the owner's D132
/// has `tm stop` leave as they stand.
fn is_settled(item: &tm_core::model::Item) -> bool {
    matches!(item.state, State::Dropped | State::Done)
}

/// **D140's refusal** (parity **P135**): a retro `tm done` on a settled line names the line as settled, says
/// nothing was written, and says to edit the line to mark it done.
fn settled_retro_done(ctx: &Ctx, id: &Id, item: &tm_core::model::Item) -> CliError {
    let file = ctx.tree.file_of(id).map(|f| f.path.clone()).unwrap_or_default();
    let (glyph, what, advice) = match item.state {
        State::Done => ("[x]", "already done", "The line is already marked done"),
        _ => ("[~]", "dropped", "To mark it done, edit its line's box to `[x]`"),
    };
    CliError::msg(format!(
        "{} is settled — {what} (`{glyph}`) in {file} — and a retro `tm done` on a settled line is refused; nothing \
         was written. {advice} (D140)",
        id.token()
    ))
}

/// **Ending the running block — the ONE body** `tm stop` runs and, since the owner's **D130**
/// (README gap 5413, parity **P128**), the stop §6.3's close writes before it takes a running
/// block's item ([`super::closing`]): the worked minutes as of the end (`stated`, D79's instant,
/// or now), the remainder written by the kernel's `est` op first (D62), the running break ended
/// at that end (D97), the box back to `[ ]`, the `stop` logged at the end (D75's clock), the
/// cache cleared, and the day file's journal lines. `verb` is what a refusal calls the command;
/// `housekeeping` says no undo recorder is running (the close a verb's load runs), so the
/// journal lines are rebased under the undo stack as D61's housekeeping lines are
/// ([`super::dayfile::note_underneath`]). Every write goes through the doors a held context
/// answers into (the owner's D96), so a TUI past midnight holds this stop with its close.
pub(crate) fn end_the_block(
    ctx: &mut Ctx,
    active: &ActiveBlock,
    stated: Option<DateTime<chrono_tz::Tz>>,
    verb: &str,
    housekeeping: bool,
) -> Result<StopOut, CliError> {
    let end = stated.unwrap_or(ctx.now_tz);
    let id = active.id.clone();
    // D75 (parity P65): the worked minutes count from the log's own `start` —
    // and, with D79's `--at`, up to the end it states.
    let worked = match stated {
        Some(e) => worked_min_at(ctx, e.fixed_offset()),
        None => worked_min(ctx),
    }
    .ok_or_else(|| no_logged_start(&id))?;
    let remaining = ctx
        .tree
        .remaining(&id)
        .unwrap_or(active.est_min)
        .saturating_sub(worked)
        .max(MIN_REMAINING_MIN);

    // **D62**: the remainder is written by the kernel's `est` op FIRST, so a
    // refusal leaves nothing written — not the break's end, not the box. The
    // box moves on the line the kernel returned (`write_estimate`).
    // A tabbed line is written as any line since the owner's D83 (README gap 32
    // closed): D66's branch for a refused estimate went with the refusal (gap 4165).
    // **D132** (README gap 5471, parity P129): a block whose item is SETTLED — `[~]` or `[x]`, as
    // a close before D130 could leave it — logs its `stop` and leaves the line as it stands: no
    // remainder written, no box reopened, so following `tm check`'s `log-taken-block` advice never
    // edits a closed file. A settled line is written by nothing here.
    let settled = ctx.tree.get(&id).is_some_and(is_settled);
    let written = match ctx.tree.get(&id).filter(|i| !is_stateless(i) && !is_settled(i)) {
        Some(_) => Some(write_estimate(ctx, verb, &id, u64::from(remaining))?),
        None => None,
    };
    // §11's break integrity: a break still running when the block stops is
    // over too, and its `break` event has to reach the log — at the stop's
    // instant, which D79's `--at` states — through the one body every verb that
    // ends a break runs, with its journal line below (the owner's D97, P95).
    let mut ended_break = end_break_first_at(ctx, end)?;
    if let Some(mut line) = written {
        line.set_state(State::Todo)?;
        ctx.write_line(&id, &line)?;
    }

    ctx.state.active = None;
    ctx.save_state()?;
    log_the_end(
        ctx,
        stated,
        Event::Stop {
            id: id.to_string(),
            remaining_min: remaining,
        },
    )?;
    ctx.reload()?;
    if let Some(b) = ended_break.as_mut() {
        note_break_ended(ctx, b, end)?;
    }
    // **D136** (README gap 5540, parity **P132**): a settled line's stop journals no remainder — the
    // line holds none (D132) — and says the line is settled. The log's `stop` still carries
    // `remaining_min`: the field is required by the log's grammar (`Log.Kind.schema`'s `.u32`) and
    // by fork 4748911's serde alike, so leaving it out would make the line malformed to both
    // readers (D136's own fallback; README gap 5560).
    let text = if settled {
        format!("stop {} {worked}m{SETTLED_NOTE}", id.token())
    } else {
        format!("stop {} {worked}m · {remaining}m left", id.token())
    };
    match (housekeeping, stated) {
        (true, Some(e)) => super::dayfile::note_underneath(ctx, e.date_naive(), e.time(), &text, None)?,
        _ => note_the_end(ctx, stated, text)?,
    }
    Ok(StopOut {
        id: id.clone(),
        worked_min: worked,
        remaining_min: remaining,
        ended: stated.map(|e| when(ctx, e)),
        break_ended: ended_break,
        settled,
    })
}

/// `tm break --json`.
#[derive(Debug, Serialize)]
pub struct BreakOut {
    /// `started`, `ended`, or — a backdated break with its length typed that a later logged `start`
    /// follows (the owner's **D143**, parity **P140**) — `finished`: its start and its end both logged.
    pub action: String,
    /// Planned minutes.
    pub planned_min: u32,
    /// Minutes it actually lasted (when ending).
    pub actual_min: Option<u32>,
    /// Where.
    pub place: Option<String>,
    /// **The end a later block's `start` had given the break this run ended** (`HH:MM`) — the owner's
    /// **D141** (README gap 5633, parity **P138**): `tm break` typed inside a logged break that D129 ended at
    /// a later start ends it at the typed instant, and this is the end it replaced. Absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub superseded_end: Option<String>,
    /// **The finished break this run logged** — the owner's **D143** (a backdated break with its length
    /// typed that a later logged `start` follows, `action` `finished`), **D148** (its length running past
    /// that start, `into_start` naming it) and **D146** (a length typed inside a break D129 ended: that
    /// break ended here, `action` `ended`, and this one logged from here). Absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub finished: Option<FinishedBreak>,
    /// **The instant the running break this run ended began** (stage 6 W-54 track H, README gap 5898) — what
    /// [`note_break_ended`] finds the break's record by, so the reply and the journal read the minutes the replay
    /// DRAWS for it. Not in `--json`; `None` for every report but a running break's ending.
    #[serde(skip)]
    pub ended_from: Option<DateTime<FixedOffset>>,
}

/// `tm break --json`'s `finished`: the span of a break logged finished in one plain `break` line
/// (the fork's shape — `t` its start, `planned_min` and `actual_min` its typed length, its place).
#[derive(Debug, Serialize, Clone)]
pub struct FinishedBreak {
    /// Its start (`HH:MM`).
    pub start: String,
    /// Its end (`HH:MM`): the start plus the typed length.
    pub end: String,
    /// The typed length, in minutes.
    pub actual_min: u32,
    /// Where.
    pub place: Option<String>,
    /// **The later logged `start` it runs past** (`HH:MM`, the owner's **D148**): the replay nets that
    /// block by the minutes the break runs into it (D92). Absent when the break ends at or before it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub into_start: Option<String>,
    /// **The item of the block it lies inside, that a later logged `done` or `stop` closed** (the owner's **D149**,
    /// parity **P147**): the replay nets that block by the minutes the break overlaps it (D100). Absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inside_block: Option<String>,
    /// **The item of the RUNNING block it lies inside** (the owner's **D152**, parity **P149**, README gap 5892): a
    /// length typed inside the open block whose typed end the log has already passed is a fact, logged finished; the
    /// replay nets the block by its minutes (D87, D100) and the block stays running, not paused. Absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inside_running: Option<String>,
    /// **The held break it begins inside, by its own span** (`HH:MM–HH:MM`; the W-54 third repair, README gaps 6050 and 6060), when
    /// none of D143, D148, D149 and D152 logged it: it ends inside that span, or runs past it to an end the log's own stamps have
    /// passed ([`FinishedBreak::adds_min`] then says what it adds). Never beside `inside_running`: that one is D152's. Absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inside_break: Option<String>,
    /// **The minutes the line adds to the breaks the day draws, when it runs past the end of `inside_break`** (README gap 6060): read
    /// off the replay before and after the line. Absent when it ends inside that span, or lies inside none.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub adds_min: Option<u32>,
    /// **Whether the block it lies inside counts fewer minutes for it** (D149 or D152; stage 6 W-54 repair track H,
    /// the W-54 critic's fourth note) — read off the replay before and after the line, never re-derived: `false` when
    /// the break lies where the block was not running (a pause, or another break). Absent when it lies inside none.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub nets: Option<bool>,
}

/// **Whether a break begun at `now` would be ended by a `start` the log already holds after it** (the owner's
/// **D129**) — asked of the KERNEL, never re-derived (§5.3): the break's `break_start` (`line`, rendered once by
/// the kernel's writer, D16) and its cache (`started`) are HELD in memory (the one hold every in-memory write goes
/// through, the owner's D96 and D106: [`Ctx::hold_begin`], the line into the hold, [`Ctx::reload`] reading the
/// context as the hold leaves it, [`Ctx::release`]), the replay over the held log answers whether D129 ended it
/// ([`Ctx::drop_break_a_start_ended`], the kernel's `open.ended`, README gap 5730), and the hold is let go, so
/// nothing reaches the disk and the context reads as before. Answers that — `Some` with the break's start and the
/// end D129 gave it (`None` for the end when the fact does not offer it, gap 5741) when a later start follows,
/// `None` when the break would run — and the held replay, which IS the replay of the log once `line` is appended
/// (the bytes [`Ctx::append_line`] writes), so a break that runs is written without a second replay. Stage 6 W-53
/// repair track H: a finished backdated break is then ONE plain `break` line, never a `break_start` (P140
/// restated, D148).
type Followed = Option<(DateTime<FixedOffset>, Option<DateTime<FixedOffset>>)>;
fn followed_by_a_start(
    ctx: &mut Ctx,
    line: &str,
    started: &BreakState,
) -> Result<(Followed, tm_core::log::Replay), CliError> {
    ctx.hold_begin()?;
    let asked = ctx.append_line(line).and_then(|()| {
        ctx.state.break_ = Some(started.clone());
        if let Some(a) = ctx.state.active.as_mut() {
            a.paused = true;
        }
        ctx.reload()
    });
    let answer = asked.map(|()| (ctx.drop_break_a_start_ended(), ctx.replay.clone()));
    ctx.release();
    answer
}

/// **Where a no-length `tm break --now <t>` falls against the breaks the log holds** — stage 6 W-54 third repair track H,
/// over track K's fact ([`Replay::held_breaks`], one entry per held break, its OWN span, never clipped by D142's union).
/// Exactly one arm for an instant, [`at_finished`]'s; the verb acts on it and never reads a log line (§5.3).
///
/// [`Replay::held_breaks`]: tm_core::log::Replay::held_breaks
#[derive(Clone, Debug, PartialEq)]
enum AtFinished {
    /// Strictly inside exactly one held break, at an instant the kernel reads as its re-time (D147). An instant only
    /// one closed span holds moves that break, so "re-timed" means moved.
    Inside(HeldBreak),
    /// At the end of a held break, or under a minute before it, no other break holding the instant: it already ends
    /// there (D147). No fact is needed, for nothing is written.
    AtEnd(HeldBreak),
    /// At the start of every break holding the instant: refused by name (the campaign's call inside D147, as P139 at
    /// a D129-ended break's start: a re-time there would leave no minutes).
    AtStart(Vec<HeldBreak>),
    /// Strictly inside exactly one held break, at an instant the kernel does not read as its re-time (no
    /// [`HeldBreak::retime_from`]): refused by name, saying what is in the way.
    NotRead(HeldBreak),
    /// Held by more than one break's closed span, or past the ends of more than one inside the widest end each one's
    /// lines gave it: which one the instant names is not clear, and a line may move nothing. Refused, naming each.
    Many(Vec<HeldBreak>),
    /// Past its end, at or before the end its own lines gave it ([`HeldBreak::out_to`], the owner's D150 as D151 narrows
    /// it), no closed span holding the instant: an earlier re-time shortened it, and the instant re-times it out.
    Out(HeldBreak),
    /// Past its end, inside [`HeldBreak::widest`], but the kernel does not read a line there (no
    /// [`HeldBreak::out_to`]): refused by name, saying what is in the way.
    OutNotRead(HeldBreak),
}

/// The end a re-timing line typed at `at` gives `b`: its start plus whole minutes, as the line's `actual_min` is.
fn line_end(b: &HeldBreak, at: DateTime<FixedOffset>) -> DateTime<FixedOffset> {
    b.started + chrono::Duration::minutes((at - b.started).num_minutes().max(0))
}

/// The one `break` line that re-times `b` to `at`, in the fork's shape: `t` its own start, its planned minutes, `actual_min`
/// the whole minutes from its start, its place — what the kernel reads as its re-time ([`HeldBreak::retime_from`]).
fn retiming_line(b: &HeldBreak, at: DateTime<FixedOffset>) -> log::LogEntry {
    log::LogEntry::new(
        b.started,
        Event::Break {
            planned_min: b.planned_min,
            actual_min: Some((at - b.started).num_minutes().max(0) as u32),
            r#where: b.place.clone(),
        },
    )
}

/// **The gate, per typed instant** (the W-54 third repair; the rule of README gap 5990, over track K's fact). `held` is
/// the kernel's list, newest first. `None`: outside every held break's closed span and every widest end, so a break
/// begins (D147, D151).
///
/// * One closed span holds `at`: at its end [`AtFinished::AtEnd`]; at its start [`AtFinished::AtStart`]; inside it
///   [`AtFinished::Inside`] when `retime_from` reads the line, else [`AtFinished::NotRead`]. A line typed under a minute past
///   the start would end the break at its start, so it is at its start; an instant under a minute before the end is at its end
///   (a line carries whole minutes from the start, and would take a minute off a reply that reads as no change, README gap 6053).
/// * Several hold it: [`AtFinished::AtStart`] at the start of all of them, else [`AtFinished::Many`].
/// * None holds it: the breaks past whose end it lies inside their widest end. One: [`AtFinished::Out`] when `out_to` reaches
///   it, else [`AtFinished::OutNotRead`]; a line typed under a minute past its end changes nothing ([`AtFinished::AtEnd`]),
///   and one whose whole-minute end another closed span holds may move nothing ([`AtFinished::Many`]). Several:
///   [`AtFinished::Many`].
fn at_finished(held: &[HeldBreak], at: DateTime<FixedOffset>) -> Option<AtFinished> {
    let by_span = |mut bs: Vec<HeldBreak>| {
        bs.sort_by_key(|b| (b.started, b.ended));
        bs
    };
    let holding = by_span(held.iter().filter(|b| b.started <= at && at <= b.ended).cloned().collect());
    match holding.as_slice() {
        [] => {
            let past = by_span(held.iter().filter(|b| b.ended < at && at <= b.widest).cloned().collect());
            match past.as_slice() {
                [] => None,
                [b] => {
                    let end = line_end(b, at);
                    let others: Vec<HeldBreak> =
                        held.iter().filter(|o| *o != b && o.started <= end && end <= o.ended).cloned().collect();
                    Some(if end <= b.ended {
                        AtFinished::AtEnd(b.clone())
                    } else if !others.is_empty() {
                        AtFinished::Many(by_span(others.into_iter().chain([b.clone()]).collect()))
                    } else if b.out_to.is_some_and(|o| at <= o) {
                        AtFinished::Out(b.clone())
                    } else {
                        AtFinished::OutNotRead(b.clone())
                    })
                }
                _ => Some(AtFinished::Many(past)),
            }
        }
        [b] if at == b.ended => Some(AtFinished::AtEnd(b.clone())),
        [b] if line_end(b, at) == b.started => Some(AtFinished::AtStart(vec![b.clone()])),
        [b] if b.ended - at < chrono::Duration::minutes(1) => Some(AtFinished::AtEnd(b.clone())),
        [b] if b.retime_from.is_some_and(|r| r <= at) => Some(AtFinished::Inside(b.clone())),
        [b] => Some(AtFinished::NotRead(b.clone())),
        many if many.iter().all(|b| b.started == at) => Some(AtFinished::AtStart(holding)),
        _ => Some(AtFinished::Many(holding)),
    }
}

/// **What is in the way of a line for `b`, in words the fact bears out** (README gap 6024's refusals): a held break at
/// `b`'s stamp with `b`'s planned minutes answers such a line (an older twin); otherwise a break logged after `b` (`held`
/// is newest first) overlaps it, or let go of a stretch that meets it (`Replay.frozen`, D129's `newerMeets`), and the
/// kernel reads the line as a break of its own. The fact does not say which; those it could be are named.
fn in_the_way(held: &[HeldBreak], b: &HeldBreak, span: &dyn Fn(&HeldBreak) -> String) -> String {
    let twin = held.iter().find(|o| *o != b && o.started == b.started && o.planned_min == b.planned_min);
    if let Some(o) = twin {
        return format!(
            "another logged break, {}, has its start and its length, so a line cannot name this one",
            span(o)
        );
    }
    let after: Vec<String> = held
        .iter()
        .take_while(|o| *o != b)
        .filter(|o| o.ended < b.ended || (o.started < b.ended && b.started < o.ended))
        .map(span)
        .collect();
    match after.as_slice() {
        [] => "a break logged after it stands in the way".to_string(),
        [one] => format!("the break {one}, logged after it, overlaps it or let go of a stretch that meets it"),
        many => format!(
            "of the breaks logged after it, one of {} overlaps it or let go of a stretch that meets it",
            many.join(", ")
        ),
    }
}

/// **The drawn Break piece holding `at` strictly inside, which no held break's span accounts for** — the kernel's drawn
/// segments against its held list: the defence of the gate's last arm. A drawn piece lies inside a held break while the
/// kernel holds it; a break past D94's bound (`Replay.pruneBrks`, 32 ledger days) is drawn and no longer held, and an
/// instant inside it must not begin a break (README gap 6043).
fn drawn_break_at(
    segments: &[&tm_core::log::LogSegment],
    at: DateTime<FixedOffset>,
) -> Option<(DateTime<FixedOffset>, DateTime<FixedOffset>)> {
    segments
        .iter()
        .filter(|s| matches!(s.kind, tm_core::log::SegmentKind::Break { .. }) && s.start < at && at < s.end)
        .max_by_key(|s| s.start)
        .map(|s| (s.start, s.end))
}

/// **The one `break` line that ends a break D129 ended at `at`** (D141): `t` its own start, its planned minutes and place,
/// `actual_min` the whole minutes from its start.
fn ending_line(b: &tm_core::log::EndedBreak, at: DateTime<FixedOffset>) -> log::LogEntry {
    log::LogEntry::new(
        b.started,
        Event::Break {
            planned_min: b.planned_min,
            actual_min: Some((at - b.started).num_minutes().max(0) as u32),
            r#where: b.r#where.clone(),
        },
    )
}

/// **The day as a line can move it**: every segment the kernel draws, its touching Break pieces merged, because a break's row cut
/// in two where the union stands is the same wall clock (README gap 6052).
fn the_day_drawn(r: &tm_core::log::Replay) -> Vec<tm_core::log::LogSegment> {
    let mut drawn: Vec<tm_core::log::LogSegment> = vec![];
    let mut all: Vec<_> = r.days.values().flat_map(|d| d.segments.iter().cloned()).collect();
    all.sort_by_key(|s| s.start);
    for s in all {
        let is_break = matches!(s.kind, tm_core::log::SegmentKind::Break { .. });
        match drawn.last_mut() {
            Some(l) if is_break && matches!(l.kind, tm_core::log::SegmentKind::Break { .. }) && s.start <= l.end => {
                l.end = l.end.max(s.end);
            }
            _ => drawn.push(s),
        }
    }
    drawn
}

/// **The wall-clock minutes the day's Break rows cover**, each minute once however many breaks draw it.
fn break_minutes_drawn(r: &tm_core::log::Replay) -> i64 {
    let mut spans: Vec<_> = r
        .days
        .values()
        .flat_map(|d| d.segments.iter())
        .filter(|s| matches!(s.kind, tm_core::log::SegmentKind::Break { .. }))
        .map(|s| (s.start, s.end))
        .collect();
    spans.sort();
    let mut total = chrono::Duration::zero();
    let mut reach: Option<DateTime<FixedOffset>> = None;
    for (from, to) in spans {
        let from = reach.map_or(from, |r| r.max(from));
        if to > from {
            total += to - from;
            reach = Some(to);
        }
    }
    total.num_minutes()
}

/// **Whether the kernel, reading this line, draws another day** — asked over the line held, nothing reaching the disk (the
/// W-54 third repair, README gaps 6045 and 6052). Track K's fact merges identical twins into one entry and a line moves only
/// the newest, so a twin the fact cannot show keeps the union drawn: "re-timed" would move nothing; and a D141 end inside a
/// break that still covers the rest gives no minute back. Read off the kernel's own drawn segments, never a line of the log (§5.3).
fn a_line_moves(ctx: &mut Ctx, entry: &log::LogEntry) -> Result<bool, CliError> {
    let line = Ctx::render_entry(entry)?;
    let before = the_day_drawn(&ctx.replay);
    ctx.hold_begin()?;
    let asked = ctx.append_line(&line).and_then(|()| ctx.reload());
    let moved = asked.map(|()| the_day_drawn(&ctx.replay) != before);
    ctx.release();
    moved
}

/// **A length typed inside a held break's closed span** (the W-54 third repair, README gap 6050; clause 4 of the break invariant),
/// when no later start, closed block it would net or passed end has logged it finished already. At a held break's very end the
/// instant is outside it, and a break begins after it, with nothing lost.
#[derive(Clone, Debug, PartialEq)]
enum LengthInHeld {
    /// No closed span holds it, or nothing is at stake: no block open at the instant and no typed-time line at or past it
    /// (README gap 6044's shape, the owner's call). A break begins, as before.
    Begins,
    /// Its typed end lies at or before the span's end or the log's latest typed-time stamp: a break already over, logged
    /// finished beside the one that holds it. The break that holds it, with the latest end, and that reach.
    Over(HeldBreak, DateTime<FixedOffset>),
    /// Its typed end lies past both, so nothing says it is over; a break begun here would run on from inside the held break, and
    /// the minutes after that break's end would be gone (gap 5810's loss). Refused, with the latest end a length may reach.
    Past(HeldBreak, DateTime<FixedOffset>),
}

fn length_in_held(replay: &tm_core::log::Replay, at: DateTime<FixedOffset>, end: DateTime<FixedOffset>) -> LengthInHeld {
    let holder = replay.held_breaks.iter().filter(|b| b.started <= at && at < b.ended).max_by_key(|b| b.ended);
    let Some(holder) = holder else {
        return LengthInHeld::Begins;
    };
    let block = replay.open_block.as_ref().is_some_and(|b| b.started <= at);
    if !block && replay.latest_t.map_or(true, |t| t < at) {
        return LengthInHeld::Begins;
    }
    let reach = replay.latest_t.map_or(holder.ended, |t| t.max(holder.ended));
    if end <= reach {
        LengthInHeld::Over(holder.clone(), reach)
    } else {
        LengthInHeld::Past(holder.clone(), reach)
    }
}

/// **Whether the kernel would read a finished `break` line typed at this instant as a break of its own** — asked over the line
/// held, nothing reaching the disk (the W-54 third repair, README gap 6051). `Err` names the break at this stamp when it would
/// not: a `break` line at a D129 ending's stamp that is not that ending's D141 line is read as P127's own line (`Replay.letGo`), its
/// minutes ignored, so the length would be gone under a reply saying "logged finished". Only a stamp a held break already
/// starts at can be misread; the fact is read before and after, never a line of the log (§5.3).
fn a_finished_line_is_read(ctx: &mut Ctx, minutes: u32, place: &Option<String>) -> Result<Result<(), HeldBreak>, CliError> {
    let at = ctx.now;
    let Some(there) = ctx.replay.held_breaks.iter().find(|b| b.started == at).cloned() else {
        return Ok(Ok(()));
    };
    let end = at + chrono::Duration::minutes(i64::from(minutes));
    let line = Ctx::render_entry(&log::LogEntry::new(
        at,
        Event::Break { planned_min: minutes, actual_min: Some(minutes), r#where: place.clone() },
    ))?;
    ctx.hold_begin()?;
    let asked = ctx.append_line(&line).and_then(|()| ctx.reload());
    let read = asked.map(|()| ctx.replay.held_breaks.iter().any(|b| b.started == at && b.ended == end));
    ctx.release();
    Ok(if read? { Ok(()) } else { Err(there) })
}

/// **What a length typed at this instant would do**, in the words of a refusal's advice: asked of the kernel over the
/// same held `break_start` the starting arm asks ([`followed_by_a_start`], [`netted_closed_block`],
/// [`inside_running_block`], [`length_in_held`]), nothing reaching the disk. `Some` when it logs a finished break, with the
/// rule; `None` when the kernel would not read the line as one (README gap 6051) or it would begin a running break inside the
/// held one (README gap 6044, the behaviour of gap 5775's row), which no refusal offers.
fn a_length_here(ctx: &mut Ctx) -> Result<Option<String>, CliError> {
    let minutes = 1;
    if a_finished_line_is_read(ctx, minutes, &None)?.is_err() {
        return Ok(None);
    }
    let cached = BreakState { started: Some(ctx.now_tz.time()), planned_min: minutes, place: None };
    let line = Ctx::render_entry(&log::LogEntry::new(ctx.now, Event::BreakStart { planned_min: minutes, r#where: None }))?;
    let (followed, held) = followed_by_a_start(ctx, &line, &cached)?;
    Ok(if followed.is_some() {
        Some("type a length to log a finished break beside it (D143)".to_string())
    } else if netted_closed_block(&ctx.replay, &held).is_some() {
        Some("type a length to log a finished break beside it (D149)".to_string())
    } else if inside_running_block(&ctx.replay, ctx.now, ctx.now + chrono::Duration::minutes(i64::from(minutes))).is_some() {
        Some("type a length the log has already passed to log a finished break beside it (D152)".to_string())
    } else {
        let end = ctx.now + chrono::Duration::minutes(i64::from(minutes));
        match length_in_held(&ctx.replay, ctx.now, end) {
            LengthInHeld::Over(_, reach) => Some(format!(
                "type a length that ends by {} to log a finished break beside it",
                reach.with_timezone(&ctx.cfg.tz).format("%H:%M")
            )),
            _ => None,
        }
    })
}

/// **The closed block a held running break would net** — the owner's **D149** (stage 6 W-54 track H, parity
/// **P147**): the kernel's own reading of a `break_start` stamped inside a block a later `done` or `stop` closed is to
/// net that block from the break's start (D129, README gap 5180), so an item whose block minutes the HELD replay
/// (`held`, [`followed_by_a_start`]'s) counts below the replay before the hold (`before`) is the block the break lies
/// inside. Both readings are the kernel's ([`Replay::block_minutes`], the minutes of CLOSED blocks: an open block's
/// minutes are its [`OpenBlock`]'s, so a break typed inside the running block nets nothing here and runs as before).
/// `None` when the held break nets no closed block — it begins after every block it could lie in.
///
/// [`Replay::block_minutes`]: tm_core::log::Replay::block_minutes
/// [`OpenBlock`]: tm_core::log::OpenBlock
fn netted_closed_block(before: &tm_core::log::Replay, held: &tm_core::log::Replay) -> Option<String> {
    before
        .items
        .keys()
        .find(|k| held.block_minutes(k) < before.block_minutes(k))
        .cloned()
}

/// **The RUNNING block a backdated finished break lies inside** — the owner's **D152** (stage 6 W-54 repair track H,
/// parity **P149**) as **D153** and **D154** read "already over": with a length typed, no later logged `start` (D143) and
/// no closed block it would net (D149), a break typed at an instant at or after the open block's own `start`
/// ([`OpenBlock::started`], the kernel's) whose typed end (`end`) the log has ALREADY passed — the latest of its TYPED-TIME
/// lines, at or after `end` ([`Replay::latest_t`], the kernel's `log.latestTyped`: undone lines and undo lines count, and a
/// `wake`, an `arrive`, an `energy` and a line past D18's fence do not, README gap 6031), never the last line in file order —
/// is a break already over: the length typed is a fact. Answers the open block's item. `None` with no block open, an instant
/// before its start, or a typed end no such line has reached (a break that may still be running: it begins as before — the
/// owner's own D152 drive with nothing logged after the block's start, README gaps 5892 and 5998). `--now` is the verb's
/// only clock, so "already over" is what the log witnesses.
///
/// [`OpenBlock::started`]: tm_core::log::OpenBlock::started
/// [`Replay::latest_t`]: tm_core::log::Replay::latest_t
fn inside_running_block(
    replay: &tm_core::log::Replay,
    at: DateTime<FixedOffset>,
    end: DateTime<FixedOffset>,
) -> Option<String> {
    let open = replay.open_block.as_ref().filter(|b| b.started <= at)?;
    replay.latest_t.filter(|t| *t >= end).map(|_| open.id.clone())
}

/// `tm break [20m] [--where walk]` — starts a break, or ends the running one.
///
/// With no break running and no length typed, an instant at or inside a break the log already holds is read by the
/// gate below (D141 for a break D129 ended, where the kernel's fact reads the line; D147, D150 and [`at_finished`] for every
/// held break, over track K's fact): it ends, re-times or re-times out exactly one held break, says that one already ends
/// there, or is refused by name — never a new break inside a held break's span. A length typed for a break already over is
/// logged finished (D143, D146, D148, D149, D152 as D153 and D154 read "already over"), and so is one typed inside a held
/// break's span that ends by that span's end or the log's latest stamp (README gap 6050); one that ends past both is refused,
/// and so is one the kernel would not read as a break of its own (README gap 6051). Otherwise a break begins (D105's
/// `break_start`), inside a held break's span only when nothing is at stake there (README gap 6044, the owner's call).
pub fn take_break(g: &Globals, args: &super::BreakArgs) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    // **The arguments are read in both arms** (the owner's D20, gap 138). The
    // running-break arm used to take its branch before it ever looked at
    // `args.dur`, so `tm break zzzz` was refused by name on a fresh tree and
    // silently accepted — ending the break, discarding both arguments and
    // exiting 0 — when a break was running. One verb, two acceptances, and a
    // user could not tell which they had got. Parsing here, ahead of the
    // branch, refuses the same spelling in both arms.
    //
    // D20 also settles what a *valid* argument does to a running break:
    // **nothing**. `tm break 20m` with a break running still just ends it;
    // retiming was considered and declined as a new feature, so `asked` is
    // read by the starting arm alone.
    let asked = match &args.dur {
        Some(s) => Some(dur(s, ctx.block_min())?.as_minutes()),
        None => None,
    };
    // **`--where` names a place of the ONE table, in both arms** — the
    // campaign's D81 call on README gap 3903 (parity P75), D20's shape: an
    // unknown word was stored, and the planner's request refuses it by name
    // (`PlanWire.placeOf?`, `badBreak place`), so a typo in `--where` would stop
    // `tm plan` after R3. Read here, ahead of the branch, so the running arm
    // refuses it too — and, as D20 settles for every valid argument, a valid
    // place does nothing to a running break. **The table is the kernel's** since
    // the owner's D111 (README gap 4904, parity P108): the one the log's grammar
    // reads a `break_start`'s place through, asked of the kernel
    // (`kernel_log::places`) only when a place was given.
    let place = match args.place.as_deref() {
        Some(word) => {
            let table = super::kernel_log::places()
                .map_err(|e| CliError::Kernel(super::kernel_bridge::fault_issue(&e, "")))?;
            if !table.iter().any(|w| w == word) {
                return Err(CliError::msg(format!(
                    "unknown break place {word:?} — `--where` is one of {} (§12.6)",
                    table.join(", ")
                )));
            }
            Some(word.to_string())
        }
        None => None,
    };
    // **At the very start of a break a later start ended, `tm break` is refused by name** — stage 6 W-52
    // repair track R, the campaign's call (revisable by the owner), parity **P139**. With no break running
    // (the fact is empty while one runs), `tm break --now <t>` at the instant a logged break D129 ended
    // began would log a second `break_start` wholly inside it — the critic's B2: the next `tm break` then
    // named the first break and the kernel ended the second. D141 forbids a second break inside the first,
    // and an end AT the start is no break at all, so the verb says which break this is and how to end it,
    // and writes nothing (D20's shape).
    if let Some(x) = ctx.ended_break_starting_at(ctx.now) {
        let tz = ctx.cfg.tz;
        let hm = |t: DateTime<FixedOffset>| t.with_timezone(&tz).format("%H:%M").to_string();
        return Err(CliError::msg(format!(
            "a break began at {} and the `start` the log holds at {} ended it (D129) — `tm break` at its own \
             start would begin a second break inside it; {}",
            hm(x.started),
            hm(x.ended),
            // A line ends it only a whole minute or more past its start, and before its end (README gap 6056): on an ending
            // a minute long or less no such instant exists, so the advice is the one that does what it says.
            if x.ended - x.started <= chrono::Duration::minutes(1) {
                format!(
                    "nothing written: a line carries whole minutes from its start, so no instant before {} can end it — `tm undo` \
                     takes the last line back, one line at a time, until that break's line is gone (D141)",
                    hm(x.ended)
                )
            } else if ctx.a_line_ends(&x) {
                format!("give a later instant, before {}, to end it there (D141)", hm(x.ended))
            } else {
                "nothing written: a later break let go of a stretch that meets it, so a line would not end it — `tm undo` \
                 takes the last line back, one line at a time, until that break's line is gone (D141)"
                    .to_string()
            },
        )));
    }
    super::kernel_bridge::gate(&ctx, "break")?;
    let rec = Recorder::start(&ctx, "break")?;
    let replay_before = ctx.replay.clone();
    // The ending arm is the one body every verb that ends a break runs (the owner's D97):
    // `end_break_first`, then `note_break_ended` below.
    let ended = end_break_first(&mut ctx)?;
    // **While a break runs, a `tm break` typed BEFORE it began is refused by name** — the campaign's call at stage 6
    // W-54 track H (README gap 5896, revisable by the owner). The ending arm above ends the running break only at an
    // instant at or after its start; before it, with no length typed, the verb used to fall through to D147's gate —
    // whose fact the kernel empties while a break runs since W-54 track K — and either said "re-timed" for a line the
    // kernel re-times nothing with and that cleared the running break (the W-53 repair critic's third note, gap 5820's
    // damage), or began a second `break_start` that D129 ran to the next start while the cached running break was
    // dropped (`tm now` then "nothing running"). The owner's D145 (built at W-54 repair track K) makes a FINISHED line
    // end only its own break, but the kernel reads no re-time and no D141 end while another break runs (README gap
    // 5921: `open.finished` and `open.ended` stay empty then), so the verb names the running break and writes nothing.
    // A LENGTH typed here keeps D143, D148, D149 and D152 — a finished break logged beside the running one, which
    // stays running in the replay and the cache — so the refusal points to it (gap 5910's advice, restored at the W-54
    // repair's land); a length that would BEGIN a break is refused below, in the starting arm.
    if ended.is_none() && asked.is_none() {
        if let Some(running) = ctx.state.break_.as_ref().and_then(|_| ctx.running_break()) {
            return Err(CliError::msg(format!(
                "a break is running since {} — `tm break` at {}, before it began, would end, re-time or begin a logged \
                 break while it runs; end the running break first (`tm break`) — a length typed for a break already over \
                 inside a block is logged finished beside it (D143, D145)",
                running.format("%H:%M"),
                ctx.now_tz.format("%H:%M"),
            )));
        }
    }
    // **A break a later start already ended, typed inside, ENDS THERE** — the owner's **D141** (README gap
    // 5633, stage 6 W-52 track H, parity **P138**). With no break running, a `tm break` typed at an instant
    // inside a logged break that D129 ended at a later block's `start`, and that no `break` line has ended
    // yet ([`Ctx::break_a_start_ended_at`]), is that break's end: its `break` line is written at the typed
    // instant in the shape every break end has (`t` the break's start, `actual_min` the typed instant less
    // it, its planned minutes and place — `end_break_at`'s, through the kernel's writer, D16), with the
    // journal line and the human clause every break end writes (D97, D101). It never logs a second
    // `break_start` inside the first, which is what this verb did until D141 (the W-51 auditor's J drive:
    // `tm plan` drew `09:30 break 40m` and `09:40 break 30m`). With no length typed, D20 settles what a
    // valid argument does here as in the other ending arm: nothing — the place is not the ended break's.
    // **With a length typed it applies D141 AND D143** — the owner's **D146** (stage 6 W-53 repair track H,
    // parity **P144**, withdrawing the campaign's interim call of README gap 5682): the break D129 ended is
    // ended at the typed instant as above, and a finished break of the typed length, with the typed place,
    // is logged from it in one plain `break` line (below) — the typed length of a break already over is a
    // fact (D143), where until W-53's repair the length and the place were discarded.
    //
    // **Where another closed span also holds the instant, a D141 line may move nothing** (the W-54 third repair, README gap 6052):
    // `09:40` and `09:30`, both D129 to 10:10, then `--now 09:45` said "ends here" with no minute back. So it is asked: a line that
    // moves nothing stands aside (the gate below refuses it by name, and a length logs a break of its own); one that does move (a
    // shorter break nested inside, `09:40 5m`) ends the break, and the reply says what still holds the instant.
    let superseded = if ended.is_none() {
        match ctx.break_a_start_ended_at(ctx.now) {
            Some(b) if matches!(at_finished(&ctx.replay.held_breaks, ctx.now), Some(AtFinished::Many(_))) => {
                let line = ending_line(&b, ctx.now);
                if a_line_moves(&mut ctx, &line)? { Some(b) } else { None }
            }
            found => found,
        }
    } else {
        None
    };
    let tz = ctx.cfg.tz;
    // **A no-length `tm break` at or inside a break already logged FINISHED re-times it** — the owner's **D147**
    // (stage 6 W-53 repair track H, parity **P145**, README gaps 5772 and 5810; track K's P143 reads the line). With
    // nothing ended above (no running break this instant ends, no break D129 ended around it — D141 and D146 come
    // first) and no length typed, an instant strictly inside a finished break's own span becomes its end: one more
    // `break` line in the fork's shape, `t` that break's own start, its planned minutes, `actual_min` the typed
    // instant less its start, its place — which the kernel reads as that break's reading, the later line at one
    // stamp winning (D141's rule reaching a finished break, D100's later fact), giving back what the shorter break
    // no longer takes (D137). At its end the instant changes nothing and the verb says so, writing nothing; at its
    // own start it is refused by name (the campaign's call inside D147: re-timing there would leave a zero-minute
    // break, as P139 refuses at a D129-ended break's start). A LENGTH typed at or inside a finished break keeps
    // D143: a new finished break (README gap 5849). Outside every held break, a break begins as before (below).
    //
    // **D150** (stage 6 W-54 track H, parity **P148**): past a finished break's CURRENT end but at or before the end its own
    // lines gave it (D151; an earlier re-time shortened it), the instant re-times it OUT — the same one line, `actual_min` the
    // typed instant less its start ([`AtFinished::Out`]).
    //
    // **One instant, at most one held break — the gate's rule** (stage 6 W-54 second repair track H, the W-54 repair's
    // verifiers' D-1 to D-3; the campaign's call, revisable by the owner; read since the W-54 third repair off track K's fact,
    // [`Replay::held_breaks`], one entry per held break by its own span, [`at_finished`]). Inside exactly one held break at an
    // instant its range reads, D147; past its end inside `out_to`, D150, over any break between; at its own end with no other
    // break there, "already ends", nothing written, whether or not a line could be read; at its start, inside it at an instant
    // the range does not read, past its end inside its widest end with no `out_to`, or meeting more than one break, refused by
    // name, each break by its own span, nothing written; outside every closed span and widest end a break begins as before.
    // A line that would draw the day as it is (a twin the fact merges, README gap 6045) is refused too ([`a_line_moves`]), so
    // "re-timed" means moved. No log line is read here (§5.3).
    //
    // [`Replay::held_breaks`]: tm_core::log::Replay::held_breaks
    let retimed = if ended.is_none() && superseded.is_none() && asked.is_none() {
        let held = ctx.replay.held_breaks.clone();
        let segments: Vec<_> = ctx.replay.days.values().flat_map(|d| d.segments.iter()).cloned().collect();
        let at = at_finished(&held, ctx.now);
        let hm = |t: DateTime<FixedOffset>| t.with_timezone(&tz).format("%H:%M").to_string();
        let span = |b: &HeldBreak| format!("{}–{}", hm(b.started), hm(b.ended));
        let typed = ctx.now_tz.format("%H:%M").to_string();
        // Each refusal's advice is what the keystroke does here: a length is offered only when it logs a finished break
        // (asked of the kernel), and `tm undo` takes the last line back, which re-opens what the line in the way closed.
        let moves = match &at {
            Some(AtFinished::Inside(f) | AtFinished::Out(f)) => {
                let line = retiming_line(f, ctx.now);
                a_line_moves(&mut ctx, &line)?
            }
            _ => true,
        };
        let length = match at {
            Some(AtFinished::AtStart(_) | AtFinished::NotRead(_) | AtFinished::Many(_) | AtFinished::OutNotRead(_)) => {
                a_length_here(&mut ctx)?
            }
            Some(AtFinished::Inside(_) | AtFinished::Out(_)) if !moves => a_length_here(&mut ctx)?,
            _ => None,
        };
        let now = ctx.now;
        let edge = |b: &HeldBreak| {
            if b.started == now {
                "its start"
            } else if b.ended == now {
                "its end"
            } else if b.ended < now {
                "past its end, inside the end its own lines gave it"
            } else {
                "inside it"
            }
        };
        let named = |bs: &[HeldBreak]| bs.iter().map(|b| format!("{} ({})", span(b), edge(b))).collect::<Vec<_>>().join(", ");
        const UNDO: &str = "`tm undo` takes the last line back, one line at a time, until the lines that overlap are gone";
        let advice = match &length {
            Some(l) => format!("{l}, or {UNDO}"),
            None => UNDO.to_string(),
        };
        let refusal = match &at {
            Some(AtFinished::AtStart(bs)) => Some(match bs.as_slice() {
                [b] => format!(
                    "a break is logged {} — `tm break` at its own start would leave it no minutes; nothing written: {} (D147)",
                    span(b),
                    if b.ended - b.started < chrono::Duration::minutes(2) {
                        // Under a minute past the start is at the start and under a minute before the end is at the end, so a
                        // break under two minutes has no instant a line re-times it at (README gap 6056).
                        let undo = "`tm undo` takes the last line back, one line at a time, until its line is gone";
                        format!(
                            "a line carries whole minutes from its start, so no instant inside it can end it: {}",
                            match &length {
                                Some(l) => format!("{l}, or {undo}"),
                                None => undo.to_string(),
                            }
                        )
                    } else if b.retime_from.is_some() {
                        "give an instant inside it to end it there".to_string()
                    } else {
                        format!("{}: {advice}", in_the_way(&held, b, &span))
                    },
                ),
                bs => format!(
                    "breaks are logged {} — `tm break` at their own start would leave them no minutes, and which one it \
                     names is not clear; nothing written: {advice} (D147)",
                    bs.iter().map(&span).collect::<Vec<_>>().join(" and "),
                ),
            }),
            Some(AtFinished::Many(bs)) => Some(format!(
                "`tm break` at {typed} meets more than one logged break — {} — and cannot tell which to re-time (D147); \
                 nothing written: {advice}",
                named(bs),
            )),
            Some(AtFinished::NotRead(b)) => Some(format!(
                "`tm break` at {typed} lies in the break {} — {}, so the kernel would read a line there as a break of \
                 its own and the break would not move (D147); nothing written: {advice}",
                named(std::slice::from_ref(b)),
                in_the_way(&held, b, &span),
            )),
            Some(AtFinished::OutNotRead(b)) => Some(format!(
                "`tm break` at {typed} lies past the end of the break {}, inside the {} its own lines gave it — {}, so \
                 the kernel would read a line there as a break of its own and the break would not move (D150); nothing \
                 written: {advice}",
                span(b),
                hm(b.widest),
                in_the_way(&held, b, &span),
            )),
            Some(AtFinished::Inside(f) | AtFinished::Out(f)) if !moves => Some(format!(
                "`tm break` at {typed} would re-time the break {}, and the day would be drawn as it is — the log holds \
                 that break twice and a line moves only one of them (D147); nothing written: {advice}",
                span(f),
            )),
            _ => None,
        };
        if let Some(refusal) = refusal {
            return Err(CliError::msg(refusal));
        }
        match at {
            Some(AtFinished::Inside(f)) => Some((f, false)),
            Some(AtFinished::Out(f)) => Some((f, true)),
            Some(AtFinished::AtEnd(f)) => {
                let (from, until) = (f.started.with_timezone(&tz), f.ended.with_timezone(&tz));
                let out = BreakOut {
                    action: "unchanged".to_string(),
                    planned_min: f.planned_min,
                    actual_min: Some((f.ended - f.started).num_minutes().max(0) as u32),
                    place: f.place,
                    superseded_end: None,
                    finished: None,
                    ended_from: None,
                };
                emit(
                    ctx.json,
                    || {
                        format!(
                            "break {}–{} already ends at {} — nothing written (D147)",
                            from.format("%H:%M"),
                            until.format("%H:%M"),
                            until.format("%H:%M")
                        )
                    },
                    &out,
                )?;
                return Ok(0);
            }
            _ => {
                let segments: Vec<_> = segments.iter().collect();
                if let Some((from, until)) = drawn_break_at(&segments, ctx.now) {
                    return Err(CliError::msg(format!(
                        "a break is drawn {}–{} here that the kernel no longer holds (past its bound of held breaks) — \
                         `tm break` would begin a break inside it; nothing written (D147)",
                        hm(from),
                        hm(until),
                    )));
                }
                None
            }
        }
    } else {
        None
    };
    // **The finished break this run logs** (D143, D146, D148): its typed length, and the later `start` D129
    // would have ended it at when it runs past that start (D148).
    let mut finished: Option<(u32, Option<DateTime<FixedOffset>>)> = None;
    // The start of the finished break this run re-timed (D147), `HH:MM`, and whether it re-timed it OUT (D150).
    let mut retimed_from: Option<String> = None;
    let mut retimed_to: Option<String> = None;
    let mut retimed_out = false;
    // The held break a finished break this run logs lies inside, when no block names why it is over (README gap 6050).
    let mut inside_break: Option<String> = None;
    // Whether the log's latest typed-time stamp has reached that finished break's typed end (the reply says so only then), and whether
    // the break runs past the end of the span named (README gap 6060).
    let mut inside_passed = false;
    let mut runs_past_held = false;
    // The block a finished break this run logs lies inside, that a later `done` or `stop` closed (D149).
    let mut inside_block: Option<String> = None;
    // The RUNNING block a finished break this run logs lies inside, its typed end already passed (D152).
    let mut inside_running: Option<String> = None;
    // Whether the context must be read again after this run's lines (not when it holds the replay of them).
    let mut reread = true;
    let mut out = if let Some(ended) = ended {
        ctx.save_state()?;
        ended
    } else if let Some((f, out_)) = retimed {
        let actual = (ctx.now - f.started).num_minutes().max(0) as u32;
        retimed_from = Some(f.started.with_timezone(&tz).format("%H:%M").to_string());
        retimed_to = Some(line_end(&f, ctx.now).with_timezone(&tz).format("%H:%M").to_string());
        retimed_out = out_;
        ctx.append_entry(&retiming_line(&f, ctx.now))?;
        BreakOut {
            action: "retimed".to_string(),
            planned_min: f.planned_min,
            actual_min: Some(actual),
            place: f.place,
            superseded_end: Some(f.ended.with_timezone(&tz).format("%H:%M").to_string()),
            finished: None,
            ended_from: None,
        }
    } else if let Some(b) = superseded {
        let actual = (ctx.now - b.started).num_minutes().max(0) as u32;
        // What else holds the instant keeps drawing: the reply says so, so "ends here" reads as what the plan will draw (README gap 6052).
        let also: Vec<String> = ctx
            .replay
            .held_breaks
            .iter()
            // The half-open rule the gate's lengths read: at its own end a break no longer holds the instant (README gap 6060).
            .filter(|h| h.started <= ctx.now && ctx.now < h.ended)
            .filter(|h| !(h.started == b.started && h.ended == b.ended && h.planned_min == b.planned_min))
            .map(|h| {
                let hm = |t: DateTime<FixedOffset>| t.with_timezone(&tz).format("%H:%M").to_string();
                format!("{}–{}", hm(h.started), hm(h.ended))
            })
            .collect();
        ctx.append_entry(&ending_line(&b, ctx.now))?;
        let (from, until) = (b.started.with_timezone(&tz), b.ended.with_timezone(&tz));
        eprintln!(
            "tm: the break that began at {} ends here, at {} — the `start` the log holds at {} had ended it \
             (D129); typed inside it, `tm break` ends it (D141){}",
            from.format("%H:%M"),
            (from + chrono::Duration::minutes(i64::from(actual))).format("%H:%M"),
            until.format("%H:%M"),
            if also.is_empty() {
                String::new()
            } else {
                format!("; the logged break {} also holds this instant, and stays", also.join(", "))
            },
        );
        if let Some(len) = asked {
            finished = Some((len, None));
        }
        BreakOut {
            action: "ended".to_string(),
            planned_min: b.planned_min,
            actual_min: Some(actual),
            place: b.r#where,
            superseded_end: Some(until.format("%H:%M").to_string()),
            finished: None,
            ended_from: None,
        }
    } else {
        let planned = asked.unwrap_or(ctx.cfg.day.break_min);
        let cached = BreakState {
            started: Some(ctx.now_tz.time()),
            planned_min: planned,
            place: place.clone(),
        };
        // **The break's START is logged** — the owner's **D105** (README "Stage 6 — W-46 track K", gaps 1034,
        // 1085 and 4740, parity **P100**): a `break_start` at `now`, its planned minutes and its place, written
        // by the kernel (D16) and read back by its replay as the running break, so `.tm/state.json`'s `break`
        // (and the pause it sets) is derivable and deleting the file mid-break changes nothing (D42). The log
        // first, then its cache. Fork 4748911 wrote no line until the break ENDED, so a running break lived in
        // the cache alone; the line that ends it (`end_break_at`) keeps the fork's shape.
        let line = Ctx::render_entry(&log::LogEntry::new(
            ctx.now,
            Event::BreakStart {
                planned_min: planned,
                r#where: place.clone(),
            },
        ))?;
        // **A backdated break with a LENGTH typed that a later logged `start` follows is logged FINISHED, in ONE
        // plain `break` line** — the owner's **D143** (parity **P140**, restated at stage 6 W-53 repair track H)
        // and **D148** (parity **P146**, closing README gap 5770). Whether a later start follows is the kernel's
        // answer for this break, asked over its `break_start` HELD so it never reaches the disk
        // ([`followed_by_a_start`]: D129, `open.ended`, never re-derived here, §5.3). The line written instead is
        // the fork's shape — `t` the break's start, `planned_min` and `actual_min` the typed length, its place —
        // with NO `break_start`, so the kernel reads it as any break line (D92: a break that runs into a block's
        // start nets the block by the minutes it runs into it; D100 inside a closed block), never as a running
        // break D129 ended and then its own line (P127's `letGo`, which kept D129's span and so read a length past
        // the start as twenty where the line said thirty, gap 5770). So the length typed is the break's whatever
        // start follows (D148 drops W-53's `fits` condition), nothing is left running, and `.tm/state.json` is
        // untouched — a break already running keeps running in it (D42, D145's host half).
        let probed = match asked {
            Some(_) => Some(followed_by_a_start(&mut ctx, &line, &cached)?),
            None => None,
        };
        // **A backdated break with a LENGTH typed inside a block a later logged `done` or `stop` already closed is
        // logged FINISHED, in the same one plain line** — the owner's **D149** (stage 6 W-54 track H, parity **P147**,
        // closing README gap 5860): D143's "a later logged block start follows it" widened to the closing line of the
        // block the break sits in. Whether it sits in one is the KERNEL's answer over the same held replay
        // ([`netted_closed_block`]: the running break the held `break_start` would be nets a closed block from its start,
        // D129's reading of a break begun inside one, README gap 5180), never re-derived from the log's lines here
        // (§5.3). The length is the break's whatever close it runs past: the kernel nets the block by the overlap (D100,
        // D148's rule), and a stopped block's `est:` is corrected below (D126).
        let closed = match &probed {
            Some((None, held)) => netted_closed_block(&ctx.replay, held),
            _ => None,
        };
        // **A backdated break with a LENGTH typed inside the RUNNING block, its typed end already passed, is logged
        // FINISHED, in the same one plain line** — the owner's **D152** (stage 6 W-54 repair track H, parity **P149**,
        // closing README gap 5892): D143's and D149's rule (the length a user types for a break already over is a fact)
        // reaching a block no later line has closed yet. Asked only when neither D143 nor D149 took it
        // ([`inside_running_block`]: the kernel's open block and the log's last stamp, never the log's lines here).
        // `.tm/state.json` is untouched, so the block stays running and unpaused (the replay nets it by the break's
        // minutes, D87, D100). A typed end the log has not reached stays a running break, as before. While a break
        // runs it is taken too (README gap 5942, lifted at the W-54 repair's land): since the owner's D145 (track K,
        // `Replay.brkPark`) the finished line ends only its own break, so the running break and its cache stay.
        let running_in = match (&probed, &closed) {
            (Some((None, _)), None) => {
                inside_running_block(&ctx.replay, ctx.now, ctx.now + chrono::Duration::minutes(i64::from(planned)))
            }
            _ => None,
        };
        // **A length typed inside a held break's closed span** (the W-54 third repair, README gap 6050; clause 4): asked only when
        // none of D143, D149 and D152 took it, for what those take reads no held break. `tm break --now 10:20 5m` inside a
        // 10:15–10:40 break the user ended, `^t4` running: the kernel's `latestTyped` reads that break's `break` line at its start
        // stamp, so D152 sees no witness of 10:25, and a `break_start` there took every minute after 10:40 from the block. The span's
        // own end is the witness: both lie in one stretch the log already reads as over. Past it, refused by name.
        let in_held = match (&probed, &closed, &running_in) {
            (Some((None, _)), None, None) => {
                length_in_held(&ctx.replay, ctx.now, ctx.now + chrono::Duration::minutes(i64::from(planned)))
            }
            _ => LengthInHeld::Begins,
        };
        let hm = |t: DateTime<FixedOffset>| t.with_timezone(&tz).format("%H:%M").to_string();
        if let LengthInHeld::Past(b, reach) = &in_held {
            // The cost is said only when there are minutes to take: a block open past the span (README gap 6060).
            let cost = match ctx.replay.open_block.as_ref().filter(|o| o.started <= ctx.now) {
                Some(o) => format!("a break begun here would take every minute of ^{} after {}", o.id, hm(b.ended)),
                None => "a break begun here would run on from inside that break".to_string(),
            };
            return Err(CliError::msg(format!(
                "`tm break {planned}m` at {} lies inside the logged break {}–{} and ends at {}, which neither that break nor the log \
                 has reached: nothing says it is over, and {cost}; nothing written: type a length that ends by {} to log a finished \
                 break beside it, or `tm undo` takes the last line back",
                ctx.now_tz.format("%H:%M"),
                hm(b.started),
                hm(b.ended),
                hm(ctx.now + chrono::Duration::minutes(i64::from(planned))),
                hm(*reach),
            )));
        }
        // At a held break's own start with its planned minutes, the kernel reads the line as THAT break's reading: not a finished break
        // beside it, and the reply would say so of a line that moved it (`10:15 20m` over 10:15–10:40). Refused, the re-time named.
        if let LengthInHeld::Over(..) = &in_held {
            if let Some(b) = ctx.replay.held_breaks.iter().find(|b| b.started == ctx.now && b.planned_min == planned) {
                return Err(CliError::msg(format!(
                    "a {planned}m break is logged {}–{} from this very instant — the kernel reads a `break` line with its start and \
                     its length as that break's own, not as a finished break beside it; nothing written: `tm break` at the instant \
                     it should end re-times it (D147), or a different length logs a finished break beside it",
                    hm(b.started),
                    hm(b.ended),
                )));
            }
        }
        // **Whatever arm logs it finished, the kernel must read the line as a break of its own** (README gap 6051): at a D129 ending's
        // own start it keeps D129's span and drops the length, under a reply that said it was logged and netted. P139 refuses that
        // instant when the ending is listed; this is the same refusal for one `ended_breaks` omits, a newer break overlapping it.
        let logs_finished = matches!(probed, Some((Some(_), _)))
            || closed.is_some()
            || running_in.is_some()
            || matches!(in_held, LengthInHeld::Over(..));
        if logs_finished {
            if let Err(there) = a_finished_line_is_read(&mut ctx, planned, &place)? {
                return Err(CliError::msg(format!(
                    "a break is logged {}–{} from this very instant — the kernel reads a `break` line at its stamp as that break's \
                     own line and keeps its span, so a {planned}m length here would be dropped; nothing written: give another \
                     instant for the length (D143), or `tm undo` takes the last line back, one line at a time",
                    hm(there.started),
                    hm(there.ended),
                )));
            }
        }
        match probed {
            Some((None, _)) if closed.is_some() || running_in.is_some() || matches!(in_held, LengthInHeld::Over(..)) => {
                if let LengthInHeld::Over(b, _) = &in_held {
                    let end = ctx.now + chrono::Duration::minutes(i64::from(planned));
                    inside_break = Some(format!("{}–{}", hm(b.started), hm(b.ended)));
                    inside_passed = ctx.replay.latest_t.is_some_and(|t| t >= end);
                    runs_past_held = end > b.ended;
                }
                finished = Some((planned, None));
                inside_block = closed;
                // D152's own name, and only D152's: this arm fired for a break it lies inside (README gap 6060).
                inside_running = running_in;
                BreakOut {
                    action: "finished".to_string(),
                    planned_min: planned,
                    actual_min: Some(planned),
                    place: place.clone(),
                    superseded_end: None,
                    finished: None,
                    ended_from: None,
                }
            }
            Some((Some((_, until)), _)) => {
                let len = planned;
                finished = Some((len, until.filter(|u| ctx.now + chrono::Duration::minutes(i64::from(len)) > *u)));
                BreakOut {
                    action: "finished".to_string(),
                    planned_min: len,
                    actual_min: Some(len),
                    place: place.clone(),
                    superseded_end: None,
                    finished: None,
                    ended_from: None,
                }
            }
            probed => {
                // A break that would BEGIN while one runs (a length typed before the running break's start, logged
                // finished by none of D143, D148 and D149) is refused by name, as the no-length keystroke is above
                // (README gap 5896): a second `break_start` would end or hide the running one (one break runs at a time).
                if let Some(running) = ctx.state.break_.as_ref().and_then(|_| ctx.running_break()) {
                    return Err(CliError::msg(format!(
                        "a break is running since {} — a break begun at {}, before it, would run beside it — one break runs \
                         at a time, and a finished line ends only its own (D145); end the running break first (`tm break`)",
                        running.format("%H:%M"),
                        ctx.now_tz.format("%H:%M"),
                    )));
                }
                ctx.append_line(&line)?;
                // The held replay is the replay of the log as just written: no second read.
                if let Some((None, held)) = probed {
                    ctx.replay = held;
                    reread = false;
                }
                ctx.state.break_ = Some(cached);
                if let Some(a) = ctx.state.active.as_mut() {
                    a.paused = true;
                }
                ctx.save_state()?;
                BreakOut {
                    action: "started".to_string(),
                    planned_min: planned,
                    actual_min: None,
                    place: place.clone(),
                    superseded_end: None,
                    finished: None,
                    ended_from: None,
                }
            }
        }
    };
    // **The finished break's one plain `break` line** (D143, D146, D148), from `now`: the typed length as its
    // planned and actual minutes, the typed place — through the kernel's writer (D16).
    let finished_out = match finished {
        Some((len, into)) => {
            let entry = log::LogEntry::new(
                ctx.now,
                Event::Break {
                    planned_min: len,
                    actual_min: Some(len),
                    r#where: place.clone(),
                },
            );
            ctx.append_entry(&entry)?;
            let end = (ctx.now + chrono::Duration::minutes(i64::from(len))).with_timezone(&tz);
            let f = FinishedBreak {
                start: ctx.now_tz.format("%H:%M").to_string(),
                end: end.format("%H:%M").to_string(),
                actual_min: len,
                place: place.clone(),
                into_start: into.map(|u| u.with_timezone(&tz).format("%H:%M").to_string()),
                inside_block: inside_block.clone(),
                inside_running: inside_running.clone(),
                inside_break: inside_break.clone(),
                adds_min: None,
                nets: None,
            };
            out.finished = Some(f.clone());
            Some((f, len, end))
        }
        None => None,
    };
    if reread || finished_out.is_some() {
        ctx.reload()?;
    }
    // **Whether the block a finished break lies inside counts fewer minutes for it** (D149, D152; stage 6 W-54 repair
    // track H, the W-54 critic's fourth note): the replay just read against the one read before the verb — a closed
    // block's minutes ([`Replay::block_minutes`]) for D149, the running block's minutes up to the break's end
    // ([`Replay::running_worked_min`]) for D152 — so the reply says "which it nets" only when they fell, never for a
    // break typed into the block's pause (critic d19: `^t1` 70 → 70).
    //
    // [`Replay::block_minutes`]: tm_core::log::Replay::block_minutes
    // [`Replay::running_worked_min`]: tm_core::log::Replay::running_worked_min
    if let (Some(f), Some((_, _, end))) = (out.finished.as_mut(), finished_out.as_ref()) {
        let end = end.fixed_offset();
        let brk = running_break_at(&ctx);
        f.nets = match (&f.inside_block, &f.inside_running) {
            (Some(k), _) => Some(ctx.replay.block_minutes(k) < replay_before.block_minutes(k)),
            (None, Some(k)) => Some(
                ctx.replay.running_worked_min(k, ctx.today, end, brk)
                    < replay_before.running_worked_min(k, ctx.today, end, brk),
            ),
            (None, None) => None,
        };
        if runs_past_held {
            f.adds_min = Some((break_minutes_drawn(&ctx.replay) - break_minutes_drawn(&replay_before)).max(0) as u32);
        }
    }
    // **A break a start already logged ends** (the owner's D129, README gap 5433): a break begun at an
    // instant before a block's `start` that the log already holds — a `--now` in the past after the
    // block, or a log merged from another machine — is ended at that start in stamp order, so it does
    // not run; the cache this verb just wrote is put right and the user is told where it ended. Since
    // W-53's repair this is reached by a break typed with NO length alone: one with a length that a start
    // follows was logged finished above (D143, D148).
    if out.action == "started" {
        if let Some((from, until)) = ctx.drop_break_a_start_ended() {
            ctx.save_state()?;
            match until {
                Some(until) => eprintln!(
                    "tm: the break that began at {} ended at {}, at the `start` the log already holds after it \
                     (D129) — it is not running",
                    from.with_timezone(&tz).format("%H:%M"),
                    until.with_timezone(&tz).format("%H:%M")
                ),
                None => eprintln!(
                    "tm: the break that began at {} was ended by a `start` the log already holds after it \
                     (D129) — it is not running",
                    from.with_timezone(&tz).format("%H:%M")
                ),
            }
        }
    }
    let start_note = |planned: u32, place: &Option<String>| {
        format!(
            "break {planned}m{}",
            place.as_ref().map(|p| format!(" where={p}")).unwrap_or_default()
        )
    };
    // The journal: an ended break's end (D97's one writer), a started break's start, and a finished break's
    // start and its end where it ended — after the end of the break D141 ended, when D146 logs both.
    match out.action.as_str() {
        "ended" | "retimed" => note_break_ended(&ctx, &mut out, ctx.now_tz)?,
        "started" => day_note(&ctx, start_note(out.planned_min, &out.place))?,
        _ => {}
    }
    if let Some((_, len, end)) = &finished_out {
        day_note(&ctx, start_note(*len, &place))?;
        let mut as_ended = BreakOut {
            action: "ended".to_string(),
            planned_min: *len,
            actual_min: Some(*len),
            place: place.clone(),
            superseded_end: None,
            finished: None,
            ended_from: None,
        };
        note_break_ended(&ctx, &mut as_ended, *end)?;
    }
    correct_netted_estimates(&mut ctx, &replay_before, "break")?;
    rec.finish(&ctx, format!("break {}", out.action))?;
    // D143, D148: a finished break is said as one — its span and its minutes — never as one running; D148
    // names the later start it runs past. D146 says the end of the break D141 ended, then the finished one.
    // D149 and D152 name the block it lies inside, and say it nets the block only when the block's minutes fell.
    let finished_line = |f: &FinishedBreak| {
        format!(
            "break {}m{} · {}–{} · logged finished ({})",
            f.actual_min,
            f.place.as_ref().map(|p| format!(" ({p})")).unwrap_or_default(),
            f.start,
            f.end,
            match (&f.into_start, out.action.as_str()) {
                (Some(s), _) => format!("it runs past the `start` at {s}, whose block it nets, D148"),
                (None, _) if f.inside_block.is_some() => {
                    let k = f.inside_block.as_deref().unwrap_or_default();
                    match f.nets {
                        Some(false) => format!(
                            "it lies inside the block of ^{k} a later `done` or `stop` closed, where ^{k} was not \
                             running (a pause, or another break), so it nets nothing, D149"
                        ),
                        _ => format!("it lies inside the block of ^{k} a later `done` or `stop` closed, which it nets, D149"),
                    }
                }
                (None, _) if f.inside_running.is_some() => {
                    let k = f.inside_running.as_deref().unwrap_or_default();
                    match f.nets {
                        Some(false) => format!(
                            "it lies inside ^{k}, which is running; ^{k} was not running there (a pause, or another \
                             break), so it nets nothing, D152"
                        ),
                        _ => format!("it lies inside ^{k}, which is running; it nets it, D152"),
                    }
                }
                // The reason that fired, and no other (README gap 6060): "the log has passed" only when its latest typed-time stamp
                // has reached the typed end; a length past the named span says so, and what it adds.
                (None, _) if f.inside_break.is_some() => {
                    let b = f.inside_break.as_deref().unwrap_or_default();
                    match (f.adds_min, inside_passed) {
                        (Some(n), _) => format!(
                            "it begins inside the break {b} the log holds and runs past its end, adding {n}m; the log has passed {}",
                            f.end
                        ),
                        (None, true) => format!("it lies inside the break {b} the log holds, and the log has passed its end"),
                        (None, false) => format!("it lies inside the break {b} the log holds"),
                    }
                }
                (None, "ended") => "typed with its length inside the break it ended, D146".to_string(),
                (None, _) => "a later start follows it, D143".to_string(),
            }
        )
    };
    emit(
        ctx.json,
        || match (out.action.as_str(), &out.finished) {
            ("finished", Some(f)) => finished_line(f),
            ("ended", Some(f)) => format!(
                "{} · {}",
                break_ended_line(out.actual_min.unwrap_or(0), out.planned_min),
                finished_line(f)
            ),
            ("ended", None) => break_ended_line(out.actual_min.unwrap_or(0), out.planned_min),
            // D147: the finished break's old span and its new end.
            ("retimed", _) => format!(
                "break {}–{} re-timed {}to end at {} ({}) · {}m of {}m",
                retimed_from.as_deref().unwrap_or_default(),
                out.superseded_end.as_deref().unwrap_or_default(),
                if retimed_out { "out " } else { "" },
                retimed_to.as_deref().unwrap_or_default(),
                if retimed_out { "D150" } else { "D147" },
                out.actual_min.unwrap_or(0),
                out.planned_min
            ),
            _ => format!(
                "break {}m{}",
                out.planned_min,
                out.place
                    .as_ref()
                    .map(|p| format!(" ({p})"))
                    .unwrap_or_default()
            ),
        },
        &out,
    )?;
    Ok(0)
}

/// **The day file's journal line for an ended break** — the ONE spelling, written by
/// [`note_break_ended`] for every verb that ends a running break (the owner's D90 and D97):
/// `break ended 10m/20m`.
fn break_ended_note(actual: u32, planned: u32) -> String {
    format!("break ended {actual}m/{planned}m")
}

/// **The human line for an ended break** — `tm break`'s, and the clause `tm interrupt` adds
/// when it ended one first (D90): `break ended · 10m of 20m`.
fn break_ended_line(actual: u32, planned: u32) -> String {
    format!("break ended · {actual}m of {planned}m")
}

/// **A verb's human line after the break it ended first** — [`break_ended_line`]'s clause, then
/// the verb's own words (`break ended · 10m of 20m · stopped ^t3 …`); the line alone when no
/// break was running. The ONE spelling every verb that ends a break prints (the owner's D90 for
/// `tm interrupt`, README gap 4501 for `tm resume`, and **D101** for `tm start`, `tm stop` and
/// `tm done` — README gap 4551, parity **P102**).
fn said_after_break(ended: Option<&BreakOut>, rest: String) -> String {
    match ended {
        Some(b) => format!("{} · {rest}", break_ended_line(b.actual_min.unwrap_or(0), b.planned_min)),
        None => rest,
    }
}

/// `tm interrupt --json` / `tm resume --json`.
#[derive(Debug, Serialize)]
pub struct InterruptOut {
    /// `interrupt` or `resume`.
    pub action: String,
    /// The block that was interrupted, if any.
    pub id: Option<String>,
    /// Minutes lost (on resume).
    pub lost_min: Option<u32>,
    /// Items dropped from today's plan as a consequence (§9).
    pub dropped: Vec<String>,
    /// **The break `tm interrupt` ended first** (the owner's D90, README gap 4340, parity
    /// P86), or `tm resume` (README gap 4501, parity P90) — `tm break`'s own report of its
    /// ending, `action` `ended`; absent when no break was running.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub break_ended: Option<BreakOut>,
    /// **The block a `tm resume` leaves paused** — one the user paused before the
    /// interruption (the W-44 repair, README gap 4610, parity P96); absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub still_paused: Option<String>,
    /// **The meeting that block is paused for**, when its pause is a calendar wall's
    /// (`WallTimer.pausedFor`: D61's, D110's or D117's) — it lifts by itself at the wall's end,
    /// and `tm pause` lifts it now (D66, README gap 3048, as `tm pause` names it; the W-48
    /// repair, README gap 5213). Absent otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub still_paused_for: Option<MeetingOut>,
}

/// **A running break, ended FIRST, as `tm break`'s ending arm reports it** — the one body
/// `tm interrupt` (the owner's D90, P86) and `tm resume` (README gap 4501, P90) call before the
/// mark they log, so neither logs it inside a running break: [`end_break`]'s line and state, and
/// `tm break`'s own report of its ending (`action` `ended`); `None` when no break was running.
/// At `now` ([`end_break`]); [`end_break_first_at`] at a stated end.
fn end_break_first(ctx: &mut Ctx) -> Result<Option<BreakOut>, CliError> {
    let running = ctx.state.break_.clone();
    let from = running_break_at(ctx);
    Ok(ended_report(running, end_break(ctx)?, from))
}

/// [`end_break_first`] at `end` — `now`, or the end a `tm stop --at`/`tm done --at` states (the
/// owner's D79: a break running then is over then too). **Every verb that ends a running break
/// ends it here** (the owner's **D97**, README gap 4391, parity **P95**): `tm break`'s ending arm,
/// `tm start`, `tm stop`, `tm done`, `tm interrupt` and `tm resume` — and, through them, the TUI's
/// keys, which run those verbs — and each writes the break's journal line through the one writer,
/// [`note_break_ended`], at the instant this returns it ended. `tm wake` ends none: it refuses
/// over a running break (D76, D81).
fn end_break_first_at(ctx: &mut Ctx, end: DateTime<chrono_tz::Tz>) -> Result<Option<BreakOut>, CliError> {
    let running = ctx.state.break_.clone();
    let from = running_break_at(ctx);
    Ok(ended_report(running, end_break_at(ctx, end)?, from))
}

/// `tm break`'s report of the break `running` was, begun at `from` and ended after `actual` minutes; `None` when
/// none was running.
fn ended_report(
    running: Option<BreakState>,
    actual: Option<u32>,
    from: Option<DateTime<FixedOffset>>,
) -> Option<BreakOut> {
    match (running, actual) {
        (Some(br), Some(actual)) => Some(BreakOut {
            action: "ended".to_string(),
            planned_min: br.planned_min,
            actual_min: Some(actual),
            place: br.place,
            superseded_end: None,
            finished: None,
            ended_from: from,
        }),
        _ => None,
    }
}

/// **The day file's journal line of a break a verb ended** — `tm break`'s own
/// ([`break_ended_note`], `break ended 10m/20m`), at `at`, the instant the break ended, in that
/// day's file: the ONE writer of it (the owner's **D97**, README gap 4391, parity **P95**). Fork
/// 4748911 wrote it from `tm break` alone, so the journal said when a break ended for one verb
/// of the six that end one; D90 and the W-43 repair gave it to `tm interrupt` and `tm resume`
/// as a second and third call of the spelling, and `tm start`, `tm stop` and `tm done` still
/// wrote none. Every caller writes it AFTER its own writes and its reload and BEFORE its own
/// journal line, so the day file reads the break's end, then the verb.
///
/// **It reads the minutes the replay DRAWS for the break it ended** (stage 6 W-54 track H, the W-53 repair critic's
/// sixth note, README gap 5898): the ended break's record in the replay just read ([`DayReplay::breaks`], drawn only
/// where no earlier break covers it, README gap 5662; stamped at its DRAWN start since the W-53 repair's clip, so it is
/// found as the earliest record of its planned minutes stamped between the break's start and its end) replaces `ended`'s wall-clock minutes, so the reply each verb
/// prints after this call, its `--json` and the journal say what `tm now` read while the break ran and what `tm
/// review day` records. A running break whose start an earlier logged break covers (the critic's F3: logged 10:20–10:40,
/// running since 10:30, ended 11:05) read `break ended · 35m of 20m` beside a review of 25; it reads 25. The log's
/// `actual_min` stays the break's wall-clock span (35), the fork's shape, which the kernel's union reads (D142). With
/// no record found the minutes are left as they were.
///
/// [`DayReplay::breaks`]: tm_core::log::DayReplay::breaks
fn note_break_ended(ctx: &Ctx, ended: &mut BreakOut, at: DateTime<chrono_tz::Tz>) -> Result<(), CliError> {
    if let Some(from) = ended.ended_from {
        let until = at.fixed_offset();
        let drawn = ctx
            .replay
            .days
            .values()
            .flat_map(|d| d.breaks.iter())
            .filter(|r| from <= r.t && r.t <= until && r.planned_min == ended.planned_min)
            .min_by_key(|r| r.t)
            .and_then(|r| r.actual_min);
        if let Some(drawn) = drawn {
            ended.actual_min = Some(drawn);
        }
    }
    super::dayfile::note(
        ctx,
        at.date_naive(),
        at.time(),
        &break_ended_note(ended.actual_min.unwrap_or(0), ended.planned_min),
    )
}

/// `tm interrupt`.
///
/// **A running break ends FIRST** — the owner's **D90** (README gap 4340, parity **P86**), as
/// `tm start` ends one before its `start`: the break's own `break` line is logged by
/// [`end_break`], the one function `tm break`'s ending arm calls, at the interruption's
/// instant, with `tm break`'s journal line ([`break_ended_note`]); then the interruption. So no
/// clock-stopping mark is ever logged inside a running break. Fork 4748911 logged the
/// `interrupt` and left the break running in `.tm/state.json`, its line written at its END —
/// after the interruption's — and the kernel's replay, which steps the interruption first,
/// credited the break's head as block time while the host's union of idle spans did not: on
/// the day `tests/cli_interrupt_break.rs` drives, `tm stop` said 10 minutes beside `tm review
/// day`'s 20, and on gap 4340's own (the break ended at 09:30) 30 beside 40.
pub fn interrupt(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    if ctx.state.interrupt.is_some() {
        return Err(CliError::msg("already interrupted — `tm resume` first"));
    }
    super::kernel_bridge::gate(&ctx, "interrupt")?;
    let rec = Recorder::start(&ctx, "interrupt")?;
    let replay_before = ctx.replay.clone();
    let mut ended = end_break_first(&mut ctx)?;
    let id = ctx.state.active.as_ref().map(|a| a.id.to_string());
    ctx.state.interrupt = Some(InterruptState {
        started: Some(ctx.now_tz.time()),
        id: ctx.state.active.as_ref().map(|a| a.id.clone()),
    });
    if let Some(a) = ctx.state.active.as_mut() {
        a.paused = true;
    }
    ctx.save_state()?;
    ctx.append_event(Event::Interrupt { id: id.clone() })?;
    ctx.reload()?;
    if let Some(b) = ended.as_mut() {
        note_break_ended(&ctx, b, ctx.now_tz)?;
    }
    day_note(
        &ctx,
        format!(
            "interrupt{}",
            id.as_ref().map(|i| format!(" ^{i}")).unwrap_or_default()
        ),
    )?;
    correct_netted_estimates(&mut ctx, &replay_before, "interrupt")?;
    rec.finish(&ctx, "interrupt")?;

    let out = InterruptOut {
        action: "interrupt".to_string(),
        id,
        lost_min: None,
        dropped: Vec::new(),
        break_ended: ended,
        still_paused: None,
        still_paused_for: None,
    };
    emit(
        ctx.json,
        || match &out.break_ended {
            Some(_) => said_after_break(out.break_ended.as_ref(), "interrupted".to_string()),
            None => "interrupted".to_string(),
        },
        &out,
    )?;
    Ok(0)
}

/// `tm resume`.
pub fn resume(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    preflight(&ctx, "resume")?;
    let Some(int) = ctx.state.interrupt.clone() else {
        return Err(CliError::msg("nothing to resume"));
    };
    let rec = Recorder::start(&ctx, "resume")?;
    let replay_before = ctx.replay.clone();
    // **The interruption's start is the log's** (the W-40 repair, README gaps 3821
    // and 3951, parity P69 — D75's clock, whose reason is this verb's too: a wrong
    // `lost_min` is a wrong fact written into the log). The instant of its own
    // `interrupt` line, `Replay::open_interruption`; `.tm/state.json`'s
    // `interrupt.started` is a bare `HH:MM`, its cache (D42), and fork 4748911 put it
    // on TODAY's date — so a `tm resume` after local midnight logged `lost_min: 0`
    // for an interruption begun before it. Only an interruption the log does not
    // hold (a hand-edited cache) keeps the cache's clock.
    let started = ctx
        .replay
        .open_interruption()
        .and_then(|i| i.start)
        .map(|t| t.with_timezone(&ctx.cfg.tz))
        .unwrap_or_else(|| ctx.at(int.started.unwrap_or_else(|| ctx.now_tz.time())));
    let lost = (ctx.now_tz - started).num_minutes().max(0) as u32;

    // §9: the tail the lost minutes cost — §10.1's `resume{dropped}` names
    // each item once, however many blocks it held in the plan that is being
    // replaced.
    let mut seen = BTreeSet::new();
    let before: Vec<String> = ctx
        .last_plan()
        .map(|p| {
            p.segments
                .iter()
                .filter_map(|s| s.item.clone())
                .filter(|i| seen.insert(i.clone()))
                .collect()
        })
        .unwrap_or_default();
    // **A running break ends FIRST** — `tm start`'s rule and the owner's D90's
    // (`tm interrupt`), reached by the one verb besides them that restarts the
    // block's clock (the W-43 repair's campaign call, README gap 4501, parity
    // **P90**). A break begun inside the interruption is still running here;
    // the fork's resume un-paused the block under it, so `tm now` drew `▶ ^m1 …
    // running` on a break and its header (the host's worked minutes, the break
    // netted) read 10m beside the row's 348m left (the kernel's replay, which
    // has no line for a running break). Ended here — its `break` line logged by
    // the one function `tm break`'s ending arm calls, before the `resume` line,
    // with `tm break`'s journal line — the block runs after the resume as the
    // verb says, and the `resume` is not stamped inside a running break.
    let mut ended = end_break_first(&mut ctx)?;
    // **A resume ends the interruption, not a pause the user took before it**
    // (the W-44 repair, README gap 4610, parity P96): the block the user paused
    // stays paused, as the kernel's replay reads the log (`Replay.resumeBlock`)
    // and the cache's own derivation does (`ctx::logged_stops`). Fork 4748911's
    // resume un-paused the block whatever held it, so `tm now` drew it running and
    // `tm stop` counted the time after the resume while `tm review day` and `tm
    // plan` read the pause.
    let still_paused = ctx.state.active.as_ref().and_then(|a| {
        ctx.replay
            .open_block
            .as_ref()
            .filter(|b| b.id == a.id.as_str())
            .map(|b| super::ctx::logged_stops(&ctx.replay, b).paused)
    });
    ctx.state.interrupt = None;
    if let Some(a) = ctx.state.active.as_mut() {
        a.paused = still_paused.unwrap_or(false);
    }
    ctx.save_state()?;
    if ended.is_some() {
        // The plan below is the one this verb writes: it reads the break's line
        // it just logged, as the next verb's load will.
        ctx.reload()?;
    }
    // **The replan reads this verb's own `resume` line** (the owner's D106, README
    // gap 4661; stage 6 W-46 track H, parity **P101**). Fork 4748911 planned
    // before it appended the line, so the plan it wrote — the day file's
    // `tm:plan` block, `.tm/last_plan.json` and the `plan` event's hash — had a
    // hole where the interruption was, and the next planning verb drew the
    // interruption `lost` there and moved the hash with no time passing: two
    // readings of one span (AGENTS §5.3). The line records `dropped`, which needs
    // the plan, so it is HELD in memory while the day is planned — by the one
    // hold every in-memory housekeeping write goes through (the owner's D96:
    // `Ctx::hold_begin`, `Ctx::append_event` into the hold, `Ctx::reload` reading
    // the context as the hold leaves it, `Ctx::release`) — and written after,
    // with `dropped` read off the plan it is written beside. The held line says
    // `dropped: []`: the replay keeps `dropped` as a record of the line
    // (`tm review day`'s), and no fact the planner reads is one of it, so the day
    // planned beside the held line is the day planned beside the written one —
    // `cli_resume_replan` holds the next planning verb's hash to it.
    ctx.hold_begin()?;
    let held = ctx
        .append_event(Event::Resume { lost_min: lost, dropped: Vec::new() })
        .and_then(|()| ctx.reload())
        .and_then(|()| planning::build(&ctx, false));
    ctx.release();
    let (plan, prios) = held?;
    let after: Vec<String> = plan
        .segments
        .iter()
        .filter_map(|s| s.item.as_ref().map(|i| i.to_string()))
        .collect();
    let dropped: Vec<String> = before
        .into_iter()
        .filter(|i| !after.contains(i))
        .collect();

    ctx.append_event(Event::Resume {
        lost_min: lost,
        dropped: dropped.clone(),
    })?;
    planning::write_plan(&mut ctx, &plan, &prios)?;
    ctx.reload()?;
    if let Some(b) = ended.as_mut() {
        note_break_ended(&ctx, b, ctx.now_tz)?;
    }
    day_note(
        &ctx,
        format!(
            "resume lost={lost}m{}",
            if dropped.is_empty() {
                String::new()
            } else {
                format!(" dropped={}", dropped.join(","))
            }
        ),
    )?;
    correct_netted_estimates(&mut ctx, &replay_before, "resume")?;
    rec.finish(&ctx, format!("resume (lost {lost}m)"))?;

    let held = ctx
        .state
        .active
        .as_ref()
        .filter(|a| a.paused && still_paused == Some(true))
        .map(|a| a.id.to_string());
    // **Which pause holds it** (the W-48 repair, README gap 5213): a block a calendar wall holds
    // paused — D61's at the wall's start, D110's or D117's when it was started or resumed inside
    // it — lifts by itself at the wall's end, and the line says so and names the meeting, as
    // `tm pause` names it (D66); only a pause the user typed waits for `tm pause`.
    let meeting = if held.is_some() {
        ask_the_walls(&ctx, running_break_at(&ctx), ctx.now_tz)?.paused_for
    } else {
        None
    };
    let said_meeting = meeting.as_ref().map(|m| (meeting_text(&ctx, &m.walls, m.from, m.to), hhmm(m.to)));
    let out = InterruptOut {
        action: "resume".to_string(),
        id: int.id.map(|i| i.to_string()),
        lost_min: Some(lost),
        dropped,
        break_ended: ended,
        still_paused: held,
        still_paused_for: meeting.as_ref().map(|m| MeetingOut {
            walls: m.walls.clone(),
            from: hhmm(m.from),
            to: hhmm(m.to),
        }),
    };
    emit(
        ctx.json,
        || {
            let said = said_after_break(out.break_ended.as_ref(), format!("resumed · lost {lost}m"));
            match (&out.still_paused, &said_meeting) {
                (Some(id), Some((m, to))) => format!(
                    "{said} · ^{id} still paused for {m} — it resumes at {to}; `tm pause` resumes it now"
                ),
                (Some(id), None) => format!("{said} · ^{id} still paused — `tm pause` resumes it"),
                (None, _) => said,
            }
        },
        &out,
    )?;
    Ok(0)
}

/// `tm pause --json`.
#[derive(Debug, Serialize)]
pub struct PauseOut {
    /// The item.
    pub id: Id,
    /// Whether the timer is now paused.
    pub paused: bool,
    /// When this resumed a timer a calendar wall had stopped (D61), the meeting
    /// it was stopped for — the campaign's D66 call on README gap 3048. Absent
    /// otherwise.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meeting: Option<MeetingOut>,
}

/// The meeting a resumed timer had been stopped for.
#[derive(Debug, Serialize)]
pub struct MeetingOut {
    /// The walls the meeting's span joins.
    pub walls: Vec<Id>,
    /// `HH:MM`.
    pub from: String,
    /// `HH:MM`.
    pub to: String,
}

/// `tm pause` — toggles the running block's timer.
pub fn pause(g: &Globals) -> Result<i32, CliError> {
    let mut ctx = Ctx::load(g, true)?;
    let Some(mut active) = ctx.state.active.clone() else {
        return Err(CliError::msg("nothing is running"));
    };
    // **The owner's D71 (README gap 3430, parity P62): inside an interruption
    // `tm pause` is REFUSED BY NAME**, before anything is written — the timer
    // is already stopped by the interruption, and `tm resume` is what starts
    // it, as `tm interrupt` already refuses a second interruption. The toggle
    // the fork made here wrote a cached `active.paused` that D42's rebuild from
    // the log contradicts. The interruption is read by the one rule `tm start`
    // and the rebuild read (`ctx::open_interruption`), never a second copy.
    if let Some(open) = super::ctx::open_interruption(&ctx.replay) {
        return Err(CliError::msg(pause_inside_an_interruption(&ctx, open)));
    }
    // **And inside a running BREAK it is refused by name too** — D71's rule one
    // state over (the W-43 repair's campaign call, README gap 4501, parity
    // **P89**): the break has already stopped the timer, and `tm break` is what
    // ends it. The toggle the fork made here was the one verb that still logged
    // a clock-STOPPING mark inside a running break once D90 made `tm interrupt`
    // end the break first: the break holds `active.paused`, so a first press
    // logged `unpause` ("resumed") and a second `pause` — stamped inside the
    // break, whose own line is written at its END. The kernel's replay closes
    // the stretch at that `pause` before it meets the break and credits the
    // break's head, which the host's union of idle spans does not: driven,
    // `tm stop` said 10m beside `tm review day`'s 20. Refused, nothing is
    // logged inside the break, and both readers read the block one way.
    if ctx.state.break_.is_some() {
        return Err(CliError::msg(pause_inside_a_break(ctx.running_break())));
    }
    super::kernel_bridge::gate(&ctx, "pause")?;
    // **D66 (the campaign's call on README gap 3048): `tm pause` inside a meeting keeps
    // RESUMING** — it is the correction for a skipped meeting — **and says so**: the kernel,
    // which decided the wall's pause, names the meeting the block is paused for now
    // (`WallTimer.pausedFor`). Asked only when this press resumes; a pause needs no name.
    let meeting = if active.paused {
        ask_the_walls(&ctx, running_break_at(&ctx), ctx.now_tz)?.paused_for
    } else {
        None
    };
    let rec = Recorder::start(&ctx, "pause")?;
    // The toggle is from the kernel's reading (the cache's `paused` is the
    // kernel's open block since the owner's D118, the load's reconcile).
    let pausing = !active.paused;
    let id = active.id.clone();
    ctx.append_event(if pausing {
        Event::Pause { id: id.to_string() }
    } else {
        Event::Unpause { id: id.to_string() }
    })?;
    ctx.reload()?;
    // **What the mark did is the kernel's to say** (the owner's D118, README gap
    // 5030, parity P114): the cache takes the kernel's reading of the open block
    // after the line it just logged, never the toggle's. They differ on exactly
    // one log a verb writes — a `pause` stamped before the block's own `start`
    // (a `--now` behind the log), which the kernel's machine reads as not the
    // block's (D99, P104) — and then nothing was paused, and the verb says so.
    let read = ctx
        .replay
        .open_block
        .as_ref()
        .filter(|b| b.id == id.as_str())
        .map(|b| super::ctx::logged_pause(&ctx.replay, b))
        .unwrap_or(pausing);
    active.paused = read;
    let paused = read;
    ctx.state.active = Some(active);
    ctx.save_state()?;
    let took = paused == pausing;
    if took {
        day_note(&ctx, timer_note(paused, &id))?;
    }
    rec.finish(&ctx, if pausing { "pause" } else { "unpause" })?;

    let said = meeting.as_ref().map(|m| meeting_text(&ctx, &m.walls, m.from, m.to));
    let out = PauseOut {
        id: id.clone(),
        paused,
        meeting: meeting.as_ref().map(|m| MeetingOut {
            walls: m.walls.clone(),
            from: hhmm(m.from),
            to: hhmm(m.to),
        }),
    };
    let started = ctx.replay.open_block.as_ref().filter(|b| b.id == id.as_str()).map(|b| b.started);
    emit(
        ctx.json,
        || match (&said, took) {
            (_, false) if !pausing => format!(
                "logged an unpause of {} at {}, and the log still holds it stopped (the log is read as the \
                 kernel reads it, D118)",
                out.id.token(),
                ctx.now_tz.format("%H:%M")
            ),
            (_, false) => format!(
                "logged a pause of {} at {}, before the block began at {} — it is not the block's, so {} keeps \
                 running (the log is read as the kernel reads it, D118)",
                out.id.token(),
                ctx.now_tz.format("%H:%M"),
                started.map(|t| t.with_timezone(&ctx.cfg.tz).format("%H:%M").to_string()).unwrap_or_default(),
                out.id.token()
            ),
            (Some(m), true) => format!("resumed {} (it was paused for {m})", out.id.token()),
            (None, true) => format!(
                "{} {}",
                if paused { "paused" } else { "resumed" },
                out.id.token()
            ),
        },
        &out,
    )?;
    Ok(0)
}

/// **D71's refusal, in words** (README gap 3430): the interruption the log
/// holds open, when it began, and the verb that ends it.
fn pause_inside_an_interruption(ctx: &Ctx, open: &tm_core::log::Interruption) -> String {
    let since = open
        .start
        .map(|t| format!(" since {}", hhmm(t.with_timezone(&ctx.cfg.tz))))
        .unwrap_or_default();
    format!(
        "an interruption is open{since} — the timer is already stopped; `tm resume` first"
    )
}

/// **The break's refusal, in words** (README gap 4501, parity P89): the
/// running break, when it began (the ONE reading of its start,
/// `Ctx::running_break`), and the verb that ends it — D71's sentence with the
/// break in the interruption's place.
fn pause_inside_a_break(since: Option<DateTime<chrono_tz::Tz>>) -> String {
    let since = since.map(|t| format!(" since {}", hhmm(t))).unwrap_or_default();
    format!("a break is running{since} — the timer is already stopped; `tm break` ends it")
}

/// `tm energy --json`.
#[derive(Debug, Serialize)]
pub struct EnergyOut {
    /// `HH:MM`, dated (`2026-09-07 23:40`) when the report is yesterday's (D86).
    pub at: String,
    /// What was predicted.
    pub pred: u8,
    /// What you reported.
    pub rep: u8,
    /// `rep − pred`.
    pub delta: i8,
    /// Hours since wake.
    pub hsw: f64,
    /// Location.
    pub loc: String,
    /// Whether the non-zero δ triggered a replan (§8.5).
    pub replanned: bool,
}

/// `tm energy 0-5 [--at HH:MM]`.
pub fn energy(g: &Globals, args: &super::EnergyArgs) -> Result<i32, CliError> {
    if args.level > 5 {
        return Err(CliError::msg("energy is 0–5"));
    }
    let mut ctx = Ctx::load(g, true)?;
    preflight(&ctx, "energy")?;
    let rec = Recorder::start(&ctx, "energy")?;
    // **The owner's D86** (README gap 4135, parity P82): the clock is read by
    // the one parser every `--at` shares, and names today's instant unless that
    // is more than twelve hours after now, then yesterday's — one definition,
    // `tm_core::capacity::report_at`. `tm stop --at`/`tm done --at` keep D79's.
    let reported = match &args.at {
        Some(t) => tm_core::capacity::report_at(ctx.cfg.tz, ctx.now_tz, parse_time(t)?),
        None => ctx.now_tz,
    };
    let f = features(&ctx, reported);
    let pred = energy::predict(&ctx.model, &ctx.cfg, &f);
    let loc = ctx.state.loc.clone().unwrap_or_else(|| "lounge".to_string());
    let entry = log::LogEntry::new(
        reported.fixed_offset(),
        Event::Energy {
            pred,
            rep: args.level,
            hsw: f.hsw,
            loc: loc.clone(),
        },
    );
    ctx.append_entry(&entry)?;
    ctx.reload()?;
    let delta = args.level as i8 - pred as i8;

    // §8.5: "Non-zero δ triggers a replan" — the posterior correction
    // re-energises every later slot (§9's "slots re-energised").
    let mut replanned = false;
    if delta != 0 {
        let (plan, prios) = planning::build(&ctx, false)?;
        planning::write_plan(&mut ctx, &plan, &prios)?;
        ctx.reload()?;
        replanned = true;
    }
    day_note(
        &ctx,
        format!(
            "energy pred={pred} rep={}{}",
            args.level,
            if replanned { " replan" } else { "" }
        ),
    )?;
    rec.finish(&ctx, format!("energy {}", args.level))?;

    let out = EnergyOut {
        // `HH:MM`, dated when the report is not today's (D86), as `tm stop`'s `ended` is.
        at: when(&ctx, reported),
        pred,
        rep: args.level,
        delta,
        hsw: f.hsw,
        loc,
        replanned,
    };
    emit(
        ctx.json,
        || {
            format!(
                "energy {} (pred {}) at {}{}",
                out.rep,
                out.pred,
                out.at,
                if out.replanned { " · replanned" } else { "" }
            )
        },
        &out,
    )?;
    Ok(0)
}

/// `tm idle --json`.
#[derive(Debug, Serialize)]
pub struct IdleOut {
    /// `work`, `break`, `routine`, `interrupt` or `leak`.
    pub attributed: String,
    /// Minutes attributed.
    pub min: u32,
}

/// `tm idle <w|b|t|i|l>` (§9.2).
pub fn idle(g: &Globals, args: &super::IdleArgs) -> Result<i32, CliError> {
    let attributed = match args.kind.to_ascii_lowercase().as_str() {
        "w" | "work" => "work",
        "b" | "break" => "break",
        "t" | "routine" => "routine",
        "i" | "interrupt" => "interrupt",
        "l" | "leak" => "leak",
        other => {
            return Err(CliError::msg(format!(
                "unknown attribution {other:?} (w work · b break · t routine · i interrupt · l leak)"
            )))
        }
    };
    let mut ctx = Ctx::load(g, true)?;
    super::kernel_bridge::gate(&ctx, "idle")?;
    let rec = Recorder::start(&ctx, "idle")?;
    let min = args.min.unwrap_or_else(|| {
        let last = ctx.replay.last_effective_t;
        match last {
            Some(t) => (ctx.now - t).num_minutes().clamp(0, 24 * 60) as u32,
            None => ctx.cfg.day.idle_min,
        }
    });
    ctx.append_event(Event::Idle {
        attributed: attributed.to_string(),
        min,
    })?;
    ctx.reload()?;
    day_note(&ctx, format!("idle {attributed} {min}m"))?;
    rec.finish(&ctx, format!("idle {attributed} {min}m"))?;

    let out = IdleOut {
        attributed: attributed.to_string(),
        min,
    };
    emit(
        ctx.json,
        || format!("{}m attributed to {}", out.min, out.attributed),
        &out,
    )?;
    Ok(0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tm_core::log::{LogSegment, SegmentKind};

    fn at_(s: &str) -> DateTime<FixedOffset> {
        DateTime::parse_from_rfc3339(&format!("2026-09-08T{s}:00-05:00")).expect("a stamp")
    }

    /// One held break as track K's fact gives it: read inside (`retime_from`), and out to `out` (`out_to`).
    fn held(from: &str, to: &str, read: bool, widest: &str, out: bool) -> HeldBreak {
        HeldBreak {
            started: at_(from),
            ended: at_(to),
            planned_min: 10,
            place: None,
            widest: at_(widest),
            retime_from: read.then(|| at_(from)),
            out_to: out.then(|| at_(widest)),
        }
    }

    fn arm_of(r: Option<AtFinished>) -> String {
        let hm = |t: DateTime<FixedOffset>| t.format("%H:%M").to_string();
        let list = |hs: &[HeldBreak]| hs.iter().map(|h| hm(h.started)).collect::<Vec<_>>().join(",");
        match r {
            Some(AtFinished::Inside(f)) => format!("inside {}", hm(f.started)),
            Some(AtFinished::AtEnd(f)) => format!("end {}", hm(f.started)),
            Some(AtFinished::AtStart(hs)) => format!("start {}", list(&hs)),
            Some(AtFinished::NotRead(f)) => format!("not read {}", hm(f.started)),
            Some(AtFinished::Many(hs)) => format!("many {}", list(&hs)),
            Some(AtFinished::Out(f)) => format!("out {}", hm(f.started)),
            Some(AtFinished::OutNotRead(f)) => format!("out not read {}", hm(f.started)),
            None => "none".to_string(),
        }
    }

    /// **The gate, per instant, over the kernel's fact** (the W-54 third repair): one closed span holding the instant
    /// answers by its own edge and its own range; several are refused unless the instant starts them all; none, then the
    /// widest ends.
    #[test]
    fn the_gate_reads_one_closed_span_several_or_a_widest_end() {
        // 09:20–09:30 (shortened from 09:50, out to 09:50), 09:35–09:40 (frozen), 10:00–10:20 nesting 10:05–10:08.
        let bs = vec![
            held("09:20", "09:30", true, "09:50", true),
            held("09:35", "09:40", false, "09:40", false),
            held("10:00", "10:20", true, "10:20", false),
            held("10:05", "10:08", true, "10:08", false),
        ];
        let arm = |t: &str| arm_of(at_finished(&bs, at_(t)));
        assert_eq!(arm("09:20"), "start 09:20");
        assert_eq!(arm("09:25"), "inside 09:20");
        assert_eq!(arm("09:30"), "end 09:20");
        assert_eq!(arm("09:32"), "out 09:20");
        assert_eq!(arm("09:37"), "not read 09:35", "inside, the range reads nothing");
        assert_eq!(arm("09:40"), "end 09:35", "an end needs no fact");
        assert_eq!(arm("09:45"), "out 09:20", "out_to reaches over a break between");
        assert_eq!(arm("09:50"), "out 09:20");
        assert_eq!(arm("09:55"), "none");
        assert_eq!(arm("10:02"), "inside 10:00");
        assert_eq!(arm("10:05"), "many 10:00,10:05", "one's start, inside the other");
        assert_eq!(arm("10:06"), "many 10:00,10:05", "inside both");
        assert_eq!(arm("10:08"), "many 10:00,10:05", "one's end, inside the other");
        assert_eq!(arm("10:15"), "inside 10:00");
        assert_eq!(arm("10:20"), "end 10:00");
        assert_eq!(arm("10:21"), "none");
        // Every instant starting all of them; adjoining breaks; widest ends meeting; out with no range.
        let twin = [held("10:30", "10:40", true, "10:40", false), held("10:30", "10:45", true, "10:45", false)];
        assert_eq!(arm_of(at_finished(&twin, at_("10:30"))), "start 10:30,10:30");
        assert_eq!(arm_of(at_finished(&twin, at_("10:45"))), "end 10:30");
        let adjoin = [held("09:20", "09:30", true, "09:30", false), held("09:30", "09:40", true, "09:40", false)];
        assert_eq!(arm_of(at_finished(&adjoin, at_("09:30"))), "many 09:20,09:30");
        let two = [held("09:20", "09:25", true, "09:50", true), held("09:22", "09:27", true, "09:50", true)];
        assert_eq!(arm_of(at_finished(&two, at_("09:40"))), "many 09:20,09:22");
        let frozen = [held("09:20", "09:25", false, "09:50", false)];
        assert_eq!(arm_of(at_finished(&frozen, at_("09:40"))), "out not read 09:20");
        assert_eq!(arm_of(at_finished(&frozen, at_("09:51"))), "none");
    }

    /// **Under a minute** (README gap 6042): a re-timing line carries whole minutes, so an instant under a minute past a
    /// break's start would end it at its start, under a minute past its end would change nothing, and past its end with
    /// another break holding the whole minute may move nothing.
    #[test]
    fn an_instant_with_seconds_is_read_at_the_end_its_line_gives() {
        let sec = |s: &str| DateTime::parse_from_rfc3339(&format!("2026-09-08T{s}-05:00")).expect("a stamp");
        let bs = [held("09:20", "09:30", true, "09:50", true), held("09:35", "09:40", true, "09:40", false)];
        assert_eq!(arm_of(at_finished(&bs, sec("09:20:30"))), "start 09:20");
        assert_eq!(arm_of(at_finished(&bs, sec("09:21:30"))), "inside 09:20");
        assert_eq!(line_end(&bs[0], sec("09:21:30")), at_("09:21"));
        assert_eq!(arm_of(at_finished(&bs, sec("09:30:30"))), "end 09:20");
        assert_eq!(arm_of(at_finished(&bs, sec("09:32:30"))), "out 09:20");
        assert_eq!(arm_of(at_finished(&bs, sec("09:40:30"))), "many 09:20,09:35", "its whole minute is the other's end");
    }

    /// **What stands in the way, by what the fact can say**: a twin at the stamp and length first, else the breaks logged
    /// after this one (the list is newest first) that could have let go of a stretch or overlap it.
    #[test]
    fn what_is_in_the_way_is_read_off_the_order_and_the_spans() {
        let hm = |t: DateTime<FixedOffset>| t.format("%H:%M").to_string();
        let span = |b: &HeldBreak| format!("{}–{}", hm(b.started), hm(b.ended));
        let frozen = held("09:40", "09:55", false, "09:55", false);
        let after = held("09:20", "09:32", true, "09:50", true);
        let older = held("08:00", "08:10", true, "08:10", false);
        let bs = [after.clone(), frozen.clone(), older];
        let said = in_the_way(&bs, &frozen, &span);
        assert!(said.contains("the break 09:20–09:32, logged after it"), "{said}");
        let twin = held("09:40", "09:50", true, "09:50", false);
        let bs = [twin, frozen.clone()];
        assert!(in_the_way(&bs, &frozen, &span).contains("has its start and its length"));
    }

    /// **The drawn break defence** (README gap 5895): a Break segment holding the instant strictly inside; none at a
    /// segment's edge or in a Block segment.
    #[test]
    fn a_drawn_break_is_read_off_the_segments() {
        let seg = |from: &str, to: &str, kind: SegmentKind| LogSegment { start: at_(from), end: at_(to), kind };
        let segments = [
            seg("09:00", "09:20", SegmentKind::Block { id: "t1".into() }),
            seg("09:20", "09:40", SegmentKind::Break { r#where: None }),
            seg("09:40", "09:50", SegmentKind::Break { r#where: None }),
        ];
        let segments: Vec<_> = segments.iter().collect();
        let hm = |t: DateTime<FixedOffset>| t.format("%H:%M").to_string();
        let read = |t: &str| drawn_break_at(&segments, at_(t)).map(|(a, b)| (hm(a), hm(b)));
        assert_eq!(read("09:25"), Some(("09:20".into(), "09:40".into())));
        assert_eq!(read("09:45"), Some(("09:40".into(), "09:50".into())));
        assert_eq!(read("09:40"), None, "at an edge");
        assert_eq!(read("09:10"), None, "a block");
        assert_eq!(read("09:55"), None, "past every break");
    }

    /// The kernel's absolute second of an RFC 3339 stamp.
    fn sec(s: &str) -> i64 {
        DateTime::parse_from_rfc3339(s).expect("a stamp").timestamp() + tm_core::planwire::EPOCH_FROM_CE
    }

    /// **A Pause the answer cuts is read with its two styles; a Pause it does
    /// not cut is refused by name — never drawn whole, never a fault; and an
    /// answer that is not one is a fault** (README gaps 3432 and 3528).
    #[test]
    fn a_pause_the_answer_does_not_cut_is_refused_and_one_it_cuts_is_read() {
        let tz: chrono_tz::Tz = "America/Chicago".parse().expect("a zone");
        let at = |s: &str| DateTime::parse_from_rfc3339(s).expect("a stamp");
        let date = chrono::NaiveDate::from_ymd_opt(2026, 9, 8).expect("a date");
        let segs = vec![LogSegment {
            start: at("2026-09-08T09:10:00-05:00"),
            end: at("2026-09-08T09:30:00-05:00"),
            kind: SegmentKind::Pause { id: "t4".into() },
        }];
        let days = vec![(date, segs.as_slice())];
        let (a, b) = (sec("2026-09-08T09:10:00-05:00"), sec("2026-09-08T09:30:00-05:00"));
        let m = sec("2026-09-08T09:20:00-05:00");
        let answered = serde_json::json!({"ok": {"emit": {"cut": [{"day": "2026-09-08",
            "pauses": [{"from": a, "to": b, "pause": [[a, m]], "wall": [[m, b]]}]}]}}});
        let cut = read_week_cut(&answered, "", tz, &days).expect("read");
        let pieces = cut.pieces_of(date, &segs[0]).expect("cut");
        let styles: Vec<_> = pieces.iter().map(|p| p.2).collect();
        assert_eq!(styles, vec![tm_core::review::Style::Pause, tm_core::review::Style::Wall]);
        assert_eq!((pieces[0].1 - pieces[0].0).num_minutes(), 10);

        let silent = serde_json::json!({"ok": {"emit": {"cut": [{"day": "2026-09-08", "pauses": []}]}}});
        let e = read_week_cut(&silent, "", tz, &days).expect_err("refused");
        assert!(!e.is_kernel_fault(), "a refusal, not a fault: {e}");
        assert!(e.to_string().contains("names no cut for the pause"), "{e}");

        let malformed = serde_json::json!({"ok": {"emit": {}}});
        let e = read_week_cut(&malformed, "", tz, &days).expect_err("refused");
        assert!(e.is_kernel_fault(), "a response that is not one is a fault: {e}");
    }
}
