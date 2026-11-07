//! One loaded plan directory, and the housekeeping every verb runs first.
//!
//! # API overview
//!
//! * [`Globals`] — the flags every verb shares: `--dir`, `--json`, `--now`.
//!   [`resolve_dir`] implements the search: `--dir`, else `$LIME_DIR`, else the
//!   first ancestor of the working directory that looks like a plan root
//!   (`config.toml` plus `.tm/` or a plan file) or has a `plan/` child that
//!   does.
//! * [`Ctx`] — the loaded directory: [`Config`], an [`FsStore`], the parsed
//!   [`PlanFiles`] and their [`Tree`], the log's [`Replay`] and the lines the
//!   log's [`Replay`] ([`LogRead`], asked for with the verb's [`ReplayScope`]
//!   through [`Ctx::replay_with`] — **the kernel**, since the switch, and the
//!   one reader of `.tm/log.jsonl`), the
//!   learned [`Model`] and `.tm/state.json` ([`RuntimeState`]), plus `now` in
//!   both `FixedOffset` (log timestamps) and `cfg.tz` (everything else).
//!   [`Ctx::load`] runs the housekeeping of §6.3 (the automatic close —
//!   one kernel `autoClose` call, [`super::closing::auto_close`], when a
//!   period has ended since `state.closed` or no kernel sweep has vouched
//!   for its stamps yet, [`super::closing::due`]) and §5.1 (waiting items whose
//!   timeout has elapsed) unless the verb opts out, and rolls the day-scoped
//!   fields of `state.json` when the date has moved on ([`roll_day`]).
//!   [`Ctx::load_for_close`] is the same minus the automatic close, for
//!   `lime close`, which *is* the close.
//! * Helpers the verbs share: [`Ctx::append_event`] (§10.1),
//!   [`Ctx::save_state`] (§10.2), [`Ctx::item`] / [`Ctx::line`] /
//!   [`Ctx::write_line`] (byte-faithful edits through
//!   [`lime_core::grammar::ItemLine`]), [`Ctx::hz`] (a [`horizon::Ctx`]) and
//!   [`Ctx::arrival_window`] (§8.1, the kernel's since W-47 track H, README gap
//!   4746).  §7's priorities and the §8.4 lookahead are the kernel's (stage 5
//!   D10 L8), and every surface reads them off the day's own request
//!   (`kernel_capacity::plan_day`; `Ctx::priorities`, a second, capacity-only
//!   request, went with its last caller at W-47 track H, README gap 4755).
//!   **`Ctx::window` and
//!   `Ctx::today_slots` are gone** (stage 6 step L9, gap 93): §8.1's window and
//!   §8.2 step 3's slots for **today** are the kernel's now, derived from its
//!   own replay, and a second definition here would be the bug AGENTS §5.3
//!   names.  The fork's versions live on as the parity harness's comparand
//!   (`lime/tests/kernel_lookahead_parity.rs`), as the fork's walls do
//!   (`Tree::walls_on`, no verb's since W-47 track H, README gap 4973).
//! * Sidecars `.tm/` grew for state §10.2 does not model:
//!   [`LAST_PLAN_PATH`] (`lime plan --diff` and the hysteresis roll),
//!   [`ARRIVAL_PLAN_PATH`] (§9's ghost row: the plan as it stood at arrival)
//!   and `.tm/undo.json` (see [`crate::cli::undo`]).

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::env;
use std::path::{Path, PathBuf};

use chrono::{DateTime, Datelike, FixedOffset, Local, NaiveDate, NaiveTime, Timelike};
use chrono_tz::Tz;
use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use serde_json::Value;

use lime_core::capacity;
use lime_core::config::Config;
use lime_core::energy::{self, Model};
use lime_core::grammar::ItemLine;
use lime_core::horizon;
use lime_core::log::{BreakRecord, DayReplay, EndedBreak, Event, LogEntry, Replay};
use lime_core::model::{Id, Item, Loc, State};
use lime_core::store::{
    self, ActiveBlock, BreakState, Closed, FsStore, InterruptState, PlanFiles, RuntimeState, Store, StoreExt,
    LOG_PATH, MODEL_PATH,
};
use lime_core::tree::Tree;
use lime_core::recur;

use super::kernel_bridge;
use super::kernel_capacity;
use super::kernel_log;
use super::out::CliError;

/// `.tm/last_plan.json` — the plan `lime plan --diff` compares against and the
/// priorities §7.4's hysteresis reads (`state.json` keeps only *yesterday's*
/// map, so the roll needs to know which day the stored one belongs to).
pub const LAST_PLAN_PATH: &str = ".tm/last_plan.json";
/// `.tm/arrival_plan.json` — the block starts as they stood at `lime arrive`
/// (§12.1's ghost row). [`RuntimeState`] has no field for it.
pub const ARRIVAL_PLAN_PATH: &str = ".tm/arrival_plan.json";

/// The flags every verb shares.
#[derive(Clone, Debug, Default)]
pub struct Globals {
    /// `--dir <plan dir>`.
    pub dir: Option<PathBuf>,
    /// `--json`.
    pub json: bool,
    /// `--now <RFC3339>` (hidden; deterministic tests).
    pub now: Option<DateTime<FixedOffset>>,
}

/// True when `dir` looks like a plan root (§2).
fn is_plan_root(dir: &Path) -> bool {
    dir.join("config.toml").is_file()
        && (dir.join(".tm").is_dir()
            || dir.join("backlog.md").is_file()
            || dir.join("week").is_dir()
            || dir.join("month").is_dir())
}

/// Find the plan directory: `--dir`, else `$LIME_DIR`, else the nearest
/// ancestor of the working directory that is a plan root or has a `plan/`
/// child that is one.
pub fn resolve_dir(explicit: Option<&Path>) -> Result<PathBuf, CliError> {
    if let Some(d) = explicit {
        return Ok(d.to_path_buf());
    }
    // `$TM_DIR` is what a user's shell profile already holds: it still answers when `$LIME_DIR` is unset.
    if let Some(d) = ["LIME_DIR", "TM_DIR"].iter().find_map(|k| env::var_os(k).filter(|v| !v.is_empty())) {
        return Ok(PathBuf::from(d));
    }
    let cwd = env::current_dir().map_err(|e| CliError::io(".", e))?;
    for dir in cwd.ancestors() {
        if is_plan_root(dir) {
            return Ok(dir.to_path_buf());
        }
        let child = dir.join("plan");
        if is_plan_root(&child) {
            return Ok(child);
        }
    }
    Err(CliError::msg(
        "no plan directory found (looked for config.toml next to .tm/, here and in every parent); \
         use --dir <path> or set LIME_DIR",
    ))
}

/// Drop the day-scoped fields of `state` when the local date has moved on
/// (§10.2: `date` says which day `window`, `budget` and `last_plan_hash`
/// belong to). Without this the first command of a new day — which need not
/// be `lime wake` or `lime arrive`, since §6.3's auto-close exists precisely for
/// the days you run neither — would plan and rewrite *yesterday's* day file
/// with yesterday's window (§8.1). Returns whether anything changed.
///
/// `active`, `break` and `interrupt` are deliberately left alone: a block
/// started before midnight is still running, and it is `lime wake` that ends
/// the night (§10.1). `lime done`/`lime stop` close them as usual.
///
/// The rule is [`RuntimeState::roll_to`], in `lime-core` since W-41 so a test can
/// name it (README gap 4041; parity P77 reads the TUI's stale state as this
/// roll leaves it).
fn roll_day(state: &mut RuntimeState, today: NaiveDate) -> bool {
    state.roll_to(today)
}

/// **The fields of `.tm/state.json` no replay of `.tm/log.jsonl` can supply**
/// (the owner's **D42**, README gap 993) — named here so the rebuild below can
/// say what it could not restore instead of regenerating it as `null`.
///
/// Each one is host-only for a reason the log module's own conventions state,
/// not for a reason this file decided.
///
/// **`break` and the `active.paused` a break sets are NOT here any more** — the
/// owner's **D105** (README "Stage 6 — W-46 track K", gaps 1034, 1085 and 4740,
/// parity **P100**). Until then a break's only line was the `break` appended
/// when it ENDED, so a running break left nothing to rebuild from: deleting the
/// file mid-break brought the block back RUNNING (README gap 1085, driven at the
/// W-21 repair step on `energy-14d`), and once R3's planner drew the running
/// break (P45) the deletion moved `lime plan` and appended a `plan` event — a
/// derived cache's deletion writing to its authority (gap 4740). `lime break` now
/// logs a `break_start` when the break begins, the kernel's replay pairs it with
/// the `break` that ends it ([`lime_core::log::Replay::open_break`]), and
/// [`derived_state`] rebuilds `break` and the pause from it. The one break the
/// log still cannot answer for is one a binary BEFORE D105 began (no
/// `break_start` line): the cache's copy is kept while the file exists
/// ([`Ctx::reconcile_state`]'s cached branch), and it is gone with the file —
/// README gap 4760.
/// **`priorities_yesterday` is NOT here any more** — the owner's **D108** (README
/// gap 4893, parity P119): §7.4's hysteresis map, which the day's first `plan`
/// line now carries (`DayReplay::priorities_yesterday`). A day whose first `plan`
/// a binary before D108 wrote carries none, and its map comes back empty.
/// * **`active.est_min`** — `Event::Start` carries `pred`, `hsw`, `slept_min`,
///   `loc`, `blocks_done` and `since_break_min`, and **no estimate**. Since the
///   owner's **D108** (README gap 4876, closed) the rebuild computes it as `lime
///   start` and `lime extend` did — [`Ctx::planned_block`] of the estimate the
///   item had before the block's logged extends, plus their minutes
///   (`OpenBlock::extended_min`, [`Ctx::rebuilt_block_minutes`]) — so deleting
///   the cache mid-extend moves nothing. It stays in this table because the log
///   still does not fix it: an estimate edited while the block runs (`lime edit
///   est=`, which writes the line and not the cache) or a duration model refitted
///   since the start moves the rebuild and not the cache (README gap 5160).
/// * **`closed`** — §6.3's stamps plus `closed.swept`, which is a fact about
///   whether a kernel `autoClose` has swept this tree and not about anything
///   that happened. Its absence is load-bearing in the safe direction (it
///   makes the automatic close sweep once), so the rebuild leaves it alone.
/// **This is the FIELD LIST, and it stopped being the notice at W-22.**
/// [`Ctx::rebuild_notice`] is the notice: two auditors drove the rebuild and
/// found the file byte-identical to the deleted one on all four of these, while
/// the sentence built out of this constant said they *"were NOT restored"*.
/// What is true of each field is what it is *derived from*, not that it is
/// lost, so the entries below say that and the notice computes the rest.
pub const HOST_ONLY_STATE: &[(&str, &str)] = &[
    ("`active.est_min`",
     "rebuilt as `lime start` and `lime extend` computed it — the item's estimate before the \
      block's logged extends, through the learned multiplier, plus their minutes (D108) — \
      but an estimate edited while the block runs, or a model refitted since its start, \
      is in the line and not in the cache (README gap 5160)"),
    ("`closed`",
     "`swept` is a fact about a sweep, not an event, and its absence makes the \
      automatic close sweep run once more, which is the safe direction"),
];

/// Why one [`HOST_ONLY_STATE`] field is what it is — the notice's own text,
/// read out of the one table rather than written twice (AGENTS §5.3).
fn host_only(field: &str) -> &'static str {
    HOST_ONLY_STATE
        .iter()
        .find(|(name, _)| *name == field)
        .map(|(_, why)| *why)
        .unwrap_or("the log does not carry it")
}

/// **Which of §10.2's fields the log can answer for, and how.**
///
/// The owner's **D42** makes `.tm/state.json` a *derivable cache*, rebuilt
/// from the log when missing or stale exactly as `.tm/cache/replay` is under
/// D13. This is the derivation, and it reads **only today's** facts:
/// [`DayReplay`] for the day-scoped fields and the two whole-log "still open"
/// facts for the running block and the running interruption.
///
/// | §10.2 field | from |
/// |---|---|
/// | `date` | `today`, when the log has anything to say about it |
/// | `wake` | `DayReplay::wake` (`Event::Wake`) |
/// | `arrival` | [`last_arrival`] — the **last** `Event::Arrive` of the day, whose `t` **is** the arrival (`lime_core::log`'s event convention; **D45**) |
/// | `loc` | the last of `DayReplay::loc_changes`, else `DayReplay::loc` |
/// | `window` | the arrival record's own payload — `DayReplay::window`, read back verbatim — on a day with **one** arrival; [`Ctx::arrival_window`] and a LOUD line on a day with more (**D45**, README gap 1306) |
/// | `budget` | `DayReplay::budget` with `window`, and recomputed with it |
/// | `active` | `Replay::open_block` — id, `started`, `paused`; `est_min` is [`Ctx::rebuilt_block_minutes`] (the owner's **D108**: `lime start`'s planned minutes plus the block's logged `extend`s, `OpenBlock::extended_min`), still host-only where the item's estimate moved mid-block ([`HOST_ONLY_STATE`]) |
/// | `interrupt` | `Replay::open_interrupt` — `started`, `id` |
/// | `last_plan_hash` | `DayReplay::last_plan_hash` (`Event::Plan`) |
/// | `break` | `Replay::open_break` — the `break_start` no `break` has ended (the owner's **D105**, parity P100): its start's `HH:MM`, `planned_min` and `where`, and the `active.paused` it sets; a break a binary before D105 began logged no `break_start` and is kept from the cache while the file exists (README gap 4760) |
/// | `priorities_yesterday` | the day's first `plan` line (the owner's **D108**, parity P119): `DayReplay::priorities_yesterday`; empty on a day with no `plan` yet, when §7.4 reads `.tm/last_plan.json`'s anyway ([`Ctx::hysteresis_input`]) |
/// | `closed` | **nothing** ([`HOST_ONLY_STATE`]); it comes back empty, which is load-bearing in the safe direction |
///
/// **The one residue inside a derivable field, measured rather than waved at.**
/// `lime plan` appends its `Event::Plan` only when the hash *moved*, so a day
/// whose first plan reproduces a hash last logged on an earlier day logs
/// nothing and `last_plan_hash` derives as `None`. That is not a regression:
/// [`roll_day`] already nulls it at every day boundary, so the derived value is
/// never worse than the cached one, and the cost of the miss is one extra
/// `plan` line.
/// The most recent day on or before `today` that has an answer for `pick`.
///
/// `.tm/state.json`'s `wake` and `loc` are not day-scoped ([`roll_day`] keeps
/// them), so neither is their derivation; every other day field reads
/// `today`'s [`DayReplay`] alone.
fn latest<T>(replay: &Replay, today: NaiveDate, pick: impl Fn(&DayReplay) -> Option<T>) -> Option<T> {
    replay.days.range(..=today).rev().find_map(|(_, d)| pick(d))
}

/// **The day's arrival as `lime arrive` leaves it: the LAST one** (the owner's
/// **D45**, README gap **1202**).
///
/// `DayReplay::arrival` is the day's **first** `Event::Arrive`, and it stays
/// that way: it is the fork's own derivation, `Replay.lean`'s
/// `a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan` proves
/// it, and T5 compares it key for key. The **cache** holds the last arrival,
/// because `lime arrive` overwrites `state.arrival` every time it runs. So on a
/// day with two arrivals the two readings disagreed, and deleting
/// `.tm/state.json` moved `arrival`, `window` and five of eleven `--json`
/// spellings with them. D45 makes the derivation follow the verb.
///
/// It reads the day's **headers** ([`Replay::view`]) rather than a fact,
/// because no fact carries the later arrivals: a header is a tag, an instant
/// and a mask bit, and that is exactly what "the last surviving `arrive` of
/// this day" needs. Rows are in **file order**, which is the order the cache
/// was written in — a retro `lime arrive --at 07:00` run after a 13:00 one wrote
/// 07:00 to the cache and appended its line last, and this returns 07:00.
///
/// **That last sentence was FALSE until README gap 1305 was repaired**, and it
/// is worth keeping the record. `Event::Arrive` was stamped with
/// [`Ctx::now`] — the instant of invocation — while `lime_core::log`'s own event
/// convention says *"`wake.t` is the wake time; `arrive.t` the arrival"*, which
/// `lime wake` honoured and `lime arrive` did not. So `--at` survived only inside
/// `window[0]`, this function returned the wall clock, and the rebuild moved
/// `arrival` and `window` to an instant carried by neither the cache nor the
/// log. The repair is in the **writer** (`day.rs`'s `arrive`), not here: one
/// fact, written where the reader already looks.
///
/// **Its one blind spot, declared:** a day whose headers the replay's scope did
/// not carry answers `None` here. Every verb that reads the runtime asks about
/// **today**, which is an open day in every scope, so this has no reachable
/// caller — but rather than claim that, [`derived_state`] falls back to
/// `DayReplay::arrival`, which is never worse than the reading this replaces.
fn last_arrival(replay: &Replay, today: NaiveDate) -> Option<DateTime<FixedOffset>> {
    arrive_rows(replay, today).next_back().map(|r| r.t)
}

/// The day's surviving `arrive` headers, in file order — the one enumeration
/// [`last_arrival`] and [`arrivals_today`] share, so the two cannot disagree
/// about which rows are arrivals.
fn arrive_rows<'a>(
    replay: &'a Replay,
    today: NaiveDate,
) -> impl DoubleEndedIterator<Item = &'a lime_core::log::ViewRow> {
    let tag = arrive_tag();
    replay
        .view()
        .iter()
        .filter(move |r| r.day == today && !r.cancelled && r.tag == tag)
}

/// **Whether a `lime wake` ran after the day's last `arrive`** — in file order,
/// undone rows skipped (README gap **3710**, the W-39 repair; D42, D45).
///
/// `day::wake` clears `arrival`, `window` and `budget` ("A new day: the window,
/// the budget and everything running are gone"), and the cache keeps them
/// cleared until the next `lime arrive`. The derivation used to restore the
/// day's LAST `arrive` whatever followed it, so `lime arrive` at 07:00, `lime arrive`
/// at 09:00 and `lime wake` left a cache with no arrival that the rebuild turned
/// into 09:00–18:00 — while the planner, reading the day's FIRST logged
/// `arrive` behind an empty state (fork `Planner::new`, gap 3390), had planned
/// 07:00–16:00 from the cache. DRIVEN on the W-39 binary: deleting
/// `.tm/state.json` moved the window, re-timed four rows, added a fifth and
/// appended a `plan` line to the log. D45's rule is that the derivation follows
/// the VERB, and the verb that ran last was `lime wake`: so a wake after the last
/// arrival derives what the wake wrote, and the planner's logged fallback reads
/// the same first `arrive` from either cache.
///
/// A `wake` is found by its tag, asked of `Event` (AGENTS §5.3). `false` when the
/// scope's headers do not reach today, which leaves the fallback below as it was.
fn woken_since_arrival(replay: &Replay, today: NaiveDate) -> bool {
    let wake = Event::Wake { slept_min: 0, onset_min: None }.name().to_string();
    let arrive = arrive_tag();
    replay
        .view()
        .iter()
        .rev()
        .filter(|r| r.day == today && !r.cancelled)
        .find_map(|r| {
            if r.tag == wake {
                Some(true)
            } else if r.tag == arrive {
                Some(false)
            } else {
                None
            }
        })
        .unwrap_or(false)
}

/// `arrive`'s tag, asked of `Event` rather than spelled a second time here
/// (AGENTS §5.3). An empty `String` allocates nothing, so the probe costs a
/// stack value and no heap.
fn arrive_tag() -> String {
    Event::Arrive {
        loc: String::new(),
        window: [String::new(), String::new()],
        budget: 0,
    }
    .name()
    .to_string()
}

/// **How many arrivals the day has**, which is what decides whether the log can
/// answer for the LAST one's window (README gap **1306**).
///
/// `DayReplay::window` and `DayReplay::budget` are the **first** `arrive`'s
/// payload — the fork's derivation, which `Replay.lean`'s
/// `a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan` proves
/// and T5 compares key for key. So on a day with exactly one arrival that
/// payload **is** the last arrival's and the rebuild reads it back verbatim;
/// with two or more, no fact carries the later payloads and the rebuild has to
/// recompute — which it says out loud ([`Ctx::rebuild_notice`]).
fn arrivals_today(replay: &Replay, today: NaiveDate) -> usize {
    arrive_rows(replay, today).count()
}

/// **The interruption the log holds open** — `Replay::open_interrupt` not yet
/// resumed. The one reading of it the rebuild ([`derived_state`]) and `lime start`
/// take (the campaign's D69 call on README gap 3283): a block begun while it
/// runs is paused, because that is what the rebuild derives from the log — the
/// cache follows the log, never the reverse.
pub(crate) fn open_interruption(replay: &Replay) -> Option<&lime_core::log::Interruption> {
    replay.open_interruption()
}

/// **What the verbs left `active.paused` at, read back from the log** — the one
/// rule the rebuild ([`derived_state`]), the cache's reconcile, `lime pause`'s
/// toggle, `lime resume` and the end of a break read the open block's stops by
/// (README gap **3521**, the W-38 repair; D42, and the campaign's D69 call on
/// gap 3283: the cache follows the log, never the reverse).
///
/// **Since the owner's D118** (README gap 5030, stage 6 W-48 track K, parity
/// **P114**) it is the KERNEL's open block, read and not re-derived: the
/// block's own pause is `OpenBlock::paused` (`Replay.Machine`'s, decoded by
/// `kernel_log::decode_facts`) and the interruption is the one the kernel's
/// replay holds open ([`open_interruption`]). Until W-48 this function was a
/// SECOND fold of the log's rows — every `pause` and `unpause` of the block
/// after its `start` row, in file order — and the kernel's machine reads a
/// `pause` stamped before the block's own `start` as not the block's (D99,
/// parity P104), which the fold read as the block's: driven, `start ^t1`
/// 09:00 then `lime --now 08:50 pause`, and at 09:30 `lime now` headed `30m of
/// 60m · paused` while `lime plan` drew `09:00 ▶ … 30m so far` and `lime stop` at
/// 09:40 said `after 40m`; after `rm .tm/state.json` the rebuild restored
/// `paused`, and the next `lime pause` said `resumed` while idling nothing. Two
/// readers of one block's state (AGENTS §5.3), and D118 names the kernel's.
///
/// What the fold read and the machine reads were otherwise the same rule, and
/// stay so: `pause` and `unpause` of this block (a typed `lime pause`, D61's
/// wall marks) set and clear the pause; `interrupt` and `resume` set and clear
/// the interruption, which holds the block too (a block begun inside one starts
/// held, P60; P103 reads one left open from an earlier ledger day); a `resume`
/// ends the interruption and not a pause the user took before it (the W-44
/// repair, README gap 4610, parity P96 — `Replay.resumeBlock`); and a `break`
/// leaves the timer as it found it (D87, parity P84 — `Replay.brkFx` moves no
/// clock that is not running). A break still RUNNING is the caller's
/// (`running_break`, `Replay::open_break`), never this function's.
pub(crate) fn logged_pause(replay: &Replay, open: &lime_core::log::OpenBlock) -> bool {
    let s = logged_stops(replay, open);
    s.paused || s.interrupted
}

/// **The two stops the kernel holds on the open block** — the block's own pause
/// and an open interruption — each with its own end (the W-44 repair, README
/// gap 4610, parity **P96**), read off the kernel's replay since the owner's
/// D118 ([`logged_pause`]). [`logged_pause`] is either stop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LoggedStops {
    /// The block's own pause (`pause` … `unpause`): `OpenBlock::paused`.
    pub paused: bool,
    /// An open interruption (`interrupt` … `resume`): [`open_interruption`].
    pub interrupted: bool,
}

/// [`LoggedStops`], the kernel's reading of the open block `open`.
pub(crate) fn logged_stops(replay: &Replay, open: &lime_core::log::OpenBlock) -> LoggedStops {
    LoggedStops { paused: open.paused, interrupted: open_interruption(replay).is_some() }
}

/// **What the log says about a CALENDAR day's plans** (the W-48 repair, README gaps 5210 and 5211): the hash of
/// its last `plan` line and the hysteresis input its first `plan` carried, each read by its line's stamp in the
/// tree's zone.
///
/// `.tm/state.json` keeps `last_plan_hash` and `priorities_yesterday` by calendar day (`roll_day`), and the replay
/// keeps its days by LEDGER day — a line written after local midnight and before the next wake is filed under the
/// previous ledger day (`Replay.dayOf`), so `replay.day(today)` held none of them and D42's rebuild, reading it,
/// dropped both: driven by the W-48 auditor and critic, deleting the cache at 00:35 re-ranked the next day, moved
/// the plan's hash and logged a `plan` line with no notice. A calendar day's lines are filed under its own ledger
/// day or the one before (a ledger day is at most a day from its wake), so the two are read, the later winning.
#[derive(Debug, Default)]
pub(crate) struct LoggedPlans {
    /// The hash of the calendar day's last `plan` line (`DayReplay::plan_at`).
    pub last_hash: Option<String>,
    /// The hysteresis input the calendar day's `plan` lines carried (`DayReplay::late_at`), `None` when none did.
    pub input: Option<BTreeMap<Id, u8>>,
}

pub(crate) fn logged_plans(replay: &Replay, tz: Tz, today: NaiveDate) -> LoggedPlans {
    let local = |t: &DateTime<FixedOffset>| t.with_timezone(&tz).date_naive();
    let mut out = LoggedPlans::default();
    // **The later LINE wins, not the later ledger day** (W-49 track L, README gap 5300; the owner's D125): each
    // ledger day's slot is the latest calendar date's last `plan` and last input it holds, with the line that wrote
    // it, and of the two ledger days a calendar day's lines can be filed under, the line later in the log wins —
    // a line a clock behind the log stamped before the wake can be appended after the wake's lines.
    let (mut plan_line, mut input_line) = (None, None);
    for d in [today.pred_opt(), Some(today)].into_iter().flatten() {
        let Some(day) = replay.day(d) else { continue };
        if day.plan_at.as_ref().is_some_and(|t| local(t) == today) && day.plan_line >= plan_line {
            out.last_hash = day.plan_hash.clone();
            plan_line = day.plan_line;
        }
        if day.late_at.as_ref().is_some_and(|t| local(t) == today) && day.late_line >= input_line {
            out.input = Some(day.late.iter().map(|(k, v)| (Id::new(k), *v)).collect());
            input_line = day.late_line;
        }
    }
    out
}

fn derived_state(replay: &Replay, tz: Tz, today: NaiveDate, running_break: bool) -> RuntimeState {
    let hhmm = |t: DateTime<FixedOffset>| t.with_timezone(&tz).time();
    let day = replay.day(today);
    let plans = logged_plans(replay, tz, today);
    // A wake after the day's last arrival cleared all three (gap 3710): the
    // derivation reads what the wake wrote, as the cache holds it.
    let woken = woken_since_arrival(replay, today);
    let one_arrival = !woken && arrivals_today(replay, today) == 1;
    let open = replay.open_block.as_ref();
    let interrupted = open_interruption(replay);
    RuntimeState {
        date: Some(today),
        // **`wake` and `loc` are the two fields [`roll_day`] deliberately does
        // NOT clear at a day boundary**, so the cache carries them across days
        // and the derivation has to as well: the most recent one on or before
        // today, not today's. A derivation that read today's `DayReplay` alone
        // answers `null` on any day with neither a `lime wake` nor a `lime arrive`
        // in it, which is WRONG and not merely narrower — measured on the T9
        // fixture, where it moved `lime now`, `lime plan`, `lime log` and two
        // reviews.
        wake: latest(replay, today, |d| d.wake).map(hhmm),
        // **The LAST `arrive` of the day, not `DayReplay::arrival`** — the
        // owner's D45, README gap 1202. `DayReplay`'s field is the day's
        // FIRST arrival, because that is what the fork derives and what
        // `Replay.lean`'s
        // `a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan`
        // proves; the CACHE
        // holds whatever the last `lime arrive` wrote. Two readings of one day,
        // and the derivation is the one that moves (AGENTS §5.3).
        arrival: (!woken)
            .then(|| last_arrival(replay, today).or(day.and_then(|d| d.arrival)))
            .flatten()
            .map(hhmm),
        loc: latest(replay, today, |d| {
            d.loc_changes.last().map(|(_, l)| l.clone()).or_else(|| d.loc.clone())
        }),
        // **The arrival record's own payload, read back verbatim** — which is
        // what `lime arrive` wrote and therefore what the cache held, walls and
        // config as they stood THEN (README gap **1306**).
        //
        // `DayReplay::window`/`budget` are the day's FIRST `arrive`'s, so this
        // is the last arrival's exactly when the day has one arrival. With two
        // or more the log carries no payload for the later ones and these stay
        // `None`; the caller fills them from `Ctx::arrival_window` and SAYS SO
        // ([`Ctx::rebuild_notice`]), the same shape `active.est_min` takes
        // below. Recomputing unconditionally is what W-23 shipped, and it moved
        // the window by 3h30m on a plain one-arrival day the moment a calendar
        // item was added after the arrival — a value in neither the cache nor
        // the log, written in silence.
        window: one_arrival
            .then(|| day.and_then(|d| d.window.as_ref()))
            .flatten()
            .and_then(|w| {
                let a = NaiveTime::parse_from_str(&w[0], "%H:%M").ok()?;
                let b = NaiveTime::parse_from_str(&w[1], "%H:%M").ok()?;
                Some((a, b))
            }),
        budget: one_arrival
            .then(|| day.and_then(|d| d.budget))
            .flatten(),
        active: open.map(|b| ActiveBlock {
            id: Id::new(&b.id),
            started: hhmm(b.started),
            // Not the log's: `Event::Start` carries no estimate. The caller
            // fills it from `Ctx::planned_block`, the one function
            // `lime start` writes it from.
            est_min: 0,
            // The kernel's open block ([`logged_pause`], the owner's D118);
            // a running break pauses it too — the log's own
            // (`Replay::open_break`, the owner's D105), or one the cache still
            // holds that a binary before D105 began (`running_break`).
            paused: logged_pause(replay, b)
                || running_break
                || replay.open_break.is_some(),
        }),
        // **The running break is the log's** (the owner's D105, parity P100):
        // the `break_start` no `break` line has ended, at its start's clock.
        break_: replay.open_break.as_ref().map(|b| BreakState {
            started: Some(hhmm(b.started)),
            planned_min: b.planned_min,
            place: b.r#where.clone(),
        }),
        interrupt: interrupted.map(|i| InterruptState {
            started: i.start.map(hhmm),
            id: i.id.as_deref().map(Id::new),
        }),
        // **By the plan lines' own stamps** (the W-48 repair, README gap 5210): the calendar day's last `plan`,
        // and the input its first `plan` carried (the owner's D108, parity P119), wherever the replay filed them.
        last_plan_hash: plans.last_hash,
        priorities_yesterday: plans.input.unwrap_or_default(),
        closed: Closed::default(),
    }
}

/// The stored plan behind `--diff` and the hysteresis roll.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
#[serde(default)]
pub struct StoredPlan {
    /// The day it planned.
    pub date: Option<NaiveDate>,
    /// [`lime_core::dayplan::DayPlan::hash`].
    pub hash: String,
    /// Every candidate's `p` when it was written (§7.4).
    pub priorities: BTreeMap<Id, u8>,
    /// The timeline, flattened for the diff.
    pub segments: Vec<StoredSegment>,
}

/// One row of a [`StoredPlan`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StoredSegment {
    /// `HH:MM`.
    pub start: String,
    /// `HH:MM`.
    pub end: String,
    /// [`lime_core::dayplan::SegKind`], lowercased.
    pub kind: String,
    /// The item, when the segment has one.
    pub item: Option<String>,
}

/// **What one read of `.tm/log.jsonl` gives a verb**: the replay, and the
/// lines the reader refused.
///
/// The pair is the shape the kernel's `log` answer already has — `facts`
/// beside `warnings` (design §10.2) — so the switch changes
/// [`Ctx::replay_of`]'s body and not this type. Before the repair the
/// warnings were computed and dropped on the floor, which is why `lime check`
/// could say `no problems` about a log with two unreadable lines in it.
#[derive(Clone, Debug)]
pub struct LogRead {
    /// Every fact the log yields (§10.1).
    pub replay: Replay,
    /// The checkpoint's ledger day after this call, or `None` when nothing is
    /// sealed ([`kernel_log::Read::ledger_day`]).
    pub ledger_day: Option<u64>,
}

/// **One line's header**, as `lime undo`'s recorder reads it (design §14.3 row
/// R6, §11.4): the physical line, the entry's tag and its primary id.
///
/// The wake-attributed day is deliberately **not** here. A tail read decides
/// days from the wakes it can see, and a tail that starts after the day's
/// `wake` would attribute its lines differently from the whole replay; the
/// recorder reads a tag and an id and nothing else, so the field it cannot
/// answer honestly is absent rather than wrong.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogHeader {
    /// The 1-based physical line.
    pub line: u64,
    /// The entry's tag ([`lime_core::log::Event::name`]).
    pub tag: String,
    /// Its primary id, when it has one.
    pub id: Option<String>,
}

/// How much history a verb's [`Replay`] must hold (design §11.1).
///
/// After the switch the kernel's answer covers the open days and the recent
/// window (`Hot`); a wider scope merges the sealed day and window records it
/// names. **Before the switch every scope is the whole log in memory**, but
/// every verb family already asks for its own, so the switch changes only
/// [`Ctx::replay_with`]'s body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ReplayScope {
    /// The answer only: today's periods, the auto-close catch-up, id-keyed
    /// facts. Every verb not named below.
    Hot,
    /// The answer plus the day records of `[from − 1, to + 1]` and the window
    /// records of `[from, to]`: a verb that names old dates (`lime log --since`,
    /// `lime close day <date>`, the TUI's week pane).
    Dates {
        /// The first date asked for.
        from: NaiveDate,
        /// The last date asked for.
        to: NaiveDate,
    },
    /// The answer plus every sealed record: the reviews, the model fit,
    /// `lime log --item`, the TUI's Review screen.
    All,
}

impl std::fmt::Display for ReplayScope {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayScope::Hot => write!(f, "hot"),
            ReplayScope::Dates { from, to } => write!(f, "dates {from}..{to}"),
            ReplayScope::All => write!(f, "all"),
        }
    }
}

/// When set, [`Ctx::replay_with`] writes the scope it was asked for to stderr
/// as `replay scope: <scope>` (the verb-family test reads it).
pub const TRACE_SCOPE_ENV: &str = "LIME_TRACE_REPLAY_SCOPE";

/// The named fault of OWNER Q9 (iii) / D18 / parity **P31**: a hand edit no
/// rebuild can window inside the memory gate. Spelled once, because
/// [`Ctx::load_tolerant`] matches on it and `lime check` prints it.
pub const REACH_TOO_FAR: &str = "reachTooFar";

impl ReplayScope {
    /// The kernel's own scope (design §11.1). The two enums are deliberately
    /// separate types: this one is the *verb family's* request, `kernel_log`'s
    /// is the wire's, and only this function relates them.
    fn to_kernel(self) -> kernel_log::Scope {
        match self {
            ReplayScope::Hot => kernel_log::Scope::Hot,
            ReplayScope::Dates { from, to } => kernel_log::Scope::Dates { from, to },
            ReplayScope::All => kernel_log::Scope::All,
        }
    }
}

/// **Why the kernel could not answer for the log**, as a named [`CliError`]
/// (design §10.3, §14.6 item 5: `kernel_bridge::refusal` gains the `log`
/// names).
///
/// [`kernel_log::GenesisError::ReachTooFar`] is the one the *user* can act on,
/// so it is the one spelled out: it names the line, the guard that refused it
/// and how far the rebuild would have had to reach, and it says which verb
/// still works. **The memory cap is never raised to make it go away** (D18);
/// the line is moved or removed instead.
pub(super) fn genesis_error(e: kernel_log::GenesisError) -> CliError {
    match e {
        kernel_log::GenesisError::ReachTooFar { line, kind, reach, bytes } => {
            let mut detail = serde_json::Map::new();
            detail.insert("refusal".into(), Value::String(REACH_TOO_FAR.into()));
            detail.insert("line".into(), Value::from(line));
            detail.insert("guard".into(), Value::String(kind.clone()));
            detail.insert("reach".into(), Value::from(reach));
            detail.insert("bytes".into(), Value::from(bytes));
            CliError::Kernel(super::out::KernelIssue {
                name: REACH_TOO_FAR.into(),
                message: format!(
                    "{REACH_TOO_FAR}: {LOG_PATH} line {line} cannot be windowed — answering it would \
                     resend {reach} lines ({bytes} bytes), past the memory gate, and the guard that \
                     refused it is {kind}. Move or remove that line; `lime check` still runs and names it"
                ),
                detail,
            })
        }
        kernel_log::GenesisError::Refused(r) => {
            CliError::msg(format!("{LOG_PATH}: the kernel refused the replay ({r:?})"))
        }
        kernel_log::GenesisError::Fault(why) => {
            CliError::Kernel(kernel_bridge::fault_issue(&format!("the log replay: {why}"), ""))
        }
    }
}

/// **What `lime plan`'s housekeeping computed IN MEMORY and did not write** — the owner's **D91**
/// (W-43 track H, README gap 4342) for §6.3's automatic close, and since the owner's **D96** (W-44
/// track H, README gap 4393) for EVERY housekeeping write: §5.1's waiting timeouts and D61's wall
/// marks too. A TUI left open past local midnight reads its plan directory as `lime plan` reads it at
/// that instant, writing nothing (D84: nothing writes on a timer); this is what it holds. The
/// housekeeping writes it through the same code `lime plan`'s does — every write a housekeeping step
/// makes goes through [`Ctx::writes`], [`Ctx::append_line`] and [`Ctx::save_state`], and while a
/// context holds, those three answer into this and not the disk. No CLI verb holds: its housekeeping
/// is written.
#[derive(Clone, Debug)]
pub struct Held {
    /// Every plan document a held write changed or created, by path, as held.
    pub docs: BTreeMap<String, String>,
    /// The log lines held, each with its newline, in order — the bytes [`Ctx::append_line`] would
    /// have appended.
    pub log: String,
    /// The plan directory as held: `config.toml` and every plan file, every held write laid over the
    /// disk's, and the held lines under [`LOG_PATH`] (the held lines alone). What a held write goes
    /// to; `docs` and `log` are read off it ([`Ctx::settle`]).
    mirror: store::MemStore,
    /// The plan files as the mirror began, which `docs` is the difference from.
    base: BTreeMap<String, String>,
    /// What the context had read before anything was held: `.tm/state.json`, the files, the tree
    /// and the replay, which [`Ctx::release`] puts back.
    before: (RuntimeState, PlanFiles, Tree, Replay),
}

/// **The plan directory as a request reads it** ([`Ctx::reading`]): the store itself, or — while an
/// automatic close is held in memory (D91) — a [`store::MemStore`] of `config.toml` and every plan
/// file with the held documents laid over them.
pub enum Reading<'a> {
    /// The plan directory on disk.
    Disk(&'a FsStore),
    /// The plan directory as the close the TUI holds would leave it.
    Held(store::MemStore),
}

impl Reading<'_> {
    /// The store to read through.
    pub fn store(&self) -> &dyn Store {
        match self {
            Reading::Disk(s) => *s,
            Reading::Held(m) => m,
        }
    }
}

/// One loaded plan directory.
pub struct Ctx {
    /// The store over the plan root ([`FsStore::root`] is the directory).
    pub store: FsStore,
    /// `config.toml` (§16).
    pub cfg: Config,
    /// `--json`.
    pub json: bool,
    /// The instant every log event is stamped with.
    pub now: DateTime<FixedOffset>,
    /// The same instant in `cfg.tz` — what the planner works in (§17.2).
    pub now_tz: DateTime<Tz>,
    /// The local date.
    pub today: NaiveDate,
    /// `.tm/state.json` (§10.2).
    pub state: RuntimeState,
    /// Every parsed file.
    pub files: PlanFiles,
    /// The tree over them (§6).
    pub tree: Tree,
    /// The replay of `.tm/log.jsonl` (§10.1) in [`Ctx::scope`], from
    /// [`Ctx::replay_with`].
    pub replay: Replay,
    /// **The named fault the replay refused with**, when this `Ctx` was loaded
    /// tolerantly and the kernel could not window the log (gap 145, D18 (iii)).
    ///
    /// `None` for every ordinary load, because a refusal is then the verb's
    /// error. Only [`Ctx::load_tolerant`] sets it, only `lime check` calls that,
    /// and `lime check` turns it into a named problem — which is the whole of
    /// D18's "every verb **except** `lime check`": the one verb that exists to
    /// find the bad line must survive it.
    ///
    /// The line is carried beside the sentence rather than parsed back out of
    /// it (§5.3: one reader of a fact, not two).
    pub replay_fault: Option<(usize, String)>,
    /// **The replay checkpoint's ledger day `L`** (§9.1), as of the call that
    /// loaded this `Ctx`; `None` when nothing is sealed.
    ///
    /// Days below `L` are final and their records went out once; days at or
    /// above it stay in the checkpoint as open days. A stall — a block or an
    /// interruption left open — holds `L` back, so the checkpoint keeps every
    /// day since as open (§9.4, §18.7). `lime check` is the one reader
    /// (README gap 119).
    pub ledger_day: Option<u64>,
    /// The scope the verb asked its replay for; [`Ctx::reload`] asks again.
    pub scope: ReplayScope,
    /// `.tm/model.json` (§8.5).
    pub model: Model,
    /// Items whose `on-event:` timeout elapsed and went back to `[ ]` (§5.1).
    pub timed_out: Vec<Id>,
    /// **The automatic close a TUI past midnight holds in memory** (the owner's D91, README gap
    /// 4342) — `None` for every CLI verb. Every request built from this context reads the plan
    /// directory through [`Ctx::reading`] and the log through [`Ctx::log_now`], so with one held it
    /// asks the kernel what `lime plan` asks after its own close.
    pub held: Option<Held>,
    /// **[`Ctx::ended_cached_break`]'s whole-log answer, and what it was asked about** — the cached
    /// break and `now` (W-51 repair track H, correcting README gap 5523): the question's last reading
    /// costs a whole-log replay, and a verb asked it from the reconcile and again from
    /// [`Ctx::log_a_cached_break`] (after the close had appended its lines), so a tree with a
    /// cache-only break paid two `All` replays per verb — on a refused tree, every verb, forever. It
    /// is asked once per verb now. The lines a verb appends between the two askings cannot hold a
    /// record of the cached break: the one writer of a break's ending line (`day::end_break_at`)
    /// takes the cached break as it writes, which changes the key.
    break_lookup: std::cell::RefCell<Option<BreakLookup>>,
}

/// What [`Ctx::break_lookup`] remembers: the cached break and `now` it was asked about, and the
/// whole-log answer.
type BreakLookup = (BreakState, DateTime<FixedOffset>, Option<BreakRecord>);

impl Ctx {
    /// Load the plan directory named by `g`. `housekeeping` runs §6.3's
    /// automatic close and §5.1's waiting timeouts first (every verb but
    /// `init`, `check`, `log`, `undo` and `tui`).
    ///
    /// The replay is asked for in [`ReplayScope::Hot`]; a verb that reads
    /// older history loads through [`Ctx::load_scoped`].
    pub fn load(g: &Globals, housekeeping: bool) -> Result<Ctx, CliError> {
        Ctx::load_with(g, housekeeping, housekeeping, false, housekeeping, |_, _| ReplayScope::Hot)
    }

    /// **[`Ctx::load`] without D61's wall marks** — the housekeeping of every
    /// verb (the day's roll, §6.3's automatic close, §5.1's timeouts) but the
    /// pause a calendar wall writes into a running block's timer
    /// (`day::stop_the_timer_at_walls`), for the two kinds of verb that must not
    /// write it at `now` (W-41 track T):
    ///
    /// * **a verb that ENDS the running block at a stated time** — `lime stop
    ///   --at`, `lime done --at` (the owner's D79): it runs the marks itself at
    ///   the end it states, once it has checked it
    ///   (`day::stop_the_timer_at_walls`). Run at `now` here, they would
    ///   log a meeting after that end as pausing a block the user says had
    ///   already ended, and the verb would then refuse the end it was asked
    ///   for because of a line its own load wrote;
    /// * **`lime wake`**, which never runs while a block does (D76 refuses it), so
    ///   the marks have nothing to do when it succeeds — and when it is refused
    ///   they would log the morning's meetings into the block D76's own message
    ///   tells the user to end with `--at`, before they can.
    pub fn load_without_wall_marks(g: &Globals) -> Result<Ctx, CliError> {
        Ctx::load_with(g, true, true, false, false, |_, _| ReplayScope::Hot)
    }

    /// **[`Ctx::load`] for the one verb that must survive a log no rebuild can
    /// window** (gap 145; OWNER Q9 (iii), D18, parity P31).
    ///
    /// D18 (iii) makes a hand edit beyond the rebuild bound a **named fault**
    /// that fails every verb by name — *except* `lime check`, because `lime check`
    /// is how the offending line is found. The fault reaches the user either
    /// way; what this changes is that here it becomes a
    /// [`Ctx::replay_fault`] and an empty [`Replay`] instead of an error, so
    /// the verb goes on to check the tree and to name the line.
    ///
    /// It tolerates **only** that fault. Every other refusal, and every I/O
    /// failure, is still an error: a `lime check` that answered "no problems"
    /// over a log it could not read would be the exact defect D18 exists to
    /// prevent.
    pub fn load_tolerant(g: &Globals) -> Result<Ctx, CliError> {
        Ctx::load_with(g, false, false, true, false, |_, _| ReplayScope::Hot)
    }

    /// [`Ctx::load`] with the replay asked for in the scope `scope` returns,
    /// given `.tm/state.json` as read and today's date (§11.1).
    pub fn load_scoped(
        g: &Globals,
        housekeeping: bool,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        Ctx::load_with(g, housekeeping, housekeeping, false, housekeeping, scope)
    }

    /// [`Ctx::load`] with housekeeping but without the automatic close — for
    /// `lime close`, whose own kernel call is the close: running the automatic
    /// one first would leave the verb reporting an empty close over a tree it
    /// had just rewritten.
    pub fn load_for_close(
        g: &Globals,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        Ctx::load_with(g, true, false, false, true, scope)
    }

    fn load_with(
        g: &Globals,
        housekeeping: bool,
        auto_close: bool,
        tolerate: bool,
        walls: bool,
        scope: impl FnOnce(&RuntimeState, NaiveDate) -> ReplayScope,
    ) -> Result<Ctx, CliError> {
        let dir = resolve_dir(g.dir.as_deref())?;
        if !dir.join(store::CONFIG_PATH).is_file() {
            return Err(CliError::msg(format!(
                "{}: not a plan directory (no config.toml) — run `lime init` first",
                dir.display()
            )));
        }
        let store = FsStore::new(dir.clone());
        let cfg = store.read_config()?;
        let now = g.now.unwrap_or_else(|| Local::now().fixed_offset());
        let now_tz = now.with_timezone(&cfg.tz);
        let today = now_tz.date_naive();
        // **D42: `.tm/state.json` is a CACHE of the log** (README gap 993), so
        // whether the file was there at all is a fact the rebuild below needs.
        // `load_state` answers a missing file with `Default::default()`, which
        // is the null-for-every-field the owner drove.
        let cached = store.exists(store::STATE_PATH);
        let mut state = store.load_state()?;
        let scope = scope(&state, today);
        // Gap 145: `lime check` alone loads tolerantly, and only `reachTooFar` is
        // tolerated — see `Ctx::load_tolerant`.
        let (replay, replay_fault, ledger_day) = match Ctx::replay_with(&store, &cfg, now, today, scope) {
            Ok(read) => (read.replay, None, read.ledger_day),
            Err(CliError::Kernel(issue)) if tolerate && issue.name == REACH_TOO_FAR => {
                let line = issue
                    .detail
                    .get("line")
                    .and_then(Value::as_u64)
                    .and_then(|l| usize::try_from(l).ok())
                    .unwrap_or(1);
                let tz = Ctx::tz_wire(&store, &cfg);
                // No ledger day: the checkpoint is exactly what could not be
                // read, so `lime check` reports the fault and never a stall.
                (Ctx::empty_replay(&cfg, &tz, today)?, Some((line, issue.message)), None)
            }
            Err(e) => return Err(e),
        };

        if housekeeping && roll_day(&mut state, today) {
            store.save_state(&state)?;
        }

        let files = store.read_tree()?;
        let tree = files.tree();
        let model = store.read_json::<Model>(MODEL_PATH)?.unwrap_or_default();
        let mut cx = Ctx {
            store,
            cfg,
            json: g.json,
            now,
            now_tz,
            today,
            state,
            files,
            tree,
            replay,
            replay_fault,
            ledger_day,
            scope,
            model,
            timed_out: Vec::new(),
            held: None,
            break_lookup: std::cell::RefCell::new(None),
        };
        // **D42**, before the automatic close and before any verb reads
        // `cx.state`: the cache is reconciled with the log it is a cache of.
        // IN MEMORY ONLY — see the function's last section.
        cx.reconcile_state(cached, housekeeping);
        let mut refused = false;
        if auto_close {
            // Writes, logs, stamps `state.closed` and reloads when it closed
            // anything; a refusal is printed and the verb goes on — but
            // nothing below writes to the tree the kernel just refused.
            refused = super::closing::auto_close(&mut cx)? == super::closing::AutoClosed::Refused;
        }
        if housekeeping {
            cx.after_the_close(refused, walls)?;
        }
        Ok(cx)
    }

    /// **§5.1's waiting timeouts, then D61's wall marks** — the housekeeping
    /// every verb runs after §6.3's automatic close ([`Ctx::load`]), and the ONE
    /// body a TUI past midnight runs to hold them in memory (the owner's D96,
    /// README gap 4393: `tui::read_as_lime_plan`, holding, so every write below
    /// answers into the hold and none reaches the disk). `refused` says the
    /// close ahead of it was refused (the timeouts then write nothing); `walls`
    /// is false for the verbs that run the wall marks at an end they state.
    ///
    /// **The owner's D61 (W-36 track T)**: a calendar wall that began while a
    /// block runs has stopped the block's timer. Its pause — and, once the wall
    /// has ended, its unpause — is logged here, the way §6.3's automatic close
    /// catches up: by the first verb that runs after the wall began
    /// ([`super::day::stop_the_timer_at_walls`]). It writes the log,
    /// `state.json` and — since the owner's D65 (W-37 track T) — the day file's
    /// journal line for each mark it logs. It does not wait on the gate because
    /// it needs none: the kernel decides it (README gap 3139) over the tree it
    /// loads, and a tree the kernel refuses gets no mark and no journal line.
    pub(crate) fn after_the_close(&mut self, refused: bool, walls: bool) -> Result<(), CliError> {
        if self.log_a_cached_break(refused)? {
            self.reload()?;
        }
        self.timed_out = self.resolve_timeouts(refused)?;
        if !self.timed_out.is_empty() {
            self.reload()?;
        }
        let now = self.now_tz;
        if walls && super::day::stop_the_timer_at_walls(self, now)? {
            self.reload()?;
        }
        Ok(())
    }

    /// **A running break `.tm/state.json` alone holds is LOGGED** — the owner's **D133** (README gaps 5437
    /// and 5340, W-50 repair track B, parity **P130**). A break a binary before the owner's D105 began
    /// logged no `break_start`, so the log held nothing of it while it ran: it lived in the cache alone,
    /// was lost with the file (README gap 4760), and the planner could read it only through a second
    /// wire spelling, `RuntimeIn.brk`, beside the replay's own running break (gap 5340). The first
    /// housekeeping verb that meets one writes its `break_start` at the instant the cache places it
    /// ([`Ctx::running_break`], D81's reading), with the cache's planned minutes and place, and says so
    /// in one line (D65's rule for a line the user did not type) — from then on the break is the log's,
    /// and the cache is its cache (D42).
    ///
    /// Only a break the log holds NO record of: one the log is running is the log's already, and one it
    /// ended ([`Ctx::ended_cached_break`], gap 5520) the reconcile has dropped. On a tree the kernel
    /// refuses nothing is written (D35), and the next verb tries again. Answers whether a line was
    /// appended.
    ///
    /// **The guards are asked cheapest first** (W-51 repair track H, correcting README gap 5523): a
    /// refused close settles it before [`Ctx::ended_cached_break`] is asked, and that answer is the one
    /// the reconcile already computed ([`Ctx::break_lookup`]) — so a verb pays at most ONE whole-log
    /// replay for a cache-only break, where it paid two, refused tree or not.
    ///
    /// **A break placed before the day's logged wake is dropped, not logged** — the owner's **D138**
    /// (parity **P133**): D81 places a cache-only break at the latest instant at or before `now`
    /// with its clock, and when that instant falls before the latest wake the log holds (at or
    /// before `now`), the break cannot have run across the wake — `lime wake` refuses while a break
    /// runs (D81's call on gap 3824) — so it is no fact the log can hold. The verb clears it from
    /// the cache, writes the cache past the same refusal guard, and says why in one line (D65's rule
    /// for a write the user did not type).
    fn log_a_cached_break(&mut self, refused: bool) -> Result<bool, CliError> {
        let Some(here) = self.state.break_.clone() else {
            return Ok(false);
        };
        if refused || self.replay.open_break.is_some() || self.ended_cached_break().is_some() {
            return Ok(false);
        }
        let Some(at) = self.running_break() else {
            return Ok(false);
        };
        if kernel_bridge::tree_refusal(self)?.is_some() {
            return Ok(false);
        }
        if let Some(woke) = self.latest_logged_wake().filter(|w| at.fixed_offset() < *w) {
            self.state.break_ = None;
            // The block's pause is then the log's alone, as a rebuild with no break derives it.
            let fresh = derived_state(&self.replay, self.cfg.tz, self.today, false);
            if let (Some(a), Some(f)) = (self.state.active.as_mut(), fresh.active.as_ref()) {
                if a.id == f.id {
                    a.paused = f.paused;
                }
            }
            self.save_state()?;
            kernel_bridge::notice(format!(
                "dropped the break .tm/state.json held running since {} ({}m) — that is before the wake the \
                 log holds at {}, and no break runs across a wake, so it was not logged (D138)",
                at.format("%Y-%m-%d %H:%M"),
                here.planned_min,
                woke.with_timezone(&self.cfg.tz).format("%Y-%m-%d %H:%M"),
            ));
            return Ok(false);
        }
        // The place is read through the kernel's one table (the owner's D111): a word the cache holds that the
        // table does not know (a hand edit) would make the line malformed, so the break is logged without it and
        // the line says so (README gap 5561; the next verb's reconcile names both places).
        let table = kernel_log::places().map_err(|e| CliError::Kernel(kernel_bridge::fault_issue(&e, "")))?;
        let (place, dropped) = match here.place.clone() {
            Some(w) if table.iter().any(|t| *t == w) => (Some(w), None),
            Some(w) => (None, Some(w)),
            None => (None, None),
        };
        self.append_entry(&LogEntry::new(
            at.fixed_offset(),
            Event::BreakStart {
                planned_min: here.planned_min,
                r#where: place.clone(),
            },
        ))?;
        kernel_bridge::notice(format!(
            "logged the break .tm/state.json holds running since {} ({}m{}) — it was begun before lime logged \
             a break's start, so .tm/log.jsonl now holds it (D133){}",
            at.format("%Y-%m-%d %H:%M"),
            here.planned_min,
            place.as_ref().map(|p| format!(", {p}")).unwrap_or_default(),
            dropped.map(|w| format!("; its place {w:?} is no word of the table and was not logged")).unwrap_or_default()
        ));
        Ok(true)
    }

    /// **Reconcile `.tm/state.json` with the log it is a cache of** — the
    /// owner's **D42**, README **gap 993**.
    ///
    /// # The defect this closes, as the owner drove it
    ///
    /// With `^p1` running, `rm .tm/state.json` regenerated the file with
    /// `date`, `wake`, `arrival`, `loc`, `window`, `budget` and `active` **all
    /// null** while `.tm/log.jsonl` still held the `wake`, the `arrive` and the
    /// `start`. `lime plan` read the log and drew `^p1` with `▶`; `lime now` read
    /// the cache and said *"nothing running"*; `lime done` and `lime stop` said
    /// *"nothing is running"* and exited **1**; `lime check` said *"no
    /// problems"*. Two readers of one day, disagreeing — AGENTS §5.3, the
    /// defect class this rebuild is named after — and a recoverable session
    /// looked unrecoverable.
    ///
    /// # The root of it: a missing file and an empty one were one value
    ///
    /// `Store::load_state` is `read_json(..)?.unwrap_or_default()`, so **"there
    /// is no file"** and **"the file says nothing is running"** arrived as the
    /// same `RuntimeState`. They are not the same statement. A `null` `active`
    /// in a file that exists is a *positive* claim — every verb that ends a
    /// block writes it — and an absent file makes no claim at all. `load_with`
    /// now asks `store.exists` before `load_state` and hands the answer here.
    ///
    /// # What this does, in two halves, and why they are not symmetric
    ///
    /// **The file is absent — REBUILD.** Every field [`derived_state`] can
    /// answer for is taken from the log, exactly as `.tm/cache/replay` is
    /// rebuilt when it is not there (D13). What the log cannot answer for is
    /// named on stderr rather than left to read as "there was nothing there"
    /// ([`HOST_ONLY_STATE`]).
    ///
    /// **The file is present and says a different block is open — STALE, and
    /// the log wins.** This is the other half of D42's *"missing or stale"*,
    /// and it is not hypothetical: `lime undo`'s own compensating line, appended
    /// to the log by hand without its `.tm/undo.json` snapshot, reopens a block
    /// the cache has already closed. **Driven at `4ccf4ef`** on
    /// `corpus/plan-basic`: `start ^p1`, `done`, then one hand-appended
    /// `{"ev":"undo","of":"done","id":"p1"}` — and `lime plan` drew `^p1` with
    /// `▶` and *"60m so far"* while `lime now` said *"nothing running"* and `lime
    /// done` said *"nothing is running"*, **with `.tm/state.json` present**.
    /// That is gap 993's whole symptom set without deleting anything, and
    /// `cli_latency`'s three-year row builds exactly that tree.
    ///
    /// The comparison is on the running block's **identity** alone. What only
    /// the cache knows about that block stays the cache's: `est_min`, which
    /// `lime extend` adds to and no event carries. Only when the log names a
    /// *different* block is the whole record replaced, and then `est_min` is
    /// rebuilt through [`Ctx::planned_block`] because the cache's belonged to
    /// another block.
    ///
    /// **And a running break the log holds and the cache does not is the
    /// log's** (the owner's D105, parity P100): its `break_start` was appended
    /// and the cache never written (a verb cut off between the two), so the
    /// break, and the pause it sets, come back from the log. A break the cache
    /// holds and the log does not is kept: a binary before D105 began it, and
    /// it logged no `break_start` to read it from.
    ///
    /// # Who is told
    ///
    /// `loud` is `housekeeping` — the verbs that **own** the day's runtime and
    /// are the ones that write it. A read verb (`lime log`, `lime check`, `lime
    /// undo`, the TUI's reloads) gets the reconciled runtime and says nothing
    /// about it: it did not rebuild anything, and `lime log`'s stdout **and
    /// stderr** are asserted byte-identical with the fork's over seven corpus
    /// trees, one of which (`logs/three-days`) ends with `^t8` still running
    /// and no `.tm/state.json` beside it. What `lime check` still cannot do is
    /// name the disagreement as a *problem* of its own — README gap 1032.
    ///
    /// **That gate is also what keeps these two lines off the TUI's screen**,
    /// and the ordering was checked rather than assumed: `tui::run` calls
    /// `tui::load` — `housekeeping`, so loud — at `tui/mod.rs:102`, **before**
    /// `tui::setup` enters the alternate screen at `:111`, and `tui::reload`
    /// loads with `housekeeping` false, so nothing writes to stderr while
    /// ratatui owns the terminal. AGENTS §4's own reason for the kernel being
    /// total is that `exit(1)` with no unwind leaves a ratatui terminal in raw
    /// mode; an `eprintln!` mid-frame is the smaller cousin of that.
    ///
    /// # It writes nothing, and that is not a shortcut
    ///
    /// The reconciled runtime lives in memory and reaches the disk only through
    /// the `save_state` the verb was going to run anyway — every one of which
    /// is **past `kernel_bridge::gate`**. Writing it here was tried and
    /// **measured**: `cli_write_gate`'s
    /// `every_write_verb_refuses_a_tree_the_kernel_cannot_load_and_writes_nothing`
    /// caught `lime wake` creating `.tm/state.json` on a tree the kernel refuses,
    /// which is precisely the D35 rule that test exists for — *"none of them
    /// writes a byte"* — and `a_now_before_the_ledger_is_answered_and_not_persisted`
    /// caught a read-only verb at an early `--now` persisting that instant's
    /// `arrival`, `window` and `budget`. A derived cache is not worth one byte
    /// written ahead of the gate.
    ///
    /// # What this is NOT
    ///
    /// It is not a second definition of any fact. `est_min` comes from
    /// [`Ctx::planned_block`], the one function `lime start` also writes it from;
    /// `wake` derives exactly as [`Ctx::logged_wake`] already fell back to the
    /// log; the day facts are `DayReplay`'s own fields and not a second read of
    /// `.tm/log.jsonl`.
    fn reconcile_state(&mut self, cached: bool, loud: bool) {
        let mut derived = derived_state(
            &self.replay,
            self.cfg.tz,
            self.today,
            self.state.break_.is_some(),
        );
        if cached {
            // **The cache exists, so it is STALE only where the log contradicts
            // it about what is OPEN.** That is one comparison, on identity, and
            // the log wins it.
            let here = self.state.active.as_ref().map(|a| a.id.clone());
            let logged = derived.active.as_ref().map(|a| a.id.clone());
            if here != logged {
                if loud {
                    let say = |id: &Option<Id>| match id {
                        Some(i) => format!("{} is running", i.token()),
                        None => "nothing is running".to_string(),
                    };
                    eprintln!(
                        "lime: .tm/state.json said {} and .tm/log.jsonl says {} — \
                         the log decides (§10.2 is a cache of it, D42)",
                        say(&here),
                        say(&logged),
                    );
                }
                self.state.active = derived.active.clone().map(|mut a| {
                    a.est_min = self.rebuilt_block_minutes(&a.id);
                    a
                });
            }
            let here = self.state.interrupt.as_ref().map(|i| i.id.clone());
            let logged = derived.interrupt.as_ref().map(|i| i.id.clone());
            if here != logged {
                self.state.interrupt = derived.interrupt.clone();
            }
            // **The paused flag is the kernel's** (the owner's D118, README gap
            // 5030, parity P114): with the cached block the log's own, its
            // `paused` is what the derivation reads off the kernel's open block
            // ([`logged_pause`]) — so a `pause` the kernel does not read as the
            // block's (one stamped before its `start`, a clock behind the log)
            // no longer leaves the header saying `paused`, and the next `lime
            // pause` toggles from the kernel's reading. A break the cache alone
            // holds (begun by a binary before D105) still pauses it: the
            // derivation was asked with it (`running_break` above).
            if let (Some(a), Some(f)) = (self.state.active.as_mut(), derived.active.as_ref()) {
                if a.id == f.id {
                    a.paused = f.paused;
                }
            }
            // **The running break, both ways** (the W-46 audit, README gap 4903): the log decides it
            // as it decides the block and the interruption above. Until the audit this read one
            // direction only — a cache with no break under a log that holds one — so a cache that
            // still held a break the log had ENDED (a crash between a verb's log append and its
            // state save, or a hand edit), or one the log's `break_start` contradicts, was served
            // while the file existed and changed the day the moment it was deleted (D42). A cached
            // break the log holds NO line for is still kept: a binary before D105 began it, and the
            // cache is all there is (P73).
            let hhmm = |b: &BreakState| b.started.map(|t| t.format("%H:%M").to_string()).unwrap_or_default();
            // **Compared at the cache's resolution** (stage 6 W-54 second repair track H, the verifiers' D-5, README gap
            // 5997): `.tm/state.json` holds a break's start as `HH:MM` ([`BreakState::started`], `opt_hhmm`), while the
            // derivation reads the `break_start`'s instant, seconds and all — a break begun on the real clock (16:47:44)
            // was never equal to its own cache, and every later verb said "a break began at 16:47 … and one began at
            // 16:47 — the log decides" with nothing to decide. The two agree when they agree to the minute.
            let at_cache = |b: &BreakState| BreakState {
                started: b.started.and_then(|t| t.with_second(0)).and_then(|t| t.with_nanosecond(0)),
                ..b.clone()
            };
            match (self.state.break_.clone(), derived.break_.clone()) {
                (None, Some(b)) => {
                    if loud {
                        eprintln!(
                            "lime: .tm/state.json said no break is running and .tm/log.jsonl says one began at {} — \
                             the log decides (§10.2 is a cache of it, D42, D105)",
                            hhmm(&b)
                        );
                    }
                    self.state.break_ = Some(b);
                    if let Some(a) = self.state.active.as_mut() {
                        a.paused = true;
                    }
                }
                (Some(here), Some(b)) if at_cache(&here) != at_cache(&b) => {
                    if loud {
                        // The place is named too (W-51 repair track H, the W-50 repair critic's fourth finding,
                        // README gap 5561): a cache whose place the kernel's table does not know is logged
                        // without it (D133, D111), and this notice then read "10:00 (15m) and … 10:00 (15m)" —
                        // two equal halves for the one field that differed.
                        let place = |b: &BreakState| b.place.as_ref().map(|p| format!(", {p}")).unwrap_or_else(|| ", no place".to_string());
                        eprintln!(
                            "lime: .tm/state.json said a break began at {} ({}m{}) and .tm/log.jsonl says one began at {} \
                             ({}m{}) — the log decides (§10.2 is a cache of it, D42, D105)",
                            hhmm(&here),
                            here.planned_min,
                            place(&here),
                            hhmm(&b),
                            b.planned_min,
                            place(&b)
                        );
                    }
                    self.state.break_ = Some(b);
                }
                (Some(here), None) if self.log_ended() => {
                    if loud {
                        eprintln!(
                            "lime: .tm/state.json said a break began at {} is running and .tm/log.jsonl ended it — \
                             the log decides (§10.2 is a cache of it, D42, D105)",
                            hhmm(&here)
                        );
                    }
                    self.state.break_ = None;
                    // The block's pause is then the log's alone, as a rebuild with no break derives it.
                    let fresh = derived_state(&self.replay, self.cfg.tz, self.today, false);
                    if let (Some(a), Some(f)) = (self.state.active.as_mut(), fresh.active.as_ref()) {
                        if a.id == f.id {
                            a.paused = f.paused;
                        }
                    }
                }
                _ => {}
            }
            return;
        }

        // **D45: the window and the budget are the LAST arrival's.**
        // `derived_state` has already read them back from the arrival record
        // whenever the log carries that record's payload; this fills the one
        // case it cannot — a day with two or more arrivals, whose later
        // payloads are no fact — from the one function `lime arrive` writes them
        // from, and [`Ctx::rebuild_notice`] names it. Same shape as
        // `active.est_min` two blocks below, and it is a fallback and not a
        // second definition: it never overwrites a value the log answered for.
        // **Here, after the cached branch, and only here** (W-47 track H, README
        // gap 4746): since the window is the KERNEL's it costs a planner call, and
        // only a rebuild reads it — a cached state never did. A tree the kernel
        // refuses gets no window back, and the notice says so by the refusal's name
        // rather than store a number nothing computed.
        let mut unwindowed = None;
        if let (Some(at), None) = (derived.arrival, derived.window) {
            match self.arrival_window(at) {
                Ok((window, budget)) => {
                    derived.window = Some(window);
                    derived.budget = Some(budget);
                }
                Err(e) => unwindowed = Some(e.to_string()),
            }
        }

        let before = self.state.clone();
        self.state = RuntimeState {
            // The running break is the log's since D105 (`derived.break_`, from
            // `Replay::open_break`), and `priorities_yesterday` since D108
            // (`derived`, from the day's first `plan`); `closed` is host-only:
            // an absent file cannot have held it, so it is `Default` — and the
            // notice below says so.
            closed: before.closed.clone(),
            active: derived.active.clone().map(|mut a| {
                a.est_min = self.rebuilt_block_minutes(&a.id);
                a
            }),
            ..derived
        };
        if self.state == before {
            return;
        }

        // **LOUD, and only when something was STRANDED.** A plan directory
        // synced without `.tm/state.json` — `lime init` gitignores it, so that is
        // the ordinary case and not an incident — has lost nothing and is told
        // nothing. A rebuild that hands a RUNNING block or a RUNNING
        // interruption back is the case gap 993 was reported as, and there the
        // fields the log cannot carry have to be named.
        //
        // **AND A TREE THAT WAS BEING USED TODAY IS STRANDED TOO** (README gap
        // 1191, the W-22 repair step). `break` is the ONE field of §10.2 that
        // genuinely cannot be derived, and it was the one field whose loss was
        // silent: with a break running and nothing started, there was no block
        // to name, so the whole notice — including its second sentence, which
        // is about the log's limits and not about the block — was suppressed,
        // and `state.break` went from a running break to `null` with no `lime:`
        // line at all. D42's own words are that a field that cannot be derived
        // *fails LOUDLY rather than regenerating as null*, so the third
        // condition is the log having anything to say about today: a synced
        // directory nobody has driven today still says nothing, and a tree that
        // has been driven today and lost its cache always does.
        //
        // Since the owner's D105 (parity P100) a running break is derived — the
        // `break_start` `lime break` logs — so the fourth condition is a running
        // break the rebuild RESTORED, named like a running block; the third
        // stays, because a break a binary before D105 began logged no
        // `break_start` and is still lost with the file.
        // A calendar day's lines before the wake are filed under the previous ledger day (README gap 5210), so a
        // `plan` the log holds for today is the log having something to say about today too.
        let used_today = self.replay.day(self.today).is_some()
            || logged_plans(&self.replay, self.cfg.tz, self.today).last_hash.is_some();
        if loud
            && (self.state.active.is_some()
                || self.state.interrupt.is_some()
                || self.state.break_.is_some()
                || used_today)
        {
            eprintln!(
                "lime: .tm/state.json was missing; rebuilt from .tm/log.jsonl \
                 (§10.2 is a cache of the log — D42){}",
                self.state
                    .active
                    .as_ref()
                    .map(|a| format!(" — {} is running, started {}", a.id.token(), a.started.format("%H:%M")))
                    .unwrap_or_default()
            );
            for line in self.rebuild_notice() {
                eprintln!("lime: {line}");
            }
            if let Some(why) = &unwindowed {
                eprintln!(
                    "lime: NOT recomputed: `window` and `budget` — the kernel refused the day's \
                     request ({why}), so nothing stands for them until it accepts the tree"
                );
            }
        }
    }

    /// **The break this verb just began, ended by a `start` the log already holds** (the owner's
    /// **D129**, README gap 5433, W-50 track K): a `break_start` stamped before a block's `start`
    /// that is already logged — `lime --now <earlier> break` after the block, or a merged log — is
    /// ended at that start in stamp order, so the kernel's replay holds no running break and the
    /// break's record instead. The cache this verb wrote a moment ago is then dropped, as the next
    /// verb's reconcile would drop it ([`Ctx::log_ended`]), and the block's pause is the log's again.
    /// Answers the break's start and **the end D129 gave it** — read off the kernel's own fact,
    /// [`Replay::ended_breaks`] (stage 6 W-52 repair track R, README gap 5730), never off the record's
    /// span, which since gap 5662 carries the minutes DRAWN and so ends early when an earlier break covers
    /// a head of it. `None` for the end when the fact does not offer the break (one a later-held break
    /// overlaps, README gap 5741: the kernel holds the ending, but no `break` line can end it there);
    /// `None` altogether when the break still runs.
    pub(crate) fn drop_break_a_start_ended(
        &mut self,
    ) -> Option<(DateTime<FixedOffset>, Option<DateTime<FixedOffset>>)> {
        let from = self.ended_cached_break()?.t;
        let until = self.replay.ended_breaks.iter().find(|x| x.started == from).map(|x| x.ended);
        self.state.break_ = None;
        let fresh = derived_state(&self.replay, self.cfg.tz, self.today, false);
        if let (Some(a), Some(f)) = (self.state.active.as_mut(), fresh.active.as_ref()) {
            if a.id == f.id {
                a.paused = f.paused;
            }
        }
        Some((from, until))
    }

    /// **The logged break a later block's `start` ended (D129) that `at` lies inside, and that a `break`
    /// line may still end there** — the owner's **D141** (README gap 5633, stage 6 W-52 track H, parity
    /// **P138**): the break `lime break --now <at>` ends at `at` instead of opening a second break inside it.
    ///
    /// **One reader of "endable"** (stage 6 W-52 repair track R, README gaps 5714 and 5730): the kernel's
    /// own fact, [`Replay::ended_breaks`] (`Replay.endable`), which `Replay.d141_reads_iff_endable` proves is
    /// exactly what its replay reads as D141 — a `break` line stamped at an entry's `started` and ending
    /// strictly before its `ended` ends that break. So this verb never says "ends here" for a line the
    /// replay would not read as an end. Until the repair this read a [`BreakRecord`]'s span as D129's end
    /// and the log's rows as "no line yet" — a second reading the replay did not share (the critic's
    /// scenario C and the auditor's J2: "ends here", and nothing moved). `at` must lie STRICTLY inside
    /// `(started, ended)`; AT `started` the verb refuses by name (P139, [`Ctx::ended_break_starting_at`]).
    /// With several around `at`, the latest-begun is answered. The fact is empty while a break runs
    /// (`Replay.endable`), so this answers `None` then with no guard of its own — the guard on
    /// `open_break`/`state.break_` it carried until the repair could not fire (`take_break` asks only after
    /// its ending arm ended nothing). `None` too when the replay's scope does not hold the break (README gap
    /// 5681).
    pub(crate) fn break_a_start_ended_at(&self, at: DateTime<FixedOffset>) -> Option<EndedBreak> {
        self.replay
            .ended_breaks
            .iter()
            .filter(|x| x.started < at && at < x.ended && self.a_line_ends(x))
            .max_by_key(|x| x.started)
            .cloned()
    }

    /// **Whether a `break` line at this ending's stamp is read as its end, today** — the kernel's one-fact-per-held-break
    /// ([`Replay::held_breaks`], `Replay.heldFacts`): [`Replay::ended_breaks`] is `Replay.endable`, which does not read
    /// `Replay.frozen`, and a break held after this one that let go of a stretch meeting it has the line read as a break
    /// of its own (W-54 third repair, README gap 6041). `true` when the fact holds no entry for it, which leaves
    /// `endable` deciding as it did.
    pub(crate) fn a_line_ends(&self, x: &EndedBreak) -> bool {
        self.replay
            .held_breaks
            .iter()
            .find(|h| h.started == x.started && h.ended == x.ended && h.planned_min == x.planned_min)
            .map_or(true, |h| h.retime_from.is_some())
    }

    /// **The logged break D129 ended whose own start is `at`** (stage 6 W-52 repair track R, the campaign's
    /// call, parity **P139**): `lime break --now <that start>` would open a second break wholly inside it,
    /// which D141 forbids, so the verb refuses it by name. Read off the same fact as
    /// [`Ctx::break_a_start_ended_at`]. **Under a minute past its start is at its start** (the W-54 third repair, README gap
    /// 6056; `at_finished`'s rule for a logged break): a line carries whole minutes from the start, so D141's arm would write
    /// `actual_min: 0` and the break would vanish under a reply saying it ended here. Inside its span only (README gap 6061): at a
    /// break under a minute long an instant past its end lies outside it, where a break begins, and at its end it already ends.
    pub(crate) fn ended_break_starting_at(&self, at: DateTime<FixedOffset>) -> Option<EndedBreak> {
        self.replay
            .ended_breaks
            .iter()
            .find(|x| x.started <= at && at < x.ended && at - x.started < chrono::Duration::minutes(1))
            .cloned()
    }

    /// **Whether the log ENDED the running break `.tm/state.json` holds** (the W-46 audit, README gap
    /// 4903) — [`Ctx::ended_cached_break`] found its record.
    fn log_ended(&self) -> bool {
        self.ended_cached_break().is_some()
    }

    /// **A replay whose rows hold the open block `block`'s own `start` row** — this context's, when its
    /// rows reach it, else one asked for the dates from the block's start to today (W-51 repair track H,
    /// README gap 5509). Under a served `Hot` replay the view is the unsealed tail: once a reseal has
    /// folded the block's `start` line, [`Replay::start_row`] finds nothing, so `lime check`'s
    /// `log-taken-block` named no taken block after its first run and D130's last activity read no
    /// mark of the block. The rows of a sealed day come back with its day record, so a [`ReplayScope::Dates`]
    /// replay from the start's date holds the start row and every mark logged since; it is asked only
    /// when the block's start has been folded (a block left running across a reseal), and when even
    /// that replay does not find it, this context's is answered as before.
    pub(crate) fn block_rows(&self, block: &lime_core::log::OpenBlock) -> std::borrow::Cow<'_, Replay> {
        let found = |r: &Replay| r.start_row(Some(block.id.as_str()), block.started).is_some();
        if found(&self.replay) || self.scope == ReplayScope::All {
            return std::borrow::Cow::Borrowed(&self.replay);
        }
        let from = block.started.with_timezone(&self.cfg.tz).date_naive().min(self.today);
        let scope = ReplayScope::Dates { from, to: self.today };
        match self.replay_in(scope) {
            Some(replay) if found(&replay) => std::borrow::Cow::Owned(replay),
            _ => std::borrow::Cow::Borrowed(&self.replay),
        }
    }

    /// **A second replay of this context's log in `scope`, for a question its own replay's scope cannot
    /// answer** — [`Ctx::replay_with`] for a CLI verb, and while housekeeping is HELD (a TUI past midnight,
    /// the owner's D96) the replay that writes nothing, over the log as held ([`kernel_log::replay_unsealed`],
    /// as [`Ctx::settle`] reads it), so asking it writes no checkpoint. `None` when it cannot be answered (a
    /// refusal, or a held read that would rebuild a sealed month file); the callers then keep their own.
    fn replay_in(&self, scope: ReplayScope) -> Option<Replay> {
        if !self.holding() {
            return Ctx::replay_with(&self.store, &self.cfg, self.now, self.today, scope).ok().map(|r| r.replay);
        }
        let bytes = self.log_now().ok()?;
        let tz = Ctx::tz_wire(&self.store, &self.cfg);
        kernel_log::replay_unsealed(self.store.root(), &bytes, self.cfg.tz, &tz, self.today, scope.to_kernel())
            .ok()
            .flatten()
            .map(|r| r.replay)
    }

    /// **The latest wake the log holds at or before `now`** (the owner's D138): the wake records of the
    /// replay's days. The scoped replay holds the open days, and a wake that is the latest one has
    /// opened the newest of them.
    fn latest_logged_wake(&self) -> Option<DateTime<FixedOffset>> {
        self.replay.days.values().filter_map(|d| d.wake).filter(|w| *w <= self.now).max()
    }

    /// **The log's record of the running break `.tm/state.json` holds, when the log has ENDED it** (the
    /// W-46 audit, README gap 4903; matched by its REAL start since W-50 repair track B, README gap 5520).
    /// `None` while the log holds a running break (the cache's is then the log's, or contradicted by it —
    /// the reconcile's other arms), and `None` for a break the log holds no record of: one a binary before
    /// the owner's D105 began, which the next verb logs (the owner's D133).
    ///
    /// The cache stores the break's start as a bare `HH:MM`, and the record sits at its real start — the
    /// `break_start` `lime break` logged, ended by a `break` line or, since the owner's D129, by a `start`
    /// stamped after it. Until this repair the record was looked for only at [`Ctx::running_break`]'s
    /// instant, D81's latest instant at or before `now` with the cached clock, which is the real start
    /// only until `now` passes the next occurrence of that clock (about a day): from then on the cache
    /// survived the log's ending — a break nobody took drawn from midnight while `.tm/state.json`
    /// existed and gone without it (D42), and logged with the hours since by the next verb that ended
    /// it. Two readings, in order:
    ///
    /// 1. the record at that instant, to the minute — the break this verb just began and a start
    ///    already logged ended (D129), and a break ended within the day;
    /// 2. else the LATEST record carrying the cached break's own clock, planned minutes and place,
    ///    at or before `now` — on whatever date, and looked for over every day of the log when this
    ///    verb's scoped replay does not hold it (a sealed month: the scoped replay holds the open days
    ///    only), so a break ended weeks ago under a cache an older binary kept rolling is found too.
    ///
    /// What the second reading cannot tell apart, recorded (README gap 5522): a break a binary before
    /// D105 began, still running in the cache alone, whose clock, minutes and place an EARLIER logged
    /// break shares, is read as that break ended.
    fn ended_cached_break(&self) -> Option<BreakRecord> {
        let here = self.state.break_.as_ref()?;
        let clock = here.started?;
        if self.replay.open_break.is_some() {
            return None;
        }
        let at = self.running_break()?;
        let minute = |t: DateTime<FixedOffset>| t.timestamp().div_euclid(60);
        if let Some(b) = self
            .replay
            .days
            .values()
            .flat_map(|d| d.breaks.iter())
            .find(|b| minute(b.t) == minute(at.fixed_offset()))
        {
            return Some(b.clone());
        }
        let tz = self.cfg.tz;
        let now = self.now;
        let same = |b: &&BreakRecord| {
            let local = b.t.with_timezone(&tz).time();
            b.t <= now
                && local.hour() == clock.hour()
                && local.minute() == clock.minute()
                && b.planned_min == here.planned_min
                && b.r#where == here.place
        };
        let latest = |r: &Replay| r.days.values().flat_map(|d| d.breaks.iter()).filter(same).max_by_key(|b| b.t).cloned();
        if let Some(b) = latest(&self.replay) {
            return Some(b);
        }
        if self.scope == ReplayScope::All {
            return None;
        }
        // The scoped replay holds the open days only; the record of a break ended in a sealed month is
        // in the whole replay. Asked only here — a cached break the log holds no running break for —
        // which the reconcile then settles, so it is not asked again.
        // Asked once per verb (README gap 5523 as corrected by W-51 repair track H): remembered against the
        // cached break and `now`.
        if let Some((b, t, answer)) = self.break_lookup.borrow().as_ref() {
            if b == here && *t == now {
                return answer.clone();
            }
        }
        let answer = self.replay_in(ReplayScope::All).and_then(|whole| latest(&whole));
        *self.break_lookup.borrow_mut() = Some((here.clone(), now, answer.clone()));
        answer
    }

    /// **What the rebuild could not put back — computed, not listed** (README
    /// gap **1192**, the W-22 repair step).
    ///
    /// The notice used to print [`HOST_ONLY_STATE`], a constant naming four
    /// fields as *"NOT restored"*. Driven by two auditors independently: the
    /// rebuilt `.tm/state.json` was **byte-identical** to the deleted one on all
    /// four, `cmp` and all — `active.paused` came back `true`, `active.est_min`
    /// came back `120`, `priorities_yesterday` and `closed` came back with their
    /// contents — while `lime now` printed *"a paused block comes back RUNNING"*
    /// and the user read that four things were lost. A loud notice that names
    /// what it did in fact restore trains the reader to ignore it, which is what
    /// makes gap 1191 land.
    ///
    /// So each clause is now checked against the state this rebuild actually
    /// produced, and the three claims are kept apart because they are three
    /// different claims:
    ///
    /// * **Restored.** `break`, since the owner's **D105** (parity P100): the
    ///   `break_start` `lime break` logs is the running break's line, so the
    ///   rebuild puts it back with the pause it sets, and says so; and a block a
    ///   `pause` or an interruption holds comes back paused from the log's own
    ///   line, said too. Until D105 this clause read *"Gone"* — nothing in the
    ///   log said a break was running (its entry was appended when it *ended*),
    ///   and the block came back running (README gaps 1034 and 1085). A break a
    ///   binary before D105 began is still gone with the file, and nothing can
    ///   say so: the file that held it is the one deleted (README gap 4760).
    /// * **Recomputed.** `active.est_min`, from [`Ctx::planned_block`] — the
    ///   item's estimate *now*, not the one the block was started with. That is
    ///   a different source, not an absence, and the number is printed so the
    ///   reader can tell whether it looks right.
    /// * **Reset.** `priorities_yesterday` (§7.4's hysteresis; no event carries
    ///   a `p`) and `closed` — and `closed`'s reset is *deliberate*, because an
    ///   absent stamp makes the automatic sweep run once more, which is the safe
    ///   direction. Calling either of those "not restored" was true of the field
    ///   and misleading about the consequence.
    fn rebuild_notice(&self) -> Vec<String> {
        let mut out = Vec::new();
        // **A running break is RESTORED, not gone** — the owner's D105 (parity
        // P100, README gaps 1034, 1085, 4740): `lime break` logs its `break_start`,
        // so the break and the pause it sets come back from the log. Until D105
        // this line said `break` was GONE, which it was. Named when there is one,
        // so a user can see the break survived (gap 1191's rule, kept: a running
        // break's fate is never left to be found).
        if let Some(b) = self.state.break_.as_ref() {
            out.push(format!(
                "RESTORED from the log: `break` — began {}, {}m planned{} — from the `break_start` \
                 `lime break` logged (D105){}.",
                b.started.map(|t| t.format("%H:%M").to_string()).unwrap_or_else(|| "?".to_string()),
                b.planned_min,
                b.place.as_ref().map(|p| format!(", {p}")).unwrap_or_default(),
                if self.state.active.is_some() { ", and the `active.paused` it sets" } else { "" }
            ));
        } else if self.state.active.as_ref().is_some_and(|a| a.paused) {
            // A block paused with no break running: the pause is the log's own
            // `pause` (or `interrupt`) line's, and the notice says so rather than
            // leaving the reader to wonder whether it was lost (gap 1192's rule).
            out.push(
                "RESTORED from the log: `active.paused` — this block's pause came back from the \
                 log's own `pause` or `interrupt` line."
                    .to_string(),
            );
        }
        // **`active.est_min` is RESTORED since the owner's D108** (README gaps
        // 4876 and 4893, parity P119): `lime start`'s planned minutes plus the
        // minutes the block's logged `extend` lines added, as the two verbs
        // computed them. Until D108 this line said RECOMPUTED: the rebuild read
        // the extended line times the multiplier, and differed by the rounding.
        if let Some(a) = self.state.active.as_ref() {
            let ext = self.open_block_extended(&a.id);
            out.push(format!(
                "RESTORED from the log: `active.est_min` is {}m — the minutes `lime start` planned{} (D108); \
                 {}.",
                a.est_min,
                if ext > 0 { format!(" plus the {ext}m its logged `extend` lines added") } else { String::new() },
                host_only("`active.est_min`")
            ));
        }
        // **`priorities_yesterday` is RESTORED since D108**: the day's first
        // `plan` line carries it. On a day with no `plan` yet the map is empty,
        // and §7.4 reads `.tm/last_plan.json`'s anyway (`Ctx::hysteresis_input`).
        // **Asked of the CALENDAR day, by the plan lines' own stamps** (W-49 track L, the W-48 recheck's finding;
        // README gap 5301): this said RESTORED whenever the LEDGER day held a `plan` (`plans_today`), so before the
        // wake — the calendar day's lines filed under the previous ledger day — it said nothing of an input the
        // rebuild had restored, and after the wake on a day whose lines carried none it said RESTORED of nothing.
        if logged_plans(&self.replay, self.cfg.tz, self.today).input.is_some() {
            out.push(format!(
                "RESTORED from the log: `priorities_yesterday` — {} item(s), from the calendar day's `plan` line that \
                 carried it (D108).",
                self.state.priorities_yesterday.len()
            ));
        }
        // **The day with two arrivals, named rather than regenerated in
        // silence** (README gap **1306**). `DayReplay` carries the FIRST
        // arrival's window and budget and no fact carries the later ones, so
        // the rebuild recomputes them from `Ctx::arrival_window` against
        // TODAY's walls and config. Any calendar item added since the arrival
        // moves the answer, and the user is the only one who can tell whether
        // it should have.
        // Only when the rebuild DID recompute them: a wake after the last
        // arrival cleared both, and nothing was recomputed (gap 3710) — and,
        // since the window is the kernel's (W-47 track H, README gap 4746), a
        // tree whose day the kernel refused got none back, which the rebuild's
        // own `NOT recomputed` line names by the refusal instead.
        let arrivals = arrivals_today(&self.replay, self.today);
        if let (true, Some((a, b))) = (arrivals > 1 && self.state.arrival.is_some(), self.state.window) {
            out.push(format!(
                "RECOMPUTED rather than restored: `window` and `budget` — the day has \
                 {arrivals} arrivals and the log's facts carry only the first one's payload, \
                 so these are {}–{} recomputed from TODAY's walls and config; a calendar item \
                 added since the arrival moves them.",
                a.format("%H:%M"),
                b.format("%H:%M")
            ));
        }
        out.push(format!("RESET, deliberately: `closed` ({}).", host_only("`closed`")));
        out
    }

    /// **The planned minutes one block of `id` gets** (§8.5): the item's
    /// remaining estimate, or one block when it has none, through
    /// [`energy::duration_multiplier`].
    ///
    /// `lime start` writes this into `state.active.est_min` and **D42**'s rebuild
    /// puts the same number back when the cache is gone. It is one function
    /// because two would be AGENTS §5.3 — the defect this rebuild exists to
    /// stop having an instance of. `Event::Start` carries no estimate, so the
    /// rebuild asks this of the estimate the item had before the block's logged
    /// extends and adds them, as `lime extend` did ([`Ctx::rebuilt_block_minutes`],
    /// the owner's D108 — README gap 4876, closed: until then the rebuild read
    /// the extended line multiplied, `round((r + by)·m)` where the cache held
    /// `round(r·m) + by`).
    /// Returns the minutes **and** the multiplier they were computed with,
    /// because `lime start --json` prints the multiplier beside them
    /// (`StartOut::multiplier`) and reading it off a second call would be the
    /// same two-definitions mistake one step smaller.
    pub fn planned_block(&self, id: &Id) -> (u32, f64) {
        self.planned_block_of(id, self.tree.remaining(id))
    }

    /// [`Ctx::planned_block`] over a given remaining estimate — the one body of
    /// §8.5's arithmetic, which [`Ctx::rebuilt_block_minutes`] asks with the
    /// estimate the item had before its block's extends (AGENTS §5.3).
    fn planned_block_of(&self, id: &Id, remaining: Option<u32>) -> (u32, f64) {
        // `lime start` has already refused a missing line, so the `unwrap_or` is
        // reached only from the rebuild — a block the log holds whose line the
        // other writers have since removed (§1.3). `duration_multiplier` looks
        // its key up and falls through to the default tag, so `0` costs the
        // ci-specific multiplier and nothing else.
        let ci = self.tree.get(id).map(|i| i.ci).unwrap_or(0);
        let tags = self.tree.tags_effective(id);
        let multiplier = energy::duration_multiplier(&self.model, ci, &tags);
        let remaining = remaining.filter(|m| *m > 0).unwrap_or_else(|| self.block_min());
        (energy::planned_minutes(remaining, multiplier), multiplier)
    }

    /// The minutes the open block of `id` has had added by its logged `extend`
    /// lines since its `start` (the kernel's `Replay.OpenBlock.ext`, D108); `0`
    /// when no block of `id` is open.
    fn open_block_extended(&self, id: &Id) -> u32 {
        self.replay
            .open_block
            .as_ref()
            .filter(|b| b.id == id.as_str())
            .map_or(0, |b| b.extended_min)
    }

    /// **`active.est_min` as the verbs that wrote it computed it** — the
    /// owner's **D108** (README gaps 4876 and 4893, parity P119): `lime start`
    /// wrote [`Ctx::planned_block`] of the item's estimate, and every `lime
    /// extend` since added its minutes to that number. The kernel's replay holds
    /// those minutes (`OpenBlock::extended_min`), and `lime extend` also wrote
    /// each of them onto the item's line (D62, a line it rewrites: not a
    /// routine's or an optional's), so the estimate `lime start` read is the
    /// line's less them. The derivation follows the verb (D45's direction):
    /// until D108 the rebuild read the extended line times the multiplier,
    /// `round((r + by)·m)` where the verbs wrote `round(r·m) + by`.
    pub fn rebuilt_block_minutes(&self, id: &Id) -> u32 {
        let ext = self.open_block_extended(id);
        if ext == 0 {
            return self.planned_block(id).0;
        }
        let wrote = self.tree.get(id).is_some_and(|i| !super::day::is_stateless(i));
        let before = if wrote {
            Some(self.tree.remaining(id).unwrap_or(0).saturating_sub(ext))
        } else {
            self.tree.remaining(id)
        };
        self.planned_block_of(id, before).0.saturating_add(ext)
    }

    /// Re-read files, tree, log and replay after a write, in the same scope — or, while this context
    /// holds its housekeeping in memory (the owner's D96), read them as the hold leaves them
    /// ([`Ctx::settle`]): a housekeeping step reloads after it writes, and held, its writes are there.
    pub fn reload(&mut self) -> Result<(), CliError> {
        if self.holding() {
            return self.settle();
        }
        self.files = self.store.read_tree()?;
        self.tree = self.files.tree();
        let read = Ctx::replay_with(&self.store, &self.cfg, self.now, self.today, self.scope)?;
        self.replay = read.replay;
        self.ledger_day = read.ledger_day;
        Ok(())
    }

    /// **The replay a verb family asks for** (design §11.1, step R13): the
    /// [`Replay`] holding every fact `scope` covers.
    ///
    /// **This is the switch** (design §14.6 item 1). The body is
    /// [`kernel_log::replay_scoped`]: the Lean kernel derives every replay
    /// fact from `.tm/log.jsonl`, resuming the checkpoint under
    /// `.tm/cache/replay` (D13) and merging the sealed records `scope` names
    /// (§11.1). Until S this delegated to `Ctx::replay_of`, the in-tree Rust
    /// reader, which design §12 has now deleted — **one reader, and it is the
    /// proved one** (D9). No caller's shape changed, which is what made S a
    /// body swap rather than a rewrite.
    ///
    /// `now` is the undo stack's clock, not the replay's: §9.6 pins the tail
    /// at the smallest `UndoEntry.log_line` younger than 14 days, so a reseal
    /// never folds away an entry `lime undo` can still reach. With
    /// [`TRACE_SCOPE_ENV`] set it names the scope on stderr.
    ///
    /// **A missing file is an empty log, and only an I/O failure is an error.**
    /// Every unreadable line — malformed JSON, an unknown field type, a bad
    /// timestamp, or bytes that are not UTF-8 — is a per-line warning the
    /// kernel carries and the verb runs anyway (design §17's parity P13, the
    /// owner's D18 (i)). `lime check` names them through its own read-only sweep
    /// ([`kernel_log::line_warnings`]), because an answer's `warnings` array is
    /// per call.
    pub fn replay_with(
        store: &FsStore,
        cfg: &Config,
        now: DateTime<FixedOffset>,
        today: NaiveDate,
        scope: ReplayScope,
    ) -> Result<LogRead, CliError> {
        if env::var_os(TRACE_SCOPE_ENV).is_some() {
            eprintln!("replay scope: {scope}");
        }
        let bytes = Ctx::log_bytes(store)?;
        let tz = Ctx::tz_wire(store, cfg);
        let pin = kernel_log::max_line_of(
            &store.read_text(super::undo::UNDO_PATH).unwrap_or_default(),
            now,
        );
        // D18's fence on this clock (the owner's D154): what `Replay::latest_t` counts up to.
        let fence = now + chrono::Duration::days(lime_core::check::LOG_FUTURE_DAYS);
        let read = kernel_log::replay_scoped_at(
            store.root(),
            &bytes,
            cfg.tz,
            &tz,
            today,
            kernel_log::instant_wire(fence).as_array().and_then(|a| Some((a[0].as_u64()?, a[1].as_u64()?))),
            scope.to_kernel(),
            pin,
        )
        .map_err(genesis_error)?;
        // CRIT 26: an unwritable or moved cache is a notice, never a failure.
        for notice in &read.notices {
            eprintln!("{notice}");
        }
        Ok(LogRead { replay: read.replay, ledger_day: read.ledger_day })
    }

    /// The log's bytes as they are on disk now; a missing file is an empty log.
    pub(super) fn log_bytes(store: &FsStore) -> Result<Vec<u8>, CliError> {
        if store.exists(LOG_PATH) {
            Ok(store.read_bytes(LOG_PATH)?)
        } else {
            Ok(Vec::new())
        }
    }

    /// **The log as a request reads it** — the file's bytes, and the lines held in memory (the owner's
    /// D91 and D96) appended as [`Ctx::append_line`] appends them, a torn last line ended first
    /// (`Store::append_text`'s rule, P19). With nothing held, the file's bytes.
    pub fn log_now(&self) -> Result<Vec<u8>, CliError> {
        let mut bytes = Ctx::log_bytes(&self.store)?;
        if let Some(lines) = self.held.as_ref().and_then(|h| h.mirror.text(LOG_PATH)).filter(|l| !l.is_empty()) {
            if !bytes.is_empty() && !bytes.ends_with(b"\n") {
                bytes.push(b'\n');
            }
            bytes.extend_from_slice(lines.as_bytes());
        }
        Ok(bytes)
    }

    /// **The plan directory as a request reads it** (the owner's D91 and D96): the store, or while
    /// housekeeping is held in memory the plan directory as it would then stand — `config.toml` and
    /// every plan file with every held write laid over the disk's, the documents `lime plan` reads after
    /// its own housekeeping. One reader for every request built from this context: the capacity and
    /// planner request, the walls request, the whole-tree question, and the in-memory close's own.
    pub fn reading(&self) -> Result<Reading<'_>, CliError> {
        match &self.held {
            None => Ok(Reading::Disk(&self.store)),
            Some(held) => Ok(Reading::Held(held.mirror.clone())),
        }
    }

    /// **Where a housekeeping write goes** (the owner's D96): the plan directory, or — while this
    /// context holds — the mirror of it the hold keeps. §5.1's timeouts write their lines and D61's
    /// wall marks their journal lines through it ([`super::dayfile`]), so the TUI holding them runs
    /// the one body `lime plan`'s housekeeping runs, and nothing reaches the disk.
    pub fn writes(&self) -> &dyn Store {
        match &self.held {
            None => &self.store,
            Some(held) => &held.mirror,
        }
    }

    /// Whether this context holds its housekeeping in memory (the owner's D91 and D96).
    pub fn holding(&self) -> bool {
        self.held.is_some()
    }

    /// **Begin holding** (the owner's D96): every housekeeping write from here goes to memory —
    /// [`Ctx::writes`], [`Ctx::append_line`] and [`Ctx::save_state`] answer into the hold — until
    /// [`Ctx::release`]. The mirror begins as the plan directory on disk; what the context read is
    /// kept, to be put back. Holding already, nothing changes.
    pub fn hold_begin(&mut self) -> Result<(), CliError> {
        if self.held.is_some() {
            return Ok(());
        }
        let mirror = store::MemStore::new();
        if self.store.exists(store::CONFIG_PATH) {
            mirror.insert(store::CONFIG_PATH, &self.store.read_text(store::CONFIG_PATH)?);
        }
        let mut base = BTreeMap::new();
        for rel in self.store.list_files()? {
            let text = self.store.read_text(&rel)?;
            mirror.insert(&rel, &text);
            base.insert(rel, text);
        }
        self.held = Some(Held {
            docs: BTreeMap::new(),
            log: String::new(),
            mirror,
            base,
            before: (self.state.clone(), self.files.clone(), self.tree.clone(), self.replay.clone()),
        });
        Ok(())
    }

    /// **Read the context as the hold leaves it** (the owner's D96): `docs` and `log` off the mirror,
    /// the files and the tree parsed from it by the one `read_tree`, and the replay of the log as
    /// `lime plan` reads it after writing the held lines — **through a replay that writes nothing**
    /// (`kernel_log::replay_unsealed`: the process's checkpoint, no reseal, the sealed records read and
    /// never rebuilt), so the worked minutes, the candidates and the planner request read the held
    /// lines (a wall's pause among them) as `lime plan`'s reload reads the written ones. This is
    /// [`Ctx::reload`] while a context holds. Nothing held, nothing to do.
    pub fn settle(&mut self) -> Result<(), CliError> {
        let Some(held) = self.held.as_mut() else {
            return Ok(());
        };
        let mut docs = BTreeMap::new();
        for rel in held.mirror.list_files()? {
            let text = held.mirror.read_text(&rel)?;
            if held.base.get(&rel) != Some(&text) {
                docs.insert(rel, text);
            }
        }
        held.docs = docs;
        held.log = held.mirror.text(LOG_PATH).unwrap_or_default();
        let files = held.mirror.read_tree()?;
        let bytes = self.log_now()?;
        let tz = Ctx::tz_wire(&self.store, &self.cfg);
        let read = kernel_log::replay_unsealed(self.store.root(), &bytes, self.cfg.tz, &tz, self.today, self.scope.to_kernel())
            .map_err(genesis_error)?
            .ok_or_else(|| {
                CliError::msg(
                    "the replay cache names a sealed month file that is missing or does not match its digest, and reading \
                     the log as held would rebuild it — a write; the next verb rebuilds it",
                )
            })?;
        self.tree = files.tree();
        self.files = files;
        self.replay = read.replay;
        Ok(())
    }

    /// **The tree as this context read it from disk** while housekeeping is held in memory (the owner's
    /// D91) — `None` when nothing is held, when [`Ctx::tree`] is that tree. The TUI's editor opens an
    /// item where it IS, and a file a held write changed is not that file on disk.
    pub fn tree_as_read(&self) -> Option<&Tree> {
        self.held.as_ref().map(|h| &h.before.2)
    }

    /// **The files as this context read them from disk** while housekeeping is held in memory (the
    /// owner's D96) — `None` when nothing is held, when [`Ctx::files`] are those files.
    pub fn files_as_read(&self) -> Option<&PlanFiles> {
        self.held.as_ref().map(|h| &h.before.1)
    }

    /// **Let go of everything held** (the owner's D91 and D96): the state, files, tree and replay this
    /// context read before it, and nothing held. The TUI asks its housekeeping again from the plan
    /// directory as it stands at every date change and reload — ONE catch-up, as `lime plan` runs one
    /// from the files it reads, never a second stacked on the first, whose lines would carry the first
    /// midnight's stamps and keys where `lime plan`'s one catch-up carries this one's.
    pub fn release(&mut self) {
        if let Some(Held { before: (state, files, tree, replay), .. }) = self.held.take() {
            self.state = state;
            self.files = files;
            self.tree = tree;
            self.replay = replay;
        }
    }

    /// The zone table the kernel attributes days with (§6.1), from the cache
    /// under the plan root when its key still matches, else probed (D13).
    pub(crate) fn tz_wire(store: &FsStore, cfg: &Config) -> Value {
        super::tz_table::wire_for(Some(&store.root().join(kernel_log::CACHE_DIR)), cfg.tz)
    }

    /// **The empty replay**, for the one verb that answers over a log no
    /// rebuild can window (gap 145, D18 (iii)).
    ///
    /// It is the *kernel's* answer for a log of no lines, not a hand-built
    /// value: §5.3's rule — a second definition of "an empty replay" would be
    /// a second reader of the same concept. It never touches the checkpoint on
    /// disk, because genesis over zero lines seals nothing.
    fn empty_replay(cfg: &Config, tz: &Value, today: NaiveDate) -> Result<Replay, CliError> {
        let want = kernel_log::Want { facts: true, headers_from: None, render: vec![], fence: None };
        let policy = kernel_log::Policy { keep_days: kernel_log::KEEP_DAYS, max_line: None };
        let now = today.format("%Y-%m-%d").to_string();
        let g = kernel_log::genesis(&now, tz, &kernel_log::split(&[]), policy, &want)
            .map_err(genesis_error)?;
        let answer = serde_json::json!({
            "lines": g.answer.lines,
            "facts": g.answer.facts.clone().unwrap_or(Value::Null),
            "headers": g.answer.headers.clone(),
        });
        kernel_log::decode_facts(&answer, cfg.tz)
            .map_err(|why| CliError::msg(format!("the kernel's empty replay: {why}")))
    }

    /// **What the undo recorder reads, through the same door** (design §14.3
    /// rows R6 and R8): the log's physical line count on disk now and, when
    /// `after` is given, the entries on the physical lines after it, each with
    /// its line, in file order. The count is exactly
    /// the whole replay's line count, and the headers are exactly the whole
    /// replay's from `after + 1` (design §14.3 row R6), without replaying the
    /// lines before `after`: a mutating verb used to replay the whole log twice
    /// more for its undo entry (W-3's audit: 4 replays a verb, ≈ 110 ms each on
    /// three years of log). A log with fewer lines than `after` (rewritten under
    /// the verb) has no tail and yields none.
    ///
    /// **This is the switch** (design §14.6 item 1): the body is the kernel's
    /// `headersFrom` ([`kernel_log::headers_after`]), which replays the tail
    /// alone from the empty checkpoint and shifts each header's line back into
    /// the whole file's numbering — exactly what the in-tree reader did here
    /// before §12 deleted it.
    pub fn log_tail_of(
        store: &FsStore,
        cfg: &Config,
        today: NaiveDate,
        after: Option<u64>,
    ) -> Result<(u64, Vec<LogHeader>), CliError> {
        let bytes = Ctx::log_bytes(store)?;
        let count = lime_core::log::physical_line_count(&bytes);
        let Some(after) = after else {
            return Ok((count, Vec::new()));
        };
        let tz = Ctx::tz_wire(store, cfg);
        let now = today.format("%Y-%m-%d").to_string();
        let rows = kernel_log::headers_after(&bytes, &now, &tz, after)
            .map_err(|why| CliError::msg(format!("{LOG_PATH}: the kernel could not read the tail ({why})")))?
            .into_iter()
            .map(|(line, tag, id)| LogHeader { line, tag, id })
            .collect();
        Ok((count, rows))
    }

    /// **The payload of the lines a verb selected** (design §11.4 step 3): the
    /// raw bytes of each line of `lines`, read from `.tm/log.jsonl` by physical
    /// line number and parsed.
    ///
    /// `lime log` is the one verb that shows a line's payload rather than its
    /// header. §11.4 gives it this order — select headers, then read the bytes
    /// of the selected lines, then render them — and this is that read: the
    /// selection comes from [`Replay::view`], and only the selected lines are
    /// parsed. A line the reader refuses has no [`lime_core::log::ViewRow`]
    /// either, so it cannot be selected and is simply absent from the map.
    ///
    /// **This is the switch** (§11.4 step 4): the body is the kernel's `render`
    /// op ([`kernel_log::render_lines`]), which returns each line's canonical
    /// rendering — **as the line's own bytes** (D22) — and its display, from the
    /// same bytes on disk. Until S the bytes were parsed here with
    /// `LogEntry::parse`, which design §12 has deleted.
    pub fn entries_at(
        store: &FsStore,
        cfg: &Config,
        today: NaiveDate,
        lines: &[u64],
    ) -> Result<BTreeMap<u64, (Box<RawValue>, String)>, CliError> {
        let mut out = BTreeMap::new();
        if lines.is_empty() {
            return Ok(out);
        }
        let bytes = Ctx::log_bytes(store)?;
        let wanted: BTreeSet<u64> = lines.iter().copied().collect();
        let tz = Ctx::tz_wire(store, cfg);
        let now = today.format("%Y-%m-%d").to_string();
        out.extend(
            kernel_log::render_lines(&bytes, &now, &tz, lines).map_err(|why| {
                CliError::msg(format!("{LOG_PATH}: the kernel could not render the selected lines ({why})"))
            })?,
        );
        // **Every asked line comes back, or this read fails by name.** The
        // paragraph above is an invariant, not a hope: `Log::parse_bytes`
        // pushes a line into `Log::lines` — and so gives it a `ViewRow` —
        // in exactly the case this loop inserts it, off the same bytes. But
        // these are two reads of one file at two instants, so a writer that
        // truncates or rewrites `.tm/log.jsonl` between them can take away a
        // line the selection has already made. Unguarded, that line was
        // absent from `--json`'s `entries` while `log_human` still printed
        // its header from the row, and the two outputs disagreed in silence.
        // Naming it costs nothing on a file nobody rewrites mid-command,
        // which is why no behaviour moves; at S the kernel's `render` op
        // answers the same lines and this guard goes with the body.
        if out.len() != wanted.len() {
            let missing = lines.iter().find(|l| !out.contains_key(l)).copied().unwrap_or(0);
            return Err(CliError::msg(format!(
                "{LOG_PATH} changed while this command was reading it: line {missing} did not \
                 read back; run the command again"
            )));
        }
        Ok(out)
    }

    /// A [`horizon::Ctx`] over the current snapshot (§6.3).
    pub fn hz(&self) -> horizon::Ctx<'_> {
        horizon::Ctx::new(&self.store, &self.files, &self.tree, self.now)
            .with_replay(&self.replay)
            // D16: the id-less fallback paths (gap 5) write the kernel's bytes too, so every
            // line the *binary* appends has one definition of its format.
            .writing_lines_with(kernel_log::render_one)
    }

    /// Append one event to `.tm/log.jsonl` (§10.1).
    pub fn append_event(&self, ev: Event) -> Result<(), CliError> {
        self.append_entry(&LogEntry::new(self.now, ev))
    }

    /// Append one already-timestamped entry.
    ///
    /// **The kernel writes the line** (owner decision **D16**; design §22.1's step S2): the verb
    /// sends the event's values and appends the bytes the kernel hands back, so
    /// `LogEntry::to_json` is no longer the binary's writer and the log's format has **one**
    /// definition — the kernel's grammar, reached through the same `Log.renderLine` the reader
    /// reads through. The bytes do not move (`the_log_emits_what_it_reads`, and T2 over every
    /// writable event); what changes is who decides them.
    ///
    /// A refusal is an error and never a written line: an event whose values the reader would
    /// refuse is named rather than appended.
    pub fn append_entry(&self, entry: &LogEntry) -> Result<(), CliError> {
        let line = Ctx::render_entry(entry)?;
        self.append_line(&line)
    }

    /// **The bytes a verb appends for `entry`** — the kernel's rendering (D16), or
    /// the refusal named. The one definition [`Ctx::append_entry`] appends and
    /// D91's in-memory close holds (`closing::close_in_memory`), so the lines the
    /// TUI holds past midnight and the lines a verb writes cannot be two
    /// renderings of one event (README gap 4504, the W-43 repair).
    pub fn render_entry(entry: &LogEntry) -> Result<String, CliError> {
        kernel_log::render_one(entry)
            .map_err(|why| CliError::msg(format!("the kernel could not write this log line: {why}")))
    }

    /// **Append one line the kernel wrote** (D16) — the bytes as the kernel
    /// rendered them, and a newline. The one appender of `.tm/log.jsonl`:
    /// [`Ctx::append_entry`] renders through it, and so do the lines the
    /// kernel decides itself (the walls' timer marks, README gap 3139).
    /// While this context holds its housekeeping in memory (the owner's D96)
    /// the line is held ([`Ctx::writes`]' mirror) and the log is not touched.
    pub fn append_line(&self, line: &str) -> Result<(), CliError> {
        let mut line = line.to_string();
        line.push('\n');
        self.writes().append_text(LOG_PATH, &line)?;
        Ok(())
    }

    /// Write `.tm/state.json` (§10.2). While this context holds its
    /// housekeeping in memory (the owner's D96) nothing is written: the state
    /// in memory IS the held one, and [`Ctx::release`] puts back the one read.
    pub fn save_state(&self) -> Result<(), CliError> {
        if self.holding() {
            return Ok(());
        }
        self.store.save_state(&self.state)?;
        Ok(())
    }

    /// The key an id-ish argument names: `^t3`, `t3` or the title of an
    /// id-less routine/optional line.
    pub fn key(arg: &str) -> Id {
        Id::new(arg.trim().trim_start_matches('^'))
    }

    /// The item behind an argument, or a "no such item" error.
    ///
    /// **An ambiguous title is refused, never resolved** (W-16 repair, gap
    /// 578). D31 keys a box-less, id-less line by its title, so two lines with
    /// one title are two lines with one address — and `Tree`'s own index gives
    /// the key to the *first* of them and keys the second `file:line`. Every
    /// verb that addresses an item by name reaches this function, and until the
    /// repair `lime drop laundry` and `lime edit laundry ci=3` on a tree with two
    /// `laundry` routines wrote the first line, exited 0 and said nothing —
    /// disambiguate-by-occurrence, which is the option **D32 declined** for the
    /// kernel and AGENTS §5.6's "the loader never picks between two readings"
    /// for everyone else. The kernel refuses the whole tree for the same
    /// collision (`LErr.dupId`, naming both lines); this names both lines too,
    /// in the same path-then-line order, so the two refusals read alike.
    ///
    /// [`Tree::ambiguous_title`] is the one place that decides it; this only
    /// asks.
    pub fn item(&self, id: &Id) -> Result<&Item, CliError> {
        self.refuse_ambiguous_title(id)?;
        self.tree
            .get(id)
            .ok_or_else(|| CliError::NotFound(id.clone()))
    }

    /// **The refusal itself**, so the three verbs that look an argument up in
    /// `self.tree` directly rather than through [`Ctx::item`] — `lime done <id>`
    /// (which tolerates a missing line, §1.3), `lime skip` and `lime routine done`
    /// (both through `instance_of`) — say the same thing in the same words.
    /// [`Tree::ambiguous_title`] is the one place that *decides* it.
    ///
    /// The key is printed bare, in backticks, and not as `^title`: a title key
    /// is never written into a file, which is the fact the kernel's own `dupId`
    /// message spells out and the reason the two positions are what the user
    /// has to go on.
    pub fn refuse_ambiguous_title(&self, id: &Id) -> Result<(), CliError> {
        let Some(spots) = self.tree.ambiguous_title(id) else {
            return Ok(());
        };
        let where_ = spots
            .iter()
            .map(|(path, line)| format!("{path}:{line}"))
            .collect::<Vec<_>>()
            .join(" and ");
        Err(CliError::msg(format!(
            "`{}` names {} lines and nothing says which: {where_}. A line with no `^id` is \
             keyed by its title, so a repeated title is an ambiguous address — the kernel \
             refuses the whole tree for it (`dupId`, naming the same two lines) and this verb \
             will not pick one. Give one of the lines an `^id`, or change a title.",
            id.as_str(),
            spots.len(),
        )))
    }

    /// The item's line, tokenized for a byte-faithful edit (§4.1).
    pub fn line(&self, id: &Id) -> Result<ItemLine, CliError> {
        Ok(self.item(id)?.line().clone())
    }

    /// Replace the item's line with `line`'s text (§1.3) — through [`Ctx::writes`], so a
    /// held context (the owner's D96) holds it: the stop §6.3's close writes before it takes
    /// a running block's item (D130, `day::end_the_block`) rewrites the line inside the TUI's
    /// held close, and every verb's own write, which never runs held, reaches the disk.
    pub fn write_line(&self, id: &Id, line: &ItemLine) -> Result<(), CliError> {
        self.writes().write_line(id, &line.to_string())?;
        Ok(())
    }

    /// **A copy of this context** for the TUI's planner (R3; `tui::mod.rs`'s
    /// `kernel_planner`), which asks the kernel for the day at every minute over
    /// the plan directory as this context read it — the documents and the log
    /// as held (D84, D91, D96), `.tm/state.json`, the tree and the replay —
    /// and moves only its own clock. Its store is a store over the same root,
    /// with no write hook: the planner writes nothing.
    pub fn fork(&self) -> Ctx {
        Ctx {
            store: FsStore::new(self.store.root()),
            cfg: self.cfg.clone(),
            json: self.json,
            now: self.now,
            now_tz: self.now_tz,
            today: self.today,
            state: self.state.clone(),
            files: self.files.clone(),
            tree: self.tree.clone(),
            replay: self.replay.clone(),
            replay_fault: self.replay_fault.clone(),
            ledger_day: self.ledger_day,
            scope: self.scope,
            model: self.model.clone(),
            timed_out: self.timed_out.clone(),
            held: self.held.clone(),
            break_lookup: std::cell::RefCell::new(self.break_lookup.borrow().clone()),
        }
    }

    /// `cfg.day.block_min`.
    pub fn block_min(&self) -> u32 {
        self.cfg.block_min()
    }

    /// The current location (§8.2 step 3's `runtime.loc`).
    pub fn loc(&self) -> Loc {
        self.state
            .loc
            .as_deref()
            .and_then(|s| Loc::parse(s).ok())
            .unwrap_or(Loc::Lounge)
    }

    /// Today's wake: `state.wake`, else the `wake` event of the day, else the
    /// fallback [`Model::wake_or_expected`] owns — the weekday's expected
    /// arrival (§8.4, §16 `[expected]`). This is the resolution the kernel's
    /// day reads too — the capacity request sends [`Ctx::logged_wake`] and
    /// `Look.wakeOf` applies this fallback, fork `Ctx::wake_time`'s, which fork
    /// 4748911's planner ran until R3 deleted it — in the same order and
    /// through the same fallback, so a plan and the verbs that cut their own
    /// slots read one wake.
    pub fn wake_time(&self) -> NaiveTime {
        self.model
            .wake_or_expected(self.logged_wake(), self.today.weekday(), &self.cfg)
    }

    /// The wake today actually has: `state.wake`, else the `wake` event of the
    /// day — what [`Ctx::wake_time`] falls back from, and what the capacity
    /// request sends as `wake` (the kernel applies the same fallback).
    pub fn logged_wake(&self) -> Option<NaiveTime> {
        self.state.wake.or_else(|| {
            self.replay
                .day(self.today)
                .and_then(|d| d.wake)
                .map(|t| t.with_timezone(&self.cfg.tz).time())
        })
    }

    /// Today's wake instant in `cfg.tz` — the PLANNED day's wake, the day bar's
    /// origin (`render::svg`).
    pub fn wake_dt(&self) -> DateTime<Tz> {
        capacity::local_dt(self.cfg.tz, self.today, self.wake_time())
    }

    /// **The wake that has HAPPENED**: the LATEST instant at or before now
    /// whose local clock is [`Ctx::wake_time`]'s ([`capacity::latest_at_or_before`])
    /// — what hours since wake counts from on every `energy` and `start` line
    /// the binary logs (`day::features`; the W-41 repair, README gap 4140;
    /// parity P79), by the rule P73 reads a running break's start by (the
    /// campaign's D81 call on README gap 3820). Fork 4748911 counted from
    /// [`Ctx::wake_dt`], the clock on TODAY's date, and `.tm/state.json`'s
    /// `wake` survives the midnight roll (`RuntimeState::roll_to`), so after
    /// local midnight `lime energy` at 00:30 logged `hsw: -6.5` for a day woken
    /// at 07:00 — a wrong fact in the log the fit reads, D75's reason. It is
    /// not `wake_dt`: the day bar draws the PLANNED day from that day's wake,
    /// a different instant from the last wake before now (README gap 4140 says
    /// why the bar was left alone).
    pub fn woke_before_now(&self) -> DateTime<Tz> {
        capacity::latest_at_or_before(self.cfg.tz, self.now_tz, self.wake_time())
    }

    /// **The wake that had happened by `at`** — [`Ctx::woke_before_now`] for an
    /// instant on today's date (P79, unchanged), and for one on an EARLIER date
    /// — the one line counted to such an instant is a `lime energy --at` report the
    /// owner's D86 dates yesterday (W-42 track H, README gap 4260, parity P82) —
    /// THAT day's own wake, the instant the log holds (D75's clock), when it is
    /// at or before `at`, else the latest instant at or before `at` with
    /// [`Ctx::wake_time`]'s clock. P79's reading there, today's wake, is AFTER the
    /// report: `--at 22:00` typed at 09:00 the next morning counted `hsw: -9.0`,
    /// the wrong fact P79 removed.
    pub fn woke_before(&self, at: DateTime<Tz>) -> DateTime<Tz> {
        let day = at.date_naive();
        if day >= self.today {
            return self.woke_before_now();
        }
        let logged = self.replay.day(day).and_then(|d| d.wake).map(|w| w.with_timezone(&self.cfg.tz));
        match logged.filter(|w| *w <= at) {
            Some(w) => w,
            None => capacity::latest_at_or_before(self.cfg.tz, at, self.wake_time()),
        }
    }

    /// Minutes slept the night before `day`, when `lime wake` recorded them —
    /// [`Ctx::slept_min`] on any date (a `lime energy --at` report D86 dates
    /// yesterday reads yesterday's night).
    pub fn slept_on(&self, day: NaiveDate) -> Option<u32> {
        self.replay.day(day).and_then(|d| d.slept_min)
    }

    /// Minutes slept last night, when `lime wake` recorded them.
    pub fn slept_min(&self) -> Option<u32> {
        self.slept_on(self.today)
    }

    /// A local time on today's date, in `cfg.tz`.
    pub fn at(&self, t: NaiveTime) -> DateTime<Tz> {
        capacity::local_dt(self.cfg.tz, self.today, t)
    }

    /// **When the break `.tm/state.json` holds running began** — the ONE
    /// reading every verb takes. **The log's instant first** (the owner's
    /// **D105**, parity P100, D75's rule for a block's start applied to a
    /// break's): the `t` of the `break_start` no `break` has ended
    /// ([`lime_core::log::Replay::open_break`]), so the `break` line that ends it
    /// is stamped where its start was logged, to the second, on whatever date.
    /// A break the log holds no `break_start` for — one a binary before D105
    /// began — keeps the cache's clock read as
    /// [`lime_core::store::BreakState::started_at`] reads it (the latest instant
    /// at or before `now` with the cached clock; the campaign's D81 call on
    /// README gap 3820, parity P73). Never [`Ctx::at`]: a break begun before
    /// local midnight is the evening's after it. `None` with no break running,
    /// or one with no `started`.
    pub fn running_break(&self) -> Option<DateTime<Tz>> {
        self.state.running_break_at(&self.replay, self.cfg.tz, self.now_tz)
    }

    /// **§8.1's working window and block budget from one arrival** — the ONE
    /// definition `lime arrive` writes into `.tm/state.json` and D42's rebuild
    /// derives back out of the log (the owner's **D45**, AGENTS §5.3).
    ///
    /// It is not a resurrection of the `Ctx::window` this module's header says
    /// is gone. That one answered "what is today's window?" beside the
    /// kernel's own answer, which is the two-definitions bug; this answers
    /// "what does `lime arrive` write at `at`?", and its two callers are `lime
    /// arrive` and the rebuild — the writer and the derivation, agreeing by
    /// construction rather than by inspection.
    ///
    /// **What it reads that the log does not carry.** The walls and the config
    /// are **today's**, not the ones standing when the arrival was logged, so
    /// a calendar item added since moves the window this returns. That is the
    /// same fidelity [`Ctx::planned_block`] gives `active.est_min` — the
    /// estimate the item carries *now* — and it is the honest one: a derivable
    /// cache is a function of the tree it is derived from. The alternative,
    /// reading `Event::Arrive`'s own `window` back, can only answer for the
    /// **first** arrival of the day (`DayReplay::window`), which is the defect
    /// D45 exists to close.
    ///
    /// **The kernel's since W-47 track H** (README gap 4746, parity P113):
    /// [`kernel_capacity::arrival_window`], the day's own request over the state
    /// the arrival would store, and the window and budget the kernel plans that
    /// day by. Until then it was `capacity::window_and_budget` over
    /// `Ctx::walls_today` (deleted with it) — the host's reading of the walls
    /// beside the kernel's, which the kernel's day then read back as the stored
    /// window.
    pub fn arrival_window(&self, at: NaiveTime) -> Result<((NaiveTime, NaiveTime), u32), CliError> {
        kernel_capacity::arrival_window(self, at)
    }

    // **`Ctx::walls_today` and `Ctx::walls_on` went with their last caller at W-47 track H**
    // (README gap 4746): the window `lime arrive` stores is the kernel's, over the kernel's walls
    // (`Look.wallsClippedOn`), so no verb reads the host's `Tree::walls_on` any more; that function
    // lives on in `lime-core` as the comparand of the fork's walls.

    // **`Ctx::window` and `Ctx::today_slots` were deleted at stage 6 step L9** (gap 93).
    // §8.1's window and §8.2 step 3's slots for today are the kernel's now: the capacity request
    // carries `at`, `state` and `allowHome`, the kernel reads last night's sleep and today's
    // energy reports off its own replay through D24's seam, and `Look.day0Hist` is the answer
    // (`Look.day_zero_is_the_spec_day_energised`).  Keeping a second definition here is exactly
    // the bug AGENTS §5.3 names; the fork's two functions live on as the comparand of
    // `lime/tests/kernel_lookahead_parity.rs`, the way the fork's walls (`Tree::walls_on`) do.

    /// Yesterday's `p` per item (§7.4). `state.priorities_yesterday` holds it
    /// once the day has rolled; before the first plan of a new day the last
    /// stored plan is the previous day's, so its priorities are the ones to
    /// compare against.
    ///
    /// **The log's input first** (the W-48 repair, README gap 5211; the owner's D108 and D42): once today's first
    /// `plan` line carries the input, every machine reading that log ranks against it — the critic drove two
    /// machines syncing one plan directory (the template's own sync model: `log.jsonl` synced, `.tm/state.json`
    /// and `.tm/last_plan.json` per machine) ranking one log `p5` and `p3`. Before today's first `plan` the input
    /// is still this machine's last stored plan's (README gap 5221).
    pub fn hysteresis_input(&self) -> BTreeMap<Id, u8> {
        if let Some(logged) = logged_plans(&self.replay, self.cfg.tz, self.today).input {
            return logged;
        }
        let stored = self.last_plan().unwrap_or_default();
        match stored.date {
            Some(d) if d == self.today => self.state.priorities_yesterday.clone(),
            Some(_) => stored.priorities,
            None => self.state.priorities_yesterday.clone(),
        }
    }

    /// `.tm/last_plan.json`, if it is readable.
    pub fn last_plan(&self) -> Option<StoredPlan> {
        self.store.read_json::<StoredPlan>(LAST_PLAN_PATH).ok().flatten()
    }

    /// Write `.tm/last_plan.json`.
    pub fn save_last_plan(&self, plan: &StoredPlan) -> Result<(), CliError> {
        self.store.write_json(LAST_PLAN_PATH, plan)?;
        Ok(())
    }

    /// The number of `plan` events already logged today (§10.1
    /// `replans_today`).
    pub fn plans_today(&self) -> u32 {
        self.replay.day(self.today).map(|d| d.plans).unwrap_or(0)
    }

    /// §5.1: `[?]` items whose `on-event:` timeout has elapsed go back to
    /// `[ ]` with `est:` reset and `waiting:` removed. Returns what changed.
    ///
    /// **Only on a tree the kernel loads whole** (the owner's D6: a dangling
    /// or cyclic `@parent` refuses the whole tree). `refused` says the
    /// automatic close ahead of this was refused, which settles it without a
    /// second call; otherwise, when some timeout has elapsed, the one shared
    /// write gate ([`kernel_bridge::tree_refusal`], the owner's D35) asks the
    /// kernel whether the tree still loads. A refusal skips every timeout,
    /// writes nothing and logs nothing, and is named on stderr — so a verb
    /// that then refuses the same tree has written nothing either
    /// (kernel/README.md "Stage 4 final, repair", defect 1: before this, a
    /// typo'd parent on the example tree's Monday rewrote `^a4` and created
    /// the log ahead of a refusal that said nothing was written). A kernel
    /// fault still fails the verb.
    ///
    /// It asked `kernel_bridge::apply(self, &[])` until D35 — the same
    /// question through the machine that ends in a write step. `tree_refusal`
    /// goes to `kernel_bridge::call` directly and cannot write at all, so
    /// there is now exactly **one** definition of "does the kernel load this
    /// tree" in the binary (AGENTS §5.3).
    fn resolve_timeouts(&mut self, refused: bool) -> Result<Vec<Id>, CliError> {
        let mut expired_ids = Vec::new();
        for id in self.tree.waiting_ids() {
            let Some(item) = self.tree.get(&id) else {
                continue;
            };
            if recur::waiting_state(item, &self.replay, self.today, &self.cfg).is_some_and(|w| w.expired) {
                expired_ids.push(id);
            }
        }
        if expired_ids.is_empty() || refused {
            return Ok(Vec::new());
        }
        if let Some(issue) = kernel_bridge::tree_refusal(self)? {
            if !kernel_bridge::capturing_kernel_stderr() {
                eprintln!(
                    "lime: the waiting timeouts (§5.1) were not applied, so nothing was written; \
                     they run again on the next command. {}",
                    issue.message
                );
            }
            return Ok(Vec::new());
        }
        let mut changed = Vec::new();
        for id in expired_ids {
            let Some(item) = self.tree.get(&id) else {
                continue;
            };
            let mut line = item.line().clone();
            recur::on_event_arrived(item).apply(&mut line)?;
            // Through `writes`: the plan directory, or held in memory past midnight (D96).
            self.writes().write_line(&id, &line.to_string())?;
            self.append_event(Event::Edit {
                id: id.to_string(),
                field: "state".to_string(),
                from: State::Waiting.as_str().to_string(),
                to: State::Todo.as_str().to_string(),
            })?;
            changed.push(id);
        }
        Ok(changed)
    }

    /// Every id already used in the tree — the uniqueness set new ids are
    /// drawn against (§17.2).
    pub fn taken_ids(&self) -> HashSet<String> {
        self.files.ids()
    }
}

#[cfg(test)]
#[path = "../../tests/support/loggen.rs"]
#[allow(dead_code)]
mod loggen;

#[cfg(test)]
mod tests {
    use super::*;

    /// **The field list and the notice do not drift apart** (README gap 1192).
    ///
    /// [`HOST_ONLY_STATE`] stopped being the sentence `lime` prints at the W-22
    /// repair step — it was a constant claiming four fields were lost while the
    /// rebuilt file came back byte-identical on all four — and stayed the
    /// *documentation* of which §10.2 fields the log cannot answer for.
    /// [`Ctx::rebuild_notice`] computes the sentence instead. This is what still
    /// ties the two together: two entries since the owner's D108 (three after
    /// D105, five before it; `break`, `active.paused` and `priorities_yesterday`
    /// became derivable), each leading with the
    /// field it is about, in the spelling the notice uses.
    ///
    /// **What it cannot check**: that the notice still *prints* each of them.
    /// That needs a `Ctx`, and it is what the two T9 cases in
    /// `cli_switch_acceptance.rs` are for.
    #[test]
    fn every_host_only_field_leads_its_own_entry() {
        // `break` and `active.paused` left the table with the owner's D105 (parity P100):
        // the `break_start` `lime break` logs makes both derivable; `priorities_yesterday` left
        // it with the owner's D108 (parity P119): the day's first `plan` line carries it.
        let fields = ["`active.est_min`", "`closed`"];
        assert_eq!(
            HOST_ONLY_STATE.len(),
            fields.len(),
            "HOST_ONLY_STATE has {} entries and this test knows {}",
            HOST_ONLY_STATE.len(),
            fields.len()
        );
        for ((name, why), field) in HOST_ONLY_STATE.iter().zip(fields) {
            assert_eq!(*name, field, "the table is not in the order this test knows");
            assert!(!why.is_empty(), "{field} has no reason beside it");
            assert_eq!(host_only(field), *why, "`host_only` cannot find {field}");
        }
    }

    /// The body of an `insta` JSON snapshot: everything after its `---`
    /// header.
    fn snapshot_body(name: &str) -> serde_json::Value {
        let path = format!(
            "{}/tests/snapshots/log_ported_facts__{name}.snap",
            env!("CARGO_MANIFEST_DIR")
        );
        let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let body = text.splitn(3, "---\n").nth(2).unwrap_or_else(|| panic!("{path}: no header"));
        serde_json::from_str(body).unwrap_or_else(|e| panic!("{path}: {e}"))
    }

    /// **`lime log`'s two outputs cannot disagree about which lines they carry.**
    /// `Ctx::entries_at` is the second host-side read of `.tm/log.jsonl` in one
    /// `lime log` (the first is the replay's), and until the guard it enforces
    /// the doc comment's invariant it dropped a line it could not read back:
    /// `--json`'s `entries` lost it while `log_human` still printed its header
    /// from the row. A line the reader never accepted has no `ViewRow` and is
    /// never asked for, so this fires only on a log rewritten mid-command —
    /// and then it is named, not swallowed.
    #[test]
    fn a_line_that_does_not_read_back_is_named_not_dropped() {
        let dir = tempfile::TempDir::new().expect("tempdir");
        std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
        // Real lines, from the generator the other tests here use: a line the
        // reader refuses never becomes a `ViewRow` and so is never asked for,
        // which is the invariant this guard rests on.
        let gen = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 1));
        let first: Vec<&str> = gen.lines().take(2).collect();
        assert_eq!(first.len(), 2, "the generator gives at least two lines");
        let text = format!("{}\n", first.join("\n"));
        std::fs::write(dir.path().join(LOG_PATH), &text).expect("write log");
        let store = FsStore::new(dir.path());
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let today = NaiveDate::from_ymd_opt(2030, 1, 1).expect("date");

        // The lines the selection can actually make: both come back.
        let got = Ctx::entries_at(&store, &cfg, today, &[1, 2]).expect("both lines read back");
        assert_eq!(got.len(), 2);
        // Nothing asked for, nothing read.
        assert!(Ctx::entries_at(&store, &cfg, today, &[]).expect("no lines").is_empty());

        // A line the file does not hold — what a truncating writer leaves
        // behind between the replay's read and this one.
        let err = Ctx::entries_at(&store, &cfg, today, &[1, 5]).expect_err("line 5 cannot read back");
        let msg = err.to_string();
        assert!(msg.contains("line 5"), "the failure names the line: {msg}");
        assert!(msg.contains(LOG_PATH), "the failure names the file: {msg}");
    }

    /// D14 (step R11): the facts nothing reads reach every caller through the
    /// one door — **the kernel's, since S**. `Ctx::replay_with` over each log on
    /// disk gives the [`lime_core::log::PortedFacts`] that
    /// `lime/tests/log_ported_facts.rs` pins.
    ///
    /// **Its comparand is bytes on disk, not a second reader.** Until S this
    /// also compared the chokepoint against `Log::parse(text).replay(..)`;
    /// design §12 deleted that reader, and had this test kept only that arm it
    /// would now be comparing the kernel with itself (README gap 146). The
    /// pinned snapshot is what survives the deletion, and it is the arm that was
    /// always doing the work: the values were measured from the fork's own
    /// reader and committed.
    #[test]
    fn the_chokepoint_returns_the_ported_facts() {
        let corpus = |n: &str| {
            std::fs::read_to_string(format!("{}/../kernel/corpus/logs/{n}.jsonl", env!("CARGO_MANIFEST_DIR")))
                .expect("corpus log")
        };
        let logs = [
            ("three_days", corpus("three-days")),
            ("energy_14d", corpus("energy-14d")),
            ("review_14d", corpus("review-14d")),
            ("malformed", corpus("malformed")),
            ("loggen_1mo_40", loggen::text(&loggen::log(loggen::Rate::Forty, 30))),
            ("loggen_1mo_61", loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30))),
        ];
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let (now, today) = late_clock();
        for (name, text) in &logs {
            let dir = tempfile::TempDir::new().expect("tempdir");
            std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
            std::fs::write(dir.path().join(LOG_PATH), text).expect("write log");
            let store = FsStore::new(dir.path());
            let door = Ctx::replay_with(&store, &cfg, now, today, ReplayScope::All)
                .expect("replay_with")
                .replay;
            let json = serde_json::to_value(door.ported_facts()).expect("json");
            assert_eq!(json, snapshot_body(name), "{name}: the pinned values");
        }
    }

    /// An instant after every log these tests read, in both shapes the door
    /// wants: `now` is the undo stack's clock and `today` the day the kernel
    /// answers for. Later than every fixture, so no line is future-dated and
    /// every day of every log is a past day.
    fn late_clock() -> (DateTime<FixedOffset>, NaiveDate) {
        let now = DateTime::parse_from_rfc3339("2030-01-01T09:00:00-05:00").expect("instant");
        (now, now.date_naive())
    }

    /// W-3's repair: the recorder's tail read is the whole replay's rows from
    /// the same line, and its count the whole replay's, at every cut of logs
    /// with malformed, blank, CRLF and torn lines.
    #[test]
    fn the_recorders_tail_is_the_whole_replays() {
        let gen = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 2));
        let mut lines: Vec<&str> = gen.lines().collect();
        lines.truncate(60);
        let good = lines.join("\n");
        let torn = &lines[3][..lines[3].len() / 2];
        let texts = [
            String::new(),
            "\n".to_string(),
            format!("{good}\n"),
            good.clone(),
            format!("{}\n\n{}\nnot json\n{}\r\n{}\n", lines[0], lines[1], lines[2], lines[4]),
            format!("{}\n{torn}", lines[0]),
            format!("{}\n{torn}{}\n{}\n", lines[0], lines[5], lines[6]),
            format!("{}\n\u{00e9}\u{0000}\n{}\n", lines[7], lines[8]),
        ];
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let (now, today) = late_clock();
        for (k, text) in texts.iter().enumerate() {
            let dir = tempfile::TempDir::new().expect("tempdir");
            std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
            if k > 0 {
                std::fs::write(dir.path().join(LOG_PATH), text).expect("write log");
            }
            let store = FsStore::new(dir.path());
            let whole = Ctx::replay_with(&store, &cfg, now, today, ReplayScope::All)
                .expect("replay_with")
                .replay;
            let (count, none) = Ctx::log_tail_of(&store, &cfg, today, None).expect("count");
            assert_eq!((count, none.len()), (whole.line_count(), 0), "text {k}");
            for after in 0..=whole.line_count() + 2 {
                let (count, rows) = Ctx::log_tail_of(&store, &cfg, today, Some(after)).expect("tail");
                let want: Vec<LogHeader> = whole
                    .headers_from(after + 1)
                    .iter()
                    .map(|r| LogHeader { line: r.line, tag: r.tag.clone(), id: r.id.clone() })
                    .collect();
                assert_eq!(count, whole.line_count(), "text {k}");
                assert_eq!(rows, want, "text {k}, after {after}");
            }
        }
    }

    /// Step R13, **turned around at S** (README gap 140's sibling): before the
    /// switch every scope *was* the whole log, because `Ctx::replay_with`
    /// delegated to the one Rust reader and ignored the scope entirely. Since S
    /// each scope is the kernel's own (§11.1) and a narrow one **legitimately**
    /// carries fewer day records — so the old assertion would now be false, and
    /// asserting it would mean the switch had not happened.
    ///
    /// What replaces it is the claim the scopes exist to preserve, and it is
    /// the one that bites: **every scope answers, and every all-time fact is
    /// whole at every scope** (design §8.4's column **A**; gaps 135 and 136).
    /// Those are exactly the facts a narrowing could silently shrink — a
    /// `lime log` total that counted only the scope's rows, or a recurrence
    /// anchor that lost the dates below the horizon.
    ///
    /// The sharper per-scope claim — that each day record a narrow scope *does*
    /// carry is the whole log's — is made where it has a comparand that is not
    /// the kernel: `lime/tests/kernel_log_door.rs`.
    #[test]
    fn every_all_time_fact_is_whole_at_every_scope_after_the_switch() {
        let d = |s: &str| NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date");
        let text = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30));
        let cfg = Config { tz: chrono_tz::America::Chicago, ..Config::default() };
        let (now, today) = late_clock();
        let dir = tempfile::TempDir::new().expect("tempdir");
        std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir");
        std::fs::write(dir.path().join(LOG_PATH), &text).expect("write log");
        let store = FsStore::new(dir.path());
        let whole = Ctx::replay_with(&store, &cfg, now, today, ReplayScope::All)
            .expect("replay_with")
            .replay;
        // Not vacuous: the log really does hold the days and the completions
        // the loop below says survive every narrowing.
        assert_eq!(whole.line_count(), text.lines().count() as u64, "the All scope reads every line");
        assert!(whole.days.len() > 7, "the fixture must be wider than one scope: {}", whole.days.len());
        assert!(!whole.done_date_totals.is_empty(), "the fixture logs no completion");
        for scope in [
            ReplayScope::Hot,
            ReplayScope::Dates { from: d("2026-09-01"), to: d("2026-09-07") },
            ReplayScope::All,
        ] {
            let r = Ctx::replay_with(&store, &cfg, now, today, scope).expect("replay_with").replay;
            assert_eq!(r.entry_count(), whole.entry_count(), "{scope}: entryCount is all-time");
            assert_eq!(r.line_count(), whole.line_count(), "{scope}: the line count is the file's");
            assert_eq!(r.done_date_totals, whole.done_date_totals, "{scope}: the done-date totals");
            assert_eq!(r.done_items, whole.done_items, "{scope}: the done items");
            assert_eq!(r.last_done, whole.last_done, "{scope}: the last completion per item");
        }
    }
}
