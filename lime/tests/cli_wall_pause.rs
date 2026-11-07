//! **A calendar wall that starts while a block is running STOPS THE TIMER** —
//! the owner's D61 (stage 6 W-36 track T, README gaps 2805 and 2932).
//!
//! `plan-basic`'s calendar holds `^g1 Meeting w/ host at:2026-09-07T12:50/13:50`.
//! A block started at 12:00 runs into it. Before D61 nothing was logged at the
//! wall: `tm now` counted the meeting as worked (`80m of 60m` at 13:20), `tm
//! done` logged it as `actual_min`, and `tm plan` drew the open stretch from
//! 12:00 across the meeting. Now the first verb after the wall BEGAN logs a
//! `pause` stamped at its start, and the first verb after it ENDED an `unpause`
//! stamped at its end — the log's own events, no new kind — so every reading
//! of the block nets the meeting out.
//!
//! Every test reads the log's bytes, not only an exit code: WHEN the entries are
//! written, and that they are written once, is the rule.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// The meeting's start and end, as the log stamps them.
const WALL_START: &str = "2026-09-07T12:50:00-05:00";
const WALL_END: &str = "2026-09-07T13:50:00-05:00";

/// `(ev, t)` of every `pause`/`unpause` entry, in file order.
fn timer_marks(tm: &Tm) -> Vec<(String, String)> {
    tm.log()
        .iter()
        .filter(|e| e["ev"] == "pause" || e["ev"] == "unpause")
        .map(|e| (e["ev"].as_str().unwrap_or_default().to_string(), e["t"].as_str().unwrap_or_default().to_string()))
        .collect()
}

/// A day with `^t4` started at 12:00, forty minutes before the meeting.
fn running_before_the_meeting() -> Tm {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

fn active(tm: &Tm, at: &str) -> Value {
    tm.json_at(at, &["now"])["active"].clone()
}

/// **The drive, pinned**: during the meeting the header reads the fifty minutes
/// before it and says `paused`; after it, fifty plus the twenty since it ended;
/// `tm done` logs those minutes — eighty, where the wall clock says 140.
#[test]
fn a_wall_that_starts_while_a_block_runs_stops_its_timer() {
    let tm = running_before_the_meeting();
    assert!(timer_marks(&tm).is_empty(), "nothing is written before the wall begins");

    let during = active(&tm, "2026-09-07T13:20:00-05:00");
    assert_eq!(during["elapsed_min"], 50, "the meeting is not worked: {during}");
    assert_eq!(during["paused"], true, "the wall paused the timer: {during}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string())],
        "the first verb after the wall began logged the pause at its start"
    );

    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["elapsed_min"], 70, "fifty before the meeting and twenty since: {after}");
    assert_eq!(after["paused"], false, "the wall's end restarted it: {after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string()), ("unpause".to_string(), WALL_END.to_string())],
        "the first verb after the wall ended logged the unpause at its end, once"
    );

    tm.ok_at("2026-09-07T14:20:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 80, "`tm done` logs the minutes the header read");
    assert_eq!(timer_marks(&tm).len(), 2, "nothing was written twice");
}

/// **A verb run only after the wall ended writes both, in order, once** — the
/// automatic close's catching-up shape — and `tm plan` then draws the running
/// stretch from the meeting's END, not from 12:00 across it.
#[test]
fn a_verb_after_the_wall_writes_the_pair_and_the_plan_draws_no_stretch_across_it() {
    let tm = running_before_the_meeting();
    let plan = tm.json_at("2026-09-07T14:10:00-05:00", &["plan"]);
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string()), ("unpause".to_string(), WALL_END.to_string())]
    );
    let segs = plan["segments"].as_array().cloned().unwrap_or_default();
    let t4: Vec<(String, String, String)> = segs
        .iter()
        .filter(|s| s["item"] == "t4")
        .map(|s| {
            (
                s["kind"].as_str().unwrap_or_default().to_string(),
                s["start"].as_str().unwrap_or_default().to_string(),
                s["end"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect();
    assert!(
        t4.iter().any(|(k, a, b)| k == "block" && a == "12:00" && b == "12:50"),
        "the stretch before the meeting ends at its start: {t4:?}"
    );
    assert!(
        !t4.iter().any(|(k, a, b)| k == "block" && a.as_str() < "13:50" && b.as_str() > "12:50"),
        "no block of ^t4 lies across the meeting: {t4:?}"
    );
    // A second verb writes nothing more.
    tm.ok_at("2026-09-07T14:15:00-05:00", &["now"]);
    assert_eq!(timer_marks(&tm).len(), 2);
}

/// **A timer the user stopped is not the wall's to touch**: paused at 12:30, the
/// block was not running when the meeting began, so nothing is logged at it and
/// the timer stays stopped after it.
#[test]
fn a_timer_already_stopped_at_the_wall_is_left_alone() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:30:00-05:00", &["pause"]);
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["paused"], true, "{after}");
    assert_eq!(after["elapsed_min"], 30, "{after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T12:30:00-05:00".to_string())],
        "only the user's own pause"
    );
}

/// **A user who skipped the meeting keeps the timer they set** (the cost D61
/// names: undercounted UNTIL they correct it): the wall paused the block at
/// 12:50, the user unpaused at 13:05 and worked on, and the wall's end writes no
/// unpause of its own over the user's.
#[test]
fn a_user_who_unpaused_during_the_meeting_keeps_their_timer() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:00:00-05:00", &["now"]);
    tm.ok_at("2026-09-07T13:05:00-05:00", &["pause"]);
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["paused"], false, "{after}");
    assert_eq!(after["elapsed_min"], 115, "50 before the wall and 65 since the user unpaused: {after}");
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), WALL_START.to_string()),
            ("unpause".to_string(), "2026-09-07T13:05:00-05:00".to_string()),
        ],
        "no second unpause at the wall's end"
    );
}

/// **A timer mark already stamped inside the meeting is the user's word** —
/// the log is the user's file too (hand-edited, or synced from a machine that
/// paused at 13:05 without this housekeeping). The wall's pause is never
/// inserted UNDER a later mark, so its automatic unpause at 13:50 cannot lift
/// the user's own pause: at 14:10 the block has worked 65 minutes, 12:00 to
/// the user's 13:05, and nothing was written.
#[test]
fn a_timer_mark_already_inside_the_meeting_is_left_to_stand() {
    let tm = running_before_the_meeting();
    let log = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&log).expect("read the log");
    text.push_str("{\"t\":\"2026-09-07T13:05:00-05:00\",\"ev\":\"pause\",\"id\":\"t4\"}\n");
    std::fs::write(&log, text).expect("write the log");
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["elapsed_min"], 65, "{after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T13:05:00-05:00".to_string())],
        "no wall pause under the user's mark, and so no wall unpause over it"
    );
}

/// **A block started inside a wall is paused from its start until the wall
/// ends** — the owner's **D110** (README gap 4748, W-47 track K, parity
/// **P106**), through the marks D61 writes.  Until W-47 this test pinned the
/// opposite ("the wall did not start while the block ran": `elapsed_min` 60
/// at 14:00 and no mark) — the line P106 moves, named here.  The first verb
/// after the start writes the `pause` stamped at the block's own start, the
/// first after the wall ended the `unpause` at its end, once each.
#[test]
fn a_block_started_inside_the_wall_is_paused_from_its_start() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let during = active(&tm, "2026-09-07T13:30:00-05:00");
    assert_eq!(during["elapsed_min"], 0, "the meeting is not worked: {during}");
    assert_eq!(during["paused"], true, "{during}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T13:00:00-05:00".to_string())],
        "the pause is stamped at the block's start, not at the wall's"
    );
    let after = active(&tm, "2026-09-07T14:00:00-05:00");
    assert_eq!(after["elapsed_min"], 10, "the ten minutes since the meeting ended: {after}");
    assert_eq!(after["paused"], false, "{after}");
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T13:00:00-05:00".to_string()),
            ("unpause".to_string(), WALL_END.to_string())
        ],
        "the unpause at the wall's end, written once"
    );
    let stop = tm.ok_at("2026-09-07T14:05:00-05:00", &["stop"]);
    assert!(stop.stdout.contains("after 15m"), "{}", stop.stdout);
    let review = tm.json_at("2026-09-07T14:06:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["block_min"].as_u64(), Some(15), "{review}");
    assert_eq!(timer_marks(&tm).len(), 2, "nothing was written twice");
}

/// **A block started after the wall ended is not the wall's**: nothing is
/// written (D110's boundary).
#[test]
fn a_block_started_after_the_wall_is_not_paused_by_it() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T13:55:00-05:00", &["start", "^t4", "--energy", "4"]);
    let after = active(&tm, "2026-09-07T14:25:00-05:00");
    assert_eq!(after["elapsed_min"], 30, "{after}");
    assert!(timer_marks(&tm).is_empty(), "{:?}", timer_marks(&tm));
}

/// **A block that ends inside the meeting leaves its wall pause open, and the
/// NEXT block's minutes are still its own** (README gap 2920, the host's one
/// reading).  `tm done` at 13:20 closes `^t4` with the wall's pause unlifted;
/// `^t1` starts after the meeting, and at 14:30 it has run thirty minutes.
/// Before W-36 the host's rule let a pause stamped before a block began swallow
/// it (next test), so D61 would have made this read zero.
#[test]
fn a_block_that_ended_inside_the_meeting_leaves_the_next_block_its_own_minutes() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:20:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 50, "the meeting is not in `^t4`'s minutes");
    tm.ok_at("2026-09-07T14:00:00-05:00", &["start", "^t1", "--energy", "4"]);
    let now = active(&tm, "2026-09-07T14:30:00-05:00");
    assert_eq!(now["id"], "t1", "{now}");
    assert_eq!(now["elapsed_min"], 30, "the old block's open pause is not the new block's: {now}");
    tm.ok_at("2026-09-07T14:35:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 35);
}

/// **The defect under it, with no wall at all** — driven on `dd8b95b`: `tm
/// pause` then `tm done` logs no `unpause`, and the host's worked-minutes rule
/// (fork `day::worked_min`) kept that pause open into the next block, so `tm
/// now` read `elapsed_min: 0` for `^t1` and `tm done` logged `actual_min: 0`.
#[test]
fn a_pause_left_open_by_a_paused_done_is_not_the_next_blocks() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T09:10:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T09:20:00-05:00", &["done"]);
    tm.ok_at("2026-09-07T09:30:00-05:00", &["start", "^t1", "--energy", "4"]);
    let now = active(&tm, "2026-09-07T10:00:00-05:00");
    assert_eq!(now["elapsed_min"], 30, "{now}");
    tm.ok_at("2026-09-07T10:05:00-05:00", &["done"]);
    assert_eq!(tm.last_ev("done")["actual_min"], 35);
}

/// The `## Log` section of a day file, one journal line per element.
fn journal(tm: &Tm, rel: &str) -> Vec<String> {
    let text = tm.read(rel);
    text.lines()
        .skip_while(|l| *l != "## Log")
        .skip(1)
        .take_while(|l| !l.starts_with("## "))
        .filter(|l| !l.trim().is_empty())
        .map(str::to_string)
        .collect()
}

/// **A verb run inside a meeting does not take `tm undo` away** (W-37 repair,
/// README gap 3330; D37). D65 gave the wall's pause the day file's journal line,
/// written by housekeeping before any undo recorder runs — so the next `tm
/// undo` of the `tm start` before it found a line it did not write and refused
/// with exit 3 (driven on `faaaac6`; the same drive undid the start on
/// `b3c29a3`). The housekeeping write now goes UNDER the stack: the start is
/// undone, and the pause's journal line stays, as the pause's log entry does.
#[test]
fn a_start_before_a_meeting_can_still_be_undone() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    assert!(journal(&tm, "day/2026-09-07.md").contains(&"12:50 pause ^t4".to_string()));
    let out = tm.run_at("2026-09-07T13:25:00-05:00", &["undo"]);
    assert_eq!(out.code, 0, "the start is undone: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("undid start"), "{}", out.stdout);
    assert!(tm.state()["active"].is_null(), "no block is running: {}", tm.state());
    let j = journal(&tm, "day/2026-09-07.md");
    assert!(!j.iter().any(|l| l.contains("start ^t4")), "the start's journal line is gone: {j:?}");
    assert!(
        j.contains(&"12:50 pause ^t4".to_string()),
        "the pause's journal line stays, as its log entry does: {j:?}"
    );
    assert_eq!(timer_marks(&tm), vec![("pause".to_string(), WALL_START.to_string())]);
}

/// **An undo under the pause keeps the pause** (gap 3330): an unrelated command
/// (an energy report, which writes the day file's journal) is undone after the wall paused
/// the block; the block stays running AND paused — the state the log says —
/// and the pause's journal line stays.
#[test]
fn an_undo_under_a_meeting_pause_keeps_the_pause() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:30:00-05:00", &["energy", "3"]);
    let before = journal(&tm, "day/2026-09-07.md");
    assert!(before.iter().any(|l| l.starts_with("12:30 energy")), "{before:?}");
    tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]);
    let out = tm.run_at("2026-09-07T13:25:00-05:00", &["undo"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let j = journal(&tm, "day/2026-09-07.md");
    assert!(!j.iter().any(|l| l.starts_with("12:30 energy")), "the report is undone: {j:?}");
    assert!(j.contains(&"12:50 pause ^t4".to_string()), "{j:?}");
    let a = &tm.state()["active"];
    assert_eq!(a["id"], "t4", "{a}");
    assert_eq!(a["paused"], true, "the undo put back the state the log says: {a}");
    let now = active(&tm, "2026-09-07T13:30:00-05:00");
    assert_eq!(now["paused"], true, "{now}");
    assert_eq!(now["elapsed_min"], 50, "{now}");
}

/// **The evening before's meeting is paused, and each mark is journaled on its
/// own day** (README gap 3334). `^t4` began at 22:30; a meeting at 22:40–22:50
/// and a late call at 23:30–00:30 follow; the first verb runs at 00:10. The
/// kernel read the walls of the verb's day alone, so the 22:40 meeting wrote
/// nothing, and the host journaled the 23:30 pause into the NEXT day's file.
#[test]
fn a_meeting_the_evening_before_is_paused_and_journaled_on_its_own_day() {
    let tm = Tm::new();
    let cal = tm.plan.join("calendar/2026-W37.md");
    let text = std::fs::read_to_string(&cal).expect("read the calendar");
    let text = text.replace(
        "- [ ] 2 CS 234 lecture       at:2026-09-09T15:00/16:20 loc:JCL ^g2",
        "- [ ] 2 Late call          at:2026-09-07T23:30/2026-09-08T00:30 loc:zoom ^g2\n\
         - [ ] 2 Evening sync       at:2026-09-07T22:40/22:50 loc:zoom ^g5",
    );
    assert!(text.contains("Evening sync"), "the fixture line was found");
    std::fs::write(&cal, text).expect("write the calendar");
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T22:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-08T00:10:00-05:00", &["now"]);
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T22:40:00-05:00".to_string()),
            ("unpause".to_string(), "2026-09-07T22:50:00-05:00".to_string()),
            ("pause".to_string(), "2026-09-07T23:30:00-05:00".to_string()),
        ],
        "both meetings stop the timer"
    );
    let j = journal(&tm, "day/2026-09-07.md");
    for want in ["22:40 pause ^t4", "22:50 unpause ^t4", "23:30 pause ^t4"] {
        assert!(j.contains(&want.to_string()), "{want} is in the evening's own file: {j:?}");
    }
    if tm.exists("day/2026-09-08.md") {
        let next = journal(&tm, "day/2026-09-08.md");
        assert!(!next.iter().any(|l| l.contains("pause ^t4")), "nothing in the next day's file: {next:?}");
    }
}

/// **A break begun inside the meeting and still running at its end keeps the block off the drawing**
/// (W-47 repair, README gap 5020): `^t4` started 12:30, the meeting pauses it at 12:50, `tm break 30m` at
/// 13:00, and at 14:00 — the break overrun, still running — the meeting's `unpause` (13:50) is logged.  The
/// host's worked minutes net the running break (20, the stretch before the meeting); until this repair the
/// kernel's day drew the block from 13:50 to `now` across the break's row, so the day held a Block over a
/// Break on a log the binary wrote with a forward clock.  Now no `^t4` block lies across the break.
#[test]
fn a_block_unpaused_by_the_meetings_end_is_not_drawn_across_a_running_break() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["break", "30m", "--where", "walk"]);
    let plan = tm.json_at("2026-09-07T14:00:00-05:00", &["plan"]);
    // **Moved at W-48 track K under parity P115 (the owner's D114, README gap 5014)**: the meeting's `unpause`
    // is NOT logged while the break that began inside it still runs — the break holds the block — and is
    // logged when the break ends (`a_running_break_past_the_meeting_holds_the_block_until_it_ends`). Until
    // W-48 this line read the pause AND the unpause at 14:00.
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string())],
        "the meeting's pause is logged, its unpause held by the running break"
    );
    let segs = plan["segments"].as_array().cloned().unwrap_or_default();
    let span = |s: &Value| (s["start"].as_str().unwrap_or_default().to_string(), s["end"].as_str().unwrap_or_default().to_string());
    let breaks: Vec<(String, String)> = segs.iter().filter(|s| s["kind"] == "break").map(span).collect();
    assert_eq!(breaks, vec![("13:00".to_string(), "14:00".to_string())], "the running break, overrun to now: {segs:?}");
    let blocks: Vec<(String, String)> = segs.iter().filter(|s| s["kind"] == "block" && s["item"] == "t4").map(span).collect();
    assert!(
        blocks.iter().all(|(a, b)| b.as_str() <= "13:00" || a.as_str() >= "14:00"),
        "no block of ^t4 lies across the running break: {blocks:?}"
    );
    assert!(blocks.contains(&("12:30".to_string(), "12:50".to_string())), "the stretch before the meeting stays drawn: {blocks:?}");
    assert_eq!(active(&tm, "2026-09-07T14:00:00-05:00")["elapsed_min"], 20, "the host's minutes net the running break");
}

/// **A break still running when the meeting ends holds the block paused** — the owner's **D114** (README gap
/// **5014**, stage 6 W-48 track K, parity **P115**). Driven at `1a37997`: `^t4` started 12:30, the meeting pauses it
/// at 12:50, `tm break 30m` at 13:00, and at 14:00 — the break overrun, still running — the meeting's `unpause`
/// (13:50) was logged and `tm now` headed `20m of 60m` running beside a running break. Now the unpause waits: at
/// 14:00 the block reads paused, and the verb that ends the break (here `tm start ^t4`, D107's continue) logs the
/// unpause stamped at the meeting's end, after the break's own line, once.
#[test]
fn a_running_break_past_the_meeting_holds_the_block_until_it_ends() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:30:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["break", "30m", "--where", "walk"]);
    let during = active(&tm, "2026-09-07T14:00:00-05:00");
    assert_eq!(during["paused"], true, "the running break holds the block past the meeting: {during}");
    assert_eq!(during["elapsed_min"], 20, "the stretch before the meeting: {during}");
    assert_eq!(timer_marks(&tm), vec![("pause".to_string(), WALL_START.to_string())], "no unpause yet");
    tm.ok_at("2026-09-07T14:05:00-05:00", &["start", "^t4"]);
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string()), ("unpause".to_string(), WALL_END.to_string())],
        "the break's end logs the meeting's unpause"
    );
    let evs: Vec<String> = tm.log().iter().map(|e| e["ev"].as_str().unwrap_or_default().to_string()).collect();
    let brk = evs.iter().rposition(|e| e == "break").expect("the break's line");
    let unp = evs.iter().rposition(|e| e == "unpause").expect("the unpause");
    assert!(brk < unp, "the unpause follows the line that ends the break: {evs:?}");
    let after = active(&tm, "2026-09-07T14:06:00-05:00");
    assert_eq!(after["paused"], false, "{after}");
    assert_eq!(after["elapsed_min"], 21, "twenty before the meeting and one since the break ended: {after}");
    let stop = tm.ok_at("2026-09-07T14:30:00-05:00", &["stop"]);
    assert!(stop.stdout.contains("after 45m"), "{}", stop.stdout);
    assert_eq!(timer_marks(&tm).len(), 2, "nothing was written twice");
}

/// **A block resumed inside a meeting is paused until it ends** — the owner's **D117** (README gaps **5036** and
/// **3042**, stage 6 W-48 track K, parity **P116**), D110's rule for a resume. Driven at `1a37997`: `^t4` started
/// 12:00, `tm interrupt` 12:40, `tm resume` 13:00 inside the 12:50–13:50 meeting, `tm stop` 14:00 — `after 100m`,
/// the meeting counted as work, because the interruption across the wall's start stood for the wall's stop and
/// nothing was written. Now the next verb logs a `pause` stamped at the resume and the `unpause` at the wall's end.
#[test]
fn a_block_resumed_inside_the_wall_is_paused_until_it_ends() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:40:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["resume"]);
    let during = active(&tm, "2026-09-07T13:30:00-05:00");
    assert_eq!(during["paused"], true, "{during}");
    assert_eq!(during["elapsed_min"], 40, "only the forty minutes before the interruption: {during}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), "2026-09-07T13:00:00-05:00".to_string())],
        "the pause is stamped at the resume, not at the wall's start"
    );
    let stop = tm.ok_at("2026-09-07T14:00:00-05:00", &["stop"]);
    assert!(stop.stdout.contains("after 50m"), "forty before the interruption, ten after the meeting: {}", stop.stdout);
    assert_eq!(
        timer_marks(&tm),
        vec![
            ("pause".to_string(), "2026-09-07T13:00:00-05:00".to_string()),
            ("unpause".to_string(), WALL_END.to_string()),
        ]
    );
    let review = tm.json_at("2026-09-07T14:01:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["block_min"].as_u64(), Some(50), "{review}");
}

/// **An interruption inside a meeting the wall paused leaves the wall's end its unpause** (the owner's D117: a block
/// resumed inside a wall is paused only until the wall ends). The wall's pause logged at 12:50, `tm interrupt` 13:05,
/// `tm resume` 13:10: until W-48 the `resume` became the last word on the timer, the wall's end logged no unpause,
/// and `tm stop` at 14:20 said `after 50m` — the block held paused past the meeting. Now the unpause is logged at
/// 13:50 and the thirty minutes since count.
#[test]
fn an_interruption_inside_the_meeting_leaves_the_walls_end_its_unpause() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:00:00-05:00", &["now"]);
    tm.ok_at("2026-09-07T13:05:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T13:10:00-05:00", &["resume"]);
    let after = active(&tm, "2026-09-07T14:10:00-05:00");
    assert_eq!(after["paused"], false, "{after}");
    assert_eq!(
        timer_marks(&tm),
        vec![("pause".to_string(), WALL_START.to_string()), ("unpause".to_string(), WALL_END.to_string())]
    );
    let stop = tm.ok_at("2026-09-07T14:20:00-05:00", &["stop"]);
    assert!(stop.stdout.contains("after 80m"), "{}", stop.stdout);
}
