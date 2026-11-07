//! **`lime now` prints ONE reading of the running block's worked minutes**
//! (stage 6 W-35 track E, README gap 2741).
//!
//! The header's `{elapsed}m of {est}m` was the wall clock since `started`, so
//! after an interruption `lime now` said `55m of 60m` in its header while the `▶`
//! row directly below it said `running · 35m left` — which is 60 − 25, the
//! WORKED minutes: two numbers for one fact on one screen. The `▶` row's
//! `left`, the open-block row's `so far` in `lime plan`, the TUI's
//! `App::active_elapsed_min`, §9.1's overtime prompt and the kernel's
//! `openWorkedMin` all read the log's open block (`OpenBlock::worked_min_at`:
//! pauses, breaks and interruptions stop the timer). The header reads it too
//! now, through the one rule both surfaces share, `Replay::active_worked_min`.
//!
//! **W-35 repair (README gap 2920): the rule under that name was a SECOND
//! reading, not the one.** The replay's open block is fork `Machine::step`'s
//! and never sees a `break` (the entry is written when the break ends), so
//! after a five-minute break `lime now` said `30m of 30m` while `lime done`, a
//! moment later, logged `actual_min: 25` — two numbers for one fact, one of
//! them in the log. `Replay::active_worked_min` is `lime done`'s own rule now
//! (fork `day::worked_min`, moved into the replay): the wall clock net of the
//! day's pauses, interruptions and breaks, the running break included. The
//! tests at the end of this file pin the header against the minutes `lime done`
//! WRITES.

mod cli_common;

use cli_common::Lime;

/// After a 30-minute interruption the header, the JSON, the `▶` row's `left`
/// and `lime plan`'s open-block row all read the same 25 worked minutes of the
/// 55 on the wall clock.
#[test]
fn lime_now_reads_one_worked_minutes_after_an_interruption() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T09:10:00-05:00", &["interrupt"]);
    lime.ok_at("2026-09-07T09:40:00-05:00", &["resume"]);
    let at = "2026-09-07T09:55:00-05:00";

    let json = lime.json_at(at, &["now"]);
    assert_eq!(json["active"]["id"], "t4", "{json}");
    assert_eq!(json["active"]["est_min"], 60, "{json}");
    assert_eq!(
        json["active"]["elapsed_min"], 25,
        "the header's minutes are the worked ones, not the 55 on the wall clock: {json}"
    );

    let out = lime.run_at(at, &["now"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let head = out.stdout.lines().next().unwrap_or_default().to_string();
    assert!(head.starts_with("▶ ^t4 "), "{}", out.stdout);
    assert!(head.ends_with("· 25m of 60m"), "the header: {head}");
    // The `▶` row below it leaves what the header has not used: 60 − 25.
    assert!(
        out.stdout.contains("running · 35m left"),
        "the row and the header agree: {}",
        out.stdout
    );
    assert!(
        !out.stdout.contains("55m"),
        "the wall-clock reading is gone from the screen: {}",
        out.stdout
    );

    // And `lime plan`'s open-block row names the same number as worked so far.
    let plan = lime.run_at(at, &["plan"]);
    assert_eq!(plan.code, 0, "{}{}", plan.stdout, plan.stderr);
    assert!(plan.stdout.contains("25m so far"), "{}", plan.stdout);
}

/// With nothing stopping the timer the two readings are the same number, so the
/// rule changes nothing on an uninterrupted block (`cli_plan`'s own 30).
#[test]
fn an_uninterrupted_block_reads_the_wall_clock_minutes() {
    let lime = Lime::new();
    lime.ok(&["start", "^t4", "--energy", "4"]);
    let json = lime.json_at("2026-09-07T09:30:00-05:00", &["now"]);
    assert_eq!(json["active"]["elapsed_min"], 30, "{json}");
}

/// The last `done` entry's `actual_min` in the tree's log.
fn logged_actual(lime: &Lime) -> Option<u64> {
    lime.last_ev("done")["actual_min"].as_u64()
}

/// **The W-35 audit's drive, pinned** (README gap 2920): a block with a
/// five-minute break, a five-minute pause and a five-minute interruption inside
/// it. Forty minutes on the wall clock, 25 worked. `lime now`'s header, its JSON
/// and the `actual_min` `lime done` writes are one number; before this repair the
/// header said 30 — the open block, which counts the break as worked.
#[test]
fn lime_now_and_lime_done_read_one_worked_minutes_across_a_break() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T09:05:00-05:00", &["break", "5m"]);
    lime.ok_at("2026-09-07T09:10:00-05:00", &["break"]);
    lime.ok_at("2026-09-07T09:15:00-05:00", &["pause"]);
    lime.ok_at("2026-09-07T09:20:00-05:00", &["pause"]);
    lime.ok_at("2026-09-07T09:25:00-05:00", &["interrupt"]);
    lime.ok_at("2026-09-07T09:30:00-05:00", &["resume"]);
    let at = "2026-09-07T09:40:00-05:00";
    let json = lime.json_at(at, &["now"]);
    assert_eq!(json["active"]["elapsed_min"], 25, "40 on the clock, 15 idle: {json}");
    let out = lime.run_at(at, &["now"]);
    let head = out.stdout.lines().next().unwrap_or_default().to_string();
    assert!(head.ends_with("· 25m of 60m"), "the header: {head}");
    lime.ok_at(at, &["done"]);
    assert_eq!(logged_actual(&lime), Some(25), "`lime done` logs the header's minutes");
}

/// **A break still running is not worked either.** `lime break` writes no entry
/// until the break ends, so the header must read `state.json`'s running break:
/// at 09:45, twenty minutes into a break begun at 09:20, the block has been
/// worked 20 minutes, not 45 — and `lime done` a minute later, which closes the
/// break, logs the same 20.
#[test]
fn a_running_break_stops_the_headers_minutes() {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    lime.ok_at("2026-09-07T09:20:00-05:00", &["break", "30m"]);
    let json = lime.json_at("2026-09-07T09:45:00-05:00", &["now"]);
    assert_eq!(json["active"]["elapsed_min"], 20, "the running break is idle: {json}");
    lime.ok_at("2026-09-07T09:46:00-05:00", &["done"]);
    assert_eq!(logged_actual(&lime), Some(20), "`lime done` logs the header's minutes");
}
