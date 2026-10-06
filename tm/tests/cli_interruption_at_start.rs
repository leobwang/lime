//! **An interruption still open at a block's `start` holds it until the `resume`, for the host as for the replay** —
//! the owner's **D99** (README gap **4619**, W-47 track K, parity **P103**).
//!
//! The kernel's replay has always read it so (fork 4748911's own machine: a `start` while an interruption is open
//! begins a block whose clock is held until the `resume`, P60), and `tm start` says so ("paused: an interruption is
//! open"). The host's worked minutes (`Replay::idle_min_since`) paired the idle marks of the block's OWN ledger days,
//! so an interruption begun on an EARLIER ledger day — the `interrupt` mark filed under that day — was not among them,
//! and the minutes from the `start` to the `resume` were counted as worked. DRIVEN at `49186d7`
//! (`scratchpad/w47-k/drive/class.sh M10`, `class-head.out`): an interruption at 21:00, the next morning's `tm wake`
//! refused over it (D81), `start` 08:00, `resume` 08:30 — `tm now` at 09:00 said `60m of 360m`, `tm done` at 09:10
//! logged `actual_min: 70`, while the replay's clock ran from the `resume` (its Block row 08:30-09:10). Now the host's
//! pairing begins with the interruption the log holds open at the `start` (`Replay::interrupted_before`, the one
//! reading the rebuild's `ctx::logged_stops` takes too): 30, 40, 40.

mod cli_common;

use std::fs;

use cli_common::Tm;

fn at(day: u32, hm: &str) -> String {
    format!("2026-09-{day:02}T{hm}:00-05:00")
}

/// The example tree, an interruption opened the evening before, the morning's wake refused over it, `^m1` started
/// inside it and the interruption resumed half an hour later.
fn held_overnight() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at(7, "06:00"), &["init", "--example"]);
    tm.ok_at(&at(7, "07:00"), &["wake", "07:00"]);
    tm.ok_at(&at(7, "21:00"), &["interrupt"]);
    let refused = tm.run_at(&at(8, "07:00"), &["wake", "07:00"]);
    assert_ne!(refused.code, 0, "D81 refuses a wake over an open interruption: {}", refused.stdout);
    let start = tm.ok_at(&at(8, "08:00"), &["start", "^m1", "--energy", "3"]);
    assert!(start.stdout.contains("paused: an interruption is open"), "{}", start.stdout);
    tm.ok_at(&at(8, "08:30"), &["resume"]);
    tm
}

fn elapsed(tm: &Tm, day: u32, hm: &str) -> u64 {
    tm.json_at(&at(day, hm), &["now"])["active"]["elapsed_min"].as_u64().expect("elapsed_min")
}

/// The `actual_min` of the log's last `done`.
fn logged_done(tm: &Tm) -> u64 {
    let log = fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log");
    let line = log.lines().rev().find(|l| l.contains("\"ev\":\"done\"")).expect("a done line");
    let v: serde_json::Value = serde_json::from_str(line).expect("json");
    v["actual_min"].as_u64().expect("actual_min")
}

#[test]
fn an_interruption_open_since_the_day_before_holds_the_block_until_the_resume() {
    let tm = held_overnight();
    assert_eq!(elapsed(&tm, 8, "09:00"), 30, "only the half hour after the resume was worked");
    // The cache follows the log (D42): deleting it rebuilds the same reading.
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(elapsed(&tm, 8, "09:00"), 30);
    tm.ok_at(&at(8, "09:10"), &["done"]);
    assert_eq!(logged_done(&tm), 40, "tm done logs the minutes after the resume");
    let review = tm.json_at(&at(8, "09:11"), &["review", "day"]);
    assert_eq!(review["review"]["block_min"].as_u64(), Some(40), "{review}");
}

/// **The control**: the same interruption resumed before the `start` holds nothing — the block runs from its start.
#[test]
fn an_interruption_resumed_before_the_start_holds_nothing() {
    let tm = Tm::empty();
    tm.ok_at(&at(7, "06:00"), &["init", "--example"]);
    tm.ok_at(&at(7, "07:00"), &["wake", "07:00"]);
    tm.ok_at(&at(7, "21:00"), &["interrupt"]);
    tm.ok_at(&at(7, "21:30"), &["resume"]);
    tm.ok_at(&at(8, "07:00"), &["wake", "07:00"]);
    tm.ok_at(&at(8, "08:00"), &["start", "^m1", "--energy", "3"]);
    assert_eq!(elapsed(&tm, 8, "09:00"), 60);
    tm.ok_at(&at(8, "09:10"), &["done"]);
    assert_eq!(logged_done(&tm), 70);
}

/// **The same day's interruption was always netted** (its mark is among the block's own day's), and still is once.
#[test]
fn an_interruption_open_since_earlier_the_same_day_is_netted_once() {
    let tm = Tm::empty();
    tm.ok_at(&at(7, "06:00"), &["init", "--example"]);
    tm.ok_at(&at(7, "07:00"), &["wake", "07:00"]);
    tm.ok_at(&at(7, "07:30"), &["interrupt"]);
    tm.ok_at(&at(7, "08:00"), &["start", "^m1", "--energy", "3"]);
    tm.ok_at(&at(7, "08:30"), &["resume"]);
    assert_eq!(elapsed(&tm, 7, "09:00"), 30);
    tm.ok_at(&at(7, "09:10"), &["done"]);
    assert_eq!(logged_done(&tm), 40);
}
