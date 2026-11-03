//! **The replay's reading of finished breaks through the binary** — stage 6 W-54 repair track K (README gaps 5920-5939).
//!
//! * **D145** (parity **P142**): a `break` line read while a break runs, not stamped in the running break's start's
//!   minute, ends only its own break — the running break stays running, no verb re-logs it (D133), and deleting
//!   `.tm/state.json` changes nothing (D42).
//! * **D151** (parity P148 restated): the widest end a re-time out may reach is the latest end the break's OWN lines
//!   gave it; the end D129 inferred from a later `start` is not one.
//! * **The finished-break fact's overlap filter** (gap 5925): a break any other held break overlaps is not re-timed;
//!   the host refuses the keystroke by name (gap 5895) and writes nothing.
//! * **D152's replay half**: a finished break line inside the running block nets it and leaves it running.

mod cli_common;

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Tm;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

fn tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

/// The J day: `^t1` 09:00–10:00 and `^t4` 10:10–11:10, both done.
fn j_day() -> Tm {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    tm
}

fn append(tm: &Tm, line: &str) {
    let mut f = OpenOptions::new().append(true).open(tm.plan.join(".tm/log.jsonl")).expect("the log");
    writeln!(f, "{line}").expect("append a line");
}

fn review(tm: &Tm, now: &str) -> (u64, Vec<(u64, u64)>) {
    let v = tm.json_at(&at(now), &["review", "day"]);
    let r = &v["review"];
    let mut breaks: Vec<(u64, u64)> = r["breaks"]["breaks"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .map(|b| (b["planned_min"].as_u64().unwrap_or_default(), b["actual_min"].as_u64().unwrap_or_default()))
        .collect();
    breaks.sort();
    (r["block_min"].as_u64().unwrap_or_else(|| panic!("{v}")), breaks)
}

fn break_starts(tm: &Tm) -> usize {
    tm.log().into_iter().filter(|e| e["ev"] == "break_start").count()
}

/// **D145 on the J day**: a break running since 11:30, then `tm break --now 09:20 5m` — the running break runs on.
#[test]
fn a_finished_break_line_ends_only_its_own_break() {
    let tm = j_day();
    tm.ok_at(&at("11:30"), &["break"]);
    tm.ok_at(&at("09:20"), &["break", "5m"]);
    let now = tm.ok_at(&at("11:40"), &["now"]);
    assert!(!now.stderr.contains("(D133)"), "nothing to re-log: {}", now.stderr);
    assert!(now.stdout.contains("on break since 11:30 · 10m of 20m"), "{}", now.stdout);
    assert_eq!(break_starts(&tm), 1, "the 11:30 break's one break_start");
    assert_eq!(review(&tm, "11:45"), (115, vec![(5, 5)]));
    assert!(tm.ok_at(&at("11:45"), &["check"]).stdout.contains("no problems"));
    let json = tm.json_at(&at("11:40"), &["now"]);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(tm.json_at(&at("11:40"), &["now"]), json);
}

/// **D145 over a running block**: `^t4` running from 10:10, a break running from 10:30, and a finished five-minute
/// break at 10:15 written into the log — the block stays paused under the running break, having worked fifteen minutes.
#[test]
fn a_finished_break_line_leaves_the_running_block_paused_under_the_running_break() {
    let tm = tree();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("10:30"), &["break"]);
    append(&tm, &format!(r#"{{"t":"{}","ev":"break","planned_min":5,"actual_min":5}}"#, at("10:15")));
    let now = tm.ok_at(&at("10:50"), &["now"]);
    assert!(!now.stderr.contains("(D133)"), "nothing to re-log: {}", now.stderr);
    assert!(now.stdout.contains("15m of 60m · paused"), "{}", now.stdout);
    assert!(now.stdout.contains("on break since 10:30 · 20m of 20m"), "{}", now.stdout);
    assert_eq!(break_starts(&tm), 1);
}

/// **D151, the critic's d6**: a break at 09:30 that a 13:00 start ended, ended by the user at 09:40 (D141), then
/// `tm break --now 11:00` — a new break begins (D129 ends it at 13:00); the 09:30 break keeps its ten minutes.
#[test]
fn d129s_end_is_not_inside_the_widest_span() {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("13:00"), &["start", "^t4"]);
    tm.ok_at(&at("14:00"), &["done"]);
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break"]);
    let out = tm.run_at(&at("11:00"), &["break"]);
    assert!(!out.stdout.contains("re-timed out"), "{}", out.stdout);
    let (_, breaks) = review(&tm, "14:30");
    assert!(breaks.contains(&(20, 10)), "{breaks:?}");
}

/// **D151, the critic's d14**: after `09:40 5m` (D146), `tm break --now 09:50` begins a new break; the five-minute
/// break is not swallowed.
#[test]
fn a_d146_break_keeps_its_own_widest_end() {
    let tm = j_day();
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break", "5m"]);
    let out = tm.run_at(&at("09:50"), &["break"]);
    assert!(!out.stdout.contains("re-timed out"), "{}", out.stdout);
    let (_, breaks) = review(&tm, "12:30");
    assert!(breaks.contains(&(5, 5)), "{breaks:?}");
}

/// **The owner's D150 scenario, unchanged**: 09:20 for thirty, re-timed to 09:40 and 09:30, then out to 09:45.
#[test]
fn a_shortened_break_is_lengthened_back_within_its_own_widest_end() {
    let tm = j_day();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:40"), &["break"]);
    tm.ok_at(&at("09:30"), &["break"]);
    let out = tm.ok_at(&at("09:45"), &["break"]);
    assert!(out.stdout.contains("re-timed out"), "{}", out.stdout);
    assert_eq!(review(&tm, "12:30"), (95, vec![(30, 25)]));
}

/// **The overlap filter**: nested `09:20 30m` + `09:30 5m`, then `tm break --now 09:32` — refused by name, nothing
/// written, the day unchanged.
#[test]
fn a_nested_finished_break_is_not_re_timed() {
    let tm = j_day();
    tm.ok_at(&at("09:20"), &["break", "30m"]);
    tm.ok_at(&at("09:30"), &["break", "5m"]);
    let before = tm.log().len();
    let day = review(&tm, "12:30");
    let out = tm.run_at(&at("09:32"), &["break"]);
    assert!(!out.stdout.contains("re-timed"), "{}", out.stdout);
    assert!(out.stderr.contains("overlaps"), "{}", out.stderr);
    assert_eq!(tm.log().len(), before, "nothing written");
    assert_eq!(review(&tm, "12:30"), day);
}

/// **D152's replay half**: `^t4` running from 10:10 and a finished ten-minute break at 10:20 written into the log —
/// the block is not paused, has worked thirty minutes at 10:50, and `tm stop` at 11:00 credits forty.
#[test]
fn a_finished_break_inside_the_running_block_nets_it_and_leaves_it_running() {
    let tm = tree();
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    append(&tm, &format!(r#"{{"t":"{}","ev":"break","planned_min":10,"actual_min":10}}"#, at("10:20")));
    let now = tm.ok_at(&at("10:50"), &["now"]);
    assert!(now.stdout.contains("30m of 60m"), "{}", now.stdout);
    assert!(!now.stdout.contains("paused"), "{}", now.stdout);
    assert!(!now.stdout.contains("on break"), "{}", now.stdout);
    let stop = tm.ok_at(&at("11:00"), &["stop"]);
    assert!(stop.stdout.contains("after 40m"), "{}", stop.stdout);
}
