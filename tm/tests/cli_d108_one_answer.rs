//! **D108's one answer, by calendar date** — stage 6 W-49 track L (README gaps 5300 and 5301; the W-48 recheck's
//! findings (a) and (b); the owner's D108 and D125).
//!
//! Until W-49 the kernel kept two answers to "what is this day's hysteresis input" — the ledger day's first
//! (`yesterday`) and its latest (`late`) — and one slot per ledger day for its last plan. A ledger day holds the lines
//! of two calendar dates (before the wake, the next date's lines are filed under it), so a `plan` a clock behind the
//! log stamped on the EARLIER date took the later date's slots: driven on the W-48 repair's binary, `plan` at Tuesday
//! 00:26 carried Tuesday's input, a `plan` stamped Monday 23:59 logged after it took the slot, and the next `plan` at
//! Tuesday 00:45 found no input for Tuesday and wrote a second one — Tuesday's input moved with no forward cause.

mod cli_common;

use cli_common::Tm;

fn plans(tm: &Tm) -> Vec<(String, bool)> {
    tm.log()
        .into_iter()
        .filter(|e| e["ev"] == "plan")
        .map(|e| (e["t"].as_str().unwrap_or_default().to_string(), e.get("yesterday").is_some()))
        .collect()
}

fn monday() -> Tm {
    let tm = Tm::empty();
    tm.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["wake", "07:00"]);
    tm.ok_at("2026-09-07T08:00:00-05:00", &["arrive"]);
    tm.ok_at("2026-09-07T08:05:00-05:00", &["plan"]);
    tm.ok_at("2026-09-07T22:00:00-05:00", &["plan"]);
    tm
}

/// **A clock behind the log across midnight moves no later date's input** (gap 5300): Tuesday's first `plan` (00:26)
/// carries Tuesday's input; a `plan` stamped Monday 23:59 logged after it does not take Tuesday's slot, so the `plan`
/// at Tuesday 00:45 carries none.
#[test]
fn a_clock_behind_the_log_moves_no_later_dates_input() {
    let tm = monday();
    tm.ok_at("2026-09-08T00:26:00-05:00", &["plan"]);
    tm.ok_at("2026-09-07T23:59:00-05:00", &["plan"]);
    tm.ok_at("2026-09-08T00:45:00-05:00", &["plan"]);
    let p = plans(&tm);
    let tuesday: Vec<&(String, bool)> = p.iter().filter(|(t, _)| t.starts_with("2026-09-08")).collect();
    assert_eq!(tuesday.len(), 2, "{p:?}");
    assert!(tuesday[0].1, "Tuesday's first plan carries the input: {p:?}");
    assert!(!tuesday[1].1, "and the 00:45 plan carries none — the input did not move: {p:?}");
}

/// **The D42 notice asks the calendar day** (gap 5301): before the wake, Tuesday's `plan` line (filed under Monday's
/// ledger day) carries the input; with `.tm/state.json` deleted, the rebuild restores it and says so. Until W-49 the
/// notice was gated on the LEDGER day's `plan` count, which is 0 for Tuesday before its wake, and said nothing.
#[test]
fn the_restored_notice_reads_the_calendar_days_plans() {
    let tm = monday();
    tm.ok_at("2026-09-08T00:26:00-05:00", &["plan"]);
    std::fs::remove_file(tm.plan.join(".tm/state.json")).expect("state");
    let now = tm.ok_at("2026-09-08T00:30:00-05:00", &["now"]);
    assert!(now.stderr.contains("RESTORED from the log: `priorities_yesterday`"), "{}", now.stderr);
}
