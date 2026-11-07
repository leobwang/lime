//! **A block a calendar wall HOLDS is reserved from the wall's release** — README
//! gap 5217, stage 6 W-49 track W, parity **P123** (the owner's D110, D117 and
//! D114, with D77's rule that the day does not change at an instant it could
//! foresee).
//!
//! `plan-basic`'s calendar holds `^g1 Meeting w/ host at:2026-09-07T12:50/13:50`.
//! While the meeting holds the running block paused — D61's pause at its start,
//! D110's at a start inside it, D117's at a resume inside it — or a break begun
//! before its end holds the block past it (D114), §8.2 choice 5b reserves the
//! block's remainder from the release, the instant nothing blocks it any more.
//! Fork 4748911 refuses a paused timer outright: until W-49 the remainder was
//! drawn only where §8.2 step 5 put it at its rank, or nowhere, and the day moved
//! when the wall's `unpause` was logged (`plan` `drift_min 70` on the auditor's
//! drive).
//!
//! These are P123's behaviour rows: every assertion reads the binary's own
//! output — the plan's rows, `tm now`'s header and JSON, and the log's `plan`
//! line — never a kernel value.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// `^id`'s Block rows in `tm --json plan` at `at`, as `(start, end, mark)`.
fn block_rows(tm: &Tm, at: &str, id: &str) -> Vec<(String, String, String)> {
    tm.json_at(at, &["plan"])["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|s| s["kind"] == "block" && s["item"] == id)
        .map(|s| {
            (
                s["start"].as_str().unwrap_or_default().to_string(),
                s["end"].as_str().unwrap_or_default().to_string(),
                s["mark"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

fn active(tm: &Tm, at: &str) -> Value {
    tm.json_at(at, &["now"])["active"].clone()
}

/// A day with `^t4` started at 12:00, fifty minutes before the meeting.
fn running_before_the_meeting() -> Tm {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

/// **D61's case: the meeting began over the running block.**  At 13:20 the plan
/// reserves `^t4` from 13:50, the meeting's end — no `▶` (it is not running) —
/// and `tm now` says the block resumes there; at 13:51, the `unpause` logged,
/// the same remainder runs from the same instant and the plan line records no
/// drift.
#[test]
fn the_held_remainder_is_reserved_from_the_meetings_end_and_nothing_drifts() {
    // Arrived, so the window is the stored one and does not move with `now` (§8.1's formula from a
    // missing arrival starts at `now`, a drift of its own).
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "home"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let held = block_rows(&tm, "2026-09-07T13:20:00-05:00", "t4");
    assert!(
        held.contains(&("13:50".to_string(), "14:00".to_string(), String::new())),
        "the remainder is reserved from the meeting's end, unmarked: {held:?}"
    );
    let now = active(&tm, "2026-09-07T13:20:00-05:00");
    assert_eq!(now["paused"], true, "{now}");
    assert_eq!(now["resumes"], "13:50", "`tm now` names the resume: {now}");
    let text = tm.ok_at("2026-09-07T13:20:00-05:00", &["now"]).stdout;
    assert!(
        text.lines().next().unwrap_or_default().ends_with("· paused · resumes 13:50"),
        "the header says when the block resumes:\n{text}"
    );

    tm.ok_at("2026-09-07T13:20:00-05:00", &["plan"]);
    tm.ok_at("2026-09-07T13:51:00-05:00", &["plan"]);
    assert_eq!(tm.last_ev("plan")["drift_min"], 0, "the wall's end moved nothing: {}", tm.last_ev("plan"));
    let after = block_rows(&tm, "2026-09-07T13:51:00-05:00", "t4");
    assert!(
        after.iter().any(|r| r.0 == "13:51" && r.1 == "14:00" && r.2 == "▶"),
        "once the wall has let go the remainder runs to the same boundary: {after:?}"
    );
    assert!(active(&tm, "2026-09-07T13:51:00-05:00").get("resumes").is_none(), "nothing holds it any more");
}

/// **D110's case: the block began inside the meeting** — paused from its start,
/// reserved from the meeting's end.
#[test]
fn a_block_started_inside_the_meeting_is_reserved_from_its_end() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    let rows = block_rows(&tm, "2026-09-07T13:30:00-05:00", "t4");
    assert!(rows.iter().any(|r| r.0 == "13:50" && r.2.is_empty()), "{rows:?}");
    assert_eq!(active(&tm, "2026-09-07T13:30:00-05:00")["resumes"], "13:50");
}

/// **D117's case: the block was resumed inside the meeting** — paused from its
/// resume, reserved from the meeting's end.
#[test]
fn a_block_resumed_inside_the_meeting_is_reserved_from_its_end() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:40:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T13:00:00-05:00", &["resume"]);
    let rows = block_rows(&tm, "2026-09-07T13:20:00-05:00", "t4");
    assert!(rows.iter().any(|r| r.0 == "13:50" && r.2.is_empty()), "{rows:?}");
    assert_eq!(active(&tm, "2026-09-07T13:20:00-05:00")["resumes"], "13:50");
}

/// **D114's case: a break begun before the meeting's end holds the block past
/// it** — reserved from the break's planned end; once the break has overrun its
/// end is the user's to say, as a running break's is (P45), and nothing is
/// reserved.
#[test]
fn a_break_that_holds_the_block_past_the_meeting_releases_it_at_its_end() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T13:40:00-05:00", &["break", "30m"]);
    let rows = block_rows(&tm, "2026-09-07T13:55:00-05:00", "t4");
    assert!(rows.iter().any(|r| r.0 == "14:10" && r.2.is_empty()), "reserved from the break's end: {rows:?}");
    assert_eq!(active(&tm, "2026-09-07T13:55:00-05:00")["resumes"], "14:10");

    let overrun: Vec<Value> = tm.json_at("2026-09-07T14:20:00-05:00", &["plan"])["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|s| s["kind"] == "block" && s["item"] == "t4" && s["energy"].is_null() && s["start"].as_str() >= Some("14:20"))
        .cloned()
        .collect();
    assert!(overrun.is_empty(), "an overrun break releases nothing: {overrun:?}");
    assert!(active(&tm, "2026-09-07T14:20:00-05:00").get("resumes").is_none());
}

/// **A pause the user typed is not a hold** — it ends when the user says, so
/// nothing is reserved after the meeting, as before P123.
#[test]
fn a_pause_the_user_typed_before_the_meeting_is_not_held_by_it() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:30:00-05:00", &["pause"]);
    let reserved: Vec<Value> = tm.json_at("2026-09-07T13:20:00-05:00", &["plan"])["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|s| s["kind"] == "block" && s["item"] == "t4" && s["energy"].is_null() && s["start"].as_str() > Some("13:20"))
        .cloned()
        .collect();
    assert!(reserved.is_empty(), "nothing is reserved for a typed pause: {reserved:?}");
    let now = active(&tm, "2026-09-07T13:20:00-05:00");
    assert_eq!(now["paused"], true);
    assert!(now.get("resumes").is_none(), "{now}");
}
