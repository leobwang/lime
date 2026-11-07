//! **`lime resume` names the meeting that still holds the block** (the W-48 repair, README gap 5213; D66's rule,
//! README gap 3048, as `lime pause` already says it).
//!
//! Driven by the W-48 auditor on the landed binary (`4aa44da`): `start ^t4` 12:30, the 12:50–13:50 meeting pauses
//! it (D61), `interrupt` 13:10, `resume` 13:30 printed `resumed · lost 20m · ^t4 still paused — `lime pause` resumes
//! it` — as though the user had paused it — while the pause is the wall's and lifts by itself at 13:50. A block the
//! user paused keeps the old line (`cli_resume_keeps_a_pause.rs`).

mod cli_common;

use cli_common::Lime;

fn at(hm: &str) -> String {
    format!("2026-09-07T{hm}:00-05:00")
}

fn tree() -> Lime {
    let lime = Lime::empty();
    lime.ok_at(&at("06:00"), &["init", "--example"]);
    lime.ok_at(&at("07:00"), &["wake", "07:00"]);
    lime.ok_at(&at("08:00"), &["arrive"]);
    lime.ok_at(&at("12:30"), &["start", "^t4", "--energy", "3"]);
    lime.ok_at(&at("13:10"), &["interrupt"]);
    lime
}

/// **The driven reproduction**, through the terminal line.
#[test]
fn a_resume_inside_the_meeting_says_which_meeting_holds_the_block() {
    let lime = tree();
    let out = lime.ok_at(&at("13:30"), &["resume"]);
    assert!(out.stdout.contains("^t4 still paused for"), "{}", out.stdout);
    assert!(out.stdout.contains("12:50–13:50"), "the meeting's span: {}", out.stdout);
    assert!(out.stdout.contains("it resumes at 13:50"), "it lifts by itself: {}", out.stdout);
}

/// **And through `--json`**: the meeting beside `still_paused`.
#[test]
fn a_resume_inside_the_meeting_carries_it_in_json() {
    let lime = tree();
    let v = lime.json_at(&at("13:30"), &["resume"]);
    assert_eq!(v["still_paused"], "t4", "{v}");
    assert_eq!(v["still_paused_for"]["from"], "12:50", "{v}");
    assert_eq!(v["still_paused_for"]["to"], "13:50", "{v}");
}
