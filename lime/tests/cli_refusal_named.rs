//! **A day the kernel plans is drawn, at every length** (the owner's D123, W-49 track P, README gap 5212) —
//! and until then, **refused BY NAME** (the W-48 repair; AGENTS §5.7).
//!
//! Driven by the W-48 critic on the landed binary (`4aa44da`): a block open since 07:00 with 600 or more logged
//! `pause`/`unpause` pairs plans a day of more than `Planner.maxCands` (1,024) segments, and the binary's second
//! call — the `plan` row section (the owner's D112) — refused it at `EmitWire.readSegs` with
//! `{"err":{"plan":"tooManySegments"}}`, which the host read as `kernel refusal (unrecognised shape)` until the W-48
//! repair named it. The owner's D123 widened the reader to every day the planner can answer (the bound is the
//! planner's, and the planner sets none: D28), and D124 put the rows in the planner's own answer, so the day is planned
//! AND drawn — as fork 4748911 planned and drew it. No parity number: the binary returns to the fork's behaviour.

mod cli_common;

use cli_common::Lime;
use std::fmt::Write as _;

/// The example tree, woken 06:05, `^t3` started 07:00 and paused and resumed `pairs` times, 40 s and 20 s apart.
fn paused_tree(pairs: u32) -> Lime {
    let lime = Lime::empty();
    lime.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
    lime.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05"]);
    lime.ok_at("2026-09-07T07:00:00-05:00", &["start", "^t3", "--energy", "4"]);
    let mut log = std::fs::read_to_string(lime.plan.join(".tm/log.jsonl")).expect("the log");
    let base = 7 * 3600 + 30; // 07:00:30, after the start's own minute
    for k in 0..pairs {
        let p = base + k * 60 + 10;
        let u = p + 40;
        let hms = |s: u32| format!("{:02}:{:02}:{:02}", s / 3600, s / 60 % 60, s % 60);
        writeln!(log, r#"{{"t":"2026-09-07T{}-05:00","ev":"pause","id":"t3"}}"#, hms(p)).expect("write");
        writeln!(log, r#"{{"t":"2026-09-07T{}-05:00","ev":"unpause","id":"t3"}}"#, hms(u)).expect("write");
    }
    std::fs::write(lime.plan.join(".tm/log.jsonl"), log).expect("the log, written");
    lime
}

/// **The driven reproduction, answered** (D123's behaviour row): 600 pairs, asked at 22:00 — every planning verb
/// plans the day and draws it, more than 1,024 rows, where until W-49 each refused it `tooManySegments`.
#[test]
fn a_day_past_the_old_row_cap_is_planned_and_drawn() {
    let lime = paused_tree(600);
    let at = "2026-09-07T22:00:00-05:00";
    let now = lime.run_at(at, &["now"]);
    assert_eq!(now.code, 0, "{}", now.stderr);
    assert!(now.stdout.contains("Exercises 5.3–5.5"), "{}", now.stdout);
    let plan = lime.run_at(at, &["plan"]);
    assert_eq!(plan.code, 0, "{}", plan.stderr);
    // Every pause is a row of its own but the ones inside the example's 12:50–13:50 meeting, which the owner's D65
    // draws as the wall alone (at most the meeting hour's sixty).
    let rows = plan.stdout.lines().filter(|l| l.contains("paused 0m")).count();
    assert!(rows >= 540, "{rows} pause rows:\n{}", &plan.stdout[..plan.stdout.len().min(2000)]);
    assert!(plan.stdout.lines().count() > 1024, "the day is drawn whole, past the old cap");
    for verb in [&["review", "day"][..], &["check"][..]] {
        let out = lime.run_at(at, verb);
        assert_eq!(out.code, 0, "lime {verb:?}: {}", out.stderr);
        assert!(!out.stderr.contains("tooManySegments") && !out.stdout.contains("tooManySegments"), "{}", out.stderr);
    }
}

/// **Its boundary**: 200 pairs plan a day the row section reads, and `lime now` answers.
#[test]
fn a_day_under_the_cap_is_answered() {
    let lime = paused_tree(200);
    let out = lime.run_at("2026-09-07T22:00:00-05:00", &["now"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.stdout.contains("t3") || out.stdout.contains("Lit review"), "{}", out.stdout);
}
