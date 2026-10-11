//! **A day the kernel plans and its own row reader refuses is refused BY NAME** (the W-48 repair, README gap
//! 5212; AGENTS §5.7).
//!
//! Driven by the W-48 critic on the landed binary (`4aa44da`): a block open since 07:00 with 600 or more logged
//! `pause`/`unpause` pairs plans a day of more than `Planner.maxCands` (1,024) segments, and the binary's second
//! call — the `plan` row section (the owner's D112) — refuses it at `EmitWire.readSegs` with
//! `{"err":{"plan":"tooManySegments"}}`. The host read every section refusal by name but that one, so `tm now`,
//! `tm plan`, `tm review day` and `tm check` all said `kernel refusal (unrecognised shape)`. The refusal itself is
//! the kernel's and stands (the bound is the owner's to move, gap 5212); what this file pins is that it is NAMED.

mod cli_common;

use cli_common::Tm;
use std::fmt::Write as _;

/// The example tree, woken 06:05, `^t3` started 07:00 and paused and resumed `pairs` times, 40 s and 20 s apart.
fn paused_tree(pairs: u32) -> Tm {
    let tm = Tm::empty();
    tm.ok_at("2026-09-07T06:00:00-05:00", &["init", "--example"]);
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05"]);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["start", "^t3", "--energy", "4"]);
    let mut log = std::fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log");
    let base = 7 * 3600 + 30; // 07:00:30, after the start's own minute
    for k in 0..pairs {
        let p = base + k * 60 + 10;
        let u = p + 40;
        let hms = |s: u32| format!("{:02}:{:02}:{:02}", s / 3600, s / 60 % 60, s % 60);
        writeln!(log, r#"{{"t":"2026-09-07T{}-05:00","ev":"pause","id":"t3"}}"#, hms(p)).expect("write");
        writeln!(log, r#"{{"t":"2026-09-07T{}-05:00","ev":"unpause","id":"t3"}}"#, hms(u)).expect("write");
    }
    std::fs::write(tm.plan.join(".tm/log.jsonl"), log).expect("the log, written");
    tm
}

/// **The driven reproduction**: 600 pairs, `tm now` at 22:00 — refused, and the refusal named.
#[test]
fn a_day_past_the_row_sections_cap_is_refused_by_name() {
    let tm = paused_tree(600);
    let out = tm.run_at("2026-09-07T22:00:00-05:00", &["now"]);
    assert_ne!(out.code, 0, "the day is refused:\n{}", out.stdout);
    assert!(out.stderr.contains("tooManySegments"), "{}", out.stderr);
    assert!(out.stderr.contains("the day's rows could not be read"), "{}", out.stderr);
    assert!(!out.stderr.contains("unrecognised shape"), "{}", out.stderr);
}

/// **Its boundary**: 200 pairs plan a day the row section reads, and `tm now` answers.
#[test]
fn a_day_under_the_cap_is_answered() {
    let tm = paused_tree(200);
    let out = tm.run_at("2026-09-07T22:00:00-05:00", &["now"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert!(out.stdout.contains("t3") || out.stdout.contains("Lit review"), "{}", out.stdout);
}
