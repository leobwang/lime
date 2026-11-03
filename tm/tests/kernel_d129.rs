//! **The owner's D129 — a `start` ends a running break, read in STAMP order** (README "Stage 6 — W-50
//! track K", gaps 5430-5433; parity **P127**).
//!
//! A `start` logged while a break runs ends that break at the start's instant, as `tm start` ends
//! one on one machine (D97: it logs the `break` line first). The reading is in stamp order: a
//! running break ends at the first `start` stamped at or after it, whatever order the lines were
//! written in — so a `break_start` written after a logged block and stamped before its start ends
//! at that start too, on an earlier ledger day or the same one. Until D129 such a break ran on: the
//! replay netted the whole block from it (README "Stage 6 — W-49 repair" §2's route 2: `tm review
//! day` load 0.0 for a block `tm done` reported 60m/60m) or, filed on the ledger day before, the
//! plan drew it from the day's start across the block (route 1, gap 5341's picture), and `tm now`
//! said nothing ran.
//!
//! Each test drives the built binary on a fresh `tm init --example` tree (America/Chicago), as the
//! W-49 repair drove the two routes, and asserts what every surface reads after: the plan draws no
//! break across the block, `tm review day` counts the block's sixty minutes, and no break runs.

mod cli_common;

use std::fs;

use serde_json::Value;

use cli_common::Tm;

/// The plan's segments as `(start, end, kind)`.
fn segments(plan: &Value) -> Vec<(String, String, String)> {
    plan["segments"]
        .as_array()
        .unwrap_or_else(|| panic!("no segments: {plan}"))
        .iter()
        .map(|s| {
            (
                s["start"].as_str().unwrap_or_default().to_string(),
                s["end"].as_str().unwrap_or_default().to_string(),
                s["kind"].as_str().unwrap_or_default().to_string(),
            )
        })
        .collect()
}

/// No break segment of `plan` lies across 07:05-08:05, the block's span.
fn no_break_across_the_block(plan: &Value) {
    for (s, e, k) in segments(plan) {
        if k == "break" {
            assert!(
                e.as_str() <= "07:05" || s.as_str() >= "08:05",
                "a break {s}-{e} is drawn across the block 07:05-08:05: {:?}",
                segments(plan)
            );
        }
    }
}

/// A fresh example tree with the block 07:05-08:05 on `day`, woken on `day` (and `prev` first when
/// given), arrived at 07:00.
fn block_day(tm: &Tm, prev: Option<&str>, day: &str) {
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    if let Some(p) = prev {
        tm.ok_at(&format!("{p}T06:05:00-05:00"), &["wake"]);
    }
    tm.ok_at(&format!("{day}T06:05:00-05:00"), &["wake"]);
    tm.ok_at(&format!("{day}T07:00:00-05:00"), &["arrive", "lounge"]);
    tm.ok_at(&format!("{day}T07:05:00-05:00"), &["start", "^t1"]);
    tm.ok_at(&format!("{day}T08:05:00-05:00"), &["done"]);
}

/// **Route 2 (one machine, the same ledger day)**: `tm --now 06:30 break` written after the block —
/// the break is 06:30-07:05, the block keeps its sixty minutes, and the verb says the break ended.
#[test]
fn a_late_break_written_after_a_block_ends_at_its_start() {
    let tm = Tm::empty();
    block_day(&tm, None, "2026-09-08");
    // No length: typed with one (`15m`, as this row read until W-53), D143 logs the break finished (P140).
    let out = tm.ok_at("2026-09-08T06:30:00-05:00", &["break"]);
    assert!(
        out.stderr.contains("ended at 07:05") && out.stderr.contains("D129"),
        "the verb did not say the break ended at the start already logged: {}",
        out.stderr
    );
    assert!(tm.state()["break"].is_null(), "the cache still holds the break: {}", tm.state());
    let plan = tm.json_at("2026-09-08T09:00:00-05:00", &["plan"]);
    no_break_across_the_block(&plan);
    assert!(
        segments(&plan).iter().any(|(s, e, k)| s == "07:05" && e == "08:05" && k == "block"),
        "the block is not drawn: {:?}",
        segments(&plan)
    );
    assert!(
        segments(&plan).iter().any(|(s, e, k)| s == "06:30" && e == "07:05" && k == "break"),
        "the break is not drawn up to the start: {:?}",
        segments(&plan)
    );
    let review = tm.json_at("2026-09-08T09:00:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["block_min"], 60, "{review}");
}

/// **Route 1 (one machine, a ledger day earlier)**: a `break_start` stamped 23:00 the day before,
/// written after the block — filed on that day, ended at 07:05, never drawn across the block.
#[test]
fn a_late_break_from_the_day_before_ends_at_the_next_start() {
    let tm = Tm::empty();
    block_day(&tm, Some("2026-09-08"), "2026-09-09");
    // No length: typed with one (`15m`, as this row read until W-53), D143 logs the break finished (P140).
    tm.ok_at("2026-09-08T23:00:00-05:00", &["break"]);
    let plan = tm.json_at("2026-09-09T09:00:00-05:00", &["plan"]);
    no_break_across_the_block(&plan);
    let review = tm.json_at("2026-09-09T09:00:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["block_min"], 60, "{review}");
    let now = tm.ok_at("2026-09-09T09:00:00-05:00", &["now"]);
    assert!(!now.stdout.contains("break"), "`tm now` reads a running break: {}", now.stdout);
}

/// **Two machines on one synced directory** (D129's own world): machine A's `tm break` at 23:00,
/// never ended; machine B, which had not seen it, works `^t1` 07:05-08:05 the next morning; the sync
/// appends B's lines after A's and A's runtime is rebuilt from the merged log. No break runs and
/// none is drawn across the block.
#[test]
fn a_break_one_machine_left_running_ends_at_the_others_start() {
    let a = Tm::empty();
    assert_eq!(a.run(&["init", "--example"]).code, 0);
    a.ok_at("2026-09-08T06:05:00-05:00", &["wake"]);
    let b = Tm::empty();
    copy(&a.plan, &b.plan);
    a.ok_at("2026-09-08T23:00:00-05:00", &["break", "15m"]);
    let before = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    b.ok_at("2026-09-09T06:05:00-05:00", &["wake"]);
    b.ok_at("2026-09-09T07:00:00-05:00", &["arrive", "lounge"]);
    b.ok_at("2026-09-09T07:05:00-05:00", &["start", "^t1"]);
    b.ok_at("2026-09-09T08:05:00-05:00", &["done"]);
    let after = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    let mine = fs::read_to_string(a.plan.join(".tm/log.jsonl")).expect("A's log");
    fs::write(a.plan.join(".tm/log.jsonl"), format!("{mine}{}", &after[before.len()..])).expect("merge");
    let _ = fs::remove_file(a.plan.join(".tm/state.json"));
    let plan = a.json_at("2026-09-09T09:00:00-05:00", &["plan"]);
    no_break_across_the_block(&plan);
    let review = a.json_at("2026-09-09T09:00:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["block_min"], 60, "{review}");
    assert!(a.state()["break"].is_null(), "the rebuilt runtime holds a running break: {}", a.state());
}

/// **A break's own `break` line after a start ended it is not a second break** (D129,
/// `Replay.Machine.brkEnded`): A's break at 23:00, B's block, then A ends its break at 09:00 — its
/// `break` line, stamped 23:00, claims ten hours; the day still draws no break across the block.
#[test]
fn a_breaks_own_line_after_the_merge_draws_no_second_break() {
    let a = Tm::empty();
    assert_eq!(a.run(&["init", "--example"]).code, 0);
    a.ok_at("2026-09-08T06:05:00-05:00", &["wake"]);
    let b = Tm::empty();
    copy(&a.plan, &b.plan);
    a.ok_at("2026-09-08T23:00:00-05:00", &["break", "15m"]);
    let before = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    b.ok_at("2026-09-09T06:05:00-05:00", &["wake"]);
    b.ok_at("2026-09-09T07:00:00-05:00", &["arrive", "lounge"]);
    b.ok_at("2026-09-09T07:05:00-05:00", &["start", "^t1"]);
    b.ok_at("2026-09-09T08:05:00-05:00", &["done"]);
    let after = fs::read_to_string(b.plan.join(".tm/log.jsonl")).expect("B's log");
    let mine = fs::read_to_string(a.plan.join(".tm/log.jsonl")).expect("A's log");
    let own = r#"{"t":"2026-09-08T23:00:00-05:00","ev":"break","planned_min":15,"actual_min":600}"#;
    fs::write(a.plan.join(".tm/log.jsonl"), format!("{mine}{}{own}\n", &after[before.len()..])).expect("merge");
    let _ = fs::remove_file(a.plan.join(".tm/state.json"));
    let plan = a.json_at("2026-09-09T09:00:00-05:00", &["plan"]);
    no_break_across_the_block(&plan);
    let review = a.json_at("2026-09-09T09:00:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["block_min"], 60, "{review}");
}

/// Copy a plan directory (the sync's snapshot).
fn copy(from: &std::path::Path, to: &std::path::Path) {
    fs::create_dir_all(to).expect("create");
    for entry in fs::read_dir(from).expect("read") {
        let entry = entry.expect("entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("type").is_dir() {
            copy(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy");
        }
    }
}

/// **The equal-stamp tie, the other way round** (README gap 5500, the W-50 critic's finding 2): `start
/// ^t1` 10:20, then `tm break` at the same instant — the start is EARLIER in the file, so it ends
/// nothing: the break runs over the block, and `tm break` does not say it ended. Until the W-50 repair
/// the kernel's `≤` ended it at once and the verb said "ended at 10:20 … (D129) — it is not running".
#[test]
fn a_break_tying_a_start_logged_before_it_runs() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake"]);
    tm.ok_at("2026-09-08T10:20:00-05:00", &["start", "^t1"]);
    let out = tm.ok_at("2026-09-08T10:20:00-05:00", &["break", "15m"]);
    assert!(!out.stderr.contains("D129"), "the tie ended the break: {}", out.stderr);
    assert!(!tm.state()["break"].is_null(), "no break runs: {}", tm.state());
    let now = tm.ok_at("2026-09-08T10:25:00-05:00", &["now"]);
    assert!(now.stdout.contains("break"), "`tm now` reads no running break: {}", now.stdout);
}

/// **A drawn piece is not a `start`** (README gap 5501, the W-50 critic's finding 3): `^t4` started 12:55
/// inside the 12:50–13:50 meeting (D110 pauses it until 13:50) and done 14:30, then `tm break` at 13:00
/// — after the block's `start`, so no start ends it: it runs, and the verb says nothing of D129. Until
/// the W-50 repair it was "ended at 13:50, at the `start` the log already holds after it" (the only
/// start is 12:55), drawn `13:00 · break 50m`, and `tm review day` read 50 minutes of break.
///
/// **Typed with NO length since the owner's D149** (stage 6 W-54 track H, parity P147; a behaviour row, never a
/// re-bless): `tm break --now 13:00 10m` inside `^t4`, which the 14:30 `done` closed, is now logged finished in one
/// plain line, so the break that RUNS — this row's subject — is the no-length keystroke; the readings are unchanged.
#[test]
fn a_late_break_inside_a_block_is_not_ended_by_its_first_drawn_piece() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake"]);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    tm.ok_at("2026-09-07T12:55:00-05:00", &["start", "^t4"]);
    tm.ok_at("2026-09-07T14:30:00-05:00", &["done"]);
    let out = tm.ok_at("2026-09-07T13:00:00-05:00", &["break"]);
    assert!(!out.stderr.contains("D129"), "a drawn piece ended the break: {}", out.stderr);
    assert!(!tm.state()["break"].is_null(), "no break runs: {}", tm.state());
    // Its own `break` line, ten minutes on, ends it there: ten minutes of break, not fifty.
    tm.ok_at("2026-09-07T13:10:00-05:00", &["break"]);
    let review = tm.json_at("2026-09-07T15:00:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["breaks"]["actual_min"], 10, "{review}");
}
