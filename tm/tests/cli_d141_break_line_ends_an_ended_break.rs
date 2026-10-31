//! **D141's replay half through the binary** (stage 6 W-52b track K2, README gaps 5633 and 5660, parity **P137**): a `break` line
//! stamped at the start of a break D129 already ended at a later block's `start`, whose end (`t + actual_min`) falls
//! before that start, is read as the break's end — the break held, drawn and recorded as `[break_start, t + actual_min)`,
//! and what the D129 reading took after it given back (D137), so the block it ran inside reads its minutes less the
//! break's own span.
//!
//! The log is the W-51 auditor's J log (`drive/J.sh`) with its second `break_start` replaced by the `break` line track H's
//! `tm break` writes since D141's host half (W-52 track H) — `t` 09:30, `actual_min` 10 — logged after `^t4`'s `done`
//! and after the 09:30 `break_start`.  It is written by hand here, so the test reads the replay's half alone: the
//! binary this test runs may predate track H's verb half.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

const TUE: &str = "2026-09-08";

/// The example tree, woken at 07:00 and arrived home at 08:00, `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done.
fn tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at(TUE, "06:00"), &["init", "--example"]);
    tm.ok_at(&at(TUE, "07:00"), &["wake", "07:00"]);
    tm.ok_at(&at(TUE, "08:00"), &["arrive", "home"]);
    tm.ok_at(&at(TUE, "09:00"), &["start", "^t1"]);
    tm.ok_at(&at(TUE, "10:00"), &["done"]);
    tm.ok_at(&at(TUE, "10:10"), &["start", "^t4"]);
    tm.ok_at(&at(TUE, "11:10"), &["done"]);
    tm
}

fn append(tm: &Tm, line: &str) {
    let log = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&log).expect("the log");
    text.push_str(line);
    text.push('\n');
    std::fs::write(&log, &text).expect("write the log");
}

fn review(tm: &Tm, now: &str) -> Value {
    tm.json_at(now, &["review", "day"])["review"].clone()
}

/// `(kind, start, end, item)` of every segment `tm --json plan` draws at `now` that begins before noon — the drawn
/// morning, 09:00–11:59; the planner's own future rows (a planned break at 14:30) come after it.
fn segments(tm: &Tm, now: &str) -> Vec<(String, String, String, Option<String>)> {
    let plan = tm.json_at(now, &["plan"]);
    plan["segments"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|s| {
            let st = |k: &str| s[k].as_str().unwrap_or_default().to_string();
            (st("kind"), st("start"), st("end"), s["item"].as_str().map(str::to_string))
        })
        .filter(|s| s.1.as_str() < "12:00")
        .collect()
}

fn break_actuals(r: &Value) -> Vec<u64> {
    r["breaks"]["breaks"].as_array().cloned().unwrap_or_default().iter().filter_map(|b| b["actual_min"].as_u64()).collect()
}

/// **P137, the brief's repro.**  The 09:30 `break_start` is ended by D129 at `^t4`'s 10:10 start and nets `^t1` to
/// thirty; the break's own line then says it lasted ten minutes: `^t1` reads fifty, `^t4` sixty, the break is drawn
/// 09:30–09:40 and recorded ten minutes.  Before D141 the line was the break's own and nothing else (P127): `^t1` thirty
/// and a forty-minute break.
#[test]
fn a_break_line_ending_a_break_d129_ended_ends_it_there_p137() {
    let tm = tree();
    let now = at(TUE, "11:15");
    assert_eq!(review(&tm, &now)["block_min"], 120, "both blocks, before any break");
    append(&tm, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break_start","planned_min":10}"#);
    let r = review(&tm, &now);
    assert_eq!(r["block_min"], 90, "D129 ends the break at ^t4's start and nets ^t1 to thirty: {r}");
    assert_eq!(break_actuals(&r), vec![40], "{r}");
    append(&tm, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break","planned_min":10,"actual_min":10}"#);
    let r = review(&tm, &now);
    assert_eq!(r["block_min"], 110, "^t1 fifty and ^t4 sixty: the break's own span alone is netted (D141): {r}");
    assert_eq!(break_actuals(&r), vec![10], "the break recorded as its line says: {r}");
    let segs = segments(&tm, &now);
    let brk: Vec<_> = segs.iter().filter(|s| s.0 == "break").collect();
    assert_eq!(brk.len(), 1, "one break drawn: {segs:?}");
    assert_eq!((brk[0].1.as_str(), brk[0].2.as_str()), ("09:30", "09:40"), "{segs:?}");
    let t1: Vec<_> = segs.iter().filter(|s| s.3.as_deref() == Some("t1")).map(|s| (s.1.clone(), s.2.clone())).collect();
    assert_eq!(t1, vec![("09:00".into(), "09:30".into()), ("09:40".into(), "10:00".into())], "{segs:?}");
    let t4: Vec<_> = segs.iter().filter(|s| s.3.as_deref() == Some("t4")).map(|s| (s.1.clone(), s.2.clone())).collect();
    assert_eq!(t4, vec![("10:10".into(), "11:10".into())], "^t4 untouched: {segs:?}");
    let chk = tm.run_at(&now, &["check"]);
    assert_eq!(chk.code, 0, "tm check is silent about the line: {} {}", chk.stdout, chk.stderr);
    assert!(!chk.stdout.contains("break") && !chk.stderr.contains("break"), "{} {}", chk.stdout, chk.stderr);
}

/// **P127's reading kept where D141 does not reach.**  The break's own line saying it lasted until or past the start
/// that ended it is that break's own line and no second break: `^t1` stays at thirty and the break at forty minutes,
/// drawn 09:30–10:10.
#[test]
fn a_break_line_ending_at_or_after_the_start_that_ended_it_is_the_breaks_own_p127() {
    let tm = tree();
    let now = at(TUE, "11:15");
    append(&tm, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break_start","planned_min":10}"#);
    append(&tm, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break","planned_min":10,"actual_min":45}"#);
    let r = review(&tm, &now);
    assert_eq!(r["block_min"], 90, "{r}");
    assert_eq!(break_actuals(&r), vec![40], "{r}");
    let segs = segments(&tm, &now);
    let brk: Vec<_> = segs.iter().filter(|s| s.0 == "break").map(|s| (s.1.clone(), s.2.clone())).collect();
    assert_eq!(brk, vec![("09:30".into(), "10:10".into())], "{segs:?}");
}
