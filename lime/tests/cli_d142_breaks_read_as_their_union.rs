//! **D142 through the binary** (stage 6 W-52 track K, README gap 5634, parity **P136**): overlapping logged breaks are
//! read as their union — each break is drawn and recorded only where no earlier break (earlier in stamp order) covers
//! it, so `lime plan`, `lime review day`'s break minutes, `over` and `by_where`, and the heat grid count each minute of wall
//! time once.  A break an earlier one covers whole draws nothing and is recorded at zero minutes.
//!
//! The log is the W-51 auditor's J log (`drive/J.sh`) as the W-51 repair binary writes it: two `break_start`s, 09:30
//! and 09:40, both ended by D129 at `^t4`'s 10:10 start.  Written by hand so the test does not depend on the host's
//! `lime break` (track H's D141 half changes what it writes there).

mod cli_common;

use cli_common::Lime;
use serde_json::Value;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

const TUE: &str = "2026-09-08";

fn tree() -> Lime {
    let lime = Lime::empty();
    lime.ok_at(&at(TUE, "06:00"), &["init", "--example"]);
    lime.ok_at(&at(TUE, "07:00"), &["wake", "07:00"]);
    lime.ok_at(&at(TUE, "08:00"), &["arrive", "home"]);
    lime.ok_at(&at(TUE, "09:00"), &["start", "^t1"]);
    lime.ok_at(&at(TUE, "10:00"), &["done"]);
    lime.ok_at(&at(TUE, "10:10"), &["start", "^t4"]);
    lime.ok_at(&at(TUE, "11:10"), &["done"]);
    lime
}

fn append(lime: &Lime, line: &str) {
    let log = lime.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&log).expect("the log");
    text.push_str(line);
    text.push('\n');
    std::fs::write(&log, &text).expect("write the log");
}

fn review(lime: &Lime, now: &str) -> Value {
    lime.json_at(now, &["review", "day"])["review"].clone()
}

fn break_rows(lime: &Lime, now: &str) -> Vec<(String, String)> {
    let plan = lime.json_at(now, &["plan"]);
    plan["segments"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .filter(|s| s["kind"] == "break")
        .map(|s| (s["start"].as_str().unwrap_or_default().to_string(), s["end"].as_str().unwrap_or_default().to_string()))
        .collect()
}

/// **P136, the brief's repro.**  The J log: one break drawn 09:30–10:10, forty break minutes — the second break,
/// wholly covered, is recorded at zero minutes (so the host still finds it, D133) — and the block minutes unchanged
/// (the replay already netted the union).  On the W-51 repair binary: `09:30 break 40m` and `09:40 break 30m`, breaks
/// `actual 40 30`.
#[test]
fn two_breaks_d129_ended_at_one_start_are_drawn_and_counted_once_p136() {
    let lime = tree();
    let now = at(TUE, "11:15");
    append(&lime, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break_start","planned_min":10}"#);
    let one = review(&lime, &now);
    append(&lime, r#"{"t":"2026-09-08T09:40:00-05:00","ev":"break_start","planned_min":20}"#);
    let r = review(&lime, &now);
    assert_eq!(r["block_min"], one["block_min"], "the block minutes do not move: {r}");
    assert_eq!(r["block_min"], 90, "{r}");
    let actual: Vec<u64> =
        r["breaks"]["breaks"].as_array().cloned().unwrap_or_default().iter().filter_map(|b| b["actual_min"].as_u64()).collect();
    assert_eq!(actual, vec![40, 0], "the covered break adds no minute: {r}");
    assert_eq!(r["breaks"]["actual_min"], 40, "forty break minutes over forty of wall time: {r}");
    let bw = &r["breaks"]["by_where"];
    assert_eq!(bw["-"], serde_json::json!([2, 40]), "{r}");
    // the logged breaks: the plan also draws the day's planned breaks after `now`
    let logged: Vec<_> = break_rows(&lime, &now).into_iter().filter(|r| r.0.as_str() < "11:15").collect();
    assert_eq!(logged, vec![("09:30".to_string(), "10:10".to_string())]);
}

/// **A break an earlier one covers in part is drawn and recorded from where the earlier one ends.**  A `break` line
/// 13:00 for twenty minutes, then a late `break` line stamped 13:10 for twenty: the second is drawn 13:20–13:30 and
/// recorded ten minutes, so the day's break minutes are thirty, the wall time the two cover.
#[test]
fn a_break_an_earlier_one_covers_in_part_is_counted_from_its_end_p136() {
    let lime = tree();
    let now = at(TUE, "14:00");
    append(&lime, r#"{"t":"2026-09-08T13:00:00-05:00","ev":"break","planned_min":20,"actual_min":20,"where":"walk"}"#);
    append(&lime, r#"{"t":"2026-09-08T13:10:00-05:00","ev":"break","planned_min":20,"actual_min":20,"where":"seat"}"#);
    let r = review(&lime, &now);
    let actual: Vec<u64> =
        r["breaks"]["breaks"].as_array().cloned().unwrap_or_default().iter().filter_map(|b| b["actual_min"].as_u64()).collect();
    assert_eq!(actual, vec![20, 10], "{r}");
    assert_eq!(r["breaks"]["actual_min"], 30, "{r}");
    assert_eq!(r["breaks"]["by_where"]["walk"], serde_json::json!([1, 20]), "{r}");
    assert_eq!(r["breaks"]["by_where"]["seat"], serde_json::json!([1, 10]), "{r}");
    let rows = break_rows(&lime, &now);
    assert!(rows.contains(&("13:00".to_string(), "13:20".to_string())), "{rows:?}");
    assert!(rows.contains(&("13:20".to_string(), "13:30".to_string())), "{rows:?}");
}
