//! **D137 through the binary** (stage 6 W-51 track K, README gaps 5504 and 5302, parity **P134**): a late break that
//! runs inside a block already closed nets the block from its start while it runs (D129, gap 5180); once the break's
//! own `break` line ends it, the block's credit is the block less what the break's SPAN takes from it — the rest given
//! back, as D100 nets any late break inside a block.
//!
//! Driven at `94542be` (W-50 repair track R's §5a drive, README gap 5504): `tm break --now 13:00 10m` inside a done
//! `^t4`, ended ten minutes later, left the block at 0 minutes in `tm review day`.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

const MON: &str = "2026-09-07";
const TUE: &str = "2026-09-08";

/// The example tree, woken at 07:00 and arrived home at 08:00 on `day`.
fn tree(day: &str) -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at(day, "06:00"), &["init", "--example"]);
    tm.ok_at(&at(day, "07:00"), &["wake", "07:00"]);
    tm.ok_at(&at(day, "08:00"), &["arrive", "home"]);
    tm
}

fn review_block_min(tm: &Tm, now: &str) -> u64 {
    let v = tm.json_at(now, &["review", "day"]);
    v["review"]["block_min"].as_u64().unwrap_or_else(|| panic!("block_min: {v}"))
}

fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

/// **D137 on a plain block (parity P134).** `^t1` 09:00–10:00, done with sixty; then — a clock behind the log — `tm
/// break --now 09:30`, which runs and nets `^t1` from 09:30 on (thirty, D129); ended at 09:40, its `break` line
/// gives back what lies after its span: fifty, the block less the break. Until D137 the block stayed at thirty.
///
/// **Typed with NO length since the owner's D149** (stage 6 W-54 track H, parity P147; a behaviour row, never a
/// re-bless): `tm break --now 09:30 10m` inside a block a later `done` closed is now logged finished in one plain line,
/// so the break that RUNS — this row's subject — is the no-length keystroke (planned the example's twenty); the
/// readings asserted are unchanged.
#[test]
fn a_late_breaks_line_gives_back_what_lies_after_it_p134() {
    let tm = tree(TUE);
    tm.ok_at(&at(TUE, "09:00"), &["start", "^t1"]);
    tm.ok_at(&at(TUE, "10:00"), &["done"]);
    assert_eq!(review_block_min(&tm, &at(TUE, "10:05")), 60, "the block, before any break");
    tm.ok_at(&at(TUE, "09:30"), &["break"]);
    assert_eq!(review_block_min(&tm, &at(TUE, "10:05")), 30, "while the break runs it nets the block from 09:30 (D129)");
    tm.ok_at(&at(TUE, "09:40"), &["break"]);
    let b = breaks(&tm);
    assert_eq!(b.len(), 2, "{b:?}");
    assert_eq!(b[0]["ev"], "break_start");
    assert_eq!(b[1]["ev"], "break");
    assert_eq!(b[1]["actual_min"], 10, "{b:?}");
    assert_eq!(review_block_min(&tm, &at(TUE, "10:05")), 50, "the rest given back once the break ended (D137)");
}

/// **The brief's repro (README gap 5504's §5a drive).** `^t4` started at 12:55 inside the 12:50–13:50 meeting, so a
/// wall holds it paused until 13:50 (D110), done at 14:30; then `tm break --now 13:00 10m`, ended at 13:10. While the
/// break runs it nets the block from 13:00 — all of it; once ended, the break's span `[13:00, 13:10)` lies inside the
/// meeting, where the block drew nothing, so nothing of the block is netted and it reads its whole forty minutes
/// (13:50–14:30). Until D137 it read 0. Typed with NO length since D149 (P147), as the row above.
#[test]
fn a_late_break_inside_a_meeting_gives_the_whole_block_back_p134() {
    let tm = tree(MON);
    tm.ok_at(&at(MON, "12:55"), &["start", "^t4"]);
    tm.ok_at(&at(MON, "14:30"), &["done"]);
    let before = review_block_min(&tm, &at(MON, "14:35"));
    assert_eq!(before, 40, "13:50-14:30: the meeting held the block paused (D110)");
    tm.ok_at(&at(MON, "13:00"), &["break"]);
    assert_eq!(review_block_min(&tm, &at(MON, "14:35")), 0, "while the break runs it nets the block from 13:00 (D129)");
    tm.ok_at(&at(MON, "13:10"), &["break"]);
    assert_eq!(review_block_min(&tm, &at(MON, "14:35")), before, "the break's span meets none of the block (D137)");
    let b = breaks(&tm);
    assert_eq!(b.last().map(|e| e["actual_min"].clone()), Some(Value::from(10)), "{b:?}");
}

/// `(kind, start, end, item)` of every segment `tm --json plan` draws at `now`.
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
        .collect()
}

/// **The W-51 auditor's K shape (README gap 5630, the W-51 repair): a give-back never undoes a later netting.** `^t1`
/// 09:00–10:00, done with sixty; then, on a log a sync or a clock behind it wrote, a `break_start` stamped 09:30 (the
/// break runs and nets `^t1` from 09:30, D129), a late `start ^t4` stamped 09:10 that cuts `^t1` there (D115), `^t4`
/// done at 09:15 with five, and the break's line saying it lasted ten minutes. The break's line ends a break that lies
/// after the cut, so `^t1` stays at ten — the day fifteen — and the plan draws `^t1` 09:00–09:10 and `^t4` 09:10–09:15,
/// never one across the other. The W-51 land gave `^t1` back thirty at the break's line (the day thirty-five) and drew
/// `^t1` from 09:00 to 09:30 across `^t4`. The lines are written by hand because the binary logs none of them in this
/// order on one machine: its `tm start` ends a running break first (D97).
#[test]
fn a_late_start_logged_while_the_break_runs_stays_cut_when_the_break_ends() {
    let tm = tree(TUE);
    tm.ok_at(&at(TUE, "09:00"), &["start", "^t1"]);
    tm.ok_at(&at(TUE, "10:00"), &["done"]);
    let now = at(TUE, "10:30");
    assert_eq!(review_block_min(&tm, &now), 60, "the block, before any late mark");
    let log = tm.plan.join(".tm/log.jsonl");
    let mut text = std::fs::read_to_string(&log).expect("the log");
    let append = |text: &mut String, line: &str| {
        text.push_str(line);
        text.push('\n');
    };
    append(&mut text, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break_start","planned_min":10}"#);
    std::fs::write(&log, &text).expect("write the log");
    assert_eq!(review_block_min(&tm, &now), 30, "the running break nets ^t1 from 09:30 (D129)");
    append(&mut text, r#"{"t":"2026-09-08T09:10:00-05:00","ev":"start","id":"t4","pred":3,"hsw":2.17,"slept_min":0,"loc":"home","blocks_done":1,"since_break_min":0}"#);
    append(&mut text, r#"{"t":"2026-09-08T09:15:00-05:00","ev":"done","id":"t4","est_min":60,"actual_min":5,"tags":[],"ci":3}"#);
    std::fs::write(&log, &text).expect("write the log");
    assert_eq!(review_block_min(&tm, &now), 15, "the late start cuts ^t1 at 09:10 (D115): ten, and ^t4's five");
    append(&mut text, r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break","planned_min":10,"actual_min":10}"#);
    std::fs::write(&log, &text).expect("write the log");
    assert_eq!(review_block_min(&tm, &now), 15, "the break's line gives back nothing the late start cut (gap 5630)");
    let blocks: Vec<_> = segments(&tm, &now)
        .into_iter()
        .filter(|s| s.3.as_deref() == Some("t1") || s.3.as_deref() == Some("t4"))
        .collect();
    let mut spans: Vec<(String, String)> = blocks.iter().map(|s| (s.1.clone(), s.2.clone())).collect();
    spans.sort();
    for w in spans.windows(2) {
        assert!(w[0].1 <= w[1].0, "no two drawn blocks overlap: {blocks:?}");
    }
    assert!(blocks.iter().any(|s| s.3.as_deref() == Some("t1") && s.1 == "09:00" && s.2 == "09:10"), "{blocks:?}");
    assert!(blocks.iter().any(|s| s.3.as_deref() == Some("t4") && s.1 == "09:10" && s.2 == "09:15"), "{blocks:?}");
}
