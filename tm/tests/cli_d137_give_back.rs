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
/// break --now 09:30 10m`, which runs and nets `^t1` from 09:30 on (thirty, D129); ended at 09:40, its `break` line
/// gives back what lies after its span: fifty, the block less the break. Until D137 the block stayed at thirty.
#[test]
fn a_late_breaks_line_gives_back_what_lies_after_it_p134() {
    let tm = tree(TUE);
    tm.ok_at(&at(TUE, "09:00"), &["start", "^t1"]);
    tm.ok_at(&at(TUE, "10:00"), &["done"]);
    assert_eq!(review_block_min(&tm, &at(TUE, "10:05")), 60, "the block, before any break");
    tm.ok_at(&at(TUE, "09:30"), &["break", "10m"]);
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
/// (13:50–14:30). Until D137 it read 0.
#[test]
fn a_late_break_inside_a_meeting_gives_the_whole_block_back_p134() {
    let tm = tree(MON);
    tm.ok_at(&at(MON, "12:55"), &["start", "^t4"]);
    tm.ok_at(&at(MON, "14:30"), &["done"]);
    let before = review_block_min(&tm, &at(MON, "14:35"));
    assert_eq!(before, 40, "13:50-14:30: the meeting held the block paused (D110)");
    tm.ok_at(&at(MON, "13:00"), &["break", "10m"]);
    assert_eq!(review_block_min(&tm, &at(MON, "14:35")), 0, "while the break runs it nets the block from 13:00 (D129)");
    tm.ok_at(&at(MON, "13:10"), &["break"]);
    assert_eq!(review_block_min(&tm, &at(MON, "14:35")), before, "the break's span meets none of the block (D137)");
    let b = breaks(&tm);
    assert_eq!(b.last().map(|e| e["actual_min"].clone()), Some(Value::from(10)), "{b:?}");
}
