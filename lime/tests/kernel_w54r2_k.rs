//! **The finished-break fact lists a break whose drawn piece is its own; a re-time is read where it gives up nothing
//! another break covers; the latest surviving stamp** — stage 6 W-54 second repair track K (README gaps 5970-5989;
//! the owner's D147, D150 and D153; `Replay.ownDrawn`, `Replay.givesUp`, `Replay.retimeBlocked`, the wire's
//! `open.finished` decoded into [`Replay::finished_breaks`], and [`Replay::latest_t`]).
//!
//! These pin what the decoder hands the host and what the kernel reads, at the replay level; the rows through the
//! binary are track H's.
//!
//! [`Replay::finished_breaks`]: lime_core::log::Replay::finished_breaks
//! [`Replay::latest_t`]: lime_core::log::Replay::latest_t

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use chrono::{DateTime, FixedOffset};
use chrono_tz::Tz;

const TZ: Tz = chrono_tz::America::Chicago;

fn at(hm: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(&format!("2026-09-08T{hm}:00-05:00")).expect("an RFC 3339 instant")
}

fn brk(hm: &str, planned: u32, actual: u32) -> String {
    format!(r#"{{"t":"2026-09-08T{hm}:00-05:00","ev":"break","planned_min":{planned},"actual_min":{actual}}}"#)
}

fn log(lines: &[String]) -> String {
    lines.iter().map(|l| format!("{l}\n")).collect()
}

/// The J day: `^t1` 09:00–10:00 and `^t4` 10:10–11:10, both done.
fn j_day() -> Vec<String> {
    vec![
        r#"{"t":"2026-09-08T09:00:00-05:00","ev":"start","id":"t1","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}"#.into(),
        r#"{"t":"2026-09-08T10:00:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":60,"tags":[],"ci":3}"#.into(),
        r#"{"t":"2026-09-08T10:10:00-05:00","ev":"start","id":"t4","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":1,"since_break_min":0}"#.into(),
        r#"{"t":"2026-09-08T11:10:00-05:00","ev":"done","id":"t4","est_min":60,"actual_min":60,"tags":[],"ci":3}"#.into(),
    ]
}

fn with(breaks: &[(&str, u32, u32)]) -> lime_core::log::Replay {
    let mut l = j_day();
    for (hm, p, a) in breaks {
        l.push(brk(hm, *p, *a));
    }
    chokepoint::replay_of_text(&log(&l), TZ)
}

fn minutes(r: &lime_core::log::Replay, id: &str) -> u32 {
    r.items.get(id).map(|i| i.minutes).unwrap_or(0)
}

fn spans(r: &lime_core::log::Replay) -> Vec<(DateTime<FixedOffset>, DateTime<FixedOffset>)> {
    r.finished_breaks.iter().map(|b| (b.started, b.ended)).collect()
}

fn block_min(r: &lime_core::log::Replay) -> u32 {
    let d = chrono::NaiveDate::from_ymd_opt(2026, 9, 8).expect("a date");
    r.days.get(&d).map(|x| x.block_min).unwrap_or(0)
}

/// The critic's E1 and E3 (README gap 5970, D-1): the newer break of a head-clipped pair is listed — its drawn piece is
/// its own — and the older one, whose piece the newer meets, is not; the review reads the union (105).
#[test]
fn the_fact_lists_the_head_clipped_break_whose_tail_is_its_own() {
    let r = with(&[("09:20", 10, 10), ("09:25", 10, 10)]);
    assert_eq!(spans(&r), vec![(at("09:25"), at("09:35"))]);
    assert_eq!(block_min(&r), 105);
    let r = with(&[("10:30", 10, 10), ("10:30", 15, 15)]);
    assert_eq!(spans(&r), vec![(at("10:30"), at("10:45"))]);
}

/// A nested break and its outer one are both omitted: the outer one's piece meets the inner break, which draws nothing.
#[test]
fn the_fact_omits_a_nested_pair() {
    let r = with(&[("09:20", 30, 30), ("09:30", 5, 5)]);
    assert!(r.finished_breaks.is_empty(), "{:?}", r.finished_breaks);
}

/// The head-clipped re-time (README gap 5962's row, the review's 107 `[10, 3]`): the 09:25 break re-timed to 09:33.
#[test]
fn a_head_clipped_break_is_re_timed_in_its_own_piece() {
    let r = with(&[("09:20", 10, 10), ("09:25", 10, 10), ("09:25", 10, 8)]);
    assert_eq!(minutes(&r, "t1"), 47);
    assert_eq!(block_min(&r), 107);
    let d = chrono::NaiveDate::from_ymd_opt(2026, 9, 8).expect("a date");
    let recs: Vec<_> = r.days[&d].breaks.iter().map(|b| (b.t, b.planned_min, b.actual_min)).collect();
    assert_eq!(recs, vec![(at("09:20"), 10, Some(10)), (at("09:30"), 10, Some(3))]);
}

/// The critic's B and C, and a line ending inside another break's stretch (README gaps 5970, 5971 and 6021): restated at W-54
/// third repair track K, which reads them: each lets go of a stretch another held break also covers, the review reads the
/// union, and the other break is frozen (`lime/tests/kernel_w54r3_k.rs`).
#[test]
fn a_retime_giving_up_another_breaks_stretch_is_read() {
    assert_eq!(block_min(&with(&[("09:20", 10, 10), ("09:25", 10, 10), ("09:20", 10, 2)])), 108, "B");
    assert_eq!(block_min(&with(&[("09:20", 30, 30), ("09:30", 5, 5), ("09:20", 30, 5)])), 110, "C");
    assert_eq!(block_min(&with(&[("09:20", 10, 10), ("09:25", 10, 10), ("09:25", 10, 3)])), 110, "inside the 09:20 break");
}

/// The critic's C2 and D-3 (README gap 5970): a re-time giving up nothing another break covers is read over a newer
/// break — 100 and 95.
#[test]
fn a_retime_giving_up_nothing_another_break_covers_is_read_over_a_newer_one() {
    assert_eq!(block_min(&with(&[("09:20", 30, 30), ("09:30", 5, 5), ("09:20", 30, 20)])), 100, "C2");
    let r = with(&[("09:20", 30, 30), ("09:20", 30, 20), ("09:35", 5, 5), ("09:20", 30, 25)]);
    assert_eq!(block_min(&r), 95, "D-3");
    assert_eq!(minutes(&r, "t1"), 35);
}

/// A re-time over an overlapped break inside the running block: the `stop` reads the union's netting.
#[test]
fn a_stop_after_a_retime_over_an_overlapped_break_reads_the_union() {
    let l: Vec<String> = vec![
        r#"{"t":"2026-09-08T10:10:00-05:00","ev":"start","id":"t4","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}"#.into(),
        brk("10:20", 10, 10),
        brk("10:25", 10, 10),
        brk("10:25", 10, 8),
        r#"{"t":"2026-09-08T11:10:00-05:00","ev":"stop","id":"t4","remaining_min":20}"#.into(),
    ];
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(minutes(&r, "t4"), 47);
}

/// D153 (README gap 5972): `o.sh`'s day — `^t4` started 10:10, paused and unpaused at 10:50, then two finished breaks
/// logged after it, stamped 10:15 and 10:40 — in either order the latest surviving stamp is 10:50, where the last line in
/// file order is the second break's.
#[test]
fn latest_t_is_the_latest_stamp_in_either_order() {
    let head: Vec<String> = vec![
        r#"{"t":"2026-09-08T10:10:00-05:00","ev":"start","id":"t4","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}"#.into(),
        r#"{"t":"2026-09-08T10:50:00-05:00","ev":"pause","id":"t4"}"#.into(),
        r#"{"t":"2026-09-08T10:50:00-05:00","ev":"unpause","id":"t4"}"#.into(),
    ];
    for (a, b) in [("10:15", "10:40"), ("10:40", "10:15")] {
        let mut l = head.clone();
        l.push(brk(a, 5, 5));
        l.push(brk(b, 5, 5));
        let r = chokepoint::replay_of_text(&log(&l), TZ);
        assert_eq!(r.latest_t, Some(at("10:50")), "{a} then {b}");
        assert_eq!(r.last_effective_t, Some(at(b)), "the last line in file order");
    }
}

/// Restated at W-54 third repair track K for the owner's D154, which reverses D153 here: a cancelled line and its undo are
/// witnesses, the instant was reached either way (`lime/tests/kernel_w54r3_k.rs` has the rest of D154).
#[test]
fn latest_t_counts_a_cancelled_line_and_its_undo() {
    let l: Vec<String> = vec![
        r#"{"t":"2026-09-08T10:10:00-05:00","ev":"start","id":"t4","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}"#.into(),
        r#"{"t":"2026-09-08T10:50:00-05:00","ev":"pause","id":"t4"}"#.into(),
        r#"{"t":"2026-09-08T11:00:00-05:00","ev":"unpause","id":"t4"}"#.into(),
        r#"{"t":"2026-09-08T11:05:00-05:00","ev":"undo","of":"unpause","id":"t4"}"#.into(),
    ];
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(r.latest_t, Some(at("11:05")));
}
