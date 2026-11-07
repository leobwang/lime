//! **The finished breaks a line re-times, and the widest end the log held for each** — stage 6 W-54 track K
//! (README gaps 5870-5876; the owner's D147 and D150, `Replay.finished`, the wire's `open.finished`, decoded into
//! [`Replay::finished_breaks`]).
//!
//! Since W-54 the fact holds only the breaks a `break` line stamped at their start with their planned minutes
//! re-times (`Replay.a_finished_break_is_re_timed_by_its_line`): not one a break held after it overlaps (the
//! W-53 repair auditor's finding 2), and nothing while a break runs (its critic's finding 3).  Each entry carries
//! [`EndedBreak::widest`], the latest end any of the break's own lines gave it, which D150's gate reads.  These
//! tests pin what the decoder hands the host, and the block minutes the kernel reads after a re-time (findings 1,
//! 3 and 4).

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

fn minutes(r: &lime_core::log::Replay, id: &str) -> u32 {
    r.items.get(id).map(|i| i.minutes).unwrap_or(0)
}

/// D150: 09:20 for thirty re-timed to 09:40, then 09:30, out to 09:45 and back to 09:35 — one break 09:20–09:35,
/// its widest end 09:50, `^t1` forty-five.
#[test]
fn a_finished_break_carries_the_widest_end_the_log_held_for_it() {
    let mut l = j_day();
    for a in [30, 20, 10, 25, 15] {
        l.push(brk("09:20", 30, a));
    }
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(r.finished_breaks.len(), 1, "{:?}", r.finished_breaks);
    let b = &r.finished_breaks[0];
    assert_eq!((b.started, b.ended, b.widest, b.planned_min), (at("09:20"), at("09:35"), at("09:50"), 30));
    assert_eq!(minutes(&r, "t1"), 45);
}

/// A break that is not re-timed has its own end as its widest.
#[test]
fn a_break_never_re_timed_is_its_own_widest() {
    let mut l = j_day();
    l.push(brk("09:30", 10, 10));
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    let b = &r.finished_breaks[0];
    assert_eq!((b.ended, b.widest), (at("09:40"), at("09:40")));
}

/// The W-53 repair auditor's finding 2: 09:20 for twenty and 09:30 for twenty — the fact names the 09:30 break
/// alone, since a line at 09:20 meets it and is read as a break of its own.  *Restated at W-54 repair track K* (README
/// gap 5925): the fact omits a break any other held break overlaps, so it names neither.  *Restated at W-54 second
/// repair track K* (README gap 5970, `Replay.ownDrawn`): the fact lists a break whose drawn piece is its own, so it names
/// the 09:30 break again (drawn 09:40–09:50), as W-54 had it, and omits the 09:20 one, whose piece the newer break meets.
#[test]
fn the_fact_omits_a_break_a_newer_one_overlaps() {
    let mut l = j_day();
    l.push(brk("09:20", 20, 20));
    l.push(brk("09:30", 20, 20));
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    let spans: Vec<_> = r.finished_breaks.iter().map(|b| (b.started, b.ended)).collect();
    assert_eq!(spans, vec![(at("09:30"), at("09:50"))]);
}

/// The W-53 repair critic's finding 3: with a break running the fact is empty, as `open.ended` is.
#[test]
fn the_fact_is_empty_while_a_break_runs() {
    let mut l = j_day();
    l.push(brk("09:20", 20, 20));
    l.push(r#"{"t":"2026-09-08T12:00:00-05:00","ev":"break_start","planned_min":20}"#.into());
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert!(r.finished_breaks.is_empty(), "{:?}", r.finished_breaks);
    assert!(r.open_break.is_some());
}

/// The W-53 repair auditor's finding 1: a break that netted `^t1` while it was OPEN, re-timed — `^t1` gets back
/// what lies past the new end.
#[test]
fn a_retime_gives_back_what_the_break_took_from_an_open_block() {
    let l: Vec<String> = vec![
        r#"{"t":"2026-09-08T09:00:00-05:00","ev":"start","id":"t1","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}"#.into(),
        r#"{"t":"2026-09-08T09:20:00-05:00","ev":"break_start","planned_min":10}"#.into(),
        brk("09:20", 10, 40),
        r#"{"t":"2026-09-08T10:00:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":20,"tags":[],"ci":5}"#.into(),
        brk("09:20", 10, 10),
    ];
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(minutes(&r, "t1"), 50);
}

/// The auditor's finding 3: a break D129 ended at `^t4`'s start, its own line ending later (P127), then re-timed
/// to 09:50 — `^t1` forty, as a plain line ending at 09:50 would leave it.
#[test]
fn a_retime_of_a_p127_break_gives_back_its_take() {
    let mut l = j_day();
    l.push(r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break_start","planned_min":20}"#.into());
    l.push(brk("09:30", 20, 50));
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(r.finished_breaks[0].widest, at("10:10"), "D129's end, which P127 kept");
    l.push(brk("09:30", 20, 20));
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(minutes(&r, "t1"), 40);
}

/// The auditor's finding 4 (the campaign's call): identical twin finished breaks re-time as one.
#[test]
fn twin_finished_breaks_are_re_timed_as_one() {
    let mut l = j_day();
    l.push(brk("09:20", 10, 10));
    l.push(brk("09:20", 10, 10));
    l.push(brk("09:20", 10, 5));
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(minutes(&r, "t1"), 55);
    assert_eq!(r.finished_breaks.len(), 1, "{:?}", r.finished_breaks);
}

/// An ending carries the end D129 gave it as its widest.
#[test]
fn an_ending_is_its_own_widest() {
    let mut l = j_day();
    l.push(r#"{"t":"2026-09-08T09:50:00-05:00","ev":"break_start","planned_min":30}"#.into());
    let r = chokepoint::replay_of_text(&log(&l), TZ);
    assert_eq!(r.ended_breaks.len(), 1, "{:?}", r.ended_breaks);
    assert_eq!((r.ended_breaks[0].ended, r.ended_breaks[0].widest), (at("10:10"), at("10:10")));
}
