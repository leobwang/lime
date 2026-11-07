//! **The breaks with their own `break` line, read off the kernel** — stage 6 W-53 repair track K (D147's fact,
//! `Replay.finished`, the wire's `open.finished`, decoded into [`Replay::finished_breaks`]).
//!
//! Every break the kernel's machine holds that has its own `break` line — a plain line, the line that ends a
//! `break_start`, or the own line of a break a `start` ended (D129, P127) — with its own start, its OWN end (never
//! clipped by D142's union), its planned minutes, its place, its ledger day and the log line that holds it.  A
//! D129 ending still waiting for its line is not among them (it is `open.ended`'s, `Replay::ended_breaks`).  The
//! host's D147 gate reads this list and nothing else; these tests pin what the decoder hands it.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use chrono::{DateTime, FixedOffset};
use chrono_tz::Tz;

const TZ: Tz = chrono_tz::America::Chicago;

fn at(s: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(s).expect("an RFC 3339 instant")
}

fn log(lines: &[&str]) -> String {
    lines.iter().map(|l| format!("{l}\n")).collect()
}

const T1_START: &str = r#"{"t":"2026-09-08T09:00:00-05:00","ev":"start","id":"t1","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}"#;
const T1_DONE: &str = r#"{"t":"2026-09-08T10:00:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":60,"tags":[],"ci":3}"#;
const T4_START: &str = r#"{"t":"2026-09-08T10:10:00-05:00","ev":"start","id":"t4","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":1,"since_break_min":0}"#;
const T4_DONE: &str = r#"{"t":"2026-09-08T11:10:00-05:00","ev":"done","id":"t4","est_min":60,"actual_min":60,"tags":[],"ci":3}"#;

/// A plain `break` line inside a done block is a finished break: its own span, planned minutes, place and line.
#[test]
fn a_plain_break_line_is_finished_with_its_own_span() {
    let text = log(&[
        T1_START,
        T1_DONE,
        r#"{"t":"2026-09-08T09:30:00-05:00","ev":"break","planned_min":10,"actual_min":10,"where":"walk"}"#,
    ]);
    let r = chokepoint::replay_of_text(&text, TZ);
    assert_eq!(r.finished_breaks.len(), 1, "{:?}", r.finished_breaks);
    let b = &r.finished_breaks[0];
    assert_eq!(b.started, at("2026-09-08T09:30:00-05:00"));
    assert_eq!(b.ended, at("2026-09-08T09:40:00-05:00"));
    assert_eq!(b.planned_min, 10);
    assert_eq!(b.r#where.as_deref(), Some("walk"));
    assert_eq!(b.key, 3, "the log line that holds it");
    assert!(r.ended_breaks.is_empty());
}

/// A break D129 ended is `open.ended`'s until its own line comes; then (P127, the line ending at D129's end) it is
/// finished, with the end D129 gave it.
#[test]
fn a_d129_ending_is_finished_only_once_its_own_line_comes() {
    let before = log(&[
        T1_START,
        T1_DONE,
        T4_START,
        T4_DONE,
        r#"{"t":"2026-09-08T09:50:00-05:00","ev":"break_start","planned_min":30}"#,
    ]);
    let r = chokepoint::replay_of_text(&before, TZ);
    assert!(r.finished_breaks.is_empty(), "{:?}", r.finished_breaks);
    assert_eq!(r.ended_breaks.len(), 1);
    let after = format!(
        "{before}{}\n",
        r#"{"t":"2026-09-08T09:50:00-05:00","ev":"break","planned_min":30,"actual_min":20}"#
    );
    let r = chokepoint::replay_of_text(&after, TZ);
    assert!(r.ended_breaks.is_empty(), "{:?}", r.ended_breaks);
    assert_eq!(r.finished_breaks.len(), 1, "{:?}", r.finished_breaks);
    let b = &r.finished_breaks[0];
    assert_eq!(b.started, at("2026-09-08T09:50:00-05:00"));
    assert_eq!(b.ended, at("2026-09-08T10:10:00-05:00"), "the end D129 gave it");
    assert_eq!(b.planned_min, 30);
}

/// A break D142 draws only in part keeps its OWN end in the fact: 07:50 for forty under 07:40 for twenty is drawn
/// from 08:00, and finished 07:50–08:30.  *Restated at W-54 track K* (README gap 5874): the fact names only the
/// breaks a line re-times, and 07:40–08:00 lies under 07:50, logged after it, so it is gone from the list; the
/// 07:50 break keeps its own end.  *Restated at W-54 repair track K* (README gap 5925): the fact omits a break ANY other
/// held break overlaps, so 07:50–08:30, which 07:40–08:00 overlaps, is gone from it too, and the fact is empty.
/// *Restated at W-54 second repair track K* (README gap 5970, `Replay.ownDrawn`): the fact lists a break whose drawn
/// piece is its own, and the 07:50 break's piece 08:00–08:30 is, so it is listed again with its own end, 08:30.
#[test]
fn a_partly_covered_break_keeps_its_own_end() {
    let text = log(&[
        r#"{"t":"2026-09-08T07:40:00-05:00","ev":"break","planned_min":20,"actual_min":20}"#,
        r#"{"t":"2026-09-08T07:50:00-05:00","ev":"break","planned_min":40,"actual_min":40}"#,
    ]);
    let r = chokepoint::replay_of_text(&text, TZ);
    let mut spans: Vec<_> = r.finished_breaks.iter().map(|b| (b.started, b.ended, b.key)).collect();
    spans.sort();
    assert_eq!(spans, vec![(at("2026-09-08T07:50:00-05:00"), at("2026-09-08T08:30:00-05:00"), 2)]);
}
