//! **One fact per held break; a take put back whole; a shared stretch let go and the break it leaves short frozen;
//! the log's latest typed-time stamp** — stage 6 W-54 third repair track K (README gaps 6020-6039; the owner's D141, D147,
//! D150, D151 and D154; `Replay.heldFacts`, `Replay.frozen`, `Replay.Closed.restored`, `Seal.latestTyped`, the wire's
//! `open.held` and `latestTyped`, decoded into [`Replay::held_breaks`] and [`Replay::latest_t`]).
//!
//! These pin what the decoder hands the host and what the kernel reads, at the replay level: the keystroke rows through
//! the binary are track H's. The first row is the invariant both tracks are measured against, at this level: on a generated
//! J day of `break` and `break_start` lines, the credit is the blocks less the union of what the fact says is held, and
//! every minute of the blocks is drawn as a block or as a break.
//!
//! [`Replay::held_breaks`]: tm_core::log::Replay::held_breaks
//! [`Replay::latest_t`]: tm_core::log::Replay::latest_t

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

use chrono::{DateTime, FixedOffset, NaiveDate};
use chrono_tz::Tz;
use std::collections::BTreeSet;
use tm_core::log::{Replay, SegmentKind};

const TZ: Tz = chrono_tz::America::Chicago;

fn at(hm: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(&format!("2026-09-08T{hm}:00-05:00")).expect("an RFC 3339 instant")
}

fn hm(m: u32) -> String {
    format!("{:02}:{:02}", m / 60, m % 60)
}

fn brk(t: &str, planned: u32, actual: u32) -> String {
    format!(r#"{{"t":"2026-09-08T{t}:00-05:00","ev":"break","planned_min":{planned},"actual_min":{actual}}}"#)
}

fn brk_start(t: &str, planned: u32) -> String {
    format!(r#"{{"t":"2026-09-08T{t}:00-05:00","ev":"break_start","planned_min":{planned}}}"#)
}

fn log(lines: &[String]) -> String {
    lines.iter().map(|l| format!("{l}\n")).collect()
}

fn start_line(t: &str, id: &str) -> String {
    format!(r#"{{"t":"2026-09-08T{t}:00-05:00","ev":"start","id":"{id}","pred":3,"hsw":2.0,"slept_min":0,"loc":"home","blocks_done":0,"since_break_min":0}}"#)
}

fn done_line(t: &str, id: &str) -> String {
    format!(r#"{{"t":"2026-09-08T{t}:00-05:00","ev":"done","id":"{id}","est_min":60,"actual_min":60,"tags":[],"ci":3}}"#)
}

/// The J day: `^t1` 09:00–10:00 and `^t4` 10:10–11:10, both done.
fn j_day() -> Vec<String> {
    vec![start_line("09:00", "t1"), done_line("10:00", "t1"), start_line("10:10", "t4"), done_line("11:10", "t4")]
}

fn day() -> NaiveDate {
    NaiveDate::from_ymd_opt(2026, 9, 8).expect("a date")
}

fn read(extra: &[String]) -> Replay {
    let mut l = j_day();
    l.extend_from_slice(extra);
    chokepoint::replay_of_text(&log(&l), TZ)
}

fn mins_of(t: DateTime<FixedOffset>) -> u32 {
    let s = t.signed_duration_since(at("00:00")).num_minutes();
    u32::try_from(s).expect("on the day")
}

type Span = (u32, u32);

fn block_rows(r: &Replay) -> Vec<Span> {
    r.days[&day()]
        .segments
        .iter()
        .filter(|s| matches!(s.kind, SegmentKind::Block { .. }))
        .map(|s| (mins_of(s.start), mins_of(s.end)))
        .collect()
}

fn break_rows(r: &Replay) -> Vec<Span> {
    r.days[&day()]
        .segments
        .iter()
        .filter(|s| matches!(s.kind, SegmentKind::Break { .. }))
        .map(|s| (mins_of(s.start), mins_of(s.end)))
        .collect()
}

fn minutes(spans: &[Span]) -> BTreeSet<u32> {
    spans.iter().flat_map(|(s, e)| *s..*e).collect()
}

const T1: Span = (9 * 60, 10 * 60);
const T4: Span = (10 * 60 + 10, 11 * 60 + 10);

/// **What the invariant says of one replay.** `None` when it holds.
fn broken(r: &Replay) -> Option<String> {
    let blocks = minutes(&[T1, T4]);
    let held: Vec<Span> = r.held_breaks.iter().map(|b| (mins_of(b.started), mins_of(b.ended))).collect();
    let union = minutes(&held);
    let credited = r.items.get("t1").map_or(0, |i| i.minutes) + r.items.get("t4").map_or(0, |i| i.minutes);
    let owed = blocks.difference(&union).count() as u32;
    if credited != owed {
        return Some(format!("credit {credited}, the blocks less the held union {owed}; held {held:?}"));
    }
    let drawn = minutes(&block_rows(r));
    if drawn.len() as u32 != owed || !drawn.is_subset(&blocks) || !drawn.is_disjoint(&union) {
        return Some(format!("drawn {:?}, owed {owed}; held {held:?}", block_rows(r)));
    }
    let brk_drawn = minutes(&break_rows(r));
    if brk_drawn != union {
        return Some(format!("breaks drawn {:?}, held {held:?}", break_rows(r)));
    }
    if r.days[&day()].block_min != owed {
        return Some(format!("block_min {}, owed {owed}", r.days[&day()].block_min));
    }
    None
}

/// A small deterministic generator: no new dependency, and a failure reprints its own lines.
struct Rng(u64);
impl Rng {
    fn next(&mut self, n: u32) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        u32::try_from(self.0 % u64::from(n)).expect("a small bound")
    }
    fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
        xs[self.next(xs.len() as u32) as usize]
    }
}

/// **The invariant, generated** (README gap 6027; the common brief's 1 and 2, at the kernel's level): any sequence of what the
/// verbs can write — a finished length, a re-time line of a line already there, ending anywhere, a `break_start` a later
/// `start` ends — leaves the credit, the block rows and the break rows the union of [`Replay::held_breaks`]. On 213e827 this
/// fails 18 of 300 by `fz.py`'s equivalent (README's §6).
#[test]
fn the_credit_and_the_rows_are_the_union_of_the_held_breaks_on_generated_days() {
    let mut rng = Rng(0x5eed_6027_u64);
    let grid: Vec<u32> = (9 * 60 + 10..10 * 60 + 5).step_by(5).collect();
    for case in 0..240 {
        let mut lines: Vec<String> = Vec::new();
        let mut known: Vec<(u32, u32)> = Vec::new();
        for _ in 0..2 + rng.next(2) {
            let s = rng.pick(&grid);
            if rng.next(8) == 0 && s < 10 * 60 + 5 {
                let p = rng.pick(&[10, 20]);
                lines.push(brk_start(&hm(s), p));
                known.push((s, p));
            } else {
                let p = rng.pick(&[5, 10, 15, 20, 30]);
                lines.push(brk(&hm(s), p, p));
                known.push((s, p));
            }
        }
        for _ in 0..1 + rng.next(4) {
            let (s, p) = rng.pick(&known);
            let a = 1 + rng.next(45);
            lines.push(brk(&hm(s), p, a));
        }
        let r = read(&lines);
        if let Some(why) = broken(&r) {
            panic!("case {case}: {why}\n{}", lines.join("\n"));
        }
    }
}

/// **The range is what the kernel reads** (`Replay.a_held_break_is_re_timed_in_its_range`, on a generated day): a line ending
/// inside a break's range moves that break's span to it, and the invariant still holds.
#[test]
fn every_instant_in_a_range_re_times_its_break_on_generated_days() {
    let mut rng = Rng(0x5eed_6022_u64);
    let grid: Vec<u32> = (9 * 60 + 10..10 * 60 + 5).step_by(5).collect();
    for case in 0..60 {
        let mut lines: Vec<String> = Vec::new();
        for _ in 0..2 + rng.next(2) {
            let (s, p) = (rng.pick(&grid), rng.pick(&[5, 10, 15, 20]));
            lines.push(brk(&hm(s), p, p));
        }
        let (s, p) = (rng.pick(&grid), 20);
        lines.push(brk(&hm(s), p, p));
        lines.push(brk(&hm(s), p, 1 + rng.next(p)));
        let r = read(&lines);
        for b in r.held_breaks.clone() {
            let (bs, be) = (mins_of(b.started), mins_of(b.ended));
            let mut ends: Vec<u32> = Vec::new();
            if let Some(f) = b.retime_from {
                let f = mins_of(f);
                ends.extend((f.max(bs + 1)..be).step_by(3));
            }
            if let Some(o) = b.out_to {
                ends.extend((be + 1..=mins_of(o)).step_by(3));
            }
            for e in ends {
                let mut more = lines.clone();
                more.push(brk(&hm(bs), b.planned_min, e - bs));
                let r2 = read(&more);
                let again = r2.held_breaks.iter().any(|h| mins_of(h.started) == bs && mins_of(h.ended) == e && h.planned_min == b.planned_min);
                assert!(again, "case {case}: {bs}..{be} to {e} not held after\n{}", more.join("\n"));
                let gone = r2.held_breaks.iter().filter(|h| h.started == b.started && h.ended == b.ended && h.planned_min == b.planned_min).count();
                assert_eq!(gone, 0, "case {case}: {bs}..{be} to {e} kept beside its re-time\n{}", more.join("\n"));
                if let Some(why) = broken(&r2) {
                    panic!("case {case}: to {e}: {why}\n{}", more.join("\n"));
                }
            }
        }
    }
}

/// The range's other side: a frozen break has none, and a line at its stamp changes no span it holds.
#[test]
fn a_frozen_break_has_no_range_and_its_line_moves_nothing() {
    let b = [brk("09:20", 10, 10), brk("09:25", 10, 10), brk("09:20", 10, 2)];
    let r = read(&b);
    assert_eq!(r.items["t1"].minutes, 48, "the critic's B is read");
    let nine25 = r.held_breaks.iter().find(|h| h.started == at("09:25")).expect("held");
    assert_eq!((nine25.ended, nine25.retime_from, nine25.out_to), (at("09:35"), None, None));
    let nine20 = r.held_breaks.iter().find(|h| h.started == at("09:20")).expect("held");
    assert_eq!((nine20.ended, nine20.widest, nine20.retime_from, nine20.out_to), (at("09:22"), at("09:30"), Some(at("09:20")), Some(at("09:30"))));
    let mut more = b.to_vec();
    more.push(brk("09:25", 10, 3));
    let r = read(&more);
    assert_eq!(r.items["t1"].minutes, 48, "gap 5971's silent short take is gone: the line is a break of its own");
    assert_eq!(broken(&r), None);
}

/// Defect A's five lines (README gap 6020): 88, and the review the plan draws.
#[test]
fn defect_a_reads_the_union() {
    let r = read(&[brk("09:20", 30, 30), brk("09:20", 30, 10), brk("09:40", 15, 15), brk("09:20", 30, 30), brk("09:40", 15, 12)]);
    assert_eq!(r.days[&day()].block_min, 88);
    assert_eq!(block_rows(&r), vec![(9 * 60, 9 * 60 + 20), (9 * 60 + 52, 10 * 60), (10 * 60 + 10, 11 * 60 + 10)]);
    assert_eq!(broken(&r), None);
}

/// The straddling piece (README gap 6020, found driving 213e827): two plain re-times of two breaks apart, review 105 and the
/// plan 100, the stretch 09:25–09:30 drawn nowhere.
#[test]
fn a_piece_wider_than_a_take_is_put_back_whole() {
    let r = read(&[brk("09:20", 10, 10), brk("09:40", 15, 15), brk("09:20", 10, 5), brk("09:40", 15, 10)]);
    assert_eq!(r.days[&day()].block_min, 105);
    assert_eq!(block_rows(&r), vec![(9 * 60, 9 * 60 + 20), (9 * 60 + 25, 9 * 60 + 40), (9 * 60 + 50, 10 * 60), (10 * 60 + 10, 11 * 60 + 10)]);
    assert_eq!(broken(&r), None);
}

/// Gap 5973 (README gap 6021): the D141 end is read, and the older break it let go of is frozen: its re-time, which the base
/// kernel "read" with a hole, is a break of its own.
#[test]
fn gap_5973s_older_break_is_frozen_by_a_d141_end() {
    let d = [brk("09:40", 5, 5), brk_start("09:30", 20), brk("09:30", 20, 5)];
    let r = read(&d);
    assert_eq!(r.days[&day()].block_min, 110);
    let nine40 = r.held_breaks.iter().find(|h| h.started == at("09:40")).expect("held");
    assert_eq!((nine40.retime_from, nine40.out_to), (None, None));
    let mut more = d.to_vec();
    more.push(brk("09:40", 5, 2));
    let r = read(&more);
    assert_eq!(r.days[&day()].block_min, 110);
    assert_eq!(broken(&r), None);
}

/// Defect D: C2 and D-3 are in range, E2's end needs no fact, and the fact lists every break of a nested pair.
#[test]
fn c2_and_d3_are_in_range() {
    let r = read(&[brk("09:20", 30, 30), brk("09:30", 5, 5)]);
    assert_eq!(r.held_breaks.len(), 2);
    let outer = r.held_breaks.iter().find(|h| h.started == at("09:20")).expect("held");
    assert_eq!((outer.ended, outer.retime_from), (at("09:50"), Some(at("09:20"))));
    let r = read(&[brk("09:20", 30, 30), brk("09:20", 30, 20), brk("09:35", 5, 5)]);
    let outer = r.held_breaks.iter().find(|h| h.started == at("09:20")).expect("held");
    assert_eq!((outer.ended, outer.widest, outer.out_to), (at("09:40"), at("09:50"), Some(at("09:50"))));
    let r = read(&[brk("09:20", 30, 30), brk("09:20", 30, 20), brk("09:35", 5, 5), brk("09:20", 30, 25)]);
    assert_eq!(r.days[&day()].block_min, 95);
    assert_eq!(broken(&r), None);
}

/// The fact holds no range while a break runs, and a D129 ending has no `out_to`.
#[test]
fn no_range_while_a_break_runs_and_no_out_to_for_an_ending() {
    let r = read(&[brk("09:20", 10, 10), brk_start("11:30", 20)]);
    assert_eq!(r.held_breaks.len(), 1);
    assert_eq!((r.held_breaks[0].retime_from, r.held_breaks[0].out_to), (None, None));
    let r = read(&[brk_start("09:30", 20)]);
    assert_eq!(r.held_breaks.len(), 1);
    let h = &r.held_breaks[0];
    assert_eq!((h.ended, h.retime_from, h.out_to), (at("10:10"), Some(at("09:30")), None));
}

// --- D154: the log's typed-time lines -------------------------------------------------------------------------------

/// The log's latest typed-time stamp, the clock `now`: over a scratch root, at [`Replay::latest_t`]'s own door.
fn latest(lines: &[String], now: &str) -> Option<DateTime<FixedOffset>> {
    let dir = tempfile::tempdir().expect("a temp dir");
    let root = dir.path();
    std::fs::create_dir_all(root.join(".tm")).expect("mkdir");
    let bytes = log(lines).into_bytes();
    std::fs::write(root.join(".tm/log.jsonl"), &bytes).expect("write");
    let wire = tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), TZ);
    let now = DateTime::parse_from_rfc3339(now).expect("an instant");
    let fence = kernel_log::instant_wire(now + chrono::Duration::days(tm_core::check::LOG_FUTURE_DAYS));
    let fence = (fence[0].as_u64().expect("sec"), fence[1].as_u64().expect("ns"));
    kernel_log::replay_scoped_at(root, &bytes, TZ, &wire, now.with_timezone(&TZ).date_naive(), Some(fence), kernel_log::Scope::All, None)
        .unwrap_or_else(|e| panic!("the door answers: {e:?}"))
        .replay
        .latest_t
}

fn energy(t: &str) -> String {
    format!(r#"{{"t":"{t}","ev":"energy","pred":3,"rep":3,"hsw":3.0,"loc":"home"}}"#)
}

/// A stated instant that can run ahead is no witness: `tm energy 3 --at 18:00` typed at 10:12.
#[test]
fn a_forward_energy_report_is_not_a_typed_stamp() {
    let l = vec![start_line("10:10", "t4"), energy("2026-09-08T18:00:00-05:00")];
    assert_eq!(latest(&l, "2026-09-08T10:15:00-05:00"), Some(at("10:10")));
}

/// An `arrive` and a `wake` stamped ahead neither.
#[test]
fn a_forward_arrive_or_wake_is_not_a_typed_stamp() {
    let arrive = r#"{"t":"2026-09-08T18:00:00-05:00","ev":"arrive","loc":"home","window":["08:00","16:00"],"budget":6}"#.to_string();
    let wake = r#"{"t":"2026-09-08T19:00:00-05:00","ev":"wake","slept_min":420}"#.to_string();
    let l = vec![start_line("10:10", "t4"), arrive, wake];
    assert_eq!(latest(&l, "2026-09-08T10:15:00-05:00"), Some(at("10:10")));
}

/// D18's far-future line hides nothing: the next-latest stamp answers, and once `now` is within two days of it, it counts.
#[test]
fn a_far_future_line_hides_nothing_and_counts_once_it_is_near() {
    let plan = r#"{"t":"2027-01-01T09:00:00-06:00","ev":"plan","hash":"x","replans_today":0,"drift_min":0}"#.to_string();
    let l = vec![start_line("10:10", "t4"), plan];
    assert_eq!(latest(&l, "2026-09-08T10:15:00-05:00"), Some(at("10:10")));
    let near = latest(&l, "2026-12-31T09:00:00-06:00").expect("a stamp");
    assert_eq!(near, DateTime::parse_from_rfc3339("2027-01-01T09:00:00-06:00").expect("an instant"));
}

/// An undone line and its undo count: the instant was reached either way (D154, reversing D153's survivors).
#[test]
fn an_undone_line_and_its_undo_count() {
    let l = vec![
        start_line("10:10", "t4"),
        r#"{"t":"2026-09-08T10:50:00-05:00","ev":"pause","id":"t4"}"#.to_string(),
        r#"{"t":"2026-09-08T10:50:00-05:00","ev":"unpause","id":"t4"}"#.to_string(),
        r#"{"t":"2026-09-08T10:51:00-05:00","ev":"undo","of":"unpause","id":"t4"}"#.to_string(),
    ];
    assert_eq!(latest(&l, "2026-09-08T10:52:00-05:00"), Some(at("10:51")));
}

/// Law: a resume answers what a genesis does, a checkpoint folded below it (`Seal.latestTyped_is_the_whole_logs`). A long log of
/// days, each ending in a note and an energy report ahead of itself, read warm from the checkpoint an earlier call left and cold.
#[test]
fn a_resume_answers_what_a_rebuild_does() {
    let mut l: Vec<String> = Vec::new();
    for d in 1..=25 {
        l.push(format!(r#"{{"t":"2026-08-{d:02}T07:00:00-05:00","ev":"wake","slept_min":420}}"#));
        l.push(format!(r#"{{"t":"2026-08-{d:02}T09:00:00-05:00","ev":"note","text":"n"}}"#));
        l.push(energy(&format!("2026-08-{d:02}T22:00:00-05:00")));
    }
    let dir = tempfile::tempdir().expect("a temp dir");
    let root = dir.path();
    std::fs::create_dir_all(root.join(".tm")).expect("mkdir");
    let wire = tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), TZ);
    let now = DateTime::parse_from_rfc3339("2026-09-20T09:00:00-05:00").expect("an instant");
    let fence = kernel_log::instant_wire(now + chrono::Duration::days(2));
    let fence = (fence[0].as_u64().expect("sec"), fence[1].as_u64().expect("ns"));
    let today = now.with_timezone(&TZ).date_naive();
    let bytes = log(&l).into_bytes();
    let first = kernel_log::replay_scoped_at(root, &bytes, TZ, &wire, today, Some(fence), kernel_log::Scope::All, None).expect("the door");
    assert!(first.ledger_day.is_some(), "the log sealed: the fold reaches this row");
    let want = DateTime::parse_from_rfc3339("2026-08-25T09:00:00-05:00").expect("an instant");
    assert_eq!(first.replay.latest_t, Some(want));
    let warm = kernel_log::replay_scoped_at(root, &bytes, TZ, &wire, today, Some(fence), kernel_log::Scope::All, None).expect("the door");
    assert_eq!(warm.replay.latest_t, Some(want), "warm");
    assert_eq!(latest(&l, "2026-09-20T09:00:00-05:00"), Some(want), "cold");
}
