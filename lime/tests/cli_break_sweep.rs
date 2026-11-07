//! **The break invariant, generated, through the binary** — stage 6 W-54 third repair track H (README gap 6040; the
//! owner's D129, D141, D143, D147, D149-D152 and the gate of README gap 5990). After ANY sequence of `lime break` keystrokes on
//! the J day (`^t1` 09:00–10:00 and `^t4` 10:10–11:10 done, review 120):
//!
//! 1. the review's `block_min` equals the minutes of the block rows `lime plan` draws, every minute of the blocks is drawn
//!    as a block or a break, and no block lies over a break;
//! 2. a cold rebuild (`.tm/state.json` and the cache deleted) answers the same;
//! 3. a reply saying "re-timed" or "ended" moved the review or the drawn rows, and a refusal wrote nothing;
//! 4. no `break_start` is written at an instant inside the closed span of a break the log holds (README gap 6044's one
//!    exception, as the test states it from the log: a length, no block open at the instant and no typed-time line stamped at or
//!    after it), and a no-length keystroke with nothing running DOES begin a break outside every held break's own span and
//!    widest end.
//!
//! The R day (`^t1` done, `^t4` running since 10:10) holds the same clauses, read after a `lime stop` at 12:30 on the copy, because
//! the review counts closed blocks (README gap 6050).
//!
//! What the log "holds" is the kernel's fact, `Replay::held_breaks`, read off the log's text before each keystroke. Every
//! read runs on a COPY of the tree: `lime plan` logs a line, and the sequence under test must hold the keystrokes alone.
//!
//! `LIME_SWEEP_BIN` runs another binary under the same clauses: that is how this test was shown to fail on 213e827's by
//! defect A's shape before it was trusted (README gap 6040). Without it, the binary under test.

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use std::fs;
use std::path::Path;
use std::process::Command;
use std::sync::OnceLock;

use chrono::{DateTime, FixedOffset};
use proptest::prelude::*;
use serde_json::Value;
use tempfile::TempDir;
use lime_core::log::Replay;

const TZ: chrono_tz::Tz = chrono_tz::America::Chicago;

/// One keystroke: `lime break --now <minute of the day> [<length>m]`.
type Key = (u32, Option<u32>);

fn hm(m: u32) -> String {
    format!("{:02}:{:02}", m / 60, m % 60)
}

fn at(m: u32) -> String {
    format!("2026-09-08T{}:00-05:00", hm(m))
}

fn stamp(m: u32) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(&at(m)).expect("an instant")
}

const fn m(h: u32, min: u32) -> u32 {
    h * 60 + min
}

fn run(dir: &Path, now: &str, args: &[&str]) -> std::process::Output {
    let bin = lime_core::devenv::var("LIME_SWEEP_BIN").unwrap_or_else(|_| env!("CARGO_BIN_EXE_lime").to_string());
    Command::new(bin).arg("--dir").arg(dir).arg("--now").arg(now).args(args).output().expect("run lime")
}

fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("a directory");
    for e in fs::read_dir(from).expect("a directory") {
        let e = e.expect("an entry");
        let target = to.join(e.file_name());
        if e.file_type().expect("a type").is_dir() {
            copy_dir(&e.path(), &target);
        } else {
            fs::copy(e.path(), &target).expect("a copy");
        }
    }
}

/// Which day a sequence runs on: `J`, both blocks done; `R`, `^t4` still running since 10:10.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Day {
    J,
    R,
}

/// The day, once per test binary; each sequence runs on a copy of it.
fn the_day(day: Day) -> &'static Path {
    static J: OnceLock<TempDir> = OnceLock::new();
    static R: OnceLock<TempDir> = OnceLock::new();
    let build = || {
        let tmp = TempDir::new().expect("a directory");
        let d = tmp.path();
        let steps: &[(&str, &[&str])] = &[
            ("06:00", &["init", "--example"]),
            ("07:00", &["wake", "07:00"]),
            ("08:00", &["arrive", "home"]),
            ("09:00", &["start", "^t1"]),
            ("10:00", &["done"]),
            ("10:10", &["start", "^t4"]),
            ("11:10", &["done"]),
        ];
        let steps = if day == Day::J { steps } else { &steps[..6] };
        for (now, args) in steps {
            let o = run(d, &format!("2026-09-08T{now}:00-05:00"), args);
            assert!(o.status.success(), "{args:?}: {}", String::from_utf8_lossy(&o.stderr));
        }
        tmp
    };
    match day {
        Day::J => J.get_or_init(build).path(),
        Day::R => R.get_or_init(build).path(),
    }
}

/// What the day reads at 12:30, on a copy.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Read {
    block_min: u64,
    blocks: Vec<(u32, u32, String)>,
    breaks: Vec<(u32, u32)>,
}

fn minutes(s: &str) -> u32 {
    let h: u32 = s[..2].parse().expect("an hour");
    let n: u32 = s[3..5].parse().expect("a minute");
    h * 60 + n
}

fn read(day: Day, tree: &Path, cold: bool) -> Result<Read, String> {
    let tmp = TempDir::new().expect("a directory");
    let d = tmp.path().join("t");
    copy_dir(tree, &d);
    if cold {
        fs::remove_file(d.join(".tm/state.json")).map_err(|e| format!("the cache: {e}"))?;
        let _ = fs::remove_dir_all(d.join(".tm/cache"));
    }
    let now = at(m(12, 30));
    if day == Day::R {
        let o = run(&d, &now, &["stop"]);
        if !o.status.success() {
            return Err(format!("`lime stop` failed: {}", String::from_utf8_lossy(&o.stderr)));
        }
    }
    let horizon = if day == Day::J { m(12, 0) } else { m(12, 30) };
    let doc = |args: &[&str]| -> Result<Value, String> {
        let o = run(&d, &now, args);
        if !o.status.success() {
            return Err(format!("`lime {}` failed: {}", args.join(" "), String::from_utf8_lossy(&o.stderr)));
        }
        serde_json::from_slice(&o.stdout).map_err(|e| format!("not JSON ({e})"))
    };
    let review = doc(&["--json", "review", "day"])?;
    let plan = doc(&["--json", "plan"])?;
    let block_min = review["review"]["block_min"].as_u64().ok_or("no block_min")?;
    let (mut blocks, mut breaks) = (vec![], vec![]);
    for s in plan["segments"].as_array().ok_or("no segments")? {
        let (from, to) = (minutes(s["start"].as_str().ok_or("a start")?), minutes(s["end"].as_str().ok_or("an end")?));
        if from >= horizon {
            continue;
        }
        match s["kind"].as_str() {
            Some("block") if s["item"] == "t1" || s["item"] == "t4" => {
                blocks.push((from, to, s["item"].as_str().unwrap_or_default().to_string()));
            }
            Some("break") => breaks.push((from, to)),
            _ => {}
        }
    }
    blocks.sort();
    breaks.sort_unstable();
    Ok(Read { block_min, blocks, breaks })
}

/// Clause 1, on one read.
fn the_day_is_one_reading(day: Day, r: &Read) -> Result<(), String> {
    let drawn: u32 = r.blocks.iter().map(|(a, b, _)| b - a).sum();
    if u64::from(drawn) != r.block_min {
        return Err(format!("the review says {} and the plan draws {drawn}: {r:?}", r.block_min));
    }
    for b in m(9, 0)..(if day == Day::J { m(11, 10) } else { m(12, 30) }) {
        if (m(10, 0)..m(10, 10)).contains(&b) {
            continue;
        }
        let blocks = r.blocks.iter().filter(|(a, e, _)| *a <= b && b < *e).count();
        let breaks = r.breaks.iter().filter(|(a, e)| *a <= b && b < *e).count();
        if blocks > 1 || (blocks == 1 && breaks > 0) {
            return Err(format!("{} is drawn twice: {r:?}", hm(b)));
        }
        if blocks == 0 && breaks == 0 {
            return Err(format!("{} is drawn nowhere: {r:?}", hm(b)));
        }
    }
    Ok(())
}

fn fact(tree: &Path) -> Replay {
    let text = fs::read_to_string(tree.join(".tm/log.jsonl")).expect("the log");
    chokepoint::replay_of_text(&text, TZ)
}

/// Spans, adjacent or overlapping ones merged: a break cut in two and drawn in the same place is the same day.
fn merged<I: IntoIterator<Item = (u32, u32)>>(spans: I) -> Vec<(u32, u32)> {
    let mut v: Vec<(u32, u32)> = spans.into_iter().collect();
    v.sort_unstable();
    let mut out: Vec<(u32, u32)> = vec![];
    for (a, b) in v {
        match out.last_mut() {
            Some(l) if a <= l.1 => l.1 = l.1.max(b),
            _ => out.push((a, b)),
        }
    }
    out
}

/// What a line must have changed for "re-timed" or "ended" to be true (clause 3): the review, or where the blocks and breaks
/// are drawn. A break's row cut in two at the typed instant, with the union as it was, is not a move (README gap 6052).
fn drawn(r: &Read) -> (u64, Vec<(u32, u32)>, Vec<(u32, u32)>) {
    (r.block_min, merged(r.blocks.iter().map(|(a, b, _)| (*a, *b))), merged(r.breaks.iter().copied()))
}

/// The log's latest stamp of a line stamped when its verb ran (D154's `typedAt?`, read off the log's text by this test).
fn latest_typed(log: &str) -> Option<DateTime<FixedOffset>> {
    log.lines()
        .filter_map(|l| serde_json::from_str::<Value>(l).ok())
        .filter(|v| !matches!(v["ev"].as_str(), Some("wake" | "arrive" | "energy")))
        .filter_map(|v| DateTime::parse_from_rfc3339(v["t"].as_str()?).ok())
        .max()
}

/// One keystroke on `tree`, holding clauses 3 and 4.
fn keystroke(day: Day, tree: &Path, (minute, len): Key) -> Result<(), String> {
    let before = fact(tree);
    let t = stamp(minute);
    // A length at a held break's very end begins after it, with nothing lost; no length there is "already ends".
    let closed: Vec<_> =
        before.held_breaks.iter().filter(|b| b.started <= t && (t < b.ended || (len.is_none() && t == b.ended))).collect();
    let reach = before.held_breaks.iter().any(|b| b.started <= t && t <= b.ended.max(b.widest));
    let snapshot = TempDir::new().expect("a directory");
    let prior = snapshot.path().join("t");
    copy_dir(tree, &prior);
    let length = len.map(|l| format!("{l}m"));
    let mut args = vec!["--json", "break"];
    if let Some(l) = &length {
        args.push(l);
    }
    let lines_of = |d: &Path| fs::read_to_string(d.join(".tm/log.jsonl")).unwrap_or_default();
    let (log0, day0, state0) = (
        lines_of(tree),
        fs::read_to_string(tree.join("day/2026-09-08.md")).unwrap_or_default(),
        fs::read_to_string(tree.join(".tm/state.json")).unwrap_or_default(),
    );
    let o = run(tree, &at(minute), &args);
    let log1 = lines_of(tree);
    let said = format!("{}{}", String::from_utf8_lossy(&o.stdout), String::from_utf8_lossy(&o.stderr));
    if !o.status.success() {
        if said.contains("a bug in lime") {
            return Err(format!("a fault: {said}"));
        }
        let (day1, state1) = (
            fs::read_to_string(tree.join("day/2026-09-08.md")).unwrap_or_default(),
            fs::read_to_string(tree.join(".tm/state.json")).unwrap_or_default(),
        );
        if log1 != log0 || day1 != day0 || state1 != state0 {
            return Err(format!("a refusal wrote: {said}"));
        }
        return Ok(());
    }
    let doc: Value = serde_json::from_slice(&o.stdout).map_err(|e| format!("not JSON ({e}): {said}"))?;
    let action = doc["action"].as_str().unwrap_or_default().to_string();
    // A length typed with an ending (D146) says both: the break ended here and a finished one from here, and the two may fill
    // the stretch again exactly (`09:15`, then `09:55 15m` up to 10:10). The union then stays, and the reply is true.
    if action == "retimed" || (action == "ended" && len.is_none()) {
        let (was, is) = (read(day, &prior, false)?, read(day, tree, false)?);
        if drawn(&was) == drawn(&is) {
            return Err(format!("the reply says {action:?} and nothing moved: {said} {is:?}"));
        }
    }
    let new_lines = log1.strip_prefix(log0.as_str()).unwrap_or_default();
    let began = new_lines.lines().any(|l| l.contains("\"ev\":\"break_start\""));
    // README gap 6044's one exception, the owner's call, in its own words read off the log: a length, no block open at the
    // instant, and no typed-time line at or past it (so no later start, no closed block around it, no passed end). Everything
    // else inside a held span is gap 5810's loss. Until the attackers' re-drive this was `len.is_some() && open_break.is_some()`,
    // true of every length that begins a break, which exempted the very shapes clause 4 exists for (README gap 6050).
    let nothing_at_stake = len.is_some()
        && before.open_block.as_ref().map_or(true, |b| t < b.started)
        && latest_typed(&log0).map_or(true, |l| l < t);
    if began && !closed.is_empty() && !nothing_at_stake {
        return Err(format!("a `break_start` inside the held span {}–{}: {said}", closed[0].started, closed[0].ended));
    }
    if len.is_none() && before.open_break.is_none() && !reach && !began {
        return Err(format!("outside every held break and widest end, no break began: {action:?} {said}"));
    }
    Ok(())
}

/// The whole invariant over one sequence, on a copy of the day; `Err` names the step.
fn on_day(day: Day, keys: &[Key]) -> Result<(), String> {
    let tmp = TempDir::new().expect("a directory");
    let tree = tmp.path().join("t");
    copy_dir(the_day(day), &tree);
    for (i, k) in keys.iter().enumerate() {
        keystroke(day, &tree, *k).map_err(|e| format!("{day:?} keystroke {i} of {keys:?}: {e}"))?;
    }
    let warm = read(day, &tree, false).map_err(|e| format!("{day:?} {keys:?}: {e}"))?;
    the_day_is_one_reading(day, &warm).map_err(|e| format!("{day:?} {keys:?}: {e}"))?;
    let cold = read(day, &tree, true).map_err(|e| format!("{day:?} {keys:?}: {e}"))?;
    if cold != warm {
        return Err(format!("{day:?} {keys:?}: warm {warm:?}, cold {cold:?}"));
    }
    Ok(())
}

fn sequence(keys: &[Key]) -> Result<(), String> {
    on_day(Day::J, keys)
}

/// The shapes of the W-54 third repair's brief, each a sequence (`None`: no length).
fn shapes() -> Vec<(&'static str, Vec<Key>)> {
    let k = |h, n, l: Option<u32>| (m(h, n), l);
    vec![
        ("A", vec![k(9, 20, Some(30)), k(9, 30, None), k(9, 40, Some(15)), k(9, 20, Some(30)), k(9, 52, None)]),
        ("Z", vec![k(9, 20, Some(10)), k(9, 40, Some(15)), k(9, 25, None), k(9, 50, None)]),
        ("B1", vec![k(9, 35, Some(5)), k(9, 30, None), k(9, 45, None), k(9, 47, None)]),
        ("B2", vec![k(9, 20, Some(10)), k(9, 25, Some(10)), k(9, 31, Some(2)), k(9, 37, None)]),
        ("d5", vec![k(9, 27, Some(10)), k(9, 30, None), k(9, 20, Some(10)), k(9, 25, Some(10)), k(9, 33, None)]),
        ("C2", vec![k(9, 20, Some(30)), k(9, 30, Some(5)), k(9, 40, None)]),
        ("D-3", vec![k(9, 20, Some(30)), k(9, 40, None), k(9, 35, Some(5)), k(9, 45, None)]),
        ("E2", vec![k(9, 20, Some(30)), k(9, 30, Some(5)), k(9, 50, None)]),
        ("5971 B", vec![k(9, 20, Some(10)), k(9, 25, Some(10)), k(9, 22, None), k(9, 28, None)]),
        ("5971 C", vec![k(9, 20, Some(30)), k(9, 30, Some(5)), k(9, 25, None)]),
        ("5973", vec![k(9, 40, Some(5)), k(9, 30, None), k(9, 42, None), k(9, 43, None)]),
        ("5973 K", vec![k(9, 40, Some(5)), k(9, 30, None), k(9, 35, None), k(9, 42, None)]),
        ("6024", vec![k(9, 20, Some(30)), k(9, 30, None), k(9, 40, Some(15)), k(9, 32, None), k(9, 45, None)]),
        ("twins", vec![k(10, 30, Some(10)), k(10, 30, Some(10)), k(10, 35, None)]),
        ("one start", vec![k(10, 30, Some(10)), k(10, 30, Some(15)), k(10, 45, None)]),
        ("after the blocks", vec![k(11, 20, Some(20)), k(11, 30, None), k(11, 25, Some(5))]),
        ("hidden twin", vec![k(9, 35, Some(15)), k(9, 15, None), k(9, 35, Some(15)), k(9, 40, None)]),
        ("span over a closed block", vec![k(10, 30, Some(90)), k(10, 35, Some(5))]),
        ("span over a closed block, past it", vec![k(10, 30, Some(90)), k(10, 35, Some(90))]),
        ("d129 start, 60m", vec![k(9, 42, None), k(9, 25, Some(30)), k(9, 42, Some(60))]),
        ("d129 start, the old advice", vec![k(9, 42, None), k(9, 25, Some(30)), k(9, 42, None), k(9, 42, Some(5)), k(9, 45, None), k(9, 30, None)]),
        ("d141 in two spans", vec![k(9, 40, None), k(9, 30, None), k(9, 45, None)]),
        ("d141 in two spans, finished", vec![k(9, 40, Some(30)), k(9, 30, None), k(9, 45, None)]),
        ("d141 at the inner start (seed)", vec![k(9, 30, None), k(9, 15, None), k(9, 30, None)]),
    ]
}

/// The R day's shapes: the block runs, so a break the user ended is the only witness of its end (README gap 6050).
fn r_shapes() -> Vec<(&'static str, Vec<Key>)> {
    let k = |h, n, l: Option<u32>| (m(h, n), l);
    vec![
        ("R", vec![k(10, 15, None), k(10, 40, None), k(10, 20, Some(5))]),
        ("R past", vec![k(10, 15, None), k(10, 40, None), k(10, 20, Some(30))]),
        ("R at its start", vec![k(10, 15, None), k(10, 40, None), k(10, 15, Some(5))]),
        ("R same length at its start", vec![k(10, 15, None), k(10, 40, None), k(10, 15, Some(20))]),
        ("R at its end", vec![k(10, 15, None), k(10, 40, None), k(10, 40, Some(5))]),
        ("R two", vec![k(10, 15, Some(5)), k(10, 20, None), k(10, 30, None), k(10, 40, None), k(10, 35, Some(5))]),
        ("d146 refills the stretch (seed)", vec![k(9, 15, None), k(9, 55, Some(15)), k(9, 15, None)]),
    ]
}

/// **Every shape of the brief holds the invariant** — and this row is what fails on 213e827's binary (`LIME_SWEEP_BIN`), by A's
/// shape: the review says 98 and the plan draws 88.
#[test]
fn the_briefs_shapes_hold_the_invariant() {
    for (name, keys) in shapes() {
        if let Err(e) = sequence(&keys) {
            panic!("{name}: {e}");
        }
    }
}

/// **The R day's shapes hold it** (README gap 6050): this row fails on the binary before that gap's fix.
#[test]
fn the_r_days_shapes_hold_the_invariant() {
    for (name, keys) in r_shapes() {
        if let Err(e) = on_day(Day::R, &keys) {
            panic!("{name}: {e}");
        }
    }
}

/// **Every minute of the morning, against every shape** — no length and five minutes typed last. Run at acceptance
/// (`--ignored`; about ten minutes on twelve threads): the result is quoted in the README, W-54 third repair track H, §2.
#[test]
#[ignore = "exhaustive: run at acceptance"]
fn every_minute_against_every_shape_holds_the_invariant() {
    let shapes = shapes();
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get().min(12));
    let r_shapes = r_shapes();
    let mut jobs: Vec<(Day, Vec<Key>)> = vec![];
    for (day, set) in [(Day::J, &shapes), (Day::R, &r_shapes)] {
        for (_, keys) in set {
            for minute in m(9, 0)..=m(11, 30) {
                for len in [None, Some(5)] {
                    let mut k = keys.clone();
                    k.push((minute, len));
                    jobs.push((day, k));
                }
            }
        }
    }
    let total = jobs.len();
    let chunks: Vec<Vec<(Day, Vec<Key>)>> =
        (0..threads).map(|i| jobs.iter().skip(i).step_by(threads).cloned().collect()).collect();
    let bad: Vec<String> = std::thread::scope(|s| {
        let hs: Vec<_> = chunks
            .iter()
            .map(|c| s.spawn(move || c.iter().filter_map(|(d, k)| on_day(*d, k).err()).collect::<Vec<_>>()))
            .collect();
        hs.into_iter().flat_map(|h| h.join().expect("a thread")).collect()
    });
    println!("SWEEP: {total} sequences, {} disagree", bad.len());
    assert!(bad.is_empty(), "{} of {total}:\n{}", bad.len(), bad[..bad.len().min(40)].join("\n"));
}

fn a_key() -> impl Strategy<Value = Key> {
    let dense = (m(9, 15) / 5..=m(10, 5) / 5).prop_map(|g| g * 5);
    let wide = (m(9, 0) / 5..=m(11, 30) / 5).prop_map(|g| g * 5);
    let at = prop_oneof![3 => dense, 1 => wide];
    let len = prop_oneof![
        2 => Just(None),
        1 => Just(Some(5u32)),
        1 => Just(Some(10u32)),
        1 => Just(Some(15u32)),
        1 => Just(Some(20u32)),
        1 => Just(Some(30u32)),
        1 => Just(Some(90u32)),
    ];
    (at, len)
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: lime_core::devenv::var("LIME_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(64),
        max_shrink_iters: 200,
        ..ProptestConfig::default()
    })]

    /// **The invariant after any 3-6 keystrokes on the five-minute grid, a length or none.** A new line in this file's
    /// `.proptest-regressions` is a finding (D46), never a dirty tree to revert.
    #[test]
    fn the_invariant_holds_after_any_break_keystrokes(keys in proptest::collection::vec(a_key(), 3..=6)) {
        if let Err(e) = sequence(&keys) {
            prop_assert!(false, "{}", e);
        }
    }

    /// **The same on the R day, its block still running** (README gap 6050): the J day cannot draw a running block.
    #[test]
    fn the_invariant_holds_after_any_break_keystrokes_on_a_running_block(keys in proptest::collection::vec(a_key(), 3..=6)) {
        if let Err(e) = on_day(Day::R, &keys) {
            prop_assert!(false, "{}", e);
        }
    }
}
