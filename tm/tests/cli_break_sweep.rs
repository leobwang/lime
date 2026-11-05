//! **The break invariant, generated, through the binary** — stage 6 W-54 third repair track H (README gap 6040; the
//! owner's D129, D141, D143, D147, D149-D152 and the gate of README gap 5990). After ANY sequence of `tm break` keystrokes on
//! the J day (`^t1` 09:00–10:00 and `^t4` 10:10–11:10 done, review 120):
//!
//! 1. the review's `block_min` equals the minutes of the block rows `tm plan` draws, every minute of the blocks is drawn
//!    as a block or a break, and no block lies over a break;
//! 2. a cold rebuild (`.tm/state.json` and the cache deleted) answers the same;
//! 3. a reply saying "re-timed" or "ended" moved the review or the drawn rows, and a refusal wrote nothing;
//! 4. no `break_start` is written at an instant inside the closed span of a break the log holds (a length with nothing to
//!    end it is the one exception, README gap 6044), and a no-length keystroke with nothing running DOES begin a break outside
//!    every held break's own span and widest end.
//!
//! What the log "holds" is the kernel's fact, `Replay::held_breaks`, read off the log's text before each keystroke. Every
//! read runs on a COPY of the tree: `tm plan` logs a line, and the sequence under test must hold the keystrokes alone.
//!
//! `TM_SWEEP_BIN` runs another binary under the same clauses: that is how this test was shown to fail on 213e827's by
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
use tm_core::log::Replay;

const TZ: chrono_tz::Tz = chrono_tz::America::Chicago;

/// One keystroke: `tm break --now <minute of the day> [<length>m]`.
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
    let bin = std::env::var("TM_SWEEP_BIN").unwrap_or_else(|_| env!("CARGO_BIN_EXE_tm").to_string());
    Command::new(bin).arg("--dir").arg(dir).arg("--now").arg(now).args(args).output().expect("run tm")
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

/// The J day, once per test binary; each sequence runs on a copy of it.
fn j_day() -> &'static Path {
    static DAY: OnceLock<TempDir> = OnceLock::new();
    DAY.get_or_init(|| {
        let tmp = TempDir::new().expect("a directory");
        let d = tmp.path();
        for (now, args) in [
            ("06:00", &["init", "--example"][..]),
            ("07:00", &["wake", "07:00"][..]),
            ("08:00", &["arrive", "home"][..]),
            ("09:00", &["start", "^t1"][..]),
            ("10:00", &["done"][..]),
            ("10:10", &["start", "^t4"][..]),
            ("11:10", &["done"][..]),
        ] {
            let o = run(d, &format!("2026-09-08T{now}:00-05:00"), args);
            assert!(o.status.success(), "{args:?}: {}", String::from_utf8_lossy(&o.stderr));
        }
        tmp
    })
    .path()
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

fn read(tree: &Path, cold: bool) -> Result<Read, String> {
    let tmp = TempDir::new().expect("a directory");
    let d = tmp.path().join("t");
    copy_dir(tree, &d);
    if cold {
        fs::remove_file(d.join(".tm/state.json")).map_err(|e| format!("the cache: {e}"))?;
        let _ = fs::remove_dir_all(d.join(".tm/cache"));
    }
    let now = at(m(12, 30));
    let doc = |args: &[&str]| -> Result<Value, String> {
        let o = run(&d, &now, args);
        if !o.status.success() {
            return Err(format!("`tm {}` failed: {}", args.join(" "), String::from_utf8_lossy(&o.stderr)));
        }
        serde_json::from_slice(&o.stdout).map_err(|e| format!("not JSON ({e})"))
    };
    let review = doc(&["--json", "review", "day"])?;
    let plan = doc(&["--json", "plan"])?;
    let block_min = review["review"]["block_min"].as_u64().ok_or("no block_min")?;
    let (mut blocks, mut breaks) = (vec![], vec![]);
    for s in plan["segments"].as_array().ok_or("no segments")? {
        let (from, to) = (minutes(s["start"].as_str().ok_or("a start")?), minutes(s["end"].as_str().ok_or("an end")?));
        if from >= m(12, 0) {
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
fn the_day_is_one_reading(r: &Read) -> Result<(), String> {
    let drawn: u32 = r.blocks.iter().map(|(a, b, _)| b - a).sum();
    if u64::from(drawn) != r.block_min {
        return Err(format!("the review says {} and the plan draws {drawn}: {r:?}", r.block_min));
    }
    for b in m(9, 0)..m(11, 10) {
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

/// One keystroke on `tree`, holding clauses 3 and 4.
fn keystroke(tree: &Path, (minute, len): Key) -> Result<(), String> {
    let before = fact(tree);
    let t = stamp(minute);
    let closed: Vec<_> = before.held_breaks.iter().filter(|b| b.started <= t && t <= b.ended).collect();
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
        if said.contains("a bug in tm") {
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
    if matches!(action.as_str(), "retimed" | "ended") {
        let (was, is) = (read(&prior, false)?, read(tree, false)?);
        if was == is {
            return Err(format!("the reply says {action:?} and nothing moved: {said} {is:?}"));
        }
    }
    let new_lines = log1.strip_prefix(log0.as_str()).unwrap_or_default();
    let began = new_lines.lines().any(|l| l.contains("\"ev\":\"break_start\""));
    // A length with nothing to end it begins a running break there (README gap 6044: gap 5775's row pins it, no start follows,
    // so gap 5810's loss cannot happen); the keystroke goes to the owner. Everything else inside a held span is the loss.
    let runs_on = len.is_some() && fact(tree).open_break.is_some();
    if began && !closed.is_empty() && !runs_on {
        return Err(format!("a `break_start` inside the held span {}–{}: {said}", closed[0].started, closed[0].ended));
    }
    if len.is_none() && before.open_break.is_none() && !reach && !began {
        return Err(format!("outside every held break and widest end, no break began: {action:?} {said}"));
    }
    Ok(())
}

/// The whole invariant over one sequence, on a copy of the J day; `Err` names the step.
fn sequence(keys: &[Key]) -> Result<(), String> {
    let tmp = TempDir::new().expect("a directory");
    let tree = tmp.path().join("t");
    copy_dir(j_day(), &tree);
    for (i, k) in keys.iter().enumerate() {
        keystroke(&tree, *k).map_err(|e| format!("keystroke {i} of {keys:?}: {e}"))?;
    }
    let warm = read(&tree, false).map_err(|e| format!("{keys:?}: {e}"))?;
    the_day_is_one_reading(&warm).map_err(|e| format!("{keys:?}: {e}"))?;
    let cold = read(&tree, true).map_err(|e| format!("{keys:?}: {e}"))?;
    if cold != warm {
        return Err(format!("{keys:?}: warm {warm:?}, cold {cold:?}"));
    }
    Ok(())
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
    ]
}

/// **Every shape of the brief holds the invariant** — and this row is what fails on 213e827's binary (`TM_SWEEP_BIN`), by A's
/// shape: the review says 98 and the plan draws 88.
#[test]
fn the_briefs_shapes_hold_the_invariant() {
    for (name, keys) in shapes() {
        if let Err(e) = sequence(&keys) {
            panic!("{name}: {e}");
        }
    }
}

/// **Every minute of the morning, against every shape** — no length and five minutes typed last. Run at acceptance
/// (`--ignored`; about a minute per thread-core): the result is quoted in README gap 6040.
#[test]
#[ignore = "exhaustive: run at acceptance"]
fn every_minute_against_every_shape_holds_the_invariant() {
    let shapes = shapes();
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get().min(12));
    let mut jobs: Vec<Vec<Key>> = vec![];
    for (_, keys) in &shapes {
        for minute in m(9, 0)..=m(11, 30) {
            for len in [None, Some(5)] {
                let mut k = keys.clone();
                k.push((minute, len));
                jobs.push(k);
            }
        }
    }
    let total = jobs.len();
    let chunks: Vec<Vec<Vec<Key>>> = (0..threads).map(|i| jobs.iter().skip(i).step_by(threads).cloned().collect()).collect();
    let bad: Vec<String> = std::thread::scope(|s| {
        let hs: Vec<_> = chunks
            .iter()
            .map(|c| s.spawn(move || c.iter().filter_map(|k| sequence(k).err()).collect::<Vec<_>>()))
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
        1 => Just(Some(30u32)),
    ];
    (at, len)
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("TM_PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(64),
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
}
