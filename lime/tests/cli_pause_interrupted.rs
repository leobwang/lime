//! **`lime pause` while an interruption is open is REFUSED BY NAME** — the
//! owner's D71 (README gap 3430, stage 6 W-39 track T, parity P62).
//!
//! The interruption has already stopped the timer, and `lime resume` is what
//! starts it again, so the refusal points there, the way `lime interrupt`
//! refuses a second interruption. Fork 4748911 toggled `active.paused` there
//! and logged `unpause`: one press "resumed" a block the open interruption
//! still held, and `lime now` then counted the interruption as worked.
//!
//! Every test reads what a user reads: the exit code, the words, every file
//! of the tree (the derived replay cache aside, D13), and `lime --json now`
//! with the cache and after deleting it (D42).

mod cli_common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use cli_common::Lime;
use serde_json::Value;

/// Every file under the plan directory by relative path, **except**
/// `.tm/cache/` — derived and rebuildable (D13): `Ctx::load` resumes the
/// replay checkpoint before any verb's body runs, so a verb that refused has
/// still written nothing a user typed or can lose. Bytes, not text.
fn snapshot(lime: &Lime) -> BTreeMap<String, Vec<u8>> {
    fn walk(root: &Path, dir: &Path, acc: &mut BTreeMap<String, Vec<u8>>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, acc);
            } else if let Ok(bytes) = fs::read(&path) {
                let rel = path.strip_prefix(root).expect("under root").display().to_string();
                if rel.replace('\\', "/").starts_with(".tm/cache/") {
                    continue;
                }
                acc.insert(rel, bytes);
            }
        }
    }
    let mut acc = BTreeMap::new();
    walk(&lime.plan, &lime.plan, &mut acc);
    acc
}

/// `lime --json now` at `at`, then again after `.tm/state.json` is deleted.
fn now_across_the_delete(lime: &Lime, at: &str) -> (Value, Value) {
    let with = lime.json_at(at, &["now"]);
    fs::remove_file(lime.plan.join(".tm/state.json")).expect("the cache");
    let without = lime.json_at(at, &["now"]);
    (with, without)
}

/// Woken at 06:05; then `^t4` running from 09:00 and an interruption from
/// 09:40 (`started_first`), or the interruption from 09:40 and `^t4` begun
/// inside it at 09:45 (P60's order).
fn interrupted(started_first: bool) -> Lime {
    let lime = Lime::new();
    lime.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    if started_first {
        lime.ok_at("2026-09-07T09:00:00-05:00", &["start", "^t4", "--energy", "4"]);
        lime.ok_at("2026-09-07T09:40:00-05:00", &["interrupt"]);
    } else {
        lime.ok_at("2026-09-07T09:40:00-05:00", &["interrupt"]);
        lime.ok_at("2026-09-07T09:45:00-05:00", &["start", "^t4", "--energy", "4"]);
    }
    lime
}

const REFUSAL: &str =
    "an interruption is open since 09:40 — the timer is already stopped; `lime resume` first";

/// **The drive, pinned, in both orders**: `lime pause` exits 1 with the words,
/// writes nothing — not the log, not `.tm/state.json`, not the day file's
/// journal, not the undo stack — and `lime --json now` answers the same with the
/// cache and after deleting it, the block still paused for the interruption.
#[test]
fn pause_inside_an_interruption_is_refused_by_name_and_writes_nothing() {
    for started_first in [true, false] {
        let lime = interrupted(started_first);
        let before = snapshot(&lime);
        let out = lime.run_at("2026-09-07T09:47:00-05:00", &["pause"]);
        assert_eq!(out.code, 1, "started_first {started_first}: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains(REFUSAL), "the refusal is said: {:?}", out.stderr);
        assert_eq!(snapshot(&lime), before, "started_first {started_first}: a refusal writes nothing");
        let (with, without) = now_across_the_delete(&lime, "2026-09-07T09:50:00-05:00");
        assert_eq!(with["active"]["paused"], true, "{with}");
        assert_eq!(with["active"]["id"], "t4", "{with}");
        assert_eq!(with, without, "deleting the runtime state changes nothing (D42)");
    }
}

/// **`--json` carries the same refusal** as §13's failure document — one
/// JSON document on stderr, nothing on stdout — exit code 1, and still writes
/// nothing.
#[test]
fn the_json_refusal_is_the_failure_document() {
    let lime = interrupted(true);
    let before = snapshot(&lime);
    let out = lime.run_at("2026-09-07T09:47:00-05:00", &["--json", "pause"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.is_empty(), "{:?}", out.stdout);
    let doc: Value = serde_json::from_str(&out.stderr)
        .unwrap_or_else(|e| panic!("stderr is not one JSON document ({e}): {:?}", out.stderr));
    assert_eq!(doc["ok"], false, "{doc}");
    assert_eq!(doc["exit_code"], 1, "{doc}");
    assert_eq!(doc["message"], REFUSAL, "{doc}");
    assert_eq!(snapshot(&lime), before);
}

/// **The interruption is not counted as worked.** Fork 4748911's toggle
/// logged `unpause` inside the interruption, and `lime now` then ran the
/// block's clock through it (`48m` at 09:50 for a block interrupted at
/// 09:40); refused, the clock stops at the interruption.
#[test]
fn the_interruption_is_not_counted_as_worked() {
    let lime = interrupted(true);
    let _ = lime.run_at("2026-09-07T09:42:00-05:00", &["pause"]);
    let now = lime.json_at("2026-09-07T09:50:00-05:00", &["now"]);
    assert_eq!(now["active"]["elapsed_min"], 40, "{now}");
    assert!(!lime.events().iter().any(|e| e == "unpause" || e == "pause"), "{:?}", lime.events());
}

/// **It does not over-bite** (AGENTS §5.8): after `lime resume` the timer is
/// the user's again — `lime pause` pauses and resumes it, logging each — and
/// with nothing running the old refusal stands unchanged.
#[test]
fn pause_works_again_after_resume_and_nothing_running_is_unchanged() {
    for started_first in [true, false] {
        let lime = interrupted(started_first);
        lime.ok_at("2026-09-07T09:55:00-05:00", &["resume"]);
        let a = lime.ok_at("2026-09-07T09:56:00-05:00", &["pause"]);
        assert_eq!(a.stdout.trim(), "paused ^t4", "{}", a.stdout);
        assert_eq!(lime.last_ev("pause")["id"], "t4");
        let b = lime.ok_at("2026-09-07T09:57:00-05:00", &["pause"]);
        assert_eq!(b.stdout.trim(), "resumed ^t4", "{}", b.stdout);
        assert_eq!(lime.last_ev("unpause")["id"], "t4");
    }
    let lime = Lime::new();
    lime.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    lime.ok_at("2026-09-07T09:40:00-05:00", &["interrupt"]);
    let out = lime.run_at("2026-09-07T09:42:00-05:00", &["pause"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("nothing is running"), "{}", out.stderr);
}
