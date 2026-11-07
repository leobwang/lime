//! **Every verb that ends a running break writes `lime break`'s journal line** — the owner's **D97**
//! (README gap 4391, parity **P95**, W-44 track H), driven through the binary for every member of
//! the class.
//!
//! The class is read off the code, not listed: a running break is ended in exactly one place
//! (`day::end_break_at`, the one function that takes `.tm/state.json`'s break and logs its line),
//! which only `end_break` and `end_break_first_at` call; the verbs reach it through
//! `end_break_first` and `end_break_first_at`, and each writes the journal line through the one
//! writer, `note_break_ended`. [`the_class_of_verbs_that_end_a_break_is_read_off_the_code`] holds
//! that shape, so a seventh verb that ends a break without saying so fails it by name.
//!
//! Fork 4748911 wrote the line from `tm break`'s ending arm alone; the owner's D90 and the W-43
//! repair gave it to `lime interrupt` and `lime resume`; `lime start`, `lime stop` and `lime done`, which
//! end a running break the same way, wrote only their own line, so the day file's journal said
//! when a break ended for three verbs of the six.

mod cli_common;

use cli_common::Lime;

const WAKE: &str = "2026-09-07T07:00:00-05:00";

/// `HH:MM` on Monday 2026-09-07, Chicago.
fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree, woken at 07:00.
fn woken() -> Lime {
    let lime = Lime::empty();
    assert_eq!(lime.run(&["init", "--example"]).code, 0);
    lime.ok_at(WAKE, &["wake", "07:00"]);
    lime
}

/// `^m1` running from 09:00 and a thirty-minute break from 09:20.
fn a_block_and_a_break() -> Lime {
    let lime = woken();
    lime.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    lime.ok_at(&at("09:20"), &["break", "30m"]);
    assert!(!lime.state()["break"].is_null(), "the break is running: {}", lime.state());
    lime
}

/// The day file's journal lines (`## Log`), as written.
fn journal(lime: &Lime) -> Vec<String> {
    lime.read("day/2026-09-07.md")
        .lines()
        .skip_while(|l| *l != "## Log")
        .skip(1)
        .take_while(|l| !l.starts_with("## "))
        .filter(|l| !l.trim().is_empty())
        .map(str::to_string)
        .collect()
}

/// The journal holds `ended` exactly once, immediately followed by a line beginning `then` — the
/// break's end, then the verb that ended it.
fn says_once_then(lime: &Lime, ended: &str, then: &str) {
    let j = journal(lime);
    let hits: Vec<usize> = j.iter().enumerate().filter(|(_, l)| l.contains("break ended")).map(|(i, _)| i).collect();
    assert_eq!(hits.len(), 1, "one `break ended` line: {j:?}");
    assert_eq!(j[hits[0]], ended, "{j:?}");
    assert!(j.get(hits[0] + 1).is_some_and(|l| l.starts_with(then)), "then `{then}`: {j:?}");
}

/// The log's `break` line: its stamp, its planned and actual minutes.
fn logged_break(lime: &Lime) -> (String, u64, u64) {
    let b = lime.last_ev("break");
    (
        b["t"].as_str().unwrap_or_default().to_string(),
        b["planned_min"].as_u64().unwrap_or(0),
        b["actual_min"].as_u64().unwrap_or(0),
    )
}

/// **`lime start` over a running break** — the behaviour row D97 names: the break's line (ten
/// minutes), then `lime break`'s journal line at 09:10, then the start's.
#[test]
fn lime_start_ends_a_running_break_and_says_so() {
    let lime = woken();
    lime.ok_at(&at("09:00"), &["break", "20m"]);
    lime.ok_at(&at("09:10"), &["start", "^m1", "--energy", "3"]);
    assert_eq!(logged_break(&lime), (at("09:00"), 20, 10));
    says_once_then(&lime, "09:10 break ended 10m/20m", "09:10 start ^m1 pred=");
    assert!(lime.state()["break"].is_null(), "{}", lime.state());
}

#[test]
fn lime_stop_ends_a_running_break_and_says_so() {
    let lime = a_block_and_a_break();
    let out = lime.ok_at(&at("09:35"), &["stop"]);
    assert!(out.stdout.contains("after 20m"), "{}", out.stdout);
    assert_eq!(logged_break(&lime), (at("09:20"), 30, 15));
    says_once_then(&lime, "09:35 break ended 15m/30m", "09:35 stop ^m1 20m · 340m left");
}

#[test]
fn lime_done_ends_a_running_break_and_says_so() {
    let lime = a_block_and_a_break();
    lime.ok_at(&at("09:35"), &["done"]);
    assert_eq!(logged_break(&lime), (at("09:20"), 30, 15));
    says_once_then(&lime, "09:35 break ended 15m/30m", "09:35 done ^m1 20m/360m");
}

/// **A stated end (the owner's D79) ends the break there**, and the journal says so at that
/// instant — `lime stop --at 09:30` at 09:35: the break's ten minutes, both lines at 09:30.
#[test]
fn a_stated_end_ends_the_break_there_and_says_so_there() {
    let lime = a_block_and_a_break();
    let out = lime.ok_at(&at("09:35"), &["stop", "--at", "09:30"]);
    assert!(out.stdout.contains("after 20m"), "{}", out.stdout);
    assert_eq!(logged_break(&lime), (at("09:20"), 30, 10));
    says_once_then(&lime, "09:30 break ended 10m/30m", "09:30 stop ^m1 20m · 340m left");

    let lime = a_block_and_a_break();
    lime.ok_at(&at("09:35"), &["done", "--at", "09:30"]);
    assert_eq!(logged_break(&lime), (at("09:20"), 30, 10));
    says_once_then(&lime, "09:30 break ended 10m/30m", "09:30 done ^m1 20m/360m");
}

/// The three verbs that already said it say it once, through the one writer (no second line).
#[test]
fn the_verbs_that_already_said_it_say_it_once() {
    let lime = a_block_and_a_break();
    lime.ok_at(&at("09:35"), &["interrupt"]);
    says_once_then(&lime, "09:35 break ended 15m/30m", "09:35 interrupt ^m1");

    let lime = woken();
    lime.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    lime.ok_at(&at("09:10"), &["interrupt"]);
    lime.ok_at(&at("09:20"), &["break", "30m"]);
    lime.ok_at(&at("09:35"), &["resume"]);
    says_once_then(&lime, "09:35 break ended 15m/30m", "09:35 resume lost=25m");

    let lime = a_block_and_a_break();
    lime.ok_at(&at("09:35"), &["break"]);
    let j = journal(&lime);
    assert_eq!(j.iter().filter(|l| l.contains("break ended")).count(), 1, "{j:?}");
    assert_eq!(j.last().map(String::as_str), Some("09:35 break ended 15m/30m"), "{j:?}");
}

/// **The terminal and `--json` say it too** — the owner's **D101** (README gap 4551, parity
/// **P102**, built at the W-46 audit's repair): `lime start`, `lime stop` and `lime done` over a running
/// break print `lime break`'s clause before their own words, as `lime interrupt` and `lime resume` do,
/// and carry `break_ended` — `lime break`'s report of the ending — in `--json`; with no break
/// running neither appears. Fork 4748911 printed and carried nothing of the break.
#[test]
fn d101_start_stop_and_done_print_and_carry_the_break_they_ended() {
    let lime = woken();
    lime.ok_at(&at("09:00"), &["break", "20m"]);
    let out = lime.ok_at(&at("09:10"), &["start", "^m1", "--energy", "3"]);
    assert!(out.stdout.starts_with("break ended · 10m of 20m · ▶ ^m1 "), "{}", out.stdout);

    let lime = a_block_and_a_break();
    let out = lime.ok_at(&at("09:35"), &["stop"]);
    assert!(out.stdout.starts_with("break ended · 15m of 30m · stopped ^m1 after 20m"), "{}", out.stdout);

    let lime = a_block_and_a_break();
    let out = lime.ok_at(&at("09:35"), &["done"]);
    assert!(out.stdout.starts_with("break ended · 15m of 30m · ✓ ^m1 "), "{}", out.stdout);

    for verb in [&["--json", "stop"][..], &["--json", "done"][..]] {
        let lime = a_block_and_a_break();
        let out = lime.ok_at(&at("09:35"), verb);
        let v: serde_json::Value = serde_json::from_str(&out.stdout).expect("JSON");
        assert_eq!(
            v["break_ended"],
            serde_json::json!({"action": "ended", "planned_min": 30, "actual_min": 15, "place": null}),
            "`lime {}`: {v}",
            verb.join(" ")
        );
    }
    let lime = woken();
    lime.ok_at(&at("09:00"), &["break", "20m"]);
    let out = lime.ok_at(&at("09:10"), &["--json", "start", "^m1", "--energy", "3"]);
    let v: serde_json::Value = serde_json::from_str(&out.stdout).expect("JSON");
    assert_eq!(v["break_ended"]["actual_min"], 10, "{v}");

    // No over-bite: no break running, no clause and no key.
    let lime = woken();
    let out = lime.ok_at(&at("09:00"), &["--json", "start", "^m1", "--energy", "3"]);
    let v: serde_json::Value = serde_json::from_str(&out.stdout).expect("JSON");
    assert!(v.get("break_ended").is_none(), "{v}");
    for verb in ["stop", "done"] {
        let lime = woken();
        lime.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
        let out = lime.ok_at(&at("09:30"), &[verb]);
        assert!(!out.stdout.contains("break ended"), "`lime {verb}`: {}", out.stdout);
    }
}

/// **No over-bite**: with no break running, none of the six writes the line.
#[test]
fn with_no_break_running_nothing_says_a_break_ended() {
    let lime = woken();
    lime.ok_at(&at("09:00"), &["start", "^m1", "--energy", "3"]);
    lime.ok_at(&at("09:10"), &["interrupt"]);
    lime.ok_at(&at("09:15"), &["resume"]);
    lime.ok_at(&at("09:30"), &["stop"]);
    lime.ok_at(&at("09:40"), &["start", "^m1", "--energy", "3"]);
    lime.ok_at(&at("09:50"), &["done"]);
    let j = journal(&lime);
    assert!(!j.iter().any(|l| l.contains("break ended")), "{j:?}");
}

/// **`lime undo` takes the journal line back with the verb**: the day file, the log's compensation
/// and the running break, as before the start.
#[test]
fn undo_takes_the_line_back_with_the_start() {
    let lime = woken();
    lime.ok_at(&at("09:00"), &["break", "20m"]);
    let before = lime.read("day/2026-09-07.md");
    lime.ok_at(&at("09:10"), &["start", "^m1", "--energy", "3"]);
    lime.ok_at(&at("09:11"), &["undo"]);
    assert_eq!(lime.read("day/2026-09-07.md"), before);
    assert!(!lime.state()["break"].is_null(), "the break runs again: {}", lime.state());
}

/// Every function of a source file, `(name, body)`, cut at its `fn` lines, `//` comments dropped.
fn bodies(text: &str) -> Vec<(String, String)> {
    let lines: Vec<&str> = text.lines().map(|l| l.find("//").map_or(l, |i| &l[..i])).collect();
    let starts: Vec<(usize, String)> = lines
        .iter()
        .enumerate()
        .filter_map(|(i, l)| {
            let t = l.trim_start();
            let rest = ["pub(crate) fn ", "pub fn ", "fn "].iter().find_map(|p| t.strip_prefix(p))?;
            Some((i, rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect()))
        })
        .collect();
    starts
        .iter()
        .enumerate()
        .map(|(n, (i, name))| {
            let end = starts.get(n + 1).map_or(lines.len(), |(j, _)| *j);
            (name.clone(), lines[*i + 1..end].join("\n"))
        })
        .collect()
}

/// **The class, read off the code** (the body shapes, not a list of verbs): over every source
/// file of the binary and of `lime-core`,
///
/// * a running break is TAKEN out of the state (`.break_.take()`) in `end_break_at` alone, and set
///   to nothing (`.break_ = None`) only where no break can be running — `lime wake`, which refuses
///   over one first (D76, D81), and D42's reconcile, which drops a cached break only where the LOG
///   already ended it and writes no line (the W-46 audit, README gap 4903) — or where a state is
///   built afresh;
/// * `end_break_at` is called by `end_break` and `end_break_first_at` alone, `end_break` by
///   `end_break_first` alone — so every verb ends a break through the two bodies;
/// * every function that calls `end_break_first` or `end_break_first_at` writes the line through
///   `note_break_ended`.
#[test]
fn the_class_of_verbs_that_end_a_break_is_read_off_the_code() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    let mut takes = Vec::new();
    let mut clears = Vec::new();
    let mut calls_at = Vec::new();
    let mut calls_now = Vec::new();
    let mut silent = Vec::new();
    let mut enders = Vec::new();
    let mut stack = vec![root.join("lime/src"), root.join("lime-core/src")];
    while let Some(dir) = stack.pop() {
        for e in std::fs::read_dir(&dir).expect("a source directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                stack.push(p);
                continue;
            }
            if p.extension().is_none_or(|x| x != "rs") {
                continue;
            }
            let rel = p.strip_prefix(&root).expect("inside").to_string_lossy().replace('\\', "/");
            let text = std::fs::read_to_string(&p).expect("a source file");
            for (name, body) in bodies(&text) {
                let here = format!("{rel}:{name}");
                if body.contains(".break_.take()") {
                    takes.push(here.clone());
                }
                if body.contains(".break_ = None") {
                    clears.push(here.clone());
                }
                if body.contains("end_break_at(") {
                    calls_at.push(here.clone());
                }
                if body.contains("end_break(") {
                    calls_now.push(here.clone());
                }
                if body.contains("end_break_first(") || body.contains("end_break_first_at(") {
                    enders.push(here.clone());
                    if !body.contains("note_break_ended(") && name != "end_break_first" {
                        silent.push(here);
                    }
                }
            }
        }
    }
    takes.sort();
    clears.sort();
    calls_at.sort();
    calls_now.sort();
    enders.sort();
    assert_eq!(takes, ["lime/src/cli/day.rs:end_break_at"], "a second place takes a running break");
    assert_eq!(
        clears,
        // `drop_break_a_start_ended` is the reconcile's own rule (a break the log ENDED, `Ctx::log_ended`) applied by
        // `lime break` to the break it has just begun, when a `start` the log already holds ends it in stamp order (the
        // owner's D129, README gap 5433, W-50 track K). `log_a_cached_break` clears a break only the cache holds whose
        // D81 instant falls before the day's logged wake — no break runs across a wake — and logs nothing for it (the
        // owner's D138, W-51 repair track H, parity P133): a break that was never the log's, so no `break` line is owed.
        [
            "lime/src/cli/ctx.rs:drop_break_a_start_ended",
            "lime/src/cli/ctx.rs:log_a_cached_break",
            "lime/src/cli/ctx.rs:reconcile_state",
            "lime/src/cli/day.rs:wake"
        ],
        "a running break set to nothing outside `lime wake`, the reconcile of a break the log ended, `lime break`'s own drop \
         of a break a logged start ended (D129), and D138's drop of a cache-only break placed before the logged wake"
    );
    assert_eq!(calls_at, ["lime/src/cli/day.rs:end_break", "lime/src/cli/day.rs:end_break_first_at"]);
    assert_eq!(calls_now, ["lime/src/cli/day.rs:end_break_first"]);
    assert!(silent.is_empty(), "a verb that ends a running break and writes no journal line: {silent:?}");
    // The six members, by name — read off the code above, and printed so a reader sees the class.
    // `lime stop`'s ending is `end_the_block` since the owner's D130 (W-50 track C, README gap 5413):
    // the one body `lime stop` runs and the stop §6.3's close writes before it takes a running item.
    let verbs: Vec<&str> = enders
        .iter()
        .map(|e| e.rsplit(':').next().unwrap_or_default())
        .filter(|n| *n != "end_break_first")
        .collect();
    assert_eq!(verbs, ["done", "end_the_block", "interrupt", "resume", "start", "take_break"], "{enders:?}");
}
