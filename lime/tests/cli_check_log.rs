//! **A damaged `.tm/log.jsonl`, and what `lime check` says about it** — the
//! owner's D18 (i) and (ii), and design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §14.6's item 7 and two of
//! its nine T9 names.
//!
//! D18 answers OWNER Q9: malformed log lines and lines dated more than two
//! days after `now` are **warnings**, listed with the exit code unchanged;
//! and every verb *except* `lime check` fails by name on `reachTooFar`, which
//! makes `lime check` precisely the verb that must keep working on a damaged
//! log, because it is how the bad line is found.
//!
//! W-6's independent audit drove three damaged trees and found none of that
//! wired: a truncated line and a line of nonsense got `no problems, exit 0`;
//! a line dated 2027 went unmentioned; and **one invalid UTF-8 byte killed
//! every verb, `lime check` included**, with the raw I/O message
//! `stream did not contain valid UTF-8` naming no line at all. These tests
//! are that audit's cases, kept.
//!
//! The UTF-8 half is design §17's parity **P13** — "a log line that is not
//! UTF-8: the kernel warns per line and the verb runs; the fork's
//! `read_to_string` fails the whole command" — answered on the host side,
//! through the same single reader (`Ctx::replay_of` reads bytes and
//! `Log::parse_bytes` splits before decoding). The row's kernel column
//! reached before the switch; the switch still owes everything else.

mod cli_common;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use std::fs::OpenOptions;
use std::io::Write;

use cli_common::Lime;

/// `lime/src/cli/kernel_log.rs`'s `CHUNK_LINES`, spelled out rather than
/// imported: a CLI test drives the binary and must not pull a `lime::cli`
/// module into its own crate (`kernel_call_counts.rs` spells out
/// `LIME_TRACE_REPLAY_SCOPE` for the same reason). If the constant moves, this
/// test's own assertion that the log spans several chunks is what fails.
const CHUNK_LINES: usize = 4_096;

/// The day after the log's last dated line, as an instant: a `now` that makes
/// no line future-dated, so `lime check`'s D18 (ii) half stays quiet and the
/// line warnings are the only thing under test.
fn day_after(text: &str) -> String {
    let last = text
        .lines()
        .rev()
        .find_map(|l| {
            let v: serde_json::Value = serde_json::from_str(l).ok()?;
            chrono::DateTime::parse_from_rfc3339(v.get("t")?.as_str()?).ok()
        })
        .expect("a dated line");
    format!("{}T12:00:00-05:00", last.date_naive() + chrono::Duration::days(1))
}

/// Append raw bytes to the log, as a hand edit or a torn write would.
fn append_bytes(lime: &Lime, bytes: &[u8]) {
    let path = lime.plan.join(".tm/log.jsonl");
    let mut f = OpenOptions::new().create(true).append(true).open(&path).expect("open the log");
    f.write_all(bytes).expect("append to the log");
}

/// The log's physical line count — the line number the last appended line has.
fn log_lines(lime: &Lime) -> usize {
    let bytes = std::fs::read(lime.plan.join(".tm/log.jsonl")).unwrap_or_default();
    let newlines = bytes.iter().filter(|b| **b == b'\n').count();
    newlines + usize::from(!bytes.is_empty() && !bytes.ends_with(b"\n"))
}

/// Every problem `lime check --json` reported, as `(code, severity, file, line)`.
fn problems(lime: &Lime) -> Vec<(String, String, String, u64)> {
    problems_at(lime, cli_common::NOW)
}

/// [`problems`] at an explicit instant — the stall tests check a tree weeks
/// after the block they are about was opened.
fn problems_at(lime: &Lime, now: &str) -> Vec<(String, String, String, u64)> {
    problems_of(&lime.json_at(now, &["check"]))
}

/// The same, off a `lime check --json` document the caller already has — for the
/// D32 case, where the tree deliberately exits 2 and `Lime::json_at`'s exit-0
/// assertion would fire first.
fn problems_of(doc: &serde_json::Value) -> Vec<(String, String, String, u64)> {
    doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .map(|p| {
            (
                p["code"].as_str().unwrap_or_default().to_string(),
                p["severity"].as_str().unwrap_or_default().to_string(),
                p["file"].as_str().unwrap_or_default().to_string(),
                p["line"].as_u64().unwrap_or_default(),
            )
        })
        .collect()
}

/// A tree with a log: one `wake`, one started block.
fn with_a_log() -> Lime {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^t4", "--energy", "4"]);
    lime
}

/// [`with_a_log`] with the block on the BACKLOG's `^a1` — a block that can still stall across later days.
/// Since the owner's D130 (W-50 track C, README gap 5413) a block on a week file's item, `^t4`, is stopped by
/// the first close that takes the item (W37's, at 2026-09-14), so it holds the ledger day no longer than its
/// week; a backlog item is in no period a close takes, and its block stays open until the user ends it.
fn with_a_stalling_log() -> Lime {
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok(&["start", "^a1", "--energy", "4"]);
    lime
}

/// **The plan-file half of the same repair** — W-16 repair, **gap 579**.
///
/// D18 / gap 145 gave `.tm/log.jsonl` a per-line tolerant read, so one damaged
/// byte is a warning that names the line (the test below). The **plan files**
/// never got it, and W-16's own `lime check` kernel load made it worse: one stray
/// byte in `plan/inbox.md` and the single verb whose whole job is diagnosis
/// exited **1** with `lime: inbox.md: stream did not contain valid UTF-8` —
/// naming no line, and not even the spec's validation exit code — while
/// `lime plan` and `lime triage` reported the impossible `inbox.md:0:` (line 0 is
/// not a line; `StoreError::Parse`'s own field doc says 0 means "the whole
/// file").
///
/// The two halves are deliberately *not* the same answer: the log's bad line is
/// a **warning** because the log is append-only history and the point is to
/// keep going, and a plan file's is an **error** because the file is the plan
/// and it has been skipped whole. Both name the line.
#[test]
fn invalid_utf8_in_a_plan_file_is_an_error_lime_check_names_by_line() {
    let lime = Lime::new();
    let clean = lime.run(&["check"]);
    assert_eq!(clean.code, 0, "{}{}", clean.stdout, clean.stderr);

    let path = lime.plan.join("inbox.md");
    let mut bytes = std::fs::read(&path).expect("read inbox.md");
    let before_lines = bytes.iter().filter(|b| **b == b'\n').count();
    bytes.extend_from_slice(b"- caf\xc3\x28 broken utf8\n");
    std::fs::write(&path, &bytes).expect("write inbox.md");
    let bad_line = (before_lines + 1) as u64;

    let out = lime.run(&["check"]);
    assert_eq!(out.code, 2, "the validation exit code: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("inbox.md"), "{}", out.stdout);
    assert!(out.stdout.contains("not valid UTF-8"), "{}", out.stdout);
    assert!(
        out.stdout.contains(&format!("inbox.md:{bad_line}:")),
        "it names the line: {}",
        out.stdout
    );
    assert!(!out.stdout.contains("inbox.md:0:"), "line 0 is not a line: {}", out.stdout);

    // The other verbs still fail — a plan file that cannot be decoded is not
    // something to plan around — and **they name the same line** (W-17 repair,
    // README gap 676).
    //
    // This loop used to assert only `!contains("inbox.md:0")`, which is a check
    // no wrong position can fail: the strict readers printed
    // `inbox.md: stream did not contain valid UTF-8` with no position at all and
    // it passed for four runs. `lime check` named the line, the write gate named
    // the line, and the reading verbs named nothing — two spellings of one
    // verdict (AGENTS §5.3), one of them the W-16 repair's own gap-579
    // complaint surviving one verb over.
    for args in [vec!["plan"], vec!["triage"], vec!["now"], vec!["review", "week"]] {
        let out = lime.run(&args);
        assert_eq!(out.code, 1, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stderr.contains(&format!("inbox.md:{bad_line}:")),
            "{args:?} does not name the line: {}",
            out.stderr
        );
        // One verdict, and not `fs::read_to_string`'s third spelling.
        assert!(out.stderr.contains("not valid UTF-8"), "{args:?}: {}", out.stderr);
        assert!(
            !out.stderr.contains("stream did not contain"),
            "{args:?} still speaks io::Error's sentence: {}",
            out.stderr
        );
        assert!(!out.stderr.contains("inbox.md:0"), "{args:?}: {}", out.stderr);
    }

    // And a **host-only write** says the same thing, plus what it means for the
    // command — the gate's clause, not a different verdict.
    let write = lime.run(&["edit", "^d2", "ci=3"]);
    assert_eq!(write.code, 1, "{}{}", write.stdout, write.stderr);
    assert!(write.stderr.contains(&format!("inbox.md:{bad_line}:")), "{}", write.stderr);
    assert!(write.stderr.contains("not valid UTF-8"), "{}", write.stderr);
}

/// **The same verdict on a SWEPT tree, which is a different reader** (W-17
/// repair, README gap 676).
///
/// There are two strict readers of a plan file and the fixture above reaches
/// only one of them. On a tree with housekeeping still to do, the guarded
/// `Snapshot::read` fails first; once §6.3's automatic close has swept, the
/// verb gets as far as `FsStore::read_text`, and *that* was
/// `fs::read_to_string`'s `ErrorKind::InvalidData` — a **third** spelling,
/// `inbox.md: stream did not contain valid UTF-8`, with no position and words
/// `store::NOT_UTF8` does not use.
///
/// Reverting either reader alone leaves the other test green, which is why this
/// one exists as well as that one.
#[test]
fn a_swept_tree_names_the_bad_line_too_and_says_the_one_verdict() {
    let lime = Lime::new();
    // Two sound runs: the second finds nothing left to close, so the verbs
    // below reach the tree read rather than the guarded close write.
    lime.ok(&["plan"]);
    lime.ok(&["plan"]);

    let path = lime.plan.join("inbox.md");
    let mut bytes = std::fs::read(&path).expect("read inbox.md");
    let before_lines = bytes.iter().filter(|b| **b == b'\n').count();
    bytes.extend_from_slice(b"- caf\xc3\x28 broken utf8\n");
    std::fs::write(&path, &bytes).expect("write inbox.md");
    let bad_line = before_lines + 1;

    let check = lime.run(&["check"]);
    assert_eq!(check.code, 2, "{}{}", check.stdout, check.stderr);
    assert!(check.stdout.contains(&format!("inbox.md:{bad_line}:")), "{}", check.stdout);

    for args in [vec!["now"], vec!["plan"], vec!["review", "week"]] {
        let out = lime.run(&args);
        assert_eq!(out.code, 1, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stderr.contains(&format!("inbox.md:{bad_line}:")),
            "{args:?} does not name the line: {}",
            out.stderr
        );
        assert!(
            !out.stderr.contains("stream did not contain"),
            "{args:?} still speaks io::Error's sentence: {}",
            out.stderr
        );
        assert!(out.stderr.contains(lime_core::store::NOT_UTF8_VERDICT), "{args:?}: {}", out.stderr);
    }
}

/// **The two spellings of "these bytes are not text" are one sentence plus a
/// clause, not two verdicts** (AGENTS §5.3, W-17 repair, README gap 676).
///
/// `store::NOT_UTF8` is what `read_tree` records as a tree problem — the verdict
/// *and* what it did about it — and `store::NOT_UTF8_VERDICT` is the verdict a
/// strict reader says, which cannot honestly add "the file was skipped" because
/// the command is about to fail instead. If the pair ever drifts, this fails.
#[test]
fn the_two_not_utf8_spellings_are_one_sentence() {
    assert!(
        lime_core::store::NOT_UTF8.starts_with(lime_core::store::NOT_UTF8_VERDICT),
        "`NOT_UTF8` ({}) is no longer `NOT_UTF8_VERDICT` ({}) plus its consequence clause",
        lime_core::store::NOT_UTF8,
        lime_core::store::NOT_UTF8_VERDICT
    );
    assert_ne!(lime_core::store::NOT_UTF8, lime_core::store::NOT_UTF8_VERDICT);
}

/// **T9**: one byte of invalid UTF-8 is one warning at its own line, the exit
/// code does not move, and every verb still runs.
#[test]
fn invalid_utf8_line_is_a_warning_and_lime_check_names_it() {
    let lime = with_a_log();
    let clean = lime.run(&["check"]);
    assert_eq!(clean.code, 0, "{}{}", clean.stdout, clean.stderr);
    assert!(clean.stdout.contains("no problems"), "{}", clean.stdout);

    append_bytes(&lime, b"{\"t\":\"2026-09-07T08:30:00-05:00\",\"ev\":\"note\",\"text\":\"\xff\xfe\"}\n");
    let line = log_lines(&lime) as u64;

    // D18 (i): a warning, the exit code unchanged.
    let out = lime.run(&["check"]);
    assert_eq!(out.code, 0, "the exit code must not move: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains(".tm/log.jsonl"), "{}", out.stdout);
    assert!(out.stdout.contains("log-line"), "{}", out.stdout);
    assert!(out.stdout.contains("invalid UTF-8"), "{}", out.stdout);
    assert!(out.stdout.contains(&format!(":{line}:")), "it names the line: {}", out.stdout);
    assert!(
        problems(&lime).contains(&("log-line".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
        "{:?}",
        problems(&lime)
    );

    // And the point of the whole row: the verbs still run. Every one of these
    // exited 1 with `stream did not contain valid UTF-8` before the repair.
    // Each gets its own damaged tree, so one verb's writes cannot disturb the
    // next one's (`lime plan` rewrites the day file `lime undo` snapshotted).
    for args in [
        vec!["now"],
        vec!["log", "--tail", "3"],
        vec!["plan"],
        vec!["review", "day"],
        vec!["model"],
        vec!["undo"],
        vec!["close", "day"],
    ] {
        let lime = with_a_log();
        append_bytes(&lime, b"{\"t\":\"2026-09-07T08:30:00-05:00\",\"ev\":\"note\",\"text\":\"\xff\xfe\"}\n");
        let out = lime.run_at("2026-09-07T11:00:00-05:00", &args);
        assert_eq!(out.code, 0, "`lime {}`: {}{}", args.join(" "), out.stdout, out.stderr);
        assert!(
            !out.stderr.contains("valid UTF-8"),
            "`lime {}` still dies on the byte: {}",
            args.join(" "),
            out.stderr
        );
    }
}

/// D18 (i)'s other half: a truncated line and a line of nonsense. The audit's
/// first damaged tree, which reported `no problems`.
#[test]
fn a_malformed_line_is_a_warning_and_lime_check_names_it() {
    let lime = with_a_log();
    append_bytes(&lime, b"{\"t\":\"2026-09-07T08:40:00-05:00\",\"ev\":\"wake\"\n");
    let truncated = log_lines(&lime) as u64;
    append_bytes(&lime, b"not json at all\n");
    let nonsense = log_lines(&lime) as u64;

    let out = lime.run(&["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("no problems"), "{}", out.stdout);
    let found = problems(&lime);
    for line in [truncated, nonsense] {
        assert!(
            found.contains(&("log-line".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
            "line {line} is not named: {found:?}"
        );
    }
    // A warning is advice: `lime check`'s exit code is the tree's alone.
    assert_eq!(lime.json(&["check"])["exit_code"], 0);
}

/// **T9**: a line dated next year is named, and it changes nothing about
/// today (D18 (ii)).
#[test]
fn a_line_dated_next_year_changes_nothing_about_today_and_lime_check_names_it() {
    let lime = with_a_log();
    let before = lime.json(&["now"]);

    append_bytes(&lime, b"{\"t\":\"2027-11-30T10:00:00-05:00\",\"ev\":\"wake\",\"slept_min\":400}\n");
    let line = log_lines(&lime) as u64;

    let after = lime.json(&["now"]);
    assert_eq!(before, after, "a line dated next year changed something about today");

    let out = lime.run(&["check"]);
    assert_eq!(out.code, 0, "the exit code must not move: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("log-future"), "{}", out.stdout);
    assert!(out.stdout.contains("2027-11-30"), "{}", out.stdout);
    assert!(
        problems(&lime).contains(&("log-future".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
        "{:?}",
        problems(&lime)
    );

    // Two days after `now` is inside the fence and is not named: the rule is
    // "more than 2 days", and a `lime wake` typed for tomorrow is ordinary.
    let lime = with_a_log();
    append_bytes(&lime, b"{\"t\":\"2026-09-09T06:00:00-05:00\",\"ev\":\"wake\",\"slept_min\":400}\n");
    let codes: Vec<String> = problems(&lime).into_iter().map(|p| p.0).collect();
    assert!(!codes.contains(&"log-future".to_string()), "{codes:?}");
}

/// W-6's audit defect: `lime close <grain> --date <an older ended period>` was
/// accepted, ignored, and reported as a close of the period it really took —
/// and it appended a `close` event for a key already closed. It is now
/// refused by name, and nothing is written.
#[test]
fn a_close_date_naming_a_period_it_does_not_take_is_refused_by_name() {
    // Tuesday 2026-09-15: the last ended day is 2026-09-14, week 2026-W37,
    // month 2026-08.
    const NOW: &str = "2026-09-15T09:00:00-05:00";
    for (grain, date, takes) in [
        ("day", "2026-08-26", "2026-09-14"),
        ("week", "2026-W25", "2026-W37"),
        ("month", "2026-07", "2026-08"),
    ] {
        let lime = Lime::new();
        let out = lime.run_at(NOW, &["close", grain, "--date", date]);
        assert_eq!(out.code, 1, "`lime close {grain} --date {date}`: {}{}", out.stdout, out.stderr);
        assert!(out.stderr.contains("periodNotTaken"), "{}", out.stderr);
        assert!(out.stderr.contains(takes), "it does not name what it takes: {}", out.stderr);
        assert!(!out.stdout.contains("closed"), "it said it closed something: {}", out.stdout);
        assert!(
            !lime.events().contains(&"close".to_string()),
            "a refused close appended a close event: {:?}",
            lime.events()
        );
    }
}

/// The `--date` help says `2026-09-13`, `2026-W37` or `2026-08`, and a
/// calendar date names the period containing it. Before the repair
/// `lime review week --date 2026-06-15` — the spelling the old `<DATE>` help
/// invited — came back `invalid iso-week` and left the ISO-week form to be
/// guessed from the error message.
#[test]
fn review_reads_a_calendar_date_for_a_week_or_a_month() {
    let lime = Lime::new();
    const NOW: &str = "2026-09-15T09:00:00-05:00";

    let by_key = lime.json_at(NOW, &["review", "week", "--date", "2026-W25"]);
    let by_date = lime.json_at(NOW, &["review", "week", "--date", "2026-06-15"]);
    assert_eq!(by_key["key"], "2026-W25");
    assert_eq!(by_date, by_key, "a Monday of W25 must review W25");
    let sunday = lime.json_at(NOW, &["review", "week", "--date", "2026-06-21"]);
    assert_eq!(sunday, by_key, "a Sunday of W25 must review W25");

    let m_key = lime.json_at(NOW, &["review", "month", "--date", "2026-07"]);
    let m_date = lime.json_at(NOW, &["review", "month", "--date", "2026-07-15"]);
    assert_eq!(m_key["key"], "2026-07");
    assert_eq!(m_date, m_key);

    // A value that is neither still fails by the period parser's own name.
    let bad = lime.run_at(NOW, &["review", "week", "--date", "garbage"]);
    assert_eq!(bad.code, 1, "{}{}", bad.stdout, bad.stderr);
    assert!(bad.stderr.contains("iso-week"), "{}", bad.stderr);

    // And the help no longer promises what the parser refuses.
    let help = lime.run(&["review", "--help"]);
    assert!(help.stdout.contains("2026-W37"), "{}", help.stdout);
}

/// **Gap 134**: `lime check` names every unreadable line of a log long enough to
/// span several genesis chunks — including one in the **first** chunk.
///
/// The kernel's `log` answer carries a `warnings` array that is **per call**
/// (`Boundary.logBody` over `logVerdicts`), and `kernel_log::genesis` returns
/// only its **last chunk's** answer. A `lime check` wired to that array would
/// name the final chunk's lines and silently drop every earlier one — at every
/// scope, `All` included. The verb asks the kernel for the lines directly
/// instead (`kernel_log::line_warnings`, a read-only sweep of the whole file
/// in chunks), which is what this test pins: the damage is put in the first
/// chunk, the middle and the last, and all three must be named.
///
/// Before the wiring this test could not fail for the right reason — the
/// in-tree Rust reader reads the whole file in one pass — so its value is that
/// it fails the moment the sweep is replaced by an answer's array.
#[test]
fn lime_check_names_an_unreadable_line_in_every_chunk_of_a_multi_chunk_log() {
    let lime = Lime::new();
    let mut lines = loggen::log(loggen::Rate::SixtyOne, 200);
    assert!(
        lines.len() > 2 * CHUNK_LINES,
        "the log must span more than two chunks, else this test proves nothing: {} lines",
        lines.len()
    );
    // One in the first chunk, one in the middle, one in the last.
    let (early, middle, late) = (10, CHUNK_LINES + 500, lines.len() - 3);
    for i in [early, middle, late] {
        lines[i] = "not json at all".to_string();
    }
    let text = loggen::text(&lines);
    // `plan-basic` has no `.tm/` until a verb writes one; this log is written
    // straight in, so the damaged lines keep the numbering the test asserts.
    std::fs::create_dir_all(lime.plan.join(".tm")).expect("mkdir .tm");
    std::fs::write(lime.plan.join(".tm/log.jsonl"), &text).expect("write the log");
    let now = day_after(&text);

    let out = lime.run_at(&now, &["check"]);
    assert_eq!(out.code, 0, "a damaged log must not move the exit code: {}{}", out.stdout, out.stderr);

    let doc = lime.json_at(&now, &["check"]);
    let named: Vec<u64> = doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .filter(|p| p["code"] == "log-line" && p["file"] == ".tm/log.jsonl")
        .map(|p| p["line"].as_u64().expect("a line"))
        .collect();
    assert_eq!(
        named,
        vec![early as u64 + 1, middle as u64 + 1, late as u64 + 1],
        "every damaged line is named, whichever chunk it fell in"
    );
    eprintln!(
        "lime check swept {} lines / {} bytes over {} chunks and named {} lines",
        lines.len(),
        text.len(),
        lines.len().div_ceil(CHUNK_LINES),
        named.len()
    );
}

/// **Gap 119 / design §9.4's "Stalls", §18.7 and design gap 88** — a block
/// left open holds the replay checkpoint's **ledger day** back, and until now
/// `lime check` said `no problems` about it.
///
/// Three runs before the switch found this unreachable and said so honestly:
/// the ledger day is a fact of the kernel's checkpoint, and no verb read one.
/// S made it reachable, so this is the test that can finally fail.
///
/// **Both directions, because the obvious check is a trapdoor** (§5.8). The
/// natural rule — "the ledger day is more than seven days behind `now`" — is
/// true of trees with nothing wrong with them: §9.4 folds only up to
/// `min(T, M) - keepDays`, so `L` trails the log's own last activity, and the
/// **control tree below runs about twelve days behind while perfectly
/// healthy**. It is the open block that must be named, with its age. So this
/// asserts the warning bites on a stall *and* stays silent on a tree that is
/// merely quiet — which is the assertion that would have caught the rule I
/// first wrote.
#[test]
fn a_stalled_ledger_day_is_named_and_a_healthy_one_is_not() {
    const LATE: &str = "2026-10-10T09:00:00-05:00";
    // Days a verb runs on between the stall and the check, so the checkpoint
    // reseals more than once and the ledger day has every chance to move on.
    const BETWEEN: &[&str] = &["2026-09-12", "2026-09-21", "2026-09-30"];

    // (1) The stall: `with_a_stalling_log` starts a block on ^a1 and nothing closes it.
    let lime = with_a_stalling_log();
    for day in BETWEEN {
        lime.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let start_line = lime.log().iter().position(|e| e["ev"] == "start").expect("a `start`") as u64 + 1;

    let out = lime.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "a stall is a warning, not an error: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("log-stall"), "the stall is not named: {}", out.stdout);
    assert!(out.stdout.contains("^a1"), "the stall does not name the block: {}", out.stdout);
    // The consequence §9.4 names, not just the cause.
    assert!(out.stdout.contains("ledger day"), "the stall does not name what it holds: {}", out.stdout);
    let found = problems_at(&lime, LATE);
    assert!(
        found.contains(&("log-stall".into(), "warning".into(), ".tm/log.jsonl".into(), start_line)),
        "the stall is not at the `start`'s own line {start_line}: {found:?}"
    );
    // D18's rule for the whole family: the exit code is the tree's alone.
    assert_eq!(lime.json_at(LATE, &["check"])["exit_code"], 0);

    // (2) The control: the same tree, the same days, the block **closed**. Its
    // ledger day still trails `now` by far more than the seven-day bound, so a
    // lag test would name it. Nothing is wrong with it and nothing is said.
    let lime = with_a_stalling_log();
    lime.ok_at("2026-09-07T10:05:00-05:00", &["done", "--went", "1"]);
    for day in BETWEEN {
        lime.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let out = lime.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        !out.stdout.contains("log-stall"),
        "a tree whose block was closed was named as stalled: {}",
        out.stdout
    );
}

/// **The bound is `> 7` days, and it is asserted on both sides of itself**
/// (`check::LOG_STALL_DAYS`; design §9.4's "a stall longer than 7 days").
///
/// A block open for exactly seven days is not a stall; one open for eight is.
/// Without this, `>=` and `>` both pass the test above, and the sentence the
/// design wrote would not be the sentence the code means.
#[test]
fn a_block_open_exactly_seven_days_is_not_yet_a_stall() {
    // `with_a_log` starts its block on 2026-09-07 (`cli_common::NOW`).
    let seven = "2026-09-14T09:00:00-05:00";
    let eight = "2026-09-15T09:00:00-05:00";

    let lime = with_a_log();
    let out = lime.run_at(seven, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        !out.stdout.contains("log-stall"),
        "a block open exactly 7 days was named a stall: {}",
        out.stdout
    );

    let lime = with_a_log();
    let out = lime.run_at(eight, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("log-stall"),
        "a block open 8 days was not named a stall: {}",
        out.stdout
    );
    assert!(out.stdout.contains("^t4"), "{}", out.stdout);
}

/// **The second stall cause design §9.4 names**: "an open block holding an
/// observation, a `stop` never followed by a `start`, or an **open
/// interruption** holds `L'` back."
///
/// `lime interrupt` leaves both at once — the block is still open and the
/// interruption sits on top of it — and both really do hold the ledger day,
/// so both are named, each at its own line with the verb that clears it. This
/// exists because an arm that is built and never exercised is the shape §9.2
/// calls a disguised gap: it would have passed review and named nothing.
#[test]
fn an_interruption_never_resumed_is_named_beside_its_block() {
    const LATE: &str = "2026-10-10T09:00:00-05:00";
    let lime = with_a_stalling_log();
    lime.ok_at("2026-09-07T09:30:00-05:00", &["interrupt"]);
    for day in ["2026-09-12", "2026-09-21", "2026-09-30"] {
        lime.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let line_of = |ev: &str| {
        lime.log().iter().position(|e| e["ev"] == ev).unwrap_or_else(|| panic!("a `{ev}`")) as u64 + 1
    };

    let out = lime.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    let stalls: Vec<_> = problems_at(&lime, LATE).into_iter().filter(|p| p.0 == "log-stall").collect();
    assert_eq!(stalls.len(), 2, "both stalls should be named, got {stalls:?}");
    for ev in ["start", "interrupt"] {
        let line = line_of(ev);
        assert!(
            stalls.contains(&("log-stall".into(), "warning".into(), ".tm/log.jsonl".into(), line)),
            "the `{ev}` at line {line} is not named: {stalls:?}"
        );
    }
    // Each names the verb that actually clears it — the point of naming them
    // separately rather than as one "something is open".
    assert!(out.stdout.contains("an interruption of ^a1"), "{}", out.stdout);
    assert!(out.stdout.contains("`lime resume`"), "{}", out.stdout);
    assert!(out.stdout.contains("`lime done`"), "{}", out.stdout);
}

/// **The third stall cause, since the owner's D105** (parity P100): a break `lime break` began and
/// nothing ended holds the ledger day as an open interruption does — the `break` line that ends
/// it is stamped at its start, so its day is one the machine can still write (`Seal.machineDays`)
/// — and `lime check` names it at its `break_start`'s own line, with the verb that ends it. Both
/// directions, as for the other two causes: the same days with the break ENDED name nothing.
#[test]
fn a_break_never_ended_is_named_as_a_stall_and_an_ended_one_is_not() {
    const LATE: &str = "2026-10-10T09:00:00-05:00";
    const BETWEEN: &[&str] = &["2026-09-12", "2026-09-21", "2026-09-30"];

    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok_at("2026-09-07T10:00:00-05:00", &["break", "20m", "--where", "walk"]);
    for day in BETWEEN {
        lime.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let line = lime.log().iter().position(|e| e["ev"] == "break_start").expect("a `break_start` (D105)") as u64 + 1;
    let out = lime.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "a stall is a warning, not an error: {}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("a break has been running since 2026-09-07 10:00"), "the break is not named: {}", out.stdout);
    assert!(out.stdout.contains("`lime break`"), "the stall does not name the verb that ends it: {}", out.stdout);
    let stalls: Vec<_> = problems_at(&lime, LATE).into_iter().filter(|p| p.0 == "log-stall").collect();
    assert_eq!(
        stalls,
        vec![("log-stall".to_string(), "warning".to_string(), ".tm/log.jsonl".to_string(), line)],
        "the stall is not at the `break_start`'s own line {line}"
    );

    // The control: the break ended twenty minutes in, the same days after.
    let lime = Lime::new();
    lime.ok(&["wake", "06:05", "--slept", "8h10m"]);
    lime.ok_at("2026-09-07T10:00:00-05:00", &["break", "20m", "--where", "walk"]);
    lime.ok_at("2026-09-07T10:20:00-05:00", &["break"]);
    for day in BETWEEN {
        lime.ok_at(&format!("{day}T09:00:00-05:00"), &["now"]);
    }
    let out = lime.run_at(LATE, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("log-stall"), "an ended break was named as stalled: {}", out.stdout);
}

/// **D18 survives D32**: the one verb that loads tolerantly still does.
///
/// D32 (gap 476) gave `lime check` sight of a kernel **load** refusal, and gap
/// 145's whole point is that `lime check` must keep working on a log no rebuild
/// can window — it is how the bad line is found. The two do not collide,
/// because the request `lime check` now sends carries **no `log` section**:
/// `{"docs":…,"cmds":[]}`, the corpus round trip's own shape.
///
/// So, on one tree with both faults at once: the log's bad line is still a
/// **warning** naming its line, the tree's collision is an **error** naming
/// both of its lines, and the exit code is 2 because of the second and never
/// because of the first — which is exactly D18's requirement that a damaged
/// log move no exit code.
#[test]
fn a_damaged_log_stays_a_warning_while_a_refused_tree_is_an_error() {
    let lime = with_a_log();
    append_bytes(&lime, b"this is not json at all\n");
    let bad_line = log_lines(&lime) as u64;
    let now = day_after(
        &std::fs::read_to_string(lime.plan.join(".tm/log.jsonl")).expect("read the log"),
    );

    // The log alone: warning, exit 0 — gap 145, unchanged.
    let out = lime.run_at(&now, &["check"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        problems_at(&lime, &now).contains(&(
            "log-line".into(),
            "warning".into(),
            ".tm/log.jsonl".into(),
            bad_line
        )),
        "{:?}",
        problems_at(&lime, &now)
    );
    let json_of = |out: &cli_common::Out| -> serde_json::Value {
        serde_json::from_str(&out.stdout).expect("check --json is JSON")
    };

    // …and now a tree the kernel refuses as well.
    let path = lime.plan.join("routines.md");
    let text = std::fs::read_to_string(&path).expect("read routines");
    let first = text.lines().next().expect("a routine line").to_string();
    std::fs::write(&path, format!("{text}{first}\n")).expect("write routines");

    let out = lime.run_at(&now, &["check"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    let ps = problems_of(&json_of(&lime.run_at(&now, &["--json", "check"])));
    // The log line is still named, still a warning.
    assert!(
        ps.contains(&("log-line".into(), "warning".into(), ".tm/log.jsonl".into(), bad_line)),
        "the damaged log stopped being named: {ps:?}"
    );
    // The tree's collision is an error, at both of its lines.
    let n = text.lines().count() as u64;
    for line in [1, n + 1] {
        assert!(
            ps.contains(&("kernel-load".into(), "error".into(), "routines.md".into(), line)),
            "routines.md:{line} is not named: {ps:?}"
        );
    }
}
