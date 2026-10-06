//! **`tm break --where` names a place of the ONE table, or is refused by
//! name** — the campaign's D81 call on README gap 3903, parity P75, stage 6
//! W-41 track T, in D20's shape (`cli_break_args.rs`: the arguments are read
//! in both arms).
//!
//! `tm break 20m --where hammock` exited 0 and stored the word, while the
//! planner's request refuses any word but the four (`PlanWire.placeOf?`,
//! `badBreak place`) — so after R3 a typo in `--where` would stop `tm plan`.
//! The four live in ONE table, which the TUI's `b` then `w`/`s`/`b`/`p` reads
//! too; fork 4748911 kept them in the TUI alone and `tm break` stored any word.
//! **Since the owner's D111 (README gap 4904, parity P108) the table is the
//! KERNEL's** — `Log.placeWords`, which the log's grammar reads a `break_start`'s
//! place through — and the host reads it off the request's `places` key
//! (`kernel_log::places`); until then it was the host's own
//! (tm_core::store::BREAK_PLACES, deleted), held to the kernel's by this file.

mod cli_common;

#[allow(dead_code)]
#[path = "support/replay.rs"]
mod chokepoint;

use cli_common::Tm;

/// The kernel's table of places, through the binary's own reader of it.
fn table() -> Vec<String> {
    chokepoint::kernel_places()
}

const AT: &str = "2026-09-08T10:00:00-05:00";

fn woken() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-08T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm
}

/// **An unknown place is refused by name, in both arms, and writes nothing**;
/// `--json` carries the same sentence.
#[test]
fn an_unknown_place_is_refused_in_both_arms() {
    let tm = woken();
    let log = tm.read(".tm/log.jsonl");
    let out = tm.run_at(AT, &["break", "20m", "--where", "hammock"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(
        out.stderr.trim(),
        "tm: unknown break place \"hammock\" — `--where` is one of walk, seat, bed, phone (§12.6)"
    );
    assert!(tm.state()["break"].is_null(), "no break began: {}", tm.state());
    assert_eq!(tm.read(".tm/log.jsonl"), log);
    let out = tm.run_at(AT, &["--json", "break", "--where", "Walk"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    let doc: serde_json::Value = serde_json::from_str(&out.stderr).expect("a JSON error document");
    assert!(doc["message"].as_str().is_some_and(|m| m.contains("unknown break place \"Walk\"")), "{doc}");

    // The running arm reads `--where` too (D20): refused, the break untouched.
    tm.ok_at(AT, &["break", "20m", "--where", "walk"]);
    let out = tm.run_at("2026-09-08T10:05:00-05:00", &["break", "--where", "hammock"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert_eq!(tm.state()["break"]["where"], "walk", "{}", tm.state());
    assert_eq!(tm.state()["break"]["started"], "10:00", "{}", tm.state());
}

/// **Every word of the table is taken, and is what the break carries** — into
/// `.tm/state.json` and onto the `break` line it logs when it ends.
#[test]
fn every_place_of_the_table_is_taken() {
    for place in table() {
        let tm = woken();
        tm.ok_at(AT, &["break", "20m", "--where", &place]);
        assert_eq!(tm.state()["break"]["where"], place.as_str());
        tm.ok_at("2026-09-08T10:20:00-05:00", &["break"]);
        assert_eq!(tm.last()["where"], place.as_str(), "{}", tm.last());
    }
}

/// **`tm break --help` lists the table's words** — the one place the four are
/// written again, as prose, held to the table here.
#[test]
fn the_help_lists_the_tables_words() {
    let tm = Tm::new();
    let out = tm.run(&["break", "--help"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    let line = out
        .stdout
        .lines()
        .find(|l| l.contains("--where"))
        .unwrap_or_else(|| panic!("no --where in {}", out.stdout));
    let help = out.stdout.split(line).nth(1).unwrap_or_default().lines().next().unwrap_or_default();
    let listed = format!("{line} {help}");
    for place in table() {
        assert!(listed.contains(place.as_str()), "{place} missing from {listed:?}");
    }
    assert!(listed.contains(&table().join(", ")), "{listed:?}");
}

/// **Every word of the table is a word the kernel's planner reads** — the claim
/// the host's table (`tm_core::store::BreakPlace` until D111) made ("a word the
/// verb wrote is a word the planner reads"), held by nothing until the W-41
/// repair (README gap 4145), and since D111 one table on both sides. `tm check` asks the kernel for the day R3's `tm plan` sends
/// (`kernel_capacity::planner_request`, P78), whose `planner.state.break.place`
/// is the cache's word: for each of the table's words, with the break running,
/// the day is planned (`no problems`). And it bites: a break the log holds no
/// `break_start` for (one a binary before the owner's D105 began, which the cache
/// alone holds), hand-edited to a word outside the table, is named `badBreak place`
/// at exit 2. **Since the W-46 audit (README gap 4903) a cache hand-edit does not
/// reach the planner while the log holds the break's `break_start`**: the log
/// decides the running break both ways (D42, D105), so the same edit over D105's
/// line plans the log's word, `no problems` — the second arm below.
#[test]
fn every_place_of_the_table_is_one_the_planner_reads() {
    let at = "2026-09-08T10:05:00-05:00";
    for place in table() {
        let tm = woken();
        tm.ok_at(AT, &["break", "20m", "--where", &place]);
        let out = tm.run_at(at, &["check"]);
        assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "`{place}`: {}{}", out.stdout, out.stderr);
    }
    let hand_edited = |keep_the_logged_start: bool| {
        let tm = woken();
        tm.ok_at(AT, &["break", "20m", "--where", "walk"]);
        if !keep_the_logged_start {
            let log = tm.plan.join(".tm/log.jsonl");
            let text = std::fs::read_to_string(&log).expect("log");
            let kept: String = text.lines().filter(|l| !l.contains("\"break_start\"")).map(|l| format!("{l}\n")).collect();
            std::fs::write(&log, kept).expect("the log a binary before D105 wrote");
        }
        let path = tm.plan.join(".tm/state.json");
        let mut state: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&path).expect("state")).expect("JSON");
        state["break"]["where"] = serde_json::Value::from("hammock");
        std::fs::write(&path, serde_json::to_string(&state).expect("JSON")).expect("the hand edit");
        tm.run_at(at, &["check"])
    };
    let out = hand_edited(false);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);
    assert!(out.stdout.contains("error[planner-refusal]: kernel refusal: badBreak place"), "{}", out.stdout);
    let out = hand_edited(true);
    assert_eq!((out.code, out.stdout.trim()), (0, "no problems"), "the log's word decides: {}{}", out.stdout, out.stderr);
}

/// **The table is the kernel's, word for word** (the owner's D111): what the
/// request's `places` key answers is `Log.placeWords` — §12.6's four, in the
/// TUI's order — and `tm break --where` takes exactly those.
#[test]
fn the_table_is_the_kernels() {
    assert_eq!(table(), vec!["walk", "seat", "bed", "phone"]);
}

/// **D111 driven: a hand-edited `break_start` place is a MALFORMED line, and the
/// day is planned** (README gap 4904, parity P108). `tm break --where walk`
/// logs the break's start; the log line hand-edited to `"where":"moon"` is no
/// word of the table, so the kernel's grammar names the line malformed — D18's
/// warning in `tm check`, at the line — and its replay holds no running break
/// for it, as fork 4748911 reads a line it does not know. Until D111 the grammar
/// read the word, the replay held the break, and the planner's request refused
/// it: `tm plan` exited on `badBreak place`.
#[test]
fn a_hand_edited_logged_place_is_a_malformed_line_and_the_day_plans() {
    let tm = woken();
    tm.ok_at(AT, &["break", "20m", "--where", "walk"]);
    let log = tm.plan.join(".tm/log.jsonl");
    let text = std::fs::read_to_string(&log).expect("log");
    let (n, line) = text
        .lines()
        .enumerate()
        .find(|(_, l)| l.contains("\"break_start\""))
        .expect("tm break logged its start");
    assert!(line.contains("\"where\":\"walk\""), "{line}");
    let edited: String = text
        .lines()
        .map(|l| if l.contains("\"break_start\"") { l.replace("\"where\":\"walk\"", "\"where\":\"moon\"") } else { l.to_string() })
        .map(|l| format!("{l}\n"))
        .collect();
    std::fs::write(&log, edited).expect("the hand edit");
    let at = "2026-09-08T10:05:00-05:00";
    let plan = tm.run_at(at, &["plan"]);
    assert_eq!(plan.code, 0, "the day is planned: {}{}", plan.stdout, plan.stderr);
    assert!(!plan.stderr.contains("badBreak"), "{}", plan.stderr);
    let check = tm.run_at(at, &["--json", "check"]);
    let doc: serde_json::Value = serde_json::from_str(&check.stdout).expect("tm check --json");
    let named: Vec<&serde_json::Value> = doc["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .filter(|p| p["file"] == ".tm/log.jsonl" && p["line"].as_u64() == Some(n as u64 + 1))
        .collect();
    assert_eq!(named.len(), 1, "the malformed line is named once: {doc}");
    assert_eq!(named[0]["severity"], "warning", "D18: a warning, never an error: {doc}");
    // The kernel's own name for the warning (`badField`, on the `break_start` line it quotes);
    // the host's text quotes the line's first 72 characters, so the word itself is cut.
    assert!(
        named[0]["message"].as_str().is_some_and(|m| m.contains("badField") && m.contains("break_start")),
        "{doc}"
    );
    // And the line is the only problem: the day itself is sound.
    assert_eq!(doc["problems"].as_array().map(Vec::len), Some(1), "{doc}");
    assert_eq!(doc["exit_code"], 0, "a warning leaves the exit code the tree's: {doc}");
}

/// **The export answers the table only when asked** (the owner's D111): `{"docs":[]}` is
/// answered as before W-47 — no `places` key — and `{"docs":[],"places":true}` with the
/// table beside the same `docs` and `report`. The FFI half of
/// `PlanWire.respondPlanner_without_places` and `PlanWire.respondPlanner_with_places`,
/// at the linked archive: the export answers the table only when the request asks.
#[test]
fn the_export_answers_the_table_only_when_asked() {
    let ask = |req: &str| -> serde_json::Value {
        serde_json::from_str(&tm_kernel_ffi::call(req).expect("the kernel answers")).expect("JSON")
    };
    let bare = ask(r#"{"docs":[]}"#);
    assert!(bare["ok"].is_object(), "{bare}");
    assert!(bare["ok"].get("places").is_none(), "a table nobody asked for: {bare}");
    let asked = ask(r#"{"docs":[],"places":true}"#);
    let mut rest = asked["ok"].as_object().expect("an ok object").clone();
    let words = rest.remove("places").expect("the table, when asked");
    assert_eq!(words, serde_json::json!(table()), "{asked}");
    assert_eq!(serde_json::Value::Object(rest), bare["ok"], "the rest of the answer is the request's own");
}
