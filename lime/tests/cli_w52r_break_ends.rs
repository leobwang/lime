//! **D141 for every break D129 ended, through the binary** (stage 6 W-52 repair track R, README gaps 5711-5714 and
//! 5730; parity **P137** restated to its reach, and **P139** — the campaign's call — for the refusal below).
//!
//! The verb's gate (`Ctx::break_a_start_ended_at`) and its D129 notice read ONE fact, the kernel's `open.ended`
//! (`Replay.endable`, `Replay.d141_reads_iff_endable`): the breaks a `break` line would end now, each with the end
//! D129 gave it. Until the repair the gate read a `BreakRecord`'s span and the log's rows, and the replay read only the
//! newest ending and forgot it at the next `break_start` — so on the critic's scenario C and the auditor's J2 the verb
//! said "ends here" and nothing moved.
//!
//! **Since the owner's D143** (stage 6 W-53 track H, parity P140) every late break below that a later `start` ends is
//! typed with NO length: typed with one (`tm break --now 09:30 10m`, as these rows read until W-53), it is logged
//! finished at once and is no break D129 ended. Each changed line is named in README "Stage 6 — W-53 track H"; the
//! readings asserted are unchanged, D129's ending being the span to the later start whatever was planned.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

const TUE: &str = "2026-09-08";

fn at(hm: &str) -> String {
    format!("{TUE}T{hm}:00-05:00")
}

/// The example tree, woken 07:00, home 08:00, `^t1` 09:00–10:00 and `^t4` 10:10–11:10 done (the J drive's day).
fn j_tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    tm.ok_at(&at("10:00"), &["done"]);
    tm.ok_at(&at("10:10"), &["start", "^t4"]);
    tm.ok_at(&at("11:10"), &["done"]);
    tm
}

/// `tm review day`'s block minutes and each break's minutes, at 12:30.
fn review(tm: &Tm) -> (u64, Vec<u64>) {
    let v = tm.json_at(&at("12:30"), &["review", "day"]);
    let r = &v["review"];
    let breaks = r["breaks"]["breaks"]
        .as_array()
        .unwrap_or_else(|| panic!("{v}"))
        .iter()
        .map(|b| b["actual_min"].as_u64().unwrap_or_default())
        .collect();
    (r["block_min"].as_u64().unwrap_or_else(|| panic!("{v}")), breaks)
}

fn breaks(tm: &Tm) -> Vec<Value> {
    tm.log().into_iter().filter(|e| e["ev"] == "break" || e["ev"] == "break_start").collect()
}

/// **The critic's scenario C, both orders** (gap 5711): three blocks, two breaks D129 ended at two later starts, then a
/// `tm break` inside each. Every one ends its break there — 140 block minutes and two ten-minute breaks, whichever is
/// typed first. On 413f769's binary the older-first order read 90 with records `[40, 50, 0]` and the newer-first 120
/// with `[40, 10, 0]`: the replay reached only the newest ending, while the verb said "ends here" for both.
#[test]
fn every_break_d129_ended_is_ended_where_typed_in_either_order_p137() {
    for first_new in [false, true] {
        let tm = j_tree();
        tm.ok_at(&at("11:20"), &["start", "^t5"]);
        tm.ok_at(&at("12:00"), &["done"]);
        tm.ok_at(&at("09:30"), &["break"]);
        tm.ok_at(&at("10:30"), &["break"]);
        assert_eq!(review(&tm), (90, vec![40, 50]), "the two endings (D129)");
        let order = if first_new { ["10:40", "09:40"] } else { ["09:40", "10:40"] };
        for hm in order {
            let out = tm.ok_at(&at(hm), &["break"]);
            assert!(out.stderr.contains("(D141)"), "{hm}: {}", out.stderr);
        }
        let (bm, mut b) = review(&tm);
        b.sort();
        assert_eq!((bm, b), (140, vec![10, 10]), "new-first {first_new}");
        let evs: Vec<_> = breaks(&tm).iter().map(|e| e["ev"].as_str().unwrap_or_default().to_string()).collect();
        assert_eq!(evs, ["break_start", "break_start", "break", "break"], "no third break_start");
    }
}

/// **The auditor's J2** (gap 5711): an ordinary break logged after the D129 ending no longer closes D141's window —
/// `tm break --now 09:40` ends the 09:30 break, `^t1` reads fifty, and the review counts the two ten-minute breaks. On
/// 413f769's binary the verb said "ends here" (`superseded_end` 10:10) and the review stayed 90 with `[40, 10]`.
#[test]
fn an_ordinary_break_in_between_does_not_close_d141_p137() {
    let tm = j_tree();
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("11:20"), &["break", "10m"]);
    tm.ok_at(&at("11:30"), &["break"]);
    assert_eq!(review(&tm), (90, vec![40, 10]));
    let v = tm.json_at(&at("09:40"), &["break"]);
    assert_eq!(v["action"], "ended", "{v}");
    assert_eq!(v["superseded_end"], "10:10", "{v}");
    let (bm, mut b) = review(&tm);
    b.sort();
    assert_eq!((bm, b), (110, vec![10, 10]));
}

/// **P139 — at the ended break's own start, `tm break` is refused by name** (the critic's B2; the campaign's call,
/// revisable by the owner). Nothing is written — the log, the day file and `.tm/state.json` are as they were — and the
/// message names the break, its start and the end D129 gave it. Until the repair the verb logged a second `break_start`
/// wholly inside the first (planned twenty), and the next `tm break` named the first while the kernel ended the second.
/// A later instant still ends it (D141).
#[test]
fn a_break_typed_at_an_ended_breaks_own_start_is_refused_p139() {
    let tm = j_tree();
    tm.ok_at(&at("09:30"), &["break"]);
    let (log0, day0, state0) = (tm.read(".tm/log.jsonl"), tm.read(&format!("day/{TUE}.md")), tm.read(".tm/state.json"));
    let out = tm.run_at(&at("09:30"), &["break"]);
    assert_ne!(out.code, 0, "refused: {}", out.stdout);
    let said = format!("{}{}", out.stdout, out.stderr);
    assert!(
        said.contains("began at 09:30") && said.contains("at 10:10") && said.contains("(D129)") && said.contains("(D141)"),
        "the refusal names the break: {said}"
    );
    assert_eq!(tm.read(".tm/log.jsonl"), log0, "nothing logged");
    assert_eq!(tm.read(&format!("day/{TUE}.md")), day0, "nothing journalled");
    assert_eq!(tm.read(".tm/state.json"), state0, "no cached break");
    let out = tm.ok_at(&at("09:40"), &["break"]);
    assert!(out.stderr.contains("(D141)"), "{}", out.stderr);
    assert_eq!(review(&tm), (110, vec![10]));
}

/// **The D129 notice prints the end D129 gave the break, from the kernel's fact** (gap 5730): after the J break is
/// ended at 09:40, a `tm break --now 09:45` begins a break that `^t4`'s 10:10 start ends, and the notice says so.
/// Restored at stage 6 W-54 repair track H to its pre-land form under the owner's **D151** (parity P148 restated):
/// a break whose end a line stated (D141 at 09:40) is not re-timed out to the end D129 inferred (10:10), so 09:45
/// begins a new break. The W-54 land had restated it under P148 to a D150 re-time out to 09:45 (`(20, 15)`, `^t1`
/// 105), which D151 withdraws; it runs again since the W-54 repair's land (track K's `wide`). The first keystroke's
/// notice and the D147 half are [`the_d129_notice_names_the_end_on_the_first_keystroke`], which runs now. Until the W-53
/// repair's land the witness was `tm break --now 09:35`, a break whose head the 09:30–09:40 break covered, so its
/// record ended at 10:05 (what 413f769's binary printed); since D147 (parity P145) that keystroke re-times the
/// finished break instead and prints no D129 notice, so no typed keystroke reaches the covered-head case.
#[test]
fn the_d129_notice_names_the_end_d129_gave_the_break() {
    let tm = j_tree();
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break"]);
    let out = tm.ok_at(&at("09:45"), &["break"]);
    assert!(out.stderr.contains("began at 09:45 ended at 10:10"), "{}", out.stderr);
    assert!(!format!("{}{}", out.stdout, out.stderr).contains("(D150)"), "{}", out.stdout);
    let tm = j_tree();
    tm.ok_at(&at("09:30"), &["break"]);
    tm.ok_at(&at("09:40"), &["break"]);
    let out = tm.ok_at(&at("09:35"), &["break"]);
    let said = format!("{}{}", out.stdout, out.stderr);
    assert!(!said.contains("(D129)") && said.contains("(D147)"), "{said}");
}

/// **The D129 notice on the first keystroke, and D147 inside the ended break** (gap 5730; split out at stage 6 W-54
/// repair track H so the notice keeps a running row while its sibling above waits on D151): `tm break --now 09:30` on
/// the J day begins a break `^t4`'s 10:10 start ends, and the notice prints that end; after `09:40` ended it (D141),
/// `--now 09:35` re-times it (D147) with no D129 notice.
#[test]
fn the_d129_notice_names_the_end_on_the_first_keystroke() {
    let tm = j_tree();
    let out = tm.ok_at(&at("09:30"), &["break"]);
    assert!(out.stderr.contains("began at 09:30 ended at 10:10"), "{}", out.stderr);
    tm.ok_at(&at("09:40"), &["break"]);
    let out = tm.ok_at(&at("09:35"), &["break"]);
    let said = format!("{}{}", out.stdout, out.stderr);
    assert!(!said.contains("(D129)") && said.contains("(D147)"), "{said}");
}
