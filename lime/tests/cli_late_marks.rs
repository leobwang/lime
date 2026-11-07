//! **The late-mark decisions, through the binary** — the owner's D115, D116 and D119 (stage 6 W-48 track K, README
//! gaps 5034, 5035, 4913, 4917 and 5029). Each is a line a clock behind the log or a hand edit can write, read one way
//! by the kernel's replay and by every surface that reads it.
//!
//! * **D115** (parity P120): a `start` stamped inside a block a later `done` already closed CUTS the closed block — the
//!   later fact wins. Driven at `1a37997` (`scratchpad/w48/k/drive/d115.sh`): `start ^t1` 09:00, `done` 10:00, then
//!   `--now 09:30 start ^t4`, `stop` 10:30 — `lime review day` counted 120 block minutes inside a 90-minute span and
//!   `lime plan` drew `^t1` (60m) across `^t4`.
//! * **D116** (parity P122): the `break` line that ends a break reads its place from its `break_start`, and a different
//!   word on it is a `lime check` warning. Driven: the end line hand-edited to `moon` under a `walk` start — `lime check`
//!   said `no problems` while `lime review day` read `moon`.
//! * **D119** (parity P121): a late `interrupt` logged after a block's `done` and stamped inside it is netted from the
//!   block, as D100 nets a late break; a late mark past the replay's 31-day bound is named by `lime check`.

mod cli_common;

use cli_common::Lime;

fn at(day: &str, hm: &str) -> String {
    format!("{day}T{hm}:00-05:00")
}

const TUE: &str = "2026-09-08";
const MON: &str = "2026-09-07";

/// The example tree, woken at 07:00 and arrived home at 08:00 on `day`.
fn tree(day: &str) -> Lime {
    let lime = Lime::empty();
    lime.ok_at(&at(day, "06:00"), &["init", "--example"]);
    lime.ok_at(&at(day, "07:00"), &["wake", "07:00"]);
    lime.ok_at(&at(day, "08:00"), &["arrive", "home"]);
    lime
}

fn review_block_min(lime: &Lime, now: &str) -> u64 {
    let v = lime.json_at(now, &["review", "day"]);
    v["review"]["block_min"].as_u64().unwrap_or_else(|| panic!("block_min: {v}"))
}

/// `(code, line)` of every `lime check` problem.
fn problems(lime: &Lime, now: &str) -> Vec<(String, u64)> {
    let v = lime.json_at(now, &["check"]);
    v["problems"]
        .as_array()
        .expect("problems")
        .iter()
        .map(|p| (p["code"].as_str().unwrap_or_default().to_string(), p["line"].as_u64().unwrap_or_default()))
        .collect()
}

/// **D115, the driven reproduction**: the late `start` at 09:30 cuts `^t1` at 09:30 — thirty minutes stand of its
/// sixty, `^t4` keeps its sixty, and the review counts ninety inside the ninety-minute span.
#[test]
fn a_late_start_cuts_the_block_it_is_stamped_inside() {
    let lime = tree(TUE);
    lime.ok_at(&at(TUE, "09:00"), &["start", "^t1", "--energy", "4"]);
    lime.ok_at(&at(TUE, "10:00"), &["done"]);
    lime.ok_at(&at(TUE, "09:30"), &["start", "^t4", "--energy", "4"]);
    lime.ok_at(&at(TUE, "10:30"), &["stop"]);
    assert_eq!(review_block_min(&lime, &at(TUE, "10:31")), 90, "thirty of ^t1 and sixty of ^t4");
    let plan = lime.ok_at(&at(TUE, "10:31"), &["plan"]);
    assert!(plan.stdout.contains("(30m)"), "^t1's done row reads the thirty minutes it kept:\n{}", plan.stdout);
    assert!(!plan.stdout.contains("(60m)"), "no block keeps the span the later start took:\n{}", plan.stdout);
}

/// **D115's boundary**: a `start` after the closed block (a forward clock) cuts nothing.
#[test]
fn a_start_after_a_closed_block_cuts_nothing() {
    let lime = tree(TUE);
    lime.ok_at(&at(TUE, "09:00"), &["start", "^t1", "--energy", "4"]);
    lime.ok_at(&at(TUE, "10:00"), &["done"]);
    lime.ok_at(&at(TUE, "10:00"), &["start", "^t4", "--energy", "4"]);
    lime.ok_at(&at(TUE, "10:30"), &["stop"]);
    assert_eq!(review_block_min(&lime, &at(TUE, "10:31")), 90, "sixty of ^t1 and thirty of ^t4");
}

/// **D119, the driven reproduction**: `start ^t1` 08:00, `done` 09:00, then `--now 08:30 interrupt` and `resume`
/// 08:40 — the block is fifty, not sixty beside the interruption's ten.
#[test]
fn a_late_interruption_is_netted_from_the_block_it_crosses() {
    let lime = tree(TUE);
    lime.ok_at(&at(TUE, "08:00"), &["start", "^t1", "--energy", "4"]);
    lime.ok_at(&at(TUE, "09:00"), &["done"]);
    lime.ok_at(&at(TUE, "08:30"), &["interrupt"]);
    lime.ok_at(&at(TUE, "08:40"), &["resume"]);
    assert_eq!(review_block_min(&lime, &at(TUE, "09:30")), 50);
    assert!(problems(&lime, &at(TUE, "09:30")).is_empty(), "inside the bound, nothing is named");
}

/// **D116, the driven reproduction**: a `walk` break whose end line is hand-edited to `moon` is read at `walk` —
/// the review and the plan — and `lime check` names the end line, a warning that moves no exit code.
#[test]
fn a_break_is_read_at_its_starts_place_and_another_word_is_named() {
    let lime = tree(MON);
    lime.ok_at(&at(MON, "09:00"), &["break", "10m", "--where", "walk"]);
    lime.ok_at(&at(MON, "09:10"), &["break"]);
    let log = lime.plan.join(".tm/log.jsonl");
    let text = std::fs::read_to_string(&log).expect("the log");
    let edited = text.replace("\"ev\":\"break\",\"planned_min\":10,\"actual_min\":10,\"where\":\"walk\"",
        "\"ev\":\"break\",\"planned_min\":10,\"actual_min\":10,\"where\":\"moon\"");
    assert_ne!(edited, text, "the end line was edited");
    std::fs::write(&log, &edited).expect("write the log");
    let line = edited.lines().position(|l| l.contains("\"where\":\"moon\"")).expect("the edited line") as u64 + 1;
    assert_eq!(problems(&lime, &at(MON, "09:30")), vec![("log-break-place".to_string(), line)]);
    let review = lime.ok_at(&at(MON, "09:30"), &["review", "day"]);
    assert!(review.stdout.contains("(walk)") && !review.stdout.contains("moon"), "{}", review.stdout);
}

/// **D119's bound, named**: `^t1` worked on Tuesday, `^t4` forty days later, then a twenty-minute break stamped across
/// Tuesday's block and logged after it — past the replay's 31-day bound, so it is not netted (the bound stays) and
/// `lime check` names the break's line.
#[test]
fn a_late_mark_past_the_bound_is_named_by_lime_check() {
    let lime = tree(TUE);
    lime.ok_at(&at(TUE, "08:00"), &["start", "^t1", "--energy", "4"]);
    lime.ok_at(&at(TUE, "09:00"), &["done"]);
    let later = "2026-10-18";
    lime.ok_at(&at(later, "07:00"), &["wake", "07:00"]);
    lime.ok_at(&at(later, "08:00"), &["start", "^t4", "--energy", "4"]);
    lime.ok_at(&at(later, "09:00"), &["stop"]);
    lime.ok_at(&at(TUE, "08:30"), &["break", "20m"]);
    lime.ok_at(&at(TUE, "08:50"), &["break"]);
    let text = std::fs::read_to_string(lime.plan.join(".tm/log.jsonl")).expect("the log");
    let line = text.lines().collect::<Vec<_>>().iter().rposition(|l| l.contains("\"ev\":\"break\"")).expect("the break line") as u64 + 1;
    let found = problems(&lime, &at(later, "09:30"));
    assert!(found.contains(&("log-late-mark".to_string(), line)), "the late break is named: {found:?}");
}
