//! **One definition of rank in the binary** — README gaps **4880** and **4755** (parity **P112**,
//! W-47 track H), driven through the binary.
//!
//! After R3 the kernel plans the day and serves its candidates in §8.2 step 5's walk order:
//! `diagnostics.served`, which orders two p0 IMPOSSIBLE items by their due date (P51, the owner's
//! D60) and every p0 impossible item before every other p0 item (D63). `tm review day`'s
//! "tomorrow" list — the top-ranked candidates the day did not get to — still sorted them by fork
//! 4748911's `priority::sorted`, `(p, root line, own line)`: their place in the file, a second
//! definition of rank beside the day's. It reads the served order of the day's own answer now (no
//! second request). And `tm review week`'s deadline health read its priorities from a second,
//! capacity-only request (`Ctx::priorities`, now deleted); it reads the day's request, the one every
//! planning verb sends, over the state as `tm plan`'s roll leaves it.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// `HH:MM` on Monday 2026-09-07, Chicago.
fn at(hhmm: &str) -> String {
    format!("2026-09-07T{hhmm}:00-05:00")
}

/// The example tree with two twenty-block items under `# Tasks`, both due this week, the LATER
/// one first in the file: both are p0 impossible, and with `^d1` (due Friday) they are three p0
/// impossible items whose file order and due-date order disagree.
fn three_impossible() -> Tm {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    let week = tm.read("week/2026-W37.md").replace(
        "# Tasks\n",
        "# Tasks\n\
         - [ ] 3 20b Big later                    due:2026-09-10 ^z1\n\
         - [ ] 3 20b Big sooner                   due:2026-09-08 ^z2\n",
    );
    std::fs::write(tm.plan.join("week/2026-W37.md"), week).expect("write the week");
    tm
}

/// The ids of `tm review day --json`'s "tomorrow" list.
fn tomorrow(tm: &Tm, now: &str) -> Vec<String> {
    let v = tm.json_at(now, &["review", "day"]);
    v["review"]["tomorrow"]
        .as_array()
        .unwrap_or_else(|| panic!("a tomorrow list: {v}"))
        .iter()
        .map(|t| t["id"].as_str().unwrap_or_default().to_string())
        .collect()
}

/// **Gap 4880's behaviour row**: at 21:00, past the window, none of the three is placed today, and
/// the list names them in the order the day serves them — `^z2` (due Tuesday), `^z1` (Thursday),
/// `^d1` (Friday) — where fork 4748911's key said `^d1 ^z1 ^z2`, their place in the file.
#[test]
fn tomorrow_lists_the_impossible_items_in_the_order_the_day_serves_them() {
    let tm = three_impossible();
    let classes = tm.json_at(&at("21:00"), &["plan"]);
    let impossible: Vec<&str> = classes["priorities"]
        .as_array()
        .expect("priorities")
        .iter()
        .filter(|p| p["class"] == "impossible")
        .filter_map(|p| p["id"].as_str())
        .collect();
    assert_eq!(impossible, ["d1", "z1", "z2"], "the world holds three p0 impossible items, in file order");
    assert_eq!(tomorrow(&tm, &at("21:00")), ["z2", "z1", "d1"]);
    let text = tm.ok_at(&at("21:00"), &["review", "day"]).stdout;
    assert!(
        text.contains(" tomorrow  first candidate z2 (p0 u=4.33) · z1 p0 u=2.17 · d1 p0 u=1.62"),
        "{text}"
    );
}

/// **No over-bite**: on the example tree itself, where no two p0 items tie, the list is the order
/// both keys agree on — the overdue `laundry` routine (p0), then `^m1` and `^m3` (p3) in file
/// order, the fork's own answer for this tree, unchanged.
#[test]
fn without_a_p0_tie_the_list_is_the_one_both_keys_give() {
    let tm = Tm::empty();
    assert_eq!(tm.run(&["init", "--example"]).code, 0);
    assert_eq!(tomorrow(&tm, &at("21:00")), ["laundry", "m1", "m3"]);
}

/// **Gap 4755**: `tm review week`'s deadline health counts the classes the day's own request ranks
/// — the three impossible items here, and the tightest slack among them — as `tm plan --json`'s
/// priorities at the same instant name them.
#[test]
fn the_weeks_deadline_health_reads_the_days_ranking() {
    let tm = three_impossible();
    let plan = tm.json_at(&at("10:00"), &["plan"]);
    let count = |class: &str| -> u64 {
        plan["priorities"].as_array().expect("priorities").iter().filter(|p| p["class"] == class).count() as u64
    };
    let week = tm.json_at(&at("10:00"), &["review", "week"]);
    let health: &Value = &week["review"]["deadline_health"];
    assert_eq!(health["impossible"], count("impossible"), "{health}");
    assert_eq!(health["impossible"], 3, "{health}");
    assert_eq!(health["overdue"], count("overdue"), "{health}");
    assert!(health["min_slack_days"].as_f64().is_some(), "{health}");
}
