//! **The host's paused flag is the kernel's open block** — the owner's **D118** (README gap **5030**, stage 6 W-48
//! track K, parity **P114**).
//!
//! The kernel's replay reads a `pause` stamped before its block's own `start` as not the block's (D99, parity P104:
//! `Replay.arm`'s `pause` arm), and the host's worked minutes read it so too (`Replay::idle_min_since`). The host's
//! paused FLAG was a second reading — a fold of every `pause` and `unpause` of the block after its `start` row, in file
//! order (`ctx::logged_stops` until W-48) — and read it as the block's. DRIVEN at `1a37997`
//! (`scratchpad/w48/k/drive/d118.sh`, `d118.head.out`): `start ^t1` 09:00, `tm --now 08:50 pause`, and at 09:30 `tm
//! now` headed `30m of 60m · paused` while `tm plan` drew `09:00 ▶ … 30m so far` and `tm stop` at 09:40 said `after
//! 40m`; after `rm .tm/state.json` the rebuild printed `RESTORED from the log: active.paused`, and the next `tm pause`
//! said `resumed ^t1` and logged an `unpause` that idled nothing. Now every surface — `tm now`'s header, `.tm/state.json`,
//! D42's rebuild and the next `tm pause` — reads the kernel's open block.

mod cli_common;

use std::fs;

use cli_common::Tm;

fn at(hm: &str) -> String {
    format!("2026-09-08T{hm}:00-05:00")
}

fn tree() -> Tm {
    let tm = Tm::empty();
    tm.ok_at(&at("06:00"), &["init", "--example"]);
    tm.ok_at(&at("07:00"), &["wake", "07:00"]);
    tm.ok_at(&at("08:00"), &["arrive", "home"]);
    tm
}

fn cached_paused(tm: &Tm) -> bool {
    let s: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(tm.plan.join(".tm/state.json")).expect("the cache")).expect("json");
    s["active"]["paused"].as_bool().expect("active.paused")
}

fn shown(tm: &Tm, hm: &str) -> (bool, u64) {
    let v = tm.json_at(&at(hm), &["now"]);
    (v["active"]["paused"].as_bool().expect("paused"), v["active"]["elapsed_min"].as_u64().expect("elapsed_min"))
}

fn last_line(tm: &Tm) -> String {
    let log = fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("the log");
    log.lines().last().expect("a line").to_string()
}

/// **The driven reproduction, every surface**: a pause stamped ten minutes before the block began is not the block's
/// — the verb says so — and the header, the cache, the rebuild and the next `tm pause` all read the block running.
#[test]
fn a_pause_stamped_before_the_blocks_start_leaves_it_running_on_every_surface() {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    let said = tm.ok_at(&at("08:50"), &["pause"]);
    assert!(said.stdout.contains("before the block began at 09:00"), "{}", said.stdout);
    assert!(last_line(&tm).contains("\"ev\":\"pause\""), "the line is logged as typed");
    assert!(!cached_paused(&tm), "the cache takes the kernel's reading");
    assert_eq!(shown(&tm, "09:30"), (false, 30), "tm now: running, 30 worked");
    // D42: the rebuild reads the same.
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(shown(&tm, "09:31"), (false, 31));
    assert!(!cached_paused(&tm));
    // The next press toggles from the kernel's reading: it pauses.
    let said = tm.ok_at(&at("09:35"), &["pause"]);
    assert!(said.stdout.contains("paused ^t1"), "{}", said.stdout);
    assert!(last_line(&tm).contains("\"ev\":\"pause\""), "{}", last_line(&tm));
    assert!(cached_paused(&tm));
    assert_eq!(shown(&tm, "09:36"), (true, 35));
    let stop = tm.ok_at(&at("09:40"), &["stop"]);
    assert!(stop.stdout.contains("after 35m"), "{}", stop.stdout);
}

/// **A stale cache is corrected at load**: a `.tm/state.json` saying `paused` over a block the kernel reads running is
/// the log's at the next verb (D42's direction), not only after a deletion.
#[test]
fn a_cache_that_says_paused_over_a_running_block_follows_the_kernel() {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    let p = tm.plan.join(".tm/state.json");
    let mut s: serde_json::Value = serde_json::from_str(&fs::read_to_string(&p).expect("cache")).expect("json");
    s["active"]["paused"] = serde_json::Value::Bool(true);
    fs::write(&p, serde_json::to_string_pretty(&s).expect("json")).expect("write");
    assert_eq!(shown(&tm, "09:30"), (false, 30));
}

/// **The control**: a pause stamped inside the block is the block's, on every surface, before and after a rebuild.
#[test]
fn a_pause_inside_the_block_is_the_blocks() {
    let tm = tree();
    tm.ok_at(&at("09:00"), &["start", "^t1"]);
    let said = tm.ok_at(&at("09:10"), &["pause"]);
    assert!(said.stdout.contains("paused ^t1"), "{}", said.stdout);
    assert!(cached_paused(&tm));
    assert_eq!(shown(&tm, "09:30"), (true, 10));
    fs::remove_file(tm.plan.join(".tm/state.json")).expect("the cache");
    assert_eq!(shown(&tm, "09:31"), (true, 10));
    let said = tm.ok_at(&at("09:40"), &["pause"]);
    assert!(said.stdout.contains("resumed ^t1"), "{}", said.stdout);
    assert_eq!(shown(&tm, "09:50"), (false, 20));
}
