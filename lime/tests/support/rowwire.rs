//! **The `plan` section's wire, in one place** — how a fork `DayPlan` becomes
//! the kernel's request, and how the two sides' cells are compared.
//!
//! This was `lime/tests/kernel_row_cells.rs`'s own until stage 6 **W-25 (step
//! R2)**, when `lime/tests/planner_invariants.rs` began sending **its** generated
//! days through the same wire. A copy would have made "the invariants' days go
//! through the wire `kernel_row_cells` tests" a claim about two encoders that
//! drift (AGENTS §5.3); this module makes it a fact about one.
//!
//! Nothing here asserts, and nothing here decides which differences are
//! allowed: `differences` reports every cell that differs and each caller
//! declares its own holes.
//!
//! **From the owner's D112 (W-47) until D124 (W-49 track P) this section was the
//! BINARY's door to its rows**; since D124 the planner's own answer carries them
//! (`EmitWire.dayRowsPairs`, the section's answer for the day's own request), and
//! the section is the test harness's door alone (`CLASS unsent plan`). There is
//! no Rust builder of a cell to compare with any more, so this module's jobs are
//! two: a day a test builds by HAND gets the kernel's rows for its segments
//! ([`with_kernel_cells`]), and a test can ask the door for the rows of any day
//! ([`kernel_rows`]). The decoder is the binary's own, `planwire::read_rows`; a
//! second one stood here until W-47 (AGENTS §5.3). The fork cells the Rust
//! builder wrote went with the builder, and the bytes it wrote are frozen by
//! value where a test still needs them (`lime/tests/kernel_row_cells.rs`, the
//! `emit_*` snapshots).

#[path = "../../src/cli/tz_table.rs"]
pub mod tz_table;

use chrono::Timelike;
use serde_json::{json, Value};

use lime_core::config::Config;
use lime_core::emit::RowCells;
use lime_core::dayplan::{self, DayPlan, SegKind, Segment};

/// The kernel's epoch and a `chrono` instant as its absolute second — the host
/// codec's (`lime_core::planwire`, W-35), not a copy of it. Not every crate that
/// includes this module reads both.
#[allow(unused_imports)]
pub use lime_core::planwire::{kernel_sec, EPOCH_FROM_CE};

// ---------------------------------------------------------------------------
// The request
// ---------------------------------------------------------------------------

/// An exact decimal as the wire's `{num, den}` pair.
///
/// The fork's multiplier is an `f64` and this kernel has no float (AGENTS §4),
/// so the test does the conversion the host will do at R3: six places, which is
/// `energy::fmt_multiplier`'s two with room to spare, over `10^6` — inside
/// `CapWire.maxPairDen`. An `f64` that is not a six-place decimal would be
/// rounded here, and the fixture's 1.6 is not one of those.
pub fn decimal_pair(x: f64) -> Value {
    let scaled = (x * 1_000_000.0).round() as u64;
    json!({"num": scaled, "den": 1_000_000u64})
}

/// **How a segment's note crosses the `plan` section.** The host holds a note
/// as prose (`SegFlags::note`) and the kernel's `Note` is a name with its
/// arguments, so the two directions differ:
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Notes {
    /// `null` but for a replayed pause, whose note IS a name both sides share:
    /// the kernel derives the column (`↓`, `⚠`) and prints no prose it was not
    /// told.
    Derive,
    /// A written note crosses as the kernel's free-text note (`idleAttributed`'s
    /// text, printed as written — a written note wins in the column, as it did in
    /// the fork's), a replayed pause as its name, and no note as `null`. For a
    /// day a test builds by HAND, whose notes are the prose it means to print.
    Written,
}

/// One segment, as the `plan` section carries it.
///
/// `instance` is not sent: no cell reads it (`Emit.rowOf` takes a `Seg` and
/// never looks at `inst`). `flags.ghost` is not sent either — the kernel makes
/// the ghost row a *kind* and the fork makes it a flag, and the fixture has no
/// ghost row.
pub fn seg_json(seg: &Segment, notes: Notes) -> Value {
    let mut o = json!({
        "start": kernel_sec(seg.start),
        "stop": kernel_sec(seg.end),
        "kind": dayplan::kind_label(&seg.kind),
        "energy": seg.energy,
        "item": seg.item.as_ref().map(|i| i.to_string()),
        "planned": seg.flags.planned_min,
        "flags": {
            "done": seg.flags.done,
            "current": seg.flags.current,
            "underused": seg.flags.underused,
            "hot": seg.flags.hot,
            "mandatory": seg.flags.mandatory,
            "deferred": seg.flags.deferred,
            "open": seg.flags.open,
        },
        // **Null but for one row** (see the module header): the fork's planner
        // wrote this column as prose and the kernel's `Note` is a name, so there
        // is nothing to send and the kernel derives what it can. The exception is
        // a replayed `lime pause` ([`Segment::is_pause`]), whose note IS a name the
        // two sides share (`PAUSED_NOTE`, `EmitWire.readNote`'s `paused`) and
        // which D68 draws from (`paused <dur>`, parity P59): sent null, the
        // kernel drew it `lost` and the host `paused`, an UNDECLARED `title`
        // difference waiting for the first generated day with a typed pause
        // (W-38 land step, README gap 3436).
        "note": match (&seg.flags.note, notes) {
            _ if seg.is_pause() => json!({"note": "paused"}),
            (Some(text), Notes::Written) => json!({"note": "idleAttributed", "text": text}),
            _ => Value::Null,
        },
    });
    if let SegKind::Batch(ids) = &seg.kind {
        o["batch"] = json!(ids.iter().map(|i| i.to_string()).collect::<Vec<_>>());
    }
    if let Some(m) = seg.flags.multiplier {
        o["mult"] = decimal_pair(m);
    }
    o
}

/// **The whole request**: the caller's documents, the zone, the clock, and the
/// `plan` section's rows.
///
/// `docs` is the caller's because the two callers hold their trees differently
/// — `kernel_row_cells.rs` reads the fixture off disk and
/// `planner_invariants.rs` generates its four files in memory — and **the docs
/// are the whole point**: the kernel reads the title, `ci`, estimate and parent
/// out of its own parse of these bytes, and is told none of them.
pub fn request(docs: Vec<Value>, plan: &DayPlan, cfg: &Config) -> Value {
    request_with(docs, plan, cfg, Notes::Derive)
}

/// [`request`], with the notes crossing as `notes` says.
pub fn request_with(docs: Vec<Value>, plan: &DayPlan, cfg: &Config, notes: Notes) -> Value {
    let prios: Vec<Value> = plan
        .priorities
        .iter()
        .map(|(id, p)| json!({"id": id.to_string(), "p": p.p}))
        .collect();
    json!({
        "docs": docs,
        "now": plan.date.to_string(),
        "blockMin": cfg.block_min(),
        "tz": tz_table::wire_for(None, cfg.tz),
        "plan": {
            "bed": format!("{:02}:{:02}", cfg.day.bed.hour(), cfg.day.bed.minute()),
            "priorities": prios,
            "segments": plan.segments.iter().map(|s| seg_json(s, notes)).collect::<Vec<_>>(),
            // The day's budget and window's end, as the binary sends the planner
            // answer's back (W-48 track R): the kernel answers the divider with them.
            "budgetBlocks": plan.budget_blocks,
            "windowEnd": kernel_sec(plan.window.1),
        }
    })
}

/// The kernel's rows for a day, as [`RowCells`].
pub fn kernel_cells(docs: Vec<Value>, plan: &DayPlan, cfg: &Config) -> Vec<RowCells> {
    match kernel_rows(docs, plan, cfg) {
        Ok(cells) => cells,
        Err(raw) => panic!("no plan.rows in the response:\n{raw}"),
    }
}

/// The same, with a **refusal returned rather than a panic**: the fuzz in
/// `planner_invariants.rs` asserts that no day the kernel plans is refused by
/// the wire, which it cannot do if a refusal aborts the case.
pub fn kernel_rows(docs: Vec<Value>, plan: &DayPlan, cfg: &Config) -> Result<Vec<RowCells>, String> {
    kernel_rows_with(docs, plan, cfg, Notes::Derive)
}

/// [`kernel_rows`], with the notes crossing as `notes` says. The rows are read
/// by the binary's own decoder (`planwire::read_rows`, the one there is).
pub fn kernel_rows_with(docs: Vec<Value>, plan: &DayPlan, cfg: &Config, notes: Notes) -> Result<Vec<RowCells>, String> {
    kernel_day_rows_with(docs, plan, cfg, notes).map(|(cells, _)| cells)
}

/// The rows AND the `window ends` divider the kernel answers beside them (W-48 track R,
/// README gaps 5031 and 1301), each read by the binary's own decoder (`planwire::read_rows`,
/// `planwire::read_divider`).
pub fn kernel_day_rows_with(
    docs: Vec<Value>,
    plan: &DayPlan,
    cfg: &Config,
    notes: Notes,
) -> Result<(Vec<RowCells>, Option<(usize, RowCells)>), String> {
    let req = request_with(docs, plan, cfg, notes);
    let raw = lime_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is json");
    let cells = lime_core::planwire::read_rows(&resp, &plan.segments).map_err(|e| format!("{e}: {raw}"))?;
    let divider = lime_core::planwire::read_divider(&resp, &plan.segments).map_err(|e| format!("{e}: {raw}"))?;
    Ok((cells, divider))
}

/// **A day a test built by hand, given the kernel's rows for its segments** —
/// the cells the `plan` section answers (`Emit.rowOf` over the kernel's own
/// parse of `docs`), with its written notes crossing as written. Since the
/// owner's D112 a day's rows ARE the kernel's cells and no Rust builds one, so a
/// test that prints a day it laid out itself asks the kernel for its rows, as
/// the binary does for every day it plans.
pub fn with_kernel_cells(docs: Vec<Value>, mut plan: DayPlan, cfg: &Config) -> DayPlan {
    (plan.cells, plan.divider) = match kernel_day_rows_with(docs, &plan, cfg, Notes::Written) {
        Ok(rows) => rows,
        Err(raw) => panic!("the kernel refused the rows of a hand-built day:\n{raw}"),
    };
    plan
}

/// `(cell name, fork, kernel)` for every cell of a row that differs.
///
/// The nine cells **and** `batchNames`, which is not a cell but is carried
/// beside them and would otherwise be compared only by the batch test.
pub fn differences(a: &RowCells, b: &RowCells) -> Vec<(&'static str, String, String)> {
    const NAMES: [&str; 9] = [
        "time", "ci", "p", "mark", "title", "parent", "est", "actual", "note",
    ];
    let mut out: Vec<(&'static str, String, String)> = NAMES
        .iter()
        .zip(a.cells().iter().zip(b.cells()))
        .filter(|(_, (x, y))| *x != y)
        .map(|(n, (x, y))| (*n, (*x).to_string(), y.to_string()))
        .collect();
    if a.batch_names != b.batch_names {
        out.push((
            "batchNames",
            format!("{:?}", a.batch_names),
            format!("{:?}", b.batch_names),
        ));
    }
    out
}