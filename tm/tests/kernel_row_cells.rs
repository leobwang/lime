//! **The kernel's cells against the bytes the Rust builder wrote** (README gaps
//! **1105** and **1318**, stage 6 W-24; restated at W-47 for the owner's
//! **D112**).
//!
//! `Emit.lean` landed at W-22 and had **no caller**. Its nineteen theorems said
//! the cells were consistent with themselves; the claim that they were the
//! *fork's* cells rested on a human having read `tm-core/src/emit.rs` beside
//! `Emit.lean`. Gap 1105 is exactly that sentence — *"the cells are proved
//! consistent with themselves and checked against the fork by reading"* — and
//! this file is the machine that stops it being true.
//!
//! # What it does since D112
//!
//! The owner's D112 made the kernel's cells the rows the binary prints (the
//! kernel answers them for every day it plans -- through the `plan` section in a
//! second call until the owner's D124, in the planner's own answer since (W-49
//! track P) -- into `DayPlan::cells`) and deleted the Rust builder
//! (`emit::row_cells` and its cell functions) these cells used to be compared
//! with. The comparison did not go with it: the builder's cells for this file's
//! days were frozen **by value** at `49186d7`, the commit before the deletion,
//! by a scratch run of `emit::row_cells` (README's W-47 track L block), and the
//! kernel's cells are held to them here — every cell, every row, **no hole**.
//!
//! * The fixture day is `tui_common`'s hand-built §4.3 timeline over the
//!   `plan-basic` tree; the kernel answers its segments through the `plan`
//!   section against its **own** parse of the same markdown, and is never told
//!   a title, a `ci`, an estimate or a parent: those four cells are the kernel's
//!   reading of one file against what the fork's parser read of it.
//! * **The two holes this file declared are closed at their cause**: gap
//!   **1102** (the `⚠` row's `due today`, `EmitDue.hotCell` over the plan's
//!   effective shape) and gap **1101** (`2b×1.6` on a line carrying `est:1b`,
//!   `Emit.itemEstOf` reading the leading estimate first). Both are §4.3's own
//!   cells; [`the_two_closed_holes_are_the_specs_own_cells`] names them.
//!
//! # What it cannot see
//!
//! * **A note the planner wrote as prose cannot cross the `plan` section**:
//!   `SegFlags::note` is a `String` and `Planner.Note` is eleven names with their
//!   arguments, so the fixture day sends `note: null` and the kernel **derives**
//!   the note column. [`the_kernel_writes_the_forks_note_sentences`] covers the
//!   eleven names the other way, and says what *it* cannot see.
//! * It is a **library-level** comparison of a few days: no binary is driven.
//!   `one_renderer.rs` drives the surfaces, and `planner_invariants.rs` holds the
//!   planner's own cells to the `plan` section's on every generated day.
//! * A frozen comparand is a fixed list: it finds nothing about a day it does
//!   not hold. The measurement over generated days that no shipped row moved at
//!   the deletion is the README's, and was made before the builder went.
//! * `Ghost` is the eleventh kind and is the kernel's alone — the fork carries
//!   the ghost row as a `SegFlags` bit — so no fork cell exists to compare it
//!   against and it is **not covered** (README gap 1322).

mod tui_common;

use chrono::Datelike;
use serde_json::{json, Value};

use tm_core::emit::{self, Layout, RowCells};
use tm_core::model::Id;
use tm_core::dayplan::{self, DayPlan, SegKind};

/// **The `plan` section's wire lives in `support/rowwire.rs`**, which
/// `tui_common` carries: one encoder and, since D112, the binary's own decoder
/// (`planwire::row_cells_of`).
use tui_common::rowwire::{differences, kernel_cells, kernel_sec, request};

// ---------------------------------------------------------------------------
// The Rust builder's cells, frozen at 49186d7 (the owner's D112 deleted it)
// ---------------------------------------------------------------------------

/// The fixture day's nine cells per row, as `emit::row_cells` wrote them.
/// `^t3`'s `est` cell is `1b×1.6` since the owner's D127 (parity P126, re-blessed under D64(d)): the
/// fixture's line carries the one estimate `1b`, which is the estimate as written the builder read.
const FROZEN_DAY: [[&str; 9]; 13] = [
    ["07:00", "5", "p1", "✓", "Read ch.6 §1–2", "@m3", "1b", "(67m)", ""],
    ["08:07", "5", "p1", "✓", "Read ch.6", "@O1", "3b", "(61m)", ""],
    ["09:08", "·", "", "✓", "break 20m", "", "", "(24m)", ""],
    ["09:32", "4", "p1", "▶", "Exercises 5.3–5.5", "@m1", "1b×1.6", "", ""],
    ["11:20", "·", "", " ", "lunch 30m", "", "", "", ""],
    ["11:50", "4↓", "p3", " ", "Claude Code drafts tests", "@m2", "1b", "", "↓ slot 4, item 3"],
    ["12:50", "⏰", "", " ", "Meeting w/ host", "", "1h", "", ""],
    ["13:50", "·", "", " ", "break 20m", "", "", "", ""],
    ["14:10", "3", "p3", " ", "Review the drafts", "@m2", "1b", "", ""],
    ["15:10", "1", "p0", "⚠", "Pick up package", "", "20m", "", "due today"],
    ["17:30", "·", "", " ", "dinner 30m", "", "", "", ""],
    ["18:00", "○", "", " ", "Severance S3E4", "", "1h", "", ""],
    ["21:30", "🌙", "", " ", "wind-down · bed 22:00", "", "", "", ""],
];
/// The same rows padded at the default layout, as `emit::plan_rows` wrote them.
const FROZEN_DAY_ROWS: [&str; 13] = [
    "07:00  5 p1 ✓ Read ch.6 §1–2               @m3  1b  (67m)",
    "08:07  5 p1 ✓ Read ch.6                    @O1  3b  (61m)",
    "09:08  ·    ✓ break 20m                             (24m)",
    "09:32  4 p1 ▶ Exercises 5.3–5.5            @m1  1b×1.6",
    "11:20  ·      lunch 30m",
    "11:50  4↓p3   Claude Code drafts tests     @m2  1b     ↓ slot 4, item 3",
    "12:50  ⏰     Meeting w/ host                   1h",
    "13:50  ·      break 20m",
    "14:10  3 p3   Review the drafts            @m2  1b",
    "15:10  1 p0 ⚠ Pick up package                   20m     due today",
    "17:30  ·      dinner 30m",
    "18:00  ○      Severance S3E4                    1h",
    "21:30  🌙     wind-down · bed 22:00",
];
/// The batch row of [`the_kernel_and_the_fork_agree_on_a_batch_row`].
const FROZEN_BATCH: [&str; 9] = ["07:00", "5", "p3", "✓", "batch: Claude Code drafts tests · Review the drafts · Pick up package (3)", "", "1b", "(67m)", ""];
const FROZEN_BATCH_MEMBERS: [&str; 3] = ["Claude Code drafts tests", "Review the drafts", "Pick up package"];
/// Its padded bytes at three title widths, the narrower two forcing `fit_batch` to cut.
const FROZEN_BATCH_ROWS: [(usize, &str); 3] = [(27, "07:00  5 p3 ✓ batch: Cla… · Re… · Pi… (3)       1b  (67m)"), (24, "07:00  5 p3 ✓ batch: Cl… · R… · P… (3)       1b  (67m)"), (18, "07:00  5 p3 ✓ batch: Claude Cod…       1b  (67m)")];
/// One row of every kind, with and without an item, of
/// [`the_kernel_and_the_fork_agree_on_every_kind_of_row`].
const FROZEN_KINDS: [[&str; 9]; 20] = [
    ["07:00", "5", "p3", " ", "Claude Code drafts tests", "@m2", "1b", "", ""],
    ["07:00", "5", "", " ", "—", "", "1b", "", ""],
    ["07:00", "5", "p3", " ", "batch: Claude Code drafts tests · Review the drafts (2)", "@m2", "1b", "", ""],
    ["07:00", "5", "p3", " ", "batch: Claude Code drafts tests · Review the drafts (2)", "", "1b", "", ""],
    ["07:00", "·", "", " ", "break 1h", "@m2", "", "", ""],
    ["07:00", "·", "", " ", "break 1h", "", "", "", ""],
    ["07:00", "5", "p3", " ", "Claude Code drafts tests", "@m2", "1b", "", ""],
    ["07:00", "5", "", " ", "—", "", "1b", "", ""],
    ["07:00", "⏰", "", " ", "Claude Code drafts tests", "@m2", "1b", "", ""],
    ["07:00", "⏰", "", " ", "—", "", "1b", "", ""],
    ["07:00", "·", "", " ", "rest 1h", "@m2", "", "", ""],
    ["07:00", "·", "", " ", "rest 1h", "", "", "", ""],
    ["07:00", "○", "", " ", "Claude Code drafts tests", "@m2", "1b", "", ""],
    ["07:00", "○", "", " ", "—", "", "1b", "", ""],
    ["07:00", "🌙", "", " ", "wind-down · bed 22:00", "@m2", "", "", ""],
    ["07:00", "🌙", "", " ", "wind-down · bed 22:00", "", "", "", ""],
    ["07:00", "·", "", " ", "Claude Code drafts tests 1h", "@m2", "", "", ""],
    ["07:00", "·", "", " ", "sleep 1h", "", "", "", ""],
    ["07:00", "·", "", " ", "lost 1h", "@m2", "", "", ""],
    ["07:00", "·", "", " ", "lost 1h", "", "", "", ""],
];
/// The members of [`FROZEN_KINDS`]' batch rows (2 and 3), `None` on every other.
const FROZEN_KINDS_MEMBERS: [Option<[&str; 2]>; 20] = [
    None,
    None,
    Some(["Claude Code drafts tests", "Review the drafts"]),
    Some(["Claude Code drafts tests", "Review the drafts"]),
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
    None,
];

/// A frozen row as [`RowCells`].
fn frozen(cells: &[&str; 9], members: Option<&[&str]>) -> RowCells {
    let s = |i: usize| cells[i].to_string();
    RowCells {
        time: s(0),
        ci: s(1),
        p: s(2),
        mark: s(3),
        title: s(4),
        parent: s(5),
        est: s(6),
        actual: s(7),
        note: s(8),
        batch_names: members.map(|m| m.iter().map(|x| x.to_string()).collect()),
    }
}

/// The fixture's documents, as the wire carries them.
fn docs() -> Vec<Value> {
    tui_common::docs_json()
}

/// [`docs`] with a hand-typed two-estimate `^t3` — `- [>] 4 2b … @m1 est:1b ^t3`, the example tree's
/// line until the owner's D127 (parity P126) — for the cell that reads a line carrying both.
fn two_estimate_docs() -> Vec<Value> {
    let text = serde_json::to_string(&docs()).expect("the docs serialise");
    assert_eq!(text.matches("- [>] 4 1b Exercises 5.3–5.5            @m1 ^t3").count(), 1, "the fixture's one-estimate `^t3`");
    serde_json::from_str(&text.replacen("- [>] 4 1b Exercises 5.3–5.5            @m1 ^t3", "- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3", 1)).expect("the docs parse")
}

// ---------------------------------------------------------------------------
// The comparisons
// ---------------------------------------------------------------------------

/// **Every cell of every row, on one day: the kernel's against the Rust
/// builder's, frozen.**
///
/// The kernel is not told a single one of the four cells it has to read the
/// plan for — `title`, `ci` (through the item), `est` and `parent` — so an
/// agreement here is two parsers agreeing about one tree, not a copy of an
/// answer. No cell is excused: until D112 two were (gaps 1101 and 1102), and
/// both are closed at their cause.
#[test]
fn the_kernel_and_the_fork_write_the_same_cells() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let lean = kernel_cells(docs(), &plan, &cfg);
    assert_eq!(
        lean.len(),
        FROZEN_DAY.len(),
        "the kernel answered {} rows for the {} the builder wrote (`Emit.rowsOf_length`'s wire half)",
        lean.len(),
        FROZEN_DAY.len()
    );
    assert!(lean.len() > 10, "a day worth comparing: {}", lean.len());
    for (i, (want, k)) in FROZEN_DAY.iter().zip(&lean).enumerate() {
        assert_eq!(
            differences(&frozen(want, None), k),
            vec![],
            "row {i} (`{}`): the kernel's cells are not the ones the Rust builder wrote",
            want[4]
        );
    }
    // And they are the day's own rows, which `tui_common::day_plan` asked the
    // kernel for through the same door.
    assert_eq!(plan.cells, lean, "the fixture day's rows are not the door's answer");
}

/// **And the bytes.** The kernel's cells, padded by the one padder, are the
/// rows the Rust builder's day file held — and `emit::plan_rows`, which every
/// surface prints since D112, is exactly them.
///
/// This is the sentence gap 1105 said had never been checked: *"no byte
/// comparison between the two has ever been run"*. It runs on every row, and
/// since D112 nothing is substituted before padding.
#[test]
fn the_kernels_cells_padded_are_the_day_files_bytes() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let layout = Layout::default();
    let lean = kernel_cells(docs(), &plan, &cfg);
    let shipped = emit::plan_rows(&plan, &layout);
    assert_eq!(shipped.len(), FROZEN_DAY_ROWS.len());
    for (i, ((want, cells), row)) in FROZEN_DAY_ROWS.iter().zip(&lean).zip(&shipped).enumerate() {
        assert_eq!(&emit::render_row(cells, &layout), want, "row {i}'s bytes are not the day file's");
        assert_eq!(row, want, "row {i}: `plan_rows` printed something else");
    }
    // And the padder really is doing work: at least one row was padded wider
    // than its cells, so `render_row` is not an identity this test could not
    // tell from one.
    assert!(
        shipped.iter().any(|r| r.contains("   ")),
        "no row has a padded column; the comparison would not see a padder"
    );
}

/// **The two holes this file declared, closed at their cause** (the owner's
/// D112): §4.3's own day prints `15:10  1 p0 ⚠  Pick up package  20m  due
/// today` and `09:20  4 p1 ▶ Exercises 5.3–5.5  @m1  2b×1.6` for a line
/// carrying both a leading `2b` and `est:1b`. The kernel answered `""` (README
/// gap 1102: no view of the deadline) and `1b×1.6` (gap 1101: `est:` first)
/// until W-47; a hole in the cells the binary prints is a moved byte on every
/// surface, so both were fixed rather than kept.
#[test]
fn the_two_closed_holes_are_the_specs_own_cells() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    // `^t3` hand-typed with both estimates: the shipped one carries one since D127 (P126).
    let lean = kernel_cells(two_estimate_docs(), &plan, &cfg);
    let row = |title: &str| lean.iter().find(|c| c.title == title).unwrap_or_else(|| panic!("no `{title}` row"));
    let hot = row("Pick up package");
    assert_eq!((hot.mark.as_str(), hot.note.as_str()), ("⚠", "due today"), "gap 1102: {hot:?}");
    let t3 = row("Exercises 5.3–5.5");
    assert_eq!(t3.est, "2b×1.6", "gap 1101: the leading estimate, as written: {t3:?}");
}

/// One block of the fixture tree's item `id`, every mark and note cleared — the
/// shape [`the_kernel_and_the_fork_agree_on_every_kind_of_row`] places.
fn plain_block(base: &DayPlan, id: &str) -> tm_core::dayplan::Segment {
    let mut seg = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();
    seg.item = Some(Id::new(id));
    seg.instance = None;
    seg.flags.note = None;
    seg.flags.done = false;
    seg.flags.current = false;
    seg.flags.hot = false;
    seg.flags.underused = false;
    seg.flags.multiplier = None;
    seg
}

/// **Parity P109, its first clause: a multiplier at a tie is written half-up**
/// (the owner's D112; README gap 1103). `Emit.multCell` rounds the multiplier
/// to two places with `Arith.halfUpQ`, the kernel's one rounding, so `1.125`
/// is `×1.13`; the deleted Rust builder wrote `energy::fmt_multiplier`, a
/// `{:.2}` that rounds the double half to even, `×1.12`. The fork's side is
/// asked of that function live, not transcribed — it is still the model
/// tables' formatter. Every row the switch census found differing (128 of
/// 3,095 over three runs) was this cell at this tie.
#[test]
fn a_multiplier_at_a_tie_is_written_half_up_p109() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);
    let mut seg = plain_block(&base, "t4");
    seg.flags.multiplier = Some(1.125);
    seg.flags.planned_min = Some(68);
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    plan.segments = vec![seg];
    let lean = kernel_cells(docs(), &plan, &cfg);
    assert_eq!(lean[0].est, "1b×1.13", "the kernel's cell: {:?}", lean[0]);
    let fork = format!("1b×{}", tm_core::energy::fmt_multiplier(1.125));
    assert_eq!(fork, "1b×1.12", "the formatter the Rust builder called");
    // And a multiplier that is not a tie is the same in both.
    let mut plan = plan.clone();
    plan.segments[0].flags.multiplier = Some(1.6);
    plan.segments[0].flags.planned_min = Some(96);
    let lean = kernel_cells(docs(), &plan, &cfg);
    assert_eq!(lean[0].est, format!("1b×{}", tm_core::energy::fmt_multiplier(1.6)), "{:?}", lean[0]);
}

/// **The estimate column is the item's written estimate times the multiplier**
/// — the three shapes `tm-core/tests/energy_model.rs` asserted of fmt_planned,
/// the Rust formatter of this column, until it went with the Rust row builder at
/// W-47 (the owner's D112): `2b×1.6` (§4.3's own `^t3`, a leading `2b` beside
/// `est:1b`), `1b` with the `×1` dropped, and `30m×1.25` (`^a1`'s leading
/// `30m`). Re-anchored on the kernel's `Emit.estCell`, the one writer of the
/// column since, rather than deleted with the formatter.
#[test]
fn the_estimate_column_is_the_written_estimate_times_the_multiplier() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    plan.segments = [("t3", 1.6, 192), ("t4", 1.0, 60), ("a1", 1.25, 38)]
        .iter()
        .map(|(id, m, planned)| {
            let mut seg = plain_block(&base, id);
            seg.flags.multiplier = Some(*m);
            seg.flags.planned_min = Some(*planned);
            seg
        })
        .collect();
    // `^t3` hand-typed with both estimates (D127, P126): the cell shows the one as written.
    let lean = kernel_cells(two_estimate_docs(), &plan, &cfg);
    let est: Vec<&str> = lean.iter().map(|c| c.est.as_str()).collect();
    assert_eq!(est, ["2b×1.6", "1b", "30m×1.25"], "{lean:?}");
}

/// **Parity P109, its second clause: a HOT row's deadline is §3.2's prep rule,
/// ONE step** (the owner's D112). The fixture's `^x2 Midterm review @x1` is
/// the interval `^x1`'s prep child, due at its start; a shapeless `^x3` under
/// `^x2` has no shape of its own and no interval for a parent, so the kernel's
/// `effectiveShape` gives it none (`effectiveShape_does_not_reach_the_grandparent`)
/// and its `⚠` row says nothing, where fork `Tree::effective_shape` walks every
/// shapeless ancestor and the deleted Rust builder wrote `due 2026-10-20`. The
/// host's reading is asked live of `Tree::effective_due`, which still feeds the
/// candidates (README gap 4955). No generated day of the switch census drew
/// such a row (0 of 666 hot rows).
#[test]
fn a_hot_rows_deadline_is_read_one_step_down_p109() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);
    let mut texts = tui_common::tree_texts();
    let week = texts
        .iter_mut()
        .find(|(p, _)| p == "week/2026-W37.md")
        .expect("the fixture's week");
    let prep = "- [ ] 5 8b Midterm review               @x1 ^x2\n";
    assert!(week.1.contains(prep), "the fixture moved: {}", week.1);
    week.1 = week.1.replace(prep, &format!("{prep}- [ ] 4 1b Practice exam @x2 ^x3\n"));
    let refs: Vec<(&str, &str)> = texts.iter().map(|(p, t)| (p.as_str(), t.as_str())).collect();
    let tree = tm_core::tree::Tree::from_texts(&refs, &cfg);
    let due = |id: &str| tree.effective_due(&Id::new(id)).map(|d| d.date().to_string());
    assert_eq!(due("x2"), Some("2026-10-20".to_string()), "the host's prep due, one step");
    assert_eq!(due("x3"), Some("2026-10-20".to_string()), "the host's walk, two steps");
    let docs: Vec<Value> = texts
        .iter()
        .map(|(p, t)| json!({"path": p, "lines": t.lines().collect::<Vec<_>>()}))
        .collect();
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.segments = ["x2", "x3"]
        .iter()
        .map(|id| {
            let mut seg = plain_block(&base, id);
            seg.flags.hot = true;
            seg
        })
        .collect();
    let lean = kernel_cells(docs, &plan, &cfg);
    assert_eq!((lean[0].mark.as_str(), lean[0].note.as_str()), ("⚠", "due 2026-10-20"), "{:?}", lean[0]);
    assert_eq!((lean[1].mark.as_str(), lean[1].note.as_str()), ("⚠", ""), "{:?}", lean[1]);
}

/// **A batch row**, which the fixture day has none of: `Emit.batchTitle` is
/// §7.5's frame over `Emit.batchNames`, the wire carries the members so the
/// fitter can reach them, and the fitted bytes are the ones `emit::fit_batch`
/// wrote over the Rust builder's member list.
#[test]
fn the_kernel_and_the_fork_agree_on_a_batch_row() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);

    // Three real ids of the fixture tree, gathered into one block.
    let members: Vec<Id> = ["t4", "t5", "a3"].iter().map(|s| Id::new(*s)).collect();
    let mut seg = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block to turn into a batch")
        .clone();
    seg.kind = SegKind::Batch(members);
    seg.item = None;
    seg.flags.note = None;
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    plan.segments = vec![seg];

    let lean = kernel_cells(docs(), &plan, &cfg);
    assert_eq!(lean.len(), 1);
    let want = frozen(&FROZEN_BATCH, Some(&FROZEN_BATCH_MEMBERS));
    assert_eq!(differences(&want, &lean[0]), vec![], "the batch row's cells");
    // The title really is the batch frame, so this test is not comparing two
    // empty strings.
    assert!(
        lean[0].title.starts_with("batch: ") && lean[0].title.ends_with("(3)"),
        "{:?}",
        lean[0].title
    );
    // And the fitted bytes, at a width that fits and two that force a cut.
    for (w, row) in FROZEN_BATCH_ROWS {
        assert_eq!(emit::render_row(&lean[0], &Layout::new(w)), row, "the batch row at title width {w}");
    }
}

/// **One row of every kind the fork can produce**, because the fixture day has
/// four of ten — each against the cells the Rust builder wrote for it.
///
/// `SegKind::Rest`, `SegKind::Lost`, `SegKind::Sleep` and `SegKind::WindDown`
/// are the kinds whose *title* carries a duration (`rest 20m`, `lost 20m`,
/// `sleep 8h`, `wind-down · bed 22:00`), and the fixture never places one;
/// without this, `Emit.titleCell`'s four corresponding branches are unwitnessed
/// by any machine and a change to them leaves every other test in this
/// repository green.
///
/// Each kind is placed twice — once with an item of the fixture tree and once
/// without — because the title cell's fallback (`—`, `routine`, `sleep`) only
/// fires on the second.
#[test]
fn the_kernel_and_the_fork_agree_on_every_kind_of_row() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);
    let proto = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();

    let kinds = [
        SegKind::Block,
        SegKind::Batch(vec![Id::new("t4"), Id::new("t5")]),
        SegKind::Break,
        SegKind::Routine,
        SegKind::Wall,
        SegKind::Rest,
        SegKind::Optional,
        SegKind::WindDown,
        SegKind::Sleep,
        SegKind::Lost,
    ];
    let mut segments = Vec::new();
    for kind in &kinds {
        for item in [Some(Id::new("t4")), None] {
            let mut seg = proto.clone();
            seg.kind = kind.clone();
            seg.item = item;
            seg.instance = None;
            seg.flags.note = None;
            seg.flags.done = false;
            seg.flags.current = false;
            seg.flags.hot = false;
            seg.flags.underused = false;
            segments.push(seg);
        }
    }
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    plan.segments = segments;

    let lean = kernel_cells(docs(), &plan, &cfg);
    assert_eq!(lean.len(), kinds.len() * 2);
    assert_eq!(FROZEN_KINDS.len(), lean.len());
    for (i, ((want, members), k)) in FROZEN_KINDS.iter().zip(&FROZEN_KINDS_MEMBERS).zip(&lean).enumerate() {
        let kind = dayplan::kind_label(&plan.segments[i].kind);
        let want = frozen(want, members.as_ref().map(|m| m.as_slice()));
        assert_eq!(
            differences(&want, k),
            vec![],
            "a `{kind}` row with item {:?}",
            plan.segments[i].item
        );
    }
    // The four duration-carrying titles really were exercised, so an agreement
    // on ten empty strings would not pass.
    for want in ["rest ", "lost ", "sleep ", "wind-down · bed "] {
        assert!(
            lean.iter().any(|c| c.title.starts_with(want)),
            "no row's title starts `{want}`: {:#?}",
            lean.iter().map(|c| c.title.clone()).collect::<Vec<_>>()
        );
    }
}

/// **The eleven `Note` names, rendered by the kernel.**
///
/// The other direction of the module header's second bullet: here the *kernel*
/// is given the name and the *fork's* row is given the sentence, so the
/// comparison is `Emit.noteText` against the text `tm-core/src/planner.rs`
/// writes at each `notes.push` / `note: Some(…)` site.
///
/// **What this cannot see**, and it is the weaker of the two comparisons: the
/// right-hand sides below are **transcribed** from the fork's `format!` strings
/// rather than produced by running its planner into each of the eleven
/// conditions. A transcription error would agree with itself. What it does
/// catch is the kernel's renderer drifting from the sentence recorded here, and
/// it covers all eleven constructors, which no fixture day does.
#[test]
fn the_kernel_writes_the_forks_note_sentences() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);
    let day = base.date;

    // (the wire's note, the sentence `tm-core/src/planner.rs` writes)
    let cases: Vec<(Value, String)> = vec![
        (
            json!({"note": "travelDay"}),
            "travel day: no blocks planned (`travel-day` wall today)".to_string(),
        ),
        (json!({"note": "travelDayWall"}), "travel day".to_string()),
        (json!({"note": "paused"}), "paused".to_string()),
        (json!({"note": "interruption"}), "interruption".to_string()),
        (
            json!({"note": "budgetSpent", "blocksDone": 6}),
            "budget spent: 6 blocks done, the rest of the day is rest".to_string(),
        ),
        (
            json!({"note": "runningLeft", "leftMin": 23}),
            "running · 23m left".to_string(),
        ),
        (
            json!({"note": "breakWhere", "text": "walk"}),
            "walk".to_string(),
        ),
        (
            json!({"note": "idleAttributed", "text": "idle → ^t3"}),
            "idle → ^t3".to_string(),
        ),
        (
            json!({"note": "plannedOf", "planned": 300, "total": 360}),
            "planned 5b of 6b (83%)".to_string(),
        ),
        (
            json!({"note": "bufferBefore", "id": "g1"}),
            format!("buffer before {}", tui_common::tree(&cfg).get(&Id::new("g1")).map(|i| i.title.clone()).expect("g1")),
        ),
        (
            json!({"note": "noPosition", "id": "t9", "durMin": 45, "lo": 0, "hi": 0}),
            String::new(), // filled in below: the two clocks are the window's
        ),
    ];

    let mut plan = DayPlan::empty(day, base.window, base.budget_blocks);
    let proto = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();
    plan.segments = vec![proto; cases.len()];

    let mut req = request(docs(), &plan, &cfg);
    // `noPosition`'s two instants are the plan window's, so the expected text
    // can be built from the same two clocks the kernel renders.
    let lo = kernel_sec(base.window.0);
    let hi = kernel_sec(base.window.1);
    let no_position = format!(
        "t9: no free 45m position in {}–{}; not planned today",
        dayplan::fmt_clock(base.window.0),
        dayplan::fmt_clock(base.window.1)
    );
    for (i, (note, _)) in cases.iter().enumerate() {
        let mut note = note.clone();
        if note["note"] == json!("noPosition") {
            note["lo"] = json!(lo);
            note["hi"] = json!(hi);
        }
        req["plan"]["segments"][i]["note"] = note;
    }

    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let rows = resp["ok"]["plan"]["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("no plan.rows:\n{raw}"));
    assert_eq!(rows.len(), cases.len());
    for (i, (note, want)) in cases.iter().enumerate() {
        let want = if want.is_empty() { &no_position } else { want };
        assert_eq!(
            rows[i]["note"].as_str().expect("note"),
            want,
            "the sentence for {note}"
        );
    }
}

/// **The wire refuses what R10 says it refuses**, through the kernel, by name.
///
/// A decoder whose rejection theorems are all proved and whose refusals never
/// reach the wire is half a guard; these are the same refusals seen from the
/// host's side.
#[test]
fn the_wire_refuses_a_bad_row_by_name() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let base = request(docs(), &plan, &cfg);

    let cases: Vec<(&str, Value, &str)> = vec![
        ("an unknown kind", json!("nosuchkind"), "badSegment 0 kind"),
        ("an inverted segment", Value::Null, "segmentRefused 0 inverted"),
    ];
    for (what, kind, want) in cases {
        let mut req = base.clone();
        if kind.is_null() {
            let stop = req["plan"]["segments"][0]["stop"].clone();
            req["plan"]["segments"][0]["start"] = json!(stop.as_i64().expect("stop") + 60);
        } else {
            req["plan"]["segments"][0]["kind"] = kind;
        }
        let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
        let resp: Value = serde_json::from_str(&raw).expect("json");
        assert_eq!(
            resp["err"]["plan"].as_str(),
            Some(want),
            "{what}: {raw}"
        );
    }

    // An energy past five, a priority past seven and a batch past the cap.
    let mut req = base.clone();
    req["plan"]["segments"][0]["energy"] = json!(6);
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("badSegment 0 energy"), "{raw}");

    let mut req = base.clone();
    req["plan"]["priorities"][0]["p"] = json!(8);
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("badPriority 0"), "{raw}");

    let mut req = base.clone();
    req["plan"]["segments"][0]["kind"] = json!("batch");
    req["plan"]["segments"][0]["batch"] =
        json!((0..17).map(|k| k.to_string()).collect::<Vec<_>>());
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("badSegment 0 batch"), "{raw}");

    // And the unmodified request is accepted, so the refusals above are not
    // this request being refused for some other reason.
    let raw = tm_kernel_ffi::call(&base.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert!(resp["ok"]["plan"]["rows"].is_array(), "{raw}");
}

/// **A `plan` section on a request that also edits the documents is refused by
/// name.**
///
/// The rows are rendered against the plan as `runLoad` read it and the
/// documents come back as the commands left them, so answering both would put
/// two states in one response. That is gap 109's stance on
/// `capacityWithCommands`, one section along, and it is a refusal rather than a
/// gap because a wrong answer here would be silent.
#[test]
fn a_plan_section_with_commands_is_refused() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let mut req = request(docs(), &plan, &cfg);
    req["cmds"] = json!([{"op": "drop", "id": "t4"}]);

    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("rowsWithCommands"), "{raw}");

    // The same command WITHOUT a `plan` section still applies, so the refusal
    // is the pairing and not the command.
    req.as_object_mut().expect("an object").remove("plan");
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert!(resp["ok"]["docs"].is_array(), "{raw}");
}

/// **A request with no `plan` section answers exactly as it did before**, which
/// is the Lean theorem `EmitWire.runRows_without_a_plan_section_is_runCap` seen
/// from the host: the FFI entry moved and nothing else did.
#[test]
fn a_request_without_a_plan_section_is_unchanged() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let mut req = request(docs(), &plan, &cfg);
    req.as_object_mut().expect("an object").remove("plan");

    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert!(resp["ok"]["docs"].is_array(), "{raw}");
    assert!(resp["ok"]["report"].is_object(), "{raw}");
    assert!(resp["ok"].get("plan").is_none(), "a plan key with no plan section: {raw}");
}

/// The fixture day this file compares actually exercises the cells it claims
/// to — otherwise an agreement on nine empty strings would pass every
/// assertion above.
#[test]
fn the_fixture_day_fills_every_column() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    const NAMES: [&str; 9] = [
        "time", "ci", "p", "mark", "title", "parent", "est", "actual", "note",
    ];
    for (i, name) in NAMES.iter().enumerate() {
        let filled = FROZEN_DAY.iter().filter(|c| !c[i].trim().is_empty()).count();
        assert!(filled > 0, "no row of the fixture day has a `{name}` cell");
    }
    // And the day covers more than one kind.
    let kinds: std::collections::BTreeSet<&str> = plan
        .segments
        .iter()
        .map(|s| dayplan::kind_label(&s.kind))
        .collect();
    assert!(kinds.len() >= 5, "one kind of row is not a day: {kinds:?}");
    assert_eq!(plan.date.year(), 2026, "the fixture moved");
}
