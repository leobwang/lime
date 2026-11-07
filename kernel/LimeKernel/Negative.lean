import LimeKernel
/-!
# The demonstration: the shipped bug does not compile

Each block below writes something the Rust wrote (or something a future writer
would plausibly write) and **fails to compile**.  This file is the only test
that checks the type system is still doing its job, so CI must assert that
`lean Negative.lean` FAILS.

    LEAN_PATH=.lake/build/lib/lean lean Negative.lean     # must print errors
-/
namespace Lime

/- CHEAT 1 — write `lime move` the way `horizon.rs::move_to` writes it: put the
   line where it is going, no question asked about what is already there. -/
def moveCheat1 (t : Site) (e : Entity) : Entity :=
  { e.val with live := t }

/- CHEAT 2 — skip the check by asserting the proof. -/
def moveCheat2 (t : Site) (e : Entity) : Entity :=
  ⟨{ e.val with live := t }, rfl⟩

/- CHEAT 3 — the bug in its original shape: `move_to` **appends the rendered
   line to the destination file**.  In this kernel a document holds prose only,
   and `planWf` says none of it parses as an item, so an appended item line is
   a plan that cannot be constructed. -/
def appendLine (l : List Char) (d : Doc) : Doc := ⟨d.path, d.prose ++ [(0, l)], d.region⟩

def moveCheat3 (i : Id) (g : Glyph) (r : RawItem) (k : DocIx) (p : WfPlan) : WfPlan :=
  ⟨⟨p.val.docs.modify k (appendLine (serializeItem i g r)), p.val.store⟩, p.property⟩

/- CHEAT 4 — a close that zeroes the remaining estimate it just measured.
   The definition is legal; the conservation obligation is not dischargeable. -/
def closeCheat (e : Entity) : Entity :=
  ⟨{ e.val with line := setEst 0 e.val.line }, e.property⟩

theorem close_conserves (bm : Nat) (e : Entity) :
    remainingOf bm e.val.line ≤ remainingOf bm (closeCheat e).val.line := by
  simp [closeCheat]

/- CHEAT 5 — export `setLeadWord` as "edit the estimate", which is what
   `lime edit ^id est=` did.  Every setter must discharge `view ∘ set = id`; this
   one cannot, and `lead_edit_is_silent` says why. -/
theorem lead_set_is_not_silent (bm : Nat) (w : List Char) (r : RawItem) :
    viewRemaining bm (setLeadWord w r) = unitValue bm w := rfl

/- CHEAT 6 — take the destination straight off the wire, which is what let
   `move ^m1 7` delete the item from a one-document plan and return `ok`.  A
   `Dest` is an index **plus a proof it is a document of this plan**, and a
   `Nat` decoded from JSON cannot supply the second field. -/
def destCheat (n : Nat) (p : WfPlan) : Dest p.val := ⟨n, by omega⟩

/- CHEAT 7 — **withdrawn, and its replacements are CHEAT 36-40.**  It read: a
   record beside a standing tombstone may not be `[ ]`, so
   `statusOfGlyphDemoted .todo` is `none` and the entity below cannot be built.
   §6.3 refutes it — `lime readopt` is "`[-]` → `[ ]`, stamp kept", and §4.3's
   own fixture pair is a `[ ]` in `week/2026-W37.md` beside the `[-]` in
   `month/2026-09.md # Demoted`.  The kernel now reads that pair, so the cheat
   asserted a restriction the model no longer has and could not stay: a
   negative test that refuses something legitimate is a trapdoor, not a check.
   What replaces it is the rule that is genuinely gone (CHEAT 37), the type
   that makes a byte-less tombstone unwritable (CHEAT 36), and the
   unconditional horizon rule (CHEAT 38). -/

/- CHEAT 8 — build the plan without answering which of a demotion's two `[-]`
   lines is the tombstone.  Deciding it by the order the host listed the
   documents was this, with the assertion hidden in a `match` that tried one
   orientation and then the other: three of `planWf`'s parts discharged and the
   rest waved through.  (`planWf` has five parts since the item fields joined
   the plan-level tier, so the first `rfl` Lean reaches is `itemsWf`'s; the
   cheat is the same one.) -/
def loadCheat (planDocs : List Doc) (store : Store)
    (h1 : docsWf ⟨planDocs, store⟩ = true) (h2 : sitesInRange ⟨planDocs, store⟩ = true)
    (h3 : pathsDistinct ⟨planDocs, store⟩ = true) : WfPlan :=
  ⟨⟨planDocs, store⟩, planWf_of_parts h1 h2 h3 rfl rfl⟩

-- ===========================================================================
-- APPENDED: the item fields and the rest of the plan-level tier
-- (State.lean / Plan.lean).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 9 — wave the **item half** of the plan-level tier through, which is
   what "cycles are only a `lime check` warning" amounts to once `lime check` and
   the acceptance rule are the same function.  `planWf` has five parts now and
   `itemsWf` is one of them; `rfl` cannot supply it. -/
def itemTierCheat (planDocs : List Doc) (store : Store)
    (h1 : docsWf ⟨planDocs, store⟩ = true) (h2 : sitesInRange ⟨planDocs, store⟩ = true)
    (h3 : pathsDistinct ⟨planDocs, store⟩ = true)
    (h4 : demotionsOriented ⟨planDocs, store⟩ = true) : WfPlan :=
  ⟨⟨planDocs, store⟩, planWf_of_parts h1 h2 h3 h4 rfl⟩

/- CHEAT 10 — the sharpest of the new ones: claim a transform that lands in
   range and keeps its tombstone behind it always succeeds.  It does not, since
   `Normalized` and `after:` acyclicity joined `planWf`: a move onto an occupied
   rank, or an edit that closes a dependency cycle, is refused by `mapAt`'s
   re-check.  The residual obligation is `hrest`, and it cannot be forgotten
   because the theorem will not apply without it. -/
theorem move_always_works (p : WfPlan) (i : Id) (f : Entity → Except KErr Entity)
    (e e' : Entity) (hget : p.val.store.get i = some e) (hf : f e = .ok e')
    (hin : entityInRange p.val e' = true) (hor : demotionOriented p.val e' = true) :
    ∃ q : WfPlan, p.mapAt i f = .ok q ∧ q.val.store.get i = some e' ∧
      q.val.docs = p.val.docs :=
  mapAt_ok_of_inRange p i f e e' hget hf hin hor

/- CHEAT 11 — `ci: 9`.  The Rust field is a `u8` and the parser clamped; here
   the bound is the type.  (Note the shape of the cheat: `(9 : Fin 6)` would
   *silently* wrap to 3 through `OfNat`, which is why every bounded value in
   this kernel comes from a smart constructor and not from a numeral.) -/
def ciCheat : Fin 6 := ⟨9, by omega⟩

/- CHEAT 12 — `#lean #lean` as two tags.  Tags are a set structurally, so the
   duplicate is not something a later `dedup` has to catch. -/
def tagCheat : TagSet := ⟨[['l', 'e', 'a', 'n'], ['l', 'e', 'a', 'n']], by decide⟩

/- CHEAT 13 — hand a raw list where the set is wanted.  `Core.tags` is a
   *view* of the line now, so the cheat is one level down: build the value the
   view returns out of a list with a duplicate in it. -/
def rawTagsCheat : TagSet := ⟨[['a'], ['a']], by decide⟩

/- CHEAT 14 — `win:25:00-…`.  A time of day is `Fin 1440`. -/
def clockCheat : Field.Clock := ⟨1500, by omega⟩

/- CHEAT 15 — `every:month:32`.  The only door into a monthly rule is
   `parseMonthDay`, and it refuses. -/
theorem monthDayCheat :
    Field.parseMonthDay ['3','2'] = some (Field.Rule.monthly 32) := by decide

end Lime

/- ======================================================================
   THE EXACT-ARITHMETIC LAYER (`LimeKernel/Base/Arith.lean`).
   Appended as its own block so that the three stage-one branches merge.
   ====================================================================== -/
namespace Lime

/- CHEAT 16 — form the quotient.  `u = need/avail` in `Nat` is integer
   division, which throws the fraction away before the comparison sees it:
   `u = 3/4` reaches the `1/2` edge, and `3/4 = 0` reaches nothing.  This is
   why `utilGe` cross-multiplies and no ratio is ever divided. -/
def utilNatDiv (need avail : Nat) (e : Arith.Q) : Bool :=
  decide (e.num ≤ e.den * (need / avail))

theorem the_quotient_is_the_comparison :
    utilNatDiv 3 4 ⟨1, 2⟩ = Arith.utilGe 3 4 ⟨1, 2⟩ := by decide

/- CHEAT 17 — round a ratio whose denominator nobody checked.  `n / 0` is
   `0` in Lean, so §8.1's budget with `block_min = 0` would be a silent
   wrong answer rather than an error.  A rounding site takes a `Pos`, and a
   raw `Q` is not one. -/
def budgetCheat (windowMin blockMin : Nat) : Nat :=
  Arith.floorQ (⟨windowMin, blockMin⟩ : Arith.Q)

/- CHEAT 18 — round the safety margin the way `priority.rs:349` does.  A
   margin rounded down stops being a margin: the reservation for one minute
   of work at `safety = 1.3` becomes one minute, which does not cover
   `13/10`.  R1's rule is a ceiling, and `needMin_covers` is why. -/
def needFloor (rem : Nat) : Nat := Arith.floorQ (Arith.scale Arith.safety rem)

theorem floor_still_covers_the_need :
    Arith.Q.le (Arith.scale Arith.safety 1).val (Arith.ofNat (needFloor 1)) = true := by decide

/- CHEAT 19 — derive §7.1's bin edges instead of tabulating them.  Three of
   the four are halvings, so `1/2^i` looks like the generating structure; it
   disagrees with the spec on every `u` in `[0.1, 0.125)`, and at `u = 0.11`
   it gives `+3` where the table gives `+2`. -/
theorem log2_ladder_is_the_table :
    Arith.binOf Arith.log2Bins 11 100 = Arith.binOf Arith.defaultBins 11 100 := by decide

/- CHEAT 20 — guard the division by zero, which is what `is_finite()` does
   in the Rust.  §7.1 says capacity zero makes `u = ∞`, so it reaches every
   edge and the item is HOT; a guard that answers "not urgent" inverts the
   rule at exactly the point where the item cannot possibly be finished. -/
def utilGuarded (need avail : Nat) (e : Arith.Q) : Bool :=
  if avail = 0 then false else Arith.utilGe need avail e

theorem the_finite_guard_is_harmless :
    utilGuarded 1 0 Arith.hotEdge = Arith.utilGe 1 0 Arith.hotEdge := by decide

end Lime

/- ═══════════════════════════════════════════════════════════════════════════
   CALENDAR CHEATS (Cal.lean / Grain.lean).  Appended; nothing above is edited.
   ═══════════════════════════════════════════════════════════════════════════ -/
-- Only so the failures below are the *type* errors they claim to be, and not
-- an elaborator budget running out first.  It applies from here on only.
set_option maxRecDepth 10000

namespace Lime

/- CHEAT 21 — hand a date straight through as valid, which is how `Feb 30`
   reaches a calendar.  `ValidDate` is a `Subtype` over a *decidable* predicate,
   so the second field is `Date.valid ⟨2024,2,30⟩ = true`, and that computes to
   `false = true`. -/
def dateCheat : Cal.ValidDate := ⟨⟨2024, 2, 30⟩, by decide⟩

/- CHEAT 22 — number the weeks inside the civil year, which is what "week 1
   starts on January 1st" does, and claim it is the ISO week.  It is not: on
   2027-01-01 this says week 1 and ISO says 2026-W53. -/
def naiveWeek (n : Nat) : Nat := (n - Cal.jan1 (Cal.ofDay n).year) / 7 + 1

theorem naive_week_is_iso :
    naiveWeek (Cal.toDay ⟨2027, 1, 1⟩) = (Cal.isoOf (Cal.toDay ⟨2027, 1, 1⟩)).week := by
  decide

/- CHEAT 23 — name a week's month without naming a tie-break, by assuming the
   week determines the month.  The rewrite is where the derivation stops:
   `week_does_not_refine_month` is the counterexample (2026-W36). -/
theorem week_refines_month : refines week month := by
  intro a b h
  rw [index_week] at h
  rw [index_month, index_month, h]

/- CHEAT 24 — declare `horizon.rs:1543`'s rule stable.  "The month of today" is
   a function of `now`, so two callers on two days of one week get two answers,
   and this does not even hold definitionally. -/
theorem month_of_today_is_stable :
    Cal.monthOfWeekByToday (Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩))
        (Cal.toDay ⟨2026, 8, 31⟩)
      = Cal.monthOfWeekByToday (Cal.weekOrdinal (Cal.toDay ⟨2026, 8, 31⟩))
        (Cal.toDay ⟨2026, 9, 6⟩) := by
  decide

/- CHEAT 25 — drop the century rule and keep "every fourth year".  Refuted by
   computation at y = 100. -/
def isLeapCheat (y : Nat) : Bool := y % 4 == 0

theorem leap_is_every_fourth_year : ∀ y, y < 2000 → Cal.isLeap y = isLeapCheat y := by
  decide

/- CHEAT 26 — get the phase of the seven-day cycle wrong by one.  The three
   cross-checks in `Cal.lean` exist to catch exactly this, and they do. -/
def weekdayCheat (n : Nat) : Cal.Weekday := Cal.Weekday.ofIndex (n % 7 + 1)

theorem cheat_weekday_1970 : weekdayCheat (Cal.toDay ⟨1970, 1, 1⟩) = .thursday := by decide


/- ======================================================================
   §4.1's field grammar — cheats added with the field grammar (Line.lean,
   Text.lean).  Every block below is a plausible claim about the grammar
   that is FALSE, and Lean says so.
   ====================================================================== -/

/- CHEAT A — drop `Rule.wf` from the `every:` round trip.  `every:0d` renders
   as `0d` and `grammar.rs` rejects `n == 0`, so `.everyNDays 0` does not come
   back; the side condition is load-bearing and `rfl` cannot supply it. -/
theorem every_needs_no_side_condition (r : Field.Rule) :
    Field.parseRule (Field.renderRule r) = some r :=
  Field.parse_render_rule r rfl

/- CHEAT B — the shipped `lime edit est=` bug, stated as a law: read the
   remaining estimate off the *leading* slot.  §4.1 says `est:` overrides it,
   and `spec_line_remaining` is the counterexample. -/
theorem leading_estimate_is_the_remaining_estimate (r : RawItem) :
    Field.viewRemainingDur r = Field.estLeadOf r := rfl

/- CHEAT C — accept a date that is not zero-padded.  `parse_date` checks the
   width (`s.len() != 10`) and so does this kernel. -/
theorem date_accepts_unpadded :
    Field.parseDate ['2','0','2','6','-','9','-','1','1'] ≠ none := by decide

/- CHEAT D — treat a flag word inside the title as a flag.  §4.1 reads a flag
   only after a `@ # ! ^ key:` token, which is why `setFlag` inserts after the
   `^id` and why it returns `none` when there is no id. -/
theorem flag_word_in_the_title_is_a_flag :
    Field.flagsOf (Field.itemOf Field.flagInTitleLine) = [Field.Flag.openEnded] := by decide

/- CHEAT E — give `cap:` a field of its own.  It is an alias of `max:`; two
   places for one budget is the defect class this kernel exists to remove. -/
theorem cap_is_its_own_field :
    Field.Key.ofName? ['c','a','p'] ≠ Field.Key.ofName? ['m','a','x'] := by decide

/- CHEAT F — drop `slotGuard` from round trip B.  A title beginning with `5`
   is eaten by the empty ci slot, so the fields do not come back: the line
   reads as `ci = 5` with a one-word title.  This is `grammar.rs`'s
   `EditError::Ambiguous`, and refusing to write the line is the fix. -/
def ambiguousFields : Field.Fields :=
  { title := [['5'], ['a','p','p','l','e','s']] }

theorem the_slot_guard_is_unnecessary :
    Field.viewFields (Field.renderItem ['t','3'] ambiguousFields) = ambiguousFields := by
  decide

end Lime

/- ==================================================================== -/
/- Round trip and `Normalized`: the cheats the plan-level proofs refuse. -/
/- ==================================================================== -/

namespace Lime

/- CHEAT 27 — "the store hands its lines back in rank order, so the sort is a
   formality."  It is not: the store enumerates its domain, not the file.  A
   two-line list in the wrong order is the whole counterexample. -/
def unsortedRanks : List (Nat × List Char) := [(2, "b".toList), (1, "a".toList)]

theorem sorting_is_a_formality : sortByRank unsortedRanks = unsortedRanks := by decide

/- CHEAT 28 — drop rank distinctness from the round trip and keep the
   conclusion.  `sorted_ext_by_key` needs a **strict** order: with `≤`, two
   lines at one rank are two different files with the same members and the sort
   has nothing to choose between them.  `Normalized` is what supplies the
   strictness, and this is the type error that says so. -/
theorem sorted_ext_by_le : ∀ (l₁ l₂ : List (Nat × List Char)),
    l₁.Pairwise (fun a b => a.1 ≤ b.1) → l₂.Pairwise (fun a b => a.1 ≤ b.1) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ :=
  sorted_ext_by_key (fun x : Nat × List Char => x.1)

/- CHEAT 29 — read the file back without asking whether ranks are distinct.
   `renderDocAt_loadCore` takes `normalized` because without it the sorted list
   is not determined by its members, and which of two lines sharing a rank comes
   first depends on the order the store enumerated its domain — i.e. on the
   order the host listed its documents. -/
theorem round_trip_without_rank_distinctness (docs : List ReqDoc)
    (items : List (Id × Entity))
    (hb : buildEntities (placementsOf 0 docs) = .ok items)
    (k : Nat) (rd : ReqDoc) (hk : docs[k]? = some rd) :
    renderDocAt (loadCore docs items) k (mkDoc rd) = rd.lines :=
  renderDocAt_loadCore docs items hb k rd hk

/- CHEAT 30 — "any rank will do."  `freshRank` is not decoration: a move onto a
   rank another line of the destination already holds is exactly the ambiguity
   `Normalized` forbids, and rank 0 is the rank a naive implementation picks. -/
theorem move_to_rank_zero_keeps_ranks_distinct (p : WfPlan) (i : Id) (e a : Entity)
    (k : DocIx) (hs : (p.val.store.get i).isSome = true)
    (hget : p.val.store.get i = some e) (hva : a.val = { e.val with live := ⟨k, 0⟩ }) :
    normalized { p.val with store := p.val.store.set i a hs } = true :=
  move_at_freshRank_normalized p i e a k hs hget hva

/- CHEAT 31 — count only the item lines when checking a rank is free.  A
   document's ranks are its prose ranks *and* its item ranks in one list, because
   `weave` orders them against each other; a relocated line landing on a
   heading's rank would move that heading with no command run.  `SitesFree` has
   two clauses for this reason. -/
theorem normalized_set_ignoring_prose (p : PlanCore) (i : Id) (e e' : Entity)
    (hs : (p.store.get i).isSome = true) (hget : p.store.get i = some e)
    (hnorm : normalized p = true)
    (hfree : ∀ l ∈ render i e', ∀ m ∈ p.lines, m.site = l.site → m ∈ render i e) :
    normalized { p with store := p.store.set i e' hs } = true :=
  normalized_set p i e e' hs hget hnorm hfree

end Lime

/- ===================================================================
   FOUND BY THE CORPUS HARNESS AND THE DIFFERENTIAL ORACLE, appended as a
   block so the stage-two branches merge.  Numbered from 27 provisionally;
   whoever merges renumbers.  Renumbered 27-30 -> 122-125 in the W-1 audit
   repair (AGENTS 6.5 item 1): the rank block above keeps 27-30.

   Each one is an assumption a reader of §4.1 would make, that the shipped
   Rust makes, and that this kernel does not satisfy.  They are here rather
   than in a report because a refutation that only lives in prose is one the
   next writer re-derives differently.  All four were found by running the
   fixture corpus (`kernel/corpus/`) and 2,048 lines from `main`'s own
   `grammar_proptest` generator through the boundary and comparing with
   `lime-core::grammar`; the counts are in `kernel/README.md`.
   =================================================================== -/
namespace Lime

/- CHEAT 122 — **withdrawn at W-42 track G (owner D83): the separator is the host's, so the
   claim it refuted is TRUE and the hole it recorded is closed.**  It read: §4.1 says an item
   line's tokens are "whitespace-separated words", and `lime-core::grammar` splits on any
   whitespace run, while `Text.lean`'s separator was `c == ' '`, so a tab was an ordinary word
   character and `a<TAB>b` was ONE token — `- [ ] x<TAB>^a1` refused as `noId`, `- [ ] x ^a1<TAB>`
   keyed `"a1\t"`, and `lime edit est=` landing on a different token from the Rust's.  Its claim,
   `(tokenize "a\tb".toList).length = 2`, now holds, which is why it cannot stay here: a
   negative test whose claim is true is a check no input can fail.  The positive statements are
   `the_separator_is_white_space` (Text.lean) and `a_tab_separates_the_id` (Line.lean); what
   still must fail is CHEAT 262, below — a separator WIDER than the host's. -/

/- CHEAT 123 — **withdrawn at W-42 track G (owner D83): the separators between the bullet and
   the box are read as the host reads them.**  It read: `parseBody` matched the literal `- [`, so
   `- <TAB>[ ] …` and `-  [ ] …` (two spaces) were not item lines but prose, written back
   unchanged and invisible to every command — 1,049 of 2,048 generated lines — and, after K3a,
   the bare grammar's bracket refusal (tokBare) kept them prose rather than bare items whose
   title begins `[`.  Its claim, `isItemLine "-  [ ] 2 30m Spaced ^a1".toList = true`, now holds.
   The positive statements are `a_line_spaced_from_its_box_is_boxed` and
   `a_bracket_in_a_bare_line_is_title_text` (Line.lean; a_line_with_a_bracket_is_not_a_bare_item,
   which said the opposite, is retired); what still must fail is CHEAT 260 and 261, below — a box
   the host does not read, and an indent it does not read either. -/

/- CHEAT 124 — §4.1 says a token the parser cannot classify stays in the title,
   and the Rust keeps `^`, `^%` and `^é` there and records a `lime check`
   problem.  `isIdWord w := w.head? == some '^'` makes every one of them an id
   token, so a bare `^` names an entity whose id is the empty list (and two such
   lines are `dupId ""`), `^%` names one called `%`, and a line carrying both
   `^%` and a real `^q7` is refused as `manyIds`.  The last of those is
   `plan-conflicts/week/2026-W37.md:23`, a line the shipped parser reads with
   id `q7`. -/
theorem a_bare_caret_is_not_an_id : isIdWord ['^'] = false := by decide

/- CHEAT 125 — §4.3's calendar rule ("generated intervals") waved through: hold
   it of *every* line the loader builds.  It used to be `rfl`, and that is the
   defect this branch fixes.  Nothing joined §4.1's `at:` to §3.1's
   `Core.shape`, so the shape was `none` for every entity the boundary
   constructed and the `.calendar` clause was unsatisfiable rather than merely
   unsatisfied — all 16 calendar item lines in the corpus refused with
   `itemCheck: fileKindShape`, four of them written exactly as §4.1 writes
   them.  `Core.shape` is `Field.viewShape` of the line now, so the rule is a
   real question about the bytes: true of `at:2026-09-07T12:50/13:50`
   (`the_spec_calendar_line_is_an_interval`, State.lean) and false of
   `plan-conflicts`' `- [ ] 3 Office hours  loc:JCL ^g7`, which is the line
   that fixture exists to have refused. -/
theorem a_loaded_line_always_satisfies_the_calendar_shape_rule
    (live : Site) (st : Status) (r : RawItem) :
    shapeWfFor DocKind.calendar
      { live := live, archive := none, status := st, line := r } = true := rfl

/- ======================================================================
   APPENDED — the cheats §3.1's field wiring makes available, and refuses.

   §3.1's item fields are **views of `Core.line`**, and §3.1's value types
   **are** §4.1's.  Each cheat below re-opens one of the two holes that were
   there before: a slot beside the line for a field to drift in, or a second
   definition of a type §4.1 already has.
   ====================================================================== -/

/- CHEAT 32 — the duplication itself: a `shape` slot on `Core`, settable
   without moving the bytes.  Two definitions of `Shape` in one kernel is how
   `est:` and the leading estimate came to disagree in the Rust; there is one
   `Shape` now and it is not something a record update can move. -/
def shapeSlotCheat (c : Core) (s : Field.Shape) : Core := { c with shape := s }

/- CHEAT 33 — a `stamps` slot beside the line, which is what `Core` used to
   carry.  `renderCore` prints the line, so a stamp written here is a stamp no
   file ever sees — and §6.3's month review cuts on "≥ 2 stamps". -/
def stampSlotCheat (c : Core) (st : Field.Stamp) : Core :=
  { c with stamps := c.stamps ++ [st] }

/- CHEAT 34 — `demote` that records the stamp without writing it.  This is the
   law the old `Core` satisfied: a line came through a demotion untouched,
   because the stamp had somewhere else to go. -/
theorem demote_leaves_the_line_alone (t : Site) (st : Field.Stamp) (e a : Entity)
    (h : demote t st e = .ok a) : a.val.line = e.val.line := by
  rw [lift_roundtrips _ _ h]

/- CHEAT 35 — refuse a lone `[-]` again.  §4.3's `month/2026-09.md#Demoted`
   holds one, `lime close month` carries it into the next month file without
   touching the week file it was paired with, and the Rust core resolves a key
   group of size one without looking for a partner.  `orphanDemotion` was the
   loader saying otherwise, and it is not a diagnostic any more. -/
def orphanDemotionCheat (i : Id) : LErr := .orphanDemotion i

-- ===========================================================================
-- APPENDED: the demotion pair — which line is the tombstone, and the bytes
-- that stand at it (State.lean / Plan.lean / Boundary.lean).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 36 — a tombstone that is a placement and nothing else.  This is the
   entity the whole corpus foundered on: one token vector, rendered at two
   sites, so §6.3's pair — the week line as it stood and the month copy with
   `est:` = remaining and `demoted:W37` appended — had no value that denotes
   it, and the loader called it `splitLine`.  A `Tomb` is a site **and** the
   bytes standing there, in one field, so "the archive has a placement but no
   text" is not a state that exists. -/
def tomblessArchiveCheat (live arch : Site) (st : Status) (r : RawItem) : Core :=
  { live := live, archive := some arch, status := st, line := r }

/- CHEAT 37 — the rule that made §4.3's fixture unreadable: force `[-]` on the
   record whenever a tombstone stands.  It was defensible as a reading of the
   *post-close* snapshot and it is false of every readopted item; the box at a
   live site is now the status and nothing else (`glyphAt_live`). -/
theorem a_record_beside_a_tombstone_always_reads_demoted
    (live arch : Site) (a l : RawItem) :
    glyphAt { live := live, archive := some ⟨arch, a⟩, status := .live .free, line := l } live
      = Glyph.demoted := rfl

/- CHEAT 38 — demand the horizon order of every demotion pair, not only of the
   ones whose boxes tie.  This is `demotionsOriented` as it was, and it is what
   refused three of the five fixture plans: §4.3's pair has its record live in
   a **week** and its archive in a **month**, so the archive's horizon does not
   precede the record's and never had to — the boxes settle that pair without
   consulting a file. -/
theorem every_tombstone_is_behind_its_record (p : WfPlan) (i : Id) (e : Entity) (r : Site)
    (hget : p.val.store.get i = some e) (harch : e.val.archiveSite = some r) :
    horizonPrecedes (docRegion p.val r.doc) (docRegion p.val e.val.live.doc) = true :=
  the_tombstone_is_behind_the_live_line p i e r hget harch

/- CHEAT 39 — refuse a pair whose two lines differ.  `LErr.splitLine` said "an
   entity owns one token vector, so there is no value that renders both", which
   was true of the model and never of the data: §6.3's close writes the two
   lines differently on purpose.  The constructor is gone. -/
def splitLineCheat (i : Id) : LErr := .splitLine i

/- CHEAT 40 — `demote` that writes one token vector to both sites, which is
   what it did before the tombstone carried its own bytes: the `demoted:` stamp
   §6.3 appends to the **copy** appeared in the week file too, and the week
   line the close was supposed to leave alone came back changed. -/
theorem demote_writes_one_token_vector (t : Site) (st : Field.Stamp) (e a : Entity)
    (h : demote t st e = .ok a) :
    a.val.archive = some ⟨e.val.live, a.val.line⟩ := by
  rw [demote_roundtrips _ _ _ _ h]

/- CHEAT 41 — `readopt` that reopens anything.  §6.3 says it "moves a *demoted
   line* into the current week (`[-]` → `[ ]`, stamp kept)", and run on a
   record that is already `[ ]` it consumes a tombstone whose bytes carry the
   `est:` and the stamp — so "stamp kept" is precisely what it loses, on the
   very pair this kernel was changed to admit.  `readopt` returns an `Except`
   now, and `KErr.notDemoted` is what it returns. -/
def readoptAnythingCheat (t : Site) (e : Entity) : Entity := readopt t e

/- CHEAT 42 — the assumption the withdrawn `demote_not_idem` rested on: that a
   second `demote` can succeed at all.  It is how the standing tombstone got
   overwritten and its file's line dropped from the render with the kernel
   returning `ok`.  §6.3 gives an item one archive record and the month close
   *moves* it, so the composite is `alreadyDemoted`
   (`demote_twice_is_not_a_thing`) — and a refutation whose second hypothesis
   has no witness is vacuous, which is why that law is withdrawn rather than
   kept.  `stamps_accumulate_across_readopt` is what replaces it. -/
theorem demote_twice_succeeds (t t' : Site) (st : Field.Stamp) (e a : Entity)
    (h1 : demote t st e = .ok a) : ∃ b, demote t' st a = .ok b :=
  ⟨_, rfl⟩

-- ===========================================================================
-- APPENDED: the `add` verb's freshness door (Plan.lean / Boundary.lean).
-- CHEAT 43 landed with the add session (9840ea8) but rode under the
-- demotion-pair banner above; this banner was added 2026-09-12 to say why
-- the block exists.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 43 — insert an item over a standing one.  `Store.set` demands
   `(get i).isSome = true`, `Store.insertFresh` demands the dual
   `(get i).isNone = true`, and handing the first proof to the second is a
   type error — which is the whole point: the two doors are complementary and
   there is no third door that takes neither proof.  Freshness for `add` is
   L21's theorem, not a runtime retry. -/
def insertOver (s : Store) (i : Id) (e : Entity) (h : (s.get i).isSome = true) :
    Store :=
  s.insertFresh i e h

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3 edit-widening session): the keyed edit's
-- bounded doors.  R10 says every bounded type crossing the wire goes through
-- the smart constructor its decoder uses; these are the three doors staying
-- shut when the smart constructor is bypassed.  Everything below must FAIL
-- to compile.
-- ===========================================================================

/- CHEAT 44 — a `ci` above the bound.  `EditVal.ci` carries `Fin 6`, so the
   wire value `7` cannot become a payload: `parseCi` is the smart constructor
   (`if h : n < 6`), and building the `Fin` by hand fails because `decide`
   cannot prove `7 < 6`. -/
def sneakCi : EditVal := .ci ⟨7, by decide⟩

/- CHEAT 45 — unset a key the edit path is not wired for.  `EditKey` demands
   `keyEditable k = true`, and `keyEditable .demoted` is `false` — `demoted:`
   is lifecycle state that `demote`/`readopt` own, and `rfl` here is a type
   error, not a policy comment.  The only door is `parseCmd`'s `dif`, which
   never opens for an unwired key. -/
def unsetDemoted : EditKey := ⟨.demoted, rfl⟩

/- CHEAT 46 — a day-carrying estimate.  `NdDur` demands `noDays = true`, and
   `(Dur.simple 3 .days).noDays` is `false`: `est=3d` dies in `ndDur?` on the
   wire, and here at `rfl`.  The value class is bounded in the type, not in a
   comment. -/
def dayEst : NdDur := ⟨Field.Dur.simple 3 Field.DurUnit.days, rfl⟩

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 2): the JSON round trip's one
-- hypothesis door.  `jval_jemit` is the induction under `jparse_jemit`, and
-- the numeral is the one value whose end is decided by the byte after it, so
-- the lemma demands `notDigitStart rest = true`.  This block is that door
-- staying shut.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 47 — read a numeral that is followed by a digit as if it stopped.
   `jval_jemit` would give `7` then `7` reading back as `(7, "7")`; the guard
   is `notDigitStart ['7'] = true`, which is `false`, so `rfl` is an
   application type mismatch.  The evaluated truth is
   `the_jval_jemit_digit_guard_bites`: those bytes read as `77`. -/
theorem sevenThenSevenReadsAsSeven :
    jval 4 (jemit (JVal.num 7) ++ ['7']) = .ok (.num 7, ['7']) :=
  jval_jemit (.num 7) 4 ['7'] (by decide) rfl

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, step 5: gap 40's bridges).  The eight keys
-- wired through `guardWf` carry wf-bounded subtypes, so the bound is in the
-- type (R10), not in a comment.  The controls — `⟨[.item "m1".toList], rfl⟩`
-- and `⟨.named "ab".toList, rfl⟩` — were checked to compile, so each failure
-- below is the bound and not `rfl` giving up.  Everything below must FAIL to
-- compile.
-- ===========================================================================

/- CHEAT 48 — an `after:` with no dependencies.  §4.1 has no empty `after:`
   (`depsWf` demands a non-empty list of well-formed deps), and `parseDeps`
   never yields one; building the payload by hand is `rfl` against
   `depsWf [] = true`, an application type mismatch. -/
def emptyAfter : EditVal := .after ⟨[], rfl⟩

/- CHEAT 49 — a `loc:` name that is not one word.  `WordLoc` demands
   `locOk`, whose `locWordOk` conjunct refuses a space: written, `loc:a b`
   would read back as `loc:a` and a title word `b`.  The wire refuses it as
   `badValue loc`; here it is `rfl` against `locOk (.named "a b") = true`. -/
def spacedLoc : WordLoc := ⟨.named "a b".toList, rfl⟩

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-4 session, step 2): `ClosePolicy` is a table, and a
-- table is only as good as the check that a corrupted row fails.  Each cheat
-- below corrupts one row and restates, over the corrupted table, the bridge
-- Close.lean proves over the real one (`closeStamp_names_the_closed_grain`,
-- `closePolicy_copies_only_below_month`).  The controls are those theorems,
-- which compile.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 50 — a day close that stamps a week stamp.  Swap the day row's stamp
   rule for `isoWeek` and the stamp it names is a week's, so the month review's
   "≥ 2 stamps" cut list would count a day's leftovers as a week's.  `decide`
   evaluates the corrupted row and proves the equation false. -/
def dayRowStampsAWeek (g : Grain) : ClosePolicy :=
  if g = day then { closePolicy g with stamp := .isoWeek } else closePolicy g

theorem dayRowStampsAWeek_names_the_closed_grain :
    (stampRuleOf (dayRowStampsAWeek day).stamp 0).map Field.Stamp.grain = some day := by
  decide

/- CHEAT 51 — a month close that leaves a tombstone.  Give the month row the
   week row's `copy` and it would demote a record a second time, which §6.3's
   month row does not do and `KErr.alreadyDemoted` refuses; the bridge's
   statement over the corrupted table is false at `month`, and `decide` says
   so. -/
def monthRowCopies (g : Grain) : ClosePolicy :=
  if g = month then { closePolicy g with disposition := .copy } else closePolicy g

theorem monthRowCopies_copies_only_below_month :
    ∀ g : Grain, (monthRowCopies g).disposition = .copy → g ≠ month := by
  decide

/- CHEAT 52 — minutes with a zero denominator.  The report emits an integer
   numerator and denominator and the host divides (AGENTS §8.2 rule 4); an
   `Arith.Pos` whose denominator is `0` would hand the host a division by zero
   inside a verified report.  `Q.ok ⟨300, 0⟩` is `false`, so `rfl` cannot prove
   it `true`. -/
def reportMinutesOverZero : CloseEntry :=
  ⟨"m2".toList, week, .copy, 0, 2, some (.week 36), some ⟨⟨300, 0⟩, rfl⟩⟩

/- CHEAT 53 — a disposition decoded from a near-miss name.  `CloseDid.ofName?`
   accepts exactly the four constructor names; reading `moved` as `move` is a
   host silently defaulting an unknown variant, which rule 2 exists to stop. -/
theorem movedDecodesAsMove : CloseDid.ofName? "moved".toList = some .move := by
  decide

/- CHEAT 54 — a close that invents its instant.  `ReqCmd.close` takes the
   request's `now` and `blockMin`; a command built without them is not a
   `ReqCmd` at all, so a host-side default has nowhere to hide. -/
def closeWithoutNow : ReqCmd := .close week

/- CHEAT 55 — a fast checker that is not the checker.  `@[csimp]` lets the
   compiler run a twin in place of a definition, and Fast.lean uses it for every
   hot conjunct of `planWf` (README gap 62); the licence is the equality.  The
   fastest `normalized` there is skips the rank check, and it has no proof of
   being `normalized`, so the swap never reaches the compiled kernel —
   `@[implemented_by]` would have taken it on trust (R4). -/
def normalizedSkip (_ : PlanCore) : Bool := true

@[csimp] theorem normalized_eq_normalizedSkip : @normalized = @normalizedSkip := by
  funext p; rfl

-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, step 2: gap 55 closed — the owner's D7 and
-- D8).  A past-due `persist` line at a week close moves to `backlog.md # Overdue`,
-- and the month rule "an outcome carries no date" reads outcomes only.  Each cheat
-- below is a door the step narrowed or opened, restated over what it must not
-- admit; the controls are `a_dated_record_loads_and_a_dated_outcome_does_not` and
-- `a_dated_month_outcome_is_rejected` (56), `closePolicy_routes_overdue_only_at_week`
-- (57) and `CloseDid.ofName?_refuses_near_overdue` (58), which compile.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 56 — a dated outcome loads.  D8 exempted `# Demoted` records from the
   month rule and nothing else: a month file whose `# Outcomes` line carries a
   `due:` is still refused, `itemCheck: fileKindShape`.  `decide` evaluates the
   loader and proves the equation false. -/
theorem datedOutcomeLoads : loadsOk datedOutcomeWitness = true := by
  decide

/- CHEAT 57 — a month close that routes overdue lines.  D7 is §6.3's week row
   ("moved to `backlog.md#Overdue` instead"); a month row with the same column
   would pull a dated `# Demoted` record out of the month review into the backlog,
   which no clause of §6.3 says.  The bridge's statement over the corrupted table
   is false at `month`. -/
def monthRowRoutesOverdue (g : Grain) : ClosePolicy :=
  if g = month then { closePolicy g with overdue := .toBacklogOverdue } else closePolicy g

theorem monthRowRoutesOverdue_routes_only_at_week :
    ∀ g : Grain, (monthRowRoutesOverdue g).overdue = .toBacklogOverdue ↔ g = week := by
  decide

/- CHEAT 58 — the fork-point report's name decoded as the kernel's.  The Rust
   `CloseReport` listed `overdue_to_backlog`; the wire's name is the constructor's,
   `moveOverdue`, and `CloseDid.ofName?` accepts exactly the six.  A host reading
   the old name as the new would be defaulting an unknown variant (rule 2). -/
theorem overdueToBacklogDecodes : CloseDid.ofName? "overdue_to_backlog".toList = some .moveOverdue := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, step 3: README gap 22 closed — the owner's
-- D6).  `Core.parent` is a view of the line, and a dangling or cyclic `@parent`
-- refuses the whole tree by name.  Each cheat below is a door the step closed;
-- the controls, which compile, are `Core.parent` and `coreOfLine_parent` (59),
-- `the_parent_tree_loads` and `a_typod_parent_refuses_the_whole_tree_by_name`
-- (60), and `a_parent_cycle_refuses_the_whole_tree_by_name` (61).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 59 — the stored slot, back.  A `parent` field beside the line is a second
   reader of `@O2` (AGENTS §5.3), and before D6 it disagreed with every file that
   carried one: it was `none` while the line said `@O2`.  There is no slot for a
   record update to set; the parent is what the bytes say. -/
def parentSlotCheat (c : Core) (j : Id) : Core := { c with parent := some j }

/- CHEAT 60 — a typo'd parent loads.  Fork-point `tm check` reported an `@ghost`
   parent and let every other command run; D6 refuses the tree, by name.  `decide`
   evaluates the loader and proves the equation false. -/
set_option maxRecDepth 40000 in
theorem typoParentLoads : loadsOk parentTypoWitness = true := by
  decide

/- CHEAT 61 — a cycle reported as a dangling link.  Both links of the ouroboros
   resolve, so the name is `parentCycle`: the dangling lemma's hypothesis is false
   at the cycle witness, and the two refusals cannot be confused. -/
set_option maxRecDepth 40000 in
theorem cycleIsDangling :
    loadPlan parentCycleWitness =
      .error (jone "err" (jone "itemCheck" (.str "danglingParent".toList))) :=
  loadPlan_refuses_a_dangling_parent _ true (by decide)

-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, step 4: goal B3 — the week row's child fold,
-- refuted as additive and performed by §6.4's `max`).  Each cheat below is a door
-- the step closed; the controls, which compile, are
-- `close_week_does_not_add_a_dropped_child_to_its_parent` (62),
-- `closePolicy_drops_children_only_at_week` (63), `CloseDid.ofName?_refuses_near_fold`
-- (64), `the_week_close_folds_dropped_children_on_a_loaded_plan` (65) and `close_dom`
-- with `close_week_drops_a_child_with_its_parent` (66).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 62 — the additive fold goal B3 stated.  `^p2` (`6b`) with its dropped `1b`
   subtask `^c3` would carry 350 minutes; §6.4's parent estimate already covers its
   decomposition, and the record reads 300.  `decide` runs the close on the loaded
   witness and proves the equation false. -/
set_option maxRecDepth 40000 in
theorem additiveFoldHolds :
    foldClosed (fun q => (q.val.store.get "p2".toList).map (fun f => remainingOf 50 f.val.line)) =
      some (some 350) := by
  decide

/- CHEAT 63 — a month close that drops children.  §6.3's child rule is the week row's;
   a month row with the same column would fold a `# Demoted` record's children into it
   at the month review's cut.  The bridge's statement over the corrupted table is false
   at `month`. -/
def monthRowDropsChildren (g : Grain) : ClosePolicy :=
  if g = month then { closePolicy g with children := .dropIntoParent } else closePolicy g

theorem monthRowDropsChildren_only_at_week :
    ∀ g : Grain, (monthRowDropsChildren g).children = .dropIntoParent ↔ g = week := by
  decide

/- CHEAT 64 — the fork-point report's list decoded as the kernel's name.  The Rust
   `CloseReport` listed `dropped_children`; the wire's name is the constructor's,
   `dropIntoParent`, and `CloseDid.ofName?` accepts exactly the nine. -/
theorem droppedChildrenDecodes : CloseDid.ofName? "dropped_children".toList = some .dropIntoParent := by
  decide

/- CHEAT 65 — a fold that forgets the stale parent.  `^p1` (`2b`) had `2b + 1b` of
   subtasks dropped with it; a close that dropped them and left the record at 100
   minutes would lose 50 minutes of open work (§0 principle 6).  The record reads
   150. -/
set_option maxRecDepth 40000 in
theorem staleParentKeepsItsEstimate :
    foldClosed (fun q => (q.val.store.get "p1".toList).map (fun f => remainingOf 50 f.val.line)) =
      some (some 100) := by
  decide

/- CHEAT 66 — the fork point's `remove_line_in`: a dropped child deleted from the plan.
   The kernel removes no entity (`close_dom`); `^c3` is still there, `[~]`. -/
set_option maxRecDepth 40000 in
theorem aDroppedChildIsDeleted :
    foldClosed (fun q => (q.val.store.get "c3".toList).isSome) = some false := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final, repair: the mixed pair's order and `NhMm`
-- in the fold).  The controls, which compile, are `unitValue_renderDur` and
-- `the_week_close_folds_an_hours_and_minutes_child` (67, 68) and
-- `the_mixed_pair_keeps_its_order_on_the_loaded_witness` (69).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 67 — the stage-one reader blind to `NhMm`, as it was.  `unitValue` reads
   `2h30m` as 150; `decide` proves the equation false. -/
theorem hoursAndMinutesReadNothing : unitValue 50 "2h30m".toList = none := by
  decide

/- CHEAT 68 — the fold that loses an `NhMm` child.  `^p1` (`6b`) with `5h + 2h30m`
   dropped would keep a record with only its stamp, 150 minutes short of its
   children; the record carries `est:9b`. -/
set_option maxRecDepth 40000 in
theorem hoursAndMinutesChildIsLost :
    closedFileLines week closeHmWitness = some
      [["# Milestones".toList,
        "- [-] 6b Parent project ^p1".toList,
        "# Tasks".toList,
        "- [~] 5h Part one @p1 ^c1".toList,
        "- [~] 2h30m Part two @p1 ^c2".toList],
       ["# Outcomes".toList, "# Demoted".toList,
        "- [-] 6b Parent project demoted:W36 ^p1".toList]] := by
  decide

/- CHEAT 69 — the mixed pair inverted.  A close that left `^p1`'s tombstone below the
   child `^c1` it dropped would reorder the week file it closed; the tombstone stands
   above. -/
set_option maxRecDepth 40000 in
theorem mixedPairInverts :
    foldClosed (fun q => match q.val.store.get "p1".toList, q.val.store.get "c1".toList with
      | some fp, some fc =>
        fp.val.archiveSite.map (fun t => decide (t.doc = fc.val.live.doc ∧ fc.val.live.rank < t.rank))
      | _, _ => none) = some (some true) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5 step 1: §6.4's `remaining` and §5.4's series
-- head).  The controls, which compile, are in Boundary.lean:
-- `remaining_reads_the_est_key_over_the_leading_estimate_on_a_loaded_plan` (70),
-- `remaining_of_a_settled_line_is_zero_on_a_loaded_plan` (71),
-- `remaining_sums_two_children_on_a_loaded_plan` (72),
-- `remaining_reads_dur_on_a_loaded_plan` (73) and
-- `the_series_head_skips_a_settled_member_on_a_loaded_plan` (74).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 70 — C1 re-entering through the rollup.  A rollup that read the leading
   estimate over the `est:` key would give `^a1` (`2b … est:30m`) its 120 minutes at a
   60-minute block; it has 30. -/
set_option maxRecDepth 40000 in
theorem theLeadingEstimateWinsOverTheKey : remainingMin 60 treePlan "a1".toList = 120 := by
  decide

/- CHEAT 71 — a Done line still owing its estimate.  `^d1` is `[x] 1b … est:40m`;
   fork-point `remaining_inner` answers `Some(0)` for a closed item, and so does the
   kernel. -/
set_option maxRecDepth 40000 in
theorem aDoneLineKeepsItsEstimate : remainingMin 60 treePlan "d1".toList = 40 := by
  decide

/- CHEAT 72 — a parent with no estimate reading nothing.  `^p1` writes no estimate;
   its children `30m` and `20m` sum to 50. -/
set_option maxRecDepth 40000 in
theorem aParentWithNoEstimateReadsNothing : remainingMin 60 treePlan "p1".toList = 0 := by
  decide

/- CHEAT 73 — `dur:` ignored.  `^w1` writes only `dur:30m`; `Item::own_remaining`
   reads it, and so does the kernel. -/
set_option maxRecDepth 40000 in
theorem aDurOnlyLineReadsNothing : remainingMin 60 treePlan "w1".toList = 0 := by
  decide

/- CHEAT 74 — the settled volume kept active.  `^v1` is `[x]`; the head of
   `## series:vols` is the next open member, `^v2`. -/
set_option maxRecDepth 40000 in
theorem theSettledVolumeIsTheHead : seriesHead treePlan 0 "vols".toList = some "v1".toList := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5 step 2: §7.1's priority, §7.2's rule table and
-- §7.4's hysteresis).  The controls, which compile, are in Priority.lean and
-- Boundary.lean: `prio_of_hot_is_zero` (75), `hysteresis_holds_one_step_back` (76),
-- `hysteresis_never_delays_hot` (77), `binsOf?_refuses_unsorted_edges` (78),
-- `rawPrio_of_pure_rank` (79), `finalPrio_of_an_optional` (80),
-- `zero_need_on_zero_capacity_is_hot` (81), `flooring_the_mixture_changes_the_bin`
-- (82) and `prio_reads_the_root_priority_on_a_loaded_plan` (83).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 75 — a `!4` root pushing a HOT item off the front.  §7.2: HOT is `p = 0`,
   whatever `k` is. -/
theorem hotYieldsToTheRootPriority : prio 4 Arith.Bin.hot = 4 := by
  decide

/- CHEAT 76 — hysteresis letting a four-step improvement through.  Yesterday `5`, raw
   `1`: §7.4 holds it at `4`. -/
theorem hysteresisLetsFourStepsThrough : hysteresis 5 1 = 1 := by
  decide

/- CHEAT 77 — hysteresis delaying HOT.  Yesterday `3`, raw `0`: "unless the new value
   is 0", so `0`, not `2`. -/
theorem hysteresisDelaysHot : hysteresis 3 0 = 2 := by
  decide

/- CHEAT 78 — gap 27's loader accepting swapped edges.  `[1/10, 1/2]` is antitone but
   not §7.1's ladder; `binsOf?` refuses it. -/
theorem swappedBinsAccepted : (binsOf? [⟨1, 10⟩, ⟨1, 2⟩]).isSome = true := by
  decide

/- CHEAT 79 — a corrupted row of §7.2's table: pure rank as `k + 3`.  The row is
   `k + 2`. -/
theorem theRankRowIsKPlusThree : (rowTable .rank).1 = .kPlus (.plus 3) := by
  decide

/- CHEAT 80 — a corrupted column of §7.2's table: `optional.md` damped by hysteresis.
   §7.2 pins it at `5` (fork-point `priority::compute`'s deviation 5). -/
theorem anOptionalIsDamped : (rowTable .optional).2 = true := by
  decide

/- CHEAT 81 — gap 25 decided the float's way.  `0/0` at a rational availability is
   HOT, not the lowest bin. -/
theorem zeroOverZeroIsTheLowestBin : binOfQ Arith.defaultBins 0 (Arith.posOfNat 0) = .plus 3 := by
  decide

/- CHEAT 82 — D10's mixture floored.  `156½` minutes and `156` put a 78-minute need in
   different bins. -/
theorem theMixtureMayBeFloored :
    binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.mkPos 313 2 (by decide))
      = binOfScaledQ Arith.defaultBins Arith.safety 60 (Arith.posOfNat 156) := by
  decide

/- CHEAT 83 — §7.1's `k` read as the default instead of the root's `!k`.  `^t1`'s root
   `^O1` writes `!1`. -/
set_option maxRecDepth 40000 in
theorem theRootPriorityIsIgnored : rootK parentTreePlan.val specDefaultPrio "t1".toList = 3 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5 step 3: §7.3's EDF reservation pass over D10's
-- rational capacity).  Banner added by the stage-5 repair; cheats 84-90 were
-- committed at fea3f81 under the step-2 banner above.  The controls, which
-- compile, are in Capacity.lean and Boundary.lean:
-- `reserve_takes_the_best_levels_earliest` (84),
-- `edf_spends_before_the_deadline_and_not_after_on_a_witness` (85, 86),
-- `edf_serves_the_earlier_deadline_first_on_a_witness` (87, 88),
-- `flooring_the_capacity_changes_the_verdict` (89), `denOf?_refuses_zero` (90)
-- and `edf_serves_a_loaded_plans_needs_earliest_deadline_first`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 84 — `capacity::reserve`'s inner loop run upward: the lowest matching level
   spent first.  30 minutes at `ci ≥ 3` from `[0,0,0,60,60,60]` come off level 5. -/
theorem theLowestMatchingLevelGoesFirst :
    (reserveRest 8 3 [DayCapacity.ofLevels 7 [0, 0, 0, 60, 60, 60]] 30).map DayCapacity.levels =
      [[0, 0, 0, 30, 60, 60]] := by
  decide

/- CHEAT 85 — a later day spent before an earlier one.  Earliest day first. -/
theorem aLaterDayGoesFirst :
    (reserveRest 2 3 edfExampleCaps 30).map DayCapacity.levels =
      [[0, 0, 0, 60, 0, 0], [0, 0, 0, 30, 0, 0]] := by
  decide

/- CHEAT 86 — a reservation taken after the deadline.  A 90-minute need due on day 1
   finds 60 minutes and leaves day 2 whole; it does not borrow day 2's. -/
theorem aDayAfterTheDeadlineIsSpent :
    (edf Den.one edfExampleCaps [⟨90, 3, 1⟩]).map DayCapacity.levels =
      [[0, 0, 0, 0, 0, 0], [0, 0, 0, 30, 0, 0]] := by
  decide

/- CHEAT 87 — the deadlines served in input order.  §7.3 sorts by due: day 1 first. -/
theorem inputOrderIsServed :
    (edfGrants Den.one edfExampleCaps edfExampleDeadlines).map (fun g => g.deadline.due) = [2, 1] := by
  decide

/- CHEAT 88 — the shortfall hidden.  The due-2 deadline is 30 minutes short, and says so. -/
theorem theShortfallIsHidden :
    (edfGrants Den.one edfExampleCaps edfExampleDeadlines).map (fun g => g.shortfall 1) = [0, 0] := by
  decide

/- CHEAT 89 — D10's mixture floored before the pass.  `30½ + 30½` minutes meet a 61-minute
   need; `30 + 30` do not, so §7.3's IMPOSSIBLE verdict differs. -/
theorem theMixtureMayBeFlooredForTheVerdict :
    (edfGrants halfDen mixtureCaps [⟨61, 4, 1⟩]).map (fun g => g.impossible halfDen) =
      (edfGrants Den.one flooredCaps [⟨61, 4, 1⟩]).map (fun g => g.impossible Den.one) := by
  decide

/- CHEAT 90 — a zero denominator accepted as the lookahead's unit (R10). -/
theorem aZeroDenominatorIsAccepted : (denOf? 0).isSome = true := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L1: the exact mixture,
-- `Lookahead.lean`).  Numbers are the design's reserved labels (design §16):
-- 108 and 109 are L1's; 117 is L5's label, taken here because the refutation it
-- inverts moved into L1 (README "Stage 5 D10 L1").  The merge renumbers.  The
-- controls, which compile, are in Lookahead.lean: `mix_at_zero_is_home` and
-- `mix_on_a_witness` (108), `mkWeight?_above_one` and `mkWeight?_on_witnesses`
-- (109), `mixing_before_the_budget_is_not_the_expectation` and
-- `mixing_before_the_budget_on_the_witness` (117).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 108 — D10's mixture with `w` and `capDen − w` swapped: the lounge weighed by
   `1 − p`.  At weight 0 the day must be home's, which has nothing at level 5. -/
def swappedMix (w : Look.Weight) (L H : Look.Hist) : Look.Hist := fun l =>
  (Look.capDen - w.val) * L l + w.val * H l

theorem theSwappedMixIsHomeAtZero :
    swappedMix Look.Weight.home (Look.histOf [0, 0, 0, 0, 0, 60]) (Look.histOf [0, 0, 0, 120, 0, 0]) 5
      = Look.capDen * Look.histOf [0, 0, 0, 120, 0, 0] 5 := by
  decide

/- CHEAT 109 — a weight above one accepted: `3/2` decoded as `1.5 · capDen`.  The type
   refuses the value, and `mkWeight?` refuses the pair by name. -/
def threeHalvesIsAWeight : Look.Weight := ⟨1500000000000000000, by decide⟩

theorem mkWeightAcceptsThreeHalves :
    (Look.mkWeight? 3 2).map Subtype.val = .ok 1500000000000000000 := by
  rfl

/- CHEAT 117 — mixing before the budget limit taken for the expectation.  Budget 60,
   lounge 60 at levels 5 and 4, home 120 at level 3, `p = ½`: the expected day keeps
   30 minutes at level 3, and the limited mixture keeps none. -/
theorem mixingBeforeTheBudgetIsTheExpectation :
    Look.mix Look.halfWeight (Look.limitHist 60 Look.budgetWitnessL) (Look.limitHist 60 Look.budgetWitnessH) 3
      = Look.limitHist (60 * Look.capDen) (Look.mix Look.halfWeight Look.budgetWitnessL Look.budgetWitnessH) 3 := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step A2: JSON gains an exact decimal;
-- gaps 42 and 43).  Numbered 119-121 because the design labels cheats 91-118
-- (its §16) and the D10 track numbers in parallel; the merge renumbers.  The
-- controls, which compile, are in Json.lean: `JVal.ofDec_plain` and
-- `jparse_reads_a_signed_decimal_as_dec` (119), `the_jval_jemit_fraction_guard_bites`
-- and `jval_jemit` over `numEnd` (120), and `jparse_reads_an_exponent_as_written`
-- (121).  CHEAT 47's guard is now `numEnd`, whose first conjunct is the
-- `notDigitStart` its comment names; it still fails for that reason.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 119 — a bare natural built as a decimal.  `7` would then have two values,
   `num 7` and `dec 7`, and `jparse` could return only one of them, so
   `jparse_jemit` would be false.  `JVal.dec` demands `d.plain = false`, and
   `⟨false, 7, [], none⟩.plain` is `true`: `rfl` is a type error. -/
def sevenAsADecimal : JVal := .dec ⟨⟨false, 7, [], none⟩, rfl⟩

/- CHEAT 120 — read a numeral followed by a fraction as if it stopped.
   `jval_jemit` would give `1` then `.5` reading back as `(1, ".5")`; the guard
   is `numEnd ['.', '5'] = true`, which is `false`, so `rfl` is an application
   type mismatch.  The old guard `notDigitStart` would have let it through;
   the evaluated truth is `the_jval_jemit_fraction_guard_bites`: `1.5`. -/
theorem oneThenAFractionReadsAsOne :
    jval 4 (jemit (JVal.num 1) ++ ['.', '5']) = .ok (.num 1, ['.', '5']) :=
  jval_jemit (.num 1) 4 ['.', '5'] (by decide) rfl

/- CHEAT 121 — an exponent marker with no digit.  The design's `JDec` stored the
   exponent as a sign and a digit list, where `some (false, [])` emits `1e`, which
   no reader takes back (`jparse_refuses_a_numeral_missing_a_digit`).  Here the
   exponent is a first digit and the rest, so the empty list is not an exponent. -/
def aBareExponentMarker : JDec := ⟨false, 1, [], some (false, [])⟩


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B1: instants, offsets and the
-- zone table in Cal.lean).  Numbered 91 and 92, the design's own labels for B1
-- (its §16); nothing in this checkout had taken them.  The D10 track numbers in
-- parallel and the merge renumbers.  The controls, which compile, are in
-- Cal.lean: `chicago_2026_offsets` and `offsetAt_reads_the_last_transition`
-- (91), `the_written_clock_is_not_the_instant_order` and `Instant.lt_irrefl`
-- (92).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 91 — a zone transition applied one second early.  Chicago springs
   forward at 2026-03-08T08:00:00Z; at 07:59:59Z the last transition at or before
   the instant is none, so `offsetAt` reads the base −06:00
   (`offsetAt_reads_the_last_transition`, `chicago_2026_offsets`), and claiming
   −05:00 there is false: `decide` refuses it. -/
theorem aTransitionAppliedOneSecondEarly :
    Cal.offsetAt Cal.chicago ⟨63908553599, 0⟩ = ⟨true, 18000⟩ := by
  decide

/- CHEAT 92 — two stamps of one instant ordered by their written clocks.
   `2026-09-07T22:00:00-05:00` reads earlier on the clock than
   `2026-09-08T03:00:00+00:00`, but local time minus offset is one UTC second
   for both (`the_written_clock_is_not_the_instant_order`), and no instant is
   before itself (`Instant.lt_irrefl`): `decide` refuses the order. -/
theorem twoStampsOfOneInstantOrderedByTheirClocks :
    (⟨(Cal.utcSecAt ⟨true, 18000⟩ (Cal.toDay ⟨2026, 9, 7⟩ * 86400 + 22 * 3600)).getD 0, 0⟩ :
        Cal.Instant)
      < ⟨(Cal.utcSecAt Cal.Offset.utc (Cal.toDay ⟨2026, 9, 8⟩ * 86400 + 3 * 3600)).getD 0, 0⟩ := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L2: the day's window, E7, in
-- `Lookahead.lean`).  Numbers 110 and 111 are the design's own L2 labels (its
-- §16); nothing in this checkout had taken them.  The D9 track numbers in
-- parallel and the merge renumbers.  The controls, which compile, are in
-- Lookahead.lean: `the_window_end_is_not_the_least_solution_over_walls_wholly_inside`
-- and `the_window_end_is_the_least_solution` (110),
-- `the_window_end_solves_the_equation` and `overlapping_walls_count_once` (111).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 110 — walls counted only when wholly inside the window (Goals.lean
   STAGE 6's `wallsInside`).  Arrival 07:00, eight hours, cap 19:00, a wall
   14:50–15:50: the stage-6 equation is solved at 15:00, because the wall is not
   wholly inside `[07:00, 15:00]`.  The fork, and `windowEnd`, extend the window
   by the wall's whole hour to 16:00, so claiming 15:00 is false: `decide`
   refuses it. -/
theorem theWindowEndCountsOnlyWallsWhollyInside :
    Look.windowEnd 420 480 1140 [(890, 950)]
      = min (420 + 480) 1140 + Look.wallsInside 420 900 [(890, 950)] := by
  decide

/- CHEAT 111 — overlapping walls not merged before the walk.  Walls 10:00–11:40
   and 10:50–12:30 each extend the window by their own length, 200 minutes, where
   their union is 150: the unmerged walk ends at 18:20 and the least solution of
   E7 at 17:30 (`the_window_end_solves_the_equation`,
   `overlapping_walls_count_once`).  `decide` refuses the equality. -/
def unmergedWindowEnd (a wm wc : Nat) (ws : List (Nat × Nat)) : Nat :=
  (Look.sortByStart (Look.clipWalls a ws)).foldl Look.extendStep (Look.windowBase a wm wc)

theorem theUnmergedWalkIsTheWindowEnd :
    unmergedWindowEnd 420 480 1140 [(650, 750), (600, 700)]
      = Look.windowEnd 420 480 1140 [(650, 750), (600, 700)] := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L3: the slot cut in
-- `Lookahead.lean`).  Numbers 112 and 113 are the design's own L3 labels (its
-- §16); nothing in this checkout had taken them.  The D9 track numbers in
-- parallel and the merge renumbers.  Each cheat is the real loop with one line
-- changed, run over the same free stretches, and claimed equal to `cutSlots` on
-- a fork-test window.  The controls, which compile, are in Lookahead.lean:
-- `a_cut_never_ends_on_a_break` and `every_break_is_followed_by_a_slot` (112),
-- `a_cut_never_ends_on_a_break` and `cutSlots_short_block_is_at_least_min_last`
-- (113).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 112 — a stretch that ends on a break: the loop places a due break
   without checking that `min_last` still fits after it.  From 07:00 to 09:45
   the break due at 09:00 leaves 25 minutes, so the fork places neither it nor a
   block (`a_cut_never_ends_on_a_break`); the cheat places the break and ends
   the stretch on it, which `every_break_is_followed_by_a_slot` forbids.
   `decide` refuses the equality.  (The design names the §4.3 cut as this
   cheat's witness, but the guard never fires on that day, so the cheat and the
   fork agree there; see the README's L3 block.) -/
def cutStretchEndingOnABreak (c : Look.CutCfg) (stop : Nat) :
    Nat → Nat → Nat → Look.CutAcc → Nat × Look.CutAcc
  | 0, _, k, acc => (k, acc)
  | fuel + 1, t, k, acc =>
    if t < stop then
      if (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k then
        cutStretchEndingOnABreak c stop fuel (t + 60 * c.breakMin) 0
          (acc.1, (t, t + 60 * c.breakMin) :: acc.2)
      else if t + 60 * c.blockMin ≤ stop then
        cutStretchEndingOnABreak c stop fuel (t + 60 * c.blockMin) (k + 1)
          (⟨t, t + 60 * c.blockMin, .block⟩ :: acc.1, acc.2)
      else if t + 60 * c.minLast ≤ stop then
        cutStretchEndingOnABreak c stop fuel stop (k + 1) (⟨t, stop, .short⟩ :: acc.1, acc.2)
      else (k, acc)
    else (k, acc)

def cutEndingOnABreak (c : Look.CutCfg) (lo hi : Nat) (walls : List (Nat × Nat)) : Look.Cut :=
  let r := (Look.freeIntervals lo hi walls).foldl
    (fun acc iv => cutStretchEndingOnABreak c iv.2 (iv.2 - iv.1 + 1) iv.1 acc.1 acc.2) (0, ([], []))
  ⟨r.2.1.reverse, r.2.2.reverse⟩

theorem aStretchEndsOnABreak :
    cutEndingOnABreak Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 585) []
      = Look.cutSlots Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 585) [] [] 0 := by
  decide

/- CHEAT 113 — the short last block dropped at exactly `min_last`: the loop
   keeps a tail only when it is strictly longer than `min_last`.  From 07:00 to
   09:50 the fork places the break at 09:00 and a 30-minute short block after it
   (`a_cut_never_ends_on_a_break`; `cutSlots_short_block_is_at_least_min_last`
   allows exactly `min_last`); the cheat drops the block and so ends on the
   break.  `decide` refuses the equality. -/
def cutStretchDroppingAtMinLast (c : Look.CutCfg) (stop : Nat) :
    Nat → Nat → Nat → Look.CutAcc → Nat × Look.CutAcc
  | 0, _, k, acc => (k, acc)
  | fuel + 1, t, k, acc =>
    if t < stop then
      if (0 < c.breakAfter ∧ 0 < c.breakMin) ∧ c.breakAfter ≤ k then
        if stop < t + 60 * c.breakMin + 60 * c.minLast then (k, acc)
        else cutStretchDroppingAtMinLast c stop fuel (t + 60 * c.breakMin) 0
          (acc.1, (t, t + 60 * c.breakMin) :: acc.2)
      else if t + 60 * c.blockMin ≤ stop then
        cutStretchDroppingAtMinLast c stop fuel (t + 60 * c.blockMin) (k + 1)
          (⟨t, t + 60 * c.blockMin, .block⟩ :: acc.1, acc.2)
      else if t + 60 * c.minLast < stop then
        cutStretchDroppingAtMinLast c stop fuel stop (k + 1) (⟨t, stop, .short⟩ :: acc.1, acc.2)
      else (k, acc)
    else (k, acc)

def cutDroppingAtMinLast (c : Look.CutCfg) (lo hi : Nat) (walls : List (Nat × Nat)) : Look.Cut :=
  let r := (Look.freeIntervals lo hi walls).foldl
    (fun acc iv => cutStretchDroppingAtMinLast c iv.2 (iv.2 - iv.1 + 1) iv.1 acc.1 acc.2) (0, ([], []))
  ⟨r.2.1.reverse, r.2.2.reverse⟩

theorem theShortBlockDroppedAtMinLast :
    cutDroppingAtMinLast Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 590) []
      = Look.cutSlots Look.CutCfg.shipped (Look.onTheSpecDay 420) (Look.onTheSpecDay 590) [] [] 0 := by
  decide



-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L4: energy and the budget limit
-- in `Lookahead.lean`).  Numbers 114, 115 and 116 are the design's own L4 labels
-- (its §16); nothing in this checkout had taken them.  The D9 track numbers in
-- parallel and the merge renumbers.  Each cheat is the real function with one
-- step changed, claimed to agree with the fork on a fork-test input.  The
-- controls, which compile, are in Lookahead.lean: `futureEnergy_home_is_capped`
-- and `energize_applies_the_home_cap` (114), `the_bucket_reads_seconds` and
-- `the_bucket_reads_seconds_on_the_spec_day` (115), `buckets_clamp` and
-- `predict_uses_the_learned_curve` (116).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 114 — no home cap: a future home day's slot energy is the prediction
   itself.  At 08:00 on the spec day, woken at 06:05, the shipped home prior is
   `1-4`'s 4, above `home_max_ci = 3`, which the fork's `cap_for_location` (and
   `futureEnergy_home_is_capped`) forbid.  `decide` refuses the claim. -/
def futureEnergyWithoutTheHomeCap (c : Look.Curves) (_homeMax : Nat) (loc : Look.Loc)
    (wake t : Cal.Instant) : Fin 6 :=
  Look.predictAt c loc.curve (Look.hswAt wake t)

theorem theHomeCapDropped :
    (futureEnergyWithoutTheHomeCap Look.Curves.shipped 3 .home ⟨Look.onTheSpecDay 365, 0⟩
      ⟨Look.onTheSpecDay 480, 0⟩).val ≤ 3 := by
  decide

/- CHEAT 115 — hours since wake from whole minutes: the wake and the slot are
   read as clock minutes before subtracting.  Woken at 06:05:40, a slot at 07:05
   is 3,560 seconds away, `hsw` 0.99 and bucket 0 in the fork; whole minutes say
   60 and bucket 1 (CRIT 6).  `decide` refuses the equality. -/
def hswFromWholeMinutes (wake t : Cal.Instant) : Int :=
  Look.hsw100 (60 * ((t.sec / 60 : Nat) - (wake.sec / 60 : Nat) : Int))

theorem hoursSinceWakeFromWholeMinutes :
    Look.bucket (hswFromWholeMinutes ⟨Look.onTheSpecDay 365 + 40, 0⟩ ⟨Look.onTheSpecDay 425, 0⟩)
      = Look.bucket (Look.hswAt ⟨Look.onTheSpecDay 365 + 40, 0⟩ ⟨Look.onTheSpecDay 425, 0⟩) := by
  decide

/- CHEAT 116 — the hours-since-wake bucket without its clamp to `0..11`: the
   learned curve is indexed by `floor(hsw)` itself.  At 30 hours the fork's
   `Model::energy_at` reads the fixture lounge curve's last entry, 2
   (`predict_uses_the_learned_curve`); the unclamped index 30 is past the
   curve's 12 entries and reads nothing.  `decide` refuses the equality. -/
def bucketWithoutTheClamp (h : Int) : Nat := if h ≤ 0 then 0 else h.toNat / 100

def learnedWithoutTheClamp (energy : List (List Char × List Nat)) (curve : List Char) (h : Int) :
    Option Nat :=
  (Look.curveLookup energy curve).bind (fun c => c[bucketWithoutTheClamp h]?)

theorem theBucketWithoutItsClamp :
    learnedWithoutTheClamp Look.fixtureEnergy Look.loungeKey 3000
      = Look.learnedLevel Look.fixtureEnergy Look.loungeKey 3000 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B2: the log's timestamps in
-- `Stamp.lean`).  The design's §16 gives B2 no cheat label, so 126 and 127 are
-- taken above the highest number in this checkout (125, W-1's repair); the D10
-- track numbers in parallel and the merge renumbers.  The controls, which
-- compile, are in Stamp.lean: `renderStamp_is_fmt_timestamp` (126) and
-- `a_leap_second_stamp_is_before_the_next_second` with `stampBefore_iff` (127).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 126 — a UTC stamp written with `Z`.  The fork's `fmt_timestamp` is
   `to_rfc3339_opts(SecondsFormat::Secs, false)`, and `use_z = false` writes
   UTC as `+00:00` (`renderStamp_is_fmt_timestamp`).  Claiming the writer's
   bytes for `2026-09-08T03:00:00Z` end in `Z` is false: `decide` refuses it. -/
theorem aUtcStampWrittenWithZ :
    LogStamp.renderStamp ⟨⟨63924433200, 0⟩, by decide⟩ ⟨⟨false, 0⟩, by decide⟩ =
      ['2','0','2','6','-','0','9','-','0','8','T','0','3',':','0','0',':','0','0','Z'] := by
  decide

/- CHEAT 127 — stamps ordered by nanosecond counts.  chrono orders a
   `DateTime<FixedOffset>` by its UTC `(secs, frac)`, and a leap second
   `2016-12-31T23:59:60.5Z` is before `2017-01-01T00:00:00Z`
   (`a_leap_second_stamp_is_before_the_next_second`).  An order by
   `Instant.nanos` puts it after, so claiming that order agrees with
   `stampBefore` on this pair is false (carried note 1): `decide` refuses it. -/
def stampBeforeByNanos (a b : Cal.VInstant × Cal.VOffset) : Bool :=
  decide (a.1.val.nanos < b.1.val.nanos)

theorem stampsOrderedByNanoseconds :
    stampBeforeByNanos (⟨⟨63618825599, 1500000000⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
        (⟨⟨63618825600, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
      = LogStamp.stampBefore (⟨⟨63618825599, 1500000000⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩)
        (⟨⟨63618825600, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B3: the typed event grammar in
-- `Log.lean`).  The design's §16 labels these 93, 94 and 106; those numbers are
-- the design's reserved-unused ones (W-1's repair left them unused), so the
-- block takes 128, 129 and 130, above the highest number in this checkout (127,
-- B2).  The D10 track numbers in parallel and the merge renumbers.  The
-- controls, which compile, are in Log.lean: `an_unknown_tag_is_never_a_warning`
-- with `malformed_line_9_is_an_unknown_mood` (128),
-- `a_known_event_is_never_read_as_unknown` with
-- `malformed_line_5_is_a_done_with_est_min_sixty` (129), and
-- `an_out_of_range_numeral_warns_even_in_an_unknown_event` (130).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 128 — an unknown tag read as a warning.  A reader that refuses every
   tag it does not know turns the fork's `{"ev":"mood","level":3}` (the fixture's
   line 9, an `Event::Unknown`) into a warning.  Claiming that reader keeps
   `an_unknown_tag_is_never_a_warning` on that line is false: once the kernel's
   verdict is rewritten in (`malformed_line_9_is_an_unknown_mood`), `decide`
   refuses it. -/
def readLineRefusingUnknownTags (n : Nat) (seg : Option (List Char)) : Log.Verdict :=
  match Log.readLine n seg with
  | .entry ⟨_, _, _, .unknown _ _⟩ => .warn n .notAnObject
  | v => v

theorem anUnknownTagReadAsAWarning :
    readLineRefusingUnknownTags 9 (some Log.malformedLine9) ≠ .warn 9 .notAnObject := by
  simp only [readLineRefusingUnknownTags, Log.malformed_line_9_is_an_unknown_mood.1, Log.malformedEntry9]
  decide

/- CHEAT 129 — a known event with a bad field read as `unknown`.  serde's
   derived `Known` never falls back: `est_min:"sixty"` on a `done` is the
   warning `event "done": est_min: …`.  A reader that files a bad payload under
   `unknown` instead reads the fixture's line 5 as an unknown event, so claiming
   `a_known_event_is_never_read_as_unknown` of it is false: `decide` refuses it on
   the line's value (never its 96 characters). -/
def readObjectFallingThroughToUnknown (n : Nat) (kvs : List (List Char × JVal)) : Log.Verdict :=
  match Log.readObject n kvs with
  | .warn _ (.badField _) =>
    match Log.readT kvs, Log.lastVal kvs Log.kEv with
    | .ok (t, o), some (.str tag) => .entry ⟨n, t, o, .unknown tag []⟩
    | _, _ => .warn n .noEv
  | v => v

def malformedPairs5 : List (List Char × JVal) :=
  match Log.malformedValue5 with
  | .obj kvs => kvs
  | _ => []

theorem aBadFieldReadAsUnknown :
    (match readObjectFallingThroughToUnknown 5 malformedPairs5 with
     | .entry e => e.ev.isUnknown
     | _ => false) = false := by
  decide

/- CHEAT 130 — `finiteF64` applied only to `hsw` (CRIT 15).  The fork collects
   the whole line as a `Map<String, Value>` before it reads a field, so `1e400`
   under any key of any event fails the line.  A reader that checks only `hsw`
   reads `{"t":…,"ev":"mood","x":1e400}` as an entry; claiming it warns
   `numberOutOfRange` there, as
   `an_out_of_range_numeral_warns_even_in_an_unknown_event` says the kernel does,
   is false: `decide` refuses it. -/
def readValueCheckingOnlyHsw (n : Nat) (v : JVal) : Log.Verdict :=
  match v with
  | .obj kvs =>
    match Log.lastVal kvs ['h','s','w'] with
    | some (.dec d) => if Log.finiteF64 d.val then Log.readObject n kvs else .warn n .numberOutOfRange
    | _ => Log.readObject n kvs
  | _ => .warn n .notAnObject

def moodOutOfRangeValue : JVal :=
  .obj [(Log.kT, .str ['2','0','2','6','-','0','9','-','0','7','T','0','8',':','0','0',':','0','0','-','0','5',':','0','0']),
    (Log.kEv, .str ['m','o','o','d']), (['x'], .dec ⟨⟨false, 1, [], some (false, 4, [0, 0])⟩, rfl⟩)]

theorem finiteF64CheckedOnlyAtHsw :
    (match readValueCheckingOnlyHsw 1 moodOutOfRangeValue with
     | .warn _ .numberOutOfRange => true
     | _ => false) = true := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step B4: the `tz` and `log` sections
-- of the request, Boundary.lean).  The design's §16 names no B4 cheat; these two
-- guard its R10 constructors.  They take 131 and 132, above the highest number in
-- this checkout (130, B3); the D10 track numbers in parallel and the merge
-- renumbers.  The controls, which compile, are in Boundary.lean:
-- `readTz_refuses_by_name` (131) and
-- `mkLogReq?_refuses_a_render_line_outside_the_tail` (132).
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 131 — a zone table built without `Cal.mkTz?`.  Rust sends the
   transitions; a decoder that wraps them in a `Cal.Tz` by asserting the proof
   would let two transitions out of order through, and `offsetAt` would read the
   last one written rather than the last one in time.  `Cal.Tz` is a subtype of
   `TzTable.wf = true`, so the assertion is a type error: `rfl` cannot prove
   `false = true`. -/
def unsortedZone : Cal.Tz :=
  ⟨⟨['k'], ⟨false, 0⟩, [(⟨200, 0⟩, ⟨false, 3600⟩), (⟨100, 0⟩, ⟨false, 0⟩)]⟩, rfl⟩

/- CHEAT 132 — a render line outside the tail answered.  A request whose tail is
   line 2 alone asks for line 1; `mkLogReq?` refuses it `renderNotInTail`, so
   claiming the request is accepted is false: `decide` refuses it. -/
theorem aRenderLineOutsideTheTailAccepted :
    (mkLogReq? ⟨2, [some ['x']], true, none, [1], false, Replay.utcZone⟩).toBool = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track, step L5: the lookahead in
-- `Lookahead.lean`).  Numbers 133 and 134 (126 and 127 on the branch, renumbered at the merge of
-- the D9 track's B2-B4, which took 126-132) were the next free numbers in this
-- checkout (the highest was 125, after W-1's repair).  The design's L5 label,
-- 117 (mixing before the budget limit), was taken by L1 and still fails there.
-- The D9 track numbers in parallel and the merge renumbers.  Each cheat is the
-- real function with one step changed, claimed to agree with the fork on a
-- fork-shaped input.  The controls, which compile, are in Lookahead.lean:
-- `a_future_day_reads_todays_wake_to_the_second` (133) and
-- `sunday_mixes_at_its_own_weight` (134).  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 133 — a future day's wake at whole minutes: `local_dt` of today's wake clock with
   its seconds dropped.  On Tuesday 2026-09-08 with a 07:05 arrival and a wake at 06:05:40,
   the fork puts the 07:05 block at 0.99 h (the lounge's `0-1`, level 4) and keeps 180
   minutes at level 5; whole minutes put it at 1.00 h (level 5) and keep 240.  `decide`
   refuses the equality. -/
def pureDayWakingOnTheMinute (I : Look.Input) (loc : Look.Loc) (d : Nat) : Look.Hist :=
  Look.limitHist (Look.budgetMinOf I.day) (Look.histOf' (Look.energize I.curves I.homeMax loc
    (Cal.instantOf I.tz d ⟨I.wake.sec / 60 % 1440, Nat.mod_lt _ (by decide)⟩) (Look.dayCut I d).slots))

theorem aFutureWakeOnTheMinute :
    pureDayWakingOnTheMinute { Look.specInput with arrival := fun _ => 425, wake := ⟨6 * 3600 + 5 * 60 + 40, 0⟩ }
        .lounge 739866 5
      = Look.pureDay { Look.specInput with arrival := fun _ => 425, wake := ⟨6 * 3600 + 5 * 60 + 40, 0⟩ }
        .lounge 739866 5 := by
  decide

/- CHEAT 134 — every future day mixed at today's weekday's weight.  The fork reads
   `p_lounge_on(date.weekday())` for each date: on Sunday 2026-09-13 the shipped 0.4, where
   Monday's is 0.9.  The Sunday lounge day keeps 120 minutes at level 5, so the expected level
   5 is 48 minutes and the cheat's 108.  `decide` refuses the equality. -/
def dayOfAtTodaysWeight (I : Look.Input) (i : Nat) : DayCapacity :=
  if i = 0 then Look.ofHist I.today (Look.day0Hist I)
  else Look.mixDay (I.today + i) (I.weight (Cal.weekdayOf I.today))
    (Look.pureDay I .lounge (I.today + i)) (Look.pureDay I .home (I.today + i))

theorem everyDayAtTodaysWeight :
    (dayOfAtTodaysWeight Look.specInput 6).numAt 5 = (Look.dayOf Look.specInput 6).numAt 5 := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L6 (design §13.6, §14.8 row
-- L6): capacity on the wire.  Numbers 135, 136 and 137 (128-130 on the branch, renumbered at the merge)
-- were the next free
-- numbers in this checkout (the highest was L5's).  The D9 track numbers
-- in parallel and the merge renumbers.  The controls, which compile, are
-- `CapWire.readWeight_on_witnesses` and `readWeight_refuses_more_than_18_places`
-- (135), `Look.curveOk_refuses_an_unsorted_curve` and `CapWire.readPrior_on_witnesses`
-- (136), and `CapWire.the_lookahead_response_emits_in_build_order` (137), in
-- Lookahead.lean and Boundary.lean.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 135 — a lounge weight of 19 decimal places accepted on the wire.  `10^-19` sent as
   the digit strings `1` / `10000000000000000000` does not divide `capDen = 10^18` (D17), so
   the wire refuses it `weightPrecision`; `decide` refuses the claim that it reads. -/
theorem aWeightOf19PlacesReads :
    (CapWire.readWeight .model .tuesday (CapWire.pairJ (.str ['1'])
      (.str ['1', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']))).isOk
      = true := by
  decide

/- CHEAT 136 — a prior curve accepted out of `from` order.  Fork `StepFn::from_pairs` sorts a
   curve by its start, and `stepAt` reads it in that order; the wire refuses an unsorted curve
   (`badStep`) rather than sorting it silently.  `4+` before `1-4`: `decide` refuses. -/
theorem anUnsortedCurveIsAccepted :
    Look.curveOk [Look.Step.from 4 3, Look.Step.range 1 4 4] = true := by
  decide

/- CHEAT 137 — a unit count as a JSON number a double holds exactly.  One hour at `capDen`
   is `60 · 10^18` units, past `2^53`; that is why every unit count crosses as a digit string
   (D17, `unitsJson`).  `decide` refuses the bound. -/
theorem anHourOfUnitsFitsADouble : Look.capDen * 60 < 2 ^ 53 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, kernel half (design
-- §13.6, §13.8): the grants on the wire.  Numbers 138, 139 and 140 were the
-- next free numbers in this checkout (the highest was L6's 137).  The D9
-- track numbers in parallel and the merge renumbers.  The controls, which
-- compile, are `Look.grantAt_none_of_not_enters` and
-- `Look.an_answer_carries_a_grant_iff_its_candidate_enters` (138),
-- `Look.priorities_on_a_witness` and `Look.servedGrants_are_the_pass` (139),
-- and `CapWire.readCands_on_witnesses` (140), in Lookahead.lean and
-- Boundary.lean.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 138 — a wall enters the EDF pass.  Fork `priority::compute` reserves only for dated
   candidates that are not walls, not optional and have no placement window (gap 80): a wall is
   placed by §8.2 step 1 and would otherwise reserve its own hours twice.  `decide` refuses. -/
theorem aWallEntersThePass :
    (Look.entering Arith.safety [⟨['w'], 3, none, 60, some 1, false, true, false, false, false, false, none⟩]).length
      = 1 := by
  decide

/- CHEAT 139 — the pass served in request order.  `^a2` (due day 2) is listed before `^a1` (due
   day 1); served first it would see all 90 minutes.  EDF serves `^a1` first, so `^a2` sees the 51
   minutes `^a1` left (`Look.priorities_on_a_witness`).  `decide` refuses the 90. -/
theorem thePassServesInRequestOrder :
    ((Look.priorities Look.defaultBinsV Arith.safety specDefaultPrio true Look.witnessCaps Look.witnessCands)[1]?.bind
      (·.grant)).map (·.avail) = some (90 * Look.capDen) := by
  decide

/- CHEAT 140 — a candidate at energy level 6 reads.  A level is `0..5` (`levelOf?`, R10); the
   wire refuses the record by its position and key, `badCandidate 0 ci`.  `decide` refuses the
   claim that it reads. -/
theorem aCandidateAtLevelSixReads :
    (CapWire.readCands (CapWire.inCands (.bool true)
      [CapWire.candJ ['a'] (.num 6) .null (.num 30) CapWire.sep8J (.bool false) .null])).isOk = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, host half (design
-- §13.8; gap 79): the floor pass.  Numbers 141 and 142 are the next free
-- numbers in this checkout (the highest was 140; the D9 track's highest on
-- rebuild-on-lean is 137, read-only check).  The controls, which compile, are
-- `Look.prioritiesWithFloors_on_a_roomier_witness` and
-- `Look.a_floor_answer_reads_what_the_pass_left` (141), and
-- `Look.the_pass_wins_over_a_floor` and `Look.prioritiesWithFloors_on_a_witness`
-- (142), in Lookahead.lean.  Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 141 — a floor reads the capacity before the pass.  Fork `floor_pass` reads `work`, the
   capacity the EDF pass left (§7.1: "net of reservations made by earlier deadlines").  Over
   `witnessFloorCaps` the pass leaves 82 minutes, so `^r`'s need of 26 is the `+1` bin and `p = 2`; read
   against the 180 minutes before the pass it would be the `+2` bin, `p = 3`.  `decide` refuses. -/
theorem aFloorReadsTheCapacityBeforeThePass :
    ((Look.prioritiesWithFloors Look.defaultBinsV Arith.safety specDefaultPrio true Look.witnessFloorCaps
      Look.witnessFloors)[4]?).map (fun o => o.out.p) = some (some 3) := by
  decide

/- CHEAT 142 — a candidate that enters the pass is answered at its floor.  Fork `compute` takes
   `edf[i].or(floor)`: the grant wins.  `^a1` enters and carries a floor in `witnessFloors`; it is
   answered by its grant and carries no floor answer.  `decide` refuses. -/
theorem aGrantedCandidateIsAnsweredAtItsFloor :
    ((Look.prioritiesWithFloors Look.defaultBinsV Arith.safety specDefaultPrio true Look.witnessCaps
      Look.witnessFloors)[2]?).map (fun o => o.floor.isSome) = some true := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step C1: the undo mask in
-- `Replay.lean`).  Design §16's label 95 ("an undo that does not cancel itself").
-- Number 143 is the next free number in this checkout (the highest was 142,
-- the merge-back).  The control, which compiles, is `Replay.an_undo_never_survives`
-- with the witnesses `Replay.the_mask_ignores_isStateChange` and
-- `Replay.undo_mask_pairs_and_dangling_ported`.  Everything below must FAIL to
-- compile.
-- ===========================================================================

/- CHEAT 143 — an undo that does not cancel itself.  Fork `undo_mask` sets
   `cancelled[i] = true` for every undo, whether or not it finds a target, so a
   replay never sees one (`Replay.an_undo_never_survives`).  A mask step that
   erases the target and then keeps the undo on the stack claims the same law and
   cannot have it: over the one-line log `[undo{of:"note"}]` the undo survives.
   `decide` refuses. -/
def maskStepKeepingTheUndo (st : List Log.Entry) (e : Log.Entry) : List Log.Entry :=
  match e.ev with
  | .undo of_ id => e :: st.eraseP (Replay.matches of_ id)
  | _            => e :: st

theorem anUndoThatKeepsItselfNeverSurvives :
    ∀ u ∈ ([Replay.wEnt 1 (.undo Log.Kind.note.tag none)].foldl maskStepKeepingTheUndo []).reverse,
      u.ev.isUndo = false := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-14 (stage 5, D9 track, step C2: the day index in
-- `Replay.lean`).  Design §16's label 96 ("a 25-hour wake day").  Number 144 is
-- the next free number in this checkout (the highest was 143, C1).  The control,
-- which compiles, is `Replay.a_wake_day_is_shorter_than_a_day` with its witness
-- `Replay.a_wake_day_is_shorter_than_a_day_is_not_vacuous`.  Everything below
-- must FAIL to compile.
-- ===========================================================================

/- CHEAT 144 — a 25-hour wake day.  Fork `DayIndex::day_of` attributes an instant
   to its last wake's date only while `t.signed_duration_since(w) < 24 h`
   (`Replay.a_wake_day_is_shorter_than_a_day`).  A `dayOf` whose window is 25
   hours claims the same law and cannot have it: in Chicago, 06:35 on 2026-09-08
   is 24 h 30 min after the 06:05 wake of the 7th, a different date, and this
   `dayOf` still puts it on the 7th.  `decide` refuses. -/
def dayOfWithA25HourDay (z : Cal.Tz) (kw : List Cal.Instant) (t : Cal.Instant) : Nat :=
  match Replay.lastWakeLe kw t with
  | some w => if (Cal.durationBetween w t).1 < 90000 then Cal.localDate z w else Cal.localDate z t
  | none => Cal.localDate z t

theorem aWakeDayOf25HoursIsShorterThanADay :
    let kw := Replay.keptWakes Cal.chicago [⟨63924375900, 0⟩]
    let t : Cal.Instant := ⟨63924464100, 0⟩
    let w : Cal.Instant := ⟨63924375900, 0⟩
    Replay.lastWakeLe kw t = some w →
    dayOfWithA25HourDay Cal.chicago kw t = Cal.localDate Cal.chicago w →
    Cal.localDate Cal.chicago t ≠ Cal.localDate Cal.chicago w →
    (Cal.durationBetween w t).1 < 86400 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C3: the machine's effects in
-- `Replay.lean`).  Design §16 names no cheat for C3; this one guards the frame
-- law, which is what lets a sealed day refuse a line (G3).  Number 145 is the
-- next free number in this checkout (the highest was 144, C2).  The control,
-- which compiles, is `Replay.applyEffects_touches_only_named_keys`.  Everything
-- below must FAIL to compile.
-- ===========================================================================

/- CHEAT 145 — an effect that writes a key it does not name.  A header effect
   names its day (`Key.day d`).  One that also counts the entry in the
   bookkeeping writes `Key.global` too, and claims the frame law for itself:
   the value at `.global` is unchanged by an effect list whose keys do not
   include `.global`.  On the empty state it is changed, and `decide` refuses. -/
def applyEffectCountingOnHeader (st : Replay.State) : Replay.Effect → Replay.State
  | .header d h => { Replay.applyEffect st (.header d h) with global := ⟨st.global.lastEffective, st.global.entries + 1⟩ }
  | e => Replay.applyEffect st e

theorem aHeaderThatCountsTouchesOnlyItsDay :
    (applyEffectCountingOnHeader (Replay.State.init 1) (.header 739865 ⟨1, ['n'], none, false⟩)).valueAt .global
      = (Replay.State.init 1).valueAt .global := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C4: the completion family in
-- `Replay.lean`).  Design §16 names no cheat for C4; this one guards quirk
-- Q6(b) (gap 118), the owner's "keep: they answer different questions".  Number 146 is
-- the next free number in this checkout (the highest was 145, C3).  The
-- control, which compiles, is `Replay.an_instance_is_its_last_record_in_file_order`
-- with its witness `Replay.instances_and_last_done_order_differently`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 146 — an instance kept by instant.  The tempting "one definition"
   port of quirk Q6(b) keeps each instance's latest record by stamp, as
   `last_done` is kept.  Fork `instances[item][inst]` is a map overwrite: the
   last record in file order wins.  On a retro append (`routine s #1 done` at
   10:00, then the same instance `done` at 08:00) the instance kept by instant
   is the 10:00 record, and the fork's is the 08:00 one, so `decide` refuses. -/
def instanceKeptByInstant (item ins : List Char) (es : List Log.Entry) : Option Replay.InstRec :=
  es.foldl (fun acc e =>
    match Replay.instRecordOf item ins e, acc with
    | some r, some a => if a.t.1 < r.t.1 then some r else some a
    | some r, none => some r
    | none, acc => acc) none

theorem anInstanceKeptByInstantIsTheLastRecordInFileOrder :
    instanceKeptByInstant ['s'] ['#', '1']
        [Replay.bE 1 63924372000 (Replay.rDone ['s'] ['#', '1']), Replay.bE 2 63924364800 (Replay.rDone ['s'] ['#', '1'])]
      = ([Replay.bE 1 63924372000 (Replay.rDone ['s'] ['#', '1']),
          Replay.bE 2 63924364800 (Replay.rDone ['s'] ['#', '1'])].reverse.findSome? (Replay.instRecordOf ['s'] ['#', '1'])) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C5: the day header and records
-- family in `Replay.lean`).  Design §16 names no cheat for C5; this one guards
-- late binding, which §8.2 lists as a rule to port ("energy_obs_slept_is_the_days_
-- first_logged_sleep").  Number 147 is the next free number in this checkout (the
-- highest was 146, C4).  The control, which compiles, is
-- `Replay.energy_obs_slept_is_the_days_first_logged_sleep` with its witness
-- `Replay.an_energy_line_before_its_wake_reads_the_wakes_sleep`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 147 — an energy observation bound early.  The tempting port reads the
   day's sleep from what has been replayed so far, so an `energy` line logged
   before its day's `wake` (`lime wake 06:05` typed after `lime energy 4`) carries no
   sleep.  Fork `slept_by_day` is built from every surviving wake before the walk:
   on `[energy 09:00, wake 06:00 slept 420]` the observation reads 420, so
   `decide` refuses the early-bound `none`. -/
theorem anEnergyLineReadsOnlyTheWakesLoggedBeforeIt :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (.energy 3 4 (.nat 2) ['h']),
        Replay.bE 2 63924357600 (.wake 420 none)]).energy.map (·.sleptMin) = [none] := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C6: the facts, the observations
-- and the headers in `Replay.lean`).  Design §16's label 105 ("an observation
-- effect keyed `global` instead of its day", CRIT 9).  Number 148 is the next
-- free number in this checkout (the highest was 147, C5).  The control, which
-- compiles, is `Replay.every_dated_output_names_its_day_key`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 148 — an observation keyed `global`.  The tempting key for an energy
   observation is the all-time one, like `last_done`'s: the fit reads every
   observation.  But an observation is dated (it lives in its day's record, and a
   sealed day's record is written once), so a guard reading keys would miss a tail
   line writing an observation into a sealed day.  `every_dated_output_names_its_
   day_key` says the key names the date `Effect.day?` gives: on an observation of
   2026-09-07 (day 739865) the global key names no date, so `decide` refuses. -/
def keyObservationsGlobally : Replay.Effect → Replay.Key
  | .obs _ => .global
  | fx => fx.key

theorem anObservationKeyedGloballyNamesItsDay :
    (keyObservationsGlobally (.obs (.energy ⟨1, (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865, 3, 4, .nat 2, ['h'], none, none,
        none, false⟩))).date?
      = (Replay.Effect.obs (.energy ⟨1, (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865, 3, 4, .nat 2, ['h'], none, none, none,
        false⟩)).day? := by
  decide


-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step C7: the undo law in
-- `Replay.lean`).  Design §16's label 107 ("`undosFor` emitted oldest first").
-- Number 149 is the next free number in this checkout (the highest was 148, C6).
-- The control, which compiles, is `Replay.undoing_a_command_replays_the_log_without_it`
-- over `Replay.undosFor`, most recent first.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 149 — `undosFor` emitted oldest first.  The tempting port walks the
   recorded events in the order the command wrote them.  But an undo takes the
   most recent surviving match, so an older event's undo can take a newer event
   of the command: `event e` (no id) then `event e` with id `x`, undone oldest
   first, writes `undo{of:"event"}` first, which takes the newer (id `x`) event,
   and then `undo{of:"event", id:"x"}`, which finds nothing and dangles.  The
   older event survives, so the undone log's `(e, none)` record is not the empty
   log's, and `decide` refuses the undo law on it (with `L = M = []`, where
   `untouchedBy` holds). -/
def undosOldestFirst (E : List Log.Entry) (n : Nat) (t : Cal.VInstant) (o : Cal.VOffset) : List Log.Entry :=
  (E.zipIdx n).map (fun p => ⟨p.2, t, o, .undo p.1.ev.tag p.1.ev.primaryId⟩)

theorem undoingOldestFirstReplaysTheLogWithoutTheCommand :
    Replay.factsView (Replay.replay Replay.utcZone
        ([Replay.bE 1 63924368400 (.named ['e'] none), Replay.bE 2 63924368460 (.named ['e'] (some ['x']))]
          ++ undosOldestFirst [Replay.bE 1 63924368400 (.named ['e'] none),
            Replay.bE 2 63924368460 (.named ['e'] (some ['x']))] 3 Replay.undoStamp Replay.undoOffset))
        (.named ['e'] none)
      = Replay.factsView (Replay.replay Replay.utcZone []) (.named ['e'] none) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step W1: the checkpoint and the
-- sealed records in `Seal.lean`).  Design §16's labels 97 ("a view without
-- `lastDone` still satisfies the partition law on its minimal witness") and 98
-- ("`readCkpt` defaulting a missing `ledgerDay` to 0").  Numbers 150 and 151 are
-- the next free numbers in this checkout (the highest was 149, C7).  The
-- controls, which compile, are `Seal.a_log_sealed_anywhere_answers_as_its_replay`
-- with `Seal.the_last_done_outlives_the_seal_of_its_days`, and
-- `Seal.readCkpt_refuses_a_checkpoint_without_its_ledgerDay`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 150 — a view without `last_done`.  The tempting answer keeps no
   all-time `last_done` and reads it off the open days: the latest completed
   duration observation of the id on a day at or after the ledger day.  It
   agrees with the replay while a `done`'s day is open, which is why a law
   checked on a log sealed before its days still holds.  Sealed after both days
   (two `done x`, on the 7th and the 8th, sealed at 2026-10-12), the open days
   hold nothing, the view reads no `last_done`, and `decide` refuses the claim
   that it reads the replay's. -/
def lastDoneFromOpenDays (v : Seal.Answer) (i : Log.Id) : Option Replay.At :=
  Replay.maxByInstant? (((v.days.flatMap (·.durations)).filter (fun o => decide (o.id = i) && !o.isPartial)).map (·.t))

theorem aViewWithoutLastDoneReadsTheReplays :
    Replay.Answer.stamp (lastDoneFromOpenDays
        (Seal.answer (Seal.ckptOfEntries Replay.utcZone 739870 739900 2 Seal.twoDoneDays [] [])) ['x'])
      = Replay.ask (Replay.replayDoc Replay.utcZone Seal.twoDoneDays) (.lastDone ['x']) := by
  decide

/- CHEAT 151 — `readCkpt` defaulting a missing `ledgerDay` to 0.  The
   tempting reader fills an absent field with its zero, as a serde default
   would.  But a ledger day of 0 makes every sealed day open again with nothing
   in it: the checkpoint of the two-done log sealed at the 8th, read without its
   `ledgerDay`, would answer the 7th as an empty open day.  `readCkpt` refuses
   `badCkpt ledgerDay` by name; `decide` refuses the claim that the defaulting
   reader does. -/
def readCkptDefaultingLedgerDay (j : JVal) : Except Seal.CkErr Seal.Ckpt :=
  match j with
  | .obj kvs =>
    if kvs.any (fun p => p.1 == Seal.kLedgerDay) then Seal.readCkpt j
    else Seal.readCkpt (.obj (kvs.take 3 ++ (Seal.kLedgerDay, .num 0) :: kvs.drop 3))
  | _ => Seal.readCkpt j

theorem aDefaultingReaderRefusesAMissingLedgerDay :
    (match readCkptDefaultingLedgerDay (.obj ((Seal.ckptPairs
        (Seal.ckptOfEntries Replay.utcZone 739870 739866 2 Seal.twoDoneDays [] [])).filter
          (fun p => !(p.1 == Seal.kLedgerDay)))) with
      | .error (.badCkpt .ledgerDay) => true
      | _ => false) = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-15 (stage 5, D9 track, step W2).  Design §16's labels 99
-- ("`resume` accepting an unsettled undo whose target is folded") and 102
-- ("the window compacted to `horizonOf L + 1`").  Numbers 152 and 153 are the
-- next free numbers in this checkout (the highest was 151, W1).  The controls,
-- which compile, are `Seal.resume_without_the_guards_is_not_replay` and
-- `Seal.the_window_at_the_horizon_reads_the_replay`.
-- Everything below must FAIL to compile.
-- ===========================================================================

/- CHEAT 152 — a resume accepting an unsettled undo whose target is folded
   (design label 99).  The tempting resume folds the tail's survivors from the
   restored state and skips G1.  After a folded `done a`, the tail's
   `undo done a` finds nothing on the tail's own stack, so the resumed answer
   keeps `a` done, while the replay of both lines cancels it.  `decide` refuses
   the claim that the unguarded resume reads the replay's `last_done`. -/
set_option maxRecDepth 8000 in
theorem anUnguardedResumeReadsTheReplaysLastDone :
    Seal.askAnswer (Seal.resumeUnguarded Replay.utcZone
        (Seal.ckptOfEntries Replay.utcZone 739865 739865 1 [Replay.bE 1 63924368400 (Replay.bDone ['a'] 50 false)] [] [])
        [Replay.bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] []) (.lastDone ['a'])
      = Seal.askAnswer (Seal.answer (Seal.ckptOfEntries Replay.utcZone 739865 739865 2
        [Replay.bE 1 63924368400 (Replay.bDone ['a'] 50 false),
         Replay.bE 2 63924368460 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] [] [])) (.lastDone ['a']) := by
  decide

/- CHEAT 153 — the window compacted to `horizonOf L + 1` (design label 102,
   CRIT 3).  The tempting compaction keeps the window from the day after the
   horizon, since the window records cover every date below it.  But the
   horizon itself is then in neither: one `done x` on 2026-08-29, sealed on
   2026-09-14 (whose horizon is the 29th), reads no done date there, and
   `decide` refuses the claim that the compacted answer reads the replay's. -/
def compactedAnswer (L : Nat) (es : List Log.Entry) : Seal.Answer :=
  { Seal.answer (Seal.ckptOfEntries Replay.utcZone L L es.length es [] []) with
      window := Seal.windowsFrom (Seal.foldedState Replay.utcZone es []) (Seal.horizonOf L + 1) }

set_option maxRecDepth 8000 in
theorem aWindowCompactedPastItsHorizonReadsTheReplay :
    Seal.askMerged (Seal.dayRecordsOfEntries Replay.utcZone 0 739872 Seal.oneDoneOnTheHorizon)
        (Seal.windowRecordsOfEntries Replay.utcZone 0 (Seal.horizonOf 739872) Seal.oneDoneOnTheHorizon)
        (compactedAnswer 739872 Seal.oneDoneOnTheHorizon) (.win 739856 (.done ['x']))
      = Replay.ask (Replay.replayDoc Replay.utcZone Seal.oneDoneOnTheHorizon) (.win 739856 (.done ['x'])) := by
  decide

/- CHEAT 154 — a reseal whose ledger day moves backwards (design label 100).
   The tempting new ledger day is the least of `F` and the unfolded lines' days,
   without the floor at the stored ledger day.  A checkpoint sealed at
   2026-09-14 and resumed the same day with `keepDays = 5` and an empty tail
   then reseals at 2026-09-09, before the days it has already sealed, and
   `decide` refuses the claim that the ledger day never moves back
   (`reseal_is_seal`'s `L ≤ L'`). -/
def resealEmptyRun : Seal.Run :=
  ⟨[], [], [], [], fun _ => none, Replay.State.init 0, [], Seal.answer (Seal.Ckpt.empty Replay.utcZone)⟩

def sealDayWithoutTheLedgerFloor (z : Cal.Tz) (T : Nat) (K : Seal.Ckpt) (p : Seal.Policy) (r : Seal.Run) (j : Nat) :
    Nat :=
  Seal.sealDayOf z T { K with ledgerDay := 0 } p r j

set_option maxRecDepth 8000 in
theorem aResealNeverMovesItsLedgerDayBack :
    ({ Seal.Ckpt.empty Replay.utcZone with ledgerDay := 739865 } : Seal.Ckpt).ledgerDay
      ≤ sealDayWithoutTheLedgerFloor Replay.utcZone 739865 { Seal.Ckpt.empty Replay.utcZone with ledgerDay := 739865 }
          ⟨5, none⟩ resealEmptyRun 0 := by
  decide

/- CHEAT 155 — a reseal that leaves a folded-target undo out of `settled`, still
   accepted afterwards (design label 101).  The tempting resealed checkpoint
   keeps no settled undos.  Folded `done b` and `done a`, and an unfolded
   `undo done a` whose target is folded: without its settled line, the undo
   dangles in the suffix and the folded `done` tag makes G1 refuse it, and
   `decide` refuses the claim that the suffix passes G1
   (`a_resealed_checkpoint_accepts_its_own_suffix`, through `tagsClear_iff`). -/
def aCheckpointWithASettledUndo : Seal.Ckpt :=
  Seal.ckptOfEntries Replay.utcZone 739865 739865 2
    [Replay.bE 1 63924368400 (Replay.bDone ['b'] 50 false), Replay.bE 2 63924368460 (Replay.bDone ['a'] 50 false)]
    [Replay.bE 3 63924368520 (.undo ['d', 'o', 'n', 'e'] (some ['a']))] []

set_option maxRecDepth 8000 in
theorem aResealWithoutItsSettledUndoAcceptsItsSuffix :
    Seal.g1 { aCheckpointWithASettledUndo with settled := [] }
      (Seal.unsettled [] [Replay.bE 3 63924368520 (.undo ['d', 'o', 'n', 'e'] (some ['a']))]) = none := by
  decide

/- CHEAT 156 — `F` computed from the log's latest day without the `T − keepDays`
   bound (design label 103, CRIT 1).  The tempting floor is the latest day any
   surviving line heads, less `keepDays`.  One note dated a year ahead, folded
   on 2026-09-14 with `keepDays = 2`, then seals to 2027-09-12, and `decide`
   refuses the claim that the reseal never seals past now
   (`a_reseal_never_seals_past_now`). -/
def aLineAYearAhead : Log.Entry := Replay.bE 1 63955872000 (.note ['x'])

def aRunOfALineAYearAhead : Seal.Run :=
  ⟨[aLineAYearAhead], [aLineAYearAhead], [aLineAYearAhead], [], fun _ => none, Replay.State.init 1, [],
   Seal.answer (Seal.Ckpt.empty Replay.utcZone)⟩

def floorFromTheLatestDay (keep : Nat) (dy : Cal.Instant → Nat) (sv : List Log.Entry) : Nat :=
  (sv.map (fun e => dy e.t.val)).foldl Nat.max 0 - keep

def sealDayFromTheLatestDay (z : Cal.Tz) (K : Seal.Ckpt) (p : Seal.Policy) (r : Seal.Run) (j : Nat) : Nat :=
  let dy := Replay.dayOf z r.index
  let n := K.items.length + K.openDays.length + r.entries.length
  let Brest := r.entries.filter (fun e => decide (K.cut + j < e.line))
  let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
  let lows := Brest.map (fun e => dy e.t.val) ++ Brest.map (fun e => e.t.val.sec / 86400 + 1)
    ++ Seal.stepLows z dy r.slept (fun e => decide (K.cut + j < e.line)) (Seal.restore K n) r.survivors
    ++ Seal.machineDays (svj.foldl (Replay.stepWith z dy r.slept) (Seal.restore K n)).machine
  Nat.max K.ledgerDay (lows.foldl Nat.min (floorFromTheLatestDay p.keepDays dy r.survivors))

set_option maxRecDepth 8000 in
theorem aFloorFromTheLatestDayNeverSealsPastNow :
    sealDayFromTheLatestDay Replay.utcZone (Seal.Ckpt.empty Replay.utcZone) ⟨2, none⟩ aRunOfALineAYearAhead 1 = 0 ∨
      sealDayFromTheLatestDay Replay.utcZone (Seal.Ckpt.empty Replay.utcZone) ⟨2, none⟩ aRunOfALineAYearAhead 1 + 2
        ≤ 739865 := by
  decide

/- CHEAT 157 — an unterminated last segment folded (design label 104, CRIT 8).
   The tempting fold point reads every tail as terminated.  One unterminated
   line, a note dated a year ahead (so no other condition holds it back), then
   folds, and `decide` refuses the claim that the unterminated line stays
   unfolded (`the_unterminated_segment_is_never_folded`). -/
def foldPointIgnoringTheEnd (z : Cal.Tz) (T : Nat) (K : Seal.Ckpt) (b : List Log.Line) (_terminated : Bool)
    (p : Seal.Policy) (r : Seal.Run) : Nat :=
  Seal.foldPointOf z T K b true p r

set_option maxRecDepth 8000 in
theorem aFoldPointIgnoringTheEndLeavesTheLastLineUnfolded :
    foldPointIgnoringTheEnd Replay.utcZone 739865 (Seal.Ckpt.empty Replay.utcZone) [⟨1, some ['x']⟩] false ⟨2, none⟩
      aRunOfALineAYearAhead < 1 := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-16 (stage 6, run W-13, step L9 — day 0 is the kernel's own;
-- design §13.5, gap 93).  Cheat 158 is the design's reserved **cheat 118**,
-- "the posterior applied after the cap"; it is numbered from the end of this
-- file (§6.2: append, never renumber), and the design's label is recorded here
-- so the two can be read together.
-- ===========================================================================

/- CHEAT 158 (design label 118) — today's posterior applied AFTER the home cap.
   `EnergyCtx::energy_at` predicts, corrects with the posterior, and caps: the
   cap is last, so a report that lifts a home level above `home_max_ci` is still
   capped.  Applying the correction after the cap lets it through.  On the §4.3
   Monday at home, with `home_max_ci = 3` and a 09:00 report of 5 against a
   prediction of 3, the fork keeps every minute at 3 and the cheat lifts three
   blocks to 5.  `decide` refuses the equality. -/
def todayEnergyCappedFirst (I : Look.Input) (t : Cal.Instant) : Fin 6 :=
  Look.correctAt I.today0.post I.today0.reports t
    (Look.capForLocation I.homeMax I.today0.allowHome (Look.capLoc I.today0.loc)
      (Look.predictShift I.curves (Look.curveKeyOf I.curves I.today0.loc)
        (Look.hswAt (Look.wakeOn I I.today) t) (I.today0.sleep.shiftOf I.today0.slept))).val

def aHomeDayWithALiftingReport : Look.Input :=
  { Look.specWalled with today0 :=
      { Look.specToday with loc := Look.homeKey, reports := [⟨Look.atSpec 540, 3, 5⟩] } }

def day0HistCappedFirst (I : Look.Input) : Look.Hist :=
  Look.histOf' ((Look.day0Cut I).slots.map fun s => (todayEnergyCappedFirst I ⟨s.start, 0⟩, s))

theorem aPosteriorAfterTheCap :
    (List.finRange 6).map (day0HistCappedFirst aHomeDayWithALiftingReport)
      = (List.finRange 6).map (Look.day0Hist aHomeDayWithALiftingReport) := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-14, track P step P0 — the planner's
-- vocabulary; design §16's two P0 cheats).  Numbered from the end of this file
-- (§6.2: append, never renumber).
-- ===========================================================================

/- CHEAT 159 — a segment that ends before it starts, accepted.  `Seg.wf` is
   `start ≤ stop` and the end inside the calendar; the fork's `Segment` has no
   such check at all and `Segment::minutes` papers over it with
   `.max(0)`, so a wall written `17:00-09:00` renders as a zero-minute row
   instead of being refused.  `mkSeg?` names it `.inverted`.  `decide` refuses
   the claim that the inverted one is well-formed. -/
def anInvertedSeg : Planner.Seg :=
  { start := 61200, stop := 32400, kind := Planner.SegKind.wall, energy := none,
    item := none, inst := none, flags := {}, planned := none, mult := none, note := none }

theorem anInvertedSegIsWellFormed : Planner.Seg.wf anInvertedSeg = true := by decide

/- CHEAT 160 — a batch of seventeen.  §7.5 gathers small items into ONE slot
   under `batch_max_min`, so `BatchIds` is bounded at `maxBatch = 16`; the
   fork's `SegKind::Batch(Vec<Id>)` is unbounded, which is the hole R10 exists
   to close.  `decide` refuses the claim that `mkBatch?` accepts seventeen. -/
def seventeenIds : List Id :=
  [['a'], ['b'], ['c'], ['d'], ['e'], ['f'], ['g'], ['h'], ['i'],
   ['j'], ['k'], ['l'], ['m'], ['n'], ['o'], ['p'], ['q']]

theorem aBatchOfSeventeenIsAccepted : (Planner.mkBatch? seventeenIds).isSome = true := by decide

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-14, track P step P1 — the walls;
-- design §16's two P1 cheats).  Numbered from the end of this file (§6.2).
-- ===========================================================================

/-- The §4.3 meeting as `wallIndex` lists it, with an hour of `buffer:` in front:
   blocked from 11:50, the event 12:50-13:50, on one day. -/
def aBufferedWall : Look.WallIx :=
  ⟨['g','1'], 739865, 739865, 42600, 46200, 49800⟩

/-- The same day's second meeting, overlapping it: 13:30-14:30. -/
def anOverlappingWall : Look.WallIx :=
  ⟨['g','2'], 739865, 739865, 48600, 48600, 52200⟩

/- CHEAT 161 — a wall placed where there was room.  §8.2 step 1 places an
   Interval instance EXACTLY where it is written; `Planner.wallRows` reads both
   ends off the index and contributes neither.  A planner that treated a wall as
   something to fit — first free position, same duration — is what
   `plan_never_moves_a_wall` exists to rule out, and it is what
   `horizon.rs`-shaped code does with everything else.  `decide` refuses the
   claim that the two agree. -/
def wallRowsAtTheFirstFreePosition (dayLo : Nat) (x : Look.WallIx) : List Planner.Seg :=
  [{ start := dayLo, stop := dayLo + (x.hi - x.evLo), kind := Planner.SegKind.wall,
     energy := none, item := some x.id, inst := none, flags := {}, planned := none,
     mult := none, note := none }]

theorem aWallPlacedWhereThereWasRoom :
    wallRowsAtTheFirstFreePosition 39600 aBufferedWall = Planner.wallRows false aBufferedWall := by
  decide

/- CHEAT 162 — an overlap filled.  §8.2 step 1: overlapping walls are reported
   pairwise in `diagnostics.conflicts`, the planner "does not resolve them", and
   BOTH stay blocked so nothing is placed in the overlap.  Shunting the later
   wall to the end of the earlier one fills the overlap and makes the conflict
   disappear — the failure that looks like success, because the report goes
   quiet.  `decide` refuses the claim that the resolved pair reports what the
   written pair reports. -/
def resolveOverlap (a b : Look.WallIx) : Look.WallIx :=
  if b.evLo < a.hi ∧ a.evLo < b.hi then { b with lo := a.hi, evLo := a.hi } else b

theorem anOverlapFilled :
    Planner.wallConflicts [aBufferedWall, resolveOverlap aBufferedWall anOverlappingWall]
      = Planner.wallConflicts [aBufferedWall, anOverlappingWall] := by
  decide

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-14, track G — L26's eleven single-run
-- laws as one checker battery, `PlanCheck.lean`, design §6).  Appended at the
-- end (§6.2: append, never renumber).
--
-- **The labels start at 171, not 161, on purpose.**  Track P is running its
-- planner steps in parallel on another branch (D26) and design §16 gives P1-P8
-- two to three cheats each, so 161-170 is left to it.  A hole in the labels
-- costs nothing; a duplicate label costs a merge-time renumber and leaves a
-- wrong number in a commit message, which this campaign has paid for twice.
-- ===========================================================================

/- CHEAT 171 — the battery cannot refuse a day.  This is AGENTS §9.2's own
   disguised gap, written out: *"a check no input can fail"*.  A checker battery
   that is true of every `(r, d)` proves nothing about `dayPlan`, and the whole
   value of `dayPlan_ok_core_given_the_budget` rests on `planOkCore` being falsifiable.  It is —
   `PlanCheck.planOkCore_can_fail` exhibits the day it refuses — so the claim
   below does not close. -/
theorem theBatteryCannotRefuseADay (r : Planner.PlanReq) (d : Planner.DayPlan) :
    PlanCheck.planOkCore r d = true := by rfl

/- CHEAT 172 — a block laid across a wall passes the wall check.  §8.3's "no
   segment overlaps a Wall" is the law, and `PlanCheck.theBlockOverAWallDay`
   puts an hour-long block at [0, 3600) under a wall at [1800, 5400).  The
   checker answers `false` and the claim that it answers `true` does not close.
   This is the pair to design §16's P1 cheat "an overlap filled": that one will
   catch the *planner* placing it, this one catches the *checker* going
   blind. -/
theorem aBlockLaidAcrossAWallPassesTheWallCheck (r : Planner.PlanReq) :
    PlanCheck.noBlockOverAWall r PlanCheck.theBlockOverAWallDay = true := by rfl

/- CHEAT 173 — a kept reservation still leaves a prefix.  This is the belief
   D29 corrects: §8.2 choice 5b reserves the running block BEFORE the budget is
   consulted, so a candidate ranking ahead of it can leave the day while the
   reservation stays, and the shorter assignment is then not a prefix of the
   longer one.  `PlanCheck.a_kept_reservation_defeats_the_prefix_but_not_the_erasure`
   proves both halves; this block asserts the half that is false. -/
theorem aKeptReservationStillLeavesAPrefix (a x : Id) (hne : x ≠ a) :
    ∃ n : Nat, ([a] : List Id) = ([x, a] : List Id).take n := ⟨1, by simp⟩

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-15**, track P, step P2 — §8.2 step 2:
-- the routines and the evening).  Appended at the end (§6.2: append, never
-- renumber).  Labels 163-165: P1 took 161-162 out of the 161-170 track P
-- reserved for its own steps, and track G's 171-173 are above.
-- ===========================================================================

/- CHEAT 163 — a routine placed outside its window.  §8.2 step 2 places a window
   instance inside ITS OWN window: `place_mandatory_and_pref` searches
   `[span.0.max(now), span.1]` and nothing else.  The tempting shortcut is "the
   earliest free position in the day" — it is shorter, it always succeeds, and it
   silently moves a 14:00-15:00 chore to breakfast, which is the failure that
   looks like success because the routine IS placed.  `decide` refuses the claim
   that the two searches agree. -/
def theEarliestFreePositionInTheWholeDay (durSec : Nat) (ws : List (Nat × Nat)) : Option Nat :=
  Planner.earliestFree 28800 79200 durSec ws

theorem aRoutinePlacedOutsideItsWindow :
    theEarliestFreePositionInTheWholeDay 1800 [] = Planner.earliestFree 50400 54000 1800 [] := by
  decide

/- CHEAT 164 — a routine whose declared window is malformed, planned anyway
   (README gap 285).  Driven on the audit's own workspace, `- lunch
   win:25:99-13:30 dur:30m  every:day` makes `lime check` name the line twice and
   `lime now` and `lime plan` proceed with rc=0, the invalid window simply dropped.
   `25:99` is not a clock, so `Field.parseWindow` answers `none`, so the item's
   shape is `Shape.none` and it declares no window at all — while its instance
   still carries one.  `Planner.mkRoutine?` answers `undeclaredWindow` and the
   verb refuses.  This block asserts the fork's behaviour instead, with both
   hypotheses satisfiable by an ordinary plan. -/
theorem aMalformedWindowIsPlannedAnyway (p : PlanCore) (x : Planner.RoutineIn) (e : Entity)
    (hget : p.store.get x.id = some e)
    (hd : Planner.declaresAWindow p x.id = false) :
    Planner.mkRoutine? p x = .ok x := by
  simp [Planner.mkRoutine?, hget, hd]

/- CHEAT 165 — the small hours reopened.  `Planner.night()` runs from the
   wind-down to the end of TOMORROW, not to midnight (fork `Planner::night`):
   §8.1's wall extension can push the window past midnight and the small hours
   are not a second working evening.  Ending the night at midnight leaves
   00:00-06:00 free, and a mandatory routine whose window closes tomorrow morning
   is then placed at 00:00 — placed, reported, and wrong.  `decide` refuses the
   claim that the two nights leave the same earliest position. -/
theorem theSmallHoursReopened :
    Planner.earliestFree 75600 108000 1800 [(75600, 86400)]
      = Planner.earliestFree 75600 108000 1800 [(75600, 172800)] := by
  decide
-- APPENDED 2026-09-17 (stage 6, run W-15, track K — K3a, the widened item
-- grammar: the state box is optional and an id-less line is keyed by its
-- title.  D31, gap 301).  Appended at the end (§6.2: append, never renumber).
-- Labels 174-176; 161-170 stay reserved for track P's planner steps.
-- ===========================================================================

/- CHEAT 174 — a **boxed** line with no `^id` is keyed by its title.  K3a keys
   an id-less line by `Field.titleKey`, but only the BARE form: §4.1 omits the
   box and the id together, in the same three files, and a line that carries a
   state box is a tracked item whose id the kernel does not invent.  So
   `- [ ] no id here` is still `PErr.noId` and the whole plan is refused, which
   is what `a_malformed_item_line_is_rejected_not_treated_as_prose` (the FFI
   suite) asserts.  `tree.rs`'s `key_of` does not look at the box and would key
   this line `Id("no id here")` with a `missing-id` warning; the divergence is
   deliberate and this block is where it is written down.

   AMENDED 2026-10-02 (W-42 track G, D83): the literal gained `RawItem`'s fourth field, the
   separators between the bullet and the box (`[]` here), and nothing else — without it this
   block would fail to elaborate for a field count and stop failing for its claim (CHEAT 176's
   D32 amendment is the precedent). -/
theorem aBoxedLineWithNoIdIsKeyedByItsTitle :
    parseLine "- [ ] no id here".toList =
      Except.ok (['n','o',' ','i','d',' ','h','e','r','e'], Glyph.todo,
        ⟨[], true, tokenize " no id here".toList, []⟩) := by rfl

/- CHEAT 175 — a box-less line can carry a state.  `serializeItem` writes back
   the box it read, so an entity whose live line is bare and whose status is
   `dropped` renders the bytes it was read from and the state vanishes on the
   next read.  `Plan.boxesWf` is the clause that refuses it and
   `a_boxless_line_cannot_carry_a_state` proves the clause fails on exactly
   that shape; driven through the wire, `{"op":"drop","id":"lunch"}` against a
   `routines.md` line answered `ok` with the line unchanged before the clause
   landed, and answers `{"err":{"kernel":"badHorizon"}}` after.

   AMENDED 2026-10-02 (W-42 track G, D83): the line literal gained `RawItem`'s fourth field
   (`[]`), for the field count and nothing else (CHEAT 174's note). -/
theorem aBoxlessLineCanCarryAState :
    boxWf { live := ⟨0, 0⟩, archive := none, status := .settled .dropped,
            line := ⟨[], false, tokenize " lunch win:11:30-13:30".toList, []⟩ } = true := by rfl

/- CHEAT 176 — two routines with one title are two entities.  A title key that
   silently collides is a wrong answer (§5.6), and the fork's fallback — key the
   *later* line `file:line` — depends on the order the host listed its
   documents, which is the defect §5.6 exists to forbid.  So the kernel refuses
   by name.  The claim below is that the loader builds an entity from two
   `lunch` placements; the positive forms are `two_titles_in_one_file_are_a_dupId`
   and `a_title_colliding_with_an_id_is_refused` (Boundary.lean), which run the
   whole loader and pin the JSON each refusal emits.

   AMENDED 2026-09-17 (W-16, **D32**): the two placement literals gained
   `Placement`'s seventh field, the document's path, and the refusal JSON this
   block used to quote inline moved with it — it is now
   `{"err":{"dupId":{"key":"lunch","a":{…},"b":{…}}}}`, which the two positive
   theorems pin byte for byte.  The edit is not a renumber (§6.2): without it
   this block would fail to elaborate for a **field count** and stop failing
   for the claim it is about, which is §9.2's disguised gap wearing check 4's
   clothes.

   AMENDED AGAIN 2026-10-02 (W-42 track G, D83): the two line literals gained `RawItem`'s fourth
   field, the separators before a box (`[]`), for the same reason. -/
theorem twoRoutinesWithOneTitleAreTwoEntities :
    (match buildEntity "lunch".toList
        [⟨0, 0, "lunch".toList, Glyph.todo, ⟨[], false, tokenize " lunch".toList, []⟩, none,
          "routines.md".toList⟩,
         ⟨0, 1, "lunch".toList, Glyph.todo, ⟨[], false, tokenize " lunch".toList, []⟩, none,
          "routines.md".toList⟩] with
     | .ok _    => true
     | .error _ => false) = true := by rfl


/- CHEAT 177 — `every:2w:<wd>` counts ISO week *numbers*, so it fires on the
   weekday of every week whose ISO number is even.  It does not: a 53-week year
   restarts the numbering and two occurrences land on consecutive weeks, which
   is why `weekIdxMod` counts whole weeks from `Recur.weekEpoch` instead.  The
   claim below is that the fortnightly rule gives BOTH Mondays of a two-week
   range; `Recur.every_two_weeks_skips_a_week` is the positive form. -/
theorem everyTwoWeeksFiresEveryWeek :
    Recur.ruleOccurrences (.everyNWeeks 2 .monday) (Cal.toDay ⟨2026, 9, 7⟩)
        (Cal.toDay ⟨2026, 9, 20⟩) 0
      = [(Cal.toDay ⟨2026, 9, 7⟩, Cal.toDay ⟨2026, 9, 7⟩),
         (Cal.toDay ⟨2026, 9, 14⟩, Cal.toDay ⟨2026, 9, 14⟩)] := by decide

/- CHEAT 178 — a `win:` routine whose window ran out this morning is still
   today's instance, so the planner can place it after the window closed.  §5.2
   and `today_instances`' own filter say otherwise: with the default
   `on-miss:expire` the chance is gone once `now` passes the close, and only
   `on-miss:persist` carries it.  The claim below is that §4.3's lunch line
   is still §5.2-mandatory at 14:00; the positive forms are
   `PlannerWit.the_lunch_routine_is_gone_by_two_in_the_afternoon` and
   `PlannerWit.a_persist_routine_is_one_carried_obligation_not_sixty_one`. -/
theorem aClosedWindowIsStillMandatory :
    Recur.isMandatory PlannerWit.recurPlan.val "lunch".toList
        ⟨"lunch".toList, .date PlannerWit.recurDay,
         some (Recur.atClock PlannerWit.recurDay ⟨810, by omega⟩),
         some (Recur.atClock PlannerWit.recurDay ⟨690, by omega⟩,
               Recur.atClock PlannerWit.recurDay ⟨810, by omega⟩),
         Log.InstanceStatus.pending⟩
        PlannerWit.recurDay (Recur.atClock PlannerWit.recurDay ⟨840, by omega⟩) = true := by decide

/- CHEAT 179 — `every:month:31` means the 31st, and a month without one has no
   occurrence.  The fork clamps the day of the month to the month's length
   (`u32::from(*day).clamp(1, month_len(y, m))`), so February's occurrence is
   the 28th — the claim below is that February 2026 has none.
   `Recur.every_month_31_clamps_in_february` is the positive form. -/
theorem monthlyThirtyFirstSkipsFebruary :
    Recur.ruleOccurrences (.monthly 31) (Cal.toDay ⟨2026, 2, 1⟩) (Cal.toDay ⟨2026, 2, 28⟩) 0
      = [] := by decide
-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run W-16, track P — P3, §8.2 step 3's slot cut
-- and §8.2 choice 5b's reservation).  Appended at the end (§6.2: append, never
-- renumber).  Labels 180-183 (renumbered from 177-180 at the W-16 land step: track K took
-- 177-179 in the same run, AGENTS §6.2/§6.5); 166-170 stay reserved for track P's later steps.
-- ===========================================================================

/- CHEAT 180 — the running block reserved for its **whole remaining estimate**.
   That is the shipped bug §8.3's E1 is written about: "the Active reservation
   covered the whole remaining estimate; a 6b item swallowed 355 minutes".  Fork
   `active_run` clips the run at `current_block_end(started)` — the end of the
   `block_min` block it is in — and `PlannerWit.theRunningRequest` is the case
   run: `m1` started at 13:40 with a 90-minute estimate and twenty worked, so
   seventy minutes are still owed and the row runs **forty**, to 14:40 and not
   to 15:10 (`PlannerWit.the_reservation_is_clipped_to_the_block_it_is_in`).
   This block asserts the boundary is seventy minutes past `now`; `decide`
   refuses, and `Planner.the_block_boundary_is_run` is the positive form. -/
theorem theReservationTakesTheWholeEstimate :
    Planner.blockBoundary 60 50400 49200 86400 = 50400 + 60 * 70 := by decide

/- CHEAT 181 — a routine placed on top of the running block (README gap 434).
   Fork `run()` pushes `active_run`'s span onto `blocked` **before**
   `place_mandatory_and_pref`, so step 2 searches around it;
   `Planner.PlanReq.blockedBeforeRoutines` is where that happens and
   `a_routine_is_never_placed_over_the_running_block` is the law.  This block
   claims the search does not notice: a half-hour routine looking in 14:00-17:00
   lands in the same place whether or not 14:00-15:00 is reserved.  `decide`
   refuses — with the reservation it is pushed to 15:00. -/
theorem aRoutineTakesTheRunningBlocksStretch :
    Planner.earliestFree 50400 61200 1800 [(50400, 54000)]
      = Planner.earliestFree 50400 61200 1800 [] := by decide

/- CHEAT 182 — the evening cut into slots.  Fork `run()`'s step 3 pushes
   `self.night()` onto `slot_blocked` before `cut_slots_around`, so nothing is
   cut from the wind-down onwards; `Planner.PlanReq.slotBlocked` is that push and
   `no_slot_reaches_the_evening` is the law.  This block claims the cut is the
   same with and without it, over 20:00-24:00 on the shipped `[day]` with the
   night starting at 21:30.  `decide` refuses. -/
theorem theEveningIsCutIntoSlots :
    Look.cutSlots Look.CutCfg.shipped 72000 86400 [] [] 0
      = Look.cutSlots Look.CutCfg.shipped 72000 86400 [(77400, 172800)] [] 0 := by decide

/- CHEAT 183 — a wall's `buffer:` run-up left unblocked (README gap 552).
   `Look.WallIx` carries no bound tying `evLo` to `hi`, and `Look.wallOfEntity`
   builds both straight out of `at:<s>/<f>`, which the grammar accepts inverted.
   On such a wall `Planner.wallRows` still draws the run-up row `[lo, evLo)`
   while the span `(x.lo, x.hi)` stops at `hi < evLo`, so a second of the run-up
   is not blocked at all.  This block asserts that the old span covers it —
   `decide` refuses, which is why `blockedByWalls` blocks `(x.lo, max evLo hi)`
   and `a_wall_row_sits_in_a_blocked_span` needs no hypothesis. -/
theorem theInvertedWallsBufferIsBlockedAnyway :
    Look.covered [(600, 700)] 800 = true := by decide

/- CHEAT 184 — §7.3's two numbers compared in different units (design §5.5).
   Design §5.5 gives `edfNumbers` as `(g.deadline.need, g.avail)`, but
   `Grant.avail` is a NUMERATOR over the pass's denominator while
   `Deadline.need` is whole minutes, and `Arith.isImpossible need avail` is
   `decide (avail < need)` on the two as given.  This block asserts the
   design's pair answers what `Grant.impossible` answers, on a grant that is
   genuinely impossible: a need of two minutes against an availability of one
   minute's worth of units.  `decide` refuses — the design's pair says `false`
   where the grant says `true` — and `Planner.edfNumbers` scales the need,
   with `edfNumbers_is_the_grants_own_impossibility` as the positive form. -/
theorem theDesignsEdfPairIsTheImpossibilityTest :
    Arith.isImpossible 2 Look.capDen
      = Grant.impossible ⟨⟨2, (3 : Fin 6), 0⟩, Look.capDen, 0⟩ Look.capDenD := by decide

/- CHEAT 185 — an id the plan does not hold sorted FIRST.  Fork
   `priority::collect_candidates` reads a candidate's line order through
   `tree.order(k).unwrap_or((usize::MAX, usize::MAX))`, so a candidate whose id
   the tree cannot find sorts **last** among its equals; `Planner.siteNums`
   encodes that as a leading marker digit because `Nat` has no maximum.  This
   block asserts the plain `(0, 0)` reading instead — that a missing site is the
   smallest one.  `decide` refuses.  The positive form is
   `PlannerWit.the_ranking_request_reads_the_plans_line_order` beside
   `the_ranking_request_is_ordered`, where `^g1` is the one candidate the plan
   holds. -/
theorem aMissingLineOrderSortsFirst :
    Planner.natsLe (Planner.siteNums none) (Planner.siteNums (some ⟨0, 0⟩)) = true := by decide

/- CHEAT 186 — the request order read as §7.4's first component.  §7.4 sorts by
   `(p, root order, own order)` and uses the arrival position only to break a
   tie; a sort that kept the wire order wherever it "looked sorted" would pass
   every length and permutation law this step proves.  This block asserts that
   `PlannerWit.theRankingRequest`'s six come back in the order they were sent —
   `decide` refuses, because the overdue candidate at position 2 and the
   mandatory one at position 3 both outrank the optional at position 1
   (`PlannerWit.the_ranking_request_is_ordered`). -/
theorem theRankingKeepsTheWireOrder :
    PlannerWit.rankedIds PlannerWit.theRankingRequest
      = PlannerWit.theRankingRequest.candAnswers.map (fun o => o.out.cand.id) := by decide

/- CHEAT 187 — a wall given a `p` and ranked with the queue.  §7.2's first row
   is off the scale (`rawPrio_of_a_wall`), and fork `sorted_candidates` reads a
   wall as `7` only so that `keyed.sort()` has a number, never to report one:
   `Planner.prioRow` drops it and `DayPlan.priorities` has five rows for six
   candidates.  This block asserts the day reports a `p` for the wall too —
   `decide` refuses.  The positive form is
   `PlannerWit.the_ranking_requests_day_carries_its_priorities`. -/
theorem theWallIsReportedWithAPriority :
    (Planner.dayPlan PlannerWit.theRankingRequest).priorities.val.length
      = PlannerWit.theRankingRequest.cands.val.length := by decide

/- ===========================================================================
   APPENDED 2026-09-18: stage 6, run W-17, track G.  Cheats 188-190 — the three
   things this step's two theorems would be if their restrictions were dropped.
   Track P owns 161-170 still (design §16's P4-P8 rows); this block was
   written as 184-186 and RENUMBERED to 188-190 at the W-17 land step, because
   track P's own P4 block took 184-187 in the same run (AGENTS §6.2: the merge
   renumbers).
   =========================================================================== -/

/- CHEAT 188 — §8.3's wall law over EVERY Block row of the day, which is the
   form `Goals.lean` carried until this step.  It is false, and
   `PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted`
   is the compiled refutation: a calendar that acquires a meeting on an hour the
   morning's log already worked puts a Wall row inside a replayed Block row.
   This block asserts the battery finds nothing wrong with that day; `decide`
   refuses, because `noBlockOverAWall` answers `false` on it. -/
theorem theReplayedPastIsNeverUnderAWall :
    PlanCheck.noBlockOverAWall PlannerWit.theMorningWallRequest
      (Planner.dayPlan PlannerWit.theMorningWallRequest) = true := by decide

/- CHEAT 189 — §6.1's lift over the whole day rather than over the rows §8.3 is
   about.  `PlanCheck.dayPlan_ok_core_given_the_budget` needs `hnopast` (the log holds no Block
   today) for exactly this reason, and `dayPlan_ok_core_from_now_given_the_budget` drops the
   hypothesis by restricting the day with `PlanCheck.withoutPast` instead.  This
   block claims the unrestricted conjunction holds at a request whose log DOES
   hold a Block and whose calendar moved onto it — the hypothesis-free lift
   nobody may ship.  `decide` refuses. -/
theorem theLiftHoldsOverTheReplayedPastToo :
    PlanCheck.planOkCore PlannerWit.theMorningWallRequest
      (Planner.dayPlan PlannerWit.theMorningWallRequest) = true := by decide

/- CHEAT 190 — the vacuous checkers asserted to have subjects.  README
   gap 396's honest half is that SIX of the eleven range over nothing on the day
   the planner produces at `theStoredRequest` (this comment read "five" until the
   W-17 repair counted `wallsUnmoved`, whose subject is at `theRequest` and not
   here — README gap 678), and
   `PlannerWit.the_battery_census_over_a_produced_day` computes it.  This block
   claims the day carries a Break row, which is what `noBlockOverABreak` would
   need to be checking anything.  `decide` refuses — the list is empty, because
   `witLines` records no `break`.  (This comment read "the cut's breaks reach the
   day only when work touches them, which is P5's `kept_breaks`, README gap 551",
   which is true of the CUT's breaks and was the wrong reason for THIS emptiness:
   a `break` in the log reaches the day today, and CHEAT 202 is the same claim at
   a request whose log holds one — W-18.) -/
theorem theProducedDayCarriesABreakRow :
    ((Planner.dayPlan PlannerWit.theStoredRequest).segments.any
      (fun s => s.val.kind == Planner.SegKind.brk)) = true := by decide

/- CHEAT 191 — §7.4's key read the ITEM's line order before its ROOT's.  The
   fork sorts `((u8::from(!is_wall)), (p, root_order, own_order)), i` and
   `Planner.CandKey.nums` puts `siteNums k.root` first for exactly that reason.
   Inverting the two left check.sh 7/7 and `cargo test --workspace` 1,337/0/9
   green through W-17, because every candidate of every witness had a root site
   equal to its own (README gap 677).  `theRootedRequest` is the plan in which
   they disagree: `^m1` is first in the week and its root `^O2` is second in the
   month, `^m2` the other way.  This block claims the order the inverted key
   would give — the candidates' own line order, which is also their request
   order.  `decide` refuses: the produced order is `^m2, ^m1`. -/
theorem theKeyReadsTheItemsOwnOrderFirst :
    PlannerWit.rankedIds PlannerWit.theRootedRequest = [['m','1'], ['m','2']] := by decide

/- CHEAT 192 — `wallsUnmoved` asserted to have a subject at the request the
   census is stated over.  `PlanCheck.wallUnmoved` takes its `store.get i = none`
   branch for a Wall row naming an id the plan does not hold, and the store
   behind `theStoredRequest` holds the morning's two tasks, not the calendar's
   `^g1` — so the checker ranges over nothing there, which is the sixth vacuous
   checker README gap 678 added to gap 650's five.  This block claims the Wall
   row's item IS in that store.  `decide` refuses.  (It is in the store behind
   `theRunningRequest`, and `PlannerWit.the_battery_census_at_the_reserved_day`
   computes that — the two requests are what the count turns on.) -/
theorem theWallRowIsInTheStoredRequestsStore :
    ((Planner.dayPlan PlannerWit.theStoredRequest).segments.filter
      (fun s => s.val.kind == Planner.SegKind.wall)).map
        (fun s => (s.val.item.bind
          (fun i => PlannerWit.theStoredRequest.plan.val.store.get i)).isSome) = [true] := by
  decide

/- ===========================================================================
   APPENDED 2026-09-18, stage 6 run W-18, track P, step P5a (AGENTS 6.2).
   The wire carries section 8.2 step 5's nine (README gap 606).  Cheats 193-200.
   (This line read "193-197"; P5b-i added 198-200 and did not move it.  Corrected
   by W-18's land step -- README gap 772.)
   =========================================================================== -/

/- CHEAT 193 — the nine claimed to reach the kernel WITHOUT the host sending
   them.  D34 keeps `collect_candidates` alive to R3 and D27 changes only where
   the facts come from, so a candidate whose `plan` object is absent from the
   wire must be REFUSED, not defaulted: a silent `PlanFacts.unconstrained` would
   make every item splittable, uncapped and `[ ]` on a tree where none of that
   is true.  This block claims the record reads with the plain nine.  `rfl`
   refuses: the answer is `badCandidate 0 plan`. -/
theorem aCandidateWithoutTheNineTakesTheUnconstrainedOnes :
    (CapWire.readCand 0 (CapWire.withoutPlanJ CapWire.a1J)).map (fun c => c.plan.val)
      = .ok Look.PlanFacts.unconstrained := rfl

/- CHEAT 194 — the two booleans claimed interchangeable.  `splittable` is the
   item's `atomic` and `wallToday` is whether an Interval covers today; a
   decoder that swapped them left W-17's whole suite green for the root/own site
   pair (gap 677) and this is the same class one field over.  `loudPlanJ` sends
   `splittable: false, wallToday: true`, so this block's claim — that the record
   reads with them the other way round — is exactly the swap.  `rfl` refuses. -/
theorem theTwoFlagsOfTheNineAreInterchangeable :
    (CapWire.readCand 0 (CapWire.withPlanJ CapWire.a1J CapWire.loudPlanJ)).map
      (fun c => (c.plan.val.splittable, c.plan.val.wallToday)) = .ok (true, false) := rfl

/- CHEAT 195 — `waiting` claimed to be a tenth fact the wire must carry.  Fork
   `priority.rs:718` sets `waiting: item.state == State::Waiting`, so it is a
   projection of `state` and `Look.PlanFacts.waiting` derives it.  This block
   claims a `[?]` candidate is NOT waiting, which is what a tenth independent
   field would allow.  `decide` refuses. -/
theorem waitingIsIndependentOfTheStateBox :
    Look.PlanFacts.waiting { Look.PlanFacts.unconstrained with
      state := Status.live .world } = false := by decide

/- CHEAT 196 — R10 claimed unnecessary for a `Nat` that the fork holds in a
   `u32`.  `plannedMin` past `Look.maxPlanMinutes` is a value no host can mean
   and the wire must refuse it rather than carry it into the fold's cursor
   arithmetic.  This block claims `mkPlanFacts?` accepts one.  `decide` refuses:
   the predicate is false and the constructor returns `none`. -/
theorem theConstructorTakesAPlannedMinutePastTheWiresU32 :
    (Look.mkPlanFacts? { Look.PlanFacts.unconstrained with
      plannedMin := 4294967296 }).isSome = true := by decide

/- CHEAT 197 — section 7's pass claimed to read the nine.  If it did, the
   widening of `Look.Cand` would be a second candidate record rather than a
   widening (AGENTS 5.3), and `prioritiesWithFloors_ignores_the_plan_facts`
   would be false.  This block claims a `Cand` and its `erasePlan` give
   different answers, which is what "the pass reads them" means.  `decide`
   refuses at the one witness the file can evaluate. -/
theorem thePassSeesTheNine :
    Look.entering (Arith.mkPos 13 10 (by decide))
      (Look.witnessCands.map (fun c => c.withPlan
        ⟨{ Look.PlanFacts.unconstrained with plannedMin := 999 }, by decide⟩))
      ≠ Look.entering (Arith.mkPos 13 10 (by decide)) Look.witnessCands := by decide

/- ===========================================================================
   APPENDED 2026-09-18, stage 6 run W-18, track P, step P5b-i (AGENTS 6.2).
   The assignment order's own filter (README gap 602).  Cheats 198-200.
   =========================================================================== -/

/- CHEAT 198 — an ineligible candidate claimed to keep its place in the
   assignment order.  Fork `priority::sorted_candidates` drops `!c.eligible()`
   before it sorts, so a `[?]` item competes for no slot at all; a fold over an
   unfiltered order would plan a block on an item the user is waiting on.  This
   block claims `^r1` still ranks fourth with its state set to `[?]` and nothing
   else changed.  `decide` refuses: it is not in the list. -/
theorem aWaitingCandidateStillRanks :
    PlannerWit.rankedIds (PlannerWit.withFactsAt PlannerWit.theRankingRequest 4
      PlannerWit.waitingFacts) = PlannerWit.rankedIds PlannerWit.theRankingRequest := by decide

/- CHEAT 199 — the `max:` cause claimed to be about the cap's presence rather
   than its two numbers.  Fork `Candidate::ineligible_reason` compares
   `cap_done_min >= cap.amount.as_minutes()`, so sixty minutes capped with thirty
   spent is eligible.  A filter that dropped every capped item would satisfy
   `each_cause_of_ineligibility_drops_the_candidate` and be wrong; this block
   claims exactly that reading.  `decide` refuses. -/
theorem anyCapAtAllDropsTheCandidate :
    PlannerWit.rankedIds (PlannerWit.withFactsAt PlannerWit.theRankingRequest 4
      PlannerWit.capLeftFacts)
      = [['g','1'], ['o','d'], ['m'], ['o'], ['r','2']] := by decide

/- CHEAT 200 — `wall_today` claimed to be read of every candidate.  The fork's
   clause is `!c.is_wall || c.wall_today`: it is read ONLY of a wall, so setting
   it on `^r1`, which is not one, must change nothing.  This block claims it
   changes the order.  `decide` refuses. -/
theorem wallTodayIsReadOfEveryCandidate :
    PlannerWit.rankedIds (PlannerWit.withFactsAt PlannerWit.theRankingRequest 4
      PlannerWit.todaysWallFacts) ≠ PlannerWit.rankedIds PlannerWit.theRankingRequest := by decide

/- ===========================================================================
   APPENDED 2026-09-18, stage 6 run W-18, track G (AGENTS 6.2).
   The break law refuted, and gap 650's measured emptiness given its real
   reason (README gap 650).  Cheats 201-202.

   RENUMBERED BY THE MERGE (AGENTS 6.2, 6.5 item 1): track G wrote these as
   193 and 194 on a branch from `eb4150f`, where 192 was the highest.  Track P
   branched from the same commit and landed 193-200 first, so both tracks
   started at 193 -- the second time in two runs (W-17's gap 671).  Every
   citation of track G's 193/194, in Lean and in prose, moved with them. -/
/- CHEAT 201 — `noBlockOverABreak` asserted to hold on a day whose log records a
   `break` across a block.  Every Break row of the day is a replayed
   one (`Planner.a_break_row_is_a_replayed_row`) and so is every Block row the
   planner did not reserve, so a log with a break stamped 07:10 but logged
   after `m1`'s 08:05 `done` (since W-44, a world with one reading: no clock
   read the break before `m1` was closed; D94 nets every break a clock meets)
   gives the day a Break row INSIDE a Block row.  This block claims the checker
   says `true` there.  `decide` refuses: it says `false`, and so does `planOkCore`.
   Since the owner's D100 (W-47 track K) the replay cuts that closed block around
   the break and the checker says `true` at `theMidBreakRequest`, so the claim is
   made at `thePreD100MidBreakRequest`, the same day as the replay drew it before
   D100 — a run the decoder no longer builds (CHEAT 289 holds the old verdict at
   the decoder's own day). -/
theorem theMidBreakDayKeepsItsBlocksOffTheBreak :
    PlanCheck.noBlockOverABreak PlannerWit.thePreD100MidBreakRequest
      (Planner.dayPlan PlannerWit.thePreD100MidBreakRequest) = true := by decide

/- CHEAT 202 — `noBlockOverABreak` asserted to range over nothing at the census
   request, which is what README gap 650 claimed of it until W-18: it gave the
   checker's emptiness to **P5**, on the reasoning that the cut's breaks reach
   the day only when work touches them (`kept_breaks`, gap 551).  That is true of
   the CUT's breaks and says nothing about the LOG's.  `censusLines` is
   `witLines` with one `break` line appended, and the day the planner produces
   carries the Break row it makes.  This block claims there is no such row.
   `decide` refuses: there is exactly one. -/
theorem theCensusDayHasNoBreakRow :
    (Planner.dayPlan PlannerWit.theCensusRequest).segments.filter
      (fun s => s.val.kind == Planner.SegKind.brk) = [] := by decide

/- ===========================================================================
   APPENDED 2026-09-18, stage 6 run W-19, track P, step P5b (AGENTS 6.2).
   §8.2 step 5's groups: the batching, the split and the `max:` commit.
   Cheats 203-205.  Whoever merges renumbers. -/
/- CHEAT 203 — §7.4's five-part `CandKey` offered where the group's key is
   wanted.  Fork `build_groups` takes the minimum of `priority::sort_key`, which
   is the THREE `(p, root_order, own_order)` and not `sorted_candidates`' tuple:
   the wall digit is meaningless there (a wall never reaches a group) and the
   request position is deliberately absent, because the fork's `out.sort_by` is
   stable and two groups that agree on all three keep the order the batching
   gave them.  Two keys, two types, so the confusion is not expressible. -/
theorem theGroupKeyIsSortedCandidatesOwnKey :
    Planner.groupKeyLe (Planner.CandKey.mk true 0 none none 0)
      (Planner.CandKey.mk true 0 none none 0) = true := by decide

/- CHEAT 204 — a group's members handed straight to `SegKind.batch`.  `BatchIds`
   is bounded at `maxBatch` (R10) and `Group.members` is a plain list, so the row
   a slot emits must pass `mkBatch?` and cannot be built from the group by
   coincidence.  This matters more than it looks: the fork's gather has NO bound
   (README gap 800), so a port that skipped the smart constructor would be one
   zero-minute multiplier away from a `Vec` of any length. -/
theorem aGroupsMembersMakeABatchRow (g : Planner.Group) :
    Planner.SegKind.batch (g.members.map (fun x => x.cand.id)) = Planner.SegKind.brk := by
  decide

/- CHEAT 205 — the gather asserted to reach PAST an equal-`ci` candidate that
   could not join.  `^b4` (40 m) takes `^b1`'s batch to 70 > 60 and stops the
   walk; `^b5` (5 m) would have fitted (10 + 20 + 5 = 35) and is left behind,
   which is §8.3's monotone-rank rule and E2's whole content.  This block claims
   the fork's `break` is a `continue`.  `decide` refuses: `^b5` leads `^b4`'s
   batch instead, and `Planner.gatherBatch_fst_is_a_prefix_of_its_ci` is why. -/
theorem theGatherReachesPastAnEqualCiCandidate :
    PlannerWit.batchIds PlannerWit.theBatchRequest =
      [[['b','1'], ['b','2'], ['b','5']], [['b','3'], ['b','6']], [['b','4']]] := by decide

/- ===========================================================================
   APPENDED 2026-09-18, stage 6 run W-19, track P, step P5b — the CURSOR.
   §8.2 step 5's slot walk: `pick`, `contiguous_fits` and the budget.
   Cheats 206-208.  Whoever merges renumbers. -/
/- CHEAT 206 — an `atomic` group asserted to be placed when the day cannot give
   it its whole run.  `^c4` asks for four hours and the §4.3 Wednesday has three
   free after the first slot, so fork `contiguous_fits` refuses every position
   and the afternoon is left to Rest rather than to a job that cannot finish.
   This block claims it is placed three times, which is what the same candidate
   does when it is **splittable** — so a cursor that read `splittable` and
   nothing else would satisfy it.  `decide` refuses. -/
theorem anAtomicGroupTakesWhateverItCanGet :
    PlannerWit.assignIds PlannerWit.theCursorAtomicRequest =
      [some [['c','1']], some [['c','4']], some [['c','4']], some [['c','4']]] := by decide

/- CHEAT 207 — a `loc:out` errand asserted to take a lounge slot.  The day is
   being lived in the lounge (`state.loc`), and fork `loc_ok` lets an item with a
   constraint take a slot only where the constraint is met or where the current
   location is unknown.  `^c2` differs from `^c1` in `loc:` and in nothing else,
   which is what makes this block about `loc_ok` and not about the order.
   `decide` refuses: `^c4` takes that slot. -/
theorem anErrandTakesALoungeSlot :
    PlannerWit.assignIds PlannerWit.theCursorRequest =
      [some [['c','1']], some [['c','2']], some [['c','4']], some [['c','4']]] := by decide

/- CHEAT 208 — a group asserted to owe **negative** minutes, which is what fork
   `Group::left_min` is (`i64`, decremented by a whole slot and incremented back
   by §8.2 step 6 when a mandatory routine displaces an assigned block).  The
   kernel carries the pair `commitMin`/`spent` instead, so "owes −50" is not a
   value of the type: `Nat` has no `Neg`, and the two readers the fork has —
   `pick`'s `left_min <= 0` and `contiguous_fits`' `need` — are `commitMin ≤
   spent` and `commitMin − spent`, which say the same thing and invert exactly
   under step 6's restore. -/
theorem aGroupCanOweNegativeMinutes (g : Planner.Group) :
    ({ g with spent := g.spent + 60 } : Planner.Group).leftMin = -50 := by decide

/- ===========================================================================
   APPENDED 2026-09-18, stage 6 run W-19, track G (AGENTS 6.2).
   The ceiling: two of the eleven are FALSE on a day the planner produces, at
   every eligibility (README gap 850).  Cheats 209-210.

   WRITTEN as 203-204 on `w19-g`, numbered from 202, the highest on
   `rebuild-on-lean` at `d1a602a`.  Track P branched from the same commit and
   took 203-208, so THE MERGE RENUMBERED THESE TWO TO 209-210 (AGENTS 6.2, 6.5
   item 1) -- the third run in three where two tracks started at the same number
   (W-17's gap 671, W-18's own note above).  Every citation of them in Lean and
   in README.md moved with them; README gap 872. -/
/- CHEAT 209 — design 6.1's lift asserted at the permissive eligibility on the
   day `PlannerWit.theQueuedRequest` produces.  That request is the census
   request with `m1`'s two log lines removed and `m2` running, so `m1` — hot,
   ranked ahead of `m2`, same document, same `ci`, same `rootPrio` — reaches no
   row of the day: `monotoneInRank` and `hotBeforeQueue` both say `false`, and
   so does `planOk`.  This block claims the whole battery passes.  `decide`
   refuses.  The other NINE conjuncts do pass, which is
   `PlannerWit.the_other_nine_hold_where_the_two_fail` and is why the number is
   a ceiling and not a failure. -/
set_option maxRecDepth 40000 in
theorem theQueuedDayPassesTheWholeBattery :
    PlanCheck.planOk PlannerWit.permissive PlannerWit.theQueuedRequest
      (Planner.dayPlan PlannerWit.theQueuedRequest) = true := by decide

/- CHEAT 210 — the same claim over `PlanCheck.withoutPast`'s day, which is the
   day `PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons_on_an_unassigned_day_given_no_eligible_impossible_item` is stated
   over.  The plausible reading is that the restriction repairs the two
   comparisons the way it repaired the wall law and the break law — it does not,
   and it cannot: dropping the past's work rows removes `m1`'s chances of being
   assigned, never adds one.  Here it removes nothing, because `m1` has no row
   on either day.  This block claims the restricted battery passes.  `decide`
   refuses. -/
set_option maxRecDepth 40000 in
theorem theRestrictedQueuedDayPassesTheWholeBattery :
    PlanCheck.planOk PlannerWit.permissive PlannerWit.theQueuedRequest
      (PlanCheck.withoutPast PlannerWit.theQueuedRequest
        (Planner.dayPlan PlannerWit.theQueuedRequest)) = true := by decide

/- ===========================================================================
   APPENDED 2026-09-19, stage 6 run W-20, track P, step P6 (AGENTS 6.2).
   §8.2 step 6's two claims a reader would make and the kernel refuses.
   Cheats 211-212. -/
/- CHEAT 211 — step 6 takes the EARLIEST free position.  That is step 2's rule,
   not step 6's: design 2's choice 6 is the LOWEST PREDICTED ENERGY position,
   ties to the earlier start.  At `PlannerWit.theRoutineRequest` the afternoon
   splits into 14:00-16:00 and 17:00-19:00 around the mandatory routine, the
   first starts at level 4 and the second at level 2, and
   `Planner.PlanReq.lowestFree` answers 17:00 where `Planner.earliestFree`
   answers 14:00 (`PlannerWit.the_lowest_energy_rule_and_the_earliest_rule_
   disagree_here`).  This block claims the earliest.  `decide` refuses. -/
set_option maxRecDepth 40000 in
theorem theDeferredRoutineTakesTheEarliestFreePosition :
    PlannerWit.theRoutineRequest.lowestFree
        [((Cal.instantOf Cal.chicago 739867 960).sec,
          (Cal.instantOf Cal.chicago 739867 1020).sec)]
        (Cal.instantOf Cal.chicago 739867 840).sec
        (Cal.instantOf Cal.chicago 739867 1140).sec 1800
      = some (Cal.instantOf Cal.chicago 739867 840).sec := by decide

/- CHEAT 212 — a day with no room for a routine loses it quietly.  Fork
   `run()`'s note (`planner.rs:1046`) exists because "a day that quietly loses
   lunch is a day no monitor can see": an instance with no position and a window
   still open is named in `diagnostics.notes`.  `PlannerWit.theCrowdedRequest`
   is `theRoutineRequest` with the instance asking for 150 minutes instead of
   30, and neither free stretch is that wide.  This block claims its day says
   nothing.  `decide` refuses -- the note is there
   (`PlannerWit.the_day_with_no_room_carries_the_note_instead`). -/
set_option maxRecDepth 100000 in
theorem aDayWithNoRoomForARoutineSaysNothingAboutIt :
    (Planner.dayPlan PlannerWit.theCrowdedRequest).diagnostics.notes.val = [] := by decide

/- ===========================================================================
   APPENDED 2026-09-19, stage 6 run W-21, track P, step P7 (AGENTS 6.2).
   §8.2 step 7's three claims a reader would make and the kernel refuses.
   Cheats 213-215. -/
/- CHEAT 213 — Rest is all the free time left in the day.  Spec 8.2 step 7 says
   "leftover SLOTS after the budget", and a slot is what the cut made: at
   `PlannerWit.theRequest` the day is planned from 14:00 and the first slot
   starts at 14:20, because the morning's two blocks put the break counter at
   two and the cut opens with a 20-minute break.  Those 20 minutes are free and
   are NOT Rest -- nothing was cut there, so there is no slot for a Rest row to
   be a piece of.  This block claims a Rest row starting at 14:00.  `decide`
   refuses; `PlannerWit.the_rest_rows_are_the_slots_no_group_took` is the list. -/
set_option maxRecDepth 100000 in
theorem theRestRowsStartWhenTheDayDoes :
    (PlannerWit.theRequest.restRows.map (fun s => s.start)).head?
      = some (Cal.instantOf Cal.chicago 739867 840).sec := by decide

/- CHEAT 214 — an optional takes every minute it has left.  Spec 8.2 step 7
   says "within `max:`", and fork's own `want` is
   `cap_left_min().map_or(remaining_min, |l| remaining_min.min(l))`.
   `PlannerWit.theOptionalRequest`'s `^p2` has 60 minutes of work left and a
   `max:` of 90 with 70 of it already spent, so it may take 20.  This block
   claims the 60.  `decide` refuses
   (`PlannerWit.an_optional_asks_for_what_its_cap_leaves`). -/
set_option maxRecDepth 100000 in
theorem anOptionalTakesEveryMinuteItHasLeft :
    (PlannerWit.theOptionalRequest.optionalFold.map (fun o => (o.id, o.want))).getLast?
      = some (['p','2'], 60) := by decide

/- CHEAT 215 — a break the day keeps is free time an optional may use.  Fork
   `emit_segments` puts `kept_breaks` into the optionals' `occupied` list
   precisely so that it is not: a break work touches is the day's rest, and an
   optional dropped onto it is the day's rest spent.  At
   `PlannerWit.theBusyRequest` the cursor's four slots and the 14:00-14:20 kept
   break cover the window, so the only stretch left is after the last slot.
   This block claims the break is free.  `decide` refuses
   (`PlannerWit.the_break_the_day_keeps_is_not_free_for_an_optional`). -/
set_option maxRecDepth 100000 in
theorem aKeptBreakIsFreeTimeForAnOptional :
    PlannerWit.theBusyRequest.optionalFree
      = [((Cal.instantOf Cal.chicago 739867 840).sec,
          (Cal.instantOf Cal.chicago 739867 860).sec),
         ((Cal.instantOf Cal.chicago 739867 1140).sec,
          (Cal.instantOf Cal.chicago 739867 1290).sec)] := by decide

/- CHEAT 216 — §4.3's row is nine cells and a renderer that forgets one is a
   `format!` with one fewer `{}`, which compiles.  Here the row is a record:
   this block builds an `Emit.Row` without its `note` cell.  The elaborator
   refuses, which is what makes `Emit.cells_are_the_nine_in_order` a statement
   about every row there is rather than about the rows somebody remembered. -/
def rowWithoutANote : Emit.Row :=
  { time := [], ci := [], p := [], mark := [], title := [], parent := [],
    est := [], actual := [] }

/- CHEAT 217 — the overflow `emit.hhmm` cannot see: it formats whatever
   `DateTime` it is handed, so a minute-of-day arithmetic that ran past the day
   printed `24:00` and the column still looked right.  The time cell here goes
   through `Field.Clock = Fin 1440`; this block asks for 24:00 and `decide`
   refuses the bound (`Emit.clockOfLocal` is where the bound is discharged). -/
def midnightTwice : Field.Clock := ⟨1440, by decide⟩

/- CHEAT 218 — G6 in its original shape: the wall's `⏰` in the MARK column,
   where it is two terminal columns wide and pushes every column after it one
   right.  `Emit.the_glyphs_stay_out_of_the_mark_column` says no segment's mark
   is any kind's glyph; this block claims a segment's is.  `rfl` refuses, and so
   would any proof, because the theorem above it is the refutation. -/
theorem theMarkColumnTakesTheWallGlyph (s : Planner.Seg) :
    Emit.markChar s = Emit.glyphOf Planner.SegKind.wall := rfl

/- CHEAT 240 — W-36 track T (README gap 2920): the host's worked minutes cross the planner
   wire as `RuntimeIn.worked : Option (Fin (Look.maxDayMin + 1))`, so a reading past a day cannot
   be held at all — `Planner.workedOf?` refuses 1441 (`a_worked_reading_past_a_day_is_refused`) and
   this block builds one by hand.  `decide` refuses the bound, which is what makes "a day at most"
   a fact about every request the planner reads rather than about the decoder alone. -/
def aWorkedReadingPastTheDay : Fin (Look.maxDayMin + 1) := ⟨1441, by decide⟩

/- ====================================================================
   W-41 TRACK K (stage 6): D78, D80 and D81's gap 3902.  Cheats 241-245, the first numbers above
   the file's highest (240).  CHEAT 240's sentence — "the host's worked minutes cross the planner
   wire as `Fin (Look.maxDayMin + 1)`" — is HISTORY since this step: `RuntimeIn.worked` is
   `Fin (Look.maxPlanMinutes + 1)` now (D81 gap 3902's width, reused), and CHEAT 240 still fails
   for its stated reason because it builds the TYPE it names, which still refuses 1441.
   ==================================================================== -/

/- CHEAT 241 — D81 gap 3902: the worked minutes' new bound bites at the width, as CHEAT 240's did
   at the day: one past `Look.maxPlanMinutes` is not a `Fin (Look.maxPlanMinutes + 1)`, and
   `decide` refuses the bound. -/
def aWorkedReadingPastTheWidth : Fin (Look.maxPlanMinutes + 1) := ⟨Look.maxPlanMinutes + 1, by decide⟩

/- CHEAT 242 — D80 (b): the conference's wire calls `^m2` `ci 0` and its plan file `ci 5`.  This
   block claims the two readings agree; `decide` computes `Planner.PlanReq.ciDisagreement` and
   refuses, which is the clause `PlanWire.planReqRefusal` refuses the request on, by name. -/
set_option maxRecDepth 400000 in
theorem theConferenceWireAgrees : PlannerWit.theConferenceRequest.ciDisagreement = none := by decide

/- CHEAT 243 — D80 (a): the last evening of 9999 runs past the calendar's last second.  This block
   claims its evening is inside the calendar; `decide` refuses, which is the clause the decoder
   refuses the request on (`eveningPastTheCalendar`). -/
set_option maxRecDepth 400000 in
theorem theLastEveningIsInsideTheCalendar :
    PlannerWit.theLastEveningRequest.eveningInsideTheCalendar = true := by decide

/- CHEAT 244 — D78: E1 as W-40 stated it — every Block row from `now` at most one block — at a
   running block logged ten seconds after `now`.  The fork's reservation (and the kernel's) runs a
   block plus the lead, 3,610 seconds; `decide` refuses the claim on the day itself. -/
set_option maxRecDepth 400000 in
theorem theOldE1HoldsAtAStartAfterNow :
    ∀ s ∈ (Planner.dayPlan PlannerWit.theStartAfterNowRequest).segments, s.val.kind = Planner.SegKind.block →
      PlannerWit.theStartAfterNowRequest.now.sec ≤ s.val.start →
      s.val.stop - s.val.start ≤ (Planner.dayPlan PlannerWit.theStartAfterNowRequest).blockMin * 60 := by
  decide

/- CHEAT 245 — D81 keeps a RUNNING BREAK's start bounded by `now` (the host reads it as the latest
   instant at or before `now`; D78 does not reach it).  This block claims `Planner.mkBreak?` builds a
   break that begins a second after `now`; `decide` refuses. -/
theorem aBreakAfterNowIsBuilt : (Planner.mkBreak? ⟨1000, 0⟩ ⟨some ⟨1001, 0⟩, 10, none⟩).isSome = true := by
  decide

-- ===========================================================================
-- APPENDED 2026-10-02 (stage 6, run W-42, track G — owner D83, README gap 32 closed: the kernel
-- reads as a separator exactly what the host reads).  Appended at the end (§6.2: append, never
-- renumber).  Labels 260-265, a band above the 246+ the parallel tracks of W-42 count from, so
-- that the land step's renumber has nothing to merge (§6.2's three CHEAT 9s).
-- ===========================================================================

/- CHEAT 260 — the box widened past the host's.  A no-break space is `White_Space` and so a
   separator between two words (`isSp`), but fork 4748911's `state_at` asks the byte after `]` to
   be ASCII whitespace, and a no-break space is not: `- [ ]<NBSP>x` carries no box to the host.
   The claim below is that it carries one here; `boxAt` refuses (`isBoxEnd`), and README gap
   4130's world — a no-break space after `[ ]` — is a box-less item to both readers. -/
theorem aNoBreakSpaceEndsABox : (boxAt "[ ]\u00A0x".toList).isSome = true := by decide

/- CHEAT 261 — the indent widened with the separator.  The host reads no indentation on an item
   line at all (`ItemLine::parse` wants `- ` at column 0); this kernel reads spaces (README gap
   46), and D83 widened the separator between words, not that.  The claim is that a tab-indented
   line is an item; `parseItem` splits the indent with `isIndent`, the space alone, and the line
   is prose to both readers. -/
theorem aTabIndentsAnItem : isItemLine "\t- [ ] x ^a1".toList = true := by decide

/- CHEAT 262 — the separator widened past `White_Space`.  A zero-width space looks like a gap and
   is not one to the host (`char::is_whitespace` is false of U+200B), so `a<ZWSP>b` is one word to
   both readers; the claim is that it separates. -/
theorem aZeroWidthSpaceSeparates : isSp '\u200B' = true := by decide

/- CHEAT 263 — the title key joined with one space, as it was until W-42 (README gap 403).  The
   host keys an id-less line by its title SPAN, verbatim; a key that collapsed `a  b` to `a b`
   would name a routine the host never sends, and once a tab is a separator it would collapse
   `Morning<TAB>stretch` too — a candidate the planner request then refuses as `ciDisagrees …
   plan none`.  The claim is the old join; `Field.titleKey` keeps the span. -/
theorem theTitleKeyJoinsWithOneSpace :
    Field.titleKey ⟨[], false, tokenize " a  b dur:1h".toList, []⟩ = some "a b".toList := by
  decide

/- CHEAT 264 — an unset that glues a box to a no-break space.  Fork 4748911's `remove_token`
   drops a token with its separator, so `- [x] due:2026-09-10<NBSP>Title ^a1` unset `due` is
   `- [x]<NBSP>Title ^a1` to the fork — a box-less line on the next read, its done state gone.
   The claim is that the kernel writes the same; `Field.unsetKey` keeps the box ended
   (`Field.endBox`). -/
theorem anUnsetGluesABoxToANoBreakSpace :
    serializeItem ['a', '1'] Glyph.done
      (Field.unsetKey .due ⟨[], true, tokenize " due:2026-09-10\u00A0Title ^a1".toList, []⟩)
      = "- [x]\u00A0Title ^a1".toList := by decide

/- CHEAT 265 — a comment opener indented by a tab.  `grammar::opens_comment` trims spaces only
   (`Plan.opensComment` is its mirror, D47), so a tab-indented `<!--` opens nothing to either
   reader; the claim is that it opens a comment once a tab is a separator. -/
theorem aTabIndentsACommentOpener : opensComment "\t<!-- x".toList = true := by decide

/- ====================================================================
   W-42 track R — the owner's D87 (README gap 4137, parity P81): a break
   taken inside a block is not block time.  Cheats 246-248, numbered from
   the highest in the checkout (245); the merge renumbers if another track
   took the same numbers (AGENTS 6.2).
   ==================================================================== -/

/- CHEAT 246 — the fork's credit: `start a` 09:00, a twenty-minute `break` at
   09:30, `stop a` 10:00, credited the block's whole sixty-minute span.  D87's
   `Replay.brkFx` stops the clock across the break, so `decide` computes 40 and
   refuses 60. -/
theorem aStoppedBlockIsCreditedItsSpan :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
        Replay.bE 2 63924370200 (.brk 20 (some 20) none), Replay.bE 3 63924372000 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 247 — the fork's drawing: the same day's segments claimed to be two,
   one Block `[09:00, 10:00]` across the Break.  `decide` computes the three
   segments `[09:00, 09:30]`, `[09:30, 09:50]`, `[09:50, 10:00]` and refuses. -/
theorem aStoppedBlockIsDrawnAcrossItsBreak :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
        Replay.bE 2 63924370200 (.brk 20 (some 20) none), Replay.bE 3 63924372000 (.stop ['a'] 0)]).days.get
        739865).map (fun a => a.segments.length) = some 2 := by
  decide

/- CHEAT 248 — C5's `arm_split` over every event, which D87 makes false: a
   `break`'s arm with a block running is its day family arm alone.  `decide`
   computes the arm, which also stops the block's clock, and refuses. -/
theorem aBreaksArmIsItsDayArm :
    Replay.arm (fun _ => 739865) (fun _ => none)
        ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none, 0, none,
          739865, [], []⟩, none, none, [], none, []⟩
        (Replay.bE 2 63924370200 (.brk 20 (some 20) none)) (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865
      = Replay.dayArm (fun _ => 739865) (fun _ => none) (Replay.bE 2 63924370200 (.brk 20 (some 20) none))
          (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865 := by
  decide

/- ====================================================================
   W-43 track K — the owner's D92 (README gap 4241, parity P85): a break
   that runs INTO a block's start is not block time.  Cheats 266-268,
   numbered from the highest in the checkout (265); the merge renumbers if
   another track took the same numbers (AGENTS 6.2).  CHEAT 201's comment and
   CHEAT 248's machine literal (`Replay.Machine` gained `brk`) were edited so
   each still fails for the reason it states.
   ==================================================================== -/

/- CHEAT 266 — the fork's credit for a break logged before a block's `start`:
   a ten-minute `break` at 08:55, `start a` 09:00, `stop a` 10:00, credited
   the block's whole sixty-minute span.  D92's Replay.restartAt started the
   clock at the break's end (`Replay.settle` since D99), so `decide` computes 55 and refuses 60. -/
theorem aBlockBegunInsideABreakIsCreditedItsSpan :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368100 (.brk 10 (some 10) none),
        Replay.bE 2 63924368400 (Replay.bStart ['a']), Replay.bE 3 63924372000 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 267 — the planner's day for that log, as fork 4748911 drew it: the
   census log with a break at 07:00 lasting into `m1`'s 07:05 `start`
   claimed to lay a Block across the Break.  `decide` computes the Block from
   07:15 and `noBlockOverABreak` true, and refuses. -/
theorem theIntoBreakDayLaysABlockAcrossTheBreak :
    PlanCheck.noBlockOverABreak PlannerWit.theIntoBreakRequest
      (Planner.dayPlan PlannerWit.theIntoBreakRequest) = false := by decide

/- CHEAT 268 — one rule at every place a clock starts: an `unpause` inside a
   break claimed to restart the clock at the unpause.  `start a` 09:00, `pause
   a` 09:10, a twenty-minute `break` at 09:15, `unpause a` 09:30, `stop a`
   10:00, credited 10 + 30 = 40.  `decide` computes 35 and refuses. -/
theorem anUnpauseInsideABreakRestartsAtTheUnpause :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
        Replay.bE 2 63924369000 (.pause ['a']), Replay.bE 3 63924369300 (.brk 20 (some 20) none),
        Replay.bE 4 63924370200 (.unpause ['a']), Replay.bE 5 63924372000 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes) = some 40 := by
  decide

-- ===========================================================================
-- APPENDED 2026-10-03 (stage 6, run W-43, track G — README gap 4346: an item line reads a date
-- through chrono's readers, `Log.instDate?` and `Field.parseDT`, the one reading of a date).
-- Appended at the end (§6.2: append, never renumber).  Labels 269-273 (266-270 on track G's branch; renumbered at the W-43 land, track K took 266-268), numbered from the highest
-- in the checkout (265); the land step renumbers if another track of W-43 took the same numbers.
-- ===========================================================================

/- CHEAT 269 — the item line's old date reader.  Until W-43 `due:` read `Field.parseDate` (four
   digits, two, two), so `due:+026-09-09` was no date to the kernel while `lime-core`'s `parse_date`
   read the year 26.  This block claims the line still reads no date there; `decide` computes the
   year-26 day and refuses. -/
theorem aSignedYearIsNoDateOnTheLine :
    Field.parseMoment ['+','0','2','6','-','0','9','-','0','9'] = none := by
  decide

/- CHEAT 270 — a date before 0001-01-01 read as a day.  chrono reads `0000-01-01` (year 0) and
   `-001-01-01` (year −1); `Day := Nat` starts at 0001-01-01 (AGENTS §4), so the kernel reads no
   date there (parity P88).  This block claims `instDate?` answers for year 0; `decide` refuses. -/
theorem aYearZeroDateIsADay :
    (Log.instDate? ['0','0','0','0','-','0','1','-','0','1']).isSome = true := by
  decide

/- CHEAT 271 — `parse_datetime` without its sixteen bytes.  chrono reads `+2026-9-7T08:15`
   (fifteen bytes) as 2026-09-07 08:15, and `model::parse_datetime` refuses it on its length before
   chrono runs.  This block claims the line reads it; `decide` refuses. -/
theorem aFifteenByteDateTimeIsRead :
    (Field.parseDT ['+','2','0','2','6','-','9','-','7','T','0','8',':','1','5']).isSome = true := by
  decide

/- CHEAT 272 — `parse_time` read as RFC 3339's clock.  chrono's `%H` skips whitespace, so
   ` 9:05` is 09:05 to `model::parse_time` (five bytes), where RFC 3339's `HH:MM` (`parseClock`)
   reads nothing.  This block claims the line's time reader refuses it; `decide` refuses. -/
theorem aSpacedClockIsNoTime : Field.parseTime [' ','9',':','0','5'] = none := by
  decide

/- CHEAT 273 — a date past 9999 written back by an edit.  The line reads `due:+10000-1-7` as the
   host does, and no render writes a five-digit year in `parse_date`'s ten bytes, so the edit path's
   `guardWf` refuses it by name.  This block claims the edit takes it; `decide` refuses. -/
theorem aYearPast9999IsEdited :
    (editValOf .due ['+','1','0','0','0','0','-','1','-','7']).isSome = true := by
  decide

/- ====================================================================
   W-44 track K — the owner's D94 (README gaps 4361 and 4506, parity P92):
   every break on a block's ledger days is netted, wherever the block's clock
   meets it.  Cheats 274-279, numbered from the highest in the checkout
   (273); the land renumbers if another track took the same numbers (AGENTS
   6.2).  CHEAT 201's comment (section 14's day moved to a break logged after
   `m1`'s `done`) and CHEAT 248's machine literal (`Replay.Machine.brks`,
   `Replay.Block.day`) were edited so each still fails for the reason it
   states.
   ==================================================================== -/

/- CHEAT 274 — D92's credit for a clock started inside an EARLIER break with a
   later one stepped between (README gap 4506): a thirty-minute `break` at
   09:00, a five-minute one at 09:40, `start a` 09:10, `stop a` 10:00,
   credited the clock's whole 50 minutes.  D94's Replay.restartAt started it
   past the first break and Replay.closeSub cut it around the second (one `Replay.settle` since D99), so
   `decide` computes 25 — the host's union — and refuses 50. -/
theorem aStartInsideAnEarlierBreakIsCreditedTheStretch :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (.brk 30 (some 30) none),
        Replay.bE 2 63924370800 (.brk 5 (some 5) none), Replay.bE 3 63924369000 (Replay.bStart ['a']),
        Replay.bE 4 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 50 := by
  decide

/- CHEAT 275 — D92's credit for a break logged ahead of a `start` but begun
   after it (README gap 4361): a ten-minute `break` at 09:05 logged before
   `start a` 09:00, `stop a` 10:00, credited 60.  D94's Replay.closeSub (`Replay.settle` since D99) cuts
   the stretch where the clock meets the break, so `decide` computes 50 and
   refuses 60. -/
theorem aBreakAheadOfItsClockIsNotNetted :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368700 (.brk 10 (some 10) none),
        Replay.bE 2 63924368400 (Replay.bStart ['a']), Replay.bE 3 63924372000 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 276 — the planner's day for gap 4361's log as D92 drew it: the census
   log with its break stamped 07:10 logged ahead of `m1`'s 07:05 `start`
   claimed to lay a Block across the Break.  `decide` computes `m1` cut around
   the Break and `noBlockOverABreak` true, and refuses. -/
theorem theAheadBreakDayLaysABlockAcrossTheBreak :
    PlanCheck.noBlockOverABreak PlannerWit.theAheadBreakRequest
      (Planner.dayPlan PlannerWit.theAheadBreakRequest) = false := by decide

/- CHEAT 277 — D94's bound claimed not to bite: a break 32 ledger days older
   than the newest held, kept.  `decide` computes `Replay.pruneBrks` dropping
   it, and refuses. -/
theorem pruneBrksKeepsABreakPastTheBound :
    (Replay.pruneBrks [⟨(⟨0, 0⟩, ⟨false, 0⟩), (⟨60, 0⟩, ⟨false, 0⟩), 40⟩,
      ⟨(⟨0, 0⟩, ⟨false, 0⟩), (⟨60, 0⟩, ⟨false, 0⟩), 8⟩]).length = 2 := by
  decide

/- CHEAT 278 — a break filed on the ledger day BEFORE the block's netted
   (README gap 4363): the 6th's wake, a thirty-minute `break` at 06:50 on the
   7th (before the 7th's 07:00 wake), `start a` 07:10, `stop a` 08:00,
   credited 40 as D92 restarted the clock at the break's end.  The host reads
   a block's idle marks from its `start`'s day on, and so does D94's machine:
   `decide` computes 50 and refuses 40. -/
theorem aBreakOnTheDayBeforeIsNetted :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924274800 (.wake 420 none),
        Replay.bE 2 63924360600 (.brk 30 (some 30) none), Replay.bE 3 63924361200 (.wake 420 none),
        Replay.bE 4 63924361800 (Replay.bStart ['a']), Replay.bE 5 63924364800 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes) = some 40 := by
  decide

/- CHEAT 279 — the open block read as D92 read it, its clock running from its
   `start` across a break held ahead of it: a fifteen-minute `break` at 10:00
   logged before `start a` 09:50, nothing after — claimed open since 09:50
   with nothing banked.  D94's `Replay.openOf` reads it past the break:
   `decide` computes ten minutes banked and the clock from 10:15, and refuses. -/
theorem theOpenBlockRunsAcrossABreakHeldAheadOfIt :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924372000 (.brk 15 (some 15) none),
        Replay.bE 2 63924371400 (Replay.bStart ['a'])]).openBlock.map
        (fun b => (b.workedMin, b.since.map (·.1.sec))) = some (0, some 63924371400) := by
  decide

/- ===========================================================================
   APPENDED 2026-10-05: stage 6, run W-46, TRACK K — the owner's D105 (README
   "Stage 6 — W-46 track K", gaps 1034, 1085, 4740; parity P100): `lime break`
   logs a `break_start`, and the replay holds the running break until a
   `break` line ends it.  Cheats 280-283 (whoever lands renumbers).
   =========================================================================== -/

/- CHEAT 280 — the pairing denied: a `break_start` at 09:30 and the `break`
   line that ends it, claimed to leave the break running.  `brkFx` ends the
   running break on every machine it writes: `decide` computes `none` and
   refuses. -/
theorem aBreakLineLeavesTheBreakRunning :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924370200 (.brkStart 20 none),
        Replay.bE 2 63924370200 (.brk 20 (some 15) none)]).openBreak ≠ none := by
  decide

/- CHEAT 281 — an undone `break_start` claimed still running: `lime undo` of
   `lime break` appends `undo{of: "break_start"}`, and the mask cancels the
   start, so no break runs.  `decide` refuses. -/
theorem anUndoneBreakStartStillRuns :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924370200 (.brkStart 20 none),
        Replay.bE 2 63924370260 (.undo Log.Kind.brkStart.tag none)]).openBreak ≠ none := by
  decide

/- CHEAT 282 — the kernel claimed to read a `break_start` as fork 4748911
   does, as an unknown event (parity P100).  It is a known kind: the unknown
   count stays 0, and `decide` refuses 1. -/
theorem aBreakStartIsAnUnknownEvent :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924370200 (.brkStart 20 none)]).unknown = 1 := by
  decide

/- CHEAT 283 — a running break claimed to hold no ledger day: the `break` line
   that ends it is stamped at its start, so its day is one the machine can
   still write (`Seal.machineDays`), and a reseal may not pass it.  `decide`
   computes `[739865]` and refuses `[]`. -/
theorem aRunningBreakHoldsNoLedgerDay :
    Seal.machineDays ⟨none, none, none, [], some ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), 20, none, 739865⟩, [], none⟩ = [] := by
  decide

/- ===========================================================================
   APPENDED 2026-10-06: stage 6, run W-47, TRACK K — the owner's D99 (README
   "Stage 6 — W-47 track K", gap 4520a; parity P104): a mark logged out of its
   stamp's order is netted where it lies, and the open block is re-drawn at
   every mark (`Replay.settle`).  Cheats 284-286, numbered from the highest in
   the checkout (283); whoever lands renumbers (AGENTS 6.2).  CHEAT 248's
   literal (`Replay.Machine` gained `brkOpen` at D105 and `Replay.Block` gained
   `idle` and `drawn` here) was edited so it fails for the reason it states:
   it failed on the literal's arity from D105 until this step.
   =========================================================================== -/

/- CHEAT 284 — the class table's M1 (S7) credited as D94 read it: `start a`
   08:00, `pause` 09:00, `unpause` 09:10, then a twenty-minute `break` at 08:30
   logged after them, `stop` 10:00, credited 110 — the stretch the pause closed
   kept whole.  `Replay.settle` nets the break from that stretch where it lies:
   `decide` computes 90, the host's union, and refuses 110. -/
theorem aBreakLoggedBehindAClosedStretchIsNotNetted :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (.pause ['a']), Replay.bE 3 63924369000 (.unpause ['a']),
        Replay.bE 4 63924366600 (.brk 20 (some 20) none), Replay.bE 5 63924372000 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes) = some 110 := by
  decide

/- CHEAT 285 — the open block's banked piece claimed undrawn while it runs
   (README gap 4525, as D94 left it): a fifteen-minute `break` at 10:00 logged
   ahead of `start a` 09:50 — the day claimed to hold no `Block` of `a`'s.
   `Replay.settle` draws `[09:50, 10:00]` at once: `decide` refuses. -/
theorem theOpenBlocksBankedPieceIsUndrawn :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924372000 (.brk 15 (some 15) none),
        Replay.bE 2 63924371400 (Replay.bStart ['a'])]).days.get 739865).map
        (fun a => a.segments.filter (fun g => g.kind == .block ['a'])) = some [] := by
  decide

/- CHEAT 286 — the class table's M7: a `pause` stamped BEFORE the block's
   `start` (logged inside it) claimed to idle the block, as D94 credited it:
   `start a` 09:00, `pause` 08:50, `unpause` 09:30, `stop` 10:00, credited 30.
   The host's pairing passes over a pause stamped before the block it would
   pause, and so does the replay since D99: `decide` computes 60 and refuses. -/
theorem aPauseStampedBeforeTheStartIdlesTheBlock :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
        Replay.bE 2 63924367800 (.pause ['a']), Replay.bE 3 63924370200 (.unpause ['a']),
        Replay.bE 4 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

/- ===========================================================================
   APPENDED 2026-10-06: stage 6, run W-47, TRACK K — the owner's D100 (README
   "Stage 6 — W-47 track K" §11, gap 4520b; parity P105): a break logged after
   a block closed, stamped inside it, is netted from it — the later break wins.
   Cheats 289-292, numbered above the highest this track has used (286 on the
   branch, 287 and 288 in the archived D110 snapshot, README §10); whoever lands
   renumbers (AGENTS 6.2).  CHEAT 201's request and comment, and CHEAT 248's
   and CHEAT 283's machine literals (`Replay.Machine` gained `closed`), were
   edited so each still fails for the reason it states: CHEAT 201 compiled at
   `theMidBreakRequest` once D100 cut that day's block around its break, and
   the two literals failed on their arity.
   =========================================================================== -/

/- CHEAT 289 — the mid-break day claimed to lay `m1`'s Block across the Break as
   the replay drew it before D100 (`PlannerWit.theMidBreakRequest`: a break
   stamped 07:10 inside `m1`'s 07:05-08:05 block, logged after its `done`).  The
   replay cuts the closed block around the break (`Replay.netClosed`), so the
   battery's `noBlockOverABreak` says `true` there: `decide` refuses `false`. -/
theorem theMidBreakDayStillLaysItsBlockAcrossTheBreak :
    PlanCheck.noBlockOverABreak PlannerWit.theMidBreakRequest
      (Planner.dayPlan PlannerWit.theMidBreakRequest) = false := by decide

/- CHEAT 290 — the class table's M11 credited as fork 4748911 and the replay
   before D100 credited it: `start a` 08:00, `done a` 09:00 (sixty), then a
   twenty-minute `break` at 08:30 logged after — the item claimed sixty.  The
   later break wins: `decide` computes forty and refuses sixty. -/
theorem aBreakLoggedAfterADoneIsNotNetted :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false),
        Replay.bE 3 63924366600 (.brk 20 (some 20) none)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 291 — the duration fit claimed to read M11's `done` as it was logged,
   sixty minutes, past the break logged after it.  The observation is netted
   with the block (`Replay.netDur`): `decide` computes `[40]` and refuses
   `[60]`. -/
theorem theFitReadsADonesLoggedMinutesPastALateBreak :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false),
        Replay.bE 3 63924366600 (.brk 20 (some 20) none)]).durations.map (·.actualMin) = [60] := by
  decide

/- CHEAT 292 — D100's bound claimed absent: a block closed thirty-two ledger
   days before the newest one held, netted by a late break across it (forty).
   `Replay.pruneClosed` dropped it when the newer block closed (README gap
   4917): `decide` computes sixty and refuses forty. -/
theorem aLateBreakNetsABlockPrunedFromTheMachine :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false),
        Replay.bE 3 63927129600 (Replay.bStart ['b']), Replay.bE 4 63927133200 (Replay.bDone ['b'] 60 false),
        Replay.bE 5 63924366600 (.brk 20 (some 20) none)]).items.get ['a']).map (·.minutes) = some 40 := by
  decide

/- ===========================================================================
   APPENDED 2026-10-06: stage 6 (the planner), run W-47, TRACK K, second
   commit — the owner's D110 (README gap 4748: a block started inside a wall
   is paused from its start until the wall ends) and D99's wall-rule days
   (gaps 4616 and 4619).  Numbered from the highest cheat in the checkout
   (286); whoever lands renumbers (AGENTS 6.2).
   =========================================================================== -/

/- CHEAT 287 — a block started INSIDE a wall claimed unpaused by it, as D61
   read it ("the wall did not start while the block ran"): the block begun at
   1500 inside the wall [1000, 2000), asked at 1800 with nothing logged, claimed
   to write nothing.  D110's rule pauses it at its own start: `decide` computes
   the one pause and refuses. -/
theorem aBlockStartedInsideAWallIsNotPausedByIt :
    WallTimer.writes ⟨1500, 0⟩ ⟨1800, 0⟩ none [] [(1000, 2000)] = [] := by
  decide

/- CHEAT 288 — gap 4616's block claimed paused again at a meeting: `t4` begun
   at 500 on ledger day 5 and paused there at 900, asked on day 7 with a
   meeting from 1000 — claimed to write something, as the rule did when it
   read only days 6 and 7 and never saw the block's own pause.  The rule reads
   the days from the block's own ledger day since W-47: the timer is already
   stopped, nothing is written, and `decide` refuses the claim. -/
theorem aBlockPausedOnAnEarlierDayIsPausedAgainAtAMeeting :
    (match WallTimer.answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [⟨5, none, some ⟨none, [.pause ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At)], none⟩,
          [], [], [], [], [], []⟩], some ⟨['t','4'], ((⟨500, 0⟩, Cal.Offset.utc) : Replay.At), 0, none, true, 5⟩, none, none, [],
          none, none, 0, 0, none, [], [], 0⟩)
        (fun _ _ => [⟨['g','1'], 7, 7, 1000, 1000, 2000⟩]) 0 (some 7) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]
      | .error _ => false) = false := by
  decide

/- ===========================================================================
   APPENDED 2026-10-05: stage 6, run W-47, TRACK L — the owner's D111 (README
   gap 4904; parity P108): a logged `break_start`'s place is read through the
   ONE table of places (`Log.placeWords`), in the log grammar, and any other
   word makes the line malformed; the planner's reader and the host read the
   same table.  Cheats 300-303 (whoever lands renumbers).
   =========================================================================== -/

/- CHEAT 300 — gap 4904's hand edit claimed to read as a running break's
   place: the reader names `"where": "moon"` `badField where`, so the emit
   (which IS the reader, D16) is an error and `rfl` refuses the entry. -/
theorem theMoonIsAPlace :
    Log.emitEvent Log.Kind.brkStart.tag [(['p','l','a','n','n','e','d','_','m','i','n'], .num 20),
        (['w','h','e','r','e'], .str ['m','o','o','n'])]
      = .ok (.brkStart 20 (some ['m','o','o','n'])) := rfl

/- CHEAT 301 — the per-field round trip claimed at EVERY value, as stage 5 B3
   stated it: a `place` the writer writes with a word the table does not hold
   is `badField`, not read back (`Log.readF_renderF_at_every_value_is_refuted`).
   `rfl` refuses. -/
theorem everyPlaceRoundTrips :
    Log.readF ['w','h','e','r','e'] .place (Log.renderF .place (some ['m','o','o','n']))
      = .ok (some ['m','o','o','n']) := rfl

/- CHEAT 302 — a `break_start` with an unknown place claimed canonical, so
   that `the_log_reads_what_it_renders` would read it back: `Event.canonical`
   asks the table, and `decide` computes `false`. -/
theorem aMoonBreakStartIsCanonical :
    (Log.Event.brkStart 20 (some ['m','o','o','n'])).canonical = true := by
  decide

/- CHEAT 303 — the planner's reader claimed to take a word the log's grammar
   refuses (gap 4904's two readers): `PlanWire.placeOf?` reads through
   `Log.isPlace`, and `decide` computes `none`. -/
theorem thePlannerReadsTheMoon : (PlanWire.placeOf? ['m','o','o','n']).isSome = true := by
  decide

/- ===========================================================================
   APPENDED 2026-10-11: stage 6, run W-48, TRACK K — the owner's D114
   (README gap 5014; parity P115: a break still running when a wall ends
   holds the block) and D117 (README gaps 5036 and 3042; parity P116: a
   block resumed inside a wall is paused from its resume until the wall
   ends).  Cheats 304-305 (whoever lands renumbers).
   =========================================================================== -/

/- CHEAT 304 — D61's unpause claimed at the wall's end while a break that
   began inside the meeting still runs: `WallTimer.breakHolds` holds it, and
   `decide` computes the empty list. -/
theorem theWallEndUnpausesUnderARunningBreak :
    WallTimer.writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) (some ⟨1200, 0⟩)
      [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [(false, 1000, 2000)] := by
  decide

/- CHEAT 305 — a block interrupted across the wall's start and resumed
   inside it claimed paused at the wall's start (or not at all): its pause is
   stamped at the resume (`WallTimer.pauseSec`), and `decide` computes it. -/
theorem aResumedBlockIsPausedAtTheWallsStart :
    WallTimer.marksOf (⟨500, 0⟩ : Cal.Instant) (WallTimer.intSpans [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)])
        (WallTimer.writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none
          [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)])
      = [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨2000, 0⟩, Cal.Offset.utc) : Replay.At)] := by
  decide

/- ===========================================================================
   APPENDED 2026-10-11: stage 6, run W-48, TRACK A — the owner's D108 (README
   gaps 4893 and 4876; parity P119: the day's first `plan` carries §7.4's
   hysteresis input, and the replay holds the open block's own extends).
   Cheats 320-323 (whoever lands renumbers).
   =========================================================================== -/

/- CHEAT 320 — **withdrawn at W-49 track L (README gap 5300; the owner's D125): the
   day's hysteresis input IS its latest input-carrying `plan`'s, so the claim it
   refuted is the law.**  It read: the day's input claimed to be its LAST `plan`'s,
   `(·.yesterday) = some [(['b'], 3)]`, refuted while `DayOp.plan` kept the
   ledger day's FIRST input in `yesterday` beside the latest in `late` — two
   answers to one question.  `yesterday` is gone, and the positive statement is
   `Replay.a_day_keeps_its_latest_plans_hysteresis_input`; what still must fail is
   CHEAT 394, below — a line stamped on an EARLIER calendar date taking the slot. -/

/- CHEAT 321 — an `extend` of the open block claimed to leave the block's own
   minutes where they were (the replay before D108): `extendFx` grows `ext`,
   and `decide` computes 15. -/
theorem anExtendLeavesTheOpenBlockAlone :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
      Replay.bE 2 63924369300 (.extend ['a'] 15)]).openBlock.map (·.ext) = some 0 := by
  decide

/- CHEAT 322 — a `p` past a `u8` claimed read at the hysteresis input: the
   reader names it `badField yesterday` (serde's `u8`), so `rfl` fails. -/
theorem aPriorityOf256IsRead :
    Log.emitEvent Log.Kind.plan.tag [(['h','a','s','h'], .str ['h']),
        (['r','e','p','l','a','n','s','_','t','o','d','a','y'], .num 1), (['d','r','i','f','t','_','m','i','n'], .num 0),
        (['y','e','s','t','e','r','d','a','y'], .obj [(['d','1'], .num 256)])]
      = .ok (.plan ['h'] 1 0 [(['d','1'], 0)]) := by
  rfl

/- CHEAT 323 — every `plan` claimed to write its (empty) hysteresis input, so
   every `plan` line but the day's first would differ from fork 4748911's: the
   empty map is skipped (`renderF`'s `prios` arm), and `rfl` fails. -/
theorem anEmptyHysteresisInputIsWritten :
    (Log.Event.plan ['h'] 1 0 []).fields = [(['h','a','s','h'], .str ['h']),
      (['r','e','p','l','a','n','s','_','t','o','d','a','y'], .num 1), (['d','r','i','f','t','_','m','i','n'], .num 0),
      (['y','e','s','t','e','r','d','a','y'], .obj [])] := by
  rfl

/- ===========================================================================
   APPENDED 2026-10-11: stage 6, run W-48, TRACK A, second commit — README gap
   5027 (the re-draw's compiled twins).  Cheats 324-325 (whoever lands
   renumbers).
   =========================================================================== -/

/- CHEAT 324 — spans that overlap claimed apart, so the one pass would draw
   pieces `pieces` itself does not: `apart` reads each end against the next
   start, and `decide` computes `false`. -/
theorem overlappingSpansAreApart : Replay.apart [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At), (((⟨63924364800 + 300, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)] = true := by
  decide

/- CHEAT 325 — the merge claimed to keep a piece a new span moved: the old
   `[600, 900)` is no new span, and `decide` computes it un-drawn. -/
theorem theMergeKeepsAMovedPiece :
    (Replay.redrawWalk (fun _ => 8) [⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).2, 7⟩]
        [(((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)]).2.1 = [] := by
  decide

/- ===========================================================================
   APPENDED 2026-10-11: stage 6, run W-48, TRACK K (third commit) — the
   owner's D115 (README gap 5034; parity P120: a late `start` stamped inside
   a block a later `done` closed cuts it), D119 (README gaps 4913, 4917 and
   5029; parity P121: a late interruption is netted from the block it
   crosses) and D116 (README gap 5035; parity P122: a break is read at its
   `break_start`'s place).  Cheats 306-308 as the track wrote them, 326-328 since the W-48 repair landed them.
   =========================================================================== -/

/- CHEAT 326 — the block a late `start` is stamped inside claimed to keep its
   whole credit, as fork 4748911 read it: `Replay.netStart` cuts it at the
   start, and `decide` computes thirty. -/
theorem aLateStartLeavesTheClosedBlockWhole :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (Replay.bStart ['b']),
        Replay.bE 4 63924370200 (.stop ['b'] 0)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 327 — a late interruption claimed to leave the block it crosses
   whole: the `resume` nets it (`Replay.netClosed`), and `decide` computes
   fifty. -/
theorem aLateInterruptionLeavesTheBlockWhole :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (.interrupt none),
        Replay.bE 4 63924367200 (.resume 10 [])]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 328 — a break claimed to be read at the word its END line writes,
   a second reading of its place: `Replay.placed` reads the `break_start`'s,
   and `decide` computes `walk`. -/
theorem aBreakIsReadAtItsEndLinesWord :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (.brkStart 10 (some ['w','a','l','k'])),
        Replay.bE 2 63924364800 (.brk 10 (some 10) (some ['m','o','o','n']))]).days.get 739865).map
      (fun a => a.breaks.map (·.where_)) = some [some ['m','o','o','n']] := by
  decide

/- ===========================================================================
   APPENDED 2026-10-11: stage 6, run W-48, THE REPAIR — D108 read by the plan
   lines' own stamps (README gaps 5210 and 5211): the day record keeps the
   last `plan` that carried a hysteresis input, beside the first.  Cheats
   329-330.
   =========================================================================== -/

/- CHEAT 329 — the latest input claimed to be the day's first, so a calendar
   day's first `plan` written before the wake (filed under the previous ledger
   day) would be read as nothing: `late` is the last `plan` that carried one,
   and `decide` computes `b 3`. -/
theorem theLatestInputIsTheDaysFirst :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (.plan ['h','1'] 0 0 [(['a'], 6)]),
      Replay.bE 2 63924370200 (.plan ['h','2'] 1 0 [(['b'], 3)])]).days.get 739865).map (·.late) = some [(['a'], 6)] := by
  decide

/- CHEAT 330 — a `plan` that carries no input claimed to clear the latest:
   it leaves it, and `decide` computes `b 3`. -/
theorem aPlanWithoutAnInputClearsTheLatest :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924370200 (.plan ['h','2'] 0 0 [(['b'], 3)]),
      Replay.bE 2 63924372000 (.plan ['h','3'] 1 0 [])]).days.get 739865).map (·.late) = some [] := by
  decide

/- ===========================================================================
   APPENDED 2026-10-13: stage 6, run W-49, TRACK P — the planner's rows in one
   call, at every length (the owner's D123 and D124; README gaps 5212 and 5130).
   Cheats 331-332.
   =========================================================================== -/

/- CHEAT 331 — a planned day's answer claimed to carry its rows and no
   divider, so the budget and the window's end would have to cross the wire a
   second time (gap 5132): `EmitWire.dayRowsPairs` is the rows AND the day's own
   divider, two pairs, and `rfl` cannot make two one. -/
theorem aPlannedDaysRowsCarryNoDivider (r : Planner.PlanReq) (d : Planner.DayPlan) :
    (EmitWire.dayRowsPairs r d).length = 1 := by
  rfl

/- CHEAT 332 — a day the planner answers claimed to fit under the old row cap
   (`Planner.maxCands`), the bound D123 removed from the reader: the planner's
   day has no segment bound (D28), so nothing proves it, and `omega` fails. -/
theorem aPlannedDayFitsUnderTheOldRowCap (r : Planner.PlanReq) (d : Planner.DayPlan) :
    (EmitWire.RowReq.ofDay r d).segs.length ≤ Planner.maxCands := by
  omega
   APPENDED 2026-10-13: stage 6, run W-49, TRACK W — the remainder after a
   wall that holds the running block (README gap 5217, parity P123; the
   owner's D110, D117 and D114).  Cheats 361-365.
   =========================================================================== -/

/- CHEAT 361 — the held block's reservation claimed to start at `now`, as
   §8.2 choice 5b's did until W-49: inside the meeting at 13:30 it starts at
   the meeting's end, 13:50, and `decide` computes it. -/
set_option maxRecDepth 400000 in
theorem theHeldReservationStartsAtNow :
    PlannerWit.theHeldRequest.activeRun.map (·.start) = some PlannerWit.theHeldRequest.now.sec := by
  decide

/- CHEAT 362 — the held block's row claimed `▶`: it is not running at
   `now`, and `Planner.PlanReq.activeRow` gives it no `▶` and no note. -/
set_option maxRecDepth 400000 in
theorem theHeldRowIsCurrent :
    PlannerWit.theHeldRequest.activeRow.map (·.flags.current) = [true] := by
  decide

/- CHEAT 363 — the meeting claimed to reserve nothing, as the fork's
   active_run refuses a paused timer: the reservation is there. -/
set_option maxRecDepth 400000 in
theorem theHeldBlockIsReservedNowhere :
    PlannerWit.theHeldRequest.activeRun = none := by
  decide

/- CHEAT 364 — D114's break claimed to reserve nothing (W-35's
   `a_running_break_pauses_the_block` as written): the block it holds past
   the meeting is reserved from the break's end. -/
set_option maxRecDepth 400000 in
theorem theBreakThatHoldsReservesNothing :
    PlannerWit.theBreakHeldRequest.activeRun = none := by
  decide

/- CHEAT 365 — an overrun break that holds the block claimed to release it
   at `now`: its end is the user's to say, and nothing is reserved. -/
set_option maxRecDepth 400000 in
theorem theOverrunBreakReleasesAtNow :
    PlannerWit.theOverrunHeldRequest.activeRun.isSome = true := by
   APPENDED 2026-10-13: stage 6, run W-49, TRACK L — a block closed, stopped
   or paused while a logged break runs is read as it will be once the break's
   line arrives (README gap 5180, `Replay.runNet`, `Replay.runSpan`).  Cheats
   391-393; and D108's one answer (README gap 5300), cheat 394.
   =========================================================================== -/

/- CHEAT 391 — a `done` under a running break claimed to keep its whole
   sixty minutes, the break's span read as block AND as break: `runNet` nets
   it at the close, and `decide` computes thirty. -/
theorem aDoneUnderARunningBreakKeepsItsMinutes :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924366600 (.brkStart 20 none),
        Replay.bE 3 63924368400 (Replay.bDone ['a'] 60 false)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 392 — a block paused under a running break claimed to have worked
   up to its pause: its drawing stops at the break's start (`runSpan`), and
   `decide` computes thirty. -/
theorem aPauseUnderARunningBreakWorksToThePause :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924366600 (.brkStart 20 none),
        Replay.bE 3 63924368400 (.pause ['a'])]).openBlock.map (·.workedMin) = some 60 := by
  decide

/- CHEAT 393 — a `break_start` logged after a `done` and stamped inside its
   block claimed to net nothing until the break's line arrives (the order a
   sync appends two machines' lines in): the `break_start` arm nets the held
   block (`runNet`), and `decide` computes thirty. -/
theorem aBreakStartLoggedAfterADoneNetsNothing :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
        Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false),
        Replay.bE 3 63924366600 (.brkStart 20 none)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/- CHEAT 394 — a `plan` a clock behind the log stamped on an EARLIER calendar
   date (23:59 on the 7th, logged after 00:26 on the 8th) claimed to take the
   day's input: the slot keeps the later date's (`Replay.notBefore`, README gap
   5300), and `decide` computes `a 6`. -/
theorem anEarlierDatesLineTakesTheInput :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924361200 (.wake 0 none),
      Replay.bE 2 63924423960 (.plan ['h','1'] 0 0 [(['a'], 6)]),
      Replay.bE 3 63924422340 (.plan ['h','2'] 1 0 [(['b'], 3)])]).days.get 739865).map (·.late)
      = some [(['b'], 3)] := by
  decide

/- ===== APPENDED W-49 TRACK Y (README "Stage 6 — W-49 track Y", gap 5161): cheats 441-442.  The
   planner section's `state.yesterday` left the decoder with the field it filled; these two say the
   type now forbids what the deleted decoder bounded. ===== -/

/- CHEAT 441 — a planner request's runtime claimed to carry yesterday's stored
   priorities: `Planner.RuntimeIn` has no such field since W-49 track Y (ranking
   reads each candidate's `Look.Cand.yesterday`, one spelling of the fact), so
   the projection is an invalid field. -/
def aRuntimeCarriesYesterday (s : Planner.RuntimeIn) := s.yesterday

/- CHEAT 442 — the planner section's refusal of a stored priority past seven
   claimed to stand: `PlanWire.PlannerRefusal` holds no such constructor since
   W-49 track Y, so the name is unknown. -/
def theYesterdayRefusalStands : PlanWire.PlannerRefusal :=
  PlanWire.PlannerRefusal.badYesterdayList

/- ===== APPENDED W-50 TRACK K (README "Stage 6 — W-50 track K", gaps 5430-5433; parity P127): cheats
   491-495.  The owner's D129: a `start` ends a running break at its instant, read in STAMP order; each cheat
   states the reading D129 replaced, and `decide` computes the one it took. ===== -/

/- CHEAT 491 — two machines merged: a `break_start` at 08:00 (never ended), then
   `start a` 08:30 and `done a` 09:30; the break claimed still running.  The
   start ended it (`Replay.endsBrk`): `decide` computes `none`. -/
theorem aStartLeavesTheBreakRunning :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (.brkStart 20 none),
      Replay.bE 2 63924366600 (Replay.bStart ['a']), Replay.bE 3 63924370200 (Replay.bDone ['a'] 60 false)]).openBreak.isSome
      = true := by
  decide

/- CHEAT 492 — route 2 (one machine): `start a` 08:30, `done a` 09:30, then a
   `break_start` written after it and stamped 08:00; the block claimed netted to
   nothing, as it was until D129.  The first start at or after 08:00 ends the
   break (`Replay.firstStart`): `decide` computes sixty. -/
theorem aLateBreakNetsTheBlockAfterIt :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924366600 (Replay.bStart ['a']),
      Replay.bE 2 63924370200 (Replay.bDone ['a'] 60 false),
      Replay.bE 3 63924364800 (.brkStart 20 none)]).items.get ['a']).map (·.minutes) = some 0 := by
  decide

/- CHEAT 493 — route 1: the late `break_start` stamped 23:00 the day before,
   claimed still running after the next morning's block.  It ended at 08:30:
   `decide` computes `false`. -/
theorem aBreakFromTheDayBeforeStillRuns :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924366600 (Replay.bStart ['a']),
      Replay.bE 2 63924370200 (Replay.bDone ['a'] 60 false),
      Replay.bE 3 63924332400 (.brkStart 15 none)]).openBreak.isSome = true := by
  decide

/- CHEAT 494 — the break's own `break` line, logged after a start ended it,
   claimed to be a second break: two records on the day.  The line is the
   break's own (`Replay.Machine.ended`): `decide` computes one. -/
theorem aBreaksOwnLineIsASecondBreak :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (.brkStart 20 none),
      Replay.bE 2 63924366600 (Replay.bStart ['a']), Replay.bE 3 63924370200 (Replay.bDone ['a'] 60 false),
      Replay.bE 4 63924364800 (.brk 20 (some 90) none)]).days.get 739865).map (·.breaks.length) = some 2 := by
  decide

/- CHEAT 495 — a `start` stamped at the break's own instant claimed to end
   nothing (the break left running, the block netted): the reading W-50 track K
   took is that it ends the break there (README gap 5431).  `decide` computes
   sixty. -/
theorem aStartAtTheBreaksInstantEndsNothing :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924366600 (.brkStart 20 none),
      Replay.bE 2 63924366600 (Replay.bStart ['a']),
      Replay.bE 3 63924370200 (Replay.bDone ['a'] 60 false)]).items.get ['a']).map (·.minutes) = some 0 := by
  decide

/- ===== APPENDED W-50 REPAIR TRACK R (README "Stage 6 — W-50 repair, track R", gaps 5500-5502): cheats
   511-514.  D129's stamp-order edges: each cheat states the reading the repair replaced, and `decide` computes the
   one it took. ===== -/

/- CHEAT 511 — `start a` 08:30, then a `break_start` stamped 08:30 logged after
   it; the tie claimed to end the break at once (no break running), as
   `firstStep`'s `≤` read it until the W-50 repair.  A tie ends a break only at a
   start later in the file (README gap 5500): `decide` computes `true`. -/
theorem aTieLoggedBeforeTheBreakEndsIt :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924366600 (Replay.bStart ['a']),
      Replay.bE 2 63924366600 (.brkStart 15 none)]).openBreak.isSome = false := by
  decide

/- CHEAT 512 — a block begun 08:30 and paused until 10:00, done 10:30, then a
   late `break_start` 09:00 and its ten-minute `break` line; the block's first
   drawn piece (10:00) claimed to be a start that ends the break, recording it
   sixty minutes long.  Only a logged `start` stamped after the break ends it
   (README gap 5501): `decide` computes ten. -/
theorem aDrawnPieceEndsTheBreak :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924366600 (Replay.bStart ['a']),
      Replay.bE 2 63924366600 (.pause ['a']), Replay.bE 3 63924372000 (.unpause ['a']),
      Replay.bE 4 63924373800 (Replay.bDone ['a'] 30 false), Replay.bE 5 63924368400 (.brkStart 10 none),
      Replay.bE 6 63924368400 (.brk 10 (some 10) none)]).days.get 739865).map
      (fun a => a.breaks.map (·.actualMin)) = some [some 60] := by
  decide

/- CHEAT 513 — two closed blocks, `a` 08:30 and `b` 10:00, logged `a` first,
   then a late `break_start` 08:00; claimed to end at the LATEST start (10:00,
   two hours).  The earliest start ends it (README gap 5502): `decide` computes
   thirty. -/
theorem theLatestStartEndsALateBreak :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924366600 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 30 false), Replay.bE 3 63924372000 (Replay.bStart ['b']),
      Replay.bE 4 63924373800 (Replay.bDone ['b'] 30 false),
      Replay.bE 5 63924364800 (.brkStart 20 none)]).days.get 739865).map
      (fun a => a.breaks.map (·.actualMin)) = some [some 120] := by
  decide

/- CHEAT 514 — the same two blocks logged `b` first: claimed to end at the
   first held block in file order (`b`, 10:00).  The earliest in STAMP order
   ends it (README gap 5502): `decide` computes thirty. -/
theorem theFirstLoggedStartEndsALateBreak :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924372000 (Replay.bStart ['b']),
      Replay.bE 2 63924373800 (Replay.bDone ['b'] 30 false), Replay.bE 3 63924366600 (Replay.bStart ['a']),
      Replay.bE 4 63924368400 (Replay.bDone ['a'] 30 false),
      Replay.bE 5 63924364800 (.brkStart 20 none)]).days.get 739865).map
      (fun a => a.breaks.map (·.actualMin)) = some [some 120] := by
  decide

-- ===========================================================================
-- APPENDED 2026-10-28 (stage 6, W-50 repair, track B — the owner's D133, README gaps 5520-5539, parity P130).
-- The running break leaves the planner wire: the planner reads it off the request's own replay
-- (`Planner.PlanReq.runningBreak`).  Cheats 551-552.  CHEAT 245 above names Planner.mkBreak?, which this track
-- deleted with the wire's `state.break` (README gap 5524), so it now fails as an unknown identifier — a wrong reason,
-- recorded rather than edited (§6.2); CHEAT 551 is its successor over the replay's reading.
-- ===========================================================================

/- CHEAT 551 — CHEAT 245's claim over the replay (D133): a request whose replay holds a
   `break_start` a second after `now` (a clock behind the log) is claimed to plan a running break.
   `PlanReq.runningBreak` reads such a break as none, as `interruptRows` reads an interruption
   begun after `now` (D78); `decide` computes it. -/
theorem aBreakTheReplayBeganAfterNowRuns :
    ({ PlannerWit.theBusyRequest with
        run := PlannerWit.withBreak PlannerWit.theBusyRequest.run (PlannerWit.theBusyRequest.now.sec + 1) 10 none } :
      Planner.PlanReq).runningBreak.isSome = true := by
  decide

/- CHEAT 552 — the host's runtime claimed to carry a running break again: a `RuntimeIn` built with
   a break beside the running block.  Since D133 the record has no such field (its constructor
   takes three), so the planner cannot be handed a second spelling of the replay's fact. -/
theorem theRuntimeCarriesABreak :
    (Planner.RuntimeIn.mk none (some ⟨none, 10, none⟩) none none).active = none := rfl

-- ===========================================================================
-- APPENDED 2026-10-30 (stage 6, W-51, track K — the owner's D137, README gaps 5580-5599, parity P134).
-- A running break's `break` line gives back what its running took outside its own span (`Replay.giveBack`), so a
-- late break inside a closed block nets the block by its own span, as D100 nets any late break.  Cheats 591-592.
-- ===========================================================================

/- CHEAT 591 — the reading before D137: a late break's line leaves the block netted from the break's start.
   `start a` 08:00, `done a` 09:00 with sixty, a `break_start` at 08:30 logged after the `done`, then its ten-minute
   `break` line: claimed thirty, what the running break netted.  Since D137 the line gives back what lies after its
   span; `decide` computes fifty (`Replay.a_late_breaks_line_gives_back_what_lies_after_it`). -/
theorem aLateBreaksLineGivesNothingBack :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (.brkStart 20 none),
      Replay.bE 4 63924366600 (.brk 20 (some 10) none)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

/- CHEAT 592 — the give-back claimed to give everything back: the same log, claimed sixty, as if the break's line
   netted nothing once it had given back.  The line nets its own span `[08:30, 08:40)` (D100); `decide` computes
   fifty. -/
theorem aLateBreaksLineNetsNothing :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (.brkStart 20 none),
      Replay.bE 4 63924366600 (.brk 20 (some 10) none)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/- ======================================================================
   W-51 repair track K (w51r-k): cheats 631-650 are this track's (631-632 taken).
   ====================================================================== -/

/- CHEAT 631 — the W-51 land's give-back: the auditor's K log, a late `start b` at 08:10 cutting `a` while the break
   started at 08:30 runs, then the break's line.  Claimed thirty for `a`, the land's reading (every minute the running break
   took handed back across `b`'s cut).  Since the repair the cut stays cut; `decide` computes ten
   (`Replay.the_k_log_reads_as_its_break_had_no_start`). -/
theorem theKLogGivesBackAcrossTheCut :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (.brkStart 20 none),
      Replay.bE 4 63924365400 (Replay.bStart ['b']), Replay.bE 5 63924365700 (Replay.bDone ['b'] 5 false),
      Replay.bE 6 63924366600 (.brk 20 (some 10) none)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

/- CHEAT 632 — the land's drawing of the auditor's C log: `a` drawn `[08:00, 08:30]` across the late interruption
   `[08:10, 08:20)` once the break's line arrived.  Since the repair the interruption stays cut out of `a`; `decide`
   computes the five segments `Replay.the_c_log_reads_as_its_break_had_no_start` names. -/
theorem theCLogDrawsAcrossTheInterruption :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (.brkStart 20 none),
      Replay.bE 4 63924365400 (.interrupt none), Replay.bE 5 63924366000 (.resume 10 []),
      Replay.bE 6 63924366600 (.brk 20 (some 10) none)]).days.get 739865).map
        (fun a => a.segments.any (fun g => g.start.1.sec = 63924364800 ∧ g.stop.1.sec = 63924366600)) = some true := by
  decide


/- ======================================================================
   W-52 track K (w52-k): cheats 651-670 are this track's.
   ====================================================================== -/

/- CHEAT 651 — the W-51 repair's reading of the J log (README gap 5634): two late `break_start`s, 08:30 and 08:40, both
   ended by D129 at `b`'s 09:10 start, each drawn and recorded — forty and thirty minutes of break over forty of wall
   time.  Claimed the two records' minutes.  Since the owner's D142 the second lies wholly inside the first and adds no
   minute; `decide` computes forty and zero (`Replay.the_j_log_draws_and_records_its_breaks_once`). -/
theorem theJLogRecordsBothBreaks :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924367200 (.brkStart 20 none)]).days.get 739865).map
        (fun a => a.breaks.map (·.actualMin)) = some [some 40, some 30] := by
  decide

/- CHEAT 652 — a break an earlier one covers in part, recorded whole (D142): `break` 08:00 for twenty, then one stamped
   08:10 for twenty.  Claimed the second's twenty minutes; `decide` computes ten, the part no earlier break covers
   (`Replay.a_break_an_earlier_covers_in_part_is_drawn_from_its_end`). -/
theorem aCoveredBreakIsRecordedWhole :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (.brk 20 (some 20) none),
      Replay.bE 2 63924365400 (.brk 20 (some 20) none)]).days.get 739865).map
        (fun a => a.breaks.map (·.actualMin)) = some [some 20, some 20] := by
  decide

/- ======================================================================
   W-52b track K2 (w52-k2): cheats 691-710 are this track's (691-693 taken).
   ====================================================================== -/

/- CHEAT 691 — P127's reading of a `break` line that ends a break D129 already ended (README gaps 5633 and 5660): the J
   log with the line track H's `lime break` writes — `t` 08:30, ten minutes — after the 08:30 `break_start` D129 ended at
   `b`'s 09:10 start.  Claimed `a` stays at thirty, the line the break's own and nothing else.  Since the owner's D141
   the line ends the break at 08:40 and gives back what the ending took after it; `decide` computes fifty
   (`Replay.a_break_line_before_its_d129_end_ends_the_break_there`). -/
theorem aBreakLineBeforeItsD129EndIsTheBreaksOwn :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924366600 (.brk 10 (some 10) none)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

/- CHEAT 692 — D141's undoing taking a segment another held break witnesses (`DayOp.unsegBrks`): two late `break_start`s
   at one stamp, both ended by D129, then the line ending the newest.  Claimed no Break segment survives — the undoing
   removing every segment the dropped head witnesses.  The first break witnesses `[08:30, 09:10)` too, so it is kept;
   `decide` computes one (`Replay.a_break_line_ending_a_covered_break_leaves_two_records`). -/
theorem theUndoingTakesASegmentAnotherBreakWitnesses :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924366600 (.brkStart 10 none), Replay.bE 7 63924366600 (.brk 10 (some 10) none)]).days.get 739865).map
        (fun a => (a.segments.filter (fun g => g.kind == .brk none)).length) = some 0 := by
  decide

/- CHEAT 693 — W-52 track K's reading of a D129 ending an earlier break covers in part (README gap 5662): a `break` line
   08:00 for thirty, then a `break_start` 08:10 a `start` at 08:40 ends.  Claimed the ending's record whole, thirty
   minutes, the overlap with the first counted twice.  Since W-52b track K2 its minutes are the drawn ones; `decide`
   computes ten (`Replay.a_d129_ending_covered_in_part_is_recorded_by_its_drawn_minutes`). -/
theorem aD129EndingCoveredInPartIsRecordedWhole :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (.brk 30 (some 30) none),
      Replay.bE 2 63924365400 (.brkStart 20 none), Replay.bE 3 63924367200 (Replay.bStart ['a'])]).days.get 739865).map
        (fun a => a.breaks.map (·.actualMin)) = some [some 30, some 30] := by
  decide

/- ============================================================================================
   W-52 repair track R (kernel half): D141 for every break D129 ended.  Cheats 711-720 are this
   block's (711-715 taken).  Each claims a reading this repair replaced; each fails because
   `decide` computes the new one.
   ============================================================================================ -/

/- CHEAT 711 — D141 reaching only the NEWEST ending (README gap 5711): scenario C, late `break_start`s 08:30 and 09:30
   ended at 09:10 and 10:20, then the 08:30 line and the 09:30 line, ten minutes each.  Claimed the day ninety — the older
   line read as a covered break of its own.  Every ending is reached since this repair; `decide` computes a hundred and
   forty (`Replay.scenario_c_older_line_first_ends_both_breaks`). -/
theorem d141ReachesOnlyTheNewestEnding :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924373200 (Replay.bStart ['c']),
      Replay.bE 6 63924375600 (Replay.bDone ['c'] 40 false), Replay.bE 7 63924366600 (.brkStart 10 none),
      Replay.bE 8 63924370200 (.brkStart 10 none), Replay.bE 9 63924366600 (.brk 10 (some 10) none),
      Replay.bE 10 63924370200 (.brk 10 (some 10) none)]).days.get 739865).map (·.blockMin) = some 90 := by
  decide

/- CHEAT 712 — an ordinary `break_start` forgetting a D129 ending's take (`forgetIdle`, README gap 5711; the W-52 auditor's
   J2): one ending, an ordinary break 10:20-10:30, then the ending's line.  Claimed the day ninety, the line skipped.
   Since this repair an ending's take is kept under its key (`Closed.held`); `decide` computes a hundred and ten
   (`Replay.j2_an_ordinary_break_after_the_ending_leaves_it_endable`). -/
theorem anOrdinaryBreakForgetsTheEndingsTake :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924373200 (.brkStart 10 none), Replay.bE 7 63924373200 (.brk 10 (some 10) none),
      Replay.bE 8 63924366600 (.brk 10 (some 10) none)]).days.get 739865).map (·.blockMin) = some 90 := by
  decide

/- CHEAT 713 — `endMachine` forgetting the running break's take (README gap 5712): `a` done, a late `break_start` 08:30
   netting it while it runs, `b`'s 09:10 `start` ending the break, then the break's line for ten.  Claimed `a` thirty.
   The take is stashed under the start's key since this repair; `decide` computes fifty
   (`Replay.a_running_break_a_start_ended_gives_back_on_its_line`). -/
theorem endMachineForgetsTheRunningTake :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924366600 (.brkStart 10 none),
      Replay.bE 4 63924369000 (Replay.bStart ['b']), Replay.bE 5 63924366600 (.brk 10 (some 10) none),
      Replay.bE 6 63924372600 (Replay.bDone ['b'] 60 false)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

/- CHEAT 714 — the fact naming a break while one runs (README gap 5714): a running `break_start` with an ending held.
   Claimed the fact non-empty.  A line read while a break runs is that break's end, never D141's (`d141Ok`), and the fact
   says what the arm reads (`Replay.d141_reads_iff_endable`); `decide` computes `[]`. -/
theorem theFactNamesABreakWhileOneRuns :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924373200 (.brkStart 10 none)]).openEnded ≠ [] := by
  decide

/- CHEAT 715 — an ending a later-held break overlaps read as endable (README gap 5741): late `break_start`s 08:30 and
   08:40, both ended at 09:10.  Claimed the fact holds the 08:30 break.  The 08:40 break overlaps it (`newerMeets`), so
   the fact holds the 08:40 one alone; `decide` computes one entry
   (`Replay.an_ending_a_later_break_overlaps_is_not_reached`). -/
theorem anOverlappedEndingIsEndable :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924367200 (.brkStart 10 none)]).openEnded.map (fun x => x.s.1.sec)) = [63924367200, 63924366600] := by
  decide

/- ============================================================================================
   APPENDED — stage 6 W-53 track K (`w53-k`): D142 in any logging order (README gap 5661) — a
   break logged after one stamped later than it reaches back and covers that one's head
   (`Replay.reachFx`, `DayOp.redraw`), and a break an ending covered is drawn again when the
   ending's own line lets it go (`Replay.growFx`).  Cheats 751-770 are this track's (751-753 taken).
   ============================================================================================ -/

/- CHEAT 751 — W-52's union read in log order (README gap 5661): `C` 08:20 for twenty, `B` 08:10 for forty, `A` 08:00 for
   thirty, logged in that order.  Claimed the day draws all three whole, as each was drawn against the breaks held when it
   was stepped.  `A` and `B`, logged after `C` and stamped before it, reach back to it; `decide` computes
   `[08:00, 08:30)` and `[08:30, 08:50)` (`Replay.three_overlapping_breaks_logged_c_b_a_are_one_day`). -/
theorem threeBreaksLoggedBackwardsDrawnWhole :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924366000 (.brk 20 (some 20) none),
      Replay.bE 2 63924365400 (.brk 40 (some 40) none), Replay.bE 3 63924364800 (.brk 30 (some 30) none)]).days.get 739865).map
      (fun a => (a.segments.filter (fun g => g.kind == .brk none)).map (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924364800, 63924366600), (63924365400, 63924367800), (63924366000, 63924367200)] := by
  decide

/- CHEAT 752 — a break a later-logged D129 ending covers drawn whole (README gap 5661): `a` 08:00–09:00, `b` 09:10–10:10,
   a late `break` line 08:40 for ten, then a late `break_start` 08:30 ended at 09:10.  Claimed the 08:40 break still drawn
   beside the ending.  The ending covers it whole; `decide` computes the one segment `[08:30, 09:10)`
   (`Replay.a_break_a_later_logged_ending_covers_is_drawn_from_its_end`). -/
theorem aBreakALaterEndingCoversIsDrawnWhole :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924372600 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924367200 (.brk 10 (some 10) none),
      Replay.bE 6 63924366600 (.brkStart 10 none)]).days.get 739865).map
      (fun a => (a.segments.filter (fun g => g.kind == .brk none)).map (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924366600, 63924369000), (63924367200, 63924367800)] := by
  decide

/- CHEAT 753 — the covered break left undrawn when the ending is let go (a reach-back with no `growFx`): the log above with
   `b` running, then the ending's own line stamped 08:30 for five.  Claimed only the line's `[08:30, 08:35)` drawn.  The
   08:40 break is no longer covered and is drawn again; `decide` computes both (`Replay.a_break_an_ending_covered_is_drawn_again_when_its_line_lets_it_go`). -/
theorem aCoveredBreakStaysUndrawn :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924364800 (Replay.bStart ['a']),
      Replay.bE 2 63924368400 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924369000 (Replay.bStart ['b']),
      Replay.bE 4 63924367200 (.brk 10 (some 10) none), Replay.bE 5 63924366600 (.brkStart 10 none),
      Replay.bE 6 63924366600 (.brk 10 (some 5) none)]).days.get 739865).map
      (fun a => (a.segments.filter (fun g => g.kind == .brk none)).map (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924366600, 63924366900)] := by
  decide

/- ======================================================================
   W-53 repair track K (`w53r-k`): cheats 771-790.  Each states the reading this step replaced and is
   refused by `decide` proving it false.
   ====================================================================== -/

/- CHEAT 771 — a re-drawing that finds its record by stamp and minutes (README gap 5791, the auditor's col3 log): breaks
   07:40 for twenty, a `break_start` 08:00 the 08:30 `start` ends, then 07:50 for forty and 07:30 for fifty logged late.
   Claimed the day `01ad5b1` drew — `07:30 break 50m` and `08:00 break 30m`, the stretch 08:00–08:20 twice.  A held break
   now carries its key and its record that key; `decide` computes `[07:30, 08:20)` and `[08:20, 08:30)`
   (`Replay.col3_is_one_day_in_either_logging_order`). -/
theorem col3DrawsAnOverlapTwice :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924363600 (.brk 20 (some 20) none), Replay.bE 2 63924364800 (.brkStart 30 none), Replay.bE 3 63924366600 (Replay.bStart ['t']), Replay.bE 4 63924368400 (Replay.bDone ['t'] 30 false), Replay.bE 5 63924364200 (.brk 40 (some 40) none), Replay.bE 6 63924363000 (.brk 50 (some 50) none)])).days.get 739865).map
      (fun a => (a.segments.filter (fun g => g.kind == .brk none)).map (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924363000, 63924366000), (63924364800, 63924366600)] := by
  decide


/- CHEAT 772 — a later shorter `break` line at a finished break's stamp read as a break of its own (the owner's D147,
   parity P143): `a` 09:00–10:00 and `b` 10:10–11:10 done, a `break` 09:30 for ten, then a later `break` 09:30 with
   four.  Claimed the reading until this step — D142's union, the later line covered whole, `a` fifty.  The later line
   now re-times the break; `decide` computes fifty-six (`Replay.a_later_shorter_line_at_a_finished_breaks_stamp_re_times_it`). -/
theorem aLaterShorterLineIsABreakOfItsOwn :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
      Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']),
      Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924370200 (.brk 10 (some 10) none),
      Replay.bE 6 63924370200 (.brk 10 (some 4) none)]).items.get ['a']).map (·.minutes) = some 50 := by
  decide


set_option maxRecDepth 400000 in
/- CHEAT 773 — the running break drawn from its own start over a logged break (the W-53 critic's F3, D142): the busy
   Wednesday's walk started at 14:00 with a break 13:50–14:10 already logged.  Claimed the row `breakRows` drew until this
   step, 14:00–14:30, ten minutes twice.  It is drawn from where the logged break stops; `decide` computes 14:10
   (`PlannerWit.a_running_break_is_drawn_from_where_the_logged_breaks_stop`). -/
theorem theCoveredWalkIsDrawnFromItsOwnStart :
    (Planner.breakRows PlannerWit.theCoveredBreakRequest).map (fun s => (s.start, s.stop)) =
      [((Cal.instantOf Cal.chicago 739867 840).sec, (Cal.instantOf Cal.chicago 739867 870).sec)] := by
  decide


/-! ## W-54 track K (README gaps 5870-5889): cheats 791-797 -/

set_option maxRecDepth 8000 in
/- CHEAT 791 — a re-time that gives back nothing to a block the break netted OPEN (the W-54 auditor's finding 1, README gap 5870):
   `a` started 09:00, a break 09:20 ended by its own line for forty, `a` done 10:00 for twenty, then the line re-timing
   the break to 09:30.  Claimed what W-53 repair track K's kernel read: twenty — the take an open block's netting never
   stashed.  The block remembers what each held break took from it when it closes (`Replay.openTakes`); `decide` computes
   fifty (`Replay.a_retime_gives_back_what_the_break_took_from_an_open_block`). -/
theorem aRetimeGivesAnOpenBlockNothing :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924369600 (.brkStart 10 none), Replay.bE 3 63924369600 (.brk 10 (some 40) none), Replay.bE 4 63924372000 (Replay.bDone ['a'] 20 false), Replay.bE 5 63924372600 (Replay.bStart ['b']), Replay.bE 6 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 7 63924369600 (.brk 10 (some 10) none)]).items.get ['a']).map (·.minutes) = some 20 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 792 — a re-time that draws its block across a later break (the W-54 critic's finding 1, README gap 5871):
   `a` 09:00–10:00, breaks 09:20 and 09:40 for five, then 09:20 re-timed to 09:22.  Claimed the drawing W-53 repair track
   K's kernel made — `a` 09:22–10:00, thirty-eight minutes through the 09:40 break, the 09:20 take never cut by the later
   netting.  A netting now cuts every take it meets (`Replay.netTake`); `decide` computes 09:22–09:40 and 09:45–10:00
   (`Replay.a_retime_keeps_a_later_breaks_take`). -/
theorem aRetimeDrawsThroughALaterBreak :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924369600 (.brk 5 (some 5) none), Replay.bE 6 63924370800 (.brk 5 (some 5) none), Replay.bE 7 63924369600 (.brk 5 (some 2) none)]).days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .block ['a'])).map (fun g => (g.start.1.sec, g.stop.1.sec))) = some [(63924368400, 63924369600), (63924369720, 63924372000)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 793 — a re-time of a P127 break that gives back nothing (the W-54 auditor's finding 3, README gap 5872):
   the J day, a `break_start` 09:30 D129 ends at 10:10, its own line 09:30 for fifty (P127: D129's end kept), then the line
   re-timing it to 09:50.  Claimed W-53 repair track K's thirty — `letGo` had dropped the ending's take.  The take is kept;
   `decide` computes forty (`Replay.a_retime_of_a_p127_break_gives_back_its_take`). -/
theorem aP127RetimeGivesNothing :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924370200 (.brkStart 20 none), Replay.bE 6 63924370200 (.brk 20 (some 50) none), Replay.bE 7 63924370200 (.brk 20 (some 20) none)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 794 — the finished-break fact naming a break no line re-times (the W-54 auditor's finding 2 and critic's 2, README gap 5874):
   the J day, breaks 09:20 and 09:30 for twenty.  Claimed W-53 repair track K's fact — both breaks — though a line at
   09:20 meets the newer break's span and is read as a break of its own (`newerMeets`).  The fact holds only what a line
   re-times; `decide` computes the 09:30 break alone (`Replay.the_fact_omits_a_break_a_newer_one_overlaps`). -/
theorem theFactNamesAnOverlappedBreak :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924369600 (.brk 20 (some 20) none), Replay.bE 6 63924370200 (.brk 20 (some 20) none)]).openFinished.map (fun x => (x.s.1.sec, x.e.1.sec)) = [(63924370200, 63924371400), (63924369600, 63924370800)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 795 — identical twin finished breaks re-timed one at a time (the W-54 auditor's finding 4, README gap 5875):
   the J day, `break --now 09:20 10m` logged twice, then the line re-timing 09:20 to 09:25.  Claimed W-53 repair track K's
   fifty — the older twin kept its ten minutes.  A later line at a finished break's stamp with its planned minutes is that
   break's reading (the campaign's call); `decide` computes fifty-five (`Replay.twin_finished_breaks_are_re_timed_as_one`). -/
theorem aTwinKeepsItsMinutes :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369600 (.brk 10 (some 10) none), Replay.bE 7 63924369600 (.brk 10 (some 5) none)]).items.get ['a']).map (·.minutes) = some 50 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 796 — a finished break that forgets the widest span the log held for it (the owner's D150, README gap 5876):
   the J day, 09:20 for thirty re-timed to 09:40, 09:30, out to 09:45 and back to 09:35.  Claimed the break's widest end
   is its own, 09:35.  The fact carries the latest end any of its lines gave it; `decide` computes 09:50
   (`Replay.a_finished_break_keeps_its_widest_end`). -/
theorem theWidestEndIsTheOwnEnd :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924369600 (.brk 30 (some 30) none), Replay.bE 6 63924369600 (.brk 30 (some 20) none), Replay.bE 7 63924369600 (.brk 30 (some 10) none), Replay.bE 8 63924369600 (.brk 30 (some 25) none), Replay.bE 9 63924369600 (.brk 30 (some 15) none)]).openFinished.map (fun x => (x.e.1.sec, x.wide.1.sec)) = [(63924370500, 63924370500)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 797 — the col3 log re-timed and drawn twice (the W-54 auditor's finding 5, README gap 5871):
   the auditor's col3 log as the sync wrote it — 07:30 for fifty, then 07:50 for forty — then the line re-timing 07:50 to
   07:55.  Claimed W-53 repair track K's drawing: `08:20–08:30` twice, the re-timed break's own segment kept because the
   D129 ending could have drawn it.  The re-time un-draws exactly the segment the break drew (`DayOp.unsegBrks`'s start);
   `decide` computes one (`Replay.col3_with_a_retime_is_one_day_in_every_logging_order`). -/
theorem col3RetimeDrawsTwice :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924363600 (.brk 20 (some 20) none), Replay.bE 2 63924364800 (.brkStart 30 none), Replay.bE 3 63924366600 (Replay.bStart ['t']), Replay.bE 4 63924368400 (Replay.bDone ['t'] 30 false), Replay.bE 5 63924363000 (.brk 50 (some 50) none), Replay.bE 6 63924364200 (.brk 40 (some 40) none), Replay.bE 7 63924364200 (.brk 40 (some 5) none)]).days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .brk none)).map (fun g => (g.start.1.sec, g.stop.1.sec))) = some [(63924363000, 63924366000), (63924366000, 63924366600), (63924366000, 63924366600)] := by
  decide


/-! ======================================================================
    APPENDED — stage 6 W-54 repair track K (`w54r-k`): the owner's D145 (a finished break's line ends only its own
    break), D151 (the widest end is the break's own lines'), and the finished-break fact's overlap filter (README gaps
    5920-5939).  Cheats 811-815.
    ====================================================================== -/

set_option maxRecDepth 8000 in
/- CHEAT 811 — a finished break's line ends the running break (the owner's D145, parity P142, README gap 5820): the J day,
   a break running since 11:30, then `lime break --now 09:20 5m`'s one plain line.  Claimed the W-54 reading: no break runs.
   The line is a finished break's and ends only its own; `decide` computes the running break
   (`Replay.a_finished_line_ends_only_its_own_break`). -/
theorem aFinishedLineEndsTheRunningBreak :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924378600 (.brkStart 20 none), Replay.bE 6 63924369600 (.brk 5 (some 5) none)])).openBreak = none := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 812 — a parked line read at the running break's place (the owner's D145, D116): a break running at `walk`, then a
   finished line with no place.  Claimed its record reads `walk`, as the running break's own line would.  A parked line is
   read at its own place; `decide` computes none (`Replay.a_parked_line_is_read_at_its_own_place`). -/
theorem aParkedLineReadsTheRunningPlace :
    ((Replay.replay Replay.utcZone [Replay.bE 1 63924378600 (.brkStart 20 (some ['w','a','l','k'])), Replay.bE 2 63924369600 (.brk 5 (some 5) none)]).days.get 739865).map (fun a => a.breaks.map (·.where_)) = some [some ['w','a','l','k']] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 813 — the running break's own line missed by its seconds (the owner's D145): a `break_start` at 09:30:27 and the line
   ending it stamped 09:30, as a binary of the D105 era wrote it.  Claimed the break still runs (the line parked).  The
   running break's own line is the one in its start's minute; `decide` computes no break running
   (`Replay.a_break_line_in_the_running_breaks_minute_ends_it`). -/
theorem theOwnLineIsMissedBySeconds :
    (Replay.replay Replay.utcZone [Replay.bE 1 (63924370200 + 27) (.brkStart 20 none), Replay.bE 2 63924370200 (.brk 20 (some 15) none)]).openBreak ≠ none := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 814 — D129's end inside the widest span (the owner's D151, README gap 5926): the critic's d6 — `a` 09:00–10:00, `b`
   13:00–14:00, a `break_start` 09:30 the 13:00 start ends, its own line ending it at 09:40.  Claimed W-54's widest end,
   13:00.  The widest end is the latest end the break's own lines gave it; `decide` computes 09:40
   (`Replay.the_widest_end_is_the_breaks_own_lines`). -/
theorem d129EndIsInTheWidestSpan :
    (Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924382800 (Replay.bStart ['b']), Replay.bE 4 63924386400 (Replay.bDone ['b'] 60 false), Replay.bE 5 63924370200 (.brkStart 20 none), Replay.bE 6 63924370200 (.brk 20 (some 10) none)]).openFinished.map (fun x => x.wide.1.sec) = [63924382800] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 815 — a nested finished break listed (the W-54 auditor's 1 and critic's 2, README gap 5925): the J day, `09:20 30m`
   then `09:30 5m` inside it.  Claimed W-54's fact: the newer five-minute break listed for a re-time.  The fact omits a break
   any other held break overlaps; `decide` computes none (`Replay.a_finished_break_another_overlaps_is_omitted`). -/
theorem aNestedFinishedBreakIsListed :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 30 (some 30) none), Replay.bE 6 63924370200 (.brk 5 (some 5) none)])).openFinished.length = 1 := by
  decide


/-! ===== W-54 second repair track K (README gaps 5970-5989): cheats 831-834 — the fact's own-piece filter and the re-time
   guard for a finished break.  Each claims a reading this track replaced, and `decide` computes the other. ===== -/

set_option maxRecDepth 8000 in
/- CHEAT 831 — the head-clipped break omitted (README gaps 5962 and 5970, the critic's E1): the J day, `09:20 10m` then
   `09:25 10m`.  Claimed W-54 repair track K's fact: empty, every break another overlaps omitted.  The 09:25 break draws
   09:30–09:35, its own (`Replay.ownDrawn`), so the fact lists it (`Replay.a_finished_break_whose_drawn_piece_another_meets_is_omitted`). -/
theorem aHeadClippedBreakIsOmitted :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369900 (.brk 10 (some 10) none)])).openFinished.length = 0 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 832 — the critic's B not read (README gaps 5970, 5971 and 6021; restated at W-54 third repair track K, when what it
   claimed became the reading): `09:20 10m`, `09:25 10m`, then the 09:20 break re-timed to 09:22.  Claimed `a` forty-five, the
   line a break of its own, as W-54 second repair track K read it.  The re-time is read and freezes the 09:25 break: `decide`
   computes forty-eight (`Replay.a_retime_of_a_covering_break_off_a_later_ones_head_is_read`). -/
theorem theCoveringBreakIsReTimedOffALaterOnesHead :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369900 (.brk 10 (some 10) none), Replay.bE 7 63924369600 (.brk 10 (some 2) none)])).items.get ['a']).map (·.minutes) = some 45 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 833 — the critic's C2 refused by the newer break (README gap 5970; W-52 repair track R's guard for every break):
   nested `09:20 30m` + `09:30 5m`, the outer re-timed to 09:40.  Claimed `a` thirty, the line a break of its own because a
   newer break overlaps the outer one (`newerMeets`).  The re-time gives up 09:40–09:50, its own, and is read: `a` forty
   (`Replay.a_retime_giving_up_nothing_another_break_covers_is_read_over_a_newer_one`). -/
theorem anOuterBreakANewerOneOverlapsIsNotReTimed :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 30 (some 30) none), Replay.bE 6 63924370200 (.brk 5 (some 5) none), Replay.bE 7 63924369600 (.brk 30 (some 20) none)])).items.get ['a']).map (·.minutes) = some 30 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 834 — a line ending inside another break's stretch not read (README gaps 5970, 5971 and 6021; restated at W-54 third
   repair track K, when what it claimed became the reading): `09:20 10m`, `09:25 10m`, then the 09:25 break re-timed to 09:28,
   inside the 09:20 break.  Claimed `a` forty-five, as W-54 second repair track K read it.  `decide` computes fifty, the union
   09:20–09:30 (`Replay.a_line_ending_inside_another_breaks_stretch_re_times_it`). -/
theorem aLineInsideAnotherBreaksStretchReTimes :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369900 (.brk 10 (some 10) none), Replay.bE 7 63924369900 (.brk 10 (some 3) none)])).items.get ['a']).map (·.minutes) = some 45 := by
  decide


/-! ===== W-54 third repair track K (README gaps 6020-6039): cheats 835-845 — a take put back whole, a shared stretch let go and the
   break it leaves short frozen, the fact per held break, the log's typed-time lines.  Each claims a reading this track replaced, and
   `decide` computes the other. ===== -/

set_option maxRecDepth 8000 in
/- CHEAT 835 — a piece wider than a take dropped (README gap 6020): `09:20 10m`, `09:40 15m`, the first re-timed to 09:25, the second to 09:50.  Claimed W-54 second repair track K's pieces: 09:25–09:30 drawn nowhere, the review 105 and the plan 100.  `decide` computes 09:25–09:40 (`Replay.a_piece_wider_than_a_take_is_put_back_whole`). -/
theorem aPieceWiderThanATakeIsDropped :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924370800 (.brk 15 (some 15) none), Replay.bE 7 63924369600 (.brk 10 (some 5) none), Replay.bE 8 63924370800 (.brk 15 (some 10) none)])).days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .block ['a'])).map (fun g => (g.start.1.sec, g.stop.1.sec))) = some [(63924368400, 63924369600), (63924370200, 63924370800), (63924371400, 63924372000)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 836 — defect A's credit (README gap 6020): five lines, the first break re-timed out over the second, the second re-timed to 09:52.  Claimed thirty-eight, what the second break's take kept of the shared stretch.  `decide` computes twenty-eight (`Replay.a_retime_out_over_a_later_break_keeps_the_takes_with_the_union`). -/
theorem aRetimeOutLeavesALaterTakeWhole :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 30 (some 30) none), Replay.bE 6 63924369600 (.brk 30 (some 10) none), Replay.bE 7 63924370800 (.brk 15 (some 15) none), Replay.bE 8 63924369600 (.brk 30 (some 30) none), Replay.bE 9 63924370800 (.brk 15 (some 12) none)])).items.get ['a']).map (·.minutes) = some 38 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 837 — the break a let-go leaves short keeps its range (README gaps 5971 and 6021): after the critic's B, the 09:25 break, its take short of 09:25–09:30.  Claimed its range from its start.  `frozen` bites; `decide` computes none (`Replay.a_retime_letting_go_of_a_shared_stretch_freezes_the_other`). -/
theorem aShortBreakKeepsItsRange :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369900 (.brk 10 (some 10) none), Replay.bE 7 63924369600 (.brk 10 (some 2) none)])).openHeld.map (fun f => (f.s.1.sec, f.e.1.sec, f.retimeFrom.map (·.1.sec), f.outTo.map (·.1.sec))) = [(63924369600, 63924369720, some 63924369600, some 63924370200), (63924369900, 63924370500, some 63924369900, none)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 838 — a frozen break re-timed (README gaps 5971 and 6021): after the critic's B, a line re-timing the 09:25 break to 09:28.  Claimed `a` fifty-three, the five its short take gives back with the three the line nets, which leaves 09:28–09:30 drawn nowhere.  `decide` computes forty-eight (`Replay.a_frozen_break_is_not_re_timed_on_the_log`). -/
theorem aFrozenBreakIsReTimed :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369900 (.brk 10 (some 10) none), Replay.bE 7 63924369600 (.brk 10 (some 2) none), Replay.bE 8 63924369900 (.brk 10 (some 3) none)])).items.get ['a']).map (·.minutes) = some 53 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 839 — the critic's C not read (README gaps 5971 and 6021): the outer break of a nested pair re-timed to 09:25.  Claimed `a` thirty.  `decide` computes fifty (`Replay.the_outer_break_is_re_timed_past_a_nested_one_and_freezes_it`). -/
theorem theOuterBreakIsNotReTimedPastANestedOne :
    ((Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 30 (some 30) none), Replay.bE 6 63924370200 (.brk 5 (some 5) none), Replay.bE 7 63924369600 (.brk 30 (some 5) none)])).items.get ['a']).map (·.minutes) = some 30 := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 840 — the older break of gap 5973's day keeps its range (README gaps 5973 and 6021): `09:40 5m`, a D129 ending from 09:30 and its own line ending it at 09:35.  Claimed the 09:40 break re-timeable.  The ending took its stretch and let it go: `decide` computes none (`Replay.gap_5973s_day_freezes_the_older_break`). -/
theorem gap5973sOlderBreakKeepsItsRange :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924370800 (.brk 5 (some 5) none), Replay.bE 6 63924370200 (.brkStart 20 none), Replay.bE 7 63924370200 (.brk 20 (some 5) none)])).openHeld.map (fun f => (f.s.1.sec, f.e.1.sec, f.retimeFrom.map (·.1.sec), f.outTo.map (·.1.sec))) = [(63924370200, 63924370500, some 63924370200, none), (63924370800, 63924371100, some 63924370800, none)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 841 — a fact clipped by D142 (README gap 6022): the head-clipped pair.  Claimed the 09:25 break's span from where it is drawn, 09:30.  The fact is unclipped; `decide` computes 09:25 (`Replay.the_fact_holds_every_held_break_unclipped`). -/
theorem theFactIsClipped :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924369900 (.brk 10 (some 10) none)])).openHeld.map (fun f => (f.s.1.sec, f.e.1.sec, f.retimeFrom.map (·.1.sec), f.outTo.map (·.1.sec))) = [(63924370200, 63924370500, some 63924369900, none), (63924369600, 63924370200, some 63924369600, none)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 842 — a range while a break runs (README gap 6022): a `break_start` 11:30 no `start` follows.  Claimed the 09:20 break re-timeable.  A line is parked while a break runs; `decide` computes none (`Replay.the_fact_is_empty_of_ranges_while_a_break_runs`). -/
theorem aRangeWhileABreakRuns :
    (Replay.replay Replay.utcZone ([Replay.bE 1 63924368400 (Replay.bStart ['a']), Replay.bE 2 63924372000 (Replay.bDone ['a'] 60 false), Replay.bE 3 63924372600 (Replay.bStart ['b']), Replay.bE 4 63924376200 (Replay.bDone ['b'] 60 false)] ++ [Replay.bE 5 63924369600 (.brk 10 (some 10) none), Replay.bE 6 63924377400 (.brkStart 20 none)])).openHeld.map (fun f => (f.s.1.sec, f.e.1.sec, f.retimeFrom.map (·.1.sec), f.outTo.map (·.1.sec))) = [(63924369600, 63924370200, some 63924369600, none)] := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 843 — a forward report witnesses an instant (the owner's D154, README gap 6023): an `energy` line stamped 18:00 folded with a `note` at 09:00.  Claimed the stated instant.  It can run ahead of the clock; `decide` computes 09:00 (`Seal.maxTyped_is_the_latest_typed_stamp`). -/
theorem aForwardReportIsATypedStamp :
    (Seal.ckptOfEntries Replay.utcZone 739865 739865 2 [Replay.bE 1 63924368400 (.note ['n']), Replay.bE 2 63924400000 (.energy 3 4 (.nat 2) ['h'])] [] []).maxTyped = some ⟨63924400000, 0⟩ := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 844 — a far-future line hides the stamp behind it (D18, D154, README gap 6023): a `note` at 09:00 and one in 2028, the fence a day later.  Claimed none, as a maximum filtered after it was taken would answer.  `decide` computes 09:00 (`Seal.latestTyped_skips_a_far_future_line_and_counts_an_undone_one`). -/
theorem aFarFutureLineHidesTheNextLatest :
    Seal.latestTyped (Seal.Ckpt.empty Replay.utcZone) [Replay.bE 1 63924368400 (.note ['n']), Replay.bE 2 63987526800 (.note ['f'])] ⟨63924454800, 0⟩ = none := by
  decide

set_option maxRecDepth 8000 in
/- CHEAT 845 — an undo line is no witness (D153 as first built; the owner's D154): a `note` at 09:00 undone at 09:01.  Claimed 09:00, the latest survivor's reading.  The instant was reached either way; `decide` computes 09:01 (`Seal.latestTyped_skips_a_far_future_line_and_counts_an_undone_one`). -/
theorem anUndoLineIsNoWitness :
    Seal.latestTyped (Seal.Ckpt.empty Replay.utcZone) [Replay.bE 1 63924368400 (.note ['n']), Replay.bE 2 63924368460 (.undo ['n', 'o', 't', 'e'] none)] ⟨63924454800, 0⟩ = some ⟨63924368400, 0⟩ := by
  decide

end Lime
