import TmKernel.SealStep
import TmKernel.SealCutMachine
import TmKernel.SealRun
/-!
# BreakFold — the replay's half of the last goal, as fold invariants (stage 6, W-49 track Q)

`Goals.plan_places_no_block_over_a_break` reduces (`PlanCheck.plan_places_no_block_over_a_break_on_an_apart_replay`,
W-48 track G) to three facts about today's record in the replay's answer.  This module proves one of them — `hopen`,
the open block's clock runs from at or after the end of every Break segment of a day — over every run
`Seal.resumeRun` builds from the empty checkpoint, as two invariants of the replay's fold carried through every step:

* `OpenAfter` — the open block's clock runs from at or after the end of every nonempty span it nets (its idle spans and
  the held breaks of its ledger days).  Every machine an arm writes is a settled one, or keeps the block and the held
  breaks of a machine that was (`arm_openAfter`).
* `BrkHeld` — every Break segment of a day's record is a break the machine holds on that ledger day, or one more than 31
  ledger days behind the newest it holds (`pruneBrks`' bound, README gap 4914).  A Break segment is written by a
  `break` line, beside the held break `brkFx` pushes with the same span and day, or — since the owner's D129 (W-50
  track K) — by a `start` that ends the running break or a `break_start` a held start ends, beside the break it holds
  with that span and day (`stepWith_brkHeld`).

The two compose to `hopen` on every day at or after the open block's own ledger day
(`the_resumed_open_block_runs_after_every_break`; at the planner's request, `PlanCheck.hopen_on_a_resumed_run`); the
bounds the theorem names are README gap 4914's pruned break and a day before the open block's (a clock behind the log,
D94).  The other two facts are not here: `hrec` needs the drawn-pieces accounting (README gap 5342) and `hrun` is false
on requests the decoder builds (README gaps 5340 and 5341, W-49 track Q).  Every definition here is a `Prop`, so the
module emits no code.
-/
namespace Tm
namespace BreakFold

open Replay
open Log (Entry)

/-- **The open block's clock runs after every span it nets**: its `since`, while its clock runs, is at or after the end
of every nonempty span `blockSpans` holds — its own idle spans and the held breaks of its ledger days (the owner's D94
and D99). -/
def OpenAfter (m : Machine) : Prop :=
  ∀ b, m.block = some b → ∀ x, b.since = some x → ∀ p ∈ blockSpans b m, p.1.1 < p.2.1 → p.2.1 ≤ x.1

/-- A machine with the same block and the same held breaks nets the same spans. -/
theorem openAfter_congr {m m' : Machine} (hb : m'.block = m.block) (hk : m'.brks = m.brks) (h : OpenAfter m) :
    OpenAfter m' := by
  intro b hb' x hx p hp hlt
  rw [hb] at hb'
  have hs : blockSpans b m' = blockSpans b m := by unfold blockSpans spansFor; rw [hk]
  exact h b hb' x hx p (hs ▸ hp) hlt

/-- A machine with no open block holds the invariant of nothing. -/
theorem openAfter_of_no_block {m : Machine} (h : m.block = none) : OpenAfter m := by
  intro b hb; rw [h] at hb; cases hb

/-- **Every settled machine holds it** (`Replay.runFrom_step_ge`). -/
theorem settle_openAfter (dy : Cal.Instant → Nat) (m : Machine) : OpenAfter (settle dy m).1 := by
  intro b' hb' x hx p hp hlt
  cases hm : m.block with
  | none => simp [settle, hm] at hb'
  | some b =>
    simp only [settle, hm, Option.some.injEq] at hb'
    subst hb'
    simp only at hx
    split at hx
    · cases hx
    · simp only [Option.some.injEq] at hx
      subst hx
      have hk := (settle_keeps dy m).2.2.1
      have hp' : p ∈ blockSpans b m := by
        unfold blockSpans spansFor at hp ⊢; rw [hk] at hp; exact hp
      exact (Replay.runFrom_step_ge _ _).2 p hp' hlt

/-- A cut takes the block. -/
theorem cut_block (dy : Cal.Instant → Nat) (m : Machine) (t : At) : (cut dy m t).1.block = none := by
  unfold cut; split
  · rfl
  · assumption

/-- A `done`'s close takes the block or leaves it, and keeps the held breaks. -/
theorem doneClose_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Log.Id) (actual : Nat) (went : Option Log.U8) :
    ((doneClose dy m t id actual went).1.block = none ∨ (doneClose dy m t id actual went).1.block = m.block) ∧
      (doneClose dy m t id actual went).1.brks = m.brks := by
  unfold doneClose
  repeat' split
  all_goals first | exact ⟨Or.inl rfl, rfl⟩ | exact ⟨Or.inr rfl, rfl⟩

/-- **Every machine an arm writes holds the invariant** when the machine it stepped from does: each is settled
(`settle_openAfter`), or a settled one with only its closed blocks moved (`netClosed`, `runNet`), or has no block (a
cut, a `done`'s close), or keeps the block and the held breaks (an `extend`, a `done` of another item). -/
theorem arm_openAfter (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat)
    (h : OpenAfter m) : ∀ m' ∈ (arm dy sl m e t d).filterMap Effect.machineOf?, OpenAfter m' := by
  intro m' hm
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    have hS : ∀ M, ∀ m' ∈ (Replay.startArm dy M e.line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?,
        OpenAfter m' := by
      intro M m' hm
      rw [Replay.startArm_machines] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      exact settle_openAfter dy _
    split at hm
    · exact hS _ m' (Replay.startEnds_mem dy m _ _ t d _ _ _ _ _ _ m' hm)
    · exact hS m m' hm
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact settle_openAfter dy _
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact settle_openAfter dy _
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    exact settle_openAfter dy _
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton, (Replay.netClosed_obs dy _ _ _ _).2.2] at hm
      subst hm
      exact openAfter_congr (Replay.netClosed_keeps dy _ _ _ _).1 (Replay.netClosed_keeps dy _ _ _ _).2.2.1
        (settle_openAfter dy _)
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact settle_openAfter dy _
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact openAfter_of_no_block ((Replay.runNet_keeps dy _).1.trans (cut_block dy m t))
      · simp at hm
    · simp at hm
  case extend id by_ =>
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, hb, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    intro b' hb' x hx p hp hlt
    simp only [Option.some.injEq] at hb'
    subst hb'
    exact h b hb x hx p hp hlt
  case done id est actual went tags ci isPartial =>
    rw [Seal.doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    obtain ⟨hb, hk⟩ := doneClose_keeps dy m t id actual.val went
    have hb1 := (Replay.runNet_keeps dy { (doneClose dy m t id actual.val went).1 with
      closed := doneClosed dy m e.line t id actual.val ci }).1
    have hk1 := (Replay.runNet_keeps dy { (doneClose dy m t id actual.val went).1 with
      closed := doneClosed dy m e.line t id actual.val ci }).2.2.1
    rcases hb with hb | hb
    · exact openAfter_of_no_block (hb1.trans hb)
    · exact openAfter_congr (hb1.trans hb) (hk1.trans hk) h
  case brk p a w =>
    have hF : ∀ (M : Machine) (k : HeldBrk), ∀ m' ∈ (brkFx dy M k).filterMap Effect.machineOf?,
        OpenAfter m' := by
      intro M k m' hm
      -- (D147: a `break` line nets as a D129 ending does, `Replay.netTake`, so its machine is `brkFx`'s)
      obtain ⟨hb1, hb2⟩ := Replay.brkFx_block dy M k m' hm
      exact openAfter_congr hb1 hb2
        (settle_openAfter dy _)
      -- (D147)
      -- (D147)
    have hA : ∀ (M : Machine) (k0 : HeldBrk), m' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k0).filterMap Effect.machineOf? → OpenAfter m' := fun M k0 hm => by
      unfold Replay.brkArmK at hm
      rw [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil,
        List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm; exact hF _ _ m' hm
    have hD : ∀ M : Machine, OpenAfter M → ∀ x0, m' ∈ (Replay.d141Arm dy M x0 e t d p.val (a.map (·.val))).filterMap Effect.machineOf? → OpenAfter m' := fun M hM x0 hm => by unfold Replay.d141Arm at hm; split at hm; (simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm; exact hA _ _ hm); (simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; exact openAfter_congr rfl rfl hM)
    -- D141, and since the owner's D147 a finished break a later line re-times: `d141Arm`'s undoing writes no machine
    split at hm
    · unfold Replay.brkOwn at hm; split at hm; exact hD m h _ hm; exact hA _ _ hm
    · unfold Replay.brkLine Replay.finArm at hm; split at hm; exact hD m h _ hm; split at hm; split at hm; exact hD m h _ hm; exact hA _ _ hm; exact hA _ _ hm
    -- (D147)
  case brkStart pl w =>
    split at hm
    · rename_i t0 _
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      obtain ⟨hb1, hb2⟩ := Replay.brkFx_block dy _ _ m' hm'
      exact openAfter_congr hb1 hb2
        (settle_openAfter dy _)
    · unfold Replay.brkStartArm at hm
      simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact openAfter_congr (Replay.runNet_keeps dy _).1 (Replay.runNet_keeps dy _).2.2.1 (settle_openAfter dy _)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm



/-- **A step keeps it** (`Seal.stepWith_machine_eq`: the step's machine is the last its arm writes, or the old one). -/
theorem stepWith_openAfter (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : OpenAfter st.machine) : OpenAfter (stepWith z dy sl st e).machine := by
  rw [Seal.stepWith_machine_eq]
  cases hl : ((arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => exact h
  | some m' => exact arm_openAfter dy sl st.machine e _ _ h m' (List.mem_of_getLast? hl)

/-- **The fold keeps it.** -/
theorem foldl_openAfter (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State), OpenAfter st.machine → OpenAfter (sv.foldl (stepWith z dy sl) st).machine
  | [], _, h => h
  | e :: sv, st, h => foldl_openAfter z dy sl sv _ (stepWith_openAfter z dy sl st e h)

/-! ## Every Break segment is a held break -/

/-- **No effect of `fx` draws a Break segment.** -/
def NoBrkSeg (fx : List Effect) : Prop :=
  ∀ x ∈ fx, ∀ d g, x = .dayAdd d (.segment g) → ∀ w, g.kind ≠ .brk w

theorem noBrkSeg_nil : NoBrkSeg [] := fun _ hx => by cases hx

theorem noBrkSeg_append {a b : List Effect} (ha : NoBrkSeg a) (hb : NoBrkSeg b) : NoBrkSeg (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with hx | hx
  · exact ha x hx
  · exact hb x hx
/-- An effect list that writes no segment at all draws no Break segment. -/
theorem noBrkSeg_of_no_segment {fx : List Effect} (h : ∀ x ∈ fx, ∀ d g, x ≠ .dayAdd d (.segment g)) : NoBrkSeg fx :=
  fun x hx d g hxg => absurd hxg (h x hx d g)
theorem redraw_noBrkSeg (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) :
    NoBrkSeg (redraw dy id old P).2 := by
  intro x hx d g hxg w hk
  rw [(Replay.redraw_draws_its_spans dy id old P x hx d g hxg).2] at hk
  cases hk
theorem settle_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) : NoBrkSeg (settle dy m).2 := by
  unfold settle; split
  · exact redraw_noBrkSeg dy _ _ _
  · exact noBrkSeg_nil
theorem closePause_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) (t : At) : NoBrkSeg (closePause dy m t).2 := by
  intro x hx d g hxg w hk
  unfold closePause at hx
  simp only at hx
  repeat' split at hx
  all_goals simp only [List.mem_singleton, List.not_mem_nil] at hx
  all_goals (try contradiction)
  subst hx
  simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at hxg
  rw [← hxg.2] at hk; cases hk
theorem creditFx_noBrkSeg (dy : Cal.Instant → Nat) (id : Log.Id) (t : At) (min : Nat) (ci : Option Log.U8) :
    NoBrkSeg (creditFx dy id t min ci) := by
  apply noBrkSeg_of_no_segment; intro x hx d g; simp only [creditFx, List.mem_cons, List.not_mem_nil] at hx
  rcases hx with rfl | rfl | rfl | h
  · simp
  · simp
  · simp
  · exact h.elim
theorem uncreditFx_noBrkSeg (c : Cut) : NoBrkSeg (uncreditFx c) := by
  apply noBrkSeg_of_no_segment; intro x hx d g; unfold uncreditFx at hx; split at hx
  · cases hx
  · simp only [List.mem_cons, List.not_mem_nil] at hx
    rcases hx with rfl | rfl | rfl | h
    · simp
    · simp
    · simp
    · exact h.elim
theorem obsFx_noBrkSeg (o : Option EnergyObs) : NoBrkSeg (obsFx o) := by
  apply noBrkSeg_of_no_segment; intro x hx d g; unfold obsFx at hx; split at hx
  · simp only [List.mem_singleton] at hx; subst hx; simp
  · cases hx
theorem cut_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) (t : At) : NoBrkSeg (cut dy m t).2 := by
  unfold cut; split
  · exact noBrkSeg_append (noBrkSeg_append (noBrkSeg_append (redraw_noBrkSeg dy _ _ _) (closePause_noBrkSeg dy m t))
      (creditFx_noBrkSeg dy _ _ _ _)) (obsFx_noBrkSeg _)
  · exact noBrkSeg_nil
theorem netOne_noBrkSeg (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Replay.Closed) :
    NoBrkSeg (netOne dy s e d C).2.1 := by
  unfold netOne; split
  · exact noBrkSeg_nil
  · refine noBrkSeg_append (redraw_noBrkSeg dy _ _ _) ?_
    split
    · apply noBrkSeg_of_no_segment; intro x hx d g
      simp only [List.mem_cons, List.not_mem_nil] at hx
      rcases hx with rfl | rfl | rfl | h
      · simp
      · simp
      · simp
      · exact h.elim
    · exact noBrkSeg_nil
theorem flatten_noBrkSeg (L : List (List Effect)) (h : ∀ l ∈ L, NoBrkSeg l) : NoBrkSeg L.flatten := by
  intro x hx; obtain ⟨l, hl, hxl⟩ := List.mem_flatten.1 hx; exact h l hl x hxl
theorem netClosed_noBrkSeg (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (m : Machine) :
    NoBrkSeg (netClosed dy s e d m).2 := by
  unfold netClosed
  apply flatten_noBrkSeg
  intro l hl; obtain ⟨C, -, rfl⟩ := List.mem_map.1 hl; exact netOne_noBrkSeg dy _ _ _ C
/-- **A give-back draws no break** (the owner's D137): it re-draws a block's pieces and credits it. -/
theorem giveBack_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) : NoBrkSeg (giveBack dy m).2 := by
  unfold giveBack
  apply flatten_noBrkSeg
  intro l hl; obtain ⟨C, -, rfl⟩ := List.mem_map.1 hl
  unfold giveOne; split
  · exact noBrkSeg_nil
  · refine noBrkSeg_append (redraw_noBrkSeg dy _ _ _) ?_
    split
    · apply noBrkSeg_of_no_segment; intro x hx d g
      simp only [List.mem_cons, List.not_mem_nil] at hx
      rcases hx with rfl | rfl | rfl | rfl | h
      · simp
      · simp
      · simp
      · simp
      · exact h.elim
    · exact noBrkSeg_nil
theorem netStart_noBrkSeg (dy : Cal.Instant → Nat) (t : At) (d : Nat) (m : Machine) :
    NoBrkSeg (netStart dy t d m).2 := by
  unfold netStart
  apply flatten_noBrkSeg
  intro l hl; obtain ⟨C, -, rfl⟩ := List.mem_map.1 hl; exact netOne_noBrkSeg dy _ _ _ C
theorem runNet_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) : NoBrkSeg (runNet dy m).2 := by
  rcases Replay.runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h]; exact noBrkSeg_nil
  · rw [h]; exact netClosed_noBrkSeg dy _ _ _ m
theorem doneClose_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Log.Id) (actual : Nat)
    (went : Option Log.U8) : NoBrkSeg (doneClose dy m t id actual went).2 := by
  unfold doneClose
  repeat' split
  all_goals first
    | exact noBrkSeg_nil
    | exact uncreditFx_noBrkSeg _
    | exact noBrkSeg_append (noBrkSeg_append (redraw_noBrkSeg dy _ _ _) (closePause_noBrkSeg dy m t)) (obsFx_noBrkSeg _)
theorem brkFx_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) (k : HeldBrk) : NoBrkSeg (brkFx dy m k) := by
  unfold brkFx netTake
  refine noBrkSeg_append (noBrkSeg_append (settle_noBrkSeg dy _) (netClosed_noBrkSeg dy _ _ _ _)) ?_
  apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
theorem doneFx_noBrkSeg (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Log.Id)
    (est actual : Nat) (went : Option Log.U8) (tags : List (List Char)) (ci : Log.U8) (isPartial : Bool) :
    NoBrkSeg (doneFx dy m line t d id est actual went tags ci isPartial) := by
  unfold doneFx
  intro x hx d' g hxg w hk
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | (((hx | hx) | hx) | hx) | hx
  · cases hxg
  · exact doneClose_noBrkSeg dy m t id actual went x hx d' g hxg w hk
  · exact creditFx_noBrkSeg dy id t actual (some ci) x hx d' g hxg w hk
  · split at hx
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      split at hx <;> simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, false_or] at hx <;> rcases hx with rfl | rfl | rfl | rfl <;> simp_all
    · cases hx
  · split at hx
    · simp only [List.mem_singleton] at hx; subst hx; cases hxg
    · simp only [List.mem_cons, List.not_mem_nil] at hx
      rcases hx with rfl | rfl | h
      · cases hxg
      · simp at hxg
      · exact h.elim
  · exact runNet_noBrkSeg dy _ x hx d' g hxg w hk

theorem extendFx_noBrkSeg (m : Machine) (id : Log.Id) (by_ : Nat) : NoBrkSeg (extendFx m id by_) := by
  apply noBrkSeg_of_no_segment; intro x hx d g; unfold extendFx at hx
  repeat' split at hx
  all_goals simp only [List.mem_singleton, List.not_mem_nil] at hx
  all_goals (try contradiction)
  subst hx; simp

/-- **Only a `break` line's own day half draws a Break segment**: the day family of any other entry draws a pause, an
interruption, an idle stretch or a routine, never a break. -/
theorem dayArm_noBrkSeg (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat)
    (h : ∀ p a w, e.ev ≠ .brk p a w) : NoBrkSeg (dayArm dy sl e t d) := by
  intro x hx d' g hxg w hk
  unfold dayArm at hx
  cases hev : e.ev <;> simp only [hev] at hx
  case brk p a w0 => exact h p a w0 hev
  case idle attributed min =>
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl) | hx
    · simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at hxg; rw [← hxg.2] at hk; cases hk
    · simp at hxg
    · split at hx
      · simp only [List.mem_singleton] at hx; subst hx; cases hxg
      · cases hx
  case routine item inst status actual =>
    split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at hxg; rw [← hxg.2] at hk; cases hk
      · simp at hxg
    · cases hx
  case wake => simp only [List.mem_singleton] at hx; subst hx; simp at hxg
  case arrive => simp only [List.mem_singleton] at hx; subst hx; simp at hxg
  case loc => simp only [List.mem_singleton] at hx; subst hx; simp at hxg
  case energy => simp only [List.mem_singleton] at hx; subst hx; cases hxg
  case plan => simp only [List.mem_singleton] at hx; subst hx; simp at hxg
  case demote => simp only [List.mem_singleton] at hx; subst hx; cases hxg
  case drop => simp only [List.mem_singleton] at hx; subst hx; cases hxg
  case close => simp only [List.mem_singleton] at hx; subst hx; cases hxg
  case unknown => simp only [List.mem_singleton] at hx; subst hx; cases hxg
  all_goals simp at hx

/-- **The completion family draws no segment.** -/
theorem completionArm_noBrkSeg (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    NoBrkSeg (completionArm z m e t d) := by
  intro x hx d' g hxg w hk
  unfold completionArm at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx; cases hxg
  · unfold completionCore at hx
    cases hev : e.ev <;> simp only [hev] at hx
    case done =>
      split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> cases hxg
    case routine =>
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | hx | hx
      · split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; cases hxg
      · subst hx; cases hxg
      · split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> cases hxg
    case skip =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; cases hxg
    case named =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; cases hxg
    all_goals simp at hx

/-- **A start's arm draws no Break segment** (C3). -/
theorem startArm_noBrkSeg (dy : Cal.Instant → Nat) (M : Machine) (line : Nat) (t : At) (d : Nat) (id : Log.Id)
    (pred : Log.U8) (rep : Option Log.U8) (hsw : Log.Num) (sleptMin : Log.U32) (loc : List Char) :
    NoBrkSeg (startArm dy M line t d id pred rep hsw sleptMin loc) := by
  unfold startArm
  refine noBrkSeg_append (noBrkSeg_append (noBrkSeg_append (noBrkSeg_append (noBrkSeg_append
    (netStart_noBrkSeg dy _ _ _) (cut_noBrkSeg dy _ _)) (runNet_noBrkSeg dy _)) ?_) (settle_noBrkSeg dy _)) ?_
  · apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
  · apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp

/-- **A `break_start`'s arm, as D105 has it, draws no Break segment.** -/
theorem brkStartArm_noBrkSeg (dy : Cal.Instant → Nat) (M : Machine) (t : At) (d : Nat) (planned : Nat)
    (where_ : Option (List Char)) : NoBrkSeg (brkStartArm dy M t d planned where_) := by
  unfold brkStartArm
  refine noBrkSeg_append (noBrkSeg_append (settle_noBrkSeg dy _) (runNet_noBrkSeg dy _)) ?_
  apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp

/-- **The one Break segment a break ended at a start draws** (D129): on the break's own ledger day, ending at `t` — *restated at the owner's D142* (README gap 5634): begun at or after `o.s`, drawn only where no earlier break covers it (`brkRecs`); D129 drew `[o.s, t)` whole. -/
theorem endRecs_seg (H : List HeldBrk) (o : Replay.OpenBrk) (t : At) (key : Nat) (x : Effect) (hx : x ∈ endRecs H o t key) (d : Nat) (g : Segment)
    (hxg : x = .dayAdd d (.segment g)) : d = o.day ∧ o.s.1 ≤ g.start.1 ∧ g.stop = t := by
  rcases Replay.endRecs_cases _ _ _ _ x hx with ⟨g', h1, h2, -, h3⟩ | ⟨r, h1⟩ | ⟨j, -, c, c', h1⟩; rotate_right; (rw [hxg] at h1; simp at h1)
  -- (W-53 track K: an ending also re-draws the breaks it reaches back to, `reachFx`, which draw no segment op)
  · rw [hxg] at h1
    simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    exact ⟨rfl, h3, h2⟩
  · rw [hxg] at h1; simp at h1

/-- **An arm draws a Break segment only for a `break` line, or for a break a start ends** (the owner's D129: a `start`
that ends the running break, and a `break_start` a held start ends, draw that break's segment, as its `break` line
would) — every other entry's arm draws none.  *Restated at D129* from "only for a `break` line", which a start ending a
running break refutes (`arm_noBrkSeg_as_w49_stated_it_is_refuted`). -/
theorem arm_noBrkSeg (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat)
    (h : ∀ p a w, e.ev ≠ .brk p a w)
    (hs : ∀ id pred rep hsw sleptMin loc b1 b2, e.ev = .start id pred rep hsw sleptMin loc b1 b2 → endsBrk m t = none)
    (hb : ∀ p w, e.ev = .brkStart p w → firstStart t d m = none) : NoBrkSeg (arm dy sl m e t d) := by
  have hd := dayArm_noBrkSeg dy sl e t d h
  unfold Replay.arm
  cases hev : e.ev
  case brk p a w => exact absurd hev (h p a w)
  case start id pred rep hsw sleptMin loc b1 b2 =>
    simp only [hs id pred rep hsw sleptMin loc b1 b2 hev]
    exact startArm_noBrkSeg dy m _ t d _ _ _ _ _ _
  case pause id =>
    simp only; split
    · split
      · refine noBrkSeg_append (settle_noBrkSeg dy _) ?_
        apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
      · exact noBrkSeg_nil
    · exact noBrkSeg_nil
  case unpause id =>
    simp only; split
    · split
      · refine noBrkSeg_append (noBrkSeg_append (closePause_noBrkSeg dy m t) (settle_noBrkSeg dy _)) ?_
        apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
      · exact noBrkSeg_nil
    · exact noBrkSeg_nil
  case interrupt id =>
    simp only
    refine noBrkSeg_append (noBrkSeg_append (closePause_noBrkSeg dy m t) (settle_noBrkSeg dy _)) ?_
    apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
  case resume lost dropped =>
    simp only; split
    · refine noBrkSeg_append (noBrkSeg_append (noBrkSeg_append ?_ (settle_noBrkSeg dy _))
        (netClosed_noBrkSeg dy _ _ _ _)) ?_
      · intro x hx d' g hxg w hk
        simp only [List.mem_cons, List.not_mem_nil] at hx
        rcases hx with rfl | rfl | rfl | hx
        · simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at hxg; rw [← hxg.2] at hk; cases hk
        · cases hxg
        · simp at hxg
        · exact hx.elim
      · apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
    · refine noBrkSeg_append (noBrkSeg_append ?_ (settle_noBrkSeg dy _)) ?_
      · apply noBrkSeg_of_no_segment; intro x hx d g
        simp only [List.mem_cons, List.not_mem_nil] at hx
        rcases hx with rfl | rfl | hx
        · simp
        · simp
        · exact hx.elim
      · apply noBrkSeg_of_no_segment; intro x hx d g; simp only [List.mem_singleton] at hx; subst hx; simp
  case stop id rem =>
    simp only; split
    · split
      · refine noBrkSeg_append (noBrkSeg_append (cut_noBrkSeg dy m t) (runNet_noBrkSeg dy _)) ?_
        apply noBrkSeg_of_no_segment; intro x hx d g
        simp only [List.mem_cons, List.not_mem_nil] at hx
        rcases hx with rfl | rfl | hx
        · simp
        · simp
        · exact hx.elim
      · exact noBrkSeg_nil
    · exact noBrkSeg_nil
  case extend id by_ =>
    simp only
    intro x hx; rcases List.mem_cons.1 hx with rfl | hx
    · intro d g hxg; cases hxg
    · exact extendFx_noBrkSeg m id by_.val x hx
  case done id est actual went tags ci isPartial =>
    exact doneFx_noBrkSeg dy m e.line t d id est.val actual.val went tags ci isPartial
  case brkStart pl w =>
    simp only [hb pl w hev]
    exact brkStartArm_noBrkSeg dy m t d _ _
  all_goals (simp only; exact hd)
/-! ### The newest ledger day the held breaks hold, and `pruneBrks`' bound -/
theorem fm_mono (i j : Nat) (hij : i ≤ j) :
    ∀ l : List HeldBrk, l.foldl (fun a k => max a k.day) i ≤ l.foldl (fun a k => max a k.day) j
  | [] => hij
  | k :: l => by
    simp only [List.foldl_cons]
    exact fm_mono _ _ (by omega) l
theorem fm_ge_init (i : Nat) : ∀ l : List HeldBrk, i ≤ l.foldl (fun a k => max a k.day) i
  | [] => Nat.le_refl i
  | k :: l => by
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left i k.day) (fm_ge_init _ l)
theorem fm_ge_mem (i : Nat) : ∀ (l : List HeldBrk) (k : HeldBrk), k ∈ l → k.day ≤ l.foldl (fun a k => max a k.day) i
  | [], _, h => by cases h
  | x :: l, k, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right i k.day) (fm_ge_init _ l)
    · exact fm_ge_mem _ l k h
theorem fm_le (i c : Nat) (hi : i ≤ c) :
    ∀ l : List HeldBrk, (∀ k ∈ l, k.day ≤ c) → l.foldl (fun a k => max a k.day) i ≤ c
  | [], _ => hi
  | x :: l, h => by
    simp only [List.foldl_cons]
    exact fm_le _ c (Nat.max_le.2 ⟨hi, h x List.mem_cons_self⟩) l (fun k hk => h k (List.mem_cons_of_mem _ hk))
theorem fm_attain (i : Nat) : ∀ l : List HeldBrk,
    l.foldl (fun a k => max a k.day) i = i ∨ ∃ k ∈ l, l.foldl (fun a k => max a k.day) i = k.day
  | [] => Or.inl rfl
  | x :: l => by
    simp only [List.foldl_cons]
    rcases fm_attain (max i x.day) l with h | ⟨k, hk, h⟩
    · rw [h]
      by_cases hx : x.day ≤ i
      · left; omega
      · right; exact ⟨x, List.mem_cons_self, by omega⟩
    · exact Or.inr ⟨k, List.mem_cons_of_mem _ hk, h⟩
/-- **`pruneBrks` keeps the newest ledger day it was given.** -/
theorem hi_pruneBrks (L : List HeldBrk) :
    (pruneBrks L).foldl (fun a k => max a k.day) 0 = L.foldl (fun a k => max a k.day) 0 := by
  unfold pruneBrks
  simp only
  apply Nat.le_antisymm
  · exact fm_le 0 _ (Nat.zero_le _) _ (fun k hk => fm_ge_mem 0 L k (List.mem_filter.1 hk).1)
  · rcases fm_attain 0 L with h | ⟨k, hk, h⟩
    · rw [h]; exact Nat.zero_le _
    · rw [h]
      exact fm_ge_mem 0 _ k (List.mem_filter.2 ⟨hk, by simp only [decide_eq_true_eq]; omega⟩)
/-- **A break `pruneBrks` drops is more than 31 ledger days behind the newest it keeps.** -/
theorem prune_keeps (k0 : HeldBrk) (l : List HeldBrk) (k : HeldBrk) (hk : k ∈ k0 :: l) :
    k ∈ pruneBrks (k0 :: l) ∨ k.day + 31 < (pruneBrks (k0 :: l)).foldl (fun a k => max a k.day) 0 := by
  rw [hi_pruneBrks]
  by_cases hc : (k0 :: l).foldl (fun a k => max a k.day) 0 ≤ k.day + 31
  · left; unfold pruneBrks; exact List.mem_filter.2 ⟨hk, by simpa using hc⟩
  · right; omega
/-- **The newest day never falls**: a held list grown by one and pruned holds a day at least as new. -/
theorem hi_grows (k0 : HeldBrk) (l : List HeldBrk) :
    l.foldl (fun a k => max a k.day) 0 ≤ (pruneBrks (k0 :: l)).foldl (fun a k => max a k.day) 0 := by
  rw [hi_pruneBrks]
  simp only [List.foldl_cons]
  exact fm_mono _ _ (Nat.zero_le _) l
/-! ### Where a day's segments come from -/
/-- **Every op but a drawing or an un-drawing keeps a day's segments.** -/
theorem DayOp.apply_segments (op : DayOp) (a : DayAcc) :
    ∀ g ∈ (op.apply a).segments, g ∈ a.segments ∨ op = .segment g ∨ ∃ k c c', op = .redraw k c c' ∧ k.s.1 ≤ g.start.1 ∧ g.stop = k.e := by
  intro g hg
  cases op with
  | segment s =>
    simp only [DayOp.apply, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hg
  | unsegment s => exact Or.inl (List.mem_of_mem_erase hg)
  | unsegBrks k c rest => (simp only [DayOp.apply, List.mem_filter] at hg; obtain ⟨hg, -⟩ := hg; split at hg; exact Or.inl (List.mem_of_mem_erase hg); exact Or.inl hg) | redraw k c c' => (simp only [DayOp.apply] at hg; unfold DayAcc.redrawBrk at hg; split at hg; exact Or.inl hg; (simp only [List.mem_append] at hg; rcases hg with hg | hg; exact Or.inr (Or.inr ⟨k, c, c', rfl, (Replay.drawSeg_mem hg).1, (Replay.drawSeg_mem hg).2.1⟩); (split at hg; exact Or.inl (List.mem_of_mem_erase hg); exact Or.inl hg)))
  | credit id min ci =>
    left; simp only [DayOp.apply] at hg; repeat' split at hg
    all_goals exact hg
  | net id ci k line =>
    left; simp only [DayOp.apply, DayAcc.netDurOf, DayAcc.netCredit] at hg; repeat' split at hg
    all_goals exact hg
  | wake t slept onset =>
    left; simp only [DayOp.apply] at hg; repeat' split at hg
    all_goals exact hg
  | arrive t lc w bu =>
    left; simp only [DayOp.apply] at hg; repeat' split at hg
    all_goals exact hg
  | idle r =>
    left; simp only [DayOp.apply] at hg; repeat' split at hg
    all_goals exact hg
  | undur l k =>
    left; simp only [DayOp.apply, DayAcc.undurOf] at hg; repeat' split at hg
    all_goals exact hg
  | durPre l k =>
    left; simp only [DayOp.apply, DayAcc.netDurOf] at hg; repeat' split at hg
    all_goals exact hg
  | _ => left; exact hg
theorem DayOp.alterFn_segments (op : DayOp) (o : Option DayAcc) (a' : DayAcc) (h : op.alterFn o = some a') :
    ∀ g ∈ a'.segments, (∃ a, o = some a ∧ g ∈ a.segments) ∨ op = .segment g ∨ ∃ k c c', op = .redraw k c c' ∧ k.s.1 ≤ g.start.1 ∧ g.stop = k.e := by
  intro g hg
  cases o with
  | some a =>
    simp only [DayOp.alterFn, Option.some.injEq] at h
    subst h
    rcases DayOp.apply_segments op a g hg with h | h
    · exact Or.inl ⟨a, rfl, h⟩
    · exact Or.inr h
  | none =>
    have he : a' = op.apply DayAcc.empty := by
      cases op <;> simp only [DayOp.alterFn, Option.some.injEq, reduceCtorEq] at h <;> exact h.symm
    subst he
    rcases DayOp.apply_segments op DayAcc.empty g hg with h | h
    · simp [DayAcc.empty] at h
    · exact Or.inr h
theorem applyEffect_days (st : State) (x : Effect) (h : ∀ d op, x ≠ .dayAdd d op) :
    (applyEffect st x).days = st.days := by
  cases x
  case dayAdd d op => exact absurd rfl (h d op)
  case itemDaySub => simp only [applyEffect]; split <;> rfl
  case obs o => cases o <;> rfl
  all_goals rfl
/-- **A segment of a day after some effects was there before, or one of them drew it.** -/
theorem applyEffects_seg_src : ∀ (fx : List Effect) (st : State) (d : Nat) (a' : DayAcc),
    (applyEffects st fx).days.get d = some a' →
      ∀ g ∈ a'.segments, (∃ a, st.days.get d = some a ∧ g ∈ a.segments) ∨ Effect.dayAdd d (.segment g) ∈ fx ∨ ∃ k c c', Effect.dayAdd d (.redraw k c c') ∈ fx ∧ k.s.1 ≤ g.start.1 ∧ g.stop = k.e
  | [], st, d, a', h, g, hg => Or.inl ⟨a', h, hg⟩
  | x :: fx, st, d, a', h, g, hg => by
    rcases applyEffects_seg_src fx (applyEffect st x) d a' h g hg with ⟨a, ha, hga⟩ | hx
    · by_cases hd : ∃ d' op, x = .dayAdd d' op
      · obtain ⟨d', op, rfl⟩ := hd
        simp only [applyEffect, Replay.HMap.get_alter] at ha
        split at ha
        · rename_i hdd
          subst hdd
          rcases DayOp.alterFn_segments op _ a ha g hga with h1 | h1 | ⟨k, c, c', rfl, h2, h3⟩; rotate_right; exact Or.inr (Or.inr ⟨k, c, c', List.mem_cons_self, h2, h3⟩)
          · exact Or.inl h1
          · subst h1; exact Or.inr (Or.inl List.mem_cons_self)
        · exact Or.inl ⟨a, ha, hga⟩
      · have := applyEffect_days st x (fun d' op hx => hd ⟨d', op, hx⟩)
        rw [this] at ha
        exact Or.inl ⟨a, ha, hga⟩
    · rcases hx with hx | ⟨k, c, c', hx, h2, h3⟩; exact Or.inr (Or.inl (List.mem_cons_of_mem _ hx)); exact Or.inr (Or.inr ⟨k, c, c', List.mem_cons_of_mem _ hx, h2, h3⟩)
/-! ### The invariant, and its step -/
/-- **Every Break segment of a day is a held break** — a break the machine holds with that segment's span on that
ledger day — **or one more than 31 ledger days behind the newest it holds** (`pruneBrks`' bound, the owner's D94, README
gap 4914). -/
def BrkHeld (st : State) : Prop :=
  ∀ d a, st.days.get d = some a → ∀ g ∈ a.segments, ∀ w, g.kind = .brk w →
    (∃ k ∈ st.machine.brks, k.s.1 ≤ g.start.1 ∧ k.e = g.stop ∧ k.day = d) ∨
      d + 31 < st.machine.brks.foldl (fun a k => max a k.day) 0
/-- **A step's held breaks are the old ones, or the old ones with one more, pruned** (`Seal.arm_brks`). -/
theorem stepWith_brks (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (stepWith z dy sl st e).machine.brks = st.machine.brks ∨
      (∃ k, (stepWith z dy sl st e).machine.brks = pruneBrks (k :: st.machine.brks)) ∨
      ∃ k x, (∃ p a w, e.ev = .brk p a w ∧ (findEnded st.machine (e.t.val, e.off.val) = some x ∨ (findEnded st.machine (e.t.val, e.off.val) = none ∧ st.machine.brkOpen = none ∧ findFin st.machine (e.t.val, e.off.val) p.val = some x)) ∧
        d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a.map (·.val))) (dy e.t.val) = true) ∧
        (stepWith z dy sl st e).machine.brks = pruneBrks (k :: st.machine.brks.erase x.hb) := by
  rw [Seal.stepWith_machine_eq]
  cases hl : ((arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => exact Or.inl rfl
  | some m' => exact Seal.arm_brks dy sl st.machine e _ _ m' (List.mem_of_getLast? hl)
/-- **A `break` line's step holds its break**: the machine after it holds `[t, brkEnd)` on the line's day, pruned — *restated at D129* for a line that is not the own line of a break a start already ended (`Machine.ended`, `findEnded`; one
ending until W-52 repair track R), which holds nothing new (`stepWith_brks_of_brk_as_w49_stated_it_is_refuted`). -/
theorem stepWith_brks_of_brk (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    {p : Log.U32} {a : Option Log.U32} {w : Option (List Char)} (hev : e.ev = .brk p a w)
    (hown : findEnded st.machine (e.t.val, e.off.val) = none) (hfin : ∀ x, st.machine.brkOpen = none → findFin st.machine (e.t.val, e.off.val) p.val = some x → d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a.map (·.val))) (dy e.t.val) = false) :
    (stepWith z dy sl st e).machine.brks =
      pruneBrks (heldOf st.machine e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val)) ::
        st.machine.brks) := by
  rw [Seal.stepWith_machine_eq]
  -- since the owner's D141 a line not its break's own is read over `forgetIdle`, whose held breaks are the old ones
  obtain ⟨M, hMb, harm⟩ : ∃ M : Machine, M = st.machine ∧ arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
      (giveBack dy M).2 ++ brkFx dy (giveBack dy M).1
        (heldOf M e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val))) ++
        brkDay M e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val)) ++ reachFx M.brks (heldOf M e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val))) := by
    exact ⟨st.machine, rfl, (Replay.arm_brk_of_endable dy sl st.machine e _ _ hev).2.2 hown hfin⟩
    -- (D147: no finished break is re-timed)
  rw [harm, List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 _ _ _ _ _ _).1, List.append_nil, List.filterMap_append,
    (Replay.giveBack_obs dy _).2.2, List.nil_append, ← hMb, ← (Replay.giveBack_keeps dy M).2.2.1]
  have hm := Replay.brkFx_brk dy (giveBack dy M).1
    (heldOf M e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val)))
  revert hm
  unfold brkFx netTake
  simp only [List.filterMap_append, (settle_fx_obs dy _).2.2, (netClosed_obs dy _ _ _ _).2.2, List.nil_append,
    List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton, forall_eq,
    List.getLast?_singleton, Option.getD_some]
  exact id
/-- **A break held on top of the old ones, pruned, is held or more than 31 ledger days behind the newest kept.** -/
theorem held_of_prune (st' : State) (k : HeldBrk) (old : List HeldBrk) (hB : st'.machine.brks = pruneBrks (k :: old))
    (d : Nat) (g : Segment) (h1 : k.s.1 ≤ g.start.1) (h2 : k.e = g.stop) (h3 : k.day = d) :
    (∃ k' ∈ st'.machine.brks, k'.s.1 ≤ g.start.1 ∧ k'.e = g.stop ∧ k'.day = d) ∨
      d + 31 < st'.machine.brks.foldl (fun a k => max a k.day) 0 := by
  rw [hB]
  rcases prune_keeps k old k List.mem_cons_self with hk' | hk'
  · exact Or.inl ⟨k, hk', h1, h2, h3⟩
  · exact Or.inr (h3 ▸ hk')
/-- **A start ending the running break holds it** (D129): the machine after it holds `[o.s, t)` on the break's ledger
day, pruned, with the old breaks. -/
theorem stepWith_brks_of_start (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    {id : Log.Id} {pred : Log.U8} {rep : Option Log.U8} {hsw : Log.Num} {sleptMin : Log.U32} {loc : List Char}
    {b1 b2 : Log.U32} (hev : e.ev = .start id pred rep hsw sleptMin loc b1 b2) {o : Replay.OpenBrk}
    (hE : endsBrk st.machine (e.t.val, e.off.val) = some o) :
    (stepWith z dy sl st e).machine.brks = pruneBrks (⟨o.s, (e.t.val, e.off.val), o.day, e.line, o.planned, o.where_, (e.t.val, e.off.val)⟩ :: st.machine.brks) := by
  rw [Seal.stepWith_machine_eq]
  have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
      endRecs st.machine.brks o (e.t.val, e.off.val) e.line ++ startArm dy (endMachine st.machine o (e.t.val, e.off.val) e.line) e.line
        (e.t.val, e.off.val) (dy e.t.val) id pred rep hsw sleptMin loc := by
    unfold Replay.arm; simp only [hev, hE]
  rw [harm, List.filterMap_append, (Replay.endRecs_obs _ _ _ _).2.2, List.nil_append, Replay.startArm_machines]
  simp only [List.getLast?_singleton, Option.getD_some]
  rw [(settle_keeps dy _).2.2.1]
  exact (Replay.runNet_keeps dy _).2.2.1.trans ((Replay.cut_brk dy _ _).trans (Replay.netStart_keeps dy _ _ _).2.2.1)
/-- **`stepWith_brks` as W-53 track K stated it, refuted** (the W-54 auditor, README gap 5877): its third case read a re-timing line only at a break D129 ended (`findEnded`), and on the W-53 repair's kernel a later line at a finished break's stamp re-times that break (D147, `findFin`) — the 09:30–09:40 break re-timed to 09:34 leaves the held breaks `[09:30–09:34]`: not the old ones, not the old ones with one more, and no ending at 09:30.  Restated at the W-53 repair with the `findFin` case; that step listed it as refuted by name and was not (README gap 5877). -/
theorem stepWith_brks_as_w53_stated_it_is_refuted :
    ¬ ∀ (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry),
      (stepWith z dy sl st e).machine.brks = st.machine.brks ∨
      (∃ k, (stepWith z dy sl st e).machine.brks = pruneBrks (k :: st.machine.brks)) ∨
      ∃ k x, (∃ p a w, e.ev = .brk p a w ∧ findEnded st.machine (e.t.val, e.off.val) = some x ∧
        d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a.map (·.val))) (dy e.t.val) = true) ∧
        (stepWith z dy sl st e).machine.brks = pruneBrks (k :: st.machine.brks.erase x.hb) := by
  intro h
  let x0 : HeldBrk := ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924370800, 0⟩, ⟨false, 0⟩), 739865, 1, 10, none, (⟨63924370800, 0⟩, ⟨false, 0⟩)⟩
  let st : State := { State.init 2 with machine := ⟨none, none, none, [x0], none, [], []⟩ }
  let e := bE 2 63924370200 (.brk 10 (some 4) none)
  let k1 : HeldBrk := ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924370440, 0⟩, ⟨false, 0⟩), 739865, 2, 10, none, (⟨63924370800, 0⟩, ⟨false, 0⟩)⟩
  have hb : (stepWith utcZone (fun _ => 739865) (fun _ => none) st e).machine.brks = [k1] := by decide
  have hE : findEnded st.machine (e.t.val, e.off.val) = none := by decide
  rcases h utcZone (fun _ => 739865) (fun _ => none) st e with h1 | ⟨k, h2⟩ | ⟨k, x, ⟨p, a, w, -, hf, -⟩, -⟩
  · rw [hb] at h1; revert h1; decide
  · rw [hb] at h2; exact pruneBrks_pair_ne k x0 k1 (by decide) rfl h2.symm
  · rw [hE] at hf; cases hf
/-- **`stepWith_brks_of_brk` as W-53 track K stated it, refuted** (the W-54 auditor, README gap 5877): with no ending at its stamp a `break` line held its break beside the old ones; a line re-timing a finished break (D147) holds it in that break's place.  The W-53 repair restated it with the hypothesis `hfin` (no finished break re-timed), which its block did not record. -/
theorem stepWith_brks_of_brk_as_w53_stated_it_is_refuted :
    ¬ ∀ (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) (p : Log.U32) (a : Option Log.U32) (w : Option (List Char)),
      e.ev = .brk p a w → findEnded st.machine (e.t.val, e.off.val) = none →
      (stepWith z dy sl st e).machine.brks = pruneBrks (heldOf st.machine e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val)) :: st.machine.brks) := by
  intro h
  have := h utcZone (fun _ => 739865) (fun _ => none) { State.init 2 with machine := ⟨none, none, none, [⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924370800, 0⟩, ⟨false, 0⟩), 739865, 1, 10, none, (⟨63924370800, 0⟩, ⟨false, 0⟩)⟩], none, [], []⟩ } (bE 2 63924370200 (.brk 10 (some 4) none)) 10 (some 4) none rfl (by decide)
  revert this; decide
/-- **A `break_start` a held start ends holds the break** (D129): `[t, t0)` on its ledger day, pruned. -/
theorem stepWith_brks_of_brkStart (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) {p : Log.U32} {w : Option (List Char)} (hev : e.ev = .brkStart p w) {t0 : At}
    (hF : firstStart (e.t.val, e.off.val) (dy e.t.val) st.machine = some t0) :
    (stepWith z dy sl st e).machine.brks = pruneBrks (⟨(e.t.val, e.off.val), t0, dy e.t.val, e.line, p.val, w, t0⟩ :: st.machine.brks) := by
  rw [Seal.stepWith_machine_eq]
  have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
      endBrkFx dy st.machine ⟨(e.t.val, e.off.val), p.val, w, dy e.t.val⟩ t0 e.line := by
    unfold Replay.arm; simp only [hev, hF]
  rw [harm]
  have hm := Replay.brkFx_brk dy { forget st.machine with ended := pushEnded (endingOf ⟨(e.t.val, e.off.val), p.val, w, dy e.t.val⟩ t0 e.line) st.machine }
    ⟨(e.t.val, e.off.val), t0, dy e.t.val, e.line, p.val, w, t0⟩
  revert hm
  unfold endBrkFx brkFx netTake
  simp only [List.filterMap_append, (settle_fx_obs dy _).2.2, (netClosed_obs dy _ _ _ _).2.2, List.nil_append, (Replay.endRecs_obs _ _ _ _).2.2,
    List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton, forall_eq, List.append_nil,
    List.getLast?_singleton, Option.getD_some]
  exact id
/-- **What D141's two day operations leave of a day's segments** (the owner's **D141**, README gap 5660, W-52b track K2):
every segment the day holds after them it held before, and on the ended break's day `D` a Break segment the held break `k`
witnesses survives only when a break of `rest` witnesses it too (`DayOp.unsegBrks`). -/
theorem undo141_seg (st : State) (D : Nat) (k : HeldBrk) (c : At) (rest : List HeldBrk) (key d : Nat) (a' : DayAcc)
    (h : (applyEffects st [.dayAdd D (.unsegBrks k c rest), .dayAdd D (.unbrkAt key)]).days.get d = some a')
    (g : Segment) (hg : g ∈ a'.segments) :
    ∃ a, st.days.get d = some a ∧ g ∈ a.segments ∧
      (d = D → ∀ w, g.kind = .brk w → k.s.1 ≤ g.start.1 → g.stop = k.e →
        ∃ k' ∈ rest, k'.s.1 ≤ g.start.1 ∧ k'.e = g.stop ∧ k'.day = k.day) := by
  simp only [applyEffects, List.foldl_cons, List.foldl_nil, applyEffect, Replay.HMap.get_alter] at h
  by_cases hd : d = D
  · subst hd
    simp only [if_true] at h
    cases ha : st.days.get d with
    | none => rw [ha] at h; simp only [DayOp.alterFn, DayOp.apply, Option.some.injEq] at h; subst h; simp [DayAcc.empty] at hg
    | some a =>
      rw [ha] at h; simp only [DayOp.alterFn, DayOp.apply, Option.some.injEq] at h; subst h
      simp only [List.mem_filter] at hg
      have hg1 : g ∈ a.segments := by obtain ⟨hg, -⟩ := hg; split at hg; exact List.mem_of_mem_erase hg; exact hg
      refine ⟨a, rfl, hg1, fun _ w hw h1 h2 => ?_⟩
      have h3 := hg.2
      simp only [hw, h1, h2, decide_true, Bool.true_and, Bool.and_true] at h3
      have h4 : ∃ x, x ∈ rest ∧ (x.s.fst ≤ g.start.fst ∧ x.e = k.e) ∧ x.day = k.day := by simpa using h3
      obtain ⟨k', hk', ⟨c1, c2⟩, c3⟩ := h4
      exact ⟨k', hk', c1, c2.trans h2.symm, c3⟩
  · simp only [if_neg hd] at h; exact ⟨a', h, hg, fun h' => absurd h' hd⟩
/-- **A `break` line ending a break D129 ended keeps the invariant** (the owner's **D141**; restated at W-52 repair track R
for an ending anywhere among those held, `findEnded`): the ending's Break segments are undone on its day save those a
break of `rest` (the held breaks with the ending's let go, `List.erase`) witnesses (`undo141_seg`), the line's own segment
is witnessed by the break it holds (`brkDay_cases`), and the held breaks after it are `rest` with the line's own on top,
pruned, whose newest day is not before the dropped one's (the line's ledger day is at or after the ended break's). -/
theorem fm_erase_le (l : List HeldBrk) (k k0 : HeldBrk) (hk : k ∈ l) (hday : k.day ≤ k0.day) :
    l.foldl (fun a k => max a k.day) 0 ≤ (k0 :: l.erase k).foldl (fun a k => max a k.day) 0 := by
  apply fm_le 0 _ (Nat.zero_le _) l
  intro j hj
  by_cases hjk : j = k
  · subst hjk; exact Nat.le_trans hday (fm_ge_mem 0 _ k0 List.mem_cons_self)
  · exact fm_ge_mem 0 _ j (List.mem_cons_of_mem _ ((List.mem_erase_of_ne hjk).2 hj))




theorem stepWith_brkHeld_d141 (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : BrkHeld st) {p : Log.U32} {a0 : Option Log.U32} {w0 : Option (List Char)} (hev : e.ev = .brk p a0 w0) {x : Ending}
    (hK : findEnded st.machine (e.t.val, e.off.val) = some x ∨ (findEnded st.machine (e.t.val, e.off.val) = none ∧ st.machine.brkOpen = none ∧ findFin st.machine (e.t.val, e.off.val) p.val = some x))
    (hg : d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a0.map (·.val))) (dy e.t.val) = true) :
    BrkHeld (stepWith z dy sl st e) := by
  have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
      [.dayAdd x.day (.unsegBrks x.hb (drawnFrom st.machine.brks x.hb) (st.machine.brks.erase x.hb)), .dayAdd x.day (.unbrkAt x.key)] ++ growFx st.machine.brks x.hb ++
        brkArmK dy (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)) (wideOf x (heldOf (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)))) := by
    rcases hK with hK | ⟨hE, ho, hF⟩; exact (Replay.arm_brk_of_endable dy sl st.machine e _ _ hev).1 x hK hg; (rcases Replay.arm_brk_eq dy sl st.machine e _ _ hev with ⟨o, ho', -⟩ | ⟨-, he⟩; (rw [ho] at ho'; cases ho'); (rw [he]; unfold Replay.brkLine Replay.finArm; simp only [hE, hF, hg, if_true]; unfold Replay.d141Arm; simp only [hg, if_true]))
  have hday : x.day ≤ dy e.t.val := by unfold d141Ok at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg.1.1.2
  have hmem : x.hb ∈ st.machine.brks := by unfold d141Ok at hg; simp only [Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg.1.2
  have hB : (stepWith z dy sl st e).machine.brks =
      pruneBrks (wideOf x (heldOf (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val))) :: st.machine.brks.erase x.hb) := by
    rw [Seal.stepWith_machine_eq, harm, List.filterMap_append, List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil]
    simp only [List.filterMap_cons, List.filterMap_nil, Effect.machineOf?, List.nil_append]
    unfold brkArmK
    rw [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 _ _ _ _ _ _).1, List.append_nil, List.filterMap_append,
      (Replay.giveBack_obs dy _).2.2, List.nil_append]
    have hm := Replay.brkFx_brk dy (giveBack dy (d141Machine st.machine x)).1
      (wideOf x (heldOf (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val))))
    rw [(Replay.giveBack_keeps dy _).2.2.1] at hm
    revert hm
    unfold brkFx netTake
    simp only [List.filterMap_append, (settle_fx_obs dy _).2.2, (netClosed_obs dy _ _ _ _).2.2, List.nil_append,
      List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton, forall_eq,
      List.getLast?_singleton, Option.getD_some]
    exact id
  -- a break of `rest` (the held breaks with the ending's let go) is held after the step, or behind the bound
  have hR : ∀ k ∈ st.machine.brks.erase x.hb, ∀ g : Segment, k.s.1 ≤ g.start.1 → g.stop = k.e →
      (∃ k' ∈ (stepWith z dy sl st e).machine.brks, k'.s.1 ≤ g.start.1 ∧ k'.e = g.stop ∧ k'.day = k.day) ∨
        k.day + 31 < (stepWith z dy sl st e).machine.brks.foldl (fun a k => max a k.day) 0 := fun k hk g h1 h2 => by
    rw [hB]; rcases prune_keeps _ _ k (List.mem_cons_of_mem _ hk) with hk' | hk'
    · exact Or.inl ⟨k, hk', h1, h2.symm, rfl⟩
    · exact Or.inr hk'
  have hfx : effectsWith z dy sl st e =
      [Effect.header (dy e.t.val) (HeaderRec.of e false), .global (e.t.val, e.off.val),
        .seam (dy e.t.val) ⟨(e.t.val, e.off.val), seamKindOf e.ev⟩] ++
      ([.dayAdd x.day (.unsegBrks x.hb (drawnFrom st.machine.brks x.hb) (st.machine.brks.erase x.hb)), .dayAdd x.day (.unbrkAt x.key)] ++ growFx st.machine.brks x.hb) ++
      (brkArmK dy (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)) (wideOf x (heldOf (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)))) ++
        completionArm z st.machine e (e.t.val, e.off.val) (dy e.t.val)) := by
    unfold effectsWith; rw [harm]; simp
  have hH : (applyEffects st [Effect.header (dy e.t.val) (HeaderRec.of e false), .global (e.t.val, e.off.val),
      .seam (dy e.t.val) ⟨(e.t.val, e.off.val), seamKindOf e.ev⟩]).days = st.days := by
    simp [applyEffects, applyEffect]
  intro d a' hget g hg' w hk
  change (applyEffects st (effectsWith z dy sl st e)).days.get d = some a' at hget
  rw [hfx, applyEffects_append, applyEffects_append st] at hget
  rcases applyEffects_seg_src _ _ d a' hget g hg' with ⟨a2, ha2, hga2⟩ | hx | ⟨kr, cr, cr', hxr, hr1, hr2⟩
  · rw [applyEffects_append] at ha2
    rcases applyEffects_seg_src _ _ d a2 ha2 g hga2 with ⟨a3, ha3, hga3⟩ | hx | ⟨kr, cr, cr', hxr, hr1, hr2⟩
    · obtain ⟨a, ha, hga, hsurv⟩ := undo141_seg _ x.day x.hb (drawnFrom st.machine.brks x.hb) (st.machine.brks.erase x.hb) x.key d a3 ha3 g hga3
      rw [hH] at ha
      rcases h d a ha g hga w hk with ⟨k1, hk1, h1, h2, h3⟩ | hd
      · by_cases hk1x : k1 = x.hb
        · subst hk1x
          obtain ⟨k', hk', c1, c2, c3⟩ := hsurv h3.symm w hk h1 h2.symm
          rcases hR k' hk' g c1 c2.symm with ⟨k'', hk'', c4, c5, c6⟩ | hb
          · exact Or.inl ⟨k'', hk'', c4, c5, c6.trans (c3.trans h3)⟩
          · exact Or.inr (by rw [← c3.trans h3]; exact hb)
        · rcases hR k1 ((List.mem_erase_of_ne hk1x).2 hk1) g h1 h2.symm with ⟨k'', hk'', c4, c5, c6⟩ | hb
          · exact Or.inl ⟨k'', hk'', c4, c5, c6.trans h3⟩
          · exact Or.inr (h3 ▸ hb)
      · rw [hB]; refine Or.inr (Nat.lt_of_lt_of_le hd ?_)
        rw [hi_pruneBrks]
        exact fm_erase_le _ _ _ hmem hday
    · obtain ⟨j, -, c, c', hj⟩ := Replay.growFx_redraw _ _ _ hx; cases hj
    · obtain ⟨j, hj, c, c', hjx⟩ := Replay.growFx_redraw _ _ _ hxr
      simp only [Effect.dayAdd.injEq, DayOp.redraw.injEq] at hjx; obtain ⟨rfl, rfl, -, -⟩ := hjx
      exact hR _ hj g hr1 hr2
  · rcases List.mem_append.1 hx with hx | hx
    · rcases Replay.brkArmK_mem hx with hx | hx | hx | ⟨j, -, c, c', hj⟩
      · exact absurd hk (giveBack_noBrkSeg dy _ _ hx d g rfl w)
      · exact absurd hk (brkFx_noBrkSeg dy _ _ _ hx d g rfl w)
      · rcases brkDay_cases _ _ _ _ _ _ _ hx with ⟨g', h1, h2, h3⟩ | ⟨r, h1⟩
        · simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          rw [hB]
          rcases prune_keeps (wideOf x (heldOf (d141Machine st.machine x) e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val))))
              _ _ List.mem_cons_self with hk' | hk'
          · exact Or.inl ⟨_, hk', h3, h2.symm, rfl⟩
          · exact Or.inr hk'
        · simp at h1
      · cases hj
    · exact absurd hk (completionArm_noBrkSeg z _ e _ _ _ hx d g rfl w)
  · rcases List.mem_append.1 hxr with hxr | hxr
    · rcases Replay.brkArmK_mem hxr with hxr | hxr | hxr | ⟨j, hj, c, c', hjx⟩
      · exact absurd rfl (Replay.giveBack_noRedraw dy _ _ hxr d kr cr cr')
      · exact absurd rfl (Replay.brkFx_noRedraw dy _ _ _ hxr d kr cr cr')
      · exact absurd rfl (Replay.brkDay_noRedraw _ _ _ _ _ _ _ hxr d kr cr cr')
      · simp only [Effect.dayAdd.injEq, DayOp.redraw.injEq] at hjx; obtain ⟨rfl, rfl, -, -⟩ := hjx
        exact hR _ hj g hr1 hr2
    · exact absurd rfl (Replay.completionArm_noRedraw z _ e _ _ _ hxr d kr cr cr')

/-- **The step**: a Break segment is drawn by a `break` line's own day half alone (`arm_noBrkSeg`, `completionArm_noBrkSeg`), beside the held break `brkFx` pushes with its span and day; every other segment and every other held break moves only by `pruneBrks`, which drops a break only when the newest day it keeps is more than 31 ahead (`prune_keeps`), and that day never falls (`hi_grows`). -/
theorem stepWith_brkHeld (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : BrkHeld st) : BrkHeld (stepWith z dy sl st e) := by
  by_cases h141 : ∃ p a0 w0 x, e.ev = .brk p a0 w0 ∧ (findEnded st.machine (e.t.val, e.off.val) = some x ∨ (findEnded st.machine (e.t.val, e.off.val) = none ∧ st.machine.brkOpen = none ∧ findFin st.machine (e.t.val, e.off.val) p.val = some x)) ∧
      d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a0.map (·.val))) (dy e.t.val) = true
  · obtain ⟨p, a0, w0, x, hev, hK, hg⟩ := h141
    exact stepWith_brkHeld_d141 z dy sl st e h hev hK hg
  intro d a' hget g hg w hk
  have hsrc := applyEffects_seg_src (effectsWith z dy sl st e) st d a' hget g hg
  rcases hsrc with ⟨a, ha, hga⟩ | hx | ⟨kr, cr, cr', hxr, hr1, hr2⟩
  · rcases h d a ha g hga w hk with ⟨k, hkB, h1, h2, h3⟩ | hd
    · rcases stepWith_brks z dy sl st e with hB | ⟨k0, hB⟩ | ⟨k0, x0, hG, -⟩
      · exact Or.inl ⟨k, hB ▸ hkB, h1, h2, h3⟩
      · rw [hB]
        rcases prune_keeps k0 _ k (List.mem_cons_of_mem _ hkB) with hk' | hk'
        · exact Or.inl ⟨k, hk', h1, h2, h3⟩
        · exact Or.inr (h3 ▸ hk')
      · obtain ⟨p, a, w, h1, h2, h3⟩ := hG; exact absurd ⟨p, a, w, x0, h1, h2, h3⟩ h141
    · rcases stepWith_brks z dy sl st e with hB | ⟨k0, hB⟩ | ⟨k0, x0, hG, -⟩
      · exact Or.inr (hB ▸ hd)
      · rw [hB]; exact Or.inr (Nat.lt_of_lt_of_le hd (hi_grows k0 _))
      · obtain ⟨p, a, w, h1, h2, h3⟩ := hG; exact absurd ⟨p, a, w, x0, h1, h2, h3⟩ h141
  · unfold effectsWith at hx
    simp only [List.mem_cons, List.mem_append] at hx
    rcases hx with hx | hx | hx | hx | hx
    · cases hx
    · cases hx
    · cases hx
    · by_cases hb : ∃ p a w, e.ev = .brk p a w
      · obtain ⟨p, a0, w0, hev⟩ := hb; have hn : ∀ x, (findEnded st.machine (e.t.val, e.off.val) = some x ∨ (findEnded st.machine (e.t.val, e.off.val) = none ∧ st.machine.brkOpen = none ∧ findFin st.machine (e.t.val, e.off.val) p.val = some x)) → d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a0.map (·.val))) (dy e.t.val) = false := fun x hx => by cases hc : d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a0.map (·.val))) (dy e.t.val); rfl; exact absurd ⟨p, a0, w0, x, hev, hx, hc⟩ h141
        cases hown' : findEnded st.machine (e.t.val, e.off.val) with
        | some x =>
          have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) = [.machine (letGo x st.machine)] := by
            exact (Replay.arm_brk_of_endable dy sl st.machine e _ _ hev).2.1 x hown' (hn x (Or.inl hown'))
            -- (D147)
          rw [harm] at hx
          simp at hx
        | none =>
        obtain ⟨M, -, harm⟩ : ∃ M : Machine, M.brks = st.machine.brks ∧ arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
            (giveBack dy M).2 ++ brkFx dy (giveBack dy M).1
              (heldOf M e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)))
              ++ brkDay M e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)) ++ reachFx M.brks (heldOf M e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val))) := by
          exact ⟨st.machine, rfl, (Replay.arm_brk_of_endable dy sl st.machine e _ _ hev).2.2 hown' (fun x ho hF => hn x (Or.inr ⟨hown', ho, hF⟩))⟩
          -- (D147)
        rw [harm] at hx
        rcases List.mem_append.1 hx with hx | hx; rotate_right; (obtain ⟨j, -, c, c', hj⟩ := Replay.reachFx_redraw _ _ _ hx; cases hj)
        rcases List.mem_append.1 hx with hx | hx
        · rcases List.mem_append.1 hx with hx | hx
          · exact absurd hk (giveBack_noBrkSeg dy _ _ hx d g rfl w)
          · exact absurd hk (brkFx_noBrkSeg dy _ _ _ hx d g rfl w)
        · -- since the owner's D142 the day half is `brkDay`: a segment begun at or after the line's stamp and ending
          -- where its break ends, so the break `brkFx` holds for the line witnesses it (`brkDay_cases`)
          rcases brkDay_cases _ _ _ _ _ _ _ hx with ⟨g', h1, h2, h3⟩ | ⟨r, h1⟩
          · simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at h1
            obtain ⟨rfl, rfl⟩ := h1
            rw [stepWith_brks_of_brk z dy sl st e hev hown' (fun x ho hF => hn x (Or.inr ⟨hown', ho, hF⟩))]
            rcases prune_keeps (heldOf st.machine e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)))
                st.machine.brks _ List.mem_cons_self with hk' | hk'
            · exact Or.inl ⟨_, hk', h3, h2.symm, rfl⟩
            · exact Or.inr hk'
          · simp at h1
          -- (a record is no segment)
      · by_cases hs : ∃ id pred rep hsw sleptMin loc b1 b2,
            e.ev = .start id pred rep hsw sleptMin loc b1 b2 ∧ ∃ o, endsBrk st.machine (e.t.val, e.off.val) = some o
        · obtain ⟨id, pred, rep, hsw, sleptMin, loc, b1, b2, hev, o, hE⟩ := hs
          have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
              endRecs st.machine.brks o (e.t.val, e.off.val) e.line ++ startArm dy (endMachine st.machine o (e.t.val, e.off.val) e.line) e.line
                (e.t.val, e.off.val) (dy e.t.val) id pred rep hsw sleptMin loc := by
            unfold Replay.arm; simp only [hev, hE]
          rw [harm] at hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨rfl, h1, h2⟩ := endRecs_seg _ o _ _ _ hx d g rfl
            exact held_of_prune _ _ _ (stepWith_brks_of_start z dy sl st e hev hE) _ g h1 h2.symm rfl
          · exact absurd hk (startArm_noBrkSeg dy _ _ _ _ _ _ _ _ _ _ _ hx d g rfl w)
        · by_cases hbs : ∃ p w0, e.ev = .brkStart p w0 ∧ ∃ t0, firstStart (e.t.val, e.off.val) (dy e.t.val) st.machine = some t0
          · obtain ⟨p, w0, hev, t0, hF⟩ := hbs
            have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
                endBrkFx dy st.machine ⟨(e.t.val, e.off.val), p.val, w0, dy e.t.val⟩ t0 e.line := by
              unfold Replay.arm; simp only [hev, hF]
            rw [harm] at hx
            unfold Replay.endBrkFx at hx
            rcases List.mem_append.1 hx with hx | hx
            · exact absurd hk (brkFx_noBrkSeg dy _ _ _ hx d g rfl w)
            · obtain ⟨rfl, h1, h2⟩ := endRecs_seg _ _ t0 _ _ hx d g rfl
              exact held_of_prune _ _ _ (stepWith_brks_of_brkStart z dy sl st e hev hF) _ g h1 h2.symm rfl
          · exact absurd hk (arm_noBrkSeg dy sl _ e _ _ (fun p a w h => hb ⟨p, a, w, h⟩)
              (fun id pred rep hsw sleptMin loc b1 b2 hev => by
                cases hE : endsBrk st.machine (e.t.val, e.off.val) with
                | none => rfl
                | some o => exact absurd ⟨id, pred, rep, hsw, sleptMin, loc, b1, b2, hev, o, hE⟩ hs)
              (fun p w0 hev => by
                cases hF : firstStart (e.t.val, e.off.val) (dy e.t.val) st.machine with
                | none => rfl
                | some t0 => exact absurd ⟨p, w0, hev, t0, hF⟩ hbs) _ hx d g rfl w)
    · exact absurd hk (completionArm_noBrkSeg z _ e _ _ _ hx d g rfl w)
  · -- W-53 track K (README gap 5661): a re-drawing's segment is witnessed by the break it re-draws, which the machine
    -- held before the step — a break the `break` line's arm, or the ending's records, reach back to (`reachFx`)
    unfold effectsWith at hxr
    simp only [List.mem_cons, List.mem_append] at hxr
    rcases hxr with hxr | hxr | hxr | hxr | hxr
    · cases hxr
    · cases hxr
    · cases hxr
    · have hw : ∀ (k0 : HeldBrk) (old : List HeldBrk), (stepWith z dy sl st e).machine.brks = pruneBrks (k0 :: old) →
          ∀ j ∈ old, ∀ c c', Effect.dayAdd d (.redraw kr cr cr') = .dayAdd j.day (.redraw j c c') →
          (∃ k ∈ (stepWith z dy sl st e).machine.brks, k.s.1 ≤ g.start.1 ∧ k.e = g.stop ∧ k.day = d) ∨
            d + 31 < (stepWith z dy sl st e).machine.brks.foldl (fun a k => max a k.day) 0 := by
        intro k0 old hB j hj c c' hjx
        simp only [Effect.dayAdd.injEq, DayOp.redraw.injEq] at hjx; obtain ⟨rfl, rfl, -, -⟩ := hjx
        rw [hB]; rcases prune_keeps k0 old kr (List.mem_cons_of_mem _ hj) with hk' | hk'
        · exact Or.inl ⟨kr, hk', hr1, hr2.symm, rfl⟩
        · exact Or.inr hk'
      by_cases hb : ∃ p a w, e.ev = .brk p a w
      · obtain ⟨p, a0, w0, hev⟩ := hb; have hn : ∀ x, (findEnded st.machine (e.t.val, e.off.val) = some x ∨ (findEnded st.machine (e.t.val, e.off.val) = none ∧ st.machine.brkOpen = none ∧ findFin st.machine (e.t.val, e.off.val) p.val = some x)) → d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a0.map (·.val))) (dy e.t.val) = false := fun x hx => by cases hc : d141Ok st.machine x (brkEnd (e.t.val, e.off.val) p.val (a0.map (·.val))) (dy e.t.val); rfl; exact absurd ⟨p, a0, w0, x, hev, hx, hc⟩ h141
        cases hown' : findEnded st.machine (e.t.val, e.off.val) with
        | some x =>
          have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) = [.machine (letGo x st.machine)] := by
            exact (Replay.arm_brk_of_endable dy sl st.machine e _ _ hev).2.1 x hown' (hn x (Or.inl hown'))
            -- (D147)
          rw [harm] at hxr; simp at hxr
        | none =>
          have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
              brkArm dy st.machine e (e.t.val, e.off.val) (dy e.t.val) p.val (a0.map (·.val)) := by
            exact (Replay.arm_brk_of_endable dy sl st.machine e _ _ hev).2.2 hown' (fun x ho hF => hn x (Or.inr ⟨hown', ho, hF⟩))
          rw [harm] at hxr
          rcases Replay.brkArm_mem hxr with hxr | hxr | hxr | ⟨j, hj, c, c', hjx⟩
          · exact absurd rfl (Replay.giveBack_noRedraw dy _ _ hxr d kr cr cr')
          · exact absurd rfl (Replay.brkFx_noRedraw dy _ _ _ hxr d kr cr cr')
          · exact absurd rfl (Replay.brkDay_noRedraw _ _ _ _ _ _ _ hxr d kr cr cr')
          · exact hw _ _ (stepWith_brks_of_brk z dy sl st e hev hown' (fun x ho hF => hn x (Or.inr ⟨hown', ho, hF⟩))) j hj c c' hjx
      · by_cases hs : ∃ id pred rep hsw sleptMin loc b1 b2,
            e.ev = .start id pred rep hsw sleptMin loc b1 b2 ∧ ∃ o, endsBrk st.machine (e.t.val, e.off.val) = some o
        · obtain ⟨id, pred, rep, hsw, sleptMin, loc, b1, b2, hev, o, hE⟩ := hs
          have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
              endRecs st.machine.brks o (e.t.val, e.off.val) e.line ++ startArm dy (endMachine st.machine o (e.t.val, e.off.val) e.line) e.line
                (e.t.val, e.off.val) (dy e.t.val) id pred rep hsw sleptMin loc := by
            unfold Replay.arm; simp only [hev, hE]
          rw [harm] at hxr
          rcases List.mem_append.1 hxr with hxr | hxr
          · rcases Replay.endRecs_cases _ _ _ _ _ hxr with ⟨g', h1, -⟩ | ⟨r, h1⟩ | ⟨j, hj, c, c', hjx⟩
            · cases h1
            · cases h1
            · exact hw _ _ (stepWith_brks_of_start z dy sl st e hev hE) j hj c c' hjx
          · exact absurd rfl (Replay.startArm_noRedraw dy _ _ _ _ _ _ _ _ _ _ _ hxr d kr cr cr')
        · by_cases hbs : ∃ p w0, e.ev = .brkStart p w0 ∧ ∃ t0, firstStart (e.t.val, e.off.val) (dy e.t.val) st.machine = some t0
          · obtain ⟨p, w0, hev, t0, hF⟩ := hbs
            have harm : arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) =
                endBrkFx dy st.machine ⟨(e.t.val, e.off.val), p.val, w0, dy e.t.val⟩ t0 e.line := by
              unfold Replay.arm; simp only [hev, hF]
            rw [harm] at hxr
            unfold Replay.endBrkFx at hxr
            rcases List.mem_append.1 hxr with hxr | hxr
            · exact absurd rfl (Replay.brkFx_noRedraw dy _ _ _ hxr d kr cr cr')
            · rcases Replay.endRecs_cases _ _ _ _ _ hxr with ⟨g', h1, -⟩ | ⟨r, h1⟩ | ⟨j, hj, c, c', hjx⟩
              · cases h1
              · cases h1
              · exact hw _ _ (stepWith_brks_of_brkStart z dy sl st e hev hF) j hj c c' hjx
          · exact absurd rfl (Replay.arm_noRedraw dy sl _ e _ _ (fun p a w h => hb ⟨p, a, w, h⟩)
              (fun id pred rep hsw sleptMin loc b1 b2 hev => by
                cases hE : endsBrk st.machine (e.t.val, e.off.val) with
                | none => rfl
                | some o => exact absurd ⟨id, pred, rep, hsw, sleptMin, loc, b1, b2, hev, o, hE⟩ hs)
              (fun p w0 hev => by
                cases hF : firstStart (e.t.val, e.off.val) (dy e.t.val) st.machine with
                | none => rfl
                | some t0 => exact absurd ⟨p, w0, hev, t0, hF⟩ hbs) _ hxr d kr cr cr')
    · exact absurd rfl (Replay.completionArm_noRedraw z _ e _ _ _ hxr d kr cr cr')



/-- **The fold keeps it.** -/
theorem foldl_brkHeld (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State), BrkHeld st → BrkHeld (sv.foldl (stepWith z dy sl) st)
  | [], _, h => h
  | e :: sv, st, h => foldl_brkHeld z dy sl sv _ (stepWith_brkHeld z dy sl st e h)

/-! ## Over the runs `Seal.resumeRun` builds -/

/-- **The empty checkpoint restores a state holding both**: no block, no day. -/
theorem restore_empty_holds (z : Cal.Tz) (n : Nat) :
    OpenAfter (Seal.restore (Seal.Ckpt.empty z) n).machine ∧ BrkHeld (Seal.restore (Seal.Ckpt.empty z) n) := by
  refine ⟨openAfter_of_no_block rfl, ?_⟩
  intro d a h
  simp [Seal.restore, Seal.Ckpt.empty, Replay.HMap.get_empty] at h

/-- **A resumed run's state holds both invariants** when the state its checkpoint restores does — every run from the
empty checkpoint (`restore_empty_holds`), which is the genesis run. -/
theorem resumeRun_holds (z : Cal.Tz) (T : Nat) (K : Seal.Ckpt) (b : List Log.Line) (run : Seal.Run)
    (h : Seal.resumeRun z T K b = .ok run)
    (hK : ∀ n, OpenAfter (Seal.restore K n).machine ∧ BrkHeld (Seal.restore K n)) :
    OpenAfter run.state.machine ∧ BrkHeld run.state := by
  obtain ⟨-, -, -, -, -, -, hrun⟩ := Seal.resumeRun_ok z T K b run h
  rw [hrun]
  obtain ⟨h1, h2⟩ := hK (K.items.length + K.openDays.length + (Log.lineEntries b).length)
  exact ⟨foldl_openAfter _ _ _ _ _ h1, foldl_brkHeld _ _ _ _ _ h2⟩

/-- A finished day keeps its segments, reordered. -/
theorem finish_segments (a : DayAcc) (g : Segment) (h : g ∈ a.finish.segments) : g ∈ a.segments := by
  unfold DayAcc.finish sortSegs at h
  exact List.mem_reverse.1 ((Replay.insSort_perm segLe _).mem_iff.1 h)

/-- **A day record of a resumed answer is the state's day, finished.** -/
theorem resumedAnswer_day_src (K : Seal.Ckpt) (st : State) (hs : List (Nat × HeaderRec)) (n : Nat)
    (ws : List (Nat × Log.LWarn)) (rec : Seal.DayRecord) (hrec : rec ∈ (Seal.resumedAnswer K st hs n ws).days)
    (acc : DayAcc) (hacc : rec.record = some acc) (g : Segment) (hg : g ∈ acc.segments) :
    ∃ a, st.days.get rec.day = some a ∧ g ∈ a.segments := by
  simp only [Seal.resumedAnswer, Seal.daysFrom, List.map_map, List.mem_map, List.mem_filter] at hrec
  obtain ⟨d, -, rfl⟩ := hrec
  simp only [Function.comp, Seal.OpenDay.finish, Seal.openDayOf, Option.map_eq_some_iff] at hacc ⊢
  obtain ⟨a, ha, rfl⟩ := hacc
  exact ⟨a, ha, finish_segments a g hg⟩

/-- **`hopen` over a resumed run, with its two bounds named** (W-49 track Q, README gap 5181): the open block's clock
runs from at or after the end of every nonempty Break segment of every day record of the answer — unless that day is
before the open block's own ledger day (a clock behind the log: the owner's D94 nets a break on a block's ledger days
alone, `spansFor`), or more than 31 ledger days behind the newest break the machine holds (`pruneBrks`, README gap
4914). -/
theorem the_resumed_open_block_runs_after_every_break (z : Cal.Tz) (T : Nat) (K : Seal.Ckpt) (b : List Log.Line)
    (run : Seal.Run) (h : Seal.resumeRun z T K b = .ok run)
    (hK : ∀ n, OpenAfter (Seal.restore K n).machine ∧ BrkHeld (Seal.restore K n)) :
    ∀ ob ∈ run.answer.openBlock.toList, ∀ s ∈ ob.since.toList, ∀ rec ∈ run.answer.days, ∀ acc ∈ rec.record.toList,
      ∀ g ∈ acc.segments, ∀ w, g.kind = .brk w → g.start.1 < g.stop.1 →
        g.stop.1 ≤ s.1 ∨ rec.day < ob.day ∨ rec.day + 31 < run.state.machine.brks.foldl (fun a k => max a k.day) 0 := by
  obtain ⟨hOA, hBH⟩ := resumeRun_holds z T K b run h hK
  obtain ⟨-, -, -, -, -, -, hrun⟩ := Seal.resumeRun_ok z T K b run h
  intro ob hob s hs rec hrec acc hacc g hg w hk hlt
  have hans : run.answer = Seal.resumedAnswer K run.state run.headers (Log.lineEntries b).length
      (Log.lineWarnings b) := by rw [hrun]
  rw [hans] at hob hrec
  cases hbk : run.state.machine.block with
  | none => simp [Seal.resumedAnswer, Replay.openOf, hbk] at hob
  | some bk =>
    simp only [Seal.resumedAnswer, Replay.openOf, hbk, Option.map_some, Option.toList_some,
      List.mem_singleton] at hob
    subst hob
    obtain ⟨a, ha, hga⟩ := resumedAnswer_day_src K run.state run.headers _ _ rec hrec acc
      (by simpa using hacc) g hg
    rcases hBH rec.day a ha g hga w hk with ⟨k, hkB, h1, h2, h3⟩ | hd
    · by_cases hday : bk.day ≤ rec.day
      · left
        have hmem : (k.s, k.e) ∈ blockSpans bk run.state.machine := by
          unfold blockSpans spansFor
          exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_filter.2 ⟨hkB, by
            simp only [decide_eq_true_eq]; omega⟩, rfl⟩)
        have := hOA bk hbk s (by simpa using hs) (k.s, k.e) hmem (by
          show k.s.1 < k.e.1
          rw [h2]; rw [Cal.Instant.le_iff] at h1; rw [Cal.Instant.lt_iff] at hlt ⊢; omega)
        rw [← h2]; exact this
      · exact Or.inr (Or.inl (by simp only; omega))
    · exact Or.inr (Or.inr hd)

/-- **On a genesis run** — the run from the empty checkpoint — the restored state holds both invariants. -/
theorem the_genesis_restore_holds (z : Cal.Tz) :
    ∀ n, OpenAfter (Seal.restore (Seal.Ckpt.empty z) n).machine ∧ BrkHeld (Seal.restore (Seal.Ckpt.empty z) n) :=
  restore_empty_holds z

/-! ## D129's refutations (stage 6, W-50 track K; README gap 5430) -/

/-- **"An arm draws a Break segment only for a `break` line", as W-49 track Q stated it, refuted by D129**: a break
running since 08:00 and a `start a` at 08:30 — the start ends the break and draws its segment `[08:00, 08:30)`, as the
`break` line `tm start` logs on one machine would (D97).  `arm_noBrkSeg` is restated with D129's two cases. -/
theorem arm_noBrkSeg_as_w49_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat),
      (∀ p a w, e.ev ≠ .brk p a w) → NoBrkSeg (arm dy sl m e t d) := by
  intro h
  let M : Machine := ⟨none, none, none, [], some ⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), 20, none, 739865⟩, [], []⟩
  let E : Entry := Replay.bE 2 63924366600 (Replay.bStart ['a'])
  let T : At := (⟨63924366600, 0⟩, ⟨false, 0⟩)
  have hm : Effect.dayAdd 739865 (.segment ⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), T, .brk none⟩) ∈
      arm (fun _ => 739865) (fun _ => none) M E T 739865 := by decide
  exact h (fun _ => 739865) (fun _ => none) M E T 739865 (by intro p a w hh; simp [E, Replay.bE, Replay.bStart] at hh)
    _ hm _ _ rfl none rfl

/-- **"A `break` line's step holds its break", as W-49 track Q stated it, refuted by D129**: the `break` line a start
already ended its break for (`Machine.ended` holds the ending, `findEnded`) holds nothing new — the break is held once, as the start
held it.  `stepWith_brks_of_brk` is restated for a line that is not that one. -/
theorem stepWith_brks_of_brk_as_w49_stated_it_is_refuted :
    ¬ ∀ (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) (p : Log.U32)
      (a : Option Log.U32) (w : Option (List Char)), e.ev = .brk p a w →
        (stepWith z dy sl st e).machine.brks =
          pruneBrks (heldOf st.machine e (e.t.val, e.off.val) (dy e.t.val) p.val (a.map (·.val)) ::
            st.machine.brks) := by
  intro h
  let st : State := { Replay.State.init 1 with
    machine := ⟨none, none, none, [], none, [], [⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), (⟨63924364800, 0⟩, ⟨false, 0⟩), 739865, 0, 20, none, (⟨63924364800, 0⟩, ⟨false, 0⟩)⟩]⟩ }
  have := congrArg List.length (h Replay.utcZone (fun _ => 739865) (fun _ => none) st
    (Replay.bE 4 63924364800 (.brk 20 (some 90) none)) 20 (some 90) none rfl)
  revert this
  decide

end BreakFold
end Tm
