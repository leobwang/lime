import TmKernel.SealPending
/-!
# SealCutMachine — a fold's machine days are its start's or its entries' days (stage 5, D9, W2: law 6)

The days a machine can still write (`machineDays`: its pending start observation's, its last cut's and its open
interruption's) are, after a step, the step's start state's or the step's own day (`stepWith_machineDays`), so a fold's
are its start state's or one of its entries' days (`foldl_machineDays`).  The reseal's ledger day reads them.
Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect)
open Log (Entry)

theorem closePause_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    (Replay.closePause dy m t).1.lastCut = m.lastCut ∧ (Replay.closePause dy m t).1.interrupt = m.interrupt :=
  Replay.closePause_lastCut dy m t

theorem cut_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    (Replay.cut dy m t).1.interrupt = m.interrupt ∧
    ((Replay.cut dy m t).1.lastCut = m.lastCut ∨ ∃ c, (Replay.cut dy m t).1.lastCut = some c ∧ c.day = dy t.1) := by
  unfold Replay.cut
  split
  · exact ⟨rfl, Or.inr ⟨_, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inl rfl⟩

/-- **The machine an arm writes that settles its block** (the owner's D99): one of the arm's own, settled — so a
field `settle` keeps (`Replay.settle_keeps`) is that machine's.  Each arm below reads it through this shape. -/
theorem arm_settled_lastCut (dy : Cal.Instant → Nat) (M : Machine) : (Replay.settle dy M).1.lastCut = M.lastCut :=
  (Replay.settle_keeps dy M).1

theorem arm_settled_interrupt (dy : Cal.Instant → Nat) (M : Machine) :
    (Replay.settle dy M).1.interrupt = M.interrupt := (Replay.settle_keeps dy M).2.1

theorem arm_settled_brkOpen (dy : Cal.Instant → Nat) (M : Machine) :
    (Replay.settle dy M).1.brkOpen = M.brkOpen := (Replay.settle_keeps dy M).2.2.2.1

/-- **A netting keeps the last cut's day** (the owner's D100; D119 nets at a `resume`): `Replay.netClosed_keeps`, read
on the day. -/
theorem netClosed_lastCut_day (dy : Cal.Instant → Nat) (s e : Replay.At) (dd : Nat) (m : Machine) :
    (Replay.netClosed dy s e dd m).1.lastCut.map (·.day) = m.lastCut.map (·.day) := by
  have h := congrArg (Option.map (fun x => x.2.2)) (Replay.netClosed_keeps dy s e dd m).2.2.2.2
  simp only [Option.map_map, Function.comp_def] at h
  exact h

/-- **The running break's netting keeps the last cut's day** (README gap 5180): `Replay.runNet_keeps`, read on the day. -/
theorem runNet_lastCut_day (dy : Cal.Instant → Nat) (M : Machine) :
    (Replay.runNet dy M).1.lastCut.map (·.day) = M.lastCut.map (·.day) := by
  have h := congrArg (Option.map (fun x => x.2.2)) (Replay.runNet_keeps dy M).2.2.2.2
  simp only [Option.map_map, Function.comp_def] at h
  exact h

/-- **What `arm_lastCut` concludes of a machine, it concludes of the running break's netting of it** (README gap
5180): the netting keeps whether a cut stands and its day. -/
theorem runNet_lastCut_cases (dy : Cal.Instant → Nat) (M m : Machine) (D : Nat)
    (h : M.lastCut.map (·.day) = m.lastCut.map (·.day) ∨ M.lastCut = none ∨ ∃ c, M.lastCut = some c ∧ c.day = D) :
    (Replay.runNet dy M).1.lastCut.map (·.day) = m.lastCut.map (·.day) ∨ (Replay.runNet dy M).1.lastCut = none ∨
      ∃ c, (Replay.runNet dy M).1.lastCut = some c ∧ c.day = D := by
  have hd := runNet_lastCut_day dy M
  rcases h with h | h | ⟨c, hc, hcd⟩
  · exact Or.inl (hd.trans h)
  · rw [h] at hd
    exact Or.inr (Or.inl (Option.map_eq_none_iff.1 hd))
  · rw [hc] at hd
    obtain ⟨c', hc', hcd'⟩ := Option.map_eq_some_iff.1 hd
    exact Or.inr (Or.inr ⟨c', hc', hcd'.trans hcd⟩)

/-- **An arm's machine keeps the last cut's day, drops the cut, or cuts on the arm's stamp's day** — restated at the owner's
D100 (README gap 4520b) from "keeps the last cut": a break logged after a cut and stamped inside its block takes its
minutes down (`Replay.netClosed`), and keeps its block, its stamp and its day (`Replay.brkFx_machine`); the day is what
the machine's days read (`stepWith_machineDays`). -/
theorem arm_lastCut (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.lastCut.map (·.day) = m.lastCut.map (·.day) ∨ m'.lastCut = none ∨ ∃ c, m'.lastCut = some c ∧ c.day = dy t.1 := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    have hS : ∀ M, ∀ m' ∈ (Replay.startArm dy M e.line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?,
        m'.lastCut = none := by
      intro M m' hm
      rw [Replay.startArm_machines] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      exact arm_settled_lastCut dy _
    split at hm
    · rename_i o _
      have hm := Replay.startEnds_mem dy m o _ t d _ _ _ _ _ _ m' hm
      exact Or.inr (Or.inl ((hS (Replay.endMachine m o t e.line) m' hm).trans rfl))
    · exact Or.inr (Or.inl (hS m m' hm))
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl (congrArg (Option.map (·.day)) (arm_settled_lastCut dy _))
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl (by rw [arm_settled_lastCut]; exact congrArg (Option.map (·.day)) (Replay.closePauseM_keeps m t).1)
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    left
    rw [arm_settled_lastCut]
    have h1 := congrArg (Option.map (·.day)) (Replay.closePauseM_keeps m t).1
    unfold Replay.interruptMachine
    split
    · exact h1
    · exact h1
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton, (Replay.netClosed_obs dy _ _ _ _).2.2] at hm
      subst hm
      left
      rw [netClosed_lastCut_day]
      exact congrArg (Option.map (·.day)) (arm_settled_lastCut dy _)
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl (congrArg (Option.map (·.day)) (arm_settled_lastCut dy _))
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact runNet_lastCut_cases dy _ m (dy t.1) (by
          rcases (cut_keeps dy m t).2 with h | h
          · exact Or.inl (congrArg (Option.map (·.day)) h)
          · exact Or.inr (Or.inr h))
      · simp at hm
    · simp at hm
  case extend id by_ =>
    -- D108: the open block's `ext` grown, nothing else of the machine.
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, -, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    exact Or.inl rfl
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    refine runNet_lastCut_cases dy _ m (dy t.1) ?_
    show (Replay.doneClose dy m t id actual.val went).1.lastCut.map (·.day) = _ ∨
      (Replay.doneClose dy m t id actual.val went).1.lastCut = none ∨ _
    unfold Replay.doneClose
    split
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · split
      · split
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · exact Or.inl rfl
  case brk p a w =>
    have hbk : ∀ (M : Machine) (k0 : Replay.HeldBrk), m' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k0).filterMap Effect.machineOf? → m' ∈ (Replay.brkFx dy (Replay.giveBack dy M).1 k0).filterMap Effect.machineOf? := fun M k0 hm => by
      unfold Replay.brkArmK at hm; rwa [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil, List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm
    have hcase : (∃ x0, m' ∈ (Replay.d141Arm dy m x0 e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) ∨ m' ∈ (Replay.brkArm dy m e t d p.val (a.map (·.val))).filterMap Effect.machineOf? := by split at hm; (rcases Replay.brkOwn_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm); (rcases Replay.brkLine_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm)
    rcases hcase with ⟨x0, hm⟩ | hm
    · unfold Replay.d141Arm at hm; split at hm  -- that break let go — its last cut, interruption and running break the old one's
      · simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.durationOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.energyOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm
        have h := congrArg (Option.map (fun x => x.2.2)) (Replay.giveBack_brkFx_machine dy _ _ m' (hbk _ _ hm)).1; simp only [Option.map_map, Function.comp_def] at h; exact Or.inl h
      · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; exact Or.inl rfl
    · have h := congrArg (Option.map (fun x => x.2.2)) (Replay.giveBack_brkFx_machine dy m _ m' (hbk _ _ hm)).1; simp only [Option.map_map, Function.comp_def] at h; exact Or.inl h
  case brkStart pl w =>
    split at hm
    · rename_i t0 _
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      have h := congrArg (Option.map (fun x => x.2.2))
        (Replay.brkFx_machine dy { Replay.forget m with ended := Replay.pushEnded (Replay.endingOf ⟨t, pl.val, w, d⟩ t0 e.line) m } ⟨t, t0, d, e.line, pl.val, w, t0⟩ m' hm').1
      simp only [Option.map_map, Function.comp_def] at h
      exact Or.inl h
    · unfold Replay.brkStartArm at hm
      simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl (((runNet_lastCut_day dy _).trans (congrArg (Option.map (·.day)) (arm_settled_lastCut dy _))).trans (congrArg (Option.map (·.day)) (Replay.forgetIdle_keeps m).2.1))
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **An arm's machine keeps the open interruption, closes it, or opens one on the arm's day.** -/
theorem arm_interrupt (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.interrupt = m.interrupt ∨ m'.interrupt = none ∨ ∃ i, m'.interrupt = some i ∧ i.2.1 = d := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    have hS : ∀ M, ∀ m' ∈ (Replay.startArm dy M e.line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?,
        m'.interrupt = M.interrupt := by
      intro M m' hm
      rw [Replay.startArm_machines] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      rw [arm_settled_interrupt]
      exact (Replay.runNet_keeps dy _).2.1.trans ((cut_interrupt dy _ t).trans (Replay.netStart_keeps dy _ _ M).2.1)
    split at hm
    · rename_i o _
      have hm := Replay.startEnds_mem dy m o _ t d _ _ _ _ _ _ m' hm
      exact Or.inl ((hS (Replay.endMachine m o t e.line) m' hm).trans rfl)
    · exact Or.inl (hS m m' hm)
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl (arm_settled_interrupt dy _)
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl ((arm_settled_interrupt dy _).trans (Replay.closePauseM_keeps m t).2.1)
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    rw [arm_settled_interrupt]
    have h1 := (Replay.closePauseM_keeps m t).2.1
    unfold Replay.interruptMachine
    split
    · exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)
    · exact Or.inl h1
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton, (Replay.netClosed_obs dy _ _ _ _).2.2] at hm
      subst hm
      right; left
      rw [(Replay.netClosed_keeps dy _ _ _ _).2.1]
      exact arm_settled_interrupt dy _
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl (arm_settled_interrupt dy _)
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl ((Replay.runNet_keeps dy _).2.1.trans (cut_keeps dy m t).1)
      · simp at hm
    · simp at hm
  case extend id by_ =>
    -- D108: the open block's `ext` grown, nothing else of the machine.
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, -, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    exact Or.inl rfl
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    rw [(Replay.runNet_keeps dy _).2.1]
    show (Replay.doneClose dy m t id actual.val went).1.interrupt = _ ∨ _
    unfold Replay.doneClose
    split
    · split
      · exact Or.inl rfl
      · exact Or.inl rfl
    · split
      · split
        · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
  case brk p a w =>
    have hbk : ∀ (M : Machine) (k0 : Replay.HeldBrk), m' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k0).filterMap Effect.machineOf? → m' ∈ (Replay.brkFx dy (Replay.giveBack dy M).1 k0).filterMap Effect.machineOf? := fun M k0 hm => by
      unfold Replay.brkArmK at hm; rwa [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil, List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm
    have hcase : (∃ x0, m' ∈ (Replay.d141Arm dy m x0 e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) ∨ m' ∈ (Replay.brkArm dy m e t d p.val (a.map (·.val))).filterMap Effect.machineOf? := by split at hm; (rcases Replay.brkOwn_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm); (rcases Replay.brkLine_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm)
    rcases hcase with ⟨x0, hm⟩ | hm
    · unfold Replay.d141Arm at hm; split at hm  -- that break let go — its last cut, interruption and running break the old one's
      · simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.durationOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.energyOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm
        exact Or.inl (Replay.giveBack_brkFx_machine dy _ _ m' (hbk _ _ hm)).2.1
      · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; exact Or.inl rfl
    · exact Or.inl (Replay.giveBack_brkFx_machine dy m _ m' (hbk _ _ hm)).2.1
  case brkStart pl w =>
    split at hm
    · rename_i t0 _
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      exact Or.inl (Replay.brkFx_machine dy { Replay.forget m with ended := Replay.pushEnded (Replay.endingOf ⟨t, pl.val, w, d⟩ t0 e.line) m } ⟨t, t0, d, e.line, pl.val, w, t0⟩ m' hm').2.1
    · unfold Replay.brkStartArm at hm
      simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl (((Replay.runNet_keeps dy _).2.1.trans (arm_settled_interrupt dy _)).trans (Replay.forgetIdle_keeps m).2.2.1)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **An arm's machine keeps the running break, ends it, or opens one on the arm's day** (the owner's D105, parity
P100): a `break_start` opens it on its own day, a `break` line ends it (`Replay.brkFx_brkOpen`), and every other arm
keeps it (`Replay.cut_brkOpen`, `Replay.settle_keeps`, `Replay.closePauseM_keeps`, `Replay.doneClose_brkOpen`). -/
theorem arm_brkOpen (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.brkOpen = m.brkOpen ∨ m'.brkOpen = none ∨ ∃ b, m'.brkOpen = some b ∧ b.day = d := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    have hS : ∀ M, ∀ m' ∈ (Replay.startArm dy M e.line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?,
        m'.brkOpen = M.brkOpen := by
      intro M m' hm
      rw [Replay.startArm_machines] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      rw [arm_settled_brkOpen]
      exact (Replay.runNet_keeps dy _).2.2.2.1.trans ((Replay.cut_brkOpen dy _ t).trans
        (Replay.netStart_keeps dy _ _ M).2.2.2.1)
    split at hm
    · rename_i o _
      have hm := Replay.startEnds_mem dy m o _ t d _ _ _ _ _ _ m' hm
      exact Or.inr (Or.inl ((hS (Replay.endMachine m o t e.line) m' hm).trans rfl))
    · exact Or.inl (hS m m' hm)
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl (arm_settled_brkOpen dy _)
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl ((arm_settled_brkOpen dy _).trans (Replay.closePauseM_keeps m t).2.2.2)
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    left
    rw [arm_settled_brkOpen]
    have h1 := (Replay.closePauseM_keeps m t).2.2.2
    unfold Replay.interruptMachine
    split
    · exact h1
    · exact h1
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton, (Replay.netClosed_obs dy _ _ _ _).2.2] at hm
      subst hm
      left
      rw [(Replay.netClosed_keeps dy _ _ _ _).2.2.2.1]
      exact arm_settled_brkOpen dy _
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl (arm_settled_brkOpen dy _)
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl ((Replay.runNet_keeps dy _).2.2.2.1.trans (Replay.cut_brkOpen dy m t))
      · simp at hm
    · simp at hm
  case extend id by_ =>
    -- D108: the open block's `ext` grown, nothing else of the machine.
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, -, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    exact Or.inl rfl
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    exact Or.inl ((Replay.runNet_keeps dy _).2.2.2.1.trans (Replay.doneClose_brkOpen dy m t id actual.val went))
  case brk p a w =>
    have hbk : ∀ (M : Machine) (k0 : Replay.HeldBrk), m' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k0).filterMap Effect.machineOf? → m' ∈ (Replay.brkFx dy (Replay.giveBack dy M).1 k0).filterMap Effect.machineOf? := fun M k0 hm => by
      unfold Replay.brkArmK at hm; rwa [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil, List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm
    have hcase : (∃ x0, m' ∈ (Replay.d141Arm dy m x0 e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) ∨ m' ∈ (Replay.brkArm dy m e t d p.val (a.map (·.val))).filterMap Effect.machineOf? := by split at hm; (rcases Replay.brkOwn_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm); (rcases Replay.brkLine_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm)
    rcases hcase with ⟨x0, hm⟩ | hm
    · unfold Replay.d141Arm at hm; split at hm  -- that break let go — its last cut, interruption and running break the old one's
      · simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.durationOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.energyOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm
        exact Or.inr (Or.inl (Replay.brkFx_brkOpen dy _ _ m' (hbk _ _ hm)))
      · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; exact Or.inl rfl
    · exact Or.inr (Or.inl (Replay.brkFx_brkOpen dy _ _ m' (hbk _ _ hm)))
  case brkStart pl w =>
    split at hm
    · rename_i t0 _
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      exact Or.inr (Or.inl (Replay.brkFx_brkOpen dy { Replay.forget m with ended := Replay.pushEnded (Replay.endingOf ⟨t, pl.val, w, d⟩ t0 e.line) m } ⟨t, t0, d, e.line, pl.val, w, t0⟩ m' hm'))
    · unfold Replay.brkStartArm at hm
      simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inr (Or.inr ⟨_, (Replay.runNet_keeps dy _).2.2.2.1.trans (arm_settled_brkOpen dy _), rfl⟩)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

theorem stepWith_machine_eq (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (Replay.stepWith z dy sl st e).machine
      = (((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast?).getD
          st.machine := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z st.machine e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  unfold Replay.stepWith
  rw [h3, hfx]

/-- **A step's machine days are its start state's or the step's day.** -/
theorem stepWith_machineDays (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (x : Nat) (hx : x ∈ machineDays (Replay.stepWith z dy sl st e).machine) :
    x ∈ machineDays st.machine ∨ x = dy e.t.val := by
  rw [stepWith_machine_eq] at hx
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => rw [hl] at hx; exact Or.inl hx
  | some m' =>
    rw [hl, Option.getD_some] at hx
    have hm := List.mem_of_getLast? hl
    unfold machineDays at hx ⊢
    simp only [List.mem_append, Option.mem_toList, Option.mem_def, Option.map_eq_some_iff] at hx ⊢
    rcases hx with ((⟨o, ho, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨i, hi, rfl⟩) | ⟨b, hb, rfl⟩
    · rcases arm_pending dy sl st.machine e _ _ m' hm with h | h | ⟨o', h, hd⟩
      · rw [h] at ho; exact Or.inl (Or.inl (Or.inl (Or.inl ⟨o, ho, rfl⟩)))
      · rw [h] at ho; cases ho
      · rw [h] at ho; cases ho; exact Or.inr hd
    · rcases arm_lastCut dy sl st.machine e _ _ m' hm with h | h | ⟨c', h, hd⟩
      · rw [hc] at h
        cases hm0 : st.machine.lastCut with
        | none => rw [hm0] at h; cases h
        | some c0 =>
          rw [hm0] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c0, rfl, h.symm⟩)))
      · rw [h] at hc; cases hc
      · rw [h] at hc; cases hc; exact Or.inr hd
    · rcases arm_interrupt dy sl st.machine e _ _ m' hm with h | h | ⟨i', h, hd⟩
      · rw [h] at hi; exact Or.inl (Or.inl (Or.inr ⟨i, hi, rfl⟩))
      · rw [h] at hi; cases hi
      · rw [h] at hi; cases hi; exact Or.inr hd
    · rcases arm_brkOpen dy sl st.machine e _ _ m' hm with h | h | ⟨b', h, hd⟩
      · rw [h] at hb; exact Or.inl (Or.inr ⟨b, hb, rfl⟩)
      · rw [h] at hb; cases hb
      · rw [h] at hb; cases hb; exact Or.inr hd

/-- **A fold's machine days are its start state's or one of its entries' days.** -/
theorem foldl_machineDays (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (x : Nat), x ∈ machineDays (sv.foldl (Replay.stepWith z dy sl) st).machine →
      x ∈ machineDays st.machine ∨ ∃ e ∈ sv, x = dy e.t.val
  | [], _, _, h => Or.inl h
  | e :: sv, st, x, h => by
    rw [List.foldl_cons] at h
    rcases foldl_machineDays z dy sl sv _ x h with h' | ⟨e', he', hd⟩
    · rcases stepWith_machineDays z dy sl st e x h' with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨e, List.mem_cons_self, h1⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd⟩

end Seal
end Tm
