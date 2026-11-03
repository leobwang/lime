import TmKernel.SealStep
/-!
# SealPending — a step's pending start observation is the old one, none, or on the step's day (stage 5, D9, W2)

Law 4 reads a day record below the ledger day through `OpenDay.finish`, which emits the machine's pending start
observation on its day.  A step keeps the open block's observation, closes it, or opens one on its own day
(`arm_pending`), so a fold's pending observation is its start state's or on one of its entries' days
(`foldl_pending`).  Specification only (D9-21).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect)
open Log (Entry)

theorem pending_none_of_pendLines (m : Machine) (h : Replay.pendLines m = []) : m.block.bind (·.obs) = none := by
  unfold Replay.pendLines at h
  cases hb : m.block.bind (·.obs) with
  | none => rfl
  | some o => rw [hb] at h; simp at h

/-- **An arm's machine keeps the pending observation, drops it, or holds one on the arm's day.** -/
theorem arm_pending (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.block.bind (·.obs) = m.block.bind (·.obs) ∨ m'.block.bind (·.obs) = none ∨
      ∃ o, m'.block.bind (·.obs) = some o ∧ o.day = d := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    have hS : ∀ M, ∀ m' ∈ (Replay.startArm dy M e.line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?,
        m'.block.bind (·.obs) = none ∨ ∃ o, m'.block.bind (·.obs) = some o ∧ o.day = d := by
      intro M m' hm
      rw [Replay.startArm_machines] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      rw [Replay.settle_obs]
      cases rep with
      | none => left; rfl
      | some rp => right; exact ⟨_, rfl, rfl⟩
    split at hm
    · rename_i o _
      have hm := Replay.startEnds_mem dy m o _ t d _ _ _ _ _ _ m' hm
      exact Or.inr (hS _ m' hm)
    · exact Or.inr (hS m m' hm)
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        left
        rw [Replay.settle_obs]
        rename_i b hb _
        simp [hb]
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        left
        rw [Replay.settle_obs, ← Replay.closePauseM_pending m t]
        cases (Replay.closePauseM m t).block <;> rfl
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    left
    rw [Replay.settle_obs]
    have h1 := Replay.closePauseM_pending m t
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
      rw [(Replay.netClosed_keeps dy _ _ _ _).1, Replay.settle_obs]
      show (m.block.map (fun b => Replay.resumeBlock b _ t)).bind (·.obs) = m.block.bind (·.obs)
      cases m.block with
      | none => rfl
      | some b => exact Replay.resumeBlock_obs b _ t
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      left
      rw [Replay.settle_obs]
      show (m.block.map (fun b => Replay.resumeBlock b _ t)).bind (·.obs) = m.block.bind (·.obs)
      cases m.block with
      | none => rfl
      | some b => exact Replay.resumeBlock_obs b _ t
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        rw [(Replay.runNet_keeps dy _).1]
        exact Or.inr (Or.inl (pending_none_of_pendLines _ (Replay.cut_obs dy m t).2.2.2))
      · simp at hm
    · simp at hm
  case extend id by_ =>
    -- D108: the open block's `ext` grown, its pending observation untouched.
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, hb, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    left
    simp [hb]
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    rw [(Replay.runNet_keeps dy _).1]
    show (Replay.doneClose dy m t id actual.val went).1.block.bind (·.obs) = _ ∨
      (Replay.doneClose dy m t id actual.val went).1.block.bind (·.obs) = none ∨ _
    unfold Replay.doneClose
    split
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · split
      · split
        · exact Or.inl rfl
        · exact Or.inl rfl
      · exact Or.inl rfl
  case brk p a w =>
    have hbk : ∀ (m'' M : Machine) (k0 : Replay.HeldBrk), M.block = m.block → m'' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k0).filterMap Effect.machineOf? → m''.block.bind (·.obs) = m.block.bind (·.obs) := fun m'' M k0 hM hm => by
      unfold Replay.brkArmK at hm
      rw [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil,
        List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm
      have h := (Replay.brkFx_machine dy _ _ m'' hm).2.2
      rw [(Replay.giveBack_keeps dy M).1, hM] at h
      exact h
    have hDA : ∀ (M m'' : Machine), M.block = m.block → ((∃ x0, m'' ∈ (Replay.d141Arm dy M x0 e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) ∨ m'' ∈ (Replay.brkArm dy M e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) → m''.block.bind (·.obs) = m.block.bind (·.obs) := fun M m'' hM hc => by
      rcases hc with ⟨x0, hm⟩ | hm
      · -- D141 (and D147's finished break): the undoing writes no machine; then a `break` line's arm over the machine with that break let go
        unfold Replay.d141Arm at hm; split at hm
        · simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.durationOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.energyOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm
          exact hbk _ (Replay.d141Machine M x0) _ hM hm
        · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; show M.block.bind (·.obs) = _; rw [hM]
      · exact hbk _ _ _ hM hm
    have hLn : ∀ (M m'' : Machine), M.block = m.block → m'' ∈ (Replay.brkLine dy M e t d p.val (a.map (·.val))).filterMap Effect.machineOf? → m''.block.bind (·.obs) = m.block.bind (·.obs) := fun M m'' hM hm => hDA M m'' hM (by rcases Replay.brkLine_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm)
    replace hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf? := by unfold Replay.arm; simp only [hev]; exact hm
    rcases Replay.arm_brk_eq dy sl m e t d hev with ⟨o, -, -, he⟩ | ⟨o, -, -, he⟩ | ⟨-, he⟩ <;> rw [he] at hm
    · exact Or.inl (hDA m m' rfl (by rcases Replay.brkOwn_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm))
    · -- the owner's D145: the parked reading, over the parked machine (its block the old one), then the running break opened again
      have hpk : (Replay.parkM dy m).block = m.block := (Replay.giveBack_keeps dy m).1
      have hM : ∀ M2, (M2 = Replay.parkM dy m ∨ M2 ∈ (Replay.brkArm dy (Replay.parkM dy m) e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) → M2.block.bind (·.obs) = m.block.bind (·.obs) := fun M2 h => by rcases h with rfl | h; (rw [hpk]); exact hDA _ _ hpk (Or.inr h)
      rcases brkPark_machine_cases hm with ⟨y, -, hm⟩ | ⟨M2, hM2, h | h⟩
      · exact Or.inl (hDA m m' rfl (Or.inl ⟨y, hm⟩))
      all_goals rw [h]
      · exact Or.inl (hM M2 hM2)
      · exact Or.inl ((reopen_keeps dy M2 o).1.trans (hM M2 hM2))
    · exact Or.inl (hLn m m' rfl hm)
  case brkStart pl w =>
    split at hm
    · rename_i t0 _
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      exact Or.inl (Replay.brkFx_machine dy { Replay.forget m with ended := Replay.pushEnded (Replay.endingOf ⟨t, pl.val, w, d⟩ t0 e.line) m } ⟨t, t0, d, e.line, pl.val, w, t0⟩ m' hm').2.2
    unfold Replay.brkStartArm at hm
    -- D105: the running break is set and the block, with its pending observation, untouched — settled over the
    -- running break and the held closed blocks netted by it since README gap 5180, neither of which moves it.
    simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
      List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
    subst hm
    rw [(Replay.runNet_keeps dy _).1, Replay.settle_obs]
    exact Or.inl (congrArg (·.bind (·.obs)) (Replay.forgetIdle_keeps m).1)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **A step's pending observation is its start's, none, or on the step's day.** -/
theorem stepWith_pending (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (Replay.stepWith z dy sl st e).machine.block.bind (·.obs) = st.machine.block.bind (·.obs) ∨
    (Replay.stepWith z dy sl st e).machine.block.bind (·.obs) = none ∨
    ∃ o, (Replay.stepWith z dy sl st e).machine.block.bind (·.obs) = some o ∧ o.day = dy e.t.val := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z st.machine e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  unfold Replay.stepWith
  rw [h3, hfx]
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => exact Or.inl rfl
  | some m' =>
    rw [Option.getD_some]
    exact arm_pending dy sl st.machine e _ _ m' (List.mem_of_getLast? hl)

/-- **A fold's pending observation is its start state's, or on one of its entries' days.** -/
theorem foldl_pending (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (o : Replay.EnergyObs),
      (sv.foldl (Replay.stepWith z dy sl) st).machine.block.bind (·.obs) = some o →
        st.machine.block.bind (·.obs) = some o ∨ ∃ e ∈ sv, o.day = dy e.t.val
  | [], _, _, h => Or.inl h
  | e :: sv, st, o, h => by
    rw [List.foldl_cons] at h
    rcases foldl_pending z dy sl sv _ o h with h' | ⟨e', he', hd⟩
    · rcases stepWith_pending z dy sl st e with h1 | h1 | ⟨o', h1, h2⟩
      · rw [h1] at h'; exact Or.inl h'
      · rw [h1] at h'; cases h'
      · rw [h1] at h'
        cases h'
        exact Or.inr ⟨e, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd⟩

end Seal
end Tm
