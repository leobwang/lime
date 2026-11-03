import TmKernel.SealResume
/-!
# SealStep — a step reads the index only where it queries it (stage 5, D9, W2)

`stepQueries dy m e` is every instant a step reads the day index at.  Two index functions that agree there give one step
(`effectsWith_congr`), and a fold's queries are its entries' own instants and the instants its start state's block holds
(`foldQueries_sub`).  Specification only (D9-21): nothing here is on the wire.
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect Block)
open Log (Entry)

section Congr

variable (dy₁ dy₂ : Cal.Instant → Nat)

/-- **A re-draw reads the index only at the starts of the pieces it draws anew** (`redrawReads`, the owner's D99). -/
theorem redraw_congr (id : Log.Id) (old : List Replay.Piece) (P : List (Replay.At × Replay.At))
    (h : ∀ q ∈ redrawReads old P, dy₁ q = dy₂ q) :
    Replay.redraw dy₁ id old P = Replay.redraw dy₂ id old P := by
  unfold Replay.redraw
  have hnew : ∀ q ∈ P, old.any (fun p => Replay.samePiece p q) = false → dy₁ q.1.1 = dy₂ q.1.1 := by
    intro q hq hn
    exact h _ (List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by simp [hn]⟩, rfl⟩)
  congr 1
  · apply List.map_congr_left
    intro q hq
    cases hf : old.find? (fun p => Replay.samePiece p q) with
    | some p => rfl
    | none =>
      have hn : old.any (fun p => Replay.samePiece p q) = false := by
        rw [List.find?_eq_none] at hf
        simpa using hf
      simp only [hnew q hq hn]
  · congr 1
    apply List.map_congr_left
    intro q hq
    obtain ⟨hq, hn⟩ := List.mem_filter.1 hq
    rw [hnew q hq (by simpa using hn)]

/-- **Settling the open block reads the index only at its new pieces' starts** (`settleReads`, D99). -/
theorem settle_congr (m : Machine) (h : ∀ q ∈ settleReads m, dy₁ q = dy₂ q) :
    Replay.settle dy₁ m = Replay.settle dy₂ m := by
  unfold Replay.settle
  cases hb : m.block with
  | none => rfl
  | some b =>
    have hr := redraw_congr dy₁ dy₂ b.id b.drawn (Replay.openPieces b m) (fun q hq => h q (by
      unfold settleReads; rw [hb]; exact hq))
    simp only [hr]

theorem closePause_congr (m : Machine) (t : Replay.At) (h : ∀ q ∈ blockPaused m, dy₁ q = dy₂ q) :
    Replay.closePause dy₁ m t = Replay.closePause dy₂ m t := by
  unfold Replay.closePause
  cases hb : m.block with
  | none => rfl
  | some b =>
    cases hs : b.pausedAt with
    | none => simp [hs]
    | some s =>
      have : dy₁ s.1 = dy₂ s.1 := h s.1 (by simp [blockPaused, hb, hs])
      simp [hs, this]

/-- **A cut reads the index only at its new pieces' starts, the pause it closes and its own stamp.** -/
theorem cut_congr (m : Machine) (t : Replay.At)
    (h : ∀ q ∈ cutReads m t ++ blockPaused m ++ [t.1], dy₁ q = dy₂ q) :
    Replay.cut dy₁ m t = Replay.cut dy₂ m t := by
  have h2 := closePause_congr dy₁ dy₂ m t (fun q hq => h q (by simp [hq]))
  have ht : dy₁ t.1 = dy₂ t.1 := h t.1 (by simp)
  unfold Replay.cut
  cases hb : m.block with
  | none => rfl
  | some b =>
    have hr := redraw_congr dy₁ dy₂ b.id b.drawn (Replay.cutPieces b m t) (fun q hq => h q (by
      simp only [List.mem_append]; left; left; unfold cutReads; rw [hb]; exact hq))
    simp only [hr, h2, ht, Replay.creditFx]

/-- **Settling a block just begun reads the index where it would over the machine the `start` began in** (the owner's
D100: the `start` arm settles over the machine its cut left, which holds the cut block closed; the settle reads only
the block, the interruption and the breaks). -/
theorem settleReads_startedMachine (m m' : Machine) (id : Log.Id) (t : Replay.At) (d : Nat)
    (o : Option Replay.EnergyObs) (hi : m'.interrupt = m.interrupt) (hb : m'.brks = m.brks)
    (hk : m'.brkOpen = m.brkOpen) :
    settleReads (Replay.startedMachine m' id t d o) = settleReads (Replay.startedMachine m id t d o) := by
  unfold settleReads
  simp [Replay.startedMachine, Replay.openPieces, Replay.openEnd, Replay.runSpan, Replay.blockSpans, Replay.openStop,
    hi, hb, hk]

theorem cut_interrupt (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) :
    (Replay.cut dy m t).1.interrupt = m.interrupt := by
  unfold Replay.cut; split <;> rfl

/-- **Netting one closed block reads the index only at the starts of the pieces it draws anew** (the owner's D100). -/
theorem netOne_congr (s e : Replay.At) (d : Nat) (C : Replay.Closed)
    (h : d < C.day ∨ ∀ q ∈ redrawReads C.drawn (Replay.cutOut s e C.spans), dy₁ q = dy₂ q) :
    Replay.netOne dy₁ s e d C = Replay.netOne dy₂ s e d C := by
  unfold Replay.netOne
  split
  · rfl
  · rename_i hd
    have hr := redraw_congr dy₁ dy₂ C.id C.drawn (Replay.cutOut s e C.spans) (h.resolve_left (fun h' => hd (Or.inl h')))
    simp only [hr]

/-- **Each held closed block a netting meets reads the index only at `closedReads`** (the owner's D100). -/
theorem netOne_congr_mem (s e : Replay.At) (d : Nat) (m : Machine)
    (h : ∀ q ∈ closedReads s e d m.closed, dy₁ q = dy₂ q) :
    ∀ C ∈ m.closed, Replay.netOne dy₁ s e d C = Replay.netOne dy₂ s e d C := by
  intro C hC
  by_cases hd : d < C.day ∨ C.drawn.all (fun p => decide (p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1)) = true
  · unfold Replay.netOne; simp only [if_pos hd]
  · apply netOne_congr
    exact Or.inr (fun q hq => h q (List.mem_flatMap.2 ⟨C, hC, by simp only [if_neg hd]; exact hq⟩))

/-- **Netting the held closed blocks reads the index only at `closedReads`** (the owner's D100). -/
theorem netClosed_congr (s e : Replay.At) (d : Nat) (m : Machine)
    (h : ∀ q ∈ closedReads s e d m.closed, dy₁ q = dy₂ q) :
    Replay.netClosed dy₁ s e d m = Replay.netClosed dy₂ s e d m := by
  have hC : ∀ C ∈ m.closed, Replay.netOne dy₁ s e d C = Replay.netOne dy₂ s e d C := by
    intro C hC
    by_cases hd : d < C.day ∨ C.drawn.all (fun p => decide (p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1)) = true
    · unfold Replay.netOne; simp only [if_pos hd]
    · apply netOne_congr
      exact Or.inr (fun q hq => h q (List.mem_flatMap.2 ⟨C, hC, by simp only [if_neg hd]; exact hq⟩))
  unfold Replay.netClosed
  have e1 : m.closed.map (fun C => (Replay.netOne dy₁ s e d C).1) =
      m.closed.map (fun C => (Replay.netOne dy₂ s e d C).1) :=
    List.map_congr_left (fun C hC' => by rw [hC C hC'])
  have e2 : m.closed.map (fun C => (Replay.netOne dy₁ s e d C).2.1) =
      m.closed.map (fun C => (Replay.netOne dy₂ s e d C).2.1) :=
    List.map_congr_left (fun C hC' => by rw [hC C hC'])
  rw [e1, e2]
  congr 2
  cases hcl : m.closed with
  | nil => cases m.lastCut <;> rfl
  | cons C rest =>
    have := hC C (by rw [hcl]; exact List.mem_cons_self ..)
    split <;> simp_all

/-- **A late start's cut reads the index only at `startReads`** (the owner's D115). -/
theorem netStart_congr (t : Replay.At) (d : Nat) (m : Machine)
    (h : ∀ q ∈ startReads t d m.closed, dy₁ q = dy₂ q) :
    Replay.netStart dy₁ t d m = Replay.netStart dy₂ t d m := by
  have hC : ∀ C ∈ m.closed, Replay.netOne dy₁ t (Replay.startEnd t C) d C =
      Replay.netOne dy₂ t (Replay.startEnd t C) d C := by
    intro C hC
    by_cases hd : d < C.day ∨ C.drawn.all (fun p => decide (p.e.1 ≤ t.1 ∨ (Replay.startEnd t C).1 ≤ p.s.1)) = true
    · unfold Replay.netOne; simp only [if_pos hd]
    · apply netOne_congr
      exact Or.inr (fun q hq => h q (List.mem_flatMap.2 ⟨C, hC, by simp only [if_neg hd]; exact hq⟩))
  unfold Replay.netStart
  have e1 : m.closed.map (fun C => (Replay.netOne dy₁ t (Replay.startEnd t C) d C).1) =
      m.closed.map (fun C => (Replay.netOne dy₂ t (Replay.startEnd t C) d C).1) :=
    List.map_congr_left (fun C hC' => by rw [hC C hC'])
  have e2 : m.closed.map (fun C => (Replay.netOne dy₁ t (Replay.startEnd t C) d C).2.1) =
      m.closed.map (fun C => (Replay.netOne dy₂ t (Replay.startEnd t C) d C).2.1) :=
    List.map_congr_left (fun C hC' => by rw [hC C hC'])
  rw [e1, e2]
  congr 2
  cases hcl : m.closed with
  | nil => cases m.lastCut <;> rfl
  | cons C rest =>
    have := hC C (by rw [hcl]; exact List.mem_cons_self ..)
    split <;> simp_all

/-- **The running break's netting reads the index only at `runReads`** (README gap 5180). -/
theorem runNet_congr (m : Machine) (h : ∀ q ∈ runReads m, dy₁ q = dy₂ q) :
    Replay.runNet dy₁ m = Replay.runNet dy₂ m := by
  unfold Replay.runNet
  unfold runReads at h
  split
  · rename_i o ho
    simp only [ho] at h
    split
    · rename_i hlt
      rw [if_pos hlt] at h
      have e : m.closed.map (Replay.runOne dy₁ o.s (Replay.runTo o.s m.closed) o.day) =
          m.closed.map (Replay.runOne dy₂ o.s (Replay.runTo o.s m.closed) o.day) :=
        List.map_congr_left (fun C hC => by
          unfold Replay.runOne
          rw [netOne_congr_mem dy₁ dy₂ _ _ _ m h C hC])
      rw [netClosed_congr dy₁ dy₂ _ _ _ m h, e]
    · rfl
  · rfl

/-- **A give-back reads the index only at `giveReads`** (the owner's D137). -/
theorem giveBack_congr (m : Machine) (h : ∀ q ∈ giveReads m, dy₁ q = dy₂ q) :
    Replay.giveBack dy₁ m = Replay.giveBack dy₂ m := by
  have hC : ∀ C ∈ m.closed, Replay.giveOne dy₁ C = Replay.giveOne dy₂ C := by
    intro C hC
    unfold Replay.giveOne
    by_cases hr : C.ran.isEmpty = true ∧ C.ranMin = 0
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr]
      rw [redraw_congr dy₁ dy₂ C.id C.drawn C.restored (fun q hq => h q (List.mem_flatMap.2 ⟨C, hC, by
        rw [show (C.ran.isEmpty && C.ranMin == 0) = false by simpa using hr]; exact hq⟩))]
  unfold Replay.giveBack
  have e1 : m.closed.map (fun C => (Replay.giveOne dy₁ C).1) = m.closed.map (fun C => (Replay.giveOne dy₂ C).1) :=
    List.map_congr_left (fun C hC' => by rw [hC C hC'])
  have e2 : m.closed.map (fun C => (Replay.giveOne dy₁ C).2.1) = m.closed.map (fun C => (Replay.giveOne dy₂ C).2.1) :=
    List.map_congr_left (fun C hC' => by rw [hC C hC'])
  rw [e1, e2]
  congr 2
  cases hcl : m.closed with
  | nil => cases m.lastCut <;> rfl
  | cons C rest =>
    have := hC C (by rw [hcl]; exact List.mem_cons_self ..)
    split <;> simp_all

/-- **Settling the open block leaves what the running break's netting reads** (README gap 5180): it moves neither the
held closed blocks nor the running break. -/
theorem runReads_settle (dy : Cal.Instant → Nat) (m : Machine) : runReads (Replay.settle dy m).1 = runReads m :=
  runReads_shp _ _ (Replay.settle_keeps dy m).2.2.2.1 (by rw [Replay.settle_closed])

/-- **A late start's cut leaves what cutting the open block reads where it was** (the owner's D115): the block, its
breaks and the interruption are the machine's (`Replay.netStart_keeps`). -/
theorem cutReads_netStart (dy : Cal.Instant → Nat) (t t' : Replay.At) (d : Nat) (m : Machine) :
    cutReads (Replay.netStart dy t d m).1 t' = cutReads m t' ∧
      blockPaused (Replay.netStart dy t d m).1 = blockPaused m := by
  obtain ⟨k1, k2, k3, -, -⟩ := Replay.netStart_keeps dy t d m
  refine ⟨?_, ?_⟩ <;> simp only [cutReads, blockPaused, Replay.cutPieces, Replay.blockSpans, Replay.openStop, k1, k2, k3]

theorem doneClose_congr (m : Machine) (t : Replay.At) (id : Log.Id) (actual : Nat) (went : Option Log.U8)
    (h : ∀ b, m.block = some b → b.id = id → ∀ q ∈ cutReads m t ++ blockPaused m, dy₁ q = dy₂ q) :
    Replay.doneClose dy₁ m t id actual went = Replay.doneClose dy₂ m t id actual went := by
  unfold Replay.doneClose
  cases hb : m.block with
  | none => rfl
  | some b =>
    simp only
    split
    · rename_i hid
      have h2 := closePause_congr dy₁ dy₂ m t (fun q hq => h b hb hid q (by simp [hq]))
      have hr := redraw_congr dy₁ dy₂ b.id b.drawn (Replay.cutPieces b m t) (fun q hq => h b hb hid q (by
        simp only [List.mem_append]; left; unfold cutReads; rw [hb]; exact hq))
      simp only [hr, h2]
    · rfl

/-- **The closed blocks a `done` leaves read the index only at its own stamp and its cut's new pieces' starts** (the owner's
D100). -/
theorem doneClosed_congr (m : Machine) (line : Nat) (t : Replay.At) (id : Log.Id) (actual : Nat) (ci : Log.U8)
    (h : ∀ b, m.block = some b → b.id = id → ∀ q ∈ cutReads m t, dy₁ q = dy₂ q) (ht : dy₁ t.1 = dy₂ t.1) :
    Replay.doneClosed dy₁ m line t id actual ci = Replay.doneClosed dy₂ m line t id actual ci := by
  unfold Replay.doneClosed
  cases hb : m.block with
  | none => simp only [ht]
  | some b =>
    simp only
    split
    · rename_i hid
      have hr := redraw_congr dy₁ dy₂ b.id b.drawn (Replay.cutPieces b m t) (fun q hq => h b hb hid q (by
        unfold cutReads; rw [hb]; exact hq))
      simp only [hr, ht]
    · rfl

/-- **A start's arm reads the index only at its queries and its own stamp** (C3, D99, D115, gap 5180). -/
theorem startArm_congr (M : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id) (pred : Log.U8)
    (rep : Option Log.U8) (hsw : Log.Num) (sleptMin : Log.U32) (loc : List Char)
    (h : ∀ q ∈ startQueries dy₁ M line t d id pred rep hsw sleptMin loc, dy₁ q = dy₂ q) (ht : dy₁ t.1 = dy₂ t.1) :
    Replay.startArm dy₁ M line t d id pred rep hsw sleptMin loc =
      Replay.startArm dy₂ M line t d id pred rep hsw sleptMin loc := by
  unfold startQueries at h
  unfold Replay.startArm
  dsimp only
  have hn := netStart_congr dy₁ dy₂ t d M (fun q hq => h q (by simp [hq]))
  have hc := cut_congr dy₁ dy₂ (Replay.netStart dy₂ t d M).1 t
    (fun q hq => by
      rw [(cutReads_netStart dy₂ _ t _ M).1, (cutReads_netStart dy₂ _ t _ M).2] at hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | hq
      · exact h q (by simp [hq])
      · exact h q (by simp [hq])
      · rw [hq]; exact ht)
  rw [hn] at h ⊢
  rw [hc] at h ⊢
  rw [runNet_congr dy₁ dy₂ _ (fun q hq => h q (by simp [hq]))]
  rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (by
    rw [settleReads_startedMachine M _ _ _ _ _
      ((Replay.runNet_keeps dy₂ _).2.1.trans ((cut_interrupt dy₂ _ _).trans (Replay.netStart_keeps dy₂ _ _ M).2.1))
      ((Replay.runNet_keeps dy₂ _).2.2.1.trans
        ((Replay.cut_brk dy₂ _ _).trans (Replay.netStart_keeps dy₂ _ _ M).2.2.1))
      ((Replay.runNet_keeps dy₂ _).2.2.2.1.trans
        ((Replay.cut_brkOpen dy₂ _ _).trans (Replay.netStart_keeps dy₂ _ _ M).2.2.2.1))] at hq
    simp [hq]))]

/-- **A break held as `[s, e)` reads the index only at its queries** (D87, D94, D100; `Replay.brkFx`). -/
theorem brkFx_congr (M : Machine) (k : Replay.HeldBrk) (h : ∀ q ∈ brkFxReads M k, dy₁ q = dy₂ q) :
    Replay.brkFx dy₁ M k = Replay.brkFx dy₂ M k := by
  unfold brkFxReads at h; have h1 := settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_left _ hq)); unfold Replay.brkFx Replay.netTake; simp only [h1]
  have h2 : ∀ q ∈ closedReads k.s k.e k.day (Replay.settle dy₂ { M with brks := Replay.pruneBrks (k :: M.brks), brkOpen := none }).1.closed, dy₁ q = dy₂ q := fun q hq => h q (List.mem_append_right _ (by rwa [Replay.settle_closed] at hq))
  have e3 : (Replay.settle dy₂ { M with brks := Replay.pruneBrks (k :: M.brks), brkOpen := none }).1.closed.map (fun C => Replay.stash k.key { Replay.runOne dy₁ k.s k.e k.day C with held := (Replay.netOne dy₁ k.s k.e k.day C).1.held }) = (Replay.settle dy₂ { M with brks := Replay.pruneBrks (k :: M.brks), brkOpen := none }).1.closed.map (fun C => Replay.stash k.key { Replay.runOne dy₂ k.s k.e k.day C with held := (Replay.netOne dy₂ k.s k.e k.day C).1.held }) := List.map_congr_left (fun C hC => by unfold Replay.runOne; rw [netOne_congr_mem dy₁ dy₂ _ _ _ _ h2 C hC])
  rw [netClosed_congr dy₁ dy₂ _ _ _ _ h2, e3]
-- (W-54 track K, README gap 5878: a duplicate law stated under takeFx's name was deleted here; the blank lines keep check 9's recorded pin sites below where they were)




/-- **An arm reads the index only at the step's queries.** -/
theorem arm_congr (sl : Nat → Option Nat) (m : Machine) (e : Entry)
    (h : ∀ q ∈ stepQueries dy₁ m e, dy₁ q = dy₂ q) :
    Replay.arm dy₁ sl m e (e.t.val, e.off.val) (dy₁ e.t.val) = Replay.arm dy₂ sl m e (e.t.val, e.off.val) (dy₂ e.t.val) := by
  have ht : dy₁ e.t.val = dy₂ e.t.val := h _ (by simp [stepQueries, entryInstants])
  unfold stepQueries at h
  rw [ht] at h ⊢
  have hE : ∀ q ∈ entryInstants e, dy₁ q = dy₂ q := fun q hq => h q (List.mem_append_left _ hq)
  unfold Replay.arm
  cases hev : e.ev <;> simp only [hev] at h ⊢
  case start id pred rep hsw sleptMin loc _ _ =>
    have ht' : dy₁ (e.t.val, e.off.val).1 = dy₂ (e.t.val, e.off.val).1 := hE e.t.val (by simp [entryInstants])
    rcases hB : Replay.endsBrk m (e.t.val, e.off.val) with _ | o <;> simp only [hB] at h ⊢
    · rw [startArm_congr dy₁ dy₂ m _ _ _ _ _ _ _ _ _ (fun q hq => h q (List.mem_append_right _ hq)) ht']
    · rw [startArm_congr dy₁ dy₂ _ _ _ _ _ _ _ _ _ _ (fun q hq => h q (List.mem_append_right _ hq)) ht']
  case pause id =>
    split
    · split
      · rename_i b hb hc
        simp only [hb] at h
        rw [if_pos hc] at h
        rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ hq))]
      · rfl
    · rfl
  case unpause id =>
    split
    · split
      · rename_i b hb hc
        simp only [hb] at h
        rw [if_pos hc] at h
        rw [closePause_congr dy₁ dy₂ m _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_left _ hq)))]
        rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_right _ hq)))]
      · rfl
    · rfl
  case interrupt id =>
    rw [closePause_congr dy₁ dy₂ m _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_left _ hq)))]
    rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_right _ hq)))]
  case resume lost dropped =>
    split
    · rename_i s sd iid hi
      simp only [hi] at h
      rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_left _ hq)))]
      rw [netClosed_congr dy₁ dy₂ _ _ _ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_right _ (by
        rwa [Replay.settle_closed] at hq))))]
    · rename_i hi
      simp only [hi] at h ⊢
      rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ hq))]
  case stop id rem =>
    split
    · split
      · rename_i b hb hc
        simp only [hb] at h
        rw [if_pos hc] at h
        have hc := cut_congr dy₁ dy₂ m (e.t.val, e.off.val) (fun q hq => by
          simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with (hq | hq) | hq
          · exact h q (by simp [hq])
          · exact h q (by simp [hq])
          · exact hE q (by simp [entryInstants, hq]))
        rw [hc] at h ⊢
        rw [runNet_congr dy₁ dy₂ _ (fun q hq => h q (by simp [hq]))]
      · rfl
    · rfl
  case done id est actual went tags ci isPartial =>
    unfold Replay.doneFx Replay.creditFx
    dsimp only
    have h1 := doneClose_congr dy₁ dy₂ m (e.t.val, e.off.val) id actual.val went (fun b hb hid q hq =>
      h q (by rcases List.mem_append.1 hq with hq | hq <;> simp [hb, hid, hq]))
    have h2 := doneClosed_congr dy₁ dy₂ m e.line (e.t.val, e.off.val) id actual.val ci (fun b hb hid q hq =>
      h q (by simp [hb, hid, hq])) (hE e.t.val (by simp [entryInstants]))
    rw [h1, h2] at h ⊢
    rw [runNet_congr dy₁ dy₂ _ (fun q hq => h q (by simp [hq]))]
    rw [hE e.t.val (by simp [entryInstants])]
  case idle attributed min =>
    unfold Replay.dayArm
    simp only [hev]
    have : dy₁ (Cal.subMinutes e.t.val min.val) = dy₂ (Cal.subMinutes e.t.val min.val) :=
      hE _ (by simp [entryInstants, gapStart?, hev])
    rw [this]
  case routine item inst status actual =>
    unfold Replay.dayArm
    simp only [hev]
    cases hst : Log.parseInstanceStatus status with
    | none => rfl
    | some st =>
      cases st <;> cases hact : actual <;> try rfl
      rename_i mm
      have : dy₁ (Cal.subMinutes e.t.val mm.val) = dy₂ (Cal.subMinutes e.t.val mm.val) :=
        hE _ (by simp [entryInstants, gapStart?, hev, hst, hact])
      simp [this]
  case brk planned actual where_ =>
    have hb : ∀ (M : Machine) (k : Replay.HeldBrk), (∀ q ∈ giveReads M ++ brkFxReads (Replay.giveBack dy₁ M).1 k, dy₁ q = dy₂ q) →
        Replay.brkArmK dy₁ M e (e.t.val, e.off.val) (dy₂ e.t.val) planned.val (actual.map (·.val)) k =
          Replay.brkArmK dy₂ M e (e.t.val, e.off.val) (dy₂ e.t.val) planned.val (actual.map (·.val)) k := by
      intro M k hq
      have hg := giveBack_congr dy₁ dy₂ M (fun q h' => hq q (List.mem_append_left _ h'))
      unfold Replay.brkArmK
      rw [brkFx_congr dy₁ dy₂ _ _ (fun q h' => hq q (List.mem_append_right _ h')), hg]
    rcases hK : Replay.findEnded m (e.t.val, e.off.val) with _ | x <;> simp only [hK] at h
    · have h1 := hb m _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_left _ hq))); cases ho : m.brkOpen <;> simp only [ho]; (unfold Replay.brkLine Replay.finArm; simp only [hK]; rcases hF : Replay.findFin m (e.t.val, e.off.val) planned.val with _ | y <;> simp only [hF] at h ⊢; exact h1; (split; (rename_i hok; unfold Replay.d141Arm; rw [if_pos hok, if_pos hok, hb _ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_right _ hq)))]); exact h1)); (unfold Replay.brkOwn; simp only [hK]; exact h1)
    · have h2 : Replay.d141Arm dy₁ m x e (e.t.val, e.off.val) (dy₂ e.t.val) planned.val (actual.map (·.val)) = Replay.d141Arm dy₂ m x e (e.t.val, e.off.val) (dy₂ e.t.val) planned.val (actual.map (·.val)) := by unfold Replay.d141Arm; split; (rename_i hok; simp only [hok, if_true] at h; rw [hb _ _ (fun q hq => h q (List.mem_append_right _ hq))]); rfl
      cases ho : m.brkOpen <;> simp only [ho]; (unfold Replay.brkLine; simp only [hK]; exact h2); (unfold Replay.brkOwn; simp only [hK]; exact h2)
    -- (D147)
  case brkStart planned where_ =>
    rcases hF : Replay.firstStart (e.t.val, e.off.val) (dy₂ e.t.val) m with _ | t0 <;> simp only [hF] at h ⊢
    · unfold Replay.brkStartArm
      dsimp only
      rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (by simp [hq]))]
      rw [runNet_congr dy₁ dy₂ _ (fun q hq => h q (by rw [runReads_settle] at hq; simp [hq]))]
    · unfold Replay.endBrkFx
      rw [brkFx_congr dy₁ dy₂ _ _ (fun q hq => h q (List.mem_append_right _ hq))]
  all_goals first | rfl | (unfold Replay.dayArm; simp only [hev])





/-- **A step reads the index only at its queries.** -/
theorem effectsWith_congr (z : Cal.Tz) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : ∀ q ∈ stepQueries dy₁ st.machine e, dy₁ q = dy₂ q) :
    Replay.effectsWith z dy₁ sl st e = Replay.effectsWith z dy₂ sl st e := by
  have ht : dy₁ e.t.val = dy₂ e.t.val := h _ (by simp [stepQueries, entryInstants])
  unfold Replay.effectsWith
  rw [arm_congr dy₁ dy₂ sl st.machine e h, ht]

end Congr

/-! ## A fold's queries -/

/-- **Every instant a fold reads the day index at**, step by step. -/
def foldQueries (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) : State → List Entry → List Cal.Instant
  | _, [] => []
  | st, e :: sv => stepQueries dy st.machine e ++ foldQueries z dy sl (Replay.stepWith z dy sl st e) sv


/-- **Two index functions agreeing at a fold's queries give one fold.** -/
theorem foldl_stepWith_congr (z : Cal.Tz) (dy₁ dy₂ : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State), (∀ q ∈ foldQueries z dy₁ sl st sv, dy₁ q = dy₂ q) →
      sv.foldl (Replay.stepWith z dy₁ sl) st = sv.foldl (Replay.stepWith z dy₂ sl) st
  | [], _, _ => rfl
  | e :: sv, st, h => by
    have h1 : ∀ q ∈ stepQueries dy₁ st.machine e, dy₁ q = dy₂ q := fun q hq => h q (List.mem_append_left _ hq)
    have hs : Replay.stepWith z dy₁ sl st e = Replay.stepWith z dy₂ sl st e := by
      unfold Replay.stepWith; rw [effectsWith_congr dy₁ dy₂ z sl st e h1]
    rw [List.foldl_cons, List.foldl_cons, ← hs]
    exact foldl_stepWith_congr z dy₁ dy₂ sl sv _ (fun q hq => h q (List.mem_append_right _ hq))

/-- **The instants a machine holds**: its open block's start, clock start, pause start and the ends of its own idle
spans (the owner's D99: a piece a later step draws begins at its start or at one of these ends), and — since the
owner's D92 (README gap 4241), every break it holds since D94 (README gaps 4361 and 4506) — the ends of the breaks it
holds, where a piece after one begins; and — since the owner's D100 (README gap 4520b) — the starts of the pieces of
every closed block it holds, where a piece a late break re-draws for one begins (or at the break's end); and — since the
owner's D137 (README gaps 5504 and 5302) — the starts of the pieces a running break took from one (`Closed.ran`), where
a piece the `break` line gives back begins; and, since W-52 repair track R (README gaps 5711 and 5712), the starts of the pieces every D129 ending holds as its take (`Closed.held`), which its own `break` line gives back. -/
def machineInstants (m : Machine) : List Cal.Instant :=
  (match m.block with
   | some b => b.started.1 :: ((b.since.map (·.1)).toList ++ (b.pausedAt.map (·.1)).toList ++ b.idle.map (·.2.1))
   | none => []) ++ (m.brks.map (·.e.1) ++ m.closed.flatMap (fun C => (C.drawn ++ C.ran ++ C.held.flatMap (·.ran)).map (·.s.1)))

/-- **What a machine holds, by where it is held** (D99). -/
theorem mem_machineInstants (m : Machine) (q : Cal.Instant) :
    q ∈ machineInstants m ↔
      (∃ b, m.block = some b ∧ (b.started.1 = q ∨ (∃ x, b.since = some x ∧ x.1 = q) ∨
        (∃ x, b.pausedAt = some x ∧ x.1 = q) ∨ (∃ sp ∈ b.idle, sp.2.1 = q))) ∨
      ((∃ k ∈ m.brks, k.e.1 = q) ∨ (∃ C ∈ m.closed, ∃ p ∈ C.drawn ++ C.ran ++ C.held.flatMap (·.ran), p.s.1 = q)) := by
  unfold machineInstants
  cases hb : m.block with
  | none => simp [List.mem_flatMap, or_and_right, exists_or]
  | some b =>
    simp only [List.mem_append, List.mem_cons, List.mem_map, Option.mem_toList, Option.map_eq_some_iff,
      Option.some.injEq, exists_eq_left', or_assoc, List.mem_flatMap]
    constructor
    · intro h
      rcases h with h | h | h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · intro h
      rcases h with h | h | h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- **Where a block's pieces begin, the machine holds** (D99): its start, or the end of one of the spans it nets. -/
theorem piece_start_mi (b : Block) (m : Machine) (hb : m.block = some b) (x t : Replay.At) (hx : x = b.started)
    (n : Nat) (q : Replay.At × Replay.At) (hq : q ∈ Replay.piecesGo (Replay.blockSpans b m) n x t) :
    q.1.1 ∈ machineInstants m := by
  rw [mem_machineInstants]
  rcases Replay.piecesGo_starts _ n x t q hq with ⟨h1, -⟩ | h1
  · subst hx; rw [h1]; exact Or.inl ⟨b, hb, Or.inl rfl⟩
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h1
    rcases List.mem_append.1 hp with hp | hp
    · exact Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨p, hp, by rw [hpe]⟩))⟩
    · obtain ⟨k, hk, -, hke⟩ := Replay.mem_spansFor hp
      exact Or.inr (Or.inl ⟨k, hk, by rw [← hpe, hke]⟩)

/-- **What a re-draw reads, the machine holds** (D99). -/
theorem redrawReads_mi (b : Block) (m : Machine) (hb : m.block = some b) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ redrawReads b.drawn (Replay.pieces (Replay.blockSpans b m) b.started t)) : q ∈ machineInstants m := by
  unfold redrawReads at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact piece_start_mi b m hb _ t rfl _ p (List.mem_filter.1 hp).1

/-- **Where an open block's pieces begin, the machine holds** (D99; README gap 5180): its start, or the end of a span
it nets — never the end of the running break's span, which is the end of the stretch drawn and so of no piece's start
(`Replay.piecesGo_lt`). -/
theorem piece_start_run_mi (b : Block) (m : Machine) (hb : m.block = some b) (x t : Replay.At) (hx : x = b.started)
    (n : Nat) (q : Replay.At × Replay.At)
    (hq : q ∈ Replay.piecesGo (Replay.blockSpans b m ++ Replay.runSpan b m t) n x t) :
    q.1.1 ∈ machineInstants m := by
  rw [mem_machineInstants]
  have hlt := Replay.piecesGo_lt _ n x t q hq
  rcases Replay.piecesGo_starts _ n x t q hq with ⟨h1, -⟩ | h1
  · subst hx; rw [h1]; exact Or.inl ⟨b, hb, Or.inl rfl⟩
  · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h1
    rcases List.mem_append.1 hp with hp | hp
    · rcases List.mem_append.1 hp with hp | hp
      · exact Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨p, hp, by rw [hpe]⟩))⟩
      · obtain ⟨k, hk, -, hke⟩ := Replay.mem_spansFor hp
        exact Or.inr (Or.inl ⟨k, hk, by rw [← hpe, hke]⟩)
    · exfalso
      unfold Replay.runSpan at hp
      split at hp
      · split at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          rw [← hpe] at hlt
          exact Cal.Instant.lt_irrefl _ hlt
        · cases hp
      · cases hp

theorem settleReads_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ settleReads m) : q ∈ machineInstants m := by
  unfold settleReads at hq
  cases hb : m.block with
  | none => rw [hb] at hq; cases hq
  | some b =>
    rw [hb] at hq
    unfold redrawReads Replay.openPieces Replay.pieces at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact piece_start_run_mi b m hb _ _ rfl _ p (List.mem_filter.1 hp).1

theorem cutReads_mi (m : Machine) (t : Replay.At) (q : Cal.Instant) (hq : q ∈ cutReads m t) : q ∈ machineInstants m := by
  unfold cutReads at hq
  cases hb : m.block with
  | none => rw [hb] at hq; cases hq
  | some b =>
    rw [hb] at hq
    exact redrawReads_mi b m hb _ q hq

theorem blockPaused_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ blockPaused m) : q ∈ machineInstants m := by
  unfold blockPaused at hq
  rw [mem_machineInstants]
  cases hb : m.block with
  | none => rw [hb] at hq; simp at hq
  | some b =>
    rw [hb] at hq
    simp only [Option.bind_some] at hq
    cases hp : b.pausedAt with
    | none => rw [hp] at hq; simp at hq
    | some x =>
      rw [hp] at hq
      simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hq
      exact Or.inl ⟨b, rfl, Or.inr (Or.inr (Or.inl ⟨x, hp, hq.symm⟩))⟩

/-! ### What each arm's intermediate machine holds (the owner's D99) -/

/-- `runFrom` answers its start or the end of one of its spans. -/
theorem runFrom_cases (H : List (Replay.At × Replay.At)) : ∀ (x : Replay.At),
    Replay.runFrom H x = x ∨ Replay.runFrom H x ∈ H.map (·.2) := by
  induction H with
  | nil => intro x; exact Or.inl rfl
  | cons p H ih =>
    intro x
    show Replay.runFrom H (if p.1.1 < p.2.1 ∧ x.1 < p.2.1 then p.2 else x) = x ∨
      Replay.runFrom H (if p.1.1 < p.2.1 ∧ x.1 < p.2.1 then p.2 else x) ∈ (p :: H).map (·.2)
    split
    · rcases ih p.2 with h | h
      · exact Or.inr (by rw [h]; exact List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih x with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **Settling adds no instant** (D99): where the block's clock runs from is its start or the end of a span it nets,
and nothing else the machine holds moves. -/
theorem settle_mi (dy : Cal.Instant → Nat) (m : Machine) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.settle dy m).1) : q ∈ machineInstants m := by
  unfold Replay.settle at hq
  cases hb : m.block with
  | none => rw [hb] at hq; exact hq
  | some b =>
    rw [hb] at hq
    rw [mem_machineInstants] at hq ⊢
    rcases hq with ⟨b', hb', h⟩ | h
    · simp only [Option.some.injEq] at hb'
      subst hb'
      rcases h with h | ⟨x, hx, hxq⟩ | h | h
      · exact Or.inl ⟨b, hb, Or.inl h⟩
      · simp only at hx
        split at hx
        · cases hx
        · simp only [Option.some.injEq] at hx
          subst hx
          rcases runFrom_cases (Replay.blockSpans b m) b.started with hr | hr
          · rw [hr] at hxq; exact Or.inl ⟨b, hb, Or.inl hxq⟩
          · obtain ⟨p, hp, hpe⟩ := List.mem_map.1 hr
            rw [← hpe] at hxq
            rcases List.mem_append.1 hp with hp | hp
            · exact Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨p, hp, hxq⟩))⟩
            · obtain ⟨k, hk, -, hke⟩ := Replay.mem_spansFor hp
              exact Or.inr (Or.inl ⟨k, hk, by rw [← hxq, hke]⟩)
      · exact Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inl h))⟩
      · exact Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr h))⟩
    · exact Or.inr h

theorem startedMachine_mi (m : Machine) (id : Log.Id) (t : Replay.At) (d : Nat) (o : Option Replay.EnergyObs)
    (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.startedMachine m id t d o)) :
    q ∈ machineInstants m ∨ q = t.1 := by
  rw [mem_machineInstants] at hq
  rcases hq with ⟨b, hb, h⟩ | ⟨k, hk, rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
  · simp only [Replay.startedMachine, Option.some.injEq] at hb
    subst hb
    rcases h with h | ⟨x, hx, -⟩ | ⟨x, hx, -⟩ | ⟨sp, hsp, -⟩
    · exact Or.inr h.symm
    · cases hx
    · cases hx
    · cases hsp
  · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩)))

theorem closePauseM_mi (m : Machine) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.closePauseM m t)) : q ∈ machineInstants m ∨ q = t.1 := by
  unfold Replay.closePauseM at hq
  cases hb : m.block with
  | none => simp only [hb] at hq; exact Or.inl hq
  | some b =>
    cases hp : b.pausedAt with
    | none => simp only [hb, hp] at hq; exact Or.inl hq
    | some p =>
      simp only [hb, hp] at hq
      rw [mem_machineInstants] at hq
      rcases hq with ⟨b', hb', h⟩ | ⟨k, hk, rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
      · simp only [Option.some.injEq] at hb'
        subst hb'
        rcases h with h | h | ⟨x, hx, -⟩ | ⟨sp, hsp, hspq⟩
        · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inl h⟩))
        · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inl h)⟩))
        · cases hx
        · simp only at hsp
          split at hsp
          · rcases List.mem_append.1 hsp with hsp | hsp
            · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨sp, hsp, hspq⟩))⟩))
            · simp only [List.mem_singleton] at hsp
              subst hsp
              exact Or.inr hspq.symm
          · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨sp, hsp, hspq⟩))⟩))
      · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
      · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩)))

theorem unpaused_mi (m : Machine) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ machineInstants { Replay.closePauseM m t with
      block := (Replay.closePauseM m t).block.map (fun b => { b with paused := false }) }) :
    q ∈ machineInstants m ∨ q = t.1 := by
  refine closePauseM_mi m t q ?_
  rw [mem_machineInstants] at hq ⊢
  rcases hq with ⟨b', hb', h⟩ | h
  · cases hc : (Replay.closePauseM m t).block with
    | none => rw [hc] at hb'; cases hb'
    | some c =>
      rw [hc] at hb'
      simp only [Option.map_some, Option.some.injEq] at hb'
      subst hb'
      exact Or.inl ⟨c, by simp, h⟩
  · exact Or.inr h

theorem interruptMachine_mi (m : Machine) (t : Replay.At) (d : Nat) (id : Option Log.Id) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.interruptMachine m t d id)) : q ∈ machineInstants m ∨ q = t.1 := by
  refine closePauseM_mi m t q ?_
  unfold Replay.interruptMachine at hq
  split at hq
  · rw [mem_machineInstants] at hq ⊢; exact hq
  · exact hq

theorem closePauseM_brks (m : Machine) (t : Replay.At) : (Replay.closePauseM m t).brks = m.brks := by
  unfold Replay.closePauseM; repeat' split
  all_goals rfl

theorem closePauseM_interrupt (m : Machine) (t : Replay.At) :
    (Replay.closePauseM m t).interrupt = m.interrupt := by
  unfold Replay.closePauseM; repeat' split
  all_goals rfl

/-- A machine whose block's instants, breaks and closed blocks agree with another's holds that one's instants. -/
theorem mi_of_block (m m' : Machine)
    (hb : m'.block.map (fun b => (b.started, b.since, b.pausedAt, b.idle)) =
      m.block.map (fun b => (b.started, b.since, b.pausedAt, b.idle)))
    (hk : m'.brks = m.brks) (hc : m'.closed = m.closed) (q : Cal.Instant) (hq : q ∈ machineInstants m') :
    q ∈ machineInstants m := by
  rw [mem_machineInstants] at hq ⊢
  rcases hq with ⟨b', hb', h⟩ | ⟨k, hk', rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
  · rw [hb'] at hb
    cases hb1 : m.block with
    | none => rw [hb1] at hb; cases hb
    | some b =>
      rw [hb1] at hb
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨h1, h2, h3, h4⟩ := hb
      rw [h1, h2, h3, h4] at h
      exact Or.inl ⟨b, rfl, h⟩
  · rw [hk] at hk'; exact Or.inr (Or.inl ⟨k, hk', rfl⟩)
  · rw [hc] at hC; exact Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩)

theorem resumed_mi (m : Machine) (span : Option (Replay.At × Replay.At)) (t : Replay.At)
    (hs : ∀ sp, span = some sp → sp.2 = t) (i : Option (Replay.At × Nat × Option Log.Id)) (q : Cal.Instant)
    (hq : q ∈ machineInstants { m with block := m.block.map (fun b => Replay.resumeBlock b span t), interrupt := i }) :
    q ∈ machineInstants m ∨ q = t.1 := by
  rw [mem_machineInstants] at hq
  rcases hq with ⟨b', hb', h⟩ | ⟨k, hk, rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
  · cases hb : m.block with
    | none => simp [hb] at hb'
    | some b =>
      simp only [hb, Option.map_some, Option.some.injEq] at hb'
      subst hb'
      simp only [Replay.resumeBlock] at h
      rcases h with h | h | ⟨x, hx, hxq⟩ | ⟨sp, hsp, hspq⟩
      · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inl h⟩))
      · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inl h)⟩))
      · split at hx
        · cases hp : b.pausedAt with
          | none =>
            rw [hp] at hx
            simp only [Option.none_or, Option.some.injEq] at hx
            subst hx
            exact Or.inr hxq.symm
          | some p =>
            rw [hp] at hx
            simp only [Option.some_or, Option.some.injEq] at hx
            subst hx
            exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inl ⟨p, hp, hxq⟩))⟩))
        · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inl ⟨x, hx, hxq⟩))⟩))
      · cases hspan : span with
        | none =>
          simp only [hspan] at hsp
          exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨sp, hsp, hspq⟩))⟩))
        | some sp0 =>
          simp only [hspan] at hsp
          split at hsp
          · rcases List.mem_append.1 hsp with hsp | hsp
            · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨sp, hsp, hspq⟩))⟩))
            · simp only [List.mem_singleton] at hsp
              subst hsp
              right; rw [← hspq, hs _ hspan]
          · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨sp, hsp, hspq⟩))⟩))
  · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩)))

theorem heldBrk_mi (m : Machine) (k : Replay.HeldBrk) (q : Cal.Instant)
    (hq : q ∈ machineInstants { m with brks := Replay.pruneBrks (k :: m.brks), brkOpen := none }) :
    q ∈ machineInstants m ∨ q = k.e.1 := by
  rw [mem_machineInstants] at hq
  rcases hq with ⟨b, hb, h⟩ | ⟨k, hk, rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
  · exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, h⟩))
  · rcases List.mem_cons.1 (Replay.mem_pruneBrks hk) with rfl | hk
    · exact Or.inr rfl
    · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩)))

/-- **What netting the closed blocks reads, the machine holds, or the break's end** (the owner's D100). -/
theorem closedReads_mi (s e : Replay.At) (d : Nat) (l : List Replay.Closed) (q : Cal.Instant)
    (hq : q ∈ closedReads s e d l) : (∃ C ∈ l, ∃ p ∈ C.drawn, p.s.1 = q) ∨ q = e.1 := by
  unfold closedReads at hq
  obtain ⟨C, hC, hq⟩ := List.mem_flatMap.1 hq
  split at hq
  · cases hq
  · unfold redrawReads at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    rcases Replay.cutOut_starts s e C.spans q' (List.mem_filter.1 hq').1 with ⟨r, hr, hre⟩ | h
    · unfold Replay.Closed.spans at hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      exact Or.inl ⟨C, hC, p, hp, by rw [hre]⟩
    · exact Or.inr (by rw [h])

/-- **What a late start's cut reads, the machine holds** (the owner's D115): every read is where a held closed block's
own piece began — never at the span's end (`Replay.cutOut_startEnd_starts`). -/
theorem startReads_mi (t : Replay.At) (d : Nat) (l : List Replay.Closed) (q : Cal.Instant)
    (hq : q ∈ startReads t d l) : ∃ C ∈ l, ∃ p ∈ C.drawn, p.s.1 = q := by
  unfold startReads at hq
  obtain ⟨C, hC, hq⟩ := List.mem_flatMap.1 hq
  split at hq
  · cases hq
  · rename_i hg
    unfold redrawReads at hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    cases ha : (C.drawn ++ C.ran ++ C.held.flatMap (·.ran)).any (fun p => decide (p.s.1 < t.1)) with
    | false => exact absurd (Or.inr (Replay.startEnd_guard t C ha)) hg
    | true =>
      obtain ⟨r, hr, hre⟩ := Replay.cutOut_startEnd_starts_of t C C.spans (fun r hr => by
        unfold Replay.Closed.spans at hr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact Replay.startEnd_ge_run t C ha p (List.mem_append_left _ (List.mem_append_left _ hp))) q' (List.mem_filter.1 hq').1
      unfold Replay.Closed.spans at hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      exact ⟨C, hC, p, hp, by rw [hre]⟩

/-- **What the running break's netting reads, the machine holds** (README gap 5180): every read is where a held closed
block's own piece began — never at the span's end, which lies past every held piece (`Replay.cutOut_runTo_starts`). -/
theorem runReads_starts (m : Machine) (q : Cal.Instant) (hq : q ∈ runReads m) :
    ∃ C ∈ m.closed, ∃ p ∈ C.drawn, p.s.1 = q := by
  unfold runReads at hq
  split at hq
  · rename_i o _
    split at hq
    · unfold closedReads at hq
      obtain ⟨C, hC, hq⟩ := List.mem_flatMap.1 hq
      split at hq
      · cases hq
      · unfold redrawReads at hq
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        obtain ⟨r, hr, hre⟩ := Replay.cutOut_runTo_starts o.s m.closed C hC q' (List.mem_filter.1 hq').1
        unfold Replay.Closed.spans at hr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact ⟨C, hC, p, hp, by rw [hre]⟩
    · cases hq
  · cases hq

theorem runReads_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ runReads m) : q ∈ machineInstants m := by
  obtain ⟨C, hC, p, hp, rfl⟩ := runReads_starts m q hq
  exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), rfl⟩))

theorem doneFx_machines (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id)
    (est actual : Nat) (went : Option Log.U8) (tags : List (List Char)) (ci : Log.U8) (isPartial : Bool) :
    (Replay.doneFx dy m line t d id est actual went tags ci isPartial).filterMap Effect.machineOf?
      = [(Replay.runNet dy { (Replay.doneClose dy m t id actual went).1 with
          closed := Replay.doneClosed dy m line t id actual ci }).1] := by
  unfold Replay.doneFx
  simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_append,
    (Replay.doneClose_obs dy m t id actual went).2.2, Replay.runNet_machines]
  by_cases ha : 0 < actual <;> by_cases hp : isPartial = true <;> simp [ha, hp, Replay.creditFx, Effect.machineOf?]

/-- **Where a cut's pieces begin, the machine holds** (D99). -/
theorem cutPieces_mi (b : Block) (m : Machine) (hb : m.block = some b) (t : Replay.At) (q : Replay.At × Replay.At)
    (hq : q ∈ Replay.cutPieces b m t) : q.1.1 ∈ machineInstants m := by
  unfold Replay.cutPieces Replay.pieces at hq
  exact piece_start_mi b m hb _ _ rfl _ q hq

/-- **Where what a held break took from an open block begins, the machine holds** (W-54, README gap 5870): every piece of `Replay.openTakes` begins at the block's start or where one of its spans ends — an idle span of its own, or a held break. -/
theorem openTakes_mi (b : Block) (m : Machine) (hb : m.block = some b) (t : Replay.At) (T : Replay.Take) (hT : T ∈ Replay.openTakes b m t) (p : Replay.Piece) (hp : p ∈ T.ran) : p.s.1 ∈ machineInstants m := by
  unfold Replay.openTakes at hT; obtain ⟨k, -, hT⟩ := List.mem_filterMap.1 hT; split at hT
  · simp only [Option.some.injEq] at hT; subst hT; simp only [List.mem_map, List.mem_filter] at hp; obtain ⟨q, ⟨hq, -⟩, rfl⟩ := hp; unfold Replay.pieces at hq; rw [mem_machineInstants]
    rcases Replay.piecesGo_starts _ _ _ _ q hq with ⟨h1, -⟩ | h1; (rw [h1]; exact Or.inl ⟨b, hb, Or.inl rfl⟩); (obtain ⟨p, hp, hpe⟩ := List.mem_map.1 h1; rcases List.mem_append.1 hp with hp | hp; exact Or.inl ⟨b, hb, Or.inr (Or.inr (Or.inr ⟨p, hp, by rw [hpe]⟩))⟩; (obtain ⟨k', hk', -, hke⟩ := Replay.mem_spansFor hp; exact Or.inr (Or.inl ⟨k', List.mem_of_mem_erase hk', by rw [← hpe, hke]⟩)))
  · cases hT
/-- **A cut's machine holds no new instant** (D99; the owner's D100: the block it closes is held, its pieces beginning
where the cut drew them). -/
theorem cut_mi (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.cut dy m t).1) : q ∈ machineInstants m := by
  unfold Replay.cut at hq
  split at hq
  · rename_i b hb
    rw [mem_machineInstants] at hq
    rcases hq with ⟨b', hb', -⟩ | ⟨k, hk, rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
    · cases hb'
    · exact (mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    · rcases List.mem_cons.1 (Replay.mem_pruneClosed hC) with rfl | hC
      · have hpc : pc ∈ (Replay.redraw dy b.id b.drawn (Replay.cutPieces b m t)).1 ∨ ∃ a, a ∈ Replay.openTakes b m t ∧ pc ∈ a.ran := by simpa using hpc
        rcases hpc with hpc | ⟨T, hT, hpT⟩; (obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy b.id b.drawn _ pc hpc; rw [hpq]
                                             exact cutPieces_mi b m hb t q' hq'); exact openTakes_mi b m hb t T hT pc hpT
      · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩))
  · exact hq

/-- **What a netting keeps of a D129 ending's take begins where a piece of a take began, or at the span's end** (the
owner's D141, W-52 repair track R): `Replay.reNetTake_starts`, over every take a held block holds. -/
theorem netOne_held_starts (dy : Cal.Instant → Nat) (s e : Replay.At) (d : Nat) (C : Replay.Closed) (pc : Replay.Piece)
    (h : pc ∈ (Replay.netOne dy s e d C).1.held.flatMap (·.ran)) : (∃ r ∈ C.held.flatMap (·.ran), pc.s = r.s) ∨ pc.s = e := by
  obtain ⟨a, ha⟩ := Replay.netOne_held dy s e d C
  rw [ha] at h
  obtain ⟨T', hT', hp⟩ := List.mem_flatMap.1 h
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
  rcases Replay.reNetTake_starts s e d C a T pc hp with ⟨r, hr, hre⟩ | h
  · exact Or.inl ⟨r, List.mem_flatMap.2 ⟨T, hT, hr⟩, hre⟩
  · exact Or.inr h

/-- **What a late start's cut keeps of a D129 ending's take begins where a piece of a take began** (the owner's D115 and
D141, W-52 repair track R): `Replay.reNetTake_startEnd_starts`. -/
theorem netOne_held_startEnd (dy : Cal.Instant → Nat) (t : Replay.At) (d : Nat) (C : Replay.Closed) (pc : Replay.Piece)
    (h : pc ∈ (Replay.netOne dy t (Replay.startEnd t C) d C).1.held.flatMap (·.ran)) : ∃ r ∈ C.held.flatMap (·.ran), pc.s = r.s := by
  obtain ⟨a, ha⟩ := Replay.netOne_held dy t (Replay.startEnd t C) d C
  rw [ha] at h
  obtain ⟨T', hT', hp⟩ := List.mem_flatMap.1 h
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hT'
  obtain ⟨r, hr, hre⟩ := Replay.reNetTake_startEnd_starts t d C a T hT pc hp
  exact ⟨r, List.mem_flatMap.2 ⟨T, hT, hr⟩, hre⟩

/-- **The machine a late break's netting leaves holds no new instant but the break's end** (the owner's D100). -/
theorem netClosed_mi (dy : Cal.Instant → Nat) (s e : Replay.At) (d : Nat) (m : Machine) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.netClosed dy s e d m).1) : q ∈ machineInstants m ∨ q = e.1 := by
  rw [mem_machineInstants] at hq
  obtain ⟨k1, -, k3, -, -⟩ := Replay.netClosed_keeps dy s e d m
  rcases hq with ⟨b, hb, h⟩ | ⟨k, hk, rfl⟩ | ⟨C', hC', pc, hpc, rfl⟩
  · rw [k1] at hb; exact Or.inl ((mem_machineInstants m _).2 (Or.inl ⟨b, hb, h⟩))
  · rw [k3] at hk; exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  · have hC'' : C' ∈ m.closed.map (fun C => (Replay.netOne dy s e d C).1) := hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC''
    rcases List.mem_append.1 hpc with hpc | hpc
    case inr =>
      rcases netOne_held_starts dy s e d C pc hpc with ⟨r, hr, hre⟩ | h
      · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, r, List.mem_append_right _ hr, by rw [hre]⟩)))
      · exact Or.inr (by rw [h])
    rcases List.mem_append.1 hpc with hpc | hpc
    case inr =>
      rw [(Replay.netOne_ran dy s e d C).1] at hpc
      rcases Replay.reNet_starts s e d C _ pc hpc with ⟨r, hr, hre⟩ | h
      · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, r, List.mem_append_left _ (List.mem_append_right _ hr), by rw [hre]⟩)))
      · exact Or.inr (by rw [h])
    unfold Replay.netOne at hpc
    split at hpc
    · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, List.mem_append_left _ (List.mem_append_left _ hpc), rfl⟩)))
    · obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy C.id C.drawn _ pc hpc
      rcases Replay.cutOut_starts s e C.spans q' hq' with ⟨r, hr, hre⟩ | h
      · unfold Replay.Closed.spans at hr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), by rw [hpq, hre]⟩)))
      · exact Or.inr (by rw [hpq, h])

/-- **The machine a late start's cut leaves holds no new instant** (the owner's D115): every piece it draws anew begins where one of the block's own began (`Replay.cutOut_startEnd_starts`). -/
theorem netStart_mi (dy : Cal.Instant → Nat) (t : Replay.At) (d : Nat) (m : Machine) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.netStart dy t d m).1) : q ∈ machineInstants m := by
  rw [mem_machineInstants] at hq
  obtain ⟨k1, -, k3, -, -⟩ := Replay.netStart_keeps dy t d m
  rcases hq with ⟨b, hb, h⟩ | ⟨k, hk, rfl⟩ | ⟨C', hC', pc, hpc, rfl⟩
  · rw [k1] at hb; exact (mem_machineInstants m _).2 (Or.inl ⟨b, hb, h⟩)
  · rw [k3] at hk; exact (mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩))
  · have hC'' : C' ∈ m.closed.map (fun C => (Replay.netOne dy t (Replay.startEnd t C) d C).1) := hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC''
    rcases List.mem_append.1 hpc with hpc | hpc
    case inr =>
      obtain ⟨r, hr, hre⟩ := netOne_held_startEnd dy t d C pc hpc
      exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, r, List.mem_append_right _ hr, by rw [hre]⟩))
    rcases List.mem_append.1 hpc with hpc | hpc
    case inr =>
      rw [(Replay.netOne_ran dy t _ d C).1] at hpc
      obtain ⟨r, hr, hre⟩ := Replay.reNet_startEnd_starts t d C _ pc hpc
      exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, r, List.mem_append_left _ (List.mem_append_right _ hr), by rw [hre]⟩))
    unfold Replay.netOne at hpc
    split at hpc
    · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, List.mem_append_left _ (List.mem_append_left _ hpc), rfl⟩))
    · rename_i hg
      obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy C.id C.drawn _ pc hpc
      cases ha : (C.drawn ++ C.ran ++ C.held.flatMap (·.ran)).any (fun p => decide (p.s.1 < t.1)) with
      | false => exact absurd (Or.inr (Replay.startEnd_guard t C ha)) hg
      | true =>
        obtain ⟨r, hr, hre⟩ := Replay.cutOut_startEnd_starts_of t C C.spans (fun r hr => by
          unfold Replay.Closed.spans at hr
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
          exact Replay.startEnd_ge_run t C ha p (List.mem_append_left _ (List.mem_append_left _ hp))) q' hq'
        unfold Replay.Closed.spans at hr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), by rw [hpq, hre]⟩))

/-- **The machine the running break's netting leaves holds no new instant** (README gap 5180): every piece it draws anew begins where one of the held block's own began (`Replay.cutOut_runTo_starts`). -/
theorem runNet_mi (dy : Cal.Instant → Nat) (m : Machine) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.runNet dy m).1) : q ∈ machineInstants m := by
  rcases Replay.runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h] at hq; exact hq
  · rw [h] at hq
    rw [mem_machineInstants] at hq
    obtain ⟨k1, -, k3, -, -⟩ := Replay.netClosed_keeps dy o.s (Replay.runTo o.s m.closed) o.day m
    rcases hq with ⟨b, hb, h'⟩ | ⟨k, hk, rfl⟩ | ⟨C', hC', pc, hpc, rfl⟩
    · rw [k1] at hb; exact (mem_machineInstants m _).2 (Or.inl ⟨b, hb, h'⟩)
    · rw [k3] at hk; exact (mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    · have hC'' : C' ∈ m.closed.map (Replay.runOne dy o.s (Replay.runTo o.s m.closed) o.day) := hC'
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC''
      rcases List.mem_append.1 hpc with hpc | hpc
      case inr =>
        exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, List.mem_append_right _ hpc, rfl⟩))
      rcases List.mem_append.1 hpc with hpc | hpc
      case inr =>
        have hpc : pc ∈ (if o.day < C.day then C.ran else C.ran ++ C.drawn.filter
            (Replay.meets o.s (Replay.runTo o.s m.closed))) := hpc
        have hpc' : pc ∈ C.drawn ++ C.ran := by
          split at hpc
          · exact List.mem_append_right _ hpc
          · rcases List.mem_append.1 hpc with h1 | h1
            · exact List.mem_append_right _ h1
            · exact List.mem_append_left _ (List.mem_filter.1 h1).1
        exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, List.mem_append_left _ hpc', rfl⟩))
      have hpc : pc ∈ (Replay.netOne dy o.s (Replay.runTo o.s m.closed) o.day C).1.drawn := hpc
      unfold Replay.netOne at hpc
      split at hpc
      · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, List.mem_append_left _ (List.mem_append_left _ hpc), rfl⟩))
      · obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy C.id C.drawn _ pc hpc
        obtain ⟨r, hr, hre⟩ := Replay.cutOut_runTo_starts o.s m.closed C hC q' hq'
        unfold Replay.Closed.spans at hr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), by rw [hpq, hre]⟩))

/-- **The closed blocks a `done` leaves begin where the machine already holds** (the owner's D100). -/
theorem doneClosed_mi (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (id : Log.Id)
    (actual : Nat) (ci : Log.U8) (C : Replay.Closed) (hC : C ∈ Replay.doneClosed dy m line t id actual ci)
    (p : Replay.Piece) (hp : p ∈ C.drawn ++ C.ran ++ C.held.flatMap (·.ran)) : p.s.1 ∈ machineInstants m := by
  unfold Replay.doneClosed at hC
  cases hb : m.block with
  | some b =>
    rw [hb] at hC
    simp only at hC
    split at hC
    · rcases List.mem_cons.1 (Replay.mem_pruneClosed hC) with rfl | hC
      · have hp : p ∈ (Replay.redraw dy b.id b.drawn (Replay.cutPieces b m t)).1 ∨ ∃ a, a ∈ Replay.openTakes b m t ∧ p ∈ a.ran := by simpa using hp
        rcases hp with hp | ⟨T, hT, hpT⟩; (obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy b.id b.drawn _ p hp; rw [hpq]; exact cutPieces_mi b m hb t q' hq'); exact openTakes_mi b m hb t T hT p hpT
      · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, hp, rfl⟩))
    · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, hp, rfl⟩))
  | none =>
    rw [hb] at hC
    simp only at hC
    rcases hlc : m.lastCut with _ | c
    · simp only [hlc] at hC
      exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, hp, rfl⟩))
    · cases hcl : m.closed with
      | nil => rw [hcl] at hC; simp only [hlc] at hC; cases hC
      | cons C0 rest =>
        simp only [hlc, hcl] at hC
        split at hC
        · rcases List.mem_cons.1 hC with rfl | hC
          · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C0, by rw [hcl]; exact List.mem_cons_self .., p, hp, rfl⟩))
          · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, by rw [hcl]; exact List.mem_cons_of_mem _ hC, p, hp, rfl⟩))
        · rw [← hcl] at hC
          exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, hp, rfl⟩))
theorem doneClose_keeps (dy : Cal.Instant → Nat) (m : Machine) (t : Replay.At) (id : Log.Id) (actual : Nat)
    (went : Option Log.U8) :
    ((Replay.doneClose dy m t id actual went).1.block = none ∨
      (Replay.doneClose dy m t id actual went).1.block = m.block) ∧
      (Replay.doneClose dy m t id actual went).1.brks = m.brks := by
  unfold Replay.doneClose
  split
  · split
    · exact ⟨Or.inl rfl, rfl⟩
    · exact ⟨Or.inr rfl, rfl⟩
  · split
    · split
      · exact ⟨Or.inr rfl, rfl⟩
      · exact ⟨Or.inr rfl, rfl⟩
    · exact ⟨Or.inr rfl, rfl⟩
/-- **A start's queries are its stamp or instants the machine it starts from holds** (C3, D99, D115, gap 5180). -/
theorem startQueries_sub (dy : Cal.Instant → Nat) (M : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id)
    (pred : Log.U8) (rep : Option Log.U8) (hsw : Log.Num) (sleptMin : Log.U32) (loc : List Char) (q : Cal.Instant)
    (hq : q ∈ startQueries dy M line t d id pred rep hsw sleptMin loc) : q = t.1 ∨ q ∈ machineInstants M := by
  unfold startQueries at hq
  simp only [List.mem_append] at hq
  rcases hq with (((hq | hq) | hq) | hq) | hq
  · obtain ⟨C, hC, p, hp, rfl⟩ := startReads_mi _ _ _ q hq
    exact Or.inr ((mem_machineInstants M _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), rfl⟩)))
  · exact Or.inr (cutReads_mi M _ q hq)
  · exact Or.inr (blockPaused_mi M q hq)
  · exact Or.inr (netStart_mi dy _ _ M q (cut_mi dy _ _ q (runReads_mi _ q hq)))
  · rcases startedMachine_mi M _ _ _ _ q (settleReads_mi _ q hq) with h | h
    · exact Or.inr h
    · exact Or.inl h
/-- **Where a held block's restored pieces begin, it held a piece** (the owner's D137): its own drawn pieces' starts and those of the pieces the running break took (`Replay.Closed.ran`). -/
theorem restored_starts (C : Replay.Closed) (q : Replay.At × Replay.At) (hq : q ∈ C.restored) :
    ∃ p ∈ C.drawn ++ C.ran, p.s = q.1 := by
  unfold Replay.Closed.restored at hq
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨p, List.mem_append_left _ (List.mem_filter.1 hp).1, rfl⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact ⟨p, List.mem_append_right _ hp, rfl⟩
/-- **What a give-back reads, the machine holds** (the owner's D137). -/
theorem giveReads_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ giveReads m) : q ∈ machineInstants m := by
  obtain ⟨C, hC, hq⟩ := List.mem_flatMap.1 hq
  split at hq
  · cases hq
  · unfold redrawReads at hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
    obtain ⟨p, hp, hpr⟩ := restored_starts C r (List.mem_filter.1 hr).1
    exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ hp, by rw [hpr]⟩))

/-- **The machine a give-back leaves holds no new instant** (the owner's D137): every piece it re-draws begins where a held block's piece, or a piece the running break took from it, began. -/
theorem giveBack_mi (dy : Cal.Instant → Nat) (m : Machine) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.giveBack dy m).1) : q ∈ machineInstants m := by
  rw [mem_machineInstants] at hq
  obtain ⟨k1, -, k3, -, -, -⟩ := Replay.giveBack_keeps dy m
  rcases hq with ⟨b, hb, h⟩ | ⟨k, hk, rfl⟩ | ⟨C', hC', pc, hpc, rfl⟩
  · rw [k1] at hb; exact (mem_machineInstants m _).2 (Or.inl ⟨b, hb, h⟩)
  · rw [k3] at hk; exact (mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩))
  · have hC'' : C' ∈ m.closed.map (fun C => (Replay.giveOne dy C).1) := hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC''
    unfold Replay.giveOne at hpc
    by_cases hr : C.ran.isEmpty = true ∧ C.ranMin = 0
    · rw [if_pos hr] at hpc
      exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩))
    · rw [if_neg hr] at hpc
      dsimp only at hpc
      simp only [List.append_nil] at hpc
      rcases List.mem_append.1 hpc with hpc | hpc
      · obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy C.id C.drawn _ pc hpc
        obtain ⟨p, hp, hpr⟩ := restored_starts C q' hq'
        exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ hp, by rw [hpq, hpr]⟩))
      · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, List.mem_append_right _ hpc, rfl⟩))

/-- **What `stash`, `unstash` and `dropTake` leave of a held block's pieces, it held** (the owner's D141, W-52 repair track
R): each moves a take between `ran` and `held`, or lets one go. -/
theorem pcs_stash (k : Nat) (C : Replay.Closed) (p : Replay.Piece)
    (h : p ∈ (Replay.stash k C).drawn ++ (Replay.stash k C).ran ++ (Replay.stash k C).held.flatMap (·.ran)) :
    p ∈ C.drawn ++ C.ran ++ C.held.flatMap (·.ran) := by
  unfold Replay.stash at h; split at h
  · exact h
  · simp only [List.append_nil, List.flatMap_cons, List.mem_append] at h ⊢
    rcases h with h | h | h <;> simp [h]
theorem pcs_dropTake (k : Nat) (C : Replay.Closed) (p : Replay.Piece)
    (h : p ∈ (Replay.dropTake k C).drawn ++ (Replay.dropTake k C).ran ++ (Replay.dropTake k C).held.flatMap (·.ran)) :
    p ∈ C.drawn ++ C.ran ++ C.held.flatMap (·.ran) := by
  unfold Replay.dropTake at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_filter] at h ⊢
  rcases h with (h | h) | ⟨T, ⟨hT, -⟩, hp⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr ⟨T, hT, hp⟩
theorem pcs_unstash (k : Nat) (C : Replay.Closed) (p : Replay.Piece)
    (h : p ∈ (Replay.unstash k C).drawn ++ (Replay.unstash k C).ran ++ (Replay.unstash k C).held.flatMap (·.ran)) :
    p ∈ C.drawn ++ C.ran ++ C.held.flatMap (·.ran) := by
  unfold Replay.unstash at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_append.1 h with h | h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · cases hf : C.held.find? (fun T => T.key == k) with
      | none => rw [hf] at h; cases h
      | some T => rw [hf] at h; exact List.mem_append_right _ (List.mem_flatMap.2 ⟨T, List.mem_of_find?_eq_some hf, h⟩)
  · exact pcs_dropTake k C p (List.mem_append_right _ h)

/-- **The machine a start ending a running break starts from holds the old one's instants and the start's stamp** (D129, `Replay.endMachine`): the break is held with the ones before it, its end the start's stamp. -/
theorem endMachine_mi (m : Machine) (o : Replay.OpenBrk) (t : Replay.At) (key : Nat) (q : Cal.Instant)
    (hq : q ∈ machineInstants (Replay.endMachine m o t key)) : q ∈ machineInstants m ∨ q = t.1 := by
  apply heldBrk_mi m ⟨o.s, t, o.day, key, o.planned, o.where_, t⟩ q
  rw [mem_machineInstants] at hq ⊢
  rcases hq with h | h | ⟨C', hC', p, hp, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
    exact Or.inr (Or.inr ⟨C, hC, p, pcs_stash key C p hp, rfl⟩)

/-- **What `firstStart` answers, the machine holds** (D129): the open block's start, or a held closed block's piece start. -/
theorem firstStart_mi (s : Replay.At) (d : Nat) (m : Machine) (x : Replay.At) (h : Replay.firstStart s d m = some x) :
    x.1 ∈ machineInstants m := by
  rw [mem_machineInstants]
  rcases Replay.firstStart_mem s d m x h with ⟨b, hb, rfl⟩ | ⟨C, hC, p, hp, rfl⟩
  · exact Or.inl ⟨b, hb, Or.inl rfl⟩
  · exact Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), rfl⟩)

/-- **A machine whose block is the old one's, whose held breaks are among the old one's, and whose held blocks' pieces begin where the old one's did holds no new instant** (the owner's D141: `Replay.forget`, `Replay.forgetIdle`, and the machine D141's line reads its `break` line over, the ended break let go). -/
theorem mi_of_sub (m M : Machine) (hb : M.block = m.block) (hk : ∀ k ∈ M.brks, k ∈ m.brks) (hc : ∀ C' ∈ M.closed, ∀ p ∈ C'.drawn ++ C'.ran ++ C'.held.flatMap (·.ran), ∃ C ∈ m.closed, ∃ p' ∈ C.drawn ++ C.ran ++ C.held.flatMap (·.ran), p'.s = p.s) (q : Cal.Instant) (hq : q ∈ machineInstants M) : q ∈ machineInstants m := by
  rw [mem_machineInstants] at hq
  rcases hq with ⟨b, hb', h⟩ | ⟨k, hk', rfl⟩ | ⟨C', hC', p, hp, rfl⟩
  · rw [hb] at hb'; exact (mem_machineInstants m _).2 (Or.inl ⟨b, hb', h⟩)
  · exact (mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk k hk', rfl⟩))
  · obtain ⟨C, hC, p', hp', he⟩ := hc C' hC' p hp; exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p', hp', by rw [he]⟩))
theorem forget_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.forget m)) : q ∈ machineInstants m :=
  mi_of_sub m (Replay.forget m) rfl (fun k hk => hk) (fun C' hC' p hp => by
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
    simp only [List.append_nil, List.mem_append] at hp
    exact ⟨C, hC, p, by rcases hp with hp | hp <;> simp [hp], rfl⟩) q hq
theorem forgetIdle_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.forgetIdle m)) : q ∈ machineInstants m := by
  unfold Replay.forgetIdle at hq; split at hq
  · exact forget_mi m q hq
  · exact hq
theorem tail_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ machineInstants { m with brks := m.brks.tail, ended := [] }) : q ∈ machineInstants m :=
  mi_of_sub m { m with brks := m.brks.tail, ended := [] } rfl (fun k hk => List.mem_of_mem_tail hk) (fun C' hC' p hp => ⟨C', hC', p, hp, rfl⟩) q hq
/-- **The machine D141's line is read over holds no new instant** (W-52 repair track R): `x`'s break let go, `x`'s take moved into `ran`. -/
theorem d141Machine_mi (m : Machine) (x : Replay.Ending) (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.d141Machine m x)) : q ∈ machineInstants m :=
  mi_of_sub m (Replay.d141Machine m x) rfl (fun k hk => List.mem_of_mem_erase hk) (fun C' hC' p hp => by
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'; exact ⟨C, hC, p, pcs_unstash x.key C p hp, rfl⟩) q hq
/-- **The machine P127's reading of the line leaves holds no new instant** (W-52 repair track R). -/
theorem letGo_mi (m : Machine) (x : Replay.Ending) (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.letGo x m)) : q ∈ machineInstants m :=
  mi_of_sub m (Replay.letGo x m) rfl (fun k hk => hk) (fun C' hC' p hp => ⟨C', hC', p, hp, rfl⟩) q hq
/-- **A break's machine holds the old machine's instants and the break's end** (D87, D92, D94, D99, D141): the break is held with the ones before it (`Replay.pruneBrks`), the block settled over them adds no instant (`settle_mi`), and every take a netting remembers or cuts (`Replay.netTake`) begins where a piece the old machine held began.  W-53 repair track K proved this as takeFx_mi, a second name for `Replay.brkFx`, and this law called it; W-54 deleted the duplicate (README gap 5878). -/
theorem brkFx_mi (dy : Cal.Instant → Nat) (m : Machine) (k : Replay.HeldBrk) (m' : Machine)
    (hm : m' ∈ (Replay.brkFx dy m k).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = k.e.1 := by
  unfold Replay.brkFx Replay.netTake at hm
  simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
    Replay.settle_machines, (Replay.netClosed_obs dy _ _ _ _).2.2, List.nil_append, List.mem_singleton] at hm
  subst hm
  have hS : ∀ q, q ∈ machineInstants (Replay.settle dy { m with brks := Replay.pruneBrks (k :: m.brks), brkOpen := none }).1 → q ∈ machineInstants m ∨ q = k.e.1 := fun q h => heldBrk_mi m k q (settle_mi dy _ q h)
  have hN : ∀ q, q ∈ machineInstants (Replay.netClosed dy k.s k.e k.day (Replay.settle dy { m with brks := Replay.pruneBrks (k :: m.brks), brkOpen := none }).1).1 → q ∈ machineInstants m ∨ q = k.e.1 := fun q h => by
    rcases netClosed_mi dy k.s k.e k.day _ q h with h | h
    · exact hS q h
    · exact Or.inr h
  rw [mem_machineInstants] at hq
  rcases hq with ⟨b, hb, h⟩ | ⟨k, hk, rfl⟩ | ⟨C', hC', p, hp, rfl⟩
  · exact hN _ ((mem_machineInstants _ _).2 (Or.inl ⟨b, hb, h⟩))
  · exact hN _ ((mem_machineInstants _ _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  · obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hC'
    have hp := pcs_stash k.key _ p hp
    unfold Replay.runOne at hp
    rcases List.mem_append.1 hp with hp | hp
    case inr => exact hN _ ((mem_machineInstants _ _).2 (Or.inr (Or.inr ⟨(Replay.netOne dy k.s k.e k.day C).1, List.mem_map.2 ⟨C, hC, rfl⟩, p, List.mem_append_right _ hp, rfl⟩)))
    rcases List.mem_append.1 hp with hp | hp
    · exact hN _ ((mem_machineInstants _ _).2 (Or.inr (Or.inr ⟨(Replay.netOne dy k.s k.e k.day C).1, List.mem_map.2 ⟨C, hC, rfl⟩, p, List.mem_append_left _ (List.mem_append_left _ hp), rfl⟩)))
    · dsimp only at hp; split at hp
      · exact hS _ ((mem_machineInstants _ _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_right _ hp), rfl⟩)))
      · rcases List.mem_append.1 hp with hp | hp
        · exact hS _ ((mem_machineInstants _ _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_right _ hp), rfl⟩)))
        · exact hS _ ((mem_machineInstants _ _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ (List.mem_filter.1 hp).1), rfl⟩)))

/-- **A held break's queries are instants the machine holds, or its end** (D87, D94, D100). -/
theorem brkFxReads_sub (M : Machine) (k : Replay.HeldBrk) (q : Cal.Instant) (hq : q ∈ brkFxReads M k) :
    q ∈ machineInstants M ∨ q = k.e.1 := by
  unfold brkFxReads at hq
  rcases List.mem_append.1 hq with hq | hq
  · exact heldBrk_mi M k q (settleReads_mi _ q hq)
  · rcases closedReads_mi _ _ _ _ q hq with ⟨C, hC, p, hp, rfl⟩ | h
    · exact Or.inl ((mem_machineInstants M _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), rfl⟩)))
    · exact Or.inr h


theorem stepQueries_sub (dy : Cal.Instant → Nat) (m : Machine) (e : Entry) (q : Cal.Instant)
    (hq : q ∈ stepQueries dy m e) : q ∈ entryInstants e ∨ q ∈ machineInstants m := by
  have hte : e.t.val ∈ entryInstants e := by simp [entryInstants]
  unfold stepQueries at hq
  rcases List.mem_append.1 hq with hq | hq
  · exact Or.inl hq
  cases hev : e.ev <;> simp only [hev] at hq
  case start =>
    split at hq
    · rename_i o _
      rcases startQueries_sub dy _ _ _ _ _ _ _ _ _ _ q hq with h | h
      · exact Or.inl (by rw [h]; exact hte)
      · rcases endMachine_mi m o _ _ q h with h | h
        · exact Or.inr h
        · exact Or.inl (by rw [h]; exact hte)
    · rcases startQueries_sub dy _ _ _ _ _ _ _ _ _ _ q hq with h | h
      · exact Or.inl (by rw [h]; exact hte)
      · exact Or.inr h
  case pause id =>
    split at hq
    · split at hq
      · rename_i b hb _
        have := settleReads_mi _ q hq
        unfold machineInstants at this ⊢
        rw [hb]
        simp only [List.mem_append, List.mem_cons] at this ⊢
        rcases this with (h | ((h | h) | h)) | h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl h))))
        · left; simp only [Option.map_some, Option.toList_some, List.mem_singleton] at h; exact h ▸ hte
        · exact Or.inr (Or.inl (Or.inr (Or.inr h)))
        · exact Or.inr (Or.inr h)
      · simp at hq
    · simp at hq
  case unpause id =>
    split at hq
    · split at hq
      · rcases List.mem_append.1 hq with hq | hq
        · exact Or.inr (blockPaused_mi m q hq)
        · rcases unpaused_mi m _ q (settleReads_mi _ q hq) with h | h
          · exact Or.inr h
          · exact Or.inl (h ▸ hte)
      · simp at hq
    · simp at hq
  case interrupt id =>
    rcases List.mem_append.1 hq with hq | hq
    · exact Or.inr (blockPaused_mi m q hq)
    · rcases interruptMachine_mi m _ _ _ q (settleReads_mi _ q hq) with h | h
      · exact Or.inr h
      · exact Or.inl (h ▸ hte)
  case resume lost dropped =>
    split at hq
    · rcases List.mem_append.1 hq with hq | hq
      · rcases resumed_mi m _ (e.t.val, e.off.val) (fun sp hsp => by cases hsp; rfl) _ q (settleReads_mi _ q hq)
          with h | h
        · exact Or.inr h
        · exact Or.inl (h ▸ hte)
      · rcases closedReads_mi _ _ _ _ q hq with ⟨C, hC, p, hp, rfl⟩ | h
        · exact Or.inr ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, List.mem_append_left _ (List.mem_append_left _ hp), rfl⟩)))
        · exact Or.inl (h ▸ hte)
    · rcases resumed_mi m none (e.t.val, e.off.val) (fun sp hsp => by cases hsp) _ q (settleReads_mi _ q hq) with h | h
      · exact Or.inr h
      · exact Or.inl (h ▸ hte)
  case stop id rem =>
    split at hq
    · split at hq
      · simp only [List.mem_append] at hq
        rcases hq with (hq | hq) | hq
        · exact Or.inr (cutReads_mi m _ q hq)
        · exact Or.inr (blockPaused_mi m q hq)
        · exact Or.inr (cut_mi dy m _ q (runReads_mi _ q hq))
      · simp at hq
    · simp at hq
  case done id est actual went tags ci isPartial =>
    rcases List.mem_append.1 hq with hq | hq
    · split at hq
      · split at hq
        · rcases List.mem_append.1 hq with hq | hq
          · exact Or.inr (cutReads_mi m _ q hq)
          · exact Or.inr (blockPaused_mi m q hq)
        · simp at hq
      · simp at hq
    · obtain ⟨C, hC, p, hp, rfl⟩ := runReads_starts _ q hq
      exact Or.inr (doneClosed_mi dy m e.line _ id actual.val ci C hC p (List.mem_append_left _ (List.mem_append_left _ hp)))
  case brkStart planned where_ =>
    split at hq
    · rename_i t0 hF
      rcases brkFxReads_sub _ _ q hq with h | h
      · exact Or.inr (forget_mi m q h)
      · exact Or.inr (h ▸ firstStart_mi _ _ m t0 hF)
    · rcases List.mem_append.1 hq with hq | hq
      · have h := settleReads_mi _ q hq
        exact Or.inr (forgetIdle_mi m q h)
      · have h := runReads_mi _ q hq
        exact Or.inr (forgetIdle_mi m q h)
  case brk planned actual where_ =>
    have hbk : ∀ (M : Machine) (k : Replay.HeldBrk), k.e = (Replay.heldOf M e (e.t.val, e.off.val) (dy e.t.val) planned.val (actual.map (·.val))).e → (∀ q, q ∈ machineInstants M → q ∈ machineInstants m) → q ∈ giveReads M ++ brkFxReads (Replay.giveBack dy M).1 k →
        q ∈ entryInstants e ∨ q ∈ machineInstants m := fun M k hk hM hq => by
      rcases List.mem_append.1 hq with hq | hq
      · exact Or.inr (hM q (giveReads_mi M q hq))
      rcases brkFxReads_sub _ _ q hq with h | h
      · exact Or.inr (hM q (giveBack_mi dy M q h))
      · left
        rw [hk] at h
        unfold entryInstants brkEndAt?
        simp [hev, h, Replay.heldOf]
    split at hq
    · split at hq
      · exact hbk _ _ (by rfl) (d141Machine_mi m _) hq
      · simp at hq
    · rcases List.mem_append.1 hq with hq | hq; exact hbk m _ (by rfl) (fun _ h => h) hq; (split at hq; exact hbk _ _ (by rfl) (d141Machine_mi m _) hq; simp at hq)
  all_goals simp at hq

/-- **A start's machine holds the old one's instants and the start's stamp** (C3, D99). -/
theorem startArm_mi (dy : Cal.Instant → Nat) (M : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id)
    (pred : Log.U8) (rep : Option Log.U8) (hsw : Log.Num) (sleptMin : Log.U32) (loc : List Char) (m' : Machine)
    (hm : m' ∈ (Replay.startArm dy M line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?)
    (q : Cal.Instant) (hq : q ∈ machineInstants m') : q ∈ machineInstants M ∨ q = t.1 := by
  rw [Replay.startArm_machines] at hm
  simp only [List.mem_singleton] at hm
  subst hm
  rcases startedMachine_mi _ _ t d _ q (settle_mi dy _ q hq) with h | h
  · exact Or.inl (netStart_mi dy t d M q (cut_mi dy _ t q (runNet_mi dy _ q h)))
  · exact Or.inr h

/-- **Every machine a step's arm writes holds only the old machine's instants and the step's stamp — on every event but a `break`.**  This was `arm_mi`'s statement over every event until the owner's D87 (README gap 4137, parity P81): a break inside a running block restarts its clock at the break's END, which is neither (`arm_mi_as_w2_stated_it_is_refuted`), and `arm_mi` is the form that holds.  *Re-proved at D92, D94 and D99 with its statement unchanged*: a settled block's clock runs from its start or the end of a span it nets (`settle_mi`), and every span it nets ends at the step's stamp or at an instant the old machine already holds. -/
theorem arm_mi_of_not_brk (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (hb : ∀ p a w, e.ev ≠ .brk p a w)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = t.1 := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case brk p a w => exact absurd hev (hb p a w)
  case start =>
    split at hm
    · rename_i o _
      have hm := Replay.startEnds_mem dy m o _ t d _ _ _ _ _ _ m' hm
      rcases startArm_mi dy _ _ t d _ _ _ _ _ _ m' hm q hq with h | h
      · exact endMachine_mi m o t _ q h
      · exact Or.inr h
    · exact startArm_mi dy m _ t d _ _ _ _ _ _ m' hm q hq
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        rename_i b hb' _
        have h1 := settle_mi dy _ q hq
        unfold machineInstants at h1 ⊢
        rw [hb']
        simp only [List.mem_append, List.mem_cons] at h1 ⊢
        rcases h1 with (h | ((h | h) | h)) | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl h))))
        · right; simpa using h
        · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
        · exact Or.inl (Or.inr h)
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact unpaused_mi m t q (settle_mi dy _ q hq)
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    exact interruptMachine_mi m t d _ q (settle_mi dy _ q hq)
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton, (Replay.netClosed_obs dy _ _ _ _).2.2] at hm
      subst hm
      rcases netClosed_mi dy _ _ _ _ q hq with hq | hq
      · exact resumed_mi m _ t (fun sp hsp => by cases hsp; rfl) _ q (settle_mi dy _ q hq)
      · exact Or.inr hq
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact resumed_mi m none t (fun sp hsp => by cases hsp) _ q (settle_mi dy _ q hq)
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (cut_mi dy m t q (runNet_mi dy _ q hq))
      · simp at hm
    · simp at hm
  case extend id by_ =>
    -- D108: the old machine, its open block's `ext` grown — no instant moves.
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, hb, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    left
    have he : machineInstants { m with block := some { b with ext := b.ext + by_.val } } = machineInstants m := by
      unfold machineInstants; rw [hb]
    rw [he] at hq; exact hq
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    left
    have hq := runNet_mi dy _ q hq
    obtain ⟨k1, k2⟩ := doneClose_keeps dy m t id actual.val went
    rw [mem_machineInstants] at hq
    rcases hq with ⟨b', hb', h⟩ | ⟨k, hk, rfl⟩ | ⟨C, hC, pc, hpc, rfl⟩
    · change (Replay.doneClose dy m t id actual.val went).1.block = some b' at hb'
      rcases k1 with k1 | k1
      · rw [k1] at hb'; cases hb'
      · rw [k1] at hb'; exact (mem_machineInstants m _).2 (Or.inl ⟨b', hb', h⟩)
    · change k ∈ (Replay.doneClose dy m t id actual.val went).1.brks at hk
      rw [k2] at hk; exact (mem_machineInstants m _).2 (Or.inr (Or.inl ⟨k, hk, rfl⟩))
    · exact doneClosed_mi dy m e.line t id actual.val ci C hC pc hpc
  case brkStart pl w =>
    split at hm
    · rename_i t0 hF
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      rcases brkFx_mi dy _ ⟨t, t0, d, e.line, pl.val, w, t0⟩ m' hm' q hq with h | h
      · exact Or.inl (forget_mi m q h)
      · rw [h]; exact Or.inl (firstStart_mi t d m t0 hF)
    · unfold Replay.brkStartArm at hm
      simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
      subst hm
      have h := settle_mi dy _ q (runNet_mi dy _ q hq)
      exact Or.inl (forgetIdle_mi m q h)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm
-- (W-54 track K, README gap 5878: a duplicate law stated under takeFx's name was deleted here; the blank lines keep check 9's recorded pin sites below where they were)












/-- **Every machine a step's arm writes holds only the old block's instants, the step's stamp, and a break's end** — the owner's D87 (README gap 4137, parity P81): a break inside a running block restarts its clock at the break's end (`Replay.brkFx`).  Restated at D87 from W2's two cases, which hold on every other event (`arm_mi_of_not_brk`). -/
theorem arm_mi (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = t.1 ∨ q ∈ (brkEndAt? e t.1).toList := by
  by_cases hb : ∃ p a w, e.ev = .brk p a w
  · obtain ⟨p, a, w, hev⟩ := hb
    have hbk : ∀ (M : Machine) (k : Replay.HeldBrk), k.e = (Replay.heldOf M e t d p.val (a.map (·.val))).e → (∀ q, q ∈ machineInstants M → q ∈ machineInstants m) → m' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k).filterMap Effect.machineOf? →
        q ∈ machineInstants m ∨ q = t.1 ∨ q ∈ (brkEndAt? e t.1).toList := fun M k hk hM hm => by
      unfold Replay.brkArmK at hm
      rw [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil,
        List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm
      rcases brkFx_mi dy _ _ m' hm q hq with h | h
      · exact Or.inl (hM q (giveBack_mi dy M q h))
      · right; right
        rw [hk] at h
        unfold brkEndAt?
        simp only [hev, Option.toList_some, List.mem_singleton, h]
        rfl
    unfold Replay.arm at hm; simp only [hev] at hm
    have hcase : (∃ x0, m' ∈ (Replay.d141Arm dy m x0 e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) ∨ m' ∈ (Replay.brkArm dy m e t d p.val (a.map (·.val))).filterMap Effect.machineOf? := by split at hm; (rcases Replay.brkOwn_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm); (rcases Replay.brkLine_machines hm with ⟨x0, -, hm⟩ | hm; exact Or.inl ⟨x0, hm⟩; exact Or.inr hm)
    rcases hcase with ⟨x0, hm⟩ | hm
    · unfold Replay.d141Arm at hm; split at hm
      · simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.durationOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.energyOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm
        exact hbk _ _ (by rfl) (d141Machine_mi m _) hm
      · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; exact Or.inl (letGo_mi m _ q hq)
    · exact hbk m _ (by rfl) (fun _ h => h) hm
  · rcases arm_mi_of_not_brk dy sl m e t d (fun p a w h => hb ⟨p, a, w, h⟩) m' hm q hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **A step's machine holds only the old block's instants and the step's own instants** (`entryInstants`: its stamp, and — the owner's D87 — a break's end).  Restated at D87 from "the old block's instants and the step's stamp", which a break inside a running block refutes (`stepWith_mi_as_w2_stated_it_is_refuted`). -/
theorem stepWith_mi (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (q : Cal.Instant) (hq : q ∈ machineInstants (Replay.stepWith z dy sl st e).machine) :
    q ∈ machineInstants st.machine ∨ q ∈ entryInstants e := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  unfold Replay.stepWith at hq
  rw [h3] at hq
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z st.machine e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  rw [hfx] at hq
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => rw [hl] at hq; exact Or.inl hq
  | some m' =>
    rw [hl, Option.getD_some] at hq
    rcases arm_mi dy sl st.machine e _ _ m' (List.mem_of_getLast? hl) q hq with h | h | h
    · exact Or.inl h
    · right; unfold entryInstants; exact List.mem_cons.2 (Or.inl h)
    · right; unfold entryInstants; exact List.mem_cons_of_mem _ (List.mem_append_right _ h)
/-- **A fold's queries are its entries' instants and its start state's block instants.** -/
theorem foldQueries_sub (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (q : Cal.Instant), q ∈ foldQueries z dy sl st sv →
      q ∈ machineInstants st.machine ∨ q ∈ sv.flatMap entryInstants
  | [], _, _, h => by simp [foldQueries] at h
  | e :: sv, st, q, h => by
    unfold foldQueries at h
    rcases List.mem_append.1 h with h | h
    · rcases stepQueries_sub dy st.machine e q h with h | h
      · exact Or.inr (List.mem_append_left _ h)
      · exact Or.inl h
    · rcases foldQueries_sub z dy sl sv _ q h with h | h
      · rcases stepWith_mi z dy sl st e q h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_append_left _ h)
      · exact Or.inr (List.mem_append_right _ h)

/-- **The machine after a fold holds its start's block instants and its entries' own instants** (their stamps, and — D87 — a break's end). -/
theorem foldl_mi (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State) (q : Cal.Instant), q ∈ machineInstants (sv.foldl (Replay.stepWith z dy sl) st).machine →
      q ∈ machineInstants st.machine ∨ q ∈ sv.flatMap entryInstants
  | [], _, _, h => Or.inl h
  | e :: sv, st, q, h => by
    rw [List.foldl_cons] at h
    rcases foldl_mi z dy sl sv _ q h with h | h
    · rcases stepWith_mi z dy sl st e q h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · exact Or.inr (List.mem_append_right _ h)

/-! ### D94's bound (README gap 4506): a machine holds the breaks of at most `maxKeepDays + 1` ledger days The machine holds every break it steps (`Replay.Machine.brks`), and every break it holds is within `maxKeepDays` ledger days of the newest one held (`Replay.pruneBrks`).  So a checkpoint — which carries the machine (`Seal.cMachine`) — holds the breaks of at most `maxKeepDays + 1` ledger days, however long the log: it does not grow with the log. -/

theorem foldl_maxDay_le (B : Nat) : ∀ (l : List Replay.HeldBrk) (a : Nat), a ≤ B → (∀ x ∈ l, x.day ≤ B) →
    l.foldl (fun a x => max a x.day) a ≤ B
  | [], _, ha, _ => ha
  | x :: l, a, ha, hl => by
    rw [List.foldl_cons]
    exact foldl_maxDay_le B l _ (Nat.max_le.2 ⟨ha, hl x List.mem_cons_self⟩)
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem le_foldl_maxDay : ∀ (l : List Replay.HeldBrk) (a : Nat), a ≤ l.foldl (fun a x => max a x.day) a ∧
    ∀ x ∈ l, x.day ≤ l.foldl (fun a x => max a x.day) a
  | [], a => ⟨Nat.le_refl _, fun x hx => absurd hx List.not_mem_nil⟩
  | x :: l, a => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := le_foldl_maxDay l (max a x.day)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 y hy

/-- **What `pruneBrks` keeps is within `maxKeepDays` ledger days of the newest break it keeps.** -/
theorem pruneBrks_within (l : List Replay.HeldBrk) :
    ∀ k ∈ Replay.pruneBrks l,
      (Replay.pruneBrks l).foldl (fun a x => max a x.day) 0 ≤ k.day + maxKeepDays := by
  intro k hk
  have hk' := hk
  rw [pruneBrks_is_bounded_by_maxKeepDays] at hk'
  simp only [List.mem_filter, decide_eq_true_eq] at hk'
  refine Nat.le_trans ?_ hk'.2
  exact foldl_maxDay_le _ _ 0 (Nat.zero_le _) (fun x hx => (le_foldl_maxDay l 0).2 x (Replay.mem_pruneBrks hx))

/-- **Every machine an arm writes holds the old machine's breaks, or `pruneBrks` over one more.** -/
theorem arm_brks (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) :
    m'.brks = m.brks ∨ (∃ k, m'.brks = Replay.pruneBrks (k :: m.brks)) ∨
      ∃ k x, (∃ p a w, e.ev = .brk p a w ∧ (Replay.findEnded m t = some x ∨ (Replay.findEnded m t = none ∧ m.brkOpen = none ∧ Replay.findFin m t p.val = some x)) ∧
        Replay.d141Ok m x (Replay.brkEnd t p.val (a.map (·.val))) d = true) ∧
        m'.brks = Replay.pruneBrks (k :: m.brks.erase x.hb) := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start id pred rep hsw sleptMin loc _ _ =>
    have hS : ∀ M, ∀ m' ∈ (Replay.startArm dy M e.line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?,
        m'.brks = M.brks := by
      intro M m' hm
      rw [Replay.startArm_machines] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      rw [(Replay.settle_keeps dy _).2.2.1]
      exact (Replay.runNet_keeps dy _).2.2.1.trans ((Replay.cut_brk dy _ t).trans (Replay.netStart_keeps dy _ _ M).2.2.1)
    split at hm
    · rename_i o _
      have hm := Replay.startEnds_mem dy m o _ t d _ _ _ _ _ _ m' hm
      exact Or.inr (Or.inl ⟨_, (hS (Replay.endMachine m o t e.line) m' hm).trans rfl⟩)
    · exact Or.inl (hS m m' hm)
  case pause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, List.nil_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
          Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        exact Or.inl ((Replay.settle_keeps dy _).2.2.1)
      · simp at hm
    · simp at hm
  case unpause id =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
        subst hm
        left
        rw [(Replay.settle_keeps dy _).2.2.1]
        exact closePauseM_brks m t
      · simp at hm
    · simp at hm
  case interrupt id =>
    simp only [List.filterMap_append, (Replay.closePause_obs dy m t).2.2, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    left
    rw [(Replay.settle_keeps dy _).2.2.1]
    have h1 := closePauseM_brks m t
    unfold Replay.interruptMachine
    split <;> simp only [h1]
  case resume lost dropped =>
    split at hm
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton, (Replay.netClosed_obs dy _ _ _ _).2.2] at hm
      subst hm
      exact Or.inl ((Replay.netClosed_keeps dy _ _ _ _).2.2.1.trans (Replay.settle_keeps dy _).2.2.1)
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl ((Replay.settle_keeps dy _).2.2.1)
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, Replay.runNet_machines, List.nil_append,
          List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl ((Replay.runNet_keeps dy _).2.2.1.trans (Replay.cut_brk dy m t))
      · simp at hm
    · simp at hm
  case extend id by_ =>
    simp only [List.filterMap_cons, Effect.machineOf?] at hm
    obtain ⟨b, hb, rfl⟩ := Replay.extendFx_machines m id by_.val m' hm
    exact Or.inl rfl
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    left
    rw [(Replay.runNet_keeps dy _).2.2.1]
    show (Replay.doneClose dy m t id actual.val went).1.brks = m.brks
    unfold Replay.doneClose
    repeat' split
    all_goals rfl
  case brk p a w =>
    have hbk : ∀ (M : Machine) (k0 : Replay.HeldBrk), m' ∈ (Replay.brkArmK dy M e t d p.val (a.map (·.val)) k0).filterMap Effect.machineOf? → ∃ k, m'.brks = Replay.pruneBrks (k :: M.brks) := fun M k0 hm => by
      unfold Replay.brkArmK at hm
      rw [List.filterMap_append, Replay.reachFx_filterMap Effect.machineOf? (fun _ _ => rfl), List.append_nil, List.filterMap_append, (Replay.brkDay_obs3 M e t d _ _).1, List.append_nil,
        List.filterMap_append, (Replay.giveBack_obs dy M).2.2, List.nil_append] at hm
      have h := Replay.brkFx_brk dy _ _ m' hm
      rw [(Replay.giveBack_keeps dy M).2.2.1] at h
      exact ⟨_, h⟩
    have hcase : (∃ x, (Replay.findEnded m t = some x ∨ (Replay.findEnded m t = none ∧ m.brkOpen = none ∧ Replay.findFin m t p.val = some x)) ∧ m' ∈ (Replay.d141Arm dy m x e t d p.val (a.map (·.val))).filterMap Effect.machineOf?) ∨ m' ∈ (Replay.brkArm dy m e t d p.val (a.map (·.val))).filterMap Effect.machineOf? := by split at hm; (rcases Replay.brkOwn_machines hm with ⟨x0, hx, hm⟩ | hm; exact Or.inl ⟨x0, Or.inl hx, hm⟩; exact Or.inr hm); (rename_i ho; rcases Replay.brkLine_machines hm with ⟨x0, hx, hm⟩ | hm; exact Or.inl ⟨x0, hx.imp id (fun h' => ⟨h'.1, ho, h'.2.1⟩), hm⟩; exact Or.inr hm)
    rcases hcase with ⟨x, hK, hm⟩ | hm
    · unfold Replay.d141Arm at hm; split at hm
      · rename_i hg
        simp only [List.filterMap_append, Replay.growFx_filterMap Effect.machineOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.durationOf? (fun _ _ => rfl), Replay.growFx_filterMap Effect.energyOf? (fun _ _ => rfl), List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.nil_append] at hm
        obtain ⟨k', h⟩ := hbk _ _ hm; exact Or.inr (Or.inr ⟨k', x, ⟨p, a, w, rfl, hK, hg⟩, h⟩)
      · simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm; subst hm; exact Or.inl rfl
    · obtain ⟨k', h⟩ := hbk _ _ hm; exact Or.inr (Or.inl ⟨k', h⟩)
  case brkStart pl w =>
    split at hm
    · rename_i t0 _
      have hm' := Replay.endBrkFx_mem dy m ⟨t, pl.val, w, d⟩ t0 e.line m' hm
      exact Or.inr (Or.inl ⟨_, Replay.brkFx_brk dy { Replay.forget m with ended := Replay.pushEnded (Replay.endingOf ⟨t, pl.val, w, d⟩ t0 e.line) m } ⟨t, t0, d, e.line, pl.val, w, t0⟩ m' hm'⟩)
    · unfold Replay.brkStartArm at hm
      simp only [List.filterMap_append, Replay.settle_machines, Replay.runNet_machines, Effect.machineOf?,
        List.filterMap_cons, List.filterMap_nil, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl (((Replay.runNet_keeps dy _).2.2.1.trans (Replay.settle_keeps dy _).2.2.1).trans (Replay.forgetIdle_keeps m).2.2.2.1)
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **`arm_brks` as W-53 track K stated it, refuted** (the W-54 auditor, README gap 5877): its third case required an ending at the line's stamp; the finished break 09:30–09:40 re-timed to 09:34 by a later line has none (D147). -/
theorem arm_brks_as_w53_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat) (m' : Machine),
      m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf? →
      m'.brks = m.brks ∨ (∃ k, m'.brks = Replay.pruneBrks (k :: m.brks)) ∨
      ∃ k x, (∃ p a w, e.ev = .brk p a w ∧ Replay.findEnded m t = some x ∧ Replay.d141Ok m x (Replay.brkEnd t p.val (a.map (·.val))) d = true) ∧
        m'.brks = Replay.pruneBrks (k :: m.brks.erase x.hb) := by
  intro h
  let x0   : Replay.HeldBrk := ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924370800, 0⟩, ⟨false, 0⟩), 739865, 1, 10, none, (⟨63924370800, 0⟩, ⟨false, 0⟩)⟩
  let M : Machine := ⟨none, none, none, [x0], none, [], []⟩
  let e := Replay.bE 2 63924370200 (.brk 10 (some 4) none)
  let t : Replay.At := (⟨63924370200, 0⟩, ⟨false, 0⟩)
  let k1   : Replay.HeldBrk := ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924370440, 0⟩, ⟨false, 0⟩), 739865, 2, 10, none, (⟨63924370800, 0⟩, ⟨false, 0⟩)⟩
  have hl : ∀ m' ∈ (Replay.arm (fun _ => 739865) (fun _ => none) M e t 739865).filterMap Effect.machineOf?, m'.brks = [k1] := by decide
  have hn : (Replay.arm (fun _ => 739865) (fun _ => none) M e t 739865).filterMap Effect.machineOf? ≠ [] := by decide
  have hE : Replay.findEnded M t = none := by decide
  obtain ⟨m', hm'⟩ := List.exists_mem_of_ne_nil _ hn
  rcases h (fun _ => 739865) (fun _ => none) M e t 739865 m' hm' with h1 | ⟨k, h2⟩ | ⟨k, x, ⟨p, a, w, -, hf, -⟩, -⟩
  · rw [hl m' hm'] at h1; revert h1; decide
  · rw [hl m' hm'] at h2; exact Replay.pruneBrks_pair_ne k x0 k1 (by decide) rfl h2.symm
  · rw [hE] at hf; cases hf

/-- **A step keeps the bound**: the machine after it holds the old one's breaks, or what `pruneBrks` keeps. -/
theorem stepWith_brks_within (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : ∀ k ∈ st.machine.brks, st.machine.brks.foldl (fun a x => max a x.day) 0 ≤ k.day + maxKeepDays) :
    ∀ k ∈ (Replay.stepWith z dy sl st e).machine.brks,
      (Replay.stepWith z dy sl st e).machine.brks.foldl (fun a x => max a x.day) 0 ≤ k.day + maxKeepDays := by
  obtain ⟨-, -, h3⟩ := Replay.applyEffects_obs (Replay.effectsWith z dy sl st e) st
  have hfx : (Replay.effectsWith z dy sl st e).filterMap Effect.machineOf?
      = (Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf? := by
    unfold Replay.effectsWith
    simp [List.filterMap_cons, List.filterMap_append, Effect.machineOf?,
      (Replay.completionArm_obs z st.machine e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  unfold Replay.stepWith
  rw [h3, hfx]
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => exact h
  | some m' =>
    rw [Option.getD_some]
    rcases arm_brks dy sl st.machine e _ _ m' (List.mem_of_getLast? hl) with hb | ⟨k, hb⟩ | ⟨k, x, -, hb⟩
    · rw [hb]; exact h
    · rw [hb]; exact pruneBrks_within _
    · rw [hb]; exact pruneBrks_within _

/-- **D94's bound, over every fold** (README gap 4506): a fold from a machine within the bound holds only breaks within `maxKeepDays` ledger days of the newest one held — the replay's (from `State.init`, which holds none), and so every checkpoint's (`ckpt_machine`). -/
theorem foldl_brks_within (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) (st : State),
      (∀ k ∈ st.machine.brks, st.machine.brks.foldl (fun a x => max a x.day) 0 ≤ k.day + maxKeepDays) →
      ∀ k ∈ (sv.foldl (Replay.stepWith z dy sl) st).machine.brks,
        (sv.foldl (Replay.stepWith z dy sl) st).machine.brks.foldl (fun a x => max a x.day) 0
          ≤ k.day + maxKeepDays
  | [], _, h => h
  | e :: sv, st, h => by
    rw [List.foldl_cons]
    exact foldl_brks_within z dy sl sv _ (stepWith_brks_within z dy sl st e h)

/-- **The replay's machine holds the breaks of at most `maxKeepDays + 1` ledger days** — every fold from the empty state. -/
theorem a_replay_holds_breaks_within_maxKeepDays_of_the_newest (z : Cal.Tz) (dy : Cal.Instant → Nat)
    (sl : Nat → Option Nat) (sv : List Entry) (n : Nat) :
    ∀ k ∈ (sv.foldl (Replay.stepWith z dy sl) (State.init n)).machine.brks,
      (sv.foldl (Replay.stepWith z dy sl) (State.init n)).machine.brks.foldl (fun a x => max a x.day) 0
        ≤ k.day + maxKeepDays :=
  foldl_brks_within z dy sl sv _ (fun k hk => by simp [State.init] at hk)

/-! ### W2's two machine-instant laws, refuted as W2 stated them (the owner's D87, README gap 4137) A `break` stepped while the open block's clock runs restarts the clock at the break's END (`Replay.brkFx`), an instant that is neither the old block's nor the step's stamp.  The two laws below are W2's statements; `arm_mi` and `stepWith_mi` are the forms that hold (the break's end is one of the entry's own instants, `entryInstants`).  The witness: `a` running since 09:00 (nothing banked), a twenty-minute `break` at 09:30. -/

/-- **`arm_mi` as W2 stated it is refuted**: the break's machine holds 09:50. -/
theorem arm_mi_as_w2_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
      (m' : Machine), m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf? →
      ∀ q ∈ machineInstants m', q ∈ machineInstants m ∨ q = t.1 := by
  intro h
  have := h (fun _ => 739865) (fun _ => none)
    ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none, 0, none, 739865,
      [], [], 0⟩, none, none, [], none, [], []⟩
    (Replay.bE 2 63924370200 (.brk 20 (some 20) none)) (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865
    ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924371400, 0⟩, ⟨false, 0⟩), false, none, 30, none, 739865,
      [], [⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), (⟨63924370200, 0⟩, ⟨false, 0⟩), 739865⟩], 0⟩,
      none, none, [⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924371400, 0⟩, ⟨false, 0⟩), 739865, 2, 20, none, (⟨63924371400, 0⟩, ⟨false, 0⟩)⟩], none, [], []⟩ (by decide)
    ⟨63924371400, 0⟩ (by decide)
  revert this
  decide

/-- **`stepWith_mi` as W2 stated it is refuted**: a step's machine can hold the break's end. -/
theorem stepWith_mi_as_w2_stated_it_is_refuted :
    ¬ ∀ (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) (q : Cal.Instant),
      q ∈ machineInstants (Replay.stepWith z dy sl st e).machine → q ∈ machineInstants st.machine ∨ q = e.t.val := by
  intro h
  have := h Replay.utcZone (fun _ => 739865) (fun _ => none)
    { Replay.State.init 1 with machine :=
      ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none, 0, none, 739865,
        [], [], 0⟩, none, none, [], none, [], []⟩ }
    (Replay.bE 2 63924370200 (.brk 20 (some 20) none)) ⟨63924371400, 0⟩ (by decide)
  revert this
  decide

/-- **A machine holds the end of the last break it stepped** (the owner's D92, README gap 4241): with no block open and the span `[09:30, 09:50]` held, its one instant is 09:50 — where a clock a later step starts inside that break begins, and where the step that closes it reads the day index (`Replay.settle`, the owner's D99). -/
theorem a_machine_holds_its_last_breaks_end :
    machineInstants ⟨none, none, none, [⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924371400, 0⟩, ⟨false, 0⟩), 739865, 0, 0, none, (⟨63924371400, 0⟩, ⟨false, 0⟩)⟩], none, [], []⟩
      = [⟨63924371400, 0⟩] := by
  decide

/-- **…and the end of every break it holds** (the owner's D94, README gap 4506): with `[09:00, 09:30]` and `[09:40, 09:45]` held, its instants are both ends — a clock a later step starts inside the earlier break begins at 09:30, and a stretch closed across the later one resumes at 09:45. -/
theorem a_machine_holds_the_end_of_every_break_it_holds :
    machineInstants ⟨none, none, none, [⟨(⟨63924370800, 0⟩, ⟨false, 0⟩), (⟨63924371100, 0⟩, ⟨false, 0⟩), 739865, 0, 0, none, (⟨63924371100, 0⟩, ⟨false, 0⟩)⟩,
      ⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), (⟨63924370200, 0⟩, ⟨false, 0⟩), 739865, 0, 0, none, (⟨63924370200, 0⟩, ⟨false, 0⟩)⟩], none, [], []⟩
      = [⟨63924371100, 0⟩, ⟨63924370200, 0⟩] := by
  decide

end Seal
end Tm
