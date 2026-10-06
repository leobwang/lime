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
    (o : Option Replay.EnergyObs) (hi : m'.interrupt = m.interrupt) (hb : m'.brks = m.brks) :
    settleReads (Replay.startedMachine m' id t d o) = settleReads (Replay.startedMachine m id t d o) := by
  unfold settleReads
  simp [Replay.startedMachine, Replay.openPieces, Replay.blockSpans, Replay.openStop, hi, hb]

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
  case start =>
    rw [cut_congr dy₁ dy₂ m (e.t.val, e.off.val) (fun q hq => by
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | hq) | hq
      · exact h q (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hq)))
      · exact h q (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hq)))
      · exact hE q (by simp [entryInstants, hq]))]
    rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_right _ (by
      rwa [settleReads_startedMachine m _ _ _ _ _ (cut_interrupt dy₂ m _) (Replay.cut_brk dy₂ m _)] at hq))))]
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
      rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ hq))]
    · rename_i hi
      simp only [hi] at h ⊢
      rw [settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ hq))]
  case stop id rem =>
    split
    · split
      · rename_i b hb hc
        simp only [hb] at h
        rw [if_pos hc] at h
        rw [cut_congr dy₁ dy₂ m (e.t.val, e.off.val) (fun q hq => by
          simp only [List.mem_append, List.mem_singleton] at hq
          rcases hq with (hq | hq) | hq
          · exact h q (List.mem_append_right _ (List.mem_append_left _ hq))
          · exact h q (List.mem_append_right _ (List.mem_append_right _ hq))
          · exact hE q (by simp [entryInstants, hq]))]
      · rfl
    · rfl
  case done id est actual went tags ci isPartial =>
    unfold Replay.doneFx Replay.creditFx
    rw [doneClose_congr dy₁ dy₂ m (e.t.val, e.off.val) id actual.val went (fun b hb hid q hq => by
      simp only [hb] at h; rw [if_pos hid] at h; exact h q (List.mem_append_right _ hq))]
    rw [doneClosed_congr dy₁ dy₂ m e.line (e.t.val, e.off.val) id actual.val ci (fun b hb hid q hq => by
      simp only [hb] at h; rw [if_pos hid] at h; exact h q (List.mem_append_right _ (List.mem_append_left _ hq)))
      (hE e.t.val (by simp [entryInstants]))]
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
    have h1 := settle_congr dy₁ dy₂ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_left _ hq)))
    have h2 : Replay.dayArm dy₁ sl e (e.t.val, e.off.val) (dy₂ e.t.val)
        = Replay.dayArm dy₂ sl e (e.t.val, e.off.val) (dy₂ e.t.val) := by
      unfold Replay.dayArm; simp only [hev]
    unfold Replay.brkFx
    simp only [h1, h2]
    rw [netClosed_congr dy₁ dy₂ _ _ _ _ (fun q hq => h q (List.mem_append_right _ (List.mem_append_right _ (by
      rwa [Replay.settle_closed] at hq))))]
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
every closed block it holds, where a piece a late break re-draws for one begins (or at the break's end). -/
def machineInstants (m : Machine) : List Cal.Instant :=
  (match m.block with
   | some b => b.started.1 :: ((b.since.map (·.1)).toList ++ (b.pausedAt.map (·.1)).toList ++ b.idle.map (·.2.1))
   | none => []) ++ (m.brks.map (·.e.1) ++ m.closed.flatMap (fun C => C.drawn.map (·.s.1)))

/-- **What a machine holds, by where it is held** (D99). -/
theorem mem_machineInstants (m : Machine) (q : Cal.Instant) :
    q ∈ machineInstants m ↔
      (∃ b, m.block = some b ∧ (b.started.1 = q ∨ (∃ x, b.since = some x ∧ x.1 = q) ∨
        (∃ x, b.pausedAt = some x ∧ x.1 = q) ∨ (∃ sp ∈ b.idle, sp.2.1 = q))) ∨
      ((∃ k ∈ m.brks, k.e.1 = q) ∨ (∃ C ∈ m.closed, ∃ p ∈ C.drawn, p.s.1 = q)) := by
  unfold machineInstants
  cases hb : m.block with
  | none => simp [List.mem_flatMap]
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

theorem settleReads_mi (m : Machine) (q : Cal.Instant) (hq : q ∈ settleReads m) : q ∈ machineInstants m := by
  unfold settleReads at hq
  cases hb : m.block with
  | none => rw [hb] at hq; cases hq
  | some b =>
    rw [hb] at hq
    exact redrawReads_mi b m hb _ q hq

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

theorem heldBrk_mi (m : Machine) (t E : Replay.At) (d : Nat) (q : Cal.Instant)
    (hq : q ∈ machineInstants { m with brks := Replay.pruneBrks (⟨t, E, d⟩ :: m.brks), brkOpen := none }) :
    q ∈ machineInstants m ∨ q = E.1 := by
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

theorem stepQueries_sub (dy : Cal.Instant → Nat) (m : Machine) (e : Entry) (q : Cal.Instant)
    (hq : q ∈ stepQueries dy m e) : q ∈ entryInstants e ∨ q ∈ machineInstants m := by
  have hte : e.t.val ∈ entryInstants e := by simp [entryInstants]
  unfold stepQueries at hq
  rcases List.mem_append.1 hq with hq | hq
  · exact Or.inl hq
  cases hev : e.ev <;> simp only [hev] at hq
  case start =>
    simp only [List.mem_append] at hq
    rcases hq with (hq | hq) | hq
    · exact Or.inr (cutReads_mi m _ q hq)
    · exact Or.inr (blockPaused_mi m q hq)
    · rcases startedMachine_mi m _ _ _ _ q (settleReads_mi _ q hq) with h | h
      · exact Or.inr h
      · exact Or.inl (h ▸ hte)
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
    · rcases resumed_mi m _ (e.t.val, e.off.val) (fun sp hsp => by cases hsp; rfl) _ q (settleReads_mi _ q hq) with h | h
      · exact Or.inr h
      · exact Or.inl (h ▸ hte)
    · rcases resumed_mi m none (e.t.val, e.off.val) (fun sp hsp => by cases hsp) _ q (settleReads_mi _ q hq) with h | h
      · exact Or.inr h
      · exact Or.inl (h ▸ hte)
  case stop id rem =>
    split at hq
    · split at hq
      · rcases List.mem_append.1 hq with hq | hq
        · exact Or.inr (cutReads_mi m _ q hq)
        · exact Or.inr (blockPaused_mi m q hq)
      · simp at hq
    · simp at hq
  case done =>
    split at hq
    · split at hq
      · rcases List.mem_append.1 hq with hq | hq
        · exact Or.inr (cutReads_mi m _ q hq)
        · exact Or.inr (blockPaused_mi m q hq)
      · simp at hq
    · simp at hq
  case brk planned actual where_ =>
    rcases List.mem_append.1 hq with hq | hq
    · rcases heldBrk_mi m _ _ _ q (settleReads_mi _ q hq) with h | h
      · exact Or.inr h
      · left
        unfold entryInstants brkEndAt?
        simp [hev, h]
    · rcases closedReads_mi _ _ _ _ q hq with ⟨C, hC, p, hp, rfl⟩ | h
      · exact Or.inr ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, hp, rfl⟩)))
      · left
        unfold entryInstants brkEndAt?
        simp [hev, h]
  all_goals simp at hq

theorem doneFx_machines (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id)
    (est actual : Nat) (went : Option Log.U8) (tags : List (List Char)) (ci : Log.U8) (isPartial : Bool) :
    (Replay.doneFx dy m line t d id est actual went tags ci isPartial).filterMap Effect.machineOf?
      = [{ (Replay.doneClose dy m t id actual went).1 with
          closed := Replay.doneClosed dy m line t id actual ci }] := by
  unfold Replay.doneFx
  simp only [List.filterMap_cons, Effect.machineOf?, List.filterMap_append,
    (Replay.doneClose_obs dy m t id actual went).2.2]
  by_cases ha : 0 < actual <;> by_cases hp : isPartial = true <;> simp [ha, hp, Replay.creditFx, Effect.machineOf?]

/-- **Where a cut's pieces begin, the machine holds** (D99). -/
theorem cutPieces_mi (b : Block) (m : Machine) (hb : m.block = some b) (t : Replay.At) (q : Replay.At × Replay.At)
    (hq : q ∈ Replay.cutPieces b m t) : q.1.1 ∈ machineInstants m := by
  unfold Replay.cutPieces Replay.pieces at hq
  exact piece_start_mi b m hb _ _ rfl _ q hq

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
      · obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy b.id b.drawn _ pc hpc
        rw [hpq]
        exact cutPieces_mi b m hb t q' hq'
      · exact (mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩))
  · exact hq

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
    unfold Replay.netOne at hpc
    split at hpc
    · exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, pc, hpc, rfl⟩)))
    · obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy C.id C.drawn _ pc hpc
      rcases Replay.cutOut_starts s e C.spans q' hq' with ⟨r, hr, hre⟩ | h
      · unfold Replay.Closed.spans at hr
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
        exact Or.inl ((mem_machineInstants m _).2 (Or.inr (Or.inr ⟨C, hC, p, hp, by rw [hpq, hre]⟩)))
      · exact Or.inr (by rw [hpq, h])

/-- **The closed blocks a `done` leaves begin where the machine already holds** (the owner's D100). -/
theorem doneClosed_mi (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (id : Log.Id)
    (actual : Nat) (ci : Log.U8) (C : Replay.Closed) (hC : C ∈ Replay.doneClosed dy m line t id actual ci)
    (p : Replay.Piece) (hp : p ∈ C.drawn) : p.s.1 ∈ machineInstants m := by
  unfold Replay.doneClosed at hC
  cases hb : m.block with
  | some b =>
    rw [hb] at hC
    simp only at hC
    split at hC
    · rcases List.mem_cons.1 (Replay.mem_pruneClosed hC) with rfl | hC
      · obtain ⟨q', hq', hpq⟩ := Replay.redraw_fst_starts dy b.id b.drawn _ p hp
        rw [hpq]; exact cutPieces_mi b m hb t q' hq'
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

/-- **Every machine a step's arm writes holds only the old machine's instants and the step's stamp — on every event but
a `break`.**  This was `arm_mi`'s statement over every event until the owner's D87 (README gap 4137, parity P81): a break
inside a running block restarts its clock at the break's END, which is neither (`arm_mi_as_w2_stated_it_is_refuted`), and
`arm_mi` is the form that holds.  *Re-proved at D92, D94 and D99 with its statement unchanged*: a settled block's clock
runs from its start or the end of a span it nets (`settle_mi`), and every span it nets ends at the step's stamp or at an
instant the old machine already holds. -/
theorem arm_mi_of_not_brk (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At)
    (d : Nat) (hb : ∀ p a w, e.ev ≠ .brk p a w)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = t.1 := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case brk p a w => exact absurd hev (hb p a w)
  case start =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    rcases startedMachine_mi _ _ t d _ q (settle_mi dy _ q hq) with h | h
    · exact Or.inl (cut_mi dy m t q h)
    · exact Or.inr h
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
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact resumed_mi m _ t (fun sp hsp => by cases hsp; rfl) _ q (settle_mi dy _ q hq)
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact resumed_mi m none t (fun sp hsp => by cases hsp) _ q (settle_mi dy _ q hq)
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (cut_mi dy m t q hq)
      · simp at hm
    · simp at hm
  case extend id by_ => simp [Effect.machineOf?] at hm
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    left
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
    simp only [Effect.machineOf?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inl hq
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

/-- **A break's machine holds the old machine's instants and the break's end** (D87, D92, D94, D99): the break is held
with the ones before it (`Replay.pruneBrks`), whose ends are `E` and the old machine's, and the block settled over them
adds no instant (`settle_mi`). -/
theorem brkFx_mi (dy : Cal.Instant → Nat) (m : Machine) (t E : Replay.At) (d : Nat) (m' : Machine)
    (hm : m' ∈ (Replay.brkFx dy m t E d).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = E.1 := by
  unfold Replay.brkFx at hm
  simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
    Replay.settle_machines, (Replay.netClosed_obs dy _ _ _ _).2.2, List.nil_append, List.mem_singleton] at hm
  subst hm
  rcases netClosed_mi dy t E d _ q hq with h | h
  · exact heldBrk_mi m t E d q (settle_mi dy _ q h)
  · exact Or.inr h

/-- **Every machine a step's arm writes holds only the old block's instants, the step's stamp, and a break's end** —
the owner's D87 (README gap 4137, parity P81): a break inside a running block restarts its clock at the break's end
(`Replay.brkFx`).  Restated at D87 from W2's two cases, which hold on every other event (`arm_mi_of_not_brk`). -/
theorem arm_mi (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
    (m' : Machine) (hm : m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf?) (q : Cal.Instant)
    (hq : q ∈ machineInstants m') : q ∈ machineInstants m ∨ q = t.1 ∨ q ∈ (brkEndAt? e t.1).toList := by
  by_cases hb : ∃ p a w, e.ev = .brk p a w
  · obtain ⟨p, a, w, hev⟩ := hb
    have ha : Replay.arm dy sl m e t d
        = Replay.brkFx dy m t (Replay.brkEnd t p.val (a.map (·.val))) d ++ Replay.dayArm dy sl e t d := by
      unfold Replay.arm; simp only [hev]
    rw [ha, List.filterMap_append, (Replay.dayArm_obs dy sl e t d).1, List.append_nil] at hm
    rcases brkFx_mi dy m t _ d m' hm q hq with h | h
    · exact Or.inl h
    · right; right
      unfold brkEndAt?
      simp only [hev, Option.toList_some, List.mem_singleton, h]
      rfl
  · rcases arm_mi_of_not_brk dy sl m e t d (fun p a w h => hb ⟨p, a, w, h⟩) m' hm q hq with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- **A step's machine holds only the old block's instants and the step's own instants** (`entryInstants`: its stamp,
and — the owner's D87 — a break's end).  Restated at D87 from "the old block's instants and the step's stamp", which
a break inside a running block refutes (`stepWith_mi_as_w2_stated_it_is_refuted`). -/
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
      (Replay.completionArm_obs z e (e.t.val, e.off.val) (dy e.t.val)).2.2]
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

/-- **The machine after a fold holds its start's block instants and its entries' own instants** (their stamps, and —
D87 — a break's end). -/
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

/-! ### D94's bound (README gap 4506): a machine holds the breaks of at most `maxKeepDays + 1` ledger days

The machine holds every break it steps (`Replay.Machine.brks`), and every break it holds is within `maxKeepDays` ledger
days of the newest one held (`Replay.pruneBrks`).  So a checkpoint — which carries the machine (`Seal.cMachine`) —
holds the breaks of at most `maxKeepDays + 1` ledger days, however long the log: it does not grow with the log. -/

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
    m'.brks = m.brks ∨ ∃ k, m'.brks = Replay.pruneBrks (k :: m.brks) := by
  unfold Replay.arm at hm
  cases hev : e.ev <;> simp only [hev] at hm
  case start =>
    simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
      Effect.machineOf?, List.filterMap_nil, Replay.settle_machines, List.mem_singleton] at hm
    subst hm
    exact Or.inl ((Replay.settle_keeps dy _).2.2.1.trans (Replay.cut_brk dy m t))
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
    split at hm <;>
    · simp only [List.filterMap_append, List.filterMap_cons, Effect.machineOf?, List.filterMap_nil,
        Replay.settle_machines, List.nil_append, List.mem_singleton] at hm
      subst hm
      exact Or.inl ((Replay.settle_keeps dy _).2.2.1)
  case stop id rem =>
    split at hm
    · split at hm
      · simp only [List.filterMap_append, (Replay.cut_obs dy m t).2.2.1, List.nil_append, List.filterMap_cons,
          Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
        subst hm
        exact Or.inl (Replay.cut_brk dy m t)
      · simp at hm
    · simp at hm
  case extend id by_ => simp [Effect.machineOf?] at hm
  case done id est actual went tags ci isPartial =>
    rw [doneFx_machines] at hm
    simp only [List.mem_singleton] at hm
    subst hm
    left
    unfold Replay.doneClose
    repeat' split
    all_goals rfl
  case brk p a w =>
    rw [List.filterMap_append, (Replay.dayArm_obs dy sl e t d).1, List.append_nil] at hm
    exact Or.inr ⟨_, Replay.brkFx_brk dy m t _ d m' hm⟩
  case brkStart pl w =>
    simp only [Effect.machineOf?, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hm
    subst hm
    exact Or.inl rfl
  all_goals rw [(Replay.dayArm_obs dy sl e t d).1] at hm; simp at hm

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
      (Replay.completionArm_obs z e (e.t.val, e.off.val) (dy e.t.val)).2.2]
  unfold Replay.stepWith
  rw [h3, hfx]
  cases hl : ((Replay.arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.machineOf?).getLast? with
  | none => exact h
  | some m' =>
    rw [Option.getD_some]
    rcases arm_brks dy sl st.machine e _ _ m' (List.mem_of_getLast? hl) with hb | ⟨k, hb⟩
    · rw [hb]; exact h
    · rw [hb]; exact pruneBrks_within _

/-- **D94's bound, over every fold** (README gap 4506): a fold from a machine within the bound holds only breaks
within `maxKeepDays` ledger days of the newest one held — the replay's (from `State.init`, which holds none), and so
every checkpoint's (`ckpt_machine`). -/
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

/-- **The replay's machine holds the breaks of at most `maxKeepDays + 1` ledger days** — every fold from the empty
state. -/
theorem a_replay_holds_breaks_within_maxKeepDays_of_the_newest (z : Cal.Tz) (dy : Cal.Instant → Nat)
    (sl : Nat → Option Nat) (sv : List Entry) (n : Nat) :
    ∀ k ∈ (sv.foldl (Replay.stepWith z dy sl) (State.init n)).machine.brks,
      (sv.foldl (Replay.stepWith z dy sl) (State.init n)).machine.brks.foldl (fun a x => max a x.day) 0
        ≤ k.day + maxKeepDays :=
  foldl_brks_within z dy sl sv _ (fun k hk => by simp [State.init] at hk)

/-! ### W2's two machine-instant laws, refuted as W2 stated them (the owner's D87, README gap 4137)

A `break` stepped while the open block's clock runs restarts the clock at the break's END (`Replay.brkFx`), an instant
that is neither the old block's nor the step's stamp.  The two laws below are W2's statements; `arm_mi` and
`stepWith_mi` are the forms that hold (the break's end is one of the entry's own instants, `entryInstants`).  The
witness: `a` running since 09:00 (nothing banked), a twenty-minute `break` at 09:30. -/

/-- **`arm_mi` as W2 stated it is refuted**: the break's machine holds 09:50. -/
theorem arm_mi_as_w2_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : Replay.At) (d : Nat)
      (m' : Machine), m' ∈ (Replay.arm dy sl m e t d).filterMap Effect.machineOf? →
      ∀ q ∈ machineInstants m', q ∈ machineInstants m ∨ q = t.1 := by
  intro h
  have := h (fun _ => 739865) (fun _ => none)
    ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none, 0, none, 739865,
      [], []⟩, none, none, [], none, []⟩
    (Replay.bE 2 63924370200 (.brk 20 (some 20) none)) (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865
    ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924371400, 0⟩, ⟨false, 0⟩), false, none, 30, none, 739865,
      [], [⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), (⟨63924370200, 0⟩, ⟨false, 0⟩), 739865⟩]⟩,
      none, none, [⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924371400, 0⟩, ⟨false, 0⟩), 739865⟩], none, []⟩ (by decide)
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
        [], []⟩, none, none, [], none, []⟩ }
    (Replay.bE 2 63924370200 (.brk 20 (some 20) none)) ⟨63924371400, 0⟩ (by decide)
  revert this
  decide

/-- **A machine holds the end of the last break it stepped** (the owner's D92, README gap 4241): with no block open
and the span `[09:30, 09:50]` held, its one instant is 09:50 — where a clock a later step starts inside that break
begins, and where the step that closes it reads the day index (`Replay.settle`, the owner's D99). -/
theorem a_machine_holds_its_last_breaks_end :
    machineInstants ⟨none, none, none, [⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924371400, 0⟩, ⟨false, 0⟩), 739865⟩], none, []⟩
      = [⟨63924371400, 0⟩] := by
  decide

/-- **…and the end of every break it holds** (the owner's D94, README gap 4506): with `[09:00, 09:30]` and
`[09:40, 09:45]` held, its instants are both ends — a clock a later step starts inside the earlier break begins at
09:30, and a stretch closed across the later one resumes at 09:45. -/
theorem a_machine_holds_the_end_of_every_break_it_holds :
    machineInstants ⟨none, none, none, [⟨(⟨63924370800, 0⟩, ⟨false, 0⟩), (⟨63924371100, 0⟩, ⟨false, 0⟩), 739865⟩,
      ⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), (⟨63924370200, 0⟩, ⟨false, 0⟩), 739865⟩], none, []⟩
      = [⟨63924371100, 0⟩, ⟨63924370200, 0⟩] := by
  decide

end Seal
end Tm
