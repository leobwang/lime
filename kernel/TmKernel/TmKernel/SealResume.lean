import TmKernel.SealLaw
/-!
# SealResume — resuming a checkpoint over its tail (stage 5, D9, W2)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.3 (the guards), §9.4 (the reseal) and §9.5 (the laws).
`resume z T K b term p` restores the state a checkpoint `K` holds (`restore`), masks the tail `b` with the settled undos
set aside (`unsettled`), refuses by G1 an undo whose target could be folded (`g1`), and steps the tail's survivors on
the stored wakes and the tail's (`tailIndex`, `tailSlept`), refusing by G2 a wake behind the cut or inside the fence,
and by G3 a reading of the index before the head second or a key below the horizons (`stepCheck`); every tail entry's
header is checked too (`headerCheck`).  The answer (`resumedAnswer`) is the resumed state grouped as `ckptOf` groups a
state, with the checkpoint's all-time aggregates below the horizons (`aggMerged`).

Nothing here is on the wire yet (W3 wires it).  D9-21: `restore` and the tail fold are `foldl`s; `unsettled` is
`filterTR`; `g1` reads `danglingOf` (a `foldl` whose steps scan the stack: quadratic on a hostile tail of undos, W5
measures it); `resumedAnswer` groups with `canon` (each insertion scans; W4's lever).
-/
namespace Tm
namespace Seal

open Replay (State Machine Effect HeaderRec EnergyObs Obs)
open Log (Entry)

/-! ## The guards' vocabulary -/

/-- **The fence** (G2): a surviving tail wake must be more than three days before every folded future instant, since
two instants on one local date are less than three days apart under any zone table (offsets are under a day). -/
def fenceSec : Nat := 259200

/-- The open block's pause start, if any. -/
def blockPaused (m : Machine) : List Cal.Instant := ((m.block.bind (·.pausedAt)).map (·.1)).toList

/-- **The instants a re-draw reads the index at** (the owner's D99, README gap 4520a): the start of every span of `P`
not drawn before — the day a new piece is filed under (`Replay.redraw`).  A piece drawn before keeps the day it was
filed under and is read nowhere. -/
def redrawReads (old : List Replay.Piece) (P : List (Replay.At × Replay.At)) : List Cal.Instant :=
  (P.filter (fun q => !old.any (fun p => Replay.samePiece p q))).map (·.1.1)

/-- **`redrawReads`, compiled** (README gap 5027, W-48 track A): the spans `Replay.redrawWalk`'s one merge leaves
undrawn, when the old pieces' and the new spans' starts strictly increase; `redrawReads` itself otherwise.  The day the
merge would file a new piece under is not read here, so it is asked with any. -/
def redrawReadsFast (old : List Replay.Piece) (P : List (Replay.At × Replay.At)) : List Cal.Instant :=
  if Replay.startsUp (old.map (fun p => (p.s, p.e))) && Replay.startsUp P then
    (Replay.redrawWalk (fun _ => 0) old P).2.2.map (·.1.1)
  else redrawReads old P

/-- **`redrawReads` is `redrawReadsFast`** (README gap 5027): `@[csimp]`, by the merge's third list
(`Replay.redrawWalkGo_spec`). -/
@[csimp] theorem redrawReads_eq_redrawReadsFast : @redrawReads = @redrawReadsFast := by
  funext old P
  unfold redrawReadsFast
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rw [Replay.redrawWalk, Replay.redrawWalkGo_spec (fun _ => 0) _ old P (Nat.le_refl _) h.1 h.2]
    rfl
  · rfl

/-- **The instants settling the open block reads the index at** (D99): its new pieces' starts. -/
def settleReads (m : Machine) : List Cal.Instant :=
  match m.block with
  | some b => redrawReads b.drawn (Replay.openPieces b m)
  | none => []

/-- **The instants cutting the open block at `t` reads the index at** (D99): its new pieces' starts. -/
def cutReads (m : Machine) (t : Replay.At) : List Cal.Instant :=
  match m.block with
  | some b => redrawReads b.drawn (Replay.cutPieces b m t)
  | none => []

/-- **The instants netting the held closed blocks reads the index at** (the owner's D100, README gap 4520b): each
block a break of ledger day `d` nets, the starts of the pieces it draws anew for it (`redrawReads`). -/
def closedReads (s e : Replay.At) (d : Nat) (l : List Replay.Closed) : List Cal.Instant :=
  l.flatMap (fun C => if d < C.day ∨ C.drawn.all (fun p => decide (p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1)) then [] else redrawReads C.drawn (Replay.cutOut s e C.spans))

/-- **The instants a late `start` at `t` reads the index at** (the owner's D115): each held closed block it cuts
(`Replay.netStart`, over the block's own span `[t, Replay.startEnd t C)`), the starts of the pieces it draws anew — which
are where the block's own pieces began (`Replay.cutOut_startEnd_starts`). -/
def startReads (t : Replay.At) (d : Nat) (l : List Replay.Closed) : List Cal.Instant :=
  l.flatMap (fun C => if d < C.day ∨ C.drawn.all (fun p => decide (p.e.1 ≤ t.1 ∨ (Replay.startEnd t C).1 ≤ p.s.1))
    then [] else redrawReads C.drawn (Replay.cutOut t (Replay.startEnd t C) C.spans))

/-- **The instants the running break's netting reads the index at** (README gap 5180, W-49 track L; `Replay.runNet`): with
a break running and a held piece drawn after its start, `closedReads` over the span `[s, Replay.runTo s)`; nothing
otherwise. -/
def runReads (m : Machine) : List Cal.Instant :=
  match m.brkOpen with
  | some o =>
    if o.s.1 < (Replay.runTo o.s m.closed).1 then closedReads o.s (Replay.runTo o.s m.closed) o.day m.closed else []
  | none => []

/-- **The instants a give-back reads the index at** (the owner's D137, README gaps 5504 and 5302; `Replay.giveBack`): each
held closed block a running break netted, the starts of the pieces it re-draws anew — where a piece the running break took
began (`Replay.Closed.ran`), which the machine holds. -/
def giveReads (m : Machine) : List Cal.Instant :=
  m.closed.flatMap (fun C => if C.ran.isEmpty then [] else redrawReads C.drawn C.restored)

/-- **The instants a break held as `[s, e)` on ledger day `d` reads the index at** (D87, D94, D100; `Replay.brkFx`): the
open block's new pieces once the break is held (`settleReads`), and each held closed block's it nets (`closedReads`). -/
def brkFxReads (m : Machine) (s e : Replay.At) (d : Nat) : List Cal.Instant :=
  settleReads { m with brks := Replay.pruneBrks (⟨s, e, d⟩ :: m.brks), brkOpen := none } ++ closedReads s e d m.closed

/-- **The instants a `start` at `t` reads the index at, over the machine it starts from** (C3, D99, D115, gap 5180;
`Replay.startArm`). -/
def startQueries (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (d : Nat) (id : Log.Id)
    (pred : Log.U8) (rep : Option Log.U8) (hsw : Log.Num) (sleptMin : Log.U32) (loc : List Char) : List Cal.Instant :=
  startReads t d m.closed ++ cutReads m t ++ blockPaused m ++
    runReads (Replay.cut dy (Replay.netStart dy t d m).1 t).1 ++
    settleReads (Replay.startedMachine m id t d
      (rep.map (fun rp => ⟨line, t, d, pred, rp, hsw, loc, some sleptMin.val, none, some id, true⟩)))

/-- **Every instant a step reads the day index at**: the entry's own (`entryInstants`), the open block's pause start
when the step closes it (`closePause`), and — since the owner's D99 (README gap 4520a) — the start of every piece the
step draws for the open block that was not drawn before (`settleReads`, `cutReads`): a piece drawn before is moved by
un-drawing it from the day it was filed under, which is read nowhere.  The day index `dy` is read here only at the
entry's own stamp (the ledger day a `start` opens its block on, and a `break` is held with). -/
def stepQueries (dy : Cal.Instant → Nat) (m : Machine) (e : Entry) : List Cal.Instant :=
  entryInstants e ++
    match e.ev with
    | .start id pred rep hsw sleptMin loc _ _ =>
      match Replay.endsBrk m (e.t.val, e.off.val) with
      | some o =>
        startQueries dy (Replay.endMachine m o (e.t.val, e.off.val)) e.line (e.t.val, e.off.val) (dy e.t.val) id pred
          rep hsw sleptMin loc
      | none => startQueries dy m e.line (e.t.val, e.off.val) (dy e.t.val) id pred rep hsw sleptMin loc
    | .pause id =>
      match m.block with
      | some b =>
        if b.id = id ∧ b.paused = false ∧ b.started.1 ≤ e.t.val then
          settleReads { m with block := some { b with paused := true, pausedAt := some (e.t.val, e.off.val) } }
        else []
      | none => []
    | .unpause id =>
      match m.block with
      | some b =>
        if b.id = id ∧ b.paused = true then
          blockPaused m ++ settleReads { Replay.closePauseM m (e.t.val, e.off.val) with
            block := (Replay.closePauseM m (e.t.val, e.off.val)).block.map (fun b => { b with paused := false }) }
        else []
      | none => []
    | .interrupt id =>
      blockPaused m ++ settleReads (Replay.interruptMachine m (e.t.val, e.off.val) (dy e.t.val) id)
    | .resume _ _ =>
      match m.interrupt with
      | some (s, sd, _) =>
        settleReads { m with block := m.block.map (fun b => Replay.resumeBlock b (some (s, (e.t.val, e.off.val)))
          (e.t.val, e.off.val)), interrupt := none } ++ closedReads s (e.t.val, e.off.val) sd m.closed
      | none => settleReads { m with block := m.block.map (fun b => Replay.resumeBlock b none (e.t.val, e.off.val)) }
    | .stop id _ =>
      match m.block with
      | some b =>
        if b.id = id then
          cutReads m (e.t.val, e.off.val) ++ blockPaused m ++ runReads (Replay.cut dy m (e.t.val, e.off.val)).1
        else []
      | none => []
    | .done id _ actual went _ ci _ =>
      (match m.block with
       | some b => if b.id = id then cutReads m (e.t.val, e.off.val) ++ blockPaused m else []
       | none => []) ++
      runReads { (Replay.doneClose dy m (e.t.val, e.off.val) id actual.val went).1 with
        closed := Replay.doneClosed dy m e.line (e.t.val, e.off.val) id actual.val ci }
    | .brkStart planned where_ =>
      match Replay.firstStart (e.t.val, e.off.val) (dy e.t.val) m with
      | some t0 => brkFxReads { m with brkEnded := some (e.t.val, e.off.val) } (e.t.val, e.off.val) t0 (dy e.t.val)
      | none =>
        settleReads { m with brkOpen := some ⟨(e.t.val, e.off.val), planned.val, where_, dy e.t.val⟩ } ++
          runReads { m with brkOpen := some ⟨(e.t.val, e.off.val), planned.val, where_, dy e.t.val⟩ }
    | .brk planned actual _ =>
      match m.brkEnded with
      | some s =>
        if Replay.atEq s (e.t.val, e.off.val) then []
        else giveReads m ++ brkFxReads (Replay.giveBack dy m).1 (e.t.val, e.off.val)
          (Replay.brkEnd (e.t.val, e.off.val) planned.val (actual.map (·.val))) (dy e.t.val)
      | none =>
        giveReads m ++ brkFxReads (Replay.giveBack dy m).1 (e.t.val, e.off.val)
          (Replay.brkEnd (e.t.val, e.off.val) planned.val (actual.map (·.val))) (dy e.t.val)
    | _ => []

/-! ### What a netting reads depends on the held blocks' days and spans alone (README gap 5180)

The running break's netting is read over a machine a step has just written (a cut's, a `done`'s), whose held blocks
carry days and credits the index gave — but `closedReads` and `Replay.runTo` read a held block's ledger day and its
pieces' spans and nothing else, and those do not depend on the index.  So the queries still depend on the index only at
the step's own stamp (`stepQueries_congr`). -/

/-- **A re-draw's pieces are the spans it was given** (D99), in order. -/
theorem redraw_fst_map (dy : Cal.Instant → Nat) (id : Log.Id) (old : List Replay.Piece) (P : List (Replay.At × Replay.At)) :
    (Replay.redraw dy id old P).1.map (fun p => (p.s, p.e)) = P := by
  unfold Replay.redraw
  simp only [List.map_map]
  refine (List.map_congr_left (fun q _ => ?_)).trans (List.map_id P)
  simp only [Function.comp_apply, id_eq]
  split
  · rename_i p hf
    have h1 := List.find?_some hf
    unfold Replay.samePiece at h1
    simp only [Bool.and_eq_true] at h1
    rw [(Replay.atEq_iff _ _).1 h1.1, (Replay.atEq_iff _ _).1 h1.2]
  · rfl

theorem closedReads_shp (s e : Replay.At) (d : Nat) : ∀ (l₁ l₂ : List Replay.Closed),
    l₁.map (fun C => (C.day, C.spans)) = l₂.map (fun C => (C.day, C.spans)) →
      closedReads s e d l₁ = closedReads s e d l₂
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | C₁ :: l₁, C₂ :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hd, hs⟩, ht⟩ := h
    have ih := closedReads_shp s e d l₁ l₂ ht
    unfold closedReads at ih ⊢
    simp only [List.flatMap_cons]
    rw [ih]
    congr 1
    have hall : ∀ C : Replay.Closed, C.drawn.all (fun p => decide (p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1)) =
        C.spans.all (fun q => decide (q.2.1 ≤ s.1 ∨ e.1 ≤ q.1.1)) := by
      intro C; simp [Replay.Closed.spans, List.all_map, Function.comp_def]
    have hrr : ∀ (C : Replay.Closed) (P : List (Replay.At × Replay.At)), redrawReads C.drawn P =
        (P.filter (fun q => !C.spans.any (fun r => Replay.atEq r.1 q.1 && Replay.atEq r.2 q.2))).map (·.1.1) := by
      intro C P; simp [redrawReads, Replay.Closed.spans, List.any_map, Replay.samePiece, Function.comp_def]
    rw [hall C₁, hall C₂, hrr, hrr, hd, hs]

theorem runTo_spans : ∀ (s : Replay.At) (l : List Replay.Closed),
    Replay.runTo s l = (l.map (fun C => (C.day, C.spans))).foldl
      (fun a S => S.2.foldl (fun b q => if b.1 < q.2.1 then q.2 else b) a) s
  | _, [] => rfl
  | s, C :: l => by
    simp only [Replay.runTo, List.map_cons, List.foldl_cons]
    rw [runTo_spans _ l]
    congr 1
    simp [Replay.Closed.spans, List.foldl_map]

theorem runReads_shp (m₁ m₂ : Machine) (hk : m₁.brkOpen = m₂.brkOpen)
    (hc : m₁.closed.map (fun C => (C.day, C.spans)) = m₂.closed.map (fun C => (C.day, C.spans))) :
    runReads m₁ = runReads m₂ := by
  unfold runReads
  have hrt : ∀ s, Replay.runTo s m₁.closed = Replay.runTo s m₂.closed := fun s => by
    rw [runTo_spans, runTo_spans, hc]
  have hcr : ∀ s e d, closedReads s e d m₁.closed = closedReads s e d m₂.closed := fun s e d =>
    closedReads_shp s e d _ _ hc
  rw [hk]; simp only [hrt, hcr]

theorem pruneClosed_shp : ∀ (l₁ l₂ : List Replay.Closed),
    l₁.map (fun C => (C.day, C.spans)) = l₂.map (fun C => (C.day, C.spans)) →
      (Replay.pruneClosed l₁).map (fun C => (C.day, C.spans)) = (Replay.pruneClosed l₂).map (fun C => (C.day, C.spans))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | c₁ :: l₁, c₂ :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hd, hs⟩, ht⟩ := h
    have hf : ∀ (c : Replay.Closed) (l : List Replay.Closed), (Replay.pruneClosed (c :: l)).map (fun C => (C.day, C.spans)) =
        (c.day, c.spans) :: ((l.map (fun C => (C.day, C.spans))).filter
          (fun x => decide (((l.map (fun C => (C.day, C.spans))).foldl (fun a k => max a k.1) c.day) ≤ x.1 + 31))) := by
      intro c l
      simp only [Replay.pruneClosed, List.map_cons, List.filter_map, List.foldl_map, Function.comp_def]
    rw [hf, hf, ht, hd, hs]

theorem netOne_shp (dy₁ dy₂ : Cal.Instant → Nat) (s e : Replay.At) (d : Nat) (C : Replay.Closed) :
    ((Replay.netOne dy₁ s e d C).1.day, (Replay.netOne dy₁ s e d C).1.spans) =
      ((Replay.netOne dy₂ s e d C).1.day, (Replay.netOne dy₂ s e d C).1.spans) := by
  unfold Replay.netOne
  split
  · rfl
  · simp only [Replay.Closed.spans, redraw_fst_map]

/-- **A give-back's held blocks' days and spans do not depend on the index** (D137): each is its block as it stood
(`Replay.Closed.restored`) on its own ledger day. -/
theorem giveBack_shp (dy₁ dy₂ : Cal.Instant → Nat) (m : Machine) :
    (Replay.giveBack dy₁ m).1.closed.map (fun C => (C.day, C.spans)) =
      (Replay.giveBack dy₂ m).1.closed.map (fun C => (C.day, C.spans)) := by
  show (m.closed.map (fun C => (Replay.giveOne dy₁ C).1)).map _ = (m.closed.map (fun C => (Replay.giveOne dy₂ C).1)).map _
  simp only [List.map_map]
  apply List.map_congr_left
  intro C _
  simp only [Function.comp_apply]
  unfold Replay.giveOne
  by_cases hr : C.ran.isEmpty = true
  · simp only [hr, if_true]
  · simp only [hr, if_false, Bool.false_eq_true, Replay.Closed.spans, redraw_fst_map]

/-- **What a `break` line nets after its give-back does not depend on the index** (D137): the give-back moves only the
held closed blocks and the last cut, and their days and spans not by the index (`giveBack_shp`). -/
theorem brkFxReads_giveBack (dy₁ dy₂ : Cal.Instant → Nat) (m : Machine) (s e : Replay.At) (d : Nat) :
    brkFxReads (Replay.giveBack dy₁ m).1 s e d = brkFxReads (Replay.giveBack dy₂ m).1 s e d := by
  unfold brkFxReads
  rw [closedReads_shp s e d _ _ (giveBack_shp dy₁ dy₂ m)]
  rfl

theorem netStart_shp (dy₁ dy₂ : Cal.Instant → Nat) (t : Replay.At) (d : Nat) (m : Machine) :
    (Replay.netStart dy₁ t d m).1.closed.map (fun C => (C.day, C.spans)) =
      (Replay.netStart dy₂ t d m).1.closed.map (fun C => (C.day, C.spans)) := by
  show (m.closed.map (fun C => (Replay.netOne dy₁ t (Replay.startEnd t C) d C).1)).map _ =
    (m.closed.map (fun C => (Replay.netOne dy₂ t (Replay.startEnd t C) d C).1)).map _
  simp only [List.map_map]
  apply List.map_congr_left
  intro C _
  exact netOne_shp dy₁ dy₂ t _ d C

theorem cut_shp (dy₁ dy₂ : Cal.Instant → Nat) (M₁ M₂ : Machine) (t : Replay.At) (hb : M₁.block = M₂.block)
    (hbr : M₁.brks = M₂.brks) (hi : M₁.interrupt = M₂.interrupt)
    (hc : M₁.closed.map (fun C => (C.day, C.spans)) = M₂.closed.map (fun C => (C.day, C.spans))) :
    (Replay.cut dy₁ M₁ t).1.closed.map (fun C => (C.day, C.spans)) =
      (Replay.cut dy₂ M₂ t).1.closed.map (fun C => (C.day, C.spans)) := by
  unfold Replay.cut
  rw [hb]
  cases hb2 : M₂.block with
  | none => exact hc
  | some b =>
    simp only
    have hP : Replay.cutPieces b M₁ t = Replay.cutPieces b M₂ t := by
      simp only [Replay.cutPieces, Replay.blockSpans, Replay.openStop, hbr, hi]
    apply pruneClosed_shp
    simp only [List.map_cons, Replay.Closed.spans, redraw_fst_map, hP]
    exact congrArg _ hc

theorem doneClosed_shp (dy₁ dy₂ : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (id : Log.Id)
    (actual : Nat) (ci : Log.U8) :
    (Replay.doneClosed dy₁ m line t id actual ci).map (fun C => (C.day, C.spans)) =
      (Replay.doneClosed dy₂ m line t id actual ci).map (fun C => (C.day, C.spans)) := by
  unfold Replay.doneClosed
  cases hb : m.block with
  | some b =>
    simp only
    split
    · apply pruneClosed_shp
      simp only [List.map_cons, Replay.Closed.spans, redraw_fst_map]
    · rfl
  | none =>
    simp only
    split
    · split <;> rfl
    · rfl

/-- **A start's queries depend on the index only through the ledger day it is given** (C3, D115, gap 5180): the running
break's netting is read over the held blocks' days and spans, which no index moves (`runReads_shp`). -/
theorem startQueries_congr (dy₁ dy₂ : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : Replay.At) (d : Nat)
    (id : Log.Id) (pred : Log.U8) (rep : Option Log.U8) (hsw : Log.Num) (sleptMin : Log.U32) (loc : List Char) :
    startQueries dy₁ m line t d id pred rep hsw sleptMin loc = startQueries dy₂ m line t d id pred rep hsw sleptMin loc := by
  unfold startQueries
  rw [runReads_shp (Replay.cut dy₁ _ _).1 (Replay.cut dy₂ _ _).1
    (by rw [Replay.cut_brkOpen, Replay.cut_brkOpen, (Replay.netStart_keeps dy₁ _ _ _).2.2.2.1,
      (Replay.netStart_keeps dy₂ _ _ _).2.2.2.1])
    (cut_shp dy₁ dy₂ _ _ _ (by rw [(Replay.netStart_keeps dy₁ _ _ _).1, (Replay.netStart_keeps dy₂ _ _ _).1])
      (by rw [(Replay.netStart_keeps dy₁ _ _ _).2.2.1, (Replay.netStart_keeps dy₂ _ _ _).2.2.1])
      (by rw [(Replay.netStart_keeps dy₁ _ _ _).2.1, (Replay.netStart_keeps dy₂ _ _ _).2.1])
      (netStart_shp dy₁ dy₂ _ _ m))]

/-- **A step's queries read the index only at its own stamp** (D99): two indexes agreeing there give one list.
*Re-proved at W-49 track L (README gap 5180)*, statement unchanged: the running break's netting is read over the held
blocks' days and spans, which no index moves (`runReads_shp`). -/
theorem stepQueries_congr (dy₁ dy₂ : Cal.Instant → Nat) (m : Machine) (e : Entry) (h : dy₁ e.t.val = dy₂ e.t.val) :
    stepQueries dy₁ m e = stepQueries dy₂ m e := by
  unfold stepQueries
  rw [h]
  cases hev : e.ev <;> simp only
  case start =>
    split <;> rw [startQueries_congr dy₁ dy₂]
  case stop =>
    split
    · split
      · rw [runReads_shp (Replay.cut dy₁ m _).1 (Replay.cut dy₂ m _).1
          (by rw [Replay.cut_brkOpen, Replay.cut_brkOpen]) (cut_shp dy₁ dy₂ m m _ rfl rfl rfl rfl)]
      · rfl
    · rfl
  case done id est actual went tags ci isPartial =>
    rw [runReads_shp { (Replay.doneClose dy₁ m (e.t.val, e.off.val) id actual.val went).1 with
        closed := Replay.doneClosed dy₁ m e.line (e.t.val, e.off.val) id actual.val ci }
      { (Replay.doneClose dy₂ m (e.t.val, e.off.val) id actual.val went).1 with
        closed := Replay.doneClosed dy₂ m e.line (e.t.val, e.off.val) id actual.val ci }
      (by show (Replay.doneClose dy₁ m (e.t.val, e.off.val) id actual.val went).1.brkOpen =
            (Replay.doneClose dy₂ m (e.t.val, e.off.val) id actual.val went).1.brkOpen
          rw [Replay.doneClose_brkOpen, Replay.doneClose_brkOpen])
      (doneClosed_shp dy₁ dy₂ m e.line (e.t.val, e.off.val) id actual.val ci)]
  case brk planned actual where_ =>
    split
    · split
      · rfl
      · rw [brkFxReads_giveBack dy₁ dy₂]
    · rw [brkFxReads_giveBack dy₁ dy₂]

/-- **The tail without its settled undos** (§7.4): a settled undo cancels nothing after the cut. -/
def unsettled (settled : List Nat) (bs : List Entry) : List Entry :=
  bs.filter (fun e => !(e.ev.isUndo && settled.contains e.line))

/-- G1 for one dangling tail undo: refused when a folded survivor may carry its tag. -/
def reachOf (K : Ckpt) (u : Entry) : Option Refusal :=
  match u.ev with
  | .undo of_ _ =>
    match K.tagLast.find? (fun p => p.1 == of_) with
    | some p => some (.undoReach u.line p.2)
    | none => if !Log.isKnownTag of_ && K.tagOverflow then some (.undoReach u.line 0) else none
  | _ => none

/-- **G1** (§7.4): the first undo of the unsettled tail that dangles there and whose tag a folded survivor may carry. -/
def g1 (K : Ckpt) (N : List Entry) : Option Refusal := ((Replay.danglingOf N).2.reverse).findSome? (reachOf K)

/-- **The tail's day index**: the stored wakes and the tail's surviving wakes. -/
def tailIndex (z : Cal.Tz) (K : Ckpt) (sv : List Entry) : List Cal.Instant :=
  Replay.keptWakes z (K.wakes ++ Replay.wakeInstants sv)

/-- **The tail's `slept_by_day`**: a day's first folded wake's, else its first tail wake's. -/
def tailSlept (z : Cal.Tz) (K : Ckpt) (kw : List Cal.Instant) (sv : List Entry) : Nat → Option Nat :=
  fun d => (Replay.KMap.get K.sleptByDay d).or (Replay.KMap.get (Replay.sleptByDay z kw sv) d)

/-- The refusal for a key below the horizons. -/
def keyRefusal (line : Nat) : Replay.Key → Refusal
  | .day d => .sealedDay line d
  | .itemDay _ d => .sealedWindow line d
  | .doneDate _ d => .sealedWindow line d
  | .instDate _ _ d => .sealedWindow line d
  | _ => .sealedDay line 0

/-- **One checked tail step**: its effects, and the first guard it fails (G3's head, G2, G3's keys). -/
def stepCheck (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (e : Entry) :
    List Effect × Option Refusal :=
  let fx := Replay.effectsWith z dy sl st e
  (fx, (((stepQueries dy st.machine e).find? (fun q => decide (q.sec < headSec K.ledgerDay))).map
          (fun _ => Refusal.sealedDay e.line (K.ledgerDay - 1)))
    <|> (if Replay.isWake e && !(K.maxT.all (· < e.t.val) && K.futureFloor.all (fun f => decide (e.t.val.sec + fenceSec < f.sec)))
         then some (.wakeBehindCut e.line e.t.val) else none)
    <|> ((fx.find? (fun x => !keyAtOrAbove K.ledgerDay (horizonOf K.ledgerDay) x.key)).map (fun x => keyRefusal e.line x.key)))

def tailFoldStep (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt)
    (acc : State × Option Refusal) (e : Entry) : State × Option Refusal :=
  let r := stepCheck z dy sl K acc.1 e
  (Replay.applyEffects acc.1 r.1, acc.2 <|> r.2)

/-- **The tail's survivors stepped from a state**, with the first refusal. -/
def tailFold (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (K : Ckpt) (st : State) (sv : List Entry) :
    State × Option Refusal :=
  sv.foldl (tailFoldStep z dy sl K) (st, none)

/-- **Every tail entry's header** (G3, cancelled entries included): at or after the head second, on a day at or after
the ledger day. -/
def headerCheck (dy : Cal.Instant → Nat) (K : Ckpt) (bs : List Entry) : Option Refusal :=
  bs.findSome? (fun e => if e.t.val.sec < headSec K.ledgerDay then some (.sealedDay e.line (K.ledgerDay - 1))
    else if dy e.t.val < K.ledgerDay then some (.sealedDay e.line (dy e.t.val)) else none)

/-- **The tail's headers**: each entry's day on the tail's index and its mask bit (a settled undo is cancelled, as every
undo is; any other entry reads the unsettled tail's mask). -/
def tailHeaders (dy : Cal.Instant → Nat) (settled : List Nat) (bs : List Entry) : List (Nat × HeaderRec) :=
  let dead := Replay.maskFast (unsettled settled bs)
  (bs.foldl (fun (acc : List (Nat × HeaderRec) × Nat) e =>
    if e.ev.isUndo && settled.contains e.line then ((dy e.t.val, HeaderRec.of e true) :: acc.1, acc.2)
    else ((dy e.t.val, HeaderRec.of e (Replay.deadAt dead acc.2)) :: acc.1, acc.2 + 1)) ([], 0)).1.reverse

/-- The stored headers of a checkpoint's open days. -/
def storedHeaders (K : Ckpt) : List (Nat × HeaderRec) := K.openDays.flatMap (fun o => o.headers.map (fun h => (o.day, h)))

/-! ## The restored state -/

/-- Write every pair's value at its key, in order. -/
def writeAll {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (l : List (κ × β)) (m : Replay.HMap κ β) : Replay.HMap κ β :=
  l.foldl (fun m p => m.alter p.1 (fun _ => some p.2)) m

/-- A checkpoint's window item minutes, as pairs. -/
def windowItemPairs (K : Ckpt) : List ((Nat × Log.Id) × Nat) :=
  K.window.flatMap (fun w => w.itemMin.map (fun p => ((w.day, p.1), p.2)))

/-- A checkpoint's window done dates, as pairs. -/
def windowDonePairs (K : Ckpt) : List ((Nat × Log.Id) × Unit) :=
  K.window.flatMap (fun w => w.doneIds.map (fun i => ((w.day, i), ())))

/-- A checkpoint's instances, the date-keyed then the others. -/
def instPairs (K : Ckpt) : List ((List Char × List Char) × Replay.InstRec) := K.window.flatMap (·.inst) ++ K.instOther

/-- Write a value at a key when there is one. -/
def writeOpt {κ β : Type} [DecidableEq κ] [Replay.KeyHash κ] (m : Replay.HMap κ β) (k : κ) : Option β → Replay.HMap κ β
  | some x => m.alter k (fun _ => some x)
  | none => m


def restore (K : Ckpt) (n : Nat) : State :=
  ⟨K.openDays.foldl (fun m o => writeOpt m o.day o.acc) (Replay.HMap.empty n),
   K.items.foldl (fun m a => writeOpt m a.id a.acc) (Replay.HMap.empty n),
   writeAll (windowItemPairs K) (Replay.HMap.empty n),
   K.openDays.flatMap (fun o => o.energy.reverse),
   K.openDays.flatMap (fun o => o.durations.reverse),
   K.openDays.flatMap (fun o => o.interrupts.reverse),
   [], K.machine, ⟨K.lastEff, 0⟩,
   K.items.foldl (fun m a => writeOpt m a.id a.lastDone) (Replay.HMap.empty n),
   writeAll (windowDonePairs K) (Replay.HMap.empty n),
   writeAll (instPairs K) (Replay.HMap.empty n),
   writeAll K.named (Replay.HMap.empty n),
   K.rwarns.reverse,
   K.openDays.flatMap (fun o => (o.demotions.map (fun r => (o.day, r))).reverse),
   K.openDays.flatMap (fun o => (o.closes.map (fun r => (o.day, r))).reverse),
   K.items.foldl (fun m a => if a.dropped then m.alter a.id (fun _ => some ()) else m) (Replay.HMap.empty n),
   K.longestLeak, K.unknown,
   K.openDays.foldl (fun m o => writeOpt m o.day o.seam) (Replay.HMap.empty n)⟩

/-- A non-start energy observation rebound to a `slept_by_day` (late binding, C5). -/
def rebindObs (g : Nat → Option Nat) (o : EnergyObs) : EnergyObs :=
  if o.fromStart then o else { o with sleptMin := g o.day }

/-- **A state's observations rebound** to a `slept_by_day`. -/
def rebindState (g : Nat → Option Nat) (st : State) : State := { st with energy := st.energy.map (rebindObs g) }

/-! ## The resumed answer -/

def minOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.min a b)

def maxOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (Nat.max a b)

/-- **One item's all-time facts after a resume**: the state's, with the first done date and the count of done dates
taking the checkpoint's dates below the horizon. -/
def aggMerged (K : Ckpt) (st : State) (i : Log.Id) : ItemAgg :=
  let old := findItem K.items i
  let ds := (st.doneDates.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)
  ⟨i, st.items.get i, st.lastDone.get i, (st.dropped.get i).isSome,
   minOpt (old.bind (·.doneFirst)) (Replay.minDay? ds),
   ((old.map (·.doneCount)).getD 0) - (K.window.filter (fun w => w.doneIds.contains i)).length + ds.length⟩

/-- **The answer of a resumed state** (§11.1's `Hot`): grouped as `ckptOf` groups a state, above the checkpoint's
horizons, with its aggregates below them. -/
def resumedAnswer (K : Ckpt) (st : State) (hs : List (Nat × HeaderRec)) (entries : Nat) (ws : List (Nat × Log.LWarn)) :
    Seal.Answer :=
  ⟨K.ledgerDay, horizonOf K.ledgerDay,
   (canon idLt (K.items.map (·.id) ++ itemIds st)).map (fun i => (aggMerged K st i).finish),
   windowsFrom st (horizonOf K.ledgerDay), instOtherOf st, namedOf st,
   (daysFrom st hs K.ledgerDay).map (OpenDay.finish st.machine),
   Replay.openOf st.machine,
   st.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
   st.machine.brkOpen,
   maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)),
   st.global.lastEffective, K.entryCount + entries, st.unknown, st.longestLeak, st.rwarns.reverse,
   (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩

/-! ## Resume -/

/-- What a resume computed, for its answer and its reseal. -/
structure Run where
  entries : List Entry
  unsettledTail : List Entry
  survivors : List Entry
  index : List Cal.Instant
  slept : Nat → Option Nat
  state : State
  headers : List (Nat × HeaderRec)
  answer : Seal.Answer

/-- **Resume, the guards and the answer** (§9.3): G0 (the zone, the cut), G4 (`now` below the ledger day), G1, then the
tail's steps (G2, G3) and headers (G3). -/
def resumeRun (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) : Except Refusal Run :=
  if K.tzKey ≠ z.val.key then .error .zone
  else if !(b.head?.all (fun l => l.n == K.cut + 1)) then .error .cutMismatch
  else if T < K.ledgerDay then .error (.nowBelowLedger T K.ledgerDay)
  else
    let bs := Log.lineEntries b
    let N := unsettled K.settled bs
    match g1 K N with
    | some r => .error r
    | none =>
      let sv := Replay.survivors N
      let kw := tailIndex z K sv
      let dy := Replay.dayOf z kw
      let sl := tailSlept z K kw sv
      let r := tailFold z dy sl K (restore K (K.items.length + K.openDays.length + bs.length)) sv
      match r.2 <|> headerCheck dy K bs with
      | some x => .error x
      | none =>
        let hs := storedHeaders K ++ tailHeaders dy K.settled bs
        let st := rebindState sl r.1
        .ok ⟨bs, N, sv, kw, sl, st, hs, resumedAnswer K st hs bs.length (Log.lineWarnings b)⟩

/-! ## The reseal (§9.4)

A run's fold point `j` counts the tail lines it folds; the folded tail is the tail's entries on lines `K.cut + 1 ..
K.cut + j`.  A cut is valid (`cutOk`) when
- (i) every folded entry not future at `T` is on a day before `F` (`floorOf`, bounded by `now`, CRIT 1);
- (ii) it is within the policy's `maxLine`;
- (iii) every unfolded surviving wake is after the folded instants not future at `T` and more than the fence before the
  future ones;
- (iv) the new `settled` fits;
- (v) it does not fold an unterminated last line (CRIT 8);
- (vi) no unfolded undo's target is folded: the stored `settled` undos are folded, and no undo of the tail is cut from
  its tail target (W1's disagreement 11, settled by the cut, not by the ledger day).
The fold point is the greatest valid cut (`greatestValid`), and the new ledger day (`sealDayOf`) is the least of `F`,
the days the unfolded lines head, name and read, and the folded machine's days, never below `L`.  A reseal is emitted
when the stored checkpoint's future classification is unchanged at `T` (`migrationOk`) and the fold point is valid. -/

/-- The later of two optional instants. -/
def maxOptI : Option Cal.Instant → Option Cal.Instant → Option Cal.Instant
  | none, b => b
  | some a, none => some a
  | some a, some b => some (if a < b then b else a)

/-- The earlier of two optional instants. -/
def minOptI : Option Cal.Instant → Option Cal.Instant → Option Cal.Instant
  | none, b => b
  | some a, none => some a
  | some a, some b => some (if b < a then b else a)

/-- **The stored checkpoint's future classification holds at `T`**: its latest non-future instant is not future at `T`
and its earliest future one still is, so every folded instant keeps its side. -/
def migrationOk (K : Ckpt) (T : Nat) : Bool := K.maxT.all (fun m => !isFuture T m) && K.futureFloor.all (isFuture T)

/-- **`F`** (§9.4's G-w): `T − keepDays`, and `M − keepDays` for `M` the greatest day the call's surviving entries not
future at `T` head (`T` when there is none). -/
def floorOf (T keep : Nat) (dy : Cal.Instant → Nat) (sv : List Entry) : Nat :=
  let ds := (sv.filter (fun e => !isFuture T e.t.val)).map (fun e => dy e.t.val)
  Nat.min (T - keep) ((match ds with | [] => T | d :: rest => rest.foldl Nat.max d) - keep)

/-- Each undo of a list with the target it cancels there (stack order, as the mask cancels). -/
def undoTargets (N : List Entry) : List (Entry × Entry) :=
  (N.foldl (fun (acc : List Entry × List (Entry × Entry)) e =>
    match e.ev with
    | .undo of_ id =>
      match acc.1.find? (Replay.«matches» of_ id) with
      | some t => (acc.1.eraseP (Replay.«matches» of_ id), (e, t) :: acc.2)
      | none => acc
    | _ => (e :: acc.1, acc.2)) ([], [])).2

/-- **The new `settled` at cut `j`**: the unfolded undos of the unsettled tail that dangle there, ascending. -/
def settledAt (K : Ckpt) (r : Run) (j : Nat) : List Nat :=
  (((Replay.danglingOf r.unsettledTail).2.filter (fun u => decide (K.cut + j < u.line))).map (·.line)).reverse

/-- The days a tail's steps bound the new ledger day by, for the entries `P` selects: every date an effect's key names,
and the day after every instant the step reads the index at (so the head second is at or before it). -/
def stepLows (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (P : Entry → Bool) (st : State)
    (sv : List Entry) : List Nat :=
  (sv.foldl (fun (acc : State × List Nat) e =>
    let fx := Replay.effectsWith z dy sl acc.1 e
    (Replay.applyEffects acc.1 fx,
     if P e then fx.filterMap (fun x => x.key.date?) ++ (stepQueries dy acc.1.machine e).map (fun q => q.sec / 86400 + 1)
       ++ acc.2 else acc.2)) (st, [])).2

/-- **A valid cut** (§9.4's conditions (i)–(v), and (vi)). -/
def cutOk (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) (j : Nat) :
    Bool :=
  let dy := Replay.dayOf z r.index
  let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
  let svr := r.survivors.filter (fun e => decide (K.cut + j < e.line))
  let QAj := Bj.flatMap entryInstants
  let maxT' := maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q)))
  let ff' := minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T)))
  decide (j ≤ b.length)
  && Bj.all (fun e => isFuture T e.t.val || decide (dy e.t.val < floorOf T p.keepDays dy r.survivors))
  && (j == 0 || p.maxLine.all (fun m => decide (K.cut + j ≤ m)))
  && (Replay.wakeInstants svr).all (fun w => maxT'.all (· < w) && ff'.all (fun f => decide (w.sec + fenceSec < f.sec)))
  && decide ((settledAt K r j).length ≤ maxSettled)
  && (terminated || decide (j < b.length) || j == 0)
  && K.settled.all (fun n => decide (n ≤ K.cut + j))
  && (undoTargets r.unsettledTail).all (fun ut => !(decide (ut.2.line ≤ K.cut + j) && decide (K.cut + j < ut.1.line)))

/-- **The greatest `j ≤ n` a check accepts**, or `0` (specification: every cut is checked). -/
def greatestValid (n : Nat) (valid : Nat → Bool) : Nat :=
  (List.range (n + 1)).foldl (fun acc j => if valid j then j else acc) 0

/-- A run's fold point: its greatest valid cut. -/
def foldPointOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) : Nat :=
  greatestValid b.length (cutOk z T K b terminated p r)

/-- **The new ledger day `L'`** at cut `j` (§9.4, with W2's head-second and read-day bounds): the least of `F`, every
unfolded line's day and the day after its stamp, every date an unfolded surviving step names and the day after every
instant it reads, and the folded machine's days; never below `L`. -/
def sealDayOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (p : Policy) (r : Run) (j : Nat) : Nat :=
  let dy := Replay.dayOf z r.index
  let n := K.items.length + K.openDays.length + r.entries.length
  let Brest := r.entries.filter (fun e => decide (K.cut + j < e.line))
  let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
  let lows := Brest.map (fun e => dy e.t.val) ++ Brest.map (fun e => e.t.val.sec / 86400 + 1)
    ++ stepLows z dy r.slept (fun e => decide (K.cut + j < e.line)) (restore K n) r.survivors
    ++ machineDays (svj.foldl (Replay.stepWith z dy r.slept) (restore K n)).machine
  Nat.max K.ledgerDay (lows.foldl Nat.min (floorOf T p.keepDays dy r.survivors))

/-- The tag filter of `keptTags`, over a tag-line list: every known tag, and the first unknown tags of bounded length. -/
def keepTags (all : List (List Char × Nat)) : List (List Char × Nat) :=
  let unknownKept := ((all.filter (fun p => !Log.isKnownTag p.1 && decide (p.1.length ≤ maxTagChars))).take maxUnknownTags)
  all.filter (fun p => Log.isKnownTag p.1 || unknownKept.contains p)

/-- Two tag-line lists merged by tag, the newer list's line winning. -/
def mergeTagLines (old new : List (List Char × Nat)) : List (List Char × Nat) :=
  (canon idLt (old.map Prod.fst ++ new.map Prod.fst)).map (fun t =>
    (t, ((new.find? (fun p => p.1 == t)).map Prod.snd).getD (((old.find? (fun p => p.1 == t)).map Prod.snd).getD 0)))

/-- **The reseal of a run** (§9.4): the checkpoint at the fold point and the records it seals. -/
def resealOf (z : Cal.Tz) (T : Nat) (K : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) (r : Run) :
    Option Resealed :=
  let j := foldPointOf z T K b terminated p r
  if migrationOk K T && cutOk z T K b terminated p r j then
    let dy := Replay.dayOf z r.index
    let n := K.items.length + K.openDays.length + r.entries.length
    let Bj := r.entries.filter (fun e => decide (e.line ≤ K.cut + j))
    let svj := r.survivors.filter (fun e => decide (e.line ≤ K.cut + j))
    let Rj := svj.foldl (Replay.stepWith z dy r.slept) (restore K n)
    let kwj := Replay.keptWakes z (K.wakes ++ Replay.wakeInstants svj)
    let sleptj := K.sleptByDay ++ Replay.sleptByDay z kwj svj
    let st := rebindState (Replay.KMap.get sleptj) Rj
    let hsj := storedHeaders K ++ (tailHeaders dy K.settled r.entries).take Bj.length
    let L' := sealDayOf z T K p r j
    let QAj := Bj.flatMap entryInstants
    let merged := mergeTagLines K.tagLast (tagLines svj)
    let ws := (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ K.cut + j))
    let ck : Ckpt := ⟨ckptVersion, K.tzKey, K.cut + j, L', T,
      maxOptI K.maxT (maxInstant? (QAj.filter (fun q => !isFuture T q))),
      minOptI K.futureFloor (minInstant? (QAj.filter (isFuture T))),
      storedWakes L' kwj, storedSlept sleptj L', keepTags merged,
      K.tagOverflow || decide ((keepTags merged).length < merged.length),
      settledAt K r j, st.machine,
      (canon idLt (K.items.map (·.id) ++ itemIds st)).map (aggMerged K st),
      windowsFrom st (horizonOf L'), instOtherOf st, namedOf st, daysFrom st hsj L',
      maxOpt K.lastDay (Replay.maxDay? (st.days.pairs.map Prod.fst)), st.global.lastEffective,
      K.entryCount + Bj.length, st.unknown, st.longestLeak, st.rwarns.reverse,
      (K.warnings ++ ws).take maxWarnings, K.warnings.length + K.warnOverflow + ws.length - maxWarnings⟩
    some ⟨ck, ck.meta, (daysIn st hsj K.ledgerDay L').map (OpenDay.finish st.machine),
      windowsIn st (horizonOf K.ledgerDay) (horizonOf L')⟩
  else none

/-- **How many tail lines a reseal folds** (§15): the resume's greatest valid cut. -/
def foldPoint (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) : Nat :=
  match resumeRun z T k b with
  | .ok r => foldPointOf z T k b terminated p r
  | .error _ => 0

/-- **The new ledger day `L'`** (§15), at the fold point. -/
def sealDay (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Policy) : Nat :=
  match resumeRun z T k b with
  | .ok r => sealDayOf z T k p r (foldPointOf z T k b terminated p r)
  | .error _ => k.ledgerDay

/-- **Resume** (§9.4): the answer, and with a policy, the reseal. -/
def resume (z : Cal.Tz) (T : Nat) (k : Ckpt) (b : List Log.Line) (terminated : Bool) (p : Option Policy) :
    Except Refusal (Seal.Answer × Option Resealed) :=
  match resumeRun z T k b with
  | .error e => .error e
  | .ok r => .ok (r.answer, p.bind (fun q => resealOf z T k b terminated q r))

/-- **`redrawReadsFast` reads through the merge, and else through `redrawReads`** (README gap 5027): over the merge's
case the one new span's start; over old pieces out of order (the fallback) every new span's start not drawn before. -/
theorem redrawReadsFast_reads_through_the_merge_and_else_through_redrawReads :
    redrawReadsFast [⟨((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1, ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).2, 7⟩, ⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1,
        ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).2, 7⟩] [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)] = [((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1.1] ∧
    redrawReadsFast [⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).2, 7⟩, ⟨((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1,
        ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).2, 7⟩] [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At), (((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)] = [((((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩)) : Replay.At × Replay.At)).1.1] := by
  decide

end Seal
end Tm
