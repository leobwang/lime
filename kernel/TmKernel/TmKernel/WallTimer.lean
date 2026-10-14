import TmKernel.SealWire
import TmKernel.Lookahead

/-!
# WallTimer — the owner's D61, decided by the kernel (stage 6, W-37 track T, README gap 3139)

**D61** (2026-09-27, parity **P53**): a calendar wall that starts while a block runs STOPS THE
TIMER.  The log's own events are written — a `pause{id}` stamped at the wall's start and an
`unpause{id}` at its end — by the housekeeping of the first verb after the wall began (and after
it ended), so `tm now`'s worked minutes, `tm done`'s `actual_min` and the drawn history all net the
meeting out.  W-36 wrote that rule in Rust (`tm/src/cli/day.rs`, `stop_the_timer_at_walls`), over
the host's own reader of the calendar (`Ctx::walls_on`, fork `Ctx::walls_on`) — a SECOND reader of
the walls beside the kernel's `Look.wallsOn`, deciding one day (AGENTS §5.3), and a rule no Lean
statement named, so D40, checks 12 and 13 and the proofs could not see it (gap 3139).

**Here the kernel decides.**  `writes` is the rule, over the replay's own facts — the open block's
start and today's idle marks (`Seal.Answer`, D24's seam) — the day's walls as `Look.wallIxOn`
selects them from the plan the request loaded, joined as fork `merge_walls` joins them
(`Look.mergeSorted` over `Look.sortByStart`, REUSED), the running break `state.json` holds (the
one fact the log does not carry: a break is logged when it ends), and `now`.  The host asks with
the `emit` section's walls form (`Boundary.readEmitSection`), appends the lines the kernel renders
(`Log.emitLine`, D16's one writer), and no longer reads a wall to decide anything.

**The rule, as W-36 wrote it and as the host ran it, port for port** — fork `tm_core::log::idle_spans` (`idleSpans`;
the replay's two stops and no break's span since the W-44 repair, gap 4550), and `day.rs`' timer_stopped_at (`stoppedAt`),
touched_after (`touchedAfter`) and last_timer_mark (`lastTimerMark`), deleted from the host here.  For each joined span
`[lo, hi)` in order: a span that began at or before the block's start, or after `now`, is not the
block's; if no pause is logged at `lo`, the wall writes one there unless the timer was already
stopped at `lo` (a pause or an interruption covering it, or the running break) or a timer
mark was stamped after `lo` (the user has been deciding since); and once `hi` has passed, it writes
an `unpause` at `hi` if none is logged there and the wall's own pause is still the last word on the
timer.  Its laws are below, each named for the case it is about:
`a_wall_that_starts_while_a_block_runs_stops_its_timer`, and the four ways it writes nothing.
-/

namespace Tm
namespace WallTimer

/-- A mark's instant: its entry's stamp, the offset aside — chrono compares instants. -/
def markAt : Replay.IdleMark → Cal.Instant
  | .pause t | .interrupt t | .unpause t | .resume t | .brk t _ => t.1

/-- Whether a mark is a `break` (the one kind the host's last_timer_mark passed over). -/
def isBrk : Replay.IdleMark → Bool
  | .brk _ _ => true
  | _ => false

/-- Whether a mark is a pause stamped at `t`. -/
def pauseAt (t : Cal.Instant) : Replay.IdleMark → Bool
  | .pause a => a.1 == t
  | _ => false

/-- Whether a mark is an unpause stamped at `t`. -/
def unpauseAt (t : Cal.Instant) : Replay.IdleMark → Bool
  | .unpause a => a.1 == t
  | _ => false

/-- One mark of the timer's pairing — TWO stops, each closed only by its own end (W-44 repair, README gaps 4550 and
4610): a pause opens the block's pause (one before `started` was another block's) and only an unpause closes it; an
interruption opens the interruption and only a resume closes it — the replay's machine (`Replay.arm`, `resumeBlock`).
A `break` opens and closes nothing: it is not the USER's stop, so one that covered a wall's start and ended inside the
meeting no longer leaves the meeting unpaused; the running break is the caller's (`idleSpans`' `brk`, which waits). -/
def spanStep (started : Cal.Instant) (st : (Option Cal.Instant × Option Cal.Instant) × List (Cal.Instant × Option Cal.Instant))
    (m : Replay.IdleMark) : (Option Cal.Instant × Option Cal.Instant) × List (Cal.Instant × Option Cal.Instant) :=
  match m with
  | .pause t => if t.1 < started then st else ((st.1.1.or (some t.1), st.1.2), st.2)
  | .unpause t => (match st.1.1 with | some a => ((none, st.1.2), st.2 ++ [(a, some t.1)]) | none => st)
  | .interrupt t => ((st.1.1, st.1.2.or (some t.1)), st.2)
  | .resume t => (match st.1.2 with | some a => ((st.1.1, none), st.2 ++ [(a, some t.1)]) | none => st)
  | .brk _ _ => st

/-- **The user's stops of the block begun at `started`** (D61's question, README gap 4550): the closed pauses and
interruptions, the pause and the interruption still open, then the running break — `none` for an end still open. -/
def idleSpans (marks : List Replay.IdleMark) (started : Cal.Instant) (brk : Option Cal.Instant) :
    List (Cal.Instant × Option Cal.Instant) :=
  (marks.foldl (spanStep started) ((none, none), [])).2 ++
    ((marks.foldl (spanStep started) ((none, none), [])).1.1.map (fun a => (a, none))).toList ++
    ((marks.foldl (spanStep started) ((none, none), [])).1.2.map (fun a => (a, none))).toList ++
    (brk.map (fun s => (s, none))).toList

/-- **Was the timer stopped at `t`** (the host's timer_stopped_at, W-36): an idle span covers it. -/
def stoppedAt (marks : List Replay.IdleMark) (started t : Cal.Instant) (brk : Option Cal.Instant) : Bool :=
  (idleSpans marks started brk).any fun sp =>
    decide (sp.1 ≤ t) && (match sp.2 with | none => true | some b => decide (t < b))

/-- **Did anything touch the timer after `t`** (the host's touched_after): a mark stamped later.
Written by recursion on the marks rather than as `List.any` (W-37 repair, README gap 3333): as a
one-line wrapper the compiler specialised its `List.any` into `step` and the symbol itself was
called by nothing but its boxed shell, which check 12 must then exempt by name (D51: that file
only shrinks).  `touchedAfter_eq_any` is the old definition, proved. -/
def touchedAfter : List Replay.IdleMark → Cal.Instant → Bool
  | [], _ => false
  | m :: ms, t => decide (t < markAt m) || touchedAfter ms t

theorem touchedAfter_eq_any (marks : List Replay.IdleMark) (t : Cal.Instant) :
    touchedAfter marks t = marks.any fun m => decide (t < markAt m) := by
  induction marks with
  | nil => rfl
  | cons m ms ih => simp [touchedAfter, ih]

/-- Whether a mark is an interruption's — an `interrupt` or a `resume` (the owner's **D117**, README gaps 5036 and 3042):
the other stop's marks (`spanStep`), which say nothing of the block's pause. -/
def isIntMark : Replay.IdleMark → Bool
  | .interrupt _ | .resume _ => true
  | _ => false

/-- **The last mark that set the block's pause** — the host's last_timer_mark: the last that is not a break, and,
since the owner's **D117**, not an interruption's (`isIntMark`).  Until W-48 an interruption taken and resumed inside a
meeting the wall had paused made its `resume` the last word, and the wall's end wrote no unpause: the block stayed
paused past the meeting — resumed inside a wall and paused not "until the wall ends" (README gap 3042).  A `resume`
ends the interruption, not the pause (`spanStep`, `Replay.resumeBlock`). -/
def lastTimerMark (marks : List Replay.IdleMark) : Option Replay.IdleMark :=
  (marks.filter fun m => !isBrk m && !isIntMark m).getLast?

/-- Whether the wall's pause at `lo` is still the last word on the timer. -/
def lastIsPauseAt (marks : List Replay.IdleMark) (lo : Cal.Instant) : Bool :=
  match lastTimerMark marks with
  | some m => pauseAt lo m
  | none => false

/-- The mark a written pause or unpause adds (its offset is the wire's business, not the rule's). -/
def markOf (pause : Bool) (t : Cal.Instant) : Replay.IdleMark :=
  if pause then .pause (t, Cal.Offset.utc) else .unpause (t, Cal.Offset.utc)

/-- **The first whole second at or after an instant** — marks are written in whole seconds. -/
def ceilSec (t : Cal.Instant) : Nat := if t.ns = 0 then t.sec else t.sec + 1

/-- **The second a span's pause would be stamped at, by the owner's D110** (README gap 4748, parity P106): the span's
own start `lo` when the wall began while the block ran (D61), and the block's own start — its first whole second at or
after it — when the block began inside the wall.  Until W-48 this was `pauseSec`; since the owner's D117 the pause
second can be a resume's (`pauseSec`). -/
def startSec (started : Cal.Instant) (s : Nat × Nat) : Nat :=
  max s.1 (ceilSec started)

/-- One mark of the interruptions' pairing (the owner's **D117**): `spanStep`'s interruption half alone — an
`interrupt` opens one (a second while one is open opens nothing) and only a `resume` closes it, the closed one
appended as `[from, until)`. -/
def intStep (st : Option Cal.Instant × List (Cal.Instant × Cal.Instant)) (m : Replay.IdleMark) :
    Option Cal.Instant × List (Cal.Instant × Cal.Instant) :=
  match m with
  | .interrupt t => (st.1.or (some t.1), st.2)
  | .resume t => (match st.1 with | some a => (none, st.2 ++ [(a, t.1)]) | none => st)
  | _ => st

/-- **The interruptions the marks close** (D117), in order. -/
def intSpans (marks : List Replay.IdleMark) : List (Cal.Instant × Cal.Instant) :=
  (marks.foldl intStep (none, [])).2

/-- **The second a span's pause is stamped at** — D110's (`startSec`), unless an interruption the log closes covers it
and its `resume` falls inside the wall: then the resume's first whole second (the owner's **D117**, README gaps 5036
and 3042, parity **P116**), so a block RESUMED inside a calendar wall is paused from its resume until the wall ends, as
one begun inside it is paused from its start.  Until W-48 the interruption covering the wall's start stood for the
wall's stop (`stoppedAt`) and nothing was written, so the timer ran from the resume through the rest of the meeting
(driven: `start` 12:00, `interrupt` 12:40, `resume` 13:00 in a 12:50–13:50 meeting, `stop` 14:00 — `after 100m`). -/
def pauseSec (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat) : Nat :=
  match ints.find? (fun i => decide (i.1 ≤ ⟨startSec started s, 0⟩) &&
      decide ((⟨startSec started s, 0⟩ : Cal.Instant) < i.2) && decide (ceilSec i.2 < s.2)) with
  | some i => ceilSec i.2
  | none => startSec started s

theorem instant_le_ceilSec (t : Cal.Instant) : t ≤ ⟨ceilSec t, 0⟩ := by
  rw [Cal.Instant.le_iff]; unfold ceilSec
  by_cases h : t.ns = 0 <;> simp [h]

theorem lt_ceilSec_of_lt (p : Nat) (t : Cal.Instant) (h : (⟨p, 0⟩ : Cal.Instant) < t) : p < ceilSec t := by
  rw [Cal.Instant.lt_iff] at h; simp only at h; unfold ceilSec; split <;> omega

theorem ceilSec_le_of_le (t : Cal.Instant) (p : Nat) (h : t ≤ ⟨p, 0⟩) : ceilSec t ≤ p := by
  rw [Cal.Instant.le_iff] at h; simp only at h; unfold ceilSec; split <;> omega

/-- **The pause second is never before D110's** (`startSec`): a resume moves it later, never earlier. -/
theorem startSec_le_pauseSec (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat) :
    startSec started s ≤ pauseSec started ints s := by
  unfold pauseSec
  split
  · rename_i i hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact Nat.le_of_lt (lt_ceilSec_of_lt _ _ hp.1.2)
  · exact Nat.le_refl _

/-- **The pause second is D110's or before the wall's end**: a resume moves it only to a second inside the wall. -/
theorem pauseSec_cases (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat) :
    pauseSec started ints s = startSec started s ∨ pauseSec started ints s < s.2 := by
  unfold pauseSec
  split
  · rename_i i hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact Or.inr hp.2
  · exact Or.inl rfl

/-- **With no interruption the log closes covering D110's second, the pause is stamped there.** -/
theorem pauseSec_of_uncovered (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat)
    (h : ∀ i ∈ ints, ¬ (i.1 ≤ ⟨startSec started s, 0⟩ ∧ (⟨startSec started s, 0⟩ : Cal.Instant) < i.2)) :
    pauseSec started ints s = startSec started s := by
  unfold pauseSec
  split
  · rename_i i hf
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact absurd ⟨hp.1.1, hp.1.2⟩ (h i hm)
  · rfl

/-- **A wall that began while the block ran is paused at its own start** — D61's case, unchanged by D110, and by the
owner's D117 where no interruption the log closes covers the wall's start.  **Restated at D117** (W-48 track K): the
statement without `hu` is refuted (`pauseSec_of_lt_as_d110_wrote_it_is_refuted`). -/
theorem pauseSec_of_lt (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat)
    (h : started < ⟨s.1, 0⟩) (hu : ∀ i ∈ ints, ¬ (i.1 ≤ ⟨s.1, 0⟩ ∧ (⟨s.1, 0⟩ : Cal.Instant) < i.2)) :
    pauseSec started ints s = s.1 := by
  have hs : startSec started s = s.1 := by
    unfold startSec
    have := ceilSec_le_of_le started s.1 (by
      rw [Cal.Instant.lt_iff] at h; rw [Cal.Instant.le_iff]; simp only at h ⊢; omega)
    omega
  rw [pauseSec_of_uncovered started ints s (by rw [hs]; exact hu), hs]

/-- **"A wall that began while the block ran is paused at its own start", as D110 wrote it, refuted by D117**: the
block begun at 500 and interrupted 900–1200 across the wall `[1000, 2000)`'s start is paused at its resume, 1200. -/
theorem pauseSec_of_lt_as_d110_wrote_it_is_refuted :
    ¬ ∀ (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat), started < ⟨s.1, 0⟩ →
      pauseSec started ints s = s.1 := by
  intro h
  have := h ⟨500, 0⟩ [(⟨900, 0⟩, ⟨1200, 0⟩)] (1000, 2000) (by decide)
  revert this; decide

/-- **The pause second is never before the block's start, nor before the wall's** (D110, and D117's). -/
theorem pauseSec_ge (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat) :
    s.1 ≤ pauseSec started ints s ∧ started ≤ ⟨pauseSec started ints s, 0⟩ := by
  have h1 := startSec_le_pauseSec started ints s
  have h2 := instant_le_ceilSec started
  refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, ?_⟩
  have h3 : ceilSec started ≤ pauseSec started ints s := Nat.le_trans (Nat.le_max_right _ _) h1
  rw [Cal.Instant.le_iff] at h2 ⊢; simp only at h2 ⊢; omega

/-- The two pairings agree on the interruption: `spanStep`'s open interruption is `intStep`'s, and every interruption
`intStep` closes `spanStep` closes too (D117). -/
theorem intSpans_fold (started : Cal.Instant) : ∀ (marks : List Replay.IdleMark)
    (p i : Option Cal.Instant) (l : List (Cal.Instant × Option Cal.Instant)) (k : List (Cal.Instant × Cal.Instant)),
    (∀ x ∈ k, (x.1, some x.2) ∈ l) →
    (marks.foldl (spanStep started) ((p, i), l)).1.2 = (marks.foldl intStep (i, k)).1 ∧
      ∀ x ∈ (marks.foldl intStep (i, k)).2, (x.1, some x.2) ∈ (marks.foldl (spanStep started) ((p, i), l)).2
  | [], _, _, _, _, h2 => ⟨rfl, h2⟩
  | m :: ms, p, i, l, k, h2 => by
    cases m with
    | pause t =>
      simp only [List.foldl_cons, spanStep, intStep]
      split
      · exact intSpans_fold started ms p i l k h2
      · exact intSpans_fold started ms _ i l k h2
    | unpause t =>
      simp only [List.foldl_cons, spanStep, intStep]
      split
      · exact intSpans_fold started ms _ i _ k (fun x hx => List.mem_append_left _ (h2 x hx))
      · exact intSpans_fold started ms _ i _ k h2
    | interrupt t =>
      simp only [List.foldl_cons, spanStep, intStep]
      exact intSpans_fold started ms p _ l k h2
    | resume t =>
      simp only [List.foldl_cons, spanStep, intStep]
      cases i with
      | none => exact intSpans_fold started ms p none l k h2
      | some a =>
        apply intSpans_fold started ms p none _ _
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact List.mem_append_left _ (h2 x hx)
        · simp only [List.mem_singleton] at hx; subst hx; simp
    | brk t a => exact intSpans_fold started ms p i l k h2

/-- **Every interruption the log closes is one of the user's stops** (`idleSpans`, D117). -/
theorem intSpans_sub (marks : List Replay.IdleMark) (started : Cal.Instant) (brk : Option Cal.Instant)
    (i : Cal.Instant × Cal.Instant) (h : i ∈ intSpans marks) : (i.1, some i.2) ∈ idleSpans marks started brk := by
  have := (intSpans_fold started marks none none [] [] (by simp)).2 i h
  unfold idleSpans
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ this))

/-- **A timer running at `t` has no interruption the log closes covering `t`** (D117). -/
theorem not_covered_of_not_stopped (marks : List Replay.IdleMark) (started t : Cal.Instant) (brk : Option Cal.Instant)
    (h : stoppedAt marks started t brk = false) : ∀ i ∈ intSpans marks, ¬ (i.1 ≤ t ∧ t < i.2) := by
  intro i hi hc
  unfold stoppedAt at h
  have := List.any_eq_false.1 h _ (intSpans_sub marks started brk i hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this ⟨hc.1, hc.2⟩

/-- `intStep` passes over a written mark. -/
theorem intStep_markOf (st : Option Cal.Instant × List (Cal.Instant × Cal.Instant)) (b : Bool) (t : Cal.Instant) :
    intStep st (markOf b t) = st := by
  unfold markOf; split <;> rfl

/-- **A break that has run since before the wall's end holds the block** (the owner's **D114**, README gap 5014,
parity **P115**): the running break `brk` began before `hi`.  While it runs the wall's `unpause` is not written — it is
written once the break has ended, by the verb that ends it — so a block is never working and on break at once.  A break
begun at or after `hi` began once the wall had ended, and holds nothing of it. -/
def breakHolds (brk : Option Cal.Instant) (hi : Nat) : Bool :=
  match brk with
  | some b => decide (b < ⟨hi, 0⟩)
  | none => false

/-- The pause half of a span: the pause at the span's pause second (`pauseSec`) is written unless one is logged there. -/
def pauseIfNew (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (s : Nat × Nat)
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) : List Replay.IdleMark × List (Bool × Nat × Nat) :=
  if acc.1.any (pauseAt ⟨pauseSec started ints s, 0⟩) then acc
  else (acc.1 ++ [markOf true ⟨pauseSec started ints s, 0⟩], acc.2 ++ [(true, s)])

/-- The unpause half: once `hi` has passed, an unpause at `hi` is written if none is logged there, the span's pause is
still the last word on the timer and — since the owner's **D114** — no break running since before `hi` holds the block
(`breakHolds`). -/
def unpauseIfDone (started now : Cal.Instant) (brk : Option Cal.Instant) (ints : List (Cal.Instant × Cal.Instant))
    (s : Nat × Nat) (a1 : List Replay.IdleMark × List (Bool × Nat × Nat)) :
    List Replay.IdleMark × List (Bool × Nat × Nat) :=
  if (decide ((⟨s.2, 0⟩ : Cal.Instant) ≤ now) && !(a1.1.any (unpauseAt ⟨s.2, 0⟩)) &&
      lastIsPauseAt a1.1 ⟨pauseSec started ints s, 0⟩ && !breakHolds brk s.2) = true
  then (a1.1 ++ [markOf false ⟨s.2, 0⟩], a1.2 ++ [(false, s)])
  else a1

/-- **One joined wall span `[lo, hi)`, in whole seconds**, against the marks so far: what it writes,
`(true, span)` for a pause at its pause second (`pauseSec`: `lo`, or the block's start when the block began inside the
wall — the owner's D110 — or the resume of an interruption that covered it — D117) and `(false, span)` for an unpause at
`hi`, and the marks with what it wrote appended (the log grows in file order).  A span that ended by the block's start
is not the block's, nor one whose pause second is after `now`.  `ints` is the interruptions the log closes
(`intSpans`). -/
def step (started now : Cal.Instant) (brk : Option Cal.Instant) (ints : List (Cal.Instant × Cal.Instant))
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (s : Nat × Nat) :
    List Replay.IdleMark × List (Bool × Nat × Nat) :=
  if ((⟨s.1, 0⟩ : Cal.Instant) ≤ started ∧ (⟨s.2, 0⟩ : Cal.Instant) ≤ started) ∨
      now < ⟨pauseSec started ints s, 0⟩ then acc
  else if (!(acc.1.any (pauseAt ⟨pauseSec started ints s, 0⟩)) &&
      (stoppedAt acc.1 started ⟨pauseSec started ints s, 0⟩ brk ||
        touchedAfter acc.1 ⟨pauseSec started ints s, 0⟩)) = true
    then acc
  else unpauseIfDone started now brk ints s (pauseIfNew started ints s acc)

/-- **What the day's walls write** (D61, P53), in order: a pause at a span's pause second, an unpause at
its end, over the block begun at `started`, the log's marks of the day, the running break and
`now`. -/
def writes (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark)
    (spans : List (Nat × Nat)) : List (Bool × Nat × Nat) :=
  (spans.foldl (step started now brk (intSpans marks)) (marks, [])).2

/-! ## The laws — one span, the day as a user has it -/

theorem inst_le (a b : Nat) : (⟨a, 0⟩ : Cal.Instant) ≤ ⟨b, 0⟩ ↔ a ≤ b := by
  rw [Cal.Instant.le_iff]; simp only; omega

theorem inst_lt (a b : Nat) : (⟨a, 0⟩ : Cal.Instant) < ⟨b, 0⟩ ↔ a < b := by
  rw [Cal.Instant.lt_iff]; simp only; omega

theorem hasUnpause_none_of_untouched (marks : List Replay.IdleMark) (lo hi : Cal.Instant)
    (ht : touchedAfter marks lo = false) (hlt : lo < hi) : marks.any (unpauseAt hi) = false := by
  rw [touchedAfter_eq_any] at ht
  rw [List.any_eq_false] at ht ⊢
  intro m hm hu
  have := ht m hm
  cases m with
  | unpause a =>
    simp only [unpauseAt, beq_iff_eq] at hu
    simp only [markAt] at this
    exact this (decide_eq_true (by rw [hu]; exact hlt))
  | pause a => simp [unpauseAt] at hu
  | interrupt a => simp [unpauseAt] at hu
  | resume a => simp [unpauseAt] at hu
  | brk a b => simp [unpauseAt] at hu

theorem lastIsPauseAt_append (marks : List Replay.IdleMark) (lo : Cal.Instant) :
    lastIsPauseAt (marks ++ [markOf true lo]) lo = true := by
  simp [lastIsPauseAt, lastTimerMark, markOf, isBrk, isIntMark, pauseAt, List.filter_append]

/-- The span's two gates, when the block began before the wall, the wall has begun and the span's pause second is its
start (**restated at the owner's D117**: `hps`, which D61's and D110's rule gave for nothing). -/
theorem step_of_running (started now : Cal.Instant) (brk : Option Cal.Instant) (ints : List (Cal.Instant × Cal.Instant))
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (s : Nat × Nat)
    (h1 : started < ⟨s.1, 0⟩) (h2 : (⟨s.1, 0⟩ : Cal.Instant) ≤ now) (hps : pauseSec started ints s = s.1) :
    step started now brk ints acc s =
      if (!(acc.1.any (pauseAt ⟨s.1, 0⟩)) &&
        (stoppedAt acc.1 started ⟨s.1, 0⟩ brk || touchedAfter acc.1 ⟨s.1, 0⟩)) = true then acc
      else unpauseIfDone started now brk ints s (pauseIfNew started ints s acc) := by
  have hn : ¬ (((⟨s.1, 0⟩ : Cal.Instant) ≤ started ∧ (⟨s.2, 0⟩ : Cal.Instant) ≤ started) ∨
      now < ⟨s.1, 0⟩) := by
    rintro (⟨h, -⟩ | h)
    · exact absurd (Cal.Instant.lt_iff _ _ |>.1 h1) (by rw [Cal.Instant.le_iff] at h; omega)
    · exact absurd h ((Cal.Instant.not_lt _ _).2 h2)
  simp only [step, hps]
  rw [if_neg hn]

/-- **D61: a wall that starts while a block runs stops its timer at the wall's start** — and, once the wall has ended
and no break running since before its end holds the block (the owner's **D114**, `breakHolds`), restarts it at its
end.  The block began before the wall (`started < lo`), the wall has begun (`lo ≤ now`), nothing is logged at `lo` yet,
the log had the timer RUNNING at `lo` and nothing has touched it since: the one span writes a pause at `lo`, and an
unpause at `hi` when `hi` has passed and no break holds it.  **Restated at D114** (W-48 track K): D61's statement, the
unpause whenever `hi` has passed, is refuted
(`a_wall_that_starts_while_a_block_runs_stops_its_timer_as_d61_wrote_it_is_refuted`). -/
theorem a_wall_that_starts_while_a_block_runs_stops_its_timer (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h1 : started < ⟨lo, 0⟩) (h2 : (⟨lo, 0⟩ : Cal.Instant) ≤ now) (hlh : lo < hi)
    (hp : marks.any (pauseAt ⟨lo, 0⟩) = false) (hs : stoppedAt marks started ⟨lo, 0⟩ brk = false)
    (ht : touchedAfter marks ⟨lo, 0⟩ = false) :
    writes started now brk marks [(lo, hi)] =
      (true, lo, hi) :: (if (⟨hi, 0⟩ : Cal.Instant) ≤ now ∧ breakHolds brk hi = false then [(false, lo, hi)]
        else []) := by
  have hps : pauseSec started (intSpans marks) (lo, hi) = lo :=
    pauseSec_of_lt started _ (lo, hi) h1 (not_covered_of_not_stopped marks started ⟨lo, 0⟩ brk hs)
  have hu : (marks ++ [markOf true ⟨lo, 0⟩]).any (unpauseAt ⟨hi, 0⟩) = false := by
    rw [List.any_append, hasUnpause_none_of_untouched marks ⟨lo, 0⟩ ⟨hi, 0⟩ ht ((inst_lt _ _).2 hlh)]
    simp [markOf, unpauseAt]
  simp only [writes, List.foldl, step_of_running started now brk _ (marks, []) (lo, hi) h1 h2 hps]
  simp only [hp, hs, ht, Bool.not_false, Bool.or_false, Bool.and_false, Bool.false_eq_true, if_false,
    pauseIfNew, unpauseIfDone, hps, hu, lastIsPauseAt_append, Bool.not_false, Bool.and_true]
  by_cases hh : (⟨hi, 0⟩ : Cal.Instant) ≤ now
  · cases breakHolds brk hi <;> simp [hh]
  · simp [hh]

/-- **D61's law as it stood, refuted by the owner's D114** (README gap 5014, parity P115): a block begun at 500, the
wall `[1000, 2000)`, a break running since 1200 — asked at 2500 the wall writes its pause and NOT its unpause, which
waits for the break to end. -/
theorem a_wall_that_starts_while_a_block_runs_stops_its_timer_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      started < ⟨lo, 0⟩ → (⟨lo, 0⟩ : Cal.Instant) ≤ now → lo < hi → marks.any (pauseAt ⟨lo, 0⟩) = false →
      stoppedAt marks started ⟨lo, 0⟩ brk = false → touchedAfter marks ⟨lo, 0⟩ = false →
      writes started now brk marks [(lo, hi)] =
        (true, lo, hi) :: (if (⟨hi, 0⟩ : Cal.Instant) ≤ now then [(false, lo, hi)] else []) := by
  intro h
  have := h ⟨500, 0⟩ ⟨2500, 0⟩ (some ⟨1200, 0⟩) [] 1000 2000 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  revert this; decide

/-- **D61's "a block started inside a wall is not paused by it", refuted by D110** (README gap 4748, parity P106): a
block begun at 1500 inside the wall `[1000, 2000)`, asked at 1800 with nothing logged, is paused at its start. -/
theorem a_block_started_inside_a_wall_is_not_paused_by_it_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      (⟨lo, 0⟩ : Cal.Instant) ≤ started → writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨1500, 0⟩ ⟨1800, 0⟩ none [] 1000 2000 (by decide)
  revert this; decide

/-- **A span whose pause second has come is paused there** — D61's law, D110's and D117's at once: the span did not end
by the block's start, its pause second (`pauseSec`, over the interruptions the log closes) is before its end and has
come (`≤ now`), nothing is logged there, the timer was running there and nothing has touched it since: the one span
writes the pause, and the unpause at `hi` once `hi` has passed and no break running since before it holds the block
(D114).  **Restated at D114 and D117** (W-48 track K); D110's statement is refuted
(`a_span_whose_pause_second_has_come_is_paused_as_d110_wrote_it_is_refuted`). -/
theorem a_span_whose_pause_second_has_come_is_paused (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hin : pauseSec started (intSpans marks) (lo, hi) < hi)
    (h2 : (⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ : Cal.Instant) ≤ now)
    (hp : marks.any (pauseAt ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) = false)
    (hs : stoppedAt marks started ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ brk = false)
    (ht : touchedAfter marks ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ = false) :
    writes started now brk marks [(lo, hi)] =
      (true, lo, hi) :: (if (⟨hi, 0⟩ : Cal.Instant) ≤ now ∧ breakHolds brk hi = false then [(false, lo, hi)]
        else []) := by
  have hstart := (pauseSec_ge started (intSpans marks) (lo, hi)).2
  have hn : ¬ (((⟨lo, 0⟩ : Cal.Instant) ≤ started ∧ (⟨hi, 0⟩ : Cal.Instant) ≤ started) ∨
      now < ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) := by
    rintro (⟨-, h⟩ | h)
    · rw [Cal.Instant.le_iff] at h hstart; simp only at h hstart; omega
    · exact absurd h ((Cal.Instant.not_lt _ _).2 h2)
  have hu : (marks ++ [markOf true ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩]).any (unpauseAt ⟨hi, 0⟩)
      = false := by
    rw [List.any_append, hasUnpause_none_of_untouched marks _ ⟨hi, 0⟩ ht ((inst_lt _ _).2 hin)]
    simp [markOf, unpauseAt]
  simp only [writes, List.foldl, step, if_neg hn]
  simp only [hp, hs, ht, Bool.not_false, Bool.or_false, Bool.and_false, Bool.false_eq_true, if_false,
    pauseIfNew, unpauseIfDone, hu, lastIsPauseAt_append, Bool.not_false, Bool.and_true]
  by_cases hh : (⟨hi, 0⟩ : Cal.Instant) ≤ now
  · cases breakHolds brk hi <;> simp [hh]
  · simp [hh]

/-- **D110's law as it stood, refuted by the owner's D114**: a block begun at 500, the wall `[1000, 2000)`, a break
running since 1200, asked at 2500 — the span is paused at 1000 (D110's pause second, `startSec`) and its unpause waits
for the break. -/
theorem a_span_whose_pause_second_has_come_is_paused_as_d110_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      startSec started (lo, hi) < hi → (⟨startSec started (lo, hi), 0⟩ : Cal.Instant) ≤ now →
      marks.any (pauseAt ⟨startSec started (lo, hi), 0⟩) = false →
      stoppedAt marks started ⟨startSec started (lo, hi), 0⟩ brk = false →
      touchedAfter marks ⟨startSec started (lo, hi), 0⟩ = false →
      writes started now brk marks [(lo, hi)] =
        (true, lo, hi) :: (if (⟨hi, 0⟩ : Cal.Instant) ≤ now then [(false, lo, hi)] else []) := by
  intro h
  have := h ⟨500, 0⟩ ⟨2500, 0⟩ (some ⟨1200, 0⟩) [] 1000 2000 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  revert this; decide

/-- **A wall that ended by the block's start is not the block's** — D61's law of a block started inside a wall, on the
subdomain D110 leaves it: the wall began and ended at or before the block's start. -/
theorem a_wall_that_ended_before_the_block_began_writes_nothing (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h1 : (⟨lo, 0⟩ : Cal.Instant) ≤ started) (h2 : (⟨hi, 0⟩ : Cal.Instant) ≤ started) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp [writes, step, h1, h2]

/-- **A wall that has not begun writes nothing.** -/
theorem a_wall_that_has_not_begun_writes_nothing (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h : now < ⟨lo, 0⟩) : writes started now brk marks [(lo, hi)] = [] := by
  have hl := (pauseSec_ge started (intSpans marks) (lo, hi)).1
  have h' : now < ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ := by
    rw [Cal.Instant.lt_iff] at h ⊢; simp only at h ⊢; omega
  simp [writes, step, h']

/-- **"A timer already stopped at the wall's start is left alone", read at the wall's start, refuted by D110**: a
block begun at 1500 inside the wall `[1000, 2000)` with an interruption 900–1200 before it — the timer was stopped at
the wall's start, not at the block's — is paused at its start. -/
theorem a_timer_already_stopped_at_the_wall_is_left_alone_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      marks.any (pauseAt ⟨lo, 0⟩) = false → stoppedAt marks started ⟨lo, 0⟩ brk = true →
        writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨1500, 0⟩ ⟨1800, 0⟩ none
    [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide)
  revert this; decide

/-- **"A timer already stopped at the span's pause second is left alone", read at D110's second, refuted by the
owner's D117** (README gaps 5036 and 3042, parity P116): a block begun at 500, interrupted 900–1200 across the wall
`[1000, 2000)`'s start — the timer stopped at 1000 — is paused at its resume, 1200, and unpaused at the wall's end. -/
theorem a_timer_already_stopped_at_the_wall_is_left_alone_as_d110_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      marks.any (pauseAt ⟨startSec started (lo, hi), 0⟩) = false →
      stoppedAt marks started ⟨startSec started (lo, hi), 0⟩ brk = true →
        writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨500, 0⟩ ⟨2500, 0⟩ none
    [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide)
  revert this; decide

/-- **A timer already stopped at the span's pause second is not the wall's to stop** — a pause or an interruption
covered it, or the running break does (the rule waits for it to be logged).  The pause second is the wall's start
(D61), the block's when it began inside the wall (D110), or the resume of an interruption the log closes across D110's
second (D117).  **Restated at D117** over that pause second. -/
theorem a_timer_already_stopped_at_the_wall_is_left_alone (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hp : marks.any (pauseAt ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) = false)
    (hs : stoppedAt marks started ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ brk = true) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp only [writes, List.foldl, step]
  split
  · rfl
  · simp [hp, hs]

/-- **"A timer mark stamped after the wall's start stands", read at the wall's start, refuted by D110**: a block begun
at 1500 inside the wall `[1000, 2000)` with an `unpause` at 1200 (another block's, before this one began) is paused at
its start — nothing has touched ITS timer since. -/
theorem a_timer_mark_after_the_walls_start_stands_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      marks.any (pauseAt ⟨lo, 0⟩) = false → touchedAfter marks ⟨lo, 0⟩ = true →
        writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨1500, 0⟩ ⟨1800, 0⟩ none [.unpause ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide)
  revert this; decide

/-- **"A timer mark stamped after the span's pause second stands", read at D110's second, refuted by the owner's
D117**: the `resume` at 1200 of an interruption across the wall `[1000, 2000)`'s start is not a decision the wall
leaves standing — the block is paused from it. -/
theorem a_timer_mark_after_the_walls_start_stands_as_d110_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      marks.any (pauseAt ⟨startSec started (lo, hi), 0⟩) = false →
      touchedAfter marks ⟨startSec started (lo, hi), 0⟩ = true →
        writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨500, 0⟩ ⟨2500, 0⟩ none
    [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide)
  revert this; decide

/-- **A timer mark stamped after the span's pause second stands**: the user has been deciding what the timer did
since, and the wall writes nothing under it.  **Restated at D117** over the pause second. -/
theorem a_timer_mark_after_the_walls_start_stands (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hp : marks.any (pauseAt ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) = false)
    (ht : touchedAfter marks ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ = true) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp only [writes, List.foldl, step]
  split
  · rfl
  · simp [hp, ht]

/-- **The wall's end restarts the timer it stopped**: with the wall's pause logged (by an earlier verb) at the span's
pause second and still the last word on the timer, a verb after the wall ended writes the unpause, once — when no break
running since before the wall's end holds the block (the owner's **D114**).  **Restated at D114 and D117** (the pause
second, `pauseSec`, in place of `lo`); D61's statement is refuted
(`the_walls_end_restarts_the_timer_it_stopped_as_d61_wrote_it_is_refuted`). -/
theorem the_walls_end_restarts_the_timer_it_stopped (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (h1 : started < ⟨lo, 0⟩) (h2 : (⟨lo, 0⟩ : Cal.Instant) ≤ now) (h3 : (⟨hi, 0⟩ : Cal.Instant) ≤ now)
    (hp : marks.any (pauseAt ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) = true)
    (hu : marks.any (unpauseAt ⟨hi, 0⟩) = false)
    (hl : lastIsPauseAt marks ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ = true)
    (hb : breakHolds brk hi = false) :
    writes started now brk marks [(lo, hi)] = [(false, lo, hi)] := by
  have hss : startSec started (lo, hi) = lo := by
    unfold startSec
    have := ceilSec_le_of_le started lo (by
      rw [Cal.Instant.lt_iff] at h1; rw [Cal.Instant.le_iff]; simp only at h1 ⊢; omega)
    simp only; omega
  have hn : ¬ (((⟨lo, 0⟩ : Cal.Instant) ≤ started ∧ (⟨hi, 0⟩ : Cal.Instant) ≤ started) ∨
      now < ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) := by
    rintro (⟨h, -⟩ | h)
    · exact absurd (Cal.Instant.lt_iff _ _ |>.1 h1) (by rw [Cal.Instant.le_iff] at h; omega)
    · rcases pauseSec_cases started (intSpans marks) (lo, hi) with hc | hc
      · rw [hc, hss] at h; exact absurd h ((Cal.Instant.not_lt _ _).2 h2)
      · rw [Cal.Instant.lt_iff, Cal.Instant.le_iff] at *; simp only at *; omega
  simp only [writes, List.foldl, step, if_neg hn]
  simp [hp, pauseIfNew, unpauseIfDone, h3, hu, hl, hb]

/-- **D61's law as it stood, refuted by the owner's D114**: the wall's pause logged at 1000 and still the last word, a
break running since 1200 — asked at 2500 the wall writes nothing; its unpause waits for the break. -/
theorem the_walls_end_restarts_the_timer_it_stopped_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      started < ⟨lo, 0⟩ → (⟨lo, 0⟩ : Cal.Instant) ≤ now → (⟨hi, 0⟩ : Cal.Instant) ≤ now →
      marks.any (pauseAt ⟨lo, 0⟩) = true → marks.any (unpauseAt ⟨hi, 0⟩) = false →
      lastIsPauseAt marks ⟨lo, 0⟩ = true → writes started now brk marks [(lo, hi)] = [(false, lo, hi)] := by
  intro h
  have := h ⟨500, 0⟩ ⟨2500, 0⟩ (some ⟨1200, 0⟩) [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  revert this; decide

/-- **"A user who resumed during the meeting keeps their timer", read at the wall's start, refuted by D110**: a block
begun at 1500 inside the wall `[1000, 2000)`, with another block's pause at 1000 unpaused at 1100, is paused at its
start — the pause at the wall's start was not this block's. -/
theorem a_user_who_resumed_during_the_meeting_keeps_their_timer_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      marks.any (pauseAt ⟨lo, 0⟩) = true → lastIsPauseAt marks ⟨lo, 0⟩ = false →
        writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨1500, 0⟩ ⟨1800, 0⟩ none
    [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨1100, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide)
  revert this; decide

/-- **"A user who resumed during the meeting keeps their timer", read at D110's second, refuted by the owner's D117**:
a pause at 1000 and its unpause at 1100, both inside an interruption 900–1200 across the wall `[1000, 2000)`'s start —
the pause second is the resume's, 1200, where the timer runs, so the wall pauses it there. -/
theorem a_user_who_resumed_during_the_meeting_keeps_their_timer_as_d110_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat),
      marks.any (pauseAt ⟨startSec started (lo, hi), 0⟩) = true →
      lastIsPauseAt marks ⟨startSec started (lo, hi), 0⟩ = false →
        writes started now brk marks [(lo, hi)] = [] := by
  intro h
  have := h ⟨500, 0⟩ ⟨2500, 0⟩ none
    [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At),
      .unpause ((⟨1100, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] 1000 2000
    (by decide) (by decide)
  revert this; decide

/-- **A user who resumed during the meeting keeps their timer** (D61's correction for a skipped
meeting): the span's pause is logged but no longer the last word on the timer, so its end writes
nothing.  Read at the span's pause second (D110, and D117's since W-48: **restated** over it). -/
theorem a_user_who_resumed_during_the_meeting_keeps_their_timer (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat)
    (hp : marks.any (pauseAt ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩) = true)
    (hl : lastIsPauseAt marks ⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ = false) :
    writes started now brk marks [(lo, hi)] = [] := by
  simp only [writes, List.foldl, step]
  split
  · rfl
  · simp [hp, pauseIfNew, unpauseIfDone, hl]

/-- **A break running since before the wall's end writes no unpause** — the owner's **D114** (README gap 5014, parity
P115): whatever the marks, the span's end is not written while such a break runs; the verb that ends the break writes
it (`tm/src/cli/day.rs`, `end_break_at`). -/
theorem a_break_running_past_the_walls_end_holds_the_block (started now : Cal.Instant) (brk : Option Cal.Instant)
    (marks : List Replay.IdleMark) (lo hi : Nat) (hb : breakHolds brk hi = true) :
    (false, lo, hi) ∉ writes started now brk marks [(lo, hi)] := by
  simp only [writes, List.foldl, step]
  intro hx
  split at hx
  · simp at hx
  · split at hx
    · simp at hx
    · unfold unpauseIfDone at hx
      rw [hb] at hx
      simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] at hx
      unfold pauseIfNew at hx
      split at hx
      · simp at hx
      · simp at hx

/-- What one span's step appends to the written list: the entries before it, then its own, each a start or an end of
`s` whose pause second is never ahead of `now`, and only for a span that did not end by the block's start (D110: a
wall the block began inside is the block's too).  **Restated at D117** over the pause second `pauseSec started ints s`
(it was D110's, `startSec`, which is never later: `startSec_le_pauseSec`). -/
theorem step_written (started now : Cal.Instant) (brk : Option Cal.Instant) (ints : List (Cal.Instant × Cal.Instant))
    (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (s : Nat × Nat) (x : Bool × Nat × Nat)
    (hx : x ∈ (step started now brk ints acc s).2) :
    x ∈ acc.2 ∨ (x.2 = s ∧ (started < ⟨s.1, 0⟩ ∨ started < ⟨s.2, 0⟩) ∧
      (⟨pauseSec started ints s, 0⟩ : Cal.Instant) ≤ now ∧ (x.1 = false → (⟨s.2, 0⟩ : Cal.Instant) ≤ now)) := by
  by_cases hc : ((⟨s.1, 0⟩ : Cal.Instant) ≤ started ∧ (⟨s.2, 0⟩ : Cal.Instant) ≤ started) ∨
      now < ⟨pauseSec started ints s, 0⟩
  · simp only [step, if_pos hc] at hx; exact Or.inl hx
  · have h1 : started < ⟨s.1, 0⟩ ∨ started < ⟨s.2, 0⟩ := by
      have := (not_or.1 hc).1
      rw [Cal.Instant.lt_iff, Cal.Instant.lt_iff]
      rw [Cal.Instant.le_iff, Cal.Instant.le_iff] at this
      simp only at this ⊢
      omega
    have h2 : (⟨pauseSec started ints s, 0⟩ : Cal.Instant) ≤ now := (Cal.Instant.not_lt _ _).1 (not_or.1 hc).2
    simp only [step, if_neg hc] at hx
    split at hx
    · exact Or.inl hx
    · unfold unpauseIfDone at hx
      split at hx
      · rename_i hq
        rcases List.mem_append.1 hx with hx | hx
        · unfold pauseIfNew at hx
          split at hx
          · exact Or.inl hx
          · rcases List.mem_append.1 hx with hx | hx
            · exact Or.inl hx
            · simp only [List.mem_singleton] at hx; subst hx
              exact Or.inr ⟨rfl, h1, h2, by simp⟩
        · simp only [List.mem_singleton] at hx; subst hx
          have h3 : (⟨s.2, 0⟩ : Cal.Instant) ≤ now := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
            exact hq.1.1.1
          exact Or.inr ⟨rfl, h1, h2, fun _ => h3⟩
      · unfold pauseIfNew at hx
        split at hx
        · exact Or.inl hx
        · rcases List.mem_append.1 hx with hx | hx
          · exact Or.inl hx
          · simp only [List.mem_singleton] at hx; subst hx
            exact Or.inr ⟨rfl, h1, h2, by simp⟩

/-- **"Everything the walls write is a joined span's own start or end, of a wall begun after the block", refuted by
D110**: a block begun at 1500 inside the wall `[1000, 2000)` is paused, and the span did not begin after it. -/
theorem mem_writes_as_d61_wrote_it_is_refuted :
    ¬ ∀ (started now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark)
      (spans : List (Nat × Nat)) (b : Bool) (lo hi : Nat), (b, lo, hi) ∈ writes started now brk marks spans →
        (lo, hi) ∈ spans ∧ started < ⟨lo, 0⟩ ∧ (⟨lo, 0⟩ : Cal.Instant) ≤ now ∧
          (b = false → (⟨hi, 0⟩ : Cal.Instant) ≤ now) := by
  intro h
  have := (h ⟨1500, 0⟩ ⟨1800, 0⟩ none [] [(1000, 2000)] true 1000 2000 (by decide)).2.1
  revert this; decide

/-- **Everything the walls write is a joined span's own start or end, never ahead of `now`, of a wall that did not end
by the block's start** — over any number of spans (the pause at the span's pause second, `pauseSec`: D110, D117).
**Restated at D117** over that pause second, which is never earlier than D110's (`startSec_le_pauseSec`), so the new
statement implies the old. -/
theorem mem_writes (started now : Cal.Instant) (brk : Option Cal.Instant)
    (marks : List Replay.IdleMark) (spans : List (Nat × Nat)) (b : Bool) (lo hi : Nat)
    (h : (b, lo, hi) ∈ writes started now brk marks spans) :
    (lo, hi) ∈ spans ∧ (started < ⟨lo, 0⟩ ∨ started < ⟨hi, 0⟩) ∧
      (⟨pauseSec started (intSpans marks) (lo, hi), 0⟩ : Cal.Instant) ≤ now ∧
      (b = false → (⟨hi, 0⟩ : Cal.Instant) ≤ now) := by
  unfold writes at h
  suffices H : ∀ (acc : List Replay.IdleMark × List (Bool × Nat × Nat)) (ss : List (Nat × Nat)),
      (∀ x ∈ acc.2, x.2 ∈ spans ∧ (started < ⟨x.2.1, 0⟩ ∨ started < ⟨x.2.2, 0⟩) ∧
        (⟨pauseSec started (intSpans marks) x.2, 0⟩ : Cal.Instant) ≤ now ∧
        (x.1 = false → (⟨x.2.2, 0⟩ : Cal.Instant) ≤ now)) →
      (∀ s ∈ ss, s ∈ spans) →
      ∀ x ∈ (ss.foldl (step started now brk (intSpans marks)) acc).2, x.2 ∈ spans ∧
        (started < ⟨x.2.1, 0⟩ ∨ started < ⟨x.2.2, 0⟩) ∧
        (⟨pauseSec started (intSpans marks) x.2, 0⟩ : Cal.Instant) ≤ now ∧
        (x.1 = false → (⟨x.2.2, 0⟩ : Cal.Instant) ≤ now) by
    exact H (marks, []) spans (by simp) (fun s hs => hs) (b, lo, hi) h
  intro acc ss hacc hss
  induction ss generalizing acc with
  | nil => exact hacc
  | cons s ss ih =>
    apply ih _ _ (fun s' hs' => hss s' (List.mem_cons_of_mem _ hs'))
    intro x hx
    rcases step_written started now brk _ acc s x hx with hx | ⟨he, h1, h2, h3⟩
    · exact hacc x hx
    · rw [he]; exact ⟨hss s (List.mem_cons_self ..), h1, h2, h3⟩

/-- The marks a written list adds to the log, in order: a pause at its span's pause second (`pauseSec`, over the
interruptions the log closes, `ints`), an unpause at its span's end. -/
def marksOf (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (w : List (Bool × Nat × Nat)) :
    List Replay.IdleMark :=
  w.map fun x => markOf x.1 (if x.1 then ⟨pauseSec started ints x.2, 0⟩ else ⟨x.2.2, 0⟩)

/-- **What the rule writes closes no interruption**: the interruptions of the log and the marks it wrote are the log's
(D117). -/
theorem intSpans_append_marksOf (marks : List Replay.IdleMark) (started : Cal.Instant)
    (ints : List (Cal.Instant × Cal.Instant)) (w : List (Bool × Nat × Nat)) :
    intSpans (marks ++ marksOf started ints w) = intSpans marks := by
  unfold intSpans marksOf
  rw [List.foldl_append]
  congr 1
  generalize marks.foldl intStep (none, []) = st
  induction w generalizing st with
  | nil => rfl
  | cons x w ih => rw [List.map_cons, List.foldl_cons, intStep_markOf, ih]

/-- **D110: a block started inside a wall is paused from its start until the wall ends** (README gap 4748, parity
P106) — the marks the rule writes for a block begun at the whole second `st` inside the wall `[lo, hi)`, with nothing
logged at `st`, its timer running there and untouched since: the `pause` stamped at the block's start (not at the
wall's), and the `unpause` at the wall's end once it has passed — and, since the owner's **D114**, no break running since
before it holds the block.  **Restated at D114**: D110's statement is refuted
(`a_block_started_inside_a_wall_is_paused_from_its_start_as_d110_wrote_it_is_refuted`). -/
theorem a_block_started_inside_a_wall_is_paused_from_its_start (now : Cal.Instant) (brk : Option Cal.Instant)
    (marks : List Replay.IdleMark) (lo hi st : Nat) (h1 : lo ≤ st) (hin : st < hi)
    (h2 : (⟨st, 0⟩ : Cal.Instant) ≤ now) (hp : marks.any (pauseAt ⟨st, 0⟩) = false)
    (hs : stoppedAt marks ⟨st, 0⟩ ⟨st, 0⟩ brk = false) (ht : touchedAfter marks ⟨st, 0⟩ = false) :
    marksOf ⟨st, 0⟩ (intSpans marks) (writes ⟨st, 0⟩ now brk marks [(lo, hi)]) =
      Replay.IdleMark.pause ((⟨st, 0⟩ : Cal.Instant), Cal.Offset.utc) ::
        (if (⟨hi, 0⟩ : Cal.Instant) ≤ now ∧ breakHolds brk hi = false then
          [Replay.IdleMark.unpause ((⟨hi, 0⟩ : Cal.Instant), Cal.Offset.utc)] else []) := by
  have hss : startSec ⟨st, 0⟩ (lo, hi) = st := by
    unfold startSec ceilSec; simp only [if_true]; exact Nat.max_eq_right h1
  have hps : pauseSec ⟨st, 0⟩ (intSpans marks) (lo, hi) = st := by
    rw [pauseSec_of_uncovered _ _ _ (by rw [hss]; exact not_covered_of_not_stopped marks _ _ brk hs), hss]
  rw [a_span_whose_pause_second_has_come_is_paused ⟨st, 0⟩ now brk marks lo hi (by rw [hps]; exact hin)
    (by rw [hps]; exact h2) (by rw [hps]; exact hp) (by rw [hps]; exact hs) (by rw [hps]; exact ht)]
  by_cases hh : (⟨hi, 0⟩ : Cal.Instant) ≤ now
  · cases breakHolds brk hi <;> simp [hh, marksOf, markOf, hps]
  · simp [hh, marksOf, markOf, hps]

/-- **D110's law as it stood, refuted by the owner's D114**: a block begun at 1500 inside the wall `[1000, 2000)`, a
break running since 1600, asked at 2500 — the block is paused from its start, and the unpause waits for the break. -/
theorem a_block_started_inside_a_wall_is_paused_from_its_start_as_d110_wrote_it_is_refuted :
    ¬ ∀ (now : Cal.Instant) (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi st : Nat), lo ≤ st →
      st < hi → (⟨st, 0⟩ : Cal.Instant) ≤ now → marks.any (pauseAt ⟨st, 0⟩) = false →
      stoppedAt marks ⟨st, 0⟩ ⟨st, 0⟩ brk = false → touchedAfter marks ⟨st, 0⟩ = false →
      (writes ⟨st, 0⟩ now brk marks [(lo, hi)]).map
          (fun x => markOf x.1 (if x.1 then ⟨startSec ⟨st, 0⟩ x.2, 0⟩ else ⟨x.2.2, 0⟩)) =
        Replay.IdleMark.pause ((⟨st, 0⟩ : Cal.Instant), Cal.Offset.utc) ::
          (if (⟨hi, 0⟩ : Cal.Instant) ≤ now then
            [Replay.IdleMark.unpause ((⟨hi, 0⟩ : Cal.Instant), Cal.Offset.utc)] else []) := by
  intro h
  have := h ⟨2500, 0⟩ (some ⟨1600, 0⟩) [] 1000 2000 1500 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  revert this; decide

/-- **D117: a block resumed inside a wall is paused from its resume until the wall ends** (README gaps 5036 and 3042,
parity P116) — the marks the rule writes for a block begun before the wall `[lo, hi)` and interrupted across its start,
the interruption closed by a `resume` whose first whole second `r` falls inside the wall, with nothing logged at `r`, the
timer running there and untouched since: the `pause` stamped at the resume, and the `unpause` at the wall's end once it
has passed and no break running since before it holds the block (D114).  Until W-48 the rule read the interruption
across the wall's start as the wall's stop and wrote nothing, so the meeting after the resume was counted as work. -/
theorem a_block_resumed_inside_a_wall_is_paused_from_its_resume (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat) (a r : Cal.Instant)
    (hf : (intSpans marks).find? (fun i => decide (i.1 ≤ ⟨startSec started (lo, hi), 0⟩) &&
      decide ((⟨startSec started (lo, hi), 0⟩ : Cal.Instant) < i.2) && decide (ceilSec i.2 < hi)) = some (a, r))
    (h2 : (⟨ceilSec r, 0⟩ : Cal.Instant) ≤ now) (hp : marks.any (pauseAt ⟨ceilSec r, 0⟩) = false)
    (hs : stoppedAt marks started ⟨ceilSec r, 0⟩ brk = false) (ht : touchedAfter marks ⟨ceilSec r, 0⟩ = false) :
    marksOf started (intSpans marks) (writes started now brk marks [(lo, hi)]) =
      Replay.IdleMark.pause ((⟨ceilSec r, 0⟩ : Cal.Instant), Cal.Offset.utc) ::
        (if (⟨hi, 0⟩ : Cal.Instant) ≤ now ∧ breakHolds brk hi = false then
          [Replay.IdleMark.unpause ((⟨hi, 0⟩ : Cal.Instant), Cal.Offset.utc)] else []) := by
  have hps : pauseSec started (intSpans marks) (lo, hi) = ceilSec r := by
    unfold pauseSec; rw [hf]
  have hin : ceilSec r < hi := by
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.2
  rw [a_span_whose_pause_second_has_come_is_paused started now brk marks lo hi (by rw [hps]; exact hin)
    (by rw [hps]; exact h2) (by rw [hps]; exact hp) (by rw [hps]; exact hs) (by rw [hps]; exact ht)]
  by_cases hh : (⟨hi, 0⟩ : Cal.Instant) ≤ now
  · cases breakHolds brk hi <;> simp [hh, marksOf, markOf, hps]
  · simp [hh, marksOf, markOf, hps]

/-- **A second verb writes nothing more** (one wall, the day a user has — AGENTS §3.1 item 4, the
subdomain in the name): once the marks the rule wrote are in the log, the next verb's run of the
same rule writes nothing, which is D61's "written once" — and D110's, for a block begun inside the wall, D117's for one
resumed inside it, and D114's whether or not a break holds the unpause.  A two-run law (owner D5), re-proved over the
pause second; the marks are rendered over the interruptions the log closes (`marksOf`'s `ints`), which what the rule
writes leaves as they were (`intSpans_append_marksOf`). -/
theorem after_one_wall_a_second_verb_writes_nothing_more (started now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (lo hi : Nat) :
    writes started now brk (marks ++ marksOf started (intSpans marks) (writes started now brk marks [(lo, hi)]))
      [(lo, hi)] = [] := by
  generalize hWd : writes started now brk marks [(lo, hi)] = Wd
  have hI : intSpans (marks ++ marksOf started (intSpans marks) Wd) = intSpans marks := intSpans_append_marksOf _ _ _ _
  unfold writes at hWd ⊢
  rw [hI]
  generalize hIg : intSpans marks = I at hWd ⊢
  subst hWd
  by_cases hc : ((⟨lo, 0⟩ : Cal.Instant) ≤ started ∧ (⟨hi, 0⟩ : Cal.Instant) ≤ started) ∨
      now < ⟨pauseSec started I (lo, hi), 0⟩
  · simp [step, hc]
  · -- One run over `ms`, unfolded once at this span.
    have hw : ∀ ms : List Replay.IdleMark, ([(lo, hi)].foldl (step started now brk I) (ms, [])).2 =
        if (!(ms.any (pauseAt ⟨pauseSec started I (lo, hi), 0⟩)) &&
          (stoppedAt ms started ⟨pauseSec started I (lo, hi), 0⟩ brk ||
            touchedAfter ms ⟨pauseSec started I (lo, hi), 0⟩)) = true then []
        else (unpauseIfDone started now brk I (lo, hi) (pauseIfNew started I (lo, hi) (ms, []))).2 := by
      intro ms
      simp only [List.foldl, step, if_neg hc]
      split <;> rfl
    -- The marks a pause and an unpause of this span add.
    have mp : marksOf started I [(true, lo, hi)] = [markOf true ⟨pauseSec started I (lo, hi), 0⟩] := rfl
    have mu : marksOf started I [(false, lo, hi)] = [markOf false ⟨hi, 0⟩] := rfl
    have mpu : marksOf started I [(true, lo, hi), (false, lo, hi)] =
        [markOf true ⟨pauseSec started I (lo, hi), 0⟩, markOf false ⟨hi, 0⟩] := rfl
    generalize hP : pauseSec started I (lo, hi) = P at hw mp mpu
    -- A list holding the pause at `P` asks nothing more of the span's pause half, and holds its unpause half's
    -- answer: the second run writes the unpause exactly when the first would have, and then once.
    have second : ∀ ms : List Replay.IdleMark, ms.any (pauseAt ⟨P, 0⟩) = true →
        (decide ((⟨hi, 0⟩ : Cal.Instant) ≤ now) && !(ms.any (unpauseAt ⟨hi, 0⟩)) && lastIsPauseAt ms ⟨P, 0⟩ &&
          !breakHolds brk hi) = false →
        ([(lo, hi)].foldl (step started now brk I) (ms, [])).2 = [] := by
      intro ms hp hq
      rw [hw ms]
      simp [hp, pauseIfNew, unpauseIfDone, hP, hq]
    cases hp : marks.any (pauseAt ⟨P, 0⟩) with
    | true =>
      cases hq : (decide ((⟨hi, 0⟩ : Cal.Instant) ≤ now) && !(marks.any (unpauseAt ⟨hi, 0⟩)) &&
          lastIsPauseAt marks ⟨P, 0⟩ && !breakHolds brk hi) with
      | true =>
        have h1 : ([(lo, hi)].foldl (step started now brk I) (marks, [])).2 = [(false, lo, hi)] := by
          rw [hw marks]; simp [hp, pauseIfNew, unpauseIfDone, hP, hq]
        rw [h1, mu]
        apply second
        · simp [hp]
        · simp [markOf, unpauseAt]
      | false =>
        have h1 : ([(lo, hi)].foldl (step started now brk I) (marks, [])).2 = [] := by
          rw [hw marks]; simp [hp, pauseIfNew, unpauseIfDone, hP, hq]
        rw [h1]
        simpa [marksOf] using h1
    | false =>
      cases hk : (stoppedAt marks started ⟨P, 0⟩ brk || touchedAfter marks ⟨P, 0⟩) with
      | true =>
        have h1 : ([(lo, hi)].foldl (step started now brk I) (marks, [])).2 = [] := by
          rw [hw marks]; simp [hp, hk]
        rw [h1]
        simpa [marksOf] using h1
      | false =>
        cases hq : (decide ((⟨hi, 0⟩ : Cal.Instant) ≤ now) &&
            !((marks ++ [markOf true ⟨P, 0⟩]).any (unpauseAt ⟨hi, 0⟩)) && !breakHolds brk hi) with
        | true =>
          have h1 : ([(lo, hi)].foldl (step started now brk I) (marks, [])).2 =
              [(true, lo, hi), (false, lo, hi)] := by
            rw [hw marks]
            simp only [hp, hk, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
            unfold pauseIfNew unpauseIfDone
            rw [hP]
            dsimp only
            simp only [hp, Bool.false_eq_true, if_false]
            rw [if_pos (by rw [lastIsPauseAt_append, Bool.and_true]; exact hq)]
            rfl
          rw [h1, mpu]
          apply second
          · simp [markOf, pauseAt]
          · simp [markOf, unpauseAt]
        | false =>
          have h1 : ([(lo, hi)].foldl (step started now brk I) (marks, [])).2 = [(true, lo, hi)] := by
            rw [hw marks]
            simp only [hp, hk, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false]
            unfold pauseIfNew unpauseIfDone
            rw [hP]
            dsimp only
            simp only [hp, Bool.false_eq_true, if_false]
            rw [if_neg (by rw [lastIsPauseAt_append, Bool.and_true, hq]; decide)]
            rfl
          rw [h1, mp]
          apply second
          · simp [markOf, pauseAt]
          · rw [lastIsPauseAt_append, Bool.and_true]; exact hq

/-- **The meeting the running block is paused for** (the campaign's D66 call on gap 3048): the
first joined span `now` falls inside whose pause — at its pause second, `pauseSec`: the wall's start, or the block's
when the block began inside the wall (D110), or the resume of an interruption across D110's second (D117) — is the last
word on the timer: what `tm pause` names when it resumes the timer inside a meeting (the correction for a skipped
one). -/
def pausedFor (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (marks : List Replay.IdleMark) : List ((Nat × Nat) × List Id) → Option ((Nat × Nat) × List Id)
  | [] => none
  | x :: xs =>
    if (lastIsPauseAt marks ⟨pauseSec started ints x.1, 0⟩ &&
        decide ((⟨pauseSec started ints x.1, 0⟩ : Cal.Instant) ≤ now) &&
        decide (now < ⟨x.1.2, 0⟩)) = true then some x else pausedFor started ints now marks xs

/-- **`pausedFor` is the first span `List.find?` finds** — its definition before the W-37 repair
wrote it by recursion (README gap 3333, as `touchedAfter_eq_any`).  **Restated at D117** over the pause second. -/
theorem pausedFor_eq_find (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id)) :
    pausedFor started ints now marks spans = spans.find? fun x =>
      lastIsPauseAt marks ⟨pauseSec started ints x.1, 0⟩ &&
      decide ((⟨pauseSec started ints x.1, 0⟩ : Cal.Instant) ≤ now) && decide (now < ⟨x.1.2, 0⟩) := by
  induction spans with
  | nil => rfl
  | cons x xs ih =>
    rw [pausedFor, List.find?_cons, ih]
    cases (lastIsPauseAt marks ⟨pauseSec started ints x.1, 0⟩ &&
      decide ((⟨pauseSec started ints x.1, 0⟩ : Cal.Instant) ≤ now) && decide (now < ⟨x.1.2, 0⟩)) <;> rfl

/-- **What `pausedFor` names is a meeting the timer is paused for, now**: one of the spans, its
pause the last timer mark, and `now` inside it from its pause second on.  **Restated at D117** over the pause second. -/
theorem pausedFor_is_a_meeting_the_timer_is_paused_for (started : Cal.Instant)
    (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id)) (x : (Nat × Nat) × List Id)
    (h : pausedFor started ints now marks spans = some x) :
    x ∈ spans ∧ lastIsPauseAt marks ⟨pauseSec started ints x.1, 0⟩ = true ∧
      (⟨pauseSec started ints x.1, 0⟩ : Cal.Instant) ≤ now ∧ now < ⟨x.1.2, 0⟩ := by
  rw [pausedFor_eq_find] at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨hm, hp.1.1, hp.1.2, hp.2⟩

/-! ## The wire: the `emit` section's walls form

The host asks `{"emit": {"walls": {"at": <stamp>, "break": <stamp> | null}}}` beside the request's
`docs`, `tz`, `log` (with facts), `now` and `blockMin`, and `Boundary.readEmitSection` answers
`ok.emit` with one entry per line to append, in order: `ev` (`pause`/`unpause`), the block's `id`,
`at` (the entry's stamp), `from`/`to` (the joined span), `walls` (the items it joins, for the
notice D65 prints) and `line` — the exact bytes, written by `Log.emitLine` (D16).  `at` and `break`
are read by B2's one stamp reader, `LogStamp.parseStamp`; `break` is the running break
`.tm/state.json` holds, the one input the log cannot give (a break is logged when it ends). -/

/-- **The walls form's refusals** (§10.3's shape): `{"err":{"emit":{"walls":<name>}}}`. -/
inductive Refusal
  /-- `emit.walls` absent or not an object -/
  | shape
  /-- `emit.walls.at` absent, repeated, or not a stamp B2's reader accepts -/
  | badAt
  /-- `emit.walls.break` present and neither `null` nor such a stamp -/
  | badBreak
  /-- no readable `tz`: a wall's instants are the zone's -/
  | tzAbsent
  /-- no `log` section that asked for facts: the open block and the marks are the replay's -/
  | logAbsent
  /-- no request `now`: the day the walls are selected for -/
  | nowAbsent
  /-- no request `blockMin`: a `buffer:` written in blocks -/
  | blockMinAbsent
  /-- commands beside the walls form: the walls are the documents as sent (gap 109's stance) -/
  | withCommands
  /-- a wall's instant, or the zone's offset at it, outside what the kernel holds (R10) -/
  | badInstant
  /-- the log's reader refuses a line the rule would write (named; not expected to fire) -/
  | refused
deriving DecidableEq, Repr, Inhabited

/-- Each refusal's wire name. -/
def Refusal.name : Refusal → String
  | .shape => "shape" | .badAt => "badAt" | .badBreak => "badBreak" | .tzAbsent => "tzAbsent"
  | .logAbsent => "logAbsent" | .nowAbsent => "nowAbsent" | .blockMinAbsent => "blockMinAbsent"
  | .withCommands => "withCommands" | .badInstant => "badInstant" | .refused => "refused"

/-- Keys in build order: `{"err":{"emit":{"walls":<name>}}}`. -/
def Refusal.json (r : Refusal) : JVal := jone "err" (jone "emit" (jone "walls" (.str r.name.toList)))

/-- The request's walls form, read. -/
structure Req where
  at_ : Cal.VInstant × Cal.VOffset
  brk : Option (Cal.VInstant × Cal.VOffset)

/-- A stamp through B2's one reader. -/
def readStamp : JVal → Option (Cal.VInstant × Cal.VOffset)
  | .str t => match LogStamp.parseStamp t with | .ok r => some r | .error _ => none
  | _ => none

/-- **`emit.walls`**: `at` required, `break` optional (`null` is none). -/
def readReq (v : JVal) : Except Refusal Req :=
  match jget v "walls" with
  | .ok (some w@(.obj _)) =>
    match jget w "at" with
    | .ok (some a) =>
      match readStamp a with
      | none => .error .badAt
      | some t =>
        match jget w "break" with
        | .ok none | .ok (some .null) => .ok ⟨t, none⟩
        | .ok (some b) =>
          match readStamp b with
          | some x => .ok ⟨t, some x⟩
          | none => .error .badBreak
        | .error _ => .error .badBreak
    | _ => .error .badAt
  | _ => .error .shape

/-- **The day's walls, joined as fork `merge_walls` joins them**, each with the items it joined:
`Look.wallIxOn`'s selection (the one the window, the cut and the wall rows read) for day `d`
**and for the day before** — the walls of `d - 1` that `d`'s selection does not already hold, as
the marks below read `d - 1`'s (README gap 3334: a block begun at 22:30 met a meeting at
22:40–22:50, and the first verb after midnight asked day `d`'s walls alone, so that meeting was
never paused and its ten minutes were counted as worked) — then `Look.clipWalls 0` (empty walls
dropped), `Look.sortByStart`, `Look.mergeSorted`, reused, not re-spelled, and the walls each joined
span contains.  The day before costs nothing on a block begun today: `step` passes over a span that
begins at or before the block's start. -/
def spansOf (ix : List Look.WallIx) (d : Nat) : List ((Nat × Nat) × List Id) :=
  let ws := (if 0 < d then (Look.wallIxOn ix (d - 1)).filter (fun w => decide (w.toDay < d)) else [])
    ++ Look.wallIxOn ix d
  (Look.mergeSorted (Look.sortByStart (Look.clipWalls 0 (ws.map fun w => (w.lo, w.hi))))).map fun m =>
    (m, (ws.filter fun w => decide (m.1 ≤ w.lo ∧ w.hi ≤ m.2 ∧ w.lo < w.hi)).map (·.id))

/-- An instant of whole seconds with the zone's offset at it, as a stamp is written. -/
def stampAt (z : Cal.Tz) (sec : Nat) : Option (Cal.VInstant × Cal.VOffset) :=
  match Cal.mkInstant? sec 0, Cal.mkOffset? (Cal.offsetAt z ⟨sec, 0⟩).west (Cal.offsetAt z ⟨sec, 0⟩).sec with
  | some i, some o => some (i, o)
  | _, _ => none

/-- **A joined span, on the wire**: `from`/`to` as stamps and the walls it joins. -/
def spanJson (z : Cal.Tz) (x : (Nat × Nat) × List Id) : Except Refusal JVal :=
  match stampAt z x.1.1, stampAt z x.1.2 with
  | some (a, ao), some (b, bo) => .ok (.obj [("from".toList, .str (LogStamp.renderStamp a ao)),
      ("to".toList, .str (LogStamp.renderStamp b bo)), ("walls".toList, .arr (x.2.map JVal.str))])
  | _, _ => .error .badInstant

/-- **One written mark, on the wire**: its line (D16's one writer) and what the host says of it — a pause stamped at its
span's pause second (`pauseSec`, the block's start for a block begun inside the wall: D110), an unpause at its end. -/
def entryJson (z : Cal.Tz) (id : Id) (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant))
    (spans : List ((Nat × Nat) × List Id))
    (w : Bool × Nat × Nat) : Except Refusal JVal :=
  match stampAt z (if w.1 then pauseSec started ints w.2 else w.2.2), stampAt z w.2.1, stampAt z w.2.2 with
  | some (i, o), some (a, ao), some (b, bo) =>
    match Log.emitLine i o (if w.1 then "pause".toList else "unpause".toList) [("id".toList, .str id)] with
    | .ok line => .ok (.obj [("ev".toList, .str (if w.1 then "pause".toList else "unpause".toList)),
        ("id".toList, .str id), ("at".toList, .str (LogStamp.renderStamp i o)),
        ("from".toList, .str (LogStamp.renderStamp a ao)), ("to".toList, .str (LogStamp.renderStamp b bo)),
        ("walls".toList, .arr ((((spans.find? fun x => x.1 == w.2).map (·.2)).getD []).map JVal.str)),
        ("line".toList, .str line)])
    | .error _ => .error .refused
  | _, _, _ => .error .badInstant

/-- **The marks the walls write and the meeting named, over the interruptions the log closes** (`ints`, the owner's
D117): `writes` over the open block `ob`, its marks and the request's spans, each mark rendered (`entryJson`), and the
meeting the block is now paused for (`pausedFor`).  `answer` hands it `intSpans marks` taken apart first — the rows are
given the list itself, not the reading of the log that gives it — so a decided witness over a whole replay does not read
the log again at every comparison the zone table makes with a pause's second (README "Stage 6 — W-48 track K"). -/
def answerRows (z : Cal.Tz) (q : Req) (ob : Replay.OpenBlock) (spans : List ((Nat × Nat) × List Id))
    (marks : List Replay.IdleMark) (ints : List (Cal.Instant × Cal.Instant)) : Except Refusal JVal := do
  let ws := writes ob.started.1 q.at_.1.val (q.brk.map (·.1.val)) marks (spans.map (·.1))
  let es ← ws.mapM (entryJson z ob.id ob.started.1 ints spans)
  let pf ← match pausedFor ob.started.1 ints q.at_.1.val (marks ++ marksOf ob.started.1 ints ws) spans with
    | none => pure JVal.null
    | some x => spanJson z x
  pure (.obj [("marks".toList, .arr es), ("pausedFor".toList, pf)])

/-- **The marks of the open block `ob`'s ledger days**, from its own (`Replay.OpenBlock.day`) to `d`, and first the
interruption the replay holds open, when it began before the block (README gap 4619) — what `answer` reads the rule over
and what the planner's hold reads (`holdOf`), one reading (AGENTS §5.3; README gap 5217). -/
def blockMarks (f : Seal.Answer) (ob : Replay.OpenBlock) (d : Nat) : List Replay.IdleMark := (match f.openInterrupt.bind (·.start) with | some s => if s.1 < ob.started.1 then [Replay.IdleMark.interrupt s] else [] | none => []) ++ (List.range' ob.day (d + 1 - ob.day)).flatMap (fun x => (((f.days.find? fun r => r.day == x).bind (·.seam)).map (·.idleMarks)).getD [])
/-- **What the walls write, answered** (gap 3139): nothing while no block is open in the replay;
otherwise `writes` over the open block, its marks, the walls of the request's day and the day
before (`spansOf`, gap 3334), the running
break and `at`, each mark rendered.  **The marks are those of every ledger day from the open block's own
(`Replay.OpenBlock.day`, its `start`'s) to `d`** — the days the host's worked minutes read the block's marks from
(`Replay::idle_min_since`; the owner's D99, README gap 4616: until W-47 day `d`'s and, stamped at or after the
block's start, the day before's, so a block open since before `d − 1` had its own early pause read as running) — and,
first, **the interruption the replay holds open, when it began before the block** (README gap 4619): its `interrupt`
mark is filed under an earlier ledger day, and the block's timer is held from its start.  The walls are the index
argument's (`Boundary.wallsEmit` passes `Look.wallIndex`), a function for `answer_congr_ix`. -/
def answer (v : JVal) (zo : Option Cal.Tz) (facts : Option Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (cmds : Nat) (today : Option Nat) (bm : Option Nat) :
    Except Refusal JVal := do
  let q ← readReq v
  let f ← match facts with | some f => pure f | none => throw .logAbsent
  let z ← match zo with | some z => pure z | none => throw .tzAbsent
  let d ← match today with | some d => pure d | none => throw .nowAbsent
  let b ← match bm with | some b => pure b | none => throw .blockMinAbsent
  if cmds ≠ 0 then throw .withCommands
  match f.openBlock with
  | none => pure (.obj [("marks".toList, .arr []), ("pausedFor".toList, .null)])
  | some ob =>
    let spans := spansOf (ixOf z b) d
    let marks := blockMarks f ob d
    match intSpans marks with
    | [] => answerRows z q ob spans marks []
    | i :: is => answerRows z q ob spans marks (i :: is)

/-- **No open block, nothing to stop**: the answer is the empty list whatever the walls. -/
theorem answer_without_an_open_block (v : JVal) (z : Cal.Tz) (f : Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (d b : Nat) (q : Req) (hq : readReq v = .ok q)
    (hf : f.openBlock = none) :
    answer v (some z) (some f) ixOf 0 (some d) (some b) =
      .ok (.obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]) := by
  simp [answer, hq, hf, bind, Except.bind, pure, Except.pure]

/-- **The walls form refuses commands beside it**, by name. -/
theorem answer_refuses_commands (v : JVal) (z : Cal.Tz) (f : Seal.Answer)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n d b : Nat) (q : Req) (hq : readReq v = .ok q)
    (hn : n ≠ 0) :
    answer v (some z) (some f) ixOf n (some d) (some b) = .error .withCommands := by
  simp [answer, hq, hn, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- **Without a replay there is no answer**: a walls request whose `log` section asked no facts is
refused `logAbsent`, never answered as if no block were open (D24's rule for a consumer handed no
replay). -/
theorem answer_refuses_without_the_replay (v : JVal) (zo : Option Cal.Tz)
    (ixOf : Cal.Tz → Nat → List Look.WallIx) (n : Nat) (d b : Option Nat) (q : Req)
    (hq : readReq v = .ok q) :
    answer v zo none ixOf n d b = .error .logAbsent := by
  simp [answer, hq, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- **The answer reads the wall index at the request's zone and block length and nowhere else.** -/
theorem answer_congr_ix (v : JVal) (z : Cal.Tz) (f : Option Seal.Answer)
    (ixOf ixOf' : Cal.Tz → Nat → List Look.WallIx) (n d b : Nat) (h : ixOf z b = ixOf' z b) :
    answer v (some z) f ixOf n (some d) (some b) = answer v (some z) f ixOf' n (some d) (some b) := by
  simp only [answer, pure_bind, h]

/-- **The refusals spell themselves** (§5.7). -/
theorem the_walls_refusals_spell_themselves :
    Refusal.name .shape = "shape" ∧ Refusal.name .badAt = "badAt" ∧
    Refusal.name .badBreak = "badBreak" ∧ Refusal.name .tzAbsent = "tzAbsent" ∧
    Refusal.name .logAbsent = "logAbsent" ∧ Refusal.name .nowAbsent = "nowAbsent" ∧
    Refusal.name .blockMinAbsent = "blockMinAbsent" ∧ Refusal.name .withCommands = "withCommands" ∧
    Refusal.name .badInstant = "badInstant" ∧ Refusal.name .refused = "refused" := by
  decide

/-! ## The rule, run (AGENTS §5.2: non-vacuity is a separate check from correctness)

A block begun at 500 s, one wall `[1000, 2000)`, and the log's marks of each case — every one of
`cli_wall_pause.rs`'s drives, at seconds a reader can check by eye.  The instants are written as
literals (`⟨s, 0⟩`), not through a helper: a helper is a definition the export does not reach,
which check 12 must then exempt by name (README gap 3333, W-37 repair; D51). -/

/-- **The rule, run**: the pause and the unpause; the pause alone while the wall runs; nothing before
it; for a block started inside it, since the owner's D110, the pause (stamped at the block's start, `pauseSec`) and the
unpause; nothing over a timer already stopped (a pause at 900, the
running break) and the wall's pause over a pause another block left (400), a stop that ended before
the wall (900–950, an interruption 990–995) and — since the W-44 repair — a break logged across the
wall's start or without its length (gap 4550); nothing under a mark stamped after the wall's start;
the end alone when the pause is logged; nothing when the user resumed inside it; two walls in order. -/
theorem the_rule_is_run :
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [] [(1000, 2000)] = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨1500, 0⟩ : Cal.Instant) none [] [(1000, 2000)] = [(true, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨900, 0⟩ : Cal.Instant) none [] [(1000, 2000)] = [] ∧
    writes (⟨1500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [] [(1000, 2000)] = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) (some (⟨900, 0⟩ : Cal.Instant)) [] [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.brk ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At) (some 1)] [(1000, 2000)] = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨400, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.interrupt ((⟨990, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨995, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.brk ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At) none] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.unpause ((⟨1500, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [(false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)]
      = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨3500, 0⟩ : Cal.Instant) none [] [(1000, 2000), (3000, 4000)]
      = [(true, 1000, 2000), (false, 1000, 2000), (true, 3000, 4000)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The meeting named, run**: inside the meeting with its pause the last mark, it is named; after
the unpause, or once the user resumed inside it, it is not; and (D110) a block begun inside it at 1300, paused at its
start, is paused for it too. -/
theorem pausedFor_is_run :
    pausedFor (⟨500, 0⟩ : Cal.Instant) (intSpans [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)]) (⟨1500, 0⟩ : Cal.Instant) [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)] [((1000, 2000), [['g','1']])]
      = some ((1000, 2000), [['g','1']]) ∧
    pausedFor (⟨500, 0⟩ : Cal.Instant) (intSpans [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨2000, 0⟩, Cal.Offset.utc) : Replay.At)]) (⟨2500, 0⟩ : Cal.Instant) [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨2000, 0⟩, Cal.Offset.utc) : Replay.At)] [((1000, 2000), [['g','1']])]
      = none ∧
    pausedFor (⟨500, 0⟩ : Cal.Instant) (intSpans [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)]) (⟨1500, 0⟩ : Cal.Instant) [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)] [((1000, 2000), [['g','1']])]
      = none ∧
    pausedFor (⟨1300, 0⟩ : Cal.Instant) (intSpans [.pause ((⟨1300, 0⟩, Cal.Offset.utc) : Replay.At)]) (⟨1500, 0⟩ : Cal.Instant) [.pause ((⟨1300, 0⟩, Cal.Offset.utc) : Replay.At)] [((1000, 2000), [['g','1']])]
      = some ((1000, 2000), [['g','1']]) := by
  decide

/-- **The walls joined, run**: two overlapping walls and one touching them are one span naming all
three; an empty wall is dropped; another day's wall is not today's; a separate wall is its own. -/
theorem spansOf_is_run :
    spansOf [⟨['g','1'], 7, 7, 1000, 1000, 2000⟩, ⟨['g','2'], 7, 7, 1500, 1500, 2500⟩,
      ⟨['g','3'], 7, 7, 3000, 3000, 3000⟩, ⟨['g','4'], 7, 7, 2500, 2500, 2600⟩,
      ⟨['g','5'], 8, 8, 1000, 1000, 2000⟩, ⟨['g','6'], 7, 7, 4000, 4000, 4500⟩] 7
      = [((1000, 2600), [['g','1'], ['g','2'], ['g','4']]), ((4000, 4500), [['g','6']])] := by
  decide

/-- **The evening before's meeting is read** (README gap 3334): asked on day 8, a wall wholly on
day 7 (`g5`, 900–950) and one crossing midnight from day 7 into day 8 (`g2`) are both spans, the
crossing one once; a wall of day 6 is not, and day 8's own wall is. -/
theorem the_evening_befores_walls_are_read :
    spansOf [⟨['g','5'], 7, 7, 900, 900, 950⟩, ⟨['g','2'], 7, 8, 1000, 1000, 2000⟩,
      ⟨['g','0'], 6, 6, 100, 100, 200⟩, ⟨['g','8'], 8, 8, 3000, 3000, 3100⟩] 8
      = [((900, 950), [['g','5']]), ((1000, 2000), [['g','2']]), ((3000, 3100), [['g','8']])] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [] ((spansOf [⟨['g','5'], 7, 7, 900, 900, 950⟩,
      ⟨['g','2'], 7, 8, 1000, 1000, 2000⟩] 8).map (·.1))
      = [(true, 900, 950), (false, 900, 950), (true, 1000, 2000), (false, 1000, 2000)] := by
  decide

/-- **The walls form read, run**: a stamp is read by B2's one reader; `break` may be `null`; a
missing `at`, an `at` that is not a stamp, a `break` that is not one and a `walls` that is not an
object are refused by name. -/
theorem readReq_is_run :
    (match readReq (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) with
      | .ok q => q.at_.1.val == ⟨63924402000, 0⟩ && q.brk.isNone
      | .error _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .obj [])]) with
      | .error .badAt => true | _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .obj [("at".toList, .str "13:20".toList)])]) with
      | .error .badAt => true | _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .num 3)])]) with
      | .error .badBreak => true | _ => false) = true ∧
    (match readReq (.obj [("walls".toList, .arr [])]) with
      | .error .shape => true | _ => false) = true := by
  decide

/-- **A refusal on the wire, in build order.** -/
theorem the_walls_refusal_is_the_err_emit_shape :
    jemit (Refusal.json .logAbsent) = "{\"err\":{\"emit\":{\"walls\":\"logAbsent\"}}}".toList := by
  decide

/-- **The day before's marks are read** (README gap 3245): a replay whose open block (`t4`, begun at
second 500) has its wall's pause and unpause filed under day 7 — a day with no wake of its own files
its entries under the day before's wake when that is within 24 hours (`Replay.dayOf`) — asked on
day 8 once the wall has ended, answers nothing more to write.  Day 8's record alone holds no mark,
and over no mark the rule writes both again (`the_rule_is_run`'s first case), which is what the
host's reading of day 8 alone did on every verb of such a day. -/
theorem the_day_befores_marks_are_read :
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [⟨7, none, some ⟨none, [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨2000, 0⟩, Cal.Offset.utc) : Replay.At)], none⟩,
          [], [], [], [], [], []⟩], some ⟨['t','4'], ((⟨500, 0⟩, Cal.Offset.utc) : Replay.At), 0, none, false, 7, 0⟩, none, none, none, none, 0,
          0, none, [], [], 0⟩)
        (fun _ _ => [⟨['g','1'], 8, 8, 1000, 1000, 2000⟩]) 0 (some 8) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]
      | .error _ => false) = true := by
  decide

/-- **A break is not a timer mark** (`lastTimerMark` passes over it, as the host's last_timer_mark
did): a break logged inside the meeting after the wall's pause leaves that pause the last word on
the timer, so the wall's end still writes the unpause. -/
theorem a_break_inside_the_meeting_leaves_the_pause_the_last_word :
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .brk ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At) (some 5)] [(1000, 2000)]
      = [(false, 1000, 2000)] := by
  decide

/-- **A block the user paused stays paused across an interruption** (the W-44 repair, README gap 4610): a pause at 900,
an interruption 950–980 — the resume ends the interruption, not the pause — so the timer is still stopped at the
wall's start and the wall writes nothing; with the pause unpaused at 990 it writes both marks.  Until the repair the
pairing closed the one open span at the resume, read the timer running at 1000 and wrote a pause over a paused block
whose unpause, at the wall's end, restarted the block the user had paused. -/
theorem a_resume_ends_the_interruption_and_not_the_users_pause :
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At),
      .interrupt ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨980, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At),
      .interrupt ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨980, 0⟩, Cal.Offset.utc) : Replay.At),
      .unpause ((⟨990, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] := by
  decide

/-- **A break across the wall's start is not the user's stop** (the W-44 repair, README gap 4550): logged with its
length (950, one minute) or without it, the wall writes its pause and its unpause, one answer for both spellings; a
break still RUNNING at the wall's start (`brk`, 950) writes nothing yet. -/
theorem a_break_across_the_walls_start_does_not_stand_for_the_users_stop :
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.brk ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At) (some 30)] [(1000, 2000)]
      = writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.brk ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At) none] [(1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.brk ((⟨950, 0⟩, Cal.Offset.utc) : Replay.At) (some 30)] [(1000, 2000)]
      = [(true, 1000, 2000), (false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨1500, 0⟩ : Cal.Instant) (some (⟨950, 0⟩ : Cal.Instant)) [] [(1000, 2000)] = [] := by
  decide

/-! ## The owner's D99 on the wall rule's days (README gaps 4616 and 4619, W-47 track K) -/

/-- **A block open since an earlier ledger day reads its own marks from its `start`'s day** (README gap 4616): `t4`
begun at 500 on ledger day 5 and paused at 900 that day, still paused, asked on day 7 with a meeting at 1000 —
the timer is the user's to have stopped, so the wall writes nothing.  Until W-47 the rule read day 7's marks and day
6's, read the timer as running at 1000 and wrote a pause over the user's (whose unpause, at the meeting's end, would
have restarted a block the user had paused). -/
theorem a_block_open_since_an_earlier_day_reads_its_own_pause :
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [⟨5, none, some ⟨none, [.pause ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At)], none⟩,
          [], [], [], [], [], []⟩], some ⟨['t','4'], ((⟨500, 0⟩, Cal.Offset.utc) : Replay.At), 0, none, true, 5, 0⟩, none, none,
          none, none, 0, 0, none, [], [], 0⟩)
        (fun _ _ => [⟨['g','1'], 7, 7, 1000, 1000, 2000⟩]) 0 (some 7) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]
      | .error _ => false) = true := by
  decide

/-- **An interruption open since before the block holds its timer at a wall too** (README gap 4619): `t4` begun at
500 on ledger day 6 inside an interruption the replay holds open since 300 (its `interrupt` filed under day 5, a day
the rule does not read), asked with a meeting at 1000 — the timer is stopped by the interruption, so the wall writes
nothing. -/
theorem an_interruption_open_since_before_the_block_holds_it_at_a_wall :
    (match answer (.obj [("walls".toList, .obj [("at".toList, .str "2026-09-07T13:20:00-05:00".toList),
        ("break".toList, .null)])]) (some Replay.utcZone)
        (some ⟨0, 0, [], [], [], [], [], some ⟨['t','4'], ((⟨500, 0⟩, Cal.Offset.utc) : Replay.At), 0, none, false, 6, 0⟩,
          some ⟨0, some ((⟨300, 0⟩, Cal.Offset.utc) : Replay.At), none, 5, none, 0, []⟩, none, none, none, 0, 0, none, [],
          [], 0⟩)
        (fun _ _ => [⟨['g','1'], 6, 6, 1000, 1000, 2000⟩]) 0 (some 6) (some 60) with
      | .ok v => v == .obj [("marks".toList, .arr []), ("pausedFor".toList, .null)]
      | .error _ => false) = true := by
  decide

/-! ## The owner's D114 and D117 on the wall rule (README gaps 5014, 5036 and 3042, W-48 track K) -/

/-- **A break running past the wall's end holds the block, and once it has ended the unpause is written** (the owner's
D114, README gap 5014, parity P115), run: the wall's pause logged at 1000 and a break running since 1200, asked at
2500 — nothing; the same break logged as ended (1200, 65 minutes) with none running — the unpause; a break begun at
2100, once the wall had ended — the unpause too; and with nothing logged, a break running since 1200 lets the pause be
written and holds the unpause. -/
theorem a_running_break_holds_the_walls_unpause_until_it_ends :
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) (some ⟨1200, 0⟩) [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .brk ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At) (some 65)]
      [(1000, 2000)] = [(false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) (some ⟨2100, 0⟩) [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)]
      = [(false, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) (some ⟨1200, 0⟩) [] [(1000, 2000)] = [(true, 1000, 2000)] := by
  decide

/-- **A block resumed inside a wall is paused from its resume until the wall ends** (the owner's D117, README gaps 5036
and 3042, parity P116), run: begun at 500 and interrupted 900–1200 across the wall `[1000, 2000)`'s start, asked at 2500
— the pause at the resume, 1200, and the unpause at the wall's end; asked at 1500 — the pause alone; resumed once the
wall had ended (2100), or still interrupted — nothing; and an interruption taken and resumed inside a meeting whose
pause the wall already wrote (1200–1300 under the pause at 1000) leaves that pause the last word, so the wall's end
writes the unpause (until W-48 the `resume` was the last word and the block stayed paused past the meeting). -/
theorem a_block_resumed_inside_a_wall_is_paused_from_its_resume_run :
    marksOf (⟨500, 0⟩ : Cal.Instant) (intSpans [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)])
        (writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)]
          [(1000, 2000)])
      = [.pause ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At), .unpause ((⟨2000, 0⟩, Cal.Offset.utc) : Replay.At)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨1500, 0⟩ : Cal.Instant) none [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At)]
      [(1000, 2000)] = [(true, 1000, 2000)] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At), .resume ((⟨2100, 0⟩, Cal.Offset.utc) : Replay.At)]
      [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.interrupt ((⟨900, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [] ∧
    writes (⟨500, 0⟩ : Cal.Instant) (⟨2500, 0⟩ : Cal.Instant) none [.pause ((⟨1000, 0⟩, Cal.Offset.utc) : Replay.At), .interrupt ((⟨1200, 0⟩, Cal.Offset.utc) : Replay.At),
      .resume ((⟨1300, 0⟩, Cal.Offset.utc) : Replay.At)] [(1000, 2000)] = [(false, 1000, 2000)] := by
  decide

/-! ## The hold a plan reserves after (README gap 5217, stage 6 W-49 track W) -/

/-- **The span that HOLDS the running block, with when it lets go** (README gap 5217, stage 6 W-49 track W): `pausedFor`'s
reading — the first joined span whose pause, at its pause second (`pauseSec`), is the last word on the timer, from that
second on — widened by the owner's **D114**: past the span's end too while a break running since before that end
(`breakHolds`) holds the block, the wall's `unpause` not yet written.  What the planner reserves the block's remainder
after (`Planner.PlanReq.wallHold`): a block so held resumes by itself, at the wall's end or the break's, with no keystroke
— unlike a pause the user typed or an interruption, which end when the user says.  Written by recursion, as `pausedFor`
is (README gap 3333), and equal to it with no break running (`heldFor_without_a_break`). -/
def heldFor (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) :
    List ((Nat × Nat) × List Id) → Option ((Nat × Nat) × List Id)
  | [] => none
  | x :: xs =>
    if (lastIsPauseAt marks ⟨pauseSec started ints x.1, 0⟩ &&
        decide ((⟨pauseSec started ints x.1, 0⟩ : Cal.Instant) ≤ now) &&
        (decide (now < ⟨x.1.2, 0⟩) || breakHolds brk x.1.2)) = true then some x
    else heldFor started ints now brk marks xs

/-- **With no break running, what holds the block is the meeting it is paused for**: `heldFor` is `pausedFor`. -/
theorem heldFor_without_a_break (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id)) :
    heldFor started ints now none marks spans = pausedFor started ints now marks spans := by
  induction spans with
  | nil => rfl
  | cons x xs ih => simp only [heldFor, pausedFor, breakHolds, Bool.or_false, ih]

/-- **What `heldFor` names holds the block, now**: one of the spans, its pause the last timer mark, `now` at or after
its pause second, and either inside it or past its end under a break running since before that end (D114). -/
theorem heldFor_spec (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id))
    (x : (Nat × Nat) × List Id) (h : heldFor started ints now brk marks spans = some x) :
    x ∈ spans ∧ lastIsPauseAt marks ⟨pauseSec started ints x.1, 0⟩ = true ∧
      (⟨pauseSec started ints x.1, 0⟩ : Cal.Instant) ≤ now ∧
      (now < ⟨x.1.2, 0⟩ ∨ breakHolds brk x.1.2 = true) := by
  induction spans with
  | nil => simp [heldFor] at h
  | cons y ys ih =>
    unfold heldFor at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      subst he
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
      exact ⟨List.mem_cons_self .., hc.1.1, hc.1.2, hc.2⟩
    · obtain ⟨hm, h1, h2, h3⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, h1, h2, h3⟩

/-- **A held block began at or before `now`**: its pause second is never before its start (`pauseSec_ge`). -/
theorem heldFor_started_le (started : Cal.Instant) (ints : List (Cal.Instant × Cal.Instant)) (now : Cal.Instant)
    (brk : Option Cal.Instant) (marks : List Replay.IdleMark) (spans : List ((Nat × Nat) × List Id))
    (x : (Nat × Nat) × List Id) (h : heldFor started ints now brk marks spans = some x) : started ≤ now := by
  have h2 := (heldFor_spec started ints now brk marks spans x h).2.2.1
  have h3 := (pauseSec_ge started ints x.1).2
  rw [Cal.Instant.le_iff] at h2 h3 ⊢; simp only at h2 h3 ⊢; omega

/-- **What holds the open block at `now`** (README gap 5217, W-49 track W): `heldFor` over the marks of the block's
ledger days as the LOG holds them (`blockMarks`) and the joined spans `spans`, under the running break `brk`.  `none`
with no open block.  The log is where the hold is: the walls form writes D61's, D110's and D117's marks before any plan
is asked of the day — the CLI's housekeeping appends them, and the TUI holds them in memory and hands them over in the
request's log (`Ctx::log_now`, the owner's D96) — so the planner (`Planner.PlanReq.wallHold`) reads the hold off the
log the request carries and never writes a mark of its own. -/
def holdOf (f : Seal.Answer) (spans : List ((Nat × Nat) × List Id)) (d : Nat) (now : Cal.Instant)
    (brk : Option Cal.Instant) : Option ((Nat × Nat) × List Id) :=
  match f.openBlock with
  | none => none
  | some ob => heldFor ob.started.1 (intSpans (blockMarks f ob d)) now brk (blockMarks f ob d) spans

/-- **What `holdOf` names holds the open block**: the replay holds a block open, the span is one of `spans`, the
block began at or before `now`, and `now` is inside the span or past it under a break running since before its end. -/
theorem holdOf_spec (f : Seal.Answer) (spans : List ((Nat × Nat) × List Id)) (d : Nat) (now : Cal.Instant)
    (brk : Option Cal.Instant) (x : (Nat × Nat) × List Id) (h : holdOf f spans d now brk = some x) :
    ∃ ob, f.openBlock = some ob ∧ x ∈ spans ∧ ob.started.1 ≤ now ∧
      (now < ⟨x.1.2, 0⟩ ∨ breakHolds brk x.1.2 = true) := by
  unfold holdOf at h
  split at h
  · simp at h
  · rename_i ob hob
    have hs := heldFor_spec _ _ _ _ _ _ x h
    exact ⟨ob, hob, hs.1, heldFor_started_le _ _ _ _ _ _ x h, hs.2.2.2⟩

/-- **Before the first free stretch everything is blocked** — the head of `Look.freeIntervals` starts at the first
free second at or after `lo`: every second from `lo` up to it is covered by a blocked span.  What a held block's
reservation starts after (README gap 5217): the wall, or the break, that holds it — nothing is placed in between. -/
theorem before_the_first_free_stretch_is_blocked (lo hi : Nat) (ws : List (Nat × Nat)) (iv : Nat × Nat)
    (rest : List (Nat × Nat)) (h : Look.freeIntervals lo hi ws = iv :: rest) (t : Nat) (h1 : lo ≤ t)
    (h2 : t < iv.1) : ∃ w ∈ ws, w.1 ≤ t ∧ t < w.2 := by
  have hmem : iv ∈ Look.freeIntervals lo hi ws := by rw [h]; exact List.mem_cons_self ..
  have hw := Look.freeIntervals_inside_the_window hmem
  have hord := Look.freeIntervals_are_in_order lo hi ws
  rw [h] at hord
  have hrest := (List.pairwise_cons.1 hord).1
  refine Classical.byContradiction fun hno => ?_
  have hfree : ∀ w ∈ ws, ¬ (w.1 ≤ t ∧ t < w.2) := fun w hw' hc => hno ⟨w, hw', hc⟩
  obtain ⟨iv', hiv', ha, hb⟩ := (Look.freeIntervals_are_the_free_units lo hi ws t).2 ⟨h1, by omega, hfree⟩
  rw [h] at hiv'
  rcases List.mem_cons.1 hiv' with he | hr
  · subst he; omega
  · have := hrest iv' hr; omega

end WallTimer
end Tm
