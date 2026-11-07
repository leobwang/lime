import LimeKernel.Planner.Planner
/-!
# `EmitDue.lean` — a HOT row's deadline, in §4.3's words (stage 6 W-47 track L, the owner's D112)

§4.3's own day prints `15:10  1 p0 ⚠  Pick up package  20m  due today`: a HOT row (§7.2) says when its deadline
falls.  Fork `tm-core/src/emit.rs` writes it in `note_cell`'s `⚠` branch, read by function name: `hot_note`,
`due_date` and `when`.  Until W-47 the kernel's `Emit.noteCell` answered `[]` there — README gap **1102**, a declared
hole while the binary's rows were Rust's, because the kernel was said to have no view of the fork's `effective_due`.  It
has had one since stage 4: `Plan.effectiveShape`, §3.2's prep rule.  The owner's **D112** makes the kernel's cells the
rows every surface prints, so the hole is fixed at its cause, and these are the words.

**Its own module, for a recorded reason.**  `Emit.lean`'s lines above its last theorem are check 9 pin sites (the
mutation roster records each by file and line), and these definitions must precede the cell that calls them; a module
`Emit.lean` imports in place of `Planner` moves no line there.  They are in namespace `Lime.Emit`, so the cell calls them
by their own names.

**What it reads, and the one place it parts from the fork.**  The deadline is the PLAN's reading (`effectiveShape`,
the one reader of a shape in this kernel), told against the day being planned (`today`).  §3.2's prep rule there is
ONE step — a shapeless item whose PARENT is an interval is due at its start (`effectiveShape_does_not_reach_the_grandparent`
pins it) — where fork `Tree::effective_shape` walks every shapeless ancestor to the first shaped one.  So a HOT row whose
only deadline is a grandparent interval's start says nothing here where the fork says `due …`: parity **P109**'s second
clause, licensed by D112 (the binary's bytes are the kernel's cells).  The HOT mark itself is the planner's
(`SegFlags.hot`); nothing here decides whether a row is hot.
-/

namespace Lime
namespace Emit

/-- **Fork `due_date`**: the day an item is due — its effective due (§6.4: a point's own day, an interval's start day),
else the last day of its window, a daily window closing on the day being planned (`today`). -/
def dueDayOf (p : PlanCore) (today : Nat) (i : Id) : Option Nat :=
  match effectiveShape p i with
  | .point m => some m.day
  | .interval s _ => some s.day
  | .window (.absolute _ e) _ => some e.day
  | .window (.daily _ _) _ => some today
  | .none => none

/- A weekday is told in `Field.renderWeekday`'s three letters, `every:`'s own (`Line.lean`), which are chrono's `%a`
(`renderWeekday_is_chronos` below).  A second table of the same seven words stood here in this module's draft and is
deleted: two definitions of one concept (AGENTS §5.3), found by reading — check 11 answered the pair on a clean build,
the two compiling their constants differently (README W-47 track L, gap 4960).  This is a comment and not a blank line
so that nothing below it moved and no check 9 pin site in this file drifted. -/

/-- **Fork `hot_note`'s words for a deadline `d` told against `today`**: `overdue`, `due today`, `due tomorrow`, a
weekday within the week (fork `when`'s `(0..7).contains(&days)` and `%a`), else the date (`Field.renderDate`, the
kernel's one `YYYY-MM-DD`). -/
def dueWords (today d : Nat) : List Char :=
  if d < today then ['o','v','e','r','d','u','e']
  else if d = today then ['d','u','e',' ','t','o','d','a','y']
  else if d = today + 1 then ['d','u','e',' ','t','o','m','o','r','r','o','w']
  else ['d','u','e',' '] ++ (if d < today + 7 then Field.renderWeekday (Cal.weekdayOf d) else Field.renderDate d)

/-- **Fork `hot_note`** — a HOT row's note: its key's deadline, in `dueWords`; `[]` when the row has no key or the key
no deadline the row could name (fork `hot_note` answering `None`). -/
def hotCell (p : PlanCore) (today : Nat) (key : Option Id) : List Char :=
  match key.bind (dueDayOf p today) with
  | none => []
  | some d => dueWords today d

/-! ## The laws -/

/-- **The words, at every branch** — 2026-09-07 (day 739865, a Monday) told against itself, the day before, the day
after, the Friday of its week and a date eight days out: the five sentences fork `hot_note` writes. -/
theorem dueWords_at_every_branch :
    dueWords 739865 739864 = "overdue".toList ∧
    dueWords 739865 739865 = "due today".toList ∧
    dueWords 739865 739866 = "due tomorrow".toList ∧
    dueWords 739865 739869 = "due Fri".toList ∧
    dueWords 739865 739873 = "due 2026-09-15".toList := by
  decide

/-- **The seven weekdays a deadline is told in are chrono's `%a`** — `Field.renderWeekday`, `every:`'s table. -/
theorem renderWeekday_is_chronos :
    [Cal.Weekday.monday, .tuesday, .wednesday, .thursday, .friday, .saturday, .sunday].map Field.renderWeekday
      = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"].map String.toList := by
  decide

/-- **No key, no deadline, no words.** -/
theorem hotCell_of_no_deadline (p : PlanCore) (today : Nat) (key : Option Id)
    (h : key.bind (dueDayOf p today) = none) : hotCell p today key = [] := by
  simp [hotCell, h]

/-- **A key with a deadline is told in `dueWords`.** -/
theorem hotCell_of_a_deadline (p : PlanCore) (today d : Nat) (key : Option Id)
    (h : key.bind (dueDayOf p today) = some d) : hotCell p today key = dueWords today d := by
  simp [hotCell, h]

/-- **A point is due on its own day.** -/
theorem dueDayOf_of_a_point (p : PlanCore) (today : Nat) (i : Id) (m : Field.Moment)
    (h : effectiveShape p i = .point m) : dueDayOf p today i = some m.day := by
  simp [dueDayOf, h]

/-- **An interval is due on the day it starts** — which is what a prep child's point is, one step down. -/
theorem dueDayOf_of_an_interval (p : PlanCore) (today : Nat) (i : Id) (s f : Field.DT)
    (h : effectiveShape p i = .interval s f) : dueDayOf p today i = some s.day := by
  simp [dueDayOf, h]

/-- **An absolute window closes on its last day.** -/
theorem dueDayOf_of_an_absolute_window (p : PlanCore) (today : Nat) (i : Id) (a b : Field.DT) (d : Field.Dur)
    (h : effectiveShape p i = .window (.absolute a b) d) : dueDayOf p today i = some b.day := by
  simp [dueDayOf, h]

/-- **A daily window closes on the day being planned**, whatever day that is. -/
theorem dueDayOf_of_a_daily_window (p : PlanCore) (today : Nat) (i : Id) (a b : Field.Clock) (d : Field.Dur)
    (h : effectiveShape p i = .window (.daily a b) d) : dueDayOf p today i = some today := by
  simp [dueDayOf, h]

/-- **A shapeless item under no interval has no deadline** — the row stays silent, as the fork's does. -/
theorem dueDayOf_of_no_shape (p : PlanCore) (today : Nat) (i : Id) (h : effectiveShape p i = .none) :
    dueDayOf p today i = none := by
  simp [dueDayOf, h]

/-- **A deadline's words are never empty** — every branch of `dueWords` says something. -/
theorem dueWords_ne_nil (today d : Nat) : dueWords today d ≠ [] := by
  unfold dueWords
  split
  · simp
  · split
    · simp
    · split
      · simp
      · simp

/-- **…so a HOT row whose key has a deadline is never silent**, whatever the day — the law a constant `hotCell`
falsifies, stated over `hotCell` itself and proved by unfolding it, not through `hotCell_of_a_deadline`, so it is a second
witness and not a corollary (check 9's second pass, README W-47 track L: `hotCell := []` was told from the definition by
`hotCell_of_a_deadline`'s proof alone until this law). -/
theorem hotCell_ne_nil_of_a_deadline (p : PlanCore) (today d : Nat) (key : Option Id)
    (h : key.bind (dueDayOf p today) = some d) : hotCell p today key ≠ [] := by
  unfold hotCell
  rw [h]
  exact dueWords_ne_nil today d

end Emit
end Lime
