import TmKernel.Log
import TmKernel.Arith
/-!
# Replay — the kernel replays `.tm/log.jsonl` (stage 5, D9 track, phase C)

Design `kernel/design/stage5/stage5-D9-D10-design.md` §7 (undo), §8 (the machine and the fact
catalogue) and §14.4 (phase C).  The fork point is the in-tree Rust, `tm-core/src/log.rs`
(`undo_mask`, `DayIndex`, `Machine`, `replay_lines`); the inventory
(`kernel/design/stage5/inventory.md` §2) is the fact base.  Phase C builds this module in steps:
C1 the undo mask, C2 the day index, C3–C5 the machine's families, C6 the facts and the headers,
C7 the undo law.  **Nothing in the binary reads it yet**: the `log` op's `facts` answer (Boundary.lean)
carries what is built so far, and `tm/tests/kernel_replay_parity.rs` (T5) compares it with the Rust.

## C1: the undo mask (§7.1)

Fork `undo_mask(entries)`, over the **raw entries in file order**, before any day or range logic
(inventory §2.2).  For each `undo{of, id?}` at `i`:

* `cancelled[i] = true`: **an undo is always cancelled itself** (`an_undo_never_survives`);
* the target is the **greatest `j < i`** with `!cancelled[j]`, entry `j` not an undo,
  `ev.name() == of`, and `ev.primary_id() == Some(id)` when `id` is given; it is cancelled;
* with no target, `i` is **dangling**.

`of` is compared with the tag, so it can name any kind, `plan`, `note` or an unknown tag included:
**`is_state_change` does not restrict the mask** (`the_mask_ignores_isStateChange`).  An undo of an
undo never matches, because undos are never targets: it dangles, and there is no redo
(`an_undo_of_an_undo_cancels_nothing_in_a_canonical_log`, `a_cancelled_event_is_never_revived`).  That
law needs the log to be canonical: an `unknown` event tagged `undo`, which no reader returns, would
match, in the fork as here (`an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo`).

**The specification** is a left fold over a stack of survivors, most recent first (`maskStep`):
an event is pushed, an undo removes the first (= most recent) match and never enters.  At step `i`
the stack holds exactly the entries `j < i` that are neither cancelled nor undos, most recent first,
so "the greatest uncancelled non-undo `j < i` that matches" is the stack's first match, which is
`List.eraseP`.  `survivors es` is the stack reversed, in file order.

**Positions, not entries, name a line.**  An `Entry` carries its line, but nothing in the type stops
a list from holding one entry twice, and every law here is stated for every list.  So the
cancelled set on the wire is by **position** (`stackI`, over `zipIdx`), and
`survivors_are_the_uncancelled_entries` ties it to `survivors`.  The one law that needs distinct
lines, `a_cancelled_event_is_never_revived`, takes `Log.linesIncreasing`, which the `log` op's entries
satisfy by construction (`the_tail_entries_have_increasing_lines`, Boundary.lean).

## The fast twin (`@[csimp]`, rule D9-21)

`List.eraseP` scans the stack, so a hostile log (thirty thousand events, then thirty thousand undos
of a tag or an id that is not there) costs a quadratic number of comparisons.  `maskFast` gives the
same answer from **per-tag and per-(tag, id) stacks of positions with lazy deletion**: an event's
position is pushed onto its tag's stack and, when it has a primary id, onto its `(tag, id)` stack;
an undo pops the dead positions off the top of the one stack it names, cancels the first live one,
and marks itself dead.  A position cancelled through one stack stays in the other until it reaches
the top there, where it is dropped.  Each position is pushed at most twice and dropped at most
twice, so the whole pass is linear in lookups.  The stacks live in `PosMap`, a hash table of
buckets that **replaces** a key's value (the loader's `IdMap` prepends a shadowing pair on every
insert, which is right for its insert-once uses and would grow a bucket per event here).  The
hash decides only which bucket is searched, never what is found.

`survivors_eq_survivorsFast` and `cancelledLines_eq_cancelledLinesFast` are the equalities; the
proofs stay on the specification (`maskFast_inv` is the simulation).  Both twins are `foldl`s over
the entries, so neither recurses per line.

## C2: the day index (§6.2)

Fork `DayIndex` (inventory §2.3), built over the **surviving** wakes (`dayIndexOf`):

* `keptWakes`: the wake instants sorted in **chrono's order** (`DateTime`'s `Ord`, the UTC `(sec, ns)`
  pair, which is `Cal.Instant`'s `≤` and not `Instant.nanos`'s order at a leap second), then fork
  `dedup_by` on the local date in `cfg.tz`.  **The porting trap: `dedup_by` is consecutive.**  The index
  keeps the first wake of each *run* of one date, not the earliest wake per date; the two differ when
  local dates are not monotone in instant order, a clock falling back across midnight
  (`the_day_index_dedups_runs_not_dates`; T5's St John's arm).
* `lastWakeLe` is `last_wake_before` (`partition_point(|w| *w <= t)`), and `dayOf` is `day_of`: the
  wake's local date when `t.signed_duration_since(w) < Duration::hours(24)` by chrono's duration
  (`Cal.durationBetween`, its leap-second rule), otherwise `t`'s own local date.
* **Restated in chrono's order.**  §15's three C2 goals test `Instant.nanos`; each is false of the
  fork's index at a leap second (`dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted`,
  `a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted`, `keptWakes_append_of_later_by_nanos_is_refuted`),
  and each is proved under its name with chrono's order and duration.
* **Quirk Q6(a), two "first wake" rules, ported faithfully** (gap 82).  The index keeps the earliest wake
  by instant per run; fork `DayReplay.wake` and `slept_by_day` (C5) read the first wake **in file order**
  attributed to the day (`firstLoggedWakeOn`).  `the_kept_wake_is_not_the_first_logged_wake` separates
  them on wakes appended out of time order, and
  `the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order` shows that is the only way
  they differ.
* **Every entry has a day**, cancelled entries and undos included (`entryDays`, fork `ViewRow::day`):
  what the `log` op's `facts.days` carries.
* Not ported: `DayIndex::bounds`, `wake_of` (`keptWakeOn` exists only to state Q6(a)) and
  `local_midnight`, which have no caller outside `log.rs`.

**The fast twins.**  `sortWakes` is an insertion sort, which `decide` evaluates; it is compiled as
core's merge sort (`sortWakes_eq_sortWakesFast`, by `eq_of_perm_of_sorted`: a list sorted in an
antisymmetric order is determined by its elements).  `entryDays` looks each entry's wake up with a fold
over the kept wakes; it is compiled as a bisection over an array of them, which is the fork's
`partition_point` (`entryDays_eq_entryDaysFast`, by `lePoint_spec` and `lastWakeLe_of_point`, using
`keptWakes_sorted`).  Without it, a log of thirty thousand wakes costs a quadratic number of instant
comparisons.

## C3: the machine, its effects, and the block family (§8.1–§8.2)

Fork `Machine::step` (inventory §2.4) as **effects**: `effects z kw slept st e` reads the state before an
entry and returns what the entry writes, each effect naming the one key it writes (`Effect.key`), and
`applyEffects` applies them in order.  `step` is the two composed, and `replay` folds `step` over the
survivors of the mask on the day index of their wakes, then `finish`es.

* **State** (§8.1).  `days` (the block fields of fork `DayReplay`), `items` (fork `ItemReplay`),
  `itemDays` (every `minutes_by_day`, keyed `(day, id)`), the observation and interruption lists, the
  headers, the machine (`block`, `lastCut`, `interrupt`) and the bookkeeping (`lastEffective`, the
  survivor count).  **A block's pending start observation lives in the block** and is emitted when the
  block closes or at `finish`, carrying its start's line; `finish` sorts by line, which puts it where the
  fork pushed it.  **`Cut.day` and the open interruption's day are stored**, computed once on the same
  index the fork recomputes them on.
* **The arms, one per event, all 27 constructors** (`arm`; `every_known_event_has_an_arm`): `start`,
  `pause`, `unpause`, `interrupt`, `resume`, `stop`, `done` (partial included) and `extend` here, every other
  event's arm `dayArm`'s (C5), and the completion family's `completionArm`'s (C4).  The helpers are ported by name (close_sub is `settle` since D99): `closePause`, `creditFx`,
  `uncreditFx`, `cut`; `doneClose` is the closing half of the `done` arm.
* **Site R8 (quirk Q6c, gap 83), ported faithfully**: `minutesOf` floors each piece's seconds on its own
  (`worked_minutes_floor_each_subsegment`), so a block paused `k` times can lose up to `k` minutes
  (`worked_minutes_is_not_the_floor_of_the_block`: two 90-second sub-segments give 2, not 3).
* **The rules a builder is tempted to fix**, each a witness: a start cuts any open block, even of its own id;
  a block cut by a start is never replaced by a `done`; a `stop` then a `done` replaces the cut's credit,
  partial or not; a `stop` for another id is ignored; a matched `done` discards the clock minutes;
  `close_pause` does not clear `paused`; a block started inside an interruption runs from the `resume`.
* **Laws.**  `applyEffects_touches_only_named_keys` (the frame law), `every_known_event_has_an_arm` (one
  header per entry) and `credit_conserves_the_day_minutes` (every day's ci minutes and ci-unknown minutes
  add up to its block minutes, by the invariant `Conserves`: the last cut's minutes are still on its day
  when a `done` takes them back), and, beside them, site R9's `load_is_exact_fifths` (a day's
  `load_fifths` is its ci minutes each weighed by its ci).
* **Sums are `Nat`** where the fork saturates `u32` (parity P17).  **`extend` writes its item**: under the
  owner's D14 `extended_min` is ported, so §8.2's "an extend changes only the bookkeeping" is refuted
  (`an_extend_changes_more_than_the_bookkeeping`) and restated
  (`an_extend_changes_only_the_bookkeeping_its_extended_minutes_and_its_blocks`, since the owner's D108).
* **Maps.**  Items and item-days, whose ids have no locality in a log, are arrays of association lists
  bucketed by `KeyHash` (`HMap`, `HMap.get_alter` on every map), updated in place when uniquely held; a
  day's ci-unknown minutes are one association list (`KMap`, `KMap.get_alter` on every list).  At C3 the
  days were a `KMap` too; C5 buckets them (below).  W4's tree maps remain the gated lever.
* **Not here**: `slept_by_day` and the day family's arms (C5, below), and the cancelled lines' headers
  (C6's second pass).

## C4: the completion family (§8.2–§8.4)

`completionArm`, a second match beside `arm`: a non-partial `done`'s `mark_done`, `routine`, `skip` and
`event`.  **Quirk Q6(b), ported faithfully** (gap 118): fork `instances[item][inst]` keeps the last record in file order
(`an_instance_is_its_last_record_in_file_order`) and fork `last_done` the latest by instant, the first of equal
instants (`last_done_is_the_latest_by_instant`, `last_done_is_the_first_of_the_latest`); a retro append
separates them (`instances_and_last_done_order_differently`).  Fork `LatestNamed` keeps two instants per
`(name, id?)`, because a "since" filter does not commute with the latest by instant when the zone's clock goes
back across midnight (`a_since_filter_does_not_commute_with_the_latest_by_instant`,
`named_keeps_the_latest_by_instant_and_the_latest_by_local_date`).  An unknown routine status is the replay
warning `unknownInstanceStatus` and reads as `Pending`.  `arm_ofBlock` keeps the block family's arm off the
completion state.  The `routine` arm's `Routine` segment and `routine_min` are day fields, C5's.

## C5: the day header and records family (§8.2–§8.4)

`dayArm`, the machine's arm for every event outside the block family (`arm` is one match: the block family's
eight events, then `dayArm`): `wake`, `arrive`, `loc`, `break`, `energy`, `idle`, `routine`'s day half, `plan`,
`demote`, `drop`, `close` and unknown events; `readopt`, `move`, `edit`, `note` and `undo` write nothing.
`DayAcc` is now the whole of fork `DayReplay`, and the state gains fork `demotions`, `closes`, `dropped_items`,
the global `longest_leak` and `unknown`.  Days are bucketed (`HMap`), as items are: a wake creates its day, and
a log of wakes on as many dates would make an association list's absent-key scan quadratic.
* **Late binding.**  `replay` builds fork `slept_by_day` before the walk (`sleptByDay`, read by its first pair
  of a day), so an `energy` line logged before its day's wake reads it
  (`energy_obs_slept_is_the_days_first_logged_sleep`, by the invariant `SleptInv`: the machine's pending
  observation is a start's).  The compiled replay keeps it in buckets (`sleptMap`).
* **Quirk Q6(a), the day's half** (gap 82): the day's `wake` and `slept_min` are the first wake **in file order**
  (`the_days_wake_is_its_first_logged_wake`), not the index's earliest by instant.
* **A gap is on the day it began**: an `idle` gap `[t − min, t]` and a routine's `[t − min, t]` are dated by
  their start (`Cal.subMinutes`), a routine's minutes by its own day (`a_gap_is_on_the_day_it_began`); a
  break ends at `addMinutes t (actual_or_planned)`.
* **The first leak maximum wins** (`the_first_leak_maximum_wins`, `the_longest_leak_is_the_first_of_the_longest`).
* **The records outside a day**: the demotions and closes are the survivors' in file order, each on its day
  (`the_demotions_are_the_survivors_demotes_in_file_order`, `the_closes_are_the_survivors_closes_in_file_order`),
  a demotion's stamp is its `from` key's (`a_demote_stamp_reads_the_week_or_date_key`), and the unknown count is
  the surviving unknown events (`the_unknown_count_is_the_surviving_unknown_events`).
* **Quirks, with their separations**: Q6(f) is **fixed** at W-12 (gap 86) — a `close` carries `period:key` as its
  primary id, so an undo of a week close cancels *that* close and not the automatic one a later verb appended,
  while a log written before the fix still reads as it did
  (`an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest`); Q6(g) is still ported
  faithfully — the calendar's today is not the replay's day after midnight
  (`the_calendar_today_is_not_the_replays_day_after_midnight`, gap 87).
* **`idle` and `idle_since` read different orders** (§8.4): `lastEffective` is the last line, `lastTOn` (fork
  `DaySeam.last_t`, which C6 derives) the latest instant (`idle_and_idle_since_read_different_orders`).

## C6: the facts, the observations and the headers (§8.2, §8.4, §11)

* **Every line has one header effect** (§8.2): a survivor's is in its `effects`, `HeaderRec.of e false`, and a
  cancelled line's is the **second pass**, `cancelledHeaderFx`, `cancelled := true`.  `entryHeaders` is every entry's
  header in file order with its day and mask bit, and the two passes are exactly it
  (`the_survivors_headers_are_the_uncancelled_entry_headers`, `the_two_header_passes_are_every_entrys_header`).  A
  header keeps its written stamp; the display (`LogStamp.displayStamp`, fork `ViewRow::display`) is rendered at
  emission.
* **The seams** (fork `DaySeam`, Phase R's R1, R2, R4) are one effect of every survivor on its day, `Effect.seam`:
  the since-break anchor (the last `break`'s end, else the first `start`), the idle marks in file order, and
  `last_t`, which is C5's `lastTOn` (`a_days_last_t_is_the_latest_stamp_of_its_survivors`).  A day holding only a
  `note` has a seam and no `DayAcc`, as in the fork.
* **A dated record carries its line**: `Interruption` (its `resume`'s; the open one 0), `Demotion` and `CloseRec`, so
  a view handed back per day restores the fork's order, as observations do (§11.2).
* **Observations are in file order** on the log op's entries, whose lines strictly increase
  (`observations_are_in_file_order_on_increasing_lines`, by the multiset of emitted and pending lines:
  `arm_obs`, `foldl_stepWith_obs`); §15's statement over every list is refuted by a repeated line
  (`observations_are_not_in_file_order_when_a_line_repeats`).
* **Every dated output names its day key** (CRIT 9): `Effect.day?` is the day of the dated record an effect writes,
  `Key.date?` the date a key names (`every_dated_output_names_its_day_key`).  The global longest leak is an all-time
  aggregate keyed `global`; its gap's day is named by the same entry's idle record
  (`every_leak_is_on_a_day_its_idle_record_names`).
* **The view** (§8.4): `replayDoc` (the facts, every header, the entry count), `Q` (one query per reading: a day's,
  a window date's, and the all-time ones), `factsView` (every fact reading, through `get`, so the answer does not
  depend on bucket counts; the line bookkeeping answers `lines`) and `ask` (it and the headers).  The wire groups the
  view by where each fact lives (`dayOuts`, `winOuts`, `itemOuts`, `instOthers`).

## C7: the undo law (§7.3)

* **The law** (`undoing_a_command_replays_the_log_without_it`): `tm undo` of a command whose events `E` are followed
  by events `M` it did not write appends `undosFor E` (one `undo{of: tag, id: primary id}` per event, most recent
  first), and when `untouchedBy E M` (no event of `M` is an undo or matches one of those undos) the view of
  `L ++ E ++ M ++ undosFor E` is the view of `L ++ M`.  **This is what "`tm undo` must replay the log, never apply an
  inverse command" (`move_has_no_inverse_command`, L22, Boundary.lean) always pointed at.**
* **Two halves**: the survivors are those of `L ++ M`, entry for entry
  (`undoing_a_command_leaves_the_survivors_of_the_log_without_it`), and the view reads only the survivors
  (`the_view_reads_only_the_survivors`): the replay sizes its maps by the log's length, and the view reads every map
  through `get` (`SameReadings`) and a map's pairs only through its keys, one set whatever the bucket count
  (`HMap.Keyed`, `HMap.perm_keys_pairs`).
* **The quirks the hypothesis excludes, ported faithfully**: Q6(d), a silent verb's `undo{of: verb}` cancels the
  latest survivor named like the verb (`a_silent_verb_undo_cancels_the_latest_event_of_its_name`), and nothing exactly
  when no survivor is (`a_silent_verb_undo_cancels_nothing_iff_no_survivor_has_its_name`; gap 84); Q6(f), the undo of a
  week close cancels the automatic close after it (`undo_after_housekeeping_cancels_the_housekeeping`), so the law
  fails without its hypothesis (`the_undo_law_fails_without_untouchedBy`; gap 86).

## Rule D9-21 (functions here over a list the wire can make large)

`survivors`, `stackI`, `danglingOf` (`foldl`, specification only: compiled as their `@[csimp]` twins or
not called by the wire), `maskFast` (`foldl` of `maskFastStep`), `survivorsFast` and
`cancelledLinesFast` (`zipIdx`, `filterTR`, `mapTR`), `keyHash` (`foldl`), `pairKey`
(`flatMapTR`, `appendTR`), `PosMap.get` (`find?`), `PosMap.set` (`filterTR`), `List.dropWhile`
(a loop), and `Log.linesIncreasing` (the tail of `&&`; specification only).
C2 adds: `sortWakesFast` (core `mergeSort`, compiled as `mergeSortTR₂` behind core's `@[csimp]`;
it recurses on halves), the dedup (`foldl` of `keptStep`, then `reverse`), `wakeInstants` (`filterTR`,
`mapTR`), `entryDaysFast` (`mapTR` and one `toArray`), `lePoint` (a bisection, recursion depth
`log₂` of the wakes), and `Cal.localDate` (`offsetAt`, a `foldl` over at most 4,096 transitions).
Specification only, never on the wire: `insertWake` and `sortWakes` (compiled as their twin),
`lastWakeLe` and `entryDays` (compiled as `entryDaysFast`), and `keptWakeOn` and `firstLoggedWakeOn`
(`find?`, a loop; not called by the op).
C3 adds: `applyEffects` and the replay's fold (`foldl`), `KMap.get` (`find?`, a loop), `KMap.alter` and
`KMap.alterGo` (a tail-recursive loop, `reverseAux`, `filterTR`), `HMap.get` and `HMap.alter` (one bucket's
`KMap`, `Array.modify`), `HMap.mapVals` and `HMap.pairs` (`toList`, `mapTR`, a `foldl`), `finish` (`mapTR`,
`reverse`, `appendTR`),
`sortObsFast` and `sortSegsFast` (core `mergeSort`, compiled as `mergeSortTR₂`), and `replayFast`'s day
lookups (the C2 bisection, `dayOfArr`).  Specification only, never on the wire: `insBy` and `insSort`
(compiled as the merge sorts), `State.valueAt` (`filter`), `KMap.vsum` (`List.sum`), and `replay` itself
(compiled as `replayFast`).
C4 adds: `completionArm`, `NamedRec.push`, `pick` and `lastMaxStep` (no recursion), `HMap.alter` per completion
effect, and `finish`'s warnings (`reverse`).  Specification only, never on the wire: `lastMax?` and
`maxByInstant?` (`foldl`), `doneInstants` (`filter`, `map`), `namedOccurrences` (`filterMap`), and the
`Effect` projections of the laws.
C5 adds: `dayArm` and `addMinutes` (no recursion; a `DayOp` is one record update, a day found in its bucket),
`sleptMap` (a `foldl` of `sleptStep`, one `HMap.alter` a wake) and its lookups (one bucket), `DayAcc.finish`'s
new reverses and `finish`'s demotions and closes (`reverse`), and `HMap.mapVals` over the days.  Specification
only, never on the wire: `sleptByDay` (`filterMap`; compiled as `sleptMap` through `replay_eq_replayFast`),
`firstLoggedSleep` (`find?`), `leakOf`, `demotionOf`, `closeOf`, `isUnknownEv` and `lastTOn` (`filter`, `map`,
`foldl`), `insBy_perm`/`insSort_perm`, and the `Effect` projections of the laws.
C6 adds: `entryHeadersFast` (`zipIdx`, `mapTR`, one `maskFast` and one array of the kept wakes; `@[csimp]` twin of
`entryHeaders`), `replayDocFast` (`@[csimp]` twin of `replayDoc`: the mask and the day index computed once for the
replay and the headers), `SeamOp.apply` (no recursion; one `HMap.alter` a survivor), `dayOuts`, `winOuts` and `itemOuts` (one
`foldl` per list or map, into buckets; `reverse` first where a day's list keeps file order), `instOthers` (`filterTR`),
`maxDay?` and `minDay?` (`foldl`).  Specification only, never on the wire: `entryHeaders` (compiled as its twin),
`cancelledHeaderFx` (`filter`, `map`), `factsView` and `ask` (`filter`, `map`; W's laws read them), `pendLines`,
`obsLines` and the `Effect` projections of the laws.
C7 adds nothing on the wire.  Specification only: `undosFor` (`zipIdx`, `map`), `untouchedBy` (`all`), and
`HMap.Keyed`, `SameReadings` and `PairsKeyed` (propositions).
-/
namespace Tm
namespace Log

/-- **The lines of a list of entries strictly increase.**  What the `log` op's entries satisfy: each
is read at its physical line (`logVerdicts_eq`), and lines only grow.  A specification: no wire
path evaluates it. -/
def linesIncreasing : List Entry → Bool
  | a :: b :: rest => decide (a.line < b.line) && linesIncreasing (b :: rest)
  | _ => true

theorem linesIncreasing_pairwise : ∀ (es : List Entry), linesIncreasing es = true →
    es.Pairwise (fun a b => a.line < b.line)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [linesIncreasing, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := linesIncreasing_pairwise (b :: rest) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

end Log

namespace Replay

open Log (Entry Event)

/-! ## The specification (§7.1) -/

/-- **`undo{of, id}` matches `e`**: fork `ev.name() == of` and, when `id` is given,
`ev.primary_id() == Some(id)`.  The fork's `!matches!(ev, Event::Undo { .. })` is not a clause:
undos never reach the stack. -/
def «matches» (of_ : List Char) (id : Option Log.Id) (e : Entry) : Bool :=
  e.ev.tag == of_ && id.all (fun x => e.ev.primaryId == some x)

/-- The survivor stack, most recent first.  An undo removes the first (= most recent) match and never
enters. -/
def maskStep (st : List Entry) (e : Entry) : List Entry :=
  match e.ev with
  | .undo of_ id => st.eraseP («matches» of_ id)
  | _            => e :: st

/-- **The entries no undo cancelled, in file order**, undos excluded. -/
def survivors (es : List Entry) : List Entry := (es.foldl maskStep []).reverse

/-- The mask with its dangling undos: the stack, and the undos that matched nothing, most recent
first. -/
def dangleStep (acc : List Entry × List Entry) (e : Entry) : List Entry × List Entry :=
  match e.ev with
  | .undo of_ id =>
    if acc.1.any («matches» of_ id) then (acc.1.eraseP («matches» of_ id), acc.2) else (acc.1, e :: acc.2)
  | _ => (e :: acc.1, acc.2)

def danglingOf (es : List Entry) : List Entry × List Entry := es.foldl dangleStep ([], [])

/-- **`u` is an undo that matched nothing at its step** (fork `UndoMask::dangling`). -/
def dangles (es : List Entry) (u : Entry) : Bool := (danglingOf es).2.contains u

/-- The stack with each entry's position in the list (`zipIdx`): what names a line when a list holds
one entry twice. -/
def maskStepI (st : List (Entry × Nat)) (p : Entry × Nat) : List (Entry × Nat) :=
  match p.1.ev with
  | .undo of_ id => st.eraseP (fun q => «matches» of_ id q.1)
  | _            => p :: st

def stackI (es : List Entry) : List (Entry × Nat) := es.zipIdx.foldl maskStepI []

/-- **Fork `UndoMask::cancelled[i]`**: the entry at position `i` is an undo or was undone. -/
def cancelledAt (es : List Entry) (i : Nat) : Bool := !((stackI es).any (fun q => q.2 == i))

/-- **The cancelled line set**: the lines of the cancelled entries, in file order (what the `log`
op's `facts.cancelled` carries, and what T5 compares with `ViewRow::cancelled`). -/
def cancelledLines (es : List Entry) : List Nat :=
  (es.zipIdx.filter (fun p => cancelledAt es p.2)).map (fun p => p.1.line)

/-! ## The laws of the specification -/

theorem survivors_nil : survivors [] = [] := rfl

/-- `survivors_snoc_event` (Goals, §15, C1). -/
theorem survivors_snoc_event (es : List Entry) (e : Entry) (h : e.ev.isUndo = false) :
    survivors (es ++ [e]) = survivors es ++ [e] := by
  unfold survivors
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have : maskStep (es.foldl maskStep []) e = e :: es.foldl maskStep [] := by
    unfold maskStep; split
    · rename_i of_ id hev; simp [hev, Event.isUndo] at h
    · rfl
  rw [this, List.reverse_cons]

/-- `survivors_snoc_undo` (Goals, §15, C1). -/
theorem survivors_snoc_undo (es : List Entry) (e : Entry) (of_ : List Char) (id : Option Log.Id)
    (h : e.ev = .undo of_ id) :
    survivors (es ++ [e]) = ((survivors es).reverse.eraseP («matches» of_ id)).reverse := by
  unfold survivors
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.reverse_reverse]
  simp only [maskStep, h]

theorem mem_foldl_maskStep : ∀ (es : List Entry) (st : List Entry) (x : Entry),
    x ∈ es.foldl maskStep st → x ∈ st ∨ x ∈ es
  | [], _, _, h => Or.inl h
  | e :: es, st, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_maskStep es _ x h with h | h
    · unfold maskStep at h
      split at h
      · exact Or.inl (List.mem_of_mem_eraseP h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem not_undo_of_mem_foldl_maskStep : ∀ (es : List Entry) (st : List Entry) (x : Entry),
    (∀ y ∈ st, y.ev.isUndo = false) → x ∈ es.foldl maskStep st → x.ev.isUndo = false
  | [], _, _, hst, h => hst _ h
  | e :: es, st, x, hst, h => by
    rw [List.foldl_cons] at h
    refine not_undo_of_mem_foldl_maskStep es _ x (fun y hy => ?_) h
    unfold maskStep at hy
    split at hy
    · exact hst y (List.mem_of_mem_eraseP hy)
    · rename_i hne
      rcases List.mem_cons.1 hy with rfl | hy
      · cases hev : y.ev <;> simp_all [Event.isUndo]
      · exact hst y hy

/-- **An undo never survives** (§7.1; cheat 143 is its negation's witness). -/
theorem an_undo_never_survives (es : List Entry) (u : Entry) (hu : u ∈ survivors es) :
    u.ev.isUndo = false :=
  not_undo_of_mem_foldl_maskStep es [] u (by simp) (List.mem_reverse.1 hu)

/-- A survivor is one of the log's entries. -/
theorem mem_of_mem_survivors (es : List Entry) (x : Entry) (h : x ∈ survivors es) : x ∈ es := by
  rcases mem_foldl_maskStep es [] x (List.mem_reverse.1 h) with h | h
  · simp at h
  · exact h

/-- `a_cancelled_event_is_never_revived` (Goals, §15, C1): an entry of a prefix that does not survive
it survives no extension.  `hl` is what rules out the same entry appearing again later. -/
theorem a_cancelled_event_is_never_revived (es fs : List Entry) (e : Entry)
    (hl : Log.linesIncreasing (es ++ fs) = true) (he : e ∈ es) (hc : e ∉ survivors es) :
    e ∉ survivors (es ++ fs) := by
  intro h
  have hp := List.pairwise_append.1 (Log.linesIncreasing_pairwise _ hl)
  unfold survivors at h hc
  rw [List.mem_reverse, List.foldl_append] at h
  rw [List.mem_reverse] at hc
  rcases mem_foldl_maskStep fs _ e h with h | h
  · exact hc h
  · exact Nat.lt_irrefl _ (hp.2.2 e he e h)

theorem danglingOf_fst_go : ∀ (es : List Entry) (st ds : List Entry),
    (es.foldl dangleStep (st, ds)).1 = es.foldl maskStep st
  | [], _, _ => rfl
  | e :: es, st, ds => by
    rw [List.foldl_cons, List.foldl_cons]
    have : ∃ ds', dangleStep (st, ds) e = (maskStep st e, ds') := by
      unfold dangleStep maskStep
      split
      · rename_i of_ id _
        by_cases ha : st.any («matches» of_ id) = true
        · exact ⟨ds, by simp [ha]⟩
        · refine ⟨e :: ds, ?_⟩
          simp only [ha, if_false, Bool.false_eq_true]
          rw [List.eraseP_of_forall_not]
          intro a hmem hm
          exact ha (List.any_eq_true.2 ⟨a, hmem, hm⟩)
      · exact ⟨ds, rfl⟩
    obtain ⟨ds', h⟩ := this
    rw [h]
    exact danglingOf_fst_go es _ ds'

/-- The dangling fold's stack is the mask's. -/
theorem danglingOf_fst (es : List Entry) : (danglingOf es).1 = es.foldl maskStep [] :=
  danglingOf_fst_go es [] []

theorem danglingOf_snd_mono : ∀ (fs : List Entry) (acc : List Entry × List Entry) (u : Entry),
    u ∈ acc.2 → u ∈ (fs.foldl dangleStep acc).2
  | [], _, _, h => h
  | f :: fs, acc, u, h => by
    rw [List.foldl_cons]
    apply danglingOf_snd_mono fs
    unfold dangleStep
    split
    · split
      · exact h
      · exact List.mem_cons_of_mem _ h
    · exact h

/-- `a_dangling_undo_dangles_in_every_extension` (Goals, §15, C1).  **Stated without §15's `hl` and
`hu`**, which the law does not need: the dangling undos of a prefix are dangling undos of every
extension, whatever the lines (README, C1 disagreement 2).  §15's form is this theorem applied to
fewer arguments. -/
theorem a_dangling_undo_dangles_in_every_extension (es fs : List Entry) (u : Entry)
    (hd : dangles es u = true) : dangles (es ++ fs) u = true := by
  unfold dangles danglingOf at *
  rw [List.foldl_append]
  simp only [List.contains_iff_mem] at *
  exact danglingOf_snd_mono fs _ u hd

/-- A dangling undo is an undo. -/
theorem an_entry_that_dangles_is_an_undo (es : List Entry) (u : Entry) (hd : dangles es u = true) :
    u.ev.isUndo = true := by
  unfold dangles danglingOf at hd
  simp only [List.contains_iff_mem] at hd
  suffices ∀ (fs : List Entry) (acc : List Entry × List Entry), (∀ y ∈ acc.2, y.ev.isUndo = true) →
      ∀ y ∈ (fs.foldl dangleStep acc).2, y.ev.isUndo = true from this es _ (by simp) u hd
  intro fs
  induction fs with
  | nil => intro acc h; exact h
  | cons f fs ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    intro y hy
    unfold dangleStep at hy
    split at hy
    · rename_i of_ id hev
      split at hy
      · exact h y hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · simp [hev, Event.isUndo]
        · exact h y hy
    · exact h y hy

/-- In a canonical event (every event `readLine` returns), only an undo carries the tag `undo`: an
unknown event's tag is not a known one. -/
theorem isUndo_of_tag_undo (ev : Event) (hc : ev.canonical = true) (ht : ev.tag = Log.Kind.undo.tag) :
    ev.isUndo = true := by
  cases ev <;> try rfl
  all_goals try (simp [Event.tag, Log.Kind.tag] at ht; done)
  rename_i t rest
  simp only [Event.tag] at ht
  subst ht
  have hk : Log.isKnownTag Log.Kind.undo.tag = true := by decide
  simp [Event.canonical, hk] at hc

/-- No survivor of a canonical log matches `undo{of:"undo"}`. -/
theorem no_survivor_matches_an_undo_of_an_undo (es : List Entry) (hc : ∀ e ∈ es, e.ev.canonical = true)
    (id : Option Log.Id) (a : Entry) (ha : a ∈ es.foldl maskStep []) :
    «matches» Log.Kind.undo.tag id a = false := by
  apply Bool.eq_false_iff.2
  intro hm
  have hundo := not_undo_of_mem_foldl_maskStep es [] a (by simp) ha
  have hmem : a ∈ es := mem_of_mem_survivors es a (List.mem_reverse.2 ha)
  unfold «matches» at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  rw [isUndo_of_tag_undo a.ev (hc a hmem) hm.1] at hundo
  cases hundo

/-- **An undo of an undo cancels nothing** in a canonical log: no stack entry is an undo, so
`undo{of:"undo"}` matches nothing and the survivors are unchanged (fork: no redo).  The hypothesis is
needed: an `unknown` event whose tag is `undo`, which no reader returns, would match
(`an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo`). -/
theorem an_undo_of_an_undo_cancels_nothing_in_a_canonical_log (es : List Entry) (u : Entry)
    (id : Option Log.Id) (hc : ∀ e ∈ es, e.ev.canonical = true)
    (h : u.ev = .undo Log.Kind.undo.tag id) : survivors (es ++ [u]) = survivors es := by
  rw [survivors_snoc_undo es u _ id h, List.eraseP_of_forall_not, List.reverse_reverse]
  intro a ha hm
  rw [List.mem_reverse] at ha
  rw [no_survivor_matches_an_undo_of_an_undo es hc id a (by simpa [survivors] using ha)] at hm
  cases hm

theorem dangleStep_of_no_match (acc : List Entry × List Entry) (e : Entry) (of_ : List Char)
    (id : Option Log.Id) (h : e.ev = .undo of_ id) (hna : acc.1.any («matches» of_ id) = false) :
    dangleStep acc e = (acc.1, e :: acc.2) := by
  unfold dangleStep; simp [h, hna]

/-- And it dangles. -/
theorem an_undo_of_an_undo_dangles_in_a_canonical_log (es : List Entry) (u : Entry) (id : Option Log.Id)
    (hc : ∀ e ∈ es, e.ev.canonical = true)
    (h : u.ev = .undo Log.Kind.undo.tag id) : dangles (es ++ [u]) u = true := by
  unfold dangles danglingOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hna : (es.foldl dangleStep ([], [])).1.any («matches» Log.Kind.undo.tag id) = false := by
    rw [danglingOf_fst_go]
    apply Bool.eq_false_iff.2
    intro hany
    obtain ⟨a, ha, hm⟩ := List.any_eq_true.1 hany
    rw [no_survivor_matches_an_undo_of_an_undo es hc id a ha] at hm
    cases hm
  rw [dangleStep_of_no_match _ u _ id h hna]
  simp

/-! ## The positions: `stackI` is the stack -/

theorem maskStepI_map (st : List (Entry × Nat)) (p : Entry × Nat) :
    (maskStepI st p).map Prod.fst = maskStep (st.map Prod.fst) p.1 := by
  unfold maskStepI maskStep
  cases hev : p.1.ev <;> simp only [List.map_cons, List.eraseP_map] <;> rfl

theorem foldl_maskStepI_map : ∀ (l : List (Entry × Nat)) (st : List (Entry × Nat)),
    (l.foldl maskStepI st).map Prod.fst = (l.map Prod.fst).foldl maskStep (st.map Prod.fst)
  | [], _ => rfl
  | p :: l, st => by
    rw [List.foldl_cons, foldl_maskStepI_map l, maskStepI_map]; rfl

theorem zipIdx_map_fst (es : List Entry) (n : Nat) : (es.zipIdx n).map Prod.fst = es := by
  induction es generalizing n with
  | nil => rfl
  | cons e es ih => simp [List.zipIdx_cons, ih]

/-- `stackI` is the mask's stack, with positions. -/
theorem stackI_map (es : List Entry) : (stackI es).map Prod.fst = es.foldl maskStep [] := by
  unfold stackI
  rw [foldl_maskStepI_map, zipIdx_map_fst]; rfl

/-! ## The fast twin -/

/-- The bucket hash (the loader's `idHash` function, restated here so this module does not import
the plan). -/
def keyHash (k : List Char) : Nat := k.foldl (fun h c => (h * 31 + c.toNat) % 4294967291) 7

/-- **A table from keys to stacks of positions** whose `set` replaces the key's value in its bucket. -/
structure PosMap where
  buckets : Array (List (List Char × List Nat))

def PosMap.empty (n : Nat) : PosMap := ⟨Array.replicate (n + 1) []⟩

def PosMap.slot (m : PosMap) (k : List Char) : Nat := keyHash k % m.buckets.size

def PosMap.get (m : PosMap) (k : List Char) : List Nat :=
  match m.buckets[m.slot k]? with
  | none   => []
  | some b =>
    match b.find? (fun q => q.1 == k) with
    | some q => q.2
    | none   => []

def PosMap.set (m : PosMap) (k : List Char) (v : List Nat) : PosMap :=
  ⟨m.buckets.modify (m.slot k) (fun b => (k, v) :: b.filter (fun q => !(q.1 == k)))⟩

theorem PosMap.size_set (m : PosMap) (k : List Char) (v : List Nat) :
    (m.set k v).buckets.size = m.buckets.size := by simp [PosMap.set]

theorem PosMap.get_empty (n : Nat) (k : List Char) : (PosMap.empty n).get k = [] := by
  simp only [PosMap.get, PosMap.slot, PosMap.empty, Array.getElem?_replicate, Array.size_replicate]
  split
  · rfl
  · rename_i b hb
    split at hb
    · cases hb; rfl
    · cases hb

theorem find?_filter_ne (b : List (List Char × List Nat)) (k j : List Char) (h : j ≠ k) :
    (b.filter (fun q => !(q.1 == k))).find? (fun q => q.1 == j) = b.find? (fun q => q.1 == j) := by
  induction b with
  | nil => rfl
  | cons q b ih =>
    by_cases hq : q.1 = k
    · have h1 : (!(q.1 == k)) = false := by simp [hq]
      have h2 : (q.1 == j) = false := by rw [hq]; exact beq_false_of_ne (Ne.symm h)
      rw [List.filter_cons, if_neg (by simp [h1]), ih, List.find?_cons, h2]
    · have h1 : (!(q.1 == k)) = true := by simp [hq]
      rw [List.filter_cons, if_pos h1, List.find?_cons, List.find?_cons, ih]

theorem PosMap.get_set (m : PosMap) (k j : List Char) (v : List Nat) (hpos : 0 < m.buckets.size) :
    (m.set k v).get j = if j = k then v else m.get j := by
  have hlt : ∀ x, keyHash x % m.buckets.size < m.buckets.size := fun x => Nat.mod_lt _ hpos
  unfold PosMap.get
  simp only [PosMap.slot, PosMap.size_set]
  simp only [PosMap.set, PosMap.slot, Array.getElem?_modify, Array.getElem?_eq_getElem (hlt j)]
  by_cases hjk : j = k
  · subst hjk; simp
  · by_cases hs : keyHash k % m.buckets.size = keyHash j % m.buckets.size
    · have hb : (k == j) = false := beq_false_of_ne (Ne.symm hjk)
      simp only [hs, if_true, Option.map_some, List.find?_cons, hb, hjk, if_false]
      rw [find?_filter_ne _ _ _ hjk]
    · simp [hs, hjk]

/-- Positions pushed per tag, and per tag and id: the key of a `(tag, id)` stack.  Injective
(`pairKey_inj`): each character of the tag is prefixed by `1`, and `0` ends the tag. -/
def pairKey (tag id : List Char) : List Char := tag.flatMap (fun c => ['1', c]) ++ '0' :: id

theorem pairKey_inj : ∀ (a b x y : List Char), pairKey a x = pairKey b y → a = b ∧ x = y
  | [], [], x, y, h => by simpa [pairKey] using h
  | [], c :: _, _, _, h => by simp [pairKey] at h
  | c :: _, [], _, _, h => by simp [pairKey] at h
  | c :: a, d :: b, x, y, h => by
    simp only [pairKey, List.flatMap_cons, List.cons_append, List.nil_append, List.cons.injEq,
      true_and] at h
    obtain ⟨hcd, h⟩ := h
    have := pairKey_inj a b x y h
    exact ⟨by rw [hcd, this.1], this.2⟩

/-- Whether position `j` has been marked dead (cancelled, or an undo). -/
def deadAt (dead : Array Bool) (j : Nat) : Bool := dead[j]?.getD false

structure MaskState where
  dead  : Array Bool
  byTag : PosMap
  byKey : PosMap

/-- **One entry of the fast pass.**  The state is taken apart in the pattern, and every lookup is
done before the update, so each table and the array reach their update with no other reference and
are changed in place (the loader's `dedupStep` pattern). -/
def maskFastStep : MaskState → Entry × Nat → MaskState
  | ⟨dead, byTag, byKey⟩, (e, k) =>
    match e.ev with
    | .undo of_ none =>
      match (byTag.get of_).dropWhile (deadAt dead) with
      | []        => ⟨dead.setIfInBounds k true, byTag.set of_ [], byKey⟩
      | j :: rest => ⟨(dead.setIfInBounds j true).setIfInBounds k true, byTag.set of_ rest, byKey⟩
    | .undo of_ (some x) =>
      match (byKey.get (pairKey of_ x)).dropWhile (deadAt dead) with
      | []        => ⟨dead.setIfInBounds k true, byTag, byKey.set (pairKey of_ x) []⟩
      | j :: rest => ⟨(dead.setIfInBounds j true).setIfInBounds k true, byTag, byKey.set (pairKey of_ x) rest⟩
    | _ =>
      match e.ev.primaryId with
      | none   => ⟨dead, byTag.set e.ev.tag (k :: byTag.get e.ev.tag), byKey⟩
      | some x =>
        ⟨dead, byTag.set e.ev.tag (k :: byTag.get e.ev.tag),
          byKey.set (pairKey e.ev.tag x) (k :: byKey.get (pairKey e.ev.tag x))⟩

def MaskState.init (n : Nat) : MaskState :=
  ⟨Array.replicate n false, PosMap.empty n, PosMap.empty n⟩

/-- **The dead positions**, by the fast pass. -/
def maskFast (es : List Entry) : Array Bool :=
  (es.zipIdx.foldl maskFastStep (MaskState.init es.length)).dead

def survivorsFast (es : List Entry) : List Entry :=
  let d := maskFast es
  (es.zipIdx.filter (fun p => !deadAt d p.2)).map Prod.fst

def cancelledLinesFast (es : List Entry) : List Nat :=
  let d := maskFast es
  (es.zipIdx.filter (fun p => deadAt d p.2)).map (fun p => p.1.line)

/-! ### The simulation -/

theorem deadAt_set (d : Array Bool) (i j : Nat) (h : i < d.size) :
    deadAt (d.setIfInBounds i true) j = (j == i || deadAt d j) := by
  unfold deadAt
  by_cases hij : i = j
  · subst hij; simp [Array.getElem?_setIfInBounds_self_of_lt h]
  · rw [Array.getElem?_setIfInBounds_ne hij]
    have : (j == i) = false := beq_false_of_ne (Ne.symm hij)
    simp [this]

theorem filter_dropWhile_cons (dd : Nat → Bool) : ∀ (L rest : List Nat) (j : Nat),
    L.dropWhile dd = j :: rest →
    L.filter (fun x => !dd x) = j :: rest.filter (fun x => !dd x) ∧ rest.Sublist L ∧ j ∈ L
  | [], _, _, h => by simp at h
  | a :: L, rest, j, h => by
    rw [List.dropWhile_cons] at h
    by_cases ha : dd a = true
    · rw [if_pos ha] at h
      obtain ⟨h1, h2, h3⟩ := filter_dropWhile_cons dd L rest j h
      refine ⟨?_, h2.cons a, List.mem_cons_of_mem _ h3⟩
      simp [ha, h1]
    · rw [if_neg ha] at h
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [ha]

theorem filter_dropWhile_nil (dd : Nat → Bool) : ∀ (L : List Nat),
    L.dropWhile dd = [] → L.filter (fun x => !dd x) = []
  | [], _ => rfl
  | a :: L, h => by
    rw [List.dropWhile_cons] at h
    by_cases ha : dd a = true
    · rw [if_pos ha] at h; simp [ha, filter_dropWhile_nil dd L h]
    · rw [if_neg ha] at h; cases h

/-- **`eraseP` is a filter by position** when positions are distinct and the first match is at `j`. -/
theorem eraseP_eq_filter_pos (pr : Entry → Bool) : ∀ (st : List (Entry × Nat)) (j : Nat) (t : List Nat),
    (st.map Prod.snd).Nodup → (st.filter (fun q => pr q.1)).map Prod.snd = j :: t →
    st.eraseP (fun q => pr q.1) = st.filter (fun q => q.2 != j)
  | [], _, _, _, h => by simp at h
  | q :: st, j, t, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hq : pr q.1 = true
    · rw [List.filter_cons, if_pos hq, List.map_cons, List.cons.injEq] at h
      rw [List.eraseP_cons, hq, cond_true, List.filter_cons]
      have hqj : (q.2 != j) = false := by simp [h.1]
      rw [hqj, if_neg (by simp)]
      symm; rw [List.filter_eq_self]
      intro a ha
      have : a.2 ≠ j := by
        intro hc; rw [← h.1] at hc
        exact hnd.1 (hc ▸ List.mem_map_of_mem ha)
      simpa using this
    · rw [List.filter_cons, if_neg hq] at h
      rw [List.eraseP_cons]
      simp only [hq, cond_false]
      have hjmem : j ∈ st.map Prod.snd := by
        have : j ∈ (st.filter (fun q => pr q.1)).map Prod.snd := by rw [h]; exact List.mem_cons_self
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 this
        exact List.mem_map_of_mem (List.mem_filter.1 ha).1
      have hqj : (q.2 != j) = true := by
        simp only [bne_iff_ne, ne_eq]
        intro hc; exact hnd.1 (hc ▸ hjmem)
      rw [List.filter_cons, if_pos hqj, eraseP_eq_filter_pos pr st j t hnd.2 h]

theorem eraseP_eq_self_of_filter_nil (pr : Entry → Bool) (st : List (Entry × Nat))
    (h : st.filter (fun q => pr q.1) = []) : st.eraseP (fun q => pr q.1) = st := by
  apply List.eraseP_of_forall_not
  intro a ha hp
  have : a ∈ st.filter (fun q => pr q.1) := List.mem_filter.2 ⟨ha, hp⟩
  rw [h] at this; cases this

/-- **The simulation invariant** after processing `P` (positions below `b`): the stack in file order is
`P`'s live entries; each tag's and each `(tag, id)`'s stack, dead positions removed, is the stack's
matching positions; every stored position is below `b`, and nothing at or above `b` is dead. -/
structure Inv (P : List (Entry × Nat)) (b : Nat) (s : MaskState) : Prop where
  stack : (P.foldl maskStepI []).reverse = P.filter (fun p => !deadAt s.dead p.2)
  tag   : ∀ g, (s.byTag.get g).filter (fun j => !deadAt s.dead j)
            = ((P.foldl maskStepI []).filter (fun q => «matches» g none q.1)).map Prod.snd
  key   : ∀ g x, (s.byKey.get (pairKey g x)).filter (fun j => !deadAt s.dead j)
            = ((P.foldl maskStepI []).filter (fun q => «matches» g (some x) q.1)).map Prod.snd
  tagLt : ∀ g, ∀ j ∈ s.byTag.get g, j < b
  keyLt : ∀ k, ∀ j ∈ s.byKey.get k, j < b
  above : ∀ j, b ≤ j → deadAt s.dead j = false
  posLt : ∀ p ∈ P, p.2 < b
  incr  : (P.map Prod.snd).Pairwise (· < ·)
  tagPos : 0 < s.byTag.buckets.size
  keyPos : 0 < s.byKey.buckets.size

theorem Inv.nodup {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s) :
    ((P.foldl maskStepI []).map Prod.snd).Nodup := by
  have h1 : ((P.foldl maskStepI []).reverse.map Prod.snd).Pairwise (· < ·) := by
    rw [h.stack]
    exact h.incr.sublist (List.filter_sublist.map Prod.snd)
  rw [List.map_reverse, List.pairwise_reverse] at h1
  exact h1.imp (fun hab => Nat.ne_of_gt hab)

/-- Killing `j` and `k` (both at or above nothing stored except `j`) filters `j` out of any list of
positions below `b ≤ k`. -/
theorem filter_kill (d : Array Bool) (j k b : Nat) (hj : j < d.size) (hk : k < d.size)
    (L : List Nat) (hL : ∀ x ∈ L, x < b) (hb : b ≤ k) :
    L.filter (fun x => !deadAt ((d.setIfInBounds j true).setIfInBounds k true) x)
      = (L.filter (fun x => !deadAt d x)).filter (fun x => x != j) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro x hx
  have hxk : (x == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hL x hx) hb))
  rw [deadAt_set _ _ _ (by simpa using hk), deadAt_set _ _ _ hj, hxk]
  cases deadAt d x <;> cases hxj : (x == j) <;> simp_all

theorem filter_kill1 (d : Array Bool) (k b : Nat) (hk : k < d.size)
    (L : List Nat) (hL : ∀ x ∈ L, x < b) (hb : b ≤ k) :
    L.filter (fun x => !deadAt (d.setIfInBounds k true) x) = L.filter (fun x => !deadAt d x) := by
  apply List.filter_congr
  intro x hx
  have hxk : (x == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hL x hx) hb))
  rw [deadAt_set _ _ _ hk, hxk]; rfl

theorem filter_pos_ne_comm (st : List (Entry × Nat)) (f : Entry × Nat → Bool) (j : Nat) :
    ((st.filter (fun q => q.2 != j)).filter f).map Prod.snd
      = ((st.filter f).map Prod.snd).filter (fun x => x != j) := by
  induction st with
  | nil => rfl
  | cons q st ih =>
    by_cases h1 : (q.2 != j) = true <;> by_cases h2 : f q = true <;>
      simp_all

theorem foldl_snoc_maskStepI (P : List (Entry × Nat)) (p : Entry × Nat) :
    (P ++ [p]).foldl maskStepI [] = maskStepI (P.foldl maskStepI []) p := by
  rw [List.foldl_append]; rfl

/-- Positions below `b` of the stack and of `P` are unaffected by dead marks at `k ≥ b`. -/
theorem stack_positions_lt {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s) :
    ∀ q ∈ P.foldl maskStepI [], q.2 < b := by
  intro q hq
  have : q ∈ (P.foldl maskStepI []).reverse := List.mem_reverse.2 hq
  rw [h.stack] at this
  exact h.posLt q ((List.mem_filter.1 this).1)

theorem Inv.step_undo_none {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (of_ : List Char) (hev : e.ev = .undo of_ none) (hb : b ≤ k)
    (hk : k < s.dead.size) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  obtain ⟨dead, byTag, byKey⟩ := s
  have hstep : maskStepI (P.foldl maskStepI []) (e, k)
      = (P.foldl maskStepI []).eraseP (fun q => «matches» of_ none q.1) := by
    simp only [maskStepI, hev]
  have hlast : ∀ d : Array Bool, deadAt d k = true → (P ++ [(e, k)]).filter (fun p => !deadAt d p.2)
      = P.filter (fun p => !deadAt d p.2) := by
    intro d hd; simp [List.filter_append, hd]
  simp only [maskFastStep, hev]
  split
  · rename_i hdrop
    have hnil := filter_dropWhile_nil (deadAt dead) _ hdrop
    have hst : (P.foldl maskStepI []).filter (fun q => «matches» of_ none q.1) = [] := by
      have := h.tag of_; simp only at this; rw [hnil] at this
      exact List.map_eq_nil_iff.1 this.symm
    have herase := eraseP_eq_self_of_filter_nil _ _ hst
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, hlast _ (by rw [deadAt_set _ _ _ hk]; simp), h.stack]
      symm; apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk]
      have : (p.2 == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]; rfl
    · intro g; simp only
      rw [PosMap.get_set _ _ _ _ h.tagPos, foldl_snoc_maskStepI, hstep, herase]
      by_cases hg : g = of_
      · subst hg; rw [if_pos rfl, hst]; rfl
      · rw [if_neg hg, filter_kill1 _ _ b hk _ (h.tagLt g) hb]; exact h.tag g
    · intro g x; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_kill1 _ _ b hk _ (h.keyLt _) hb]
      exact h.key g x
    · intro g j hj; simp only at hj
      rw [PosMap.get_set _ _ _ _ h.tagPos] at hj
      split at hj
      · cases hj
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g j hj) hb)
    · intro g j hj; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g j hj) hb)
    · intro j hj; simp only
      rw [deadAt_set _ _ _ hk]
      have : (j == k) = false := beq_false_of_ne (by omega)
      rw [this, h.above j (by omega)]; rfl
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb)
      · simp at hp; subst hp; exact Nat.lt_succ_self _
    · rw [List.map_append, List.pairwise_append]
      refine ⟨h.incr, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      simp at hc; subst hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact Nat.lt_of_lt_of_le (h.posLt p hp) hb
    · simp only; rw [PosMap.size_set]; exact h.tagPos
    · exact h.keyPos
  · rename_i j rest hdrop
    obtain ⟨hfl, hsub, hjmem⟩ := filter_dropWhile_cons (deadAt dead) _ rest j hdrop
    have hjb : j < b := h.tagLt of_ j hjmem
    -- `j` is below `b ≤ k < size`
    have hjd : j < dead.size := Nat.lt_of_lt_of_le hjb (Nat.le_of_lt (Nat.lt_of_le_of_lt hb hk))
    have htag := h.tag of_
    simp only at htag
    rw [hfl] at htag
    have herase := eraseP_eq_filter_pos (fun e => «matches» of_ none e) _ j _ h.nodup htag.symm
    have hk' : k < (dead.setIfInBounds j true).size := by simpa using hk
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, ← List.filter_reverse, h.stack, hlast _ (by rw [deadAt_set _ _ _ hk']; simp), List.filter_filter]
      apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have : (p.2 == k) = false :=
        beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]
      cases deadAt dead p.2 <;> cases hpj : (p.2 == j) <;> simp_all
    · intro g; simp only
      rw [PosMap.get_set _ _ _ _ h.tagPos, foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm]
      by_cases hg : g = of_
      · subst hg
        rw [if_pos rfl, filter_kill _ _ _ b hjd hk _ (fun x hx => h.tagLt g x (hsub.subset hx)) hb, ← htag]
        simp
      · rw [if_neg hg, filter_kill _ _ _ b hjd hk _ (h.tagLt g) hb, h.tag g]
    · intro g x; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm,
        filter_kill _ _ _ b hjd hk _ (h.keyLt _) hb, h.key g x]
    · intro g i hi; simp only at hi
      rw [PosMap.get_set _ _ _ _ h.tagPos] at hi
      split at hi
      · rename_i hg; subst hg
        exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt _ i (hsub.subset hi)) hb)
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g i hi) hb)
    · intro g i hi; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g i hi) hb)
    · intro i hi; simp only
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have h1 : (i == k) = false := beq_false_of_ne (by omega)
      have h2 : (i == j) = false := beq_false_of_ne (by omega)
      rw [h1, h2, h.above i (by omega)]; rfl
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb)
      · simp at hp; subst hp; exact Nat.lt_succ_self _
    · rw [List.map_append, List.pairwise_append]
      refine ⟨h.incr, List.pairwise_singleton _ _, ?_⟩
      intro a ha c hc
      simp at hc; subst hc
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
      exact Nat.lt_of_lt_of_le (h.posLt p hp) hb
    · simp only; rw [PosMap.size_set]; exact h.tagPos
    · exact h.keyPos

theorem Inv.posLt_snoc {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hb : b ≤ k) : ∀ p ∈ P ++ [(e, k)], p.2 < k + 1 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb)
  · simp at hp; subst hp; exact Nat.lt_succ_self _

theorem Inv.incr_snoc {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hb : b ≤ k) : ((P ++ [(e, k)]).map Prod.snd).Pairwise (· < ·) := by
  rw [List.map_append, List.pairwise_append]
  refine ⟨h.incr, List.pairwise_singleton _ _, ?_⟩
  intro a ha c hc
  simp at hc; subst hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  exact Nat.lt_of_lt_of_le (h.posLt p hp) hb

theorem Inv.step_undo_some {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (of_ x : List Char) (hev : e.ev = .undo of_ (some x)) (hb : b ≤ k)
    (hk : k < s.dead.size) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  obtain ⟨dead, byTag, byKey⟩ := s
  have hstep : maskStepI (P.foldl maskStepI []) (e, k)
      = (P.foldl maskStepI []).eraseP (fun q => «matches» of_ (some x) q.1) := by
    simp only [maskStepI, hev]
  have hlast : ∀ d : Array Bool, deadAt d k = true → (P ++ [(e, k)]).filter (fun p => !deadAt d p.2)
      = P.filter (fun p => !deadAt d p.2) := by
    intro d hd; simp [List.filter_append, hd]
  simp only [maskFastStep, hev]
  split
  · rename_i hdrop
    have hnil := filter_dropWhile_nil (deadAt dead) _ hdrop
    have hst : (P.foldl maskStepI []).filter (fun q => «matches» of_ (some x) q.1) = [] := by
      have := h.key of_ x; simp only at this; rw [hnil] at this
      exact List.map_eq_nil_iff.1 this.symm
    have herase := eraseP_eq_self_of_filter_nil _ _ hst
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.posLt_snoc e k hb, h.incr_snoc e k hb, h.tagPos, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, hlast _ (by rw [deadAt_set _ _ _ hk]; simp), h.stack]
      symm; apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk]
      have : (p.2 == k) = false := beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]; rfl
    · intro g; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_kill1 _ _ b hk _ (h.tagLt g) hb]
      exact h.tag g
    · intro g y; simp only
      rw [PosMap.get_set _ _ _ _ h.keyPos, foldl_snoc_maskStepI, hstep, herase]
      by_cases hgy : pairKey g y = pairKey of_ x
      · obtain ⟨rfl, rfl⟩ := pairKey_inj _ _ _ _ hgy
        rw [if_pos rfl, hst]; rfl
      · rw [if_neg hgy, filter_kill1 _ _ b hk _ (h.keyLt _) hb]; exact h.key g y
    · intro g j hj; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g j hj) hb)
    · intro g j hj; simp only at hj
      rw [PosMap.get_set _ _ _ _ h.keyPos] at hj
      split at hj
      · cases hj
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g j hj) hb)
    · intro j hj; simp only
      rw [deadAt_set _ _ _ hk]
      have : (j == k) = false := beq_false_of_ne (by omega)
      rw [this, h.above j (by omega)]; rfl
    · simp only; rw [PosMap.size_set]; exact h.keyPos
  · rename_i j rest hdrop
    obtain ⟨hfl, hsub, hjmem⟩ := filter_dropWhile_cons (deadAt dead) _ rest j hdrop
    have hjb : j < b := h.keyLt _ j hjmem
    have hjd : j < dead.size := Nat.lt_of_lt_of_le hjb (Nat.le_of_lt (Nat.lt_of_le_of_lt hb hk))
    have hkey := h.key of_ x
    simp only at hkey
    rw [hfl] at hkey
    have herase := eraseP_eq_filter_pos (fun e => «matches» of_ (some x) e) _ j _ h.nodup hkey.symm
    have hk' : k < (dead.setIfInBounds j true).size := by simpa using hk
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.posLt_snoc e k hb, h.incr_snoc e k hb, h.tagPos, ?_⟩, by simp⟩
    · simp only
      rw [foldl_snoc_maskStepI, hstep, herase, ← List.filter_reverse, h.stack,
        hlast _ (by rw [deadAt_set _ _ _ hk']; simp), List.filter_filter]
      apply List.filter_congr; intro p hp
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have : (p.2 == k) = false :=
        beq_false_of_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h.posLt p hp) hb))
      rw [this]
      cases deadAt dead p.2 <;> cases hpj : (p.2 == j) <;> simp_all
    · intro g; simp only
      rw [foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm,
        filter_kill _ _ _ b hjd hk _ (h.tagLt g) hb, h.tag g]
    · intro g y; simp only
      rw [PosMap.get_set _ _ _ _ h.keyPos, foldl_snoc_maskStepI, hstep, herase, filter_pos_ne_comm]
      by_cases hgy : pairKey g y = pairKey of_ x
      · obtain ⟨rfl, rfl⟩ := pairKey_inj _ _ _ _ hgy
        rw [if_pos rfl, filter_kill _ _ _ b hjd hk _ (fun i hi => h.keyLt _ i (hsub.subset hi)) hb, ← hkey]
        simp
      · rw [if_neg hgy, filter_kill _ _ _ b hjd hk _ (h.keyLt _) hb, h.key g y]
    · intro g i hi; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g i hi) hb)
    · intro g i hi; simp only at hi
      rw [PosMap.get_set _ _ _ _ h.keyPos] at hi
      split at hi
      · rename_i hg; subst hg
        exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt _ i (hsub.subset hi)) hb)
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt g i hi) hb)
    · intro i hi; simp only
      rw [deadAt_set _ _ _ hk', deadAt_set _ _ _ hjd]
      have h1 : (i == k) = false := beq_false_of_ne (by omega)
      have h2 : (i == j) = false := beq_false_of_ne (by omega)
      rw [h1, h2, h.above i (by omega)]; rfl
    · simp only; rw [PosMap.size_set]; exact h.keyPos

theorem maskFastStep_event (dead : Array Bool) (byTag byKey : PosMap) (e : Entry) (k : Nat)
    (hev : e.ev.isUndo = false) :
    maskFastStep ⟨dead, byTag, byKey⟩ (e, k) =
      ⟨dead, byTag.set e.ev.tag (k :: byTag.get e.ev.tag),
        match e.ev.primaryId with
        | none   => byKey
        | some x => byKey.set (pairKey e.ev.tag x) (k :: byKey.get (pairKey e.ev.tag x))⟩ := by
  simp only [maskFastStep]
  split
  · rename_i of_ hq; simp [hq, Event.isUndo] at hev
  · rename_i of_ x hq; simp [hq, Event.isUndo] at hev
  · cases e.ev.primaryId <;> rfl

theorem maskStepI_event (st : List (Entry × Nat)) (p : Entry × Nat) (hev : p.1.ev.isUndo = false) :
    maskStepI st p = p :: st := by
  unfold maskStepI
  split
  · rename_i of_ id hq; simp [hq, Event.isUndo] at hev
  · rfl

theorem Inv.step_event {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hev : e.ev.isUndo = false) (hb : b ≤ k) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  obtain ⟨dead, byTag, byKey⟩ := s
  have hst : (P ++ [(e, k)]).foldl maskStepI [] = (e, k) :: P.foldl maskStepI [] := by
    rw [foldl_snoc_maskStepI, maskStepI_event _ _ hev]
  have hka : deadAt dead k = false := h.above k hb
  rw [maskFastStep_event _ _ _ _ _ hev]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, h.posLt_snoc e k hb, h.incr_snoc e k hb, ?_, ?_⟩, rfl⟩
  · simp only
    rw [hst, List.reverse_cons, h.stack, List.filter_append]
    simp [hka]
  · intro g; simp only
    rw [PosMap.get_set _ _ _ _ h.tagPos, hst, List.filter_cons]
    by_cases hg : g = e.ev.tag
    · have hm : «matches» g none e = true := by simp [«matches», hg]
      rw [if_pos hg, if_pos hm, List.filter_cons, if_pos (by simp [hka]), List.map_cons]
      rw [hg]; exact congrArg _ (hg ▸ h.tag g)
    · have hm : «matches» g none e = false := by
        simp only [«matches», Option.all_none, Bool.and_true]
        exact beq_false_of_ne (Ne.symm hg)
      rw [if_neg hg, if_neg (by simp [hm])]
      exact h.tag g
  · intro g y; simp only
    rw [hst, List.filter_cons]
    cases hp : e.ev.primaryId with
    | none =>
      have hm : «matches» g (some y) e = false := by simp [«matches», hp]
      simp only [hm, Bool.false_eq_true, if_false]
      exact h.key g y
    | some x =>
      simp only
      rw [PosMap.get_set _ _ _ _ h.keyPos]
      by_cases hgy : pairKey g y = pairKey e.ev.tag x
      · obtain ⟨hg, hy⟩ := pairKey_inj _ _ _ _ hgy
        subst hg; subst hy
        have hm : «matches» e.ev.tag (some y) e = true := by simp [«matches», hp]
        rw [if_pos rfl, if_pos hm, List.filter_cons, if_pos (by simp [hka]), List.map_cons, h.key]
      · have hm : «matches» g (some y) e = false := by
          simp only [«matches», hp, Option.all_some, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
            Option.some.injEq]
          by_cases hg : e.ev.tag = g
          · right; intro hxy; exact hgy (by rw [hg, hxy])
          · left; exact hg
        rw [if_neg hgy, if_neg (by simp [hm])]
        exact h.key g y
  · intro g j hj; simp only at hj
    rw [PosMap.get_set _ _ _ _ h.tagPos] at hj
    split at hj
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt _ j hj) hb)
    · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.tagLt g j hj) hb)
  · intro q j hj; simp only at hj
    cases hp : e.ev.primaryId with
    | none => simp only [hp] at hj; exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt q j hj) hb)
    | some x =>
      simp only [hp] at hj
      rw [PosMap.get_set _ _ _ _ h.keyPos] at hj
      split at hj
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt _ j hj) hb)
      · exact Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le (h.keyLt q j hj) hb)
  · intro j hj; exact h.above j (by omega)
  · simp only; rw [PosMap.size_set]; exact h.tagPos
  · simp only
    cases e.ev.primaryId with
    | none => exact h.keyPos
    | some x => simp only; rw [PosMap.size_set]; exact h.keyPos

theorem Inv.step {P : List (Entry × Nat)} {b : Nat} {s : MaskState} (h : Inv P b s)
    (e : Entry) (k : Nat) (hb : b ≤ k) (hk : k < s.dead.size) :
    Inv (P ++ [(e, k)]) (k + 1) (maskFastStep s (e, k)) ∧
      (maskFastStep s (e, k)).dead.size = s.dead.size := by
  cases hev : e.ev with
  | undo of_ id =>
    cases id with
    | none => exact h.step_undo_none e k of_ hev hb hk
    | some x => exact h.step_undo_some e k of_ x hev hb hk
  | _ => exact h.step_event e k (by simp [hev, Event.isUndo]) hb

theorem Inv.init (n : Nat) : Inv [] 0 (MaskState.init n) where
  stack := rfl
  tag := by intro g; simp [MaskState.init, PosMap.get_empty]
  key := by intro g x; simp [MaskState.init, PosMap.get_empty]
  tagLt := by intro g j hj; simp [MaskState.init, PosMap.get_empty] at hj
  keyLt := by intro g j hj; simp [MaskState.init, PosMap.get_empty] at hj
  above := by intro j _; simp only [MaskState.init, deadAt, Array.getElem?_replicate]; split <;> rfl
  posLt := by simp
  incr := List.Pairwise.nil
  tagPos := by simp [MaskState.init, PosMap.empty]
  keyPos := by simp [MaskState.init, PosMap.empty]

/-- **The simulation** (`maskFast_inv`): after the fast pass over `es` from position `n`, the invariant
holds of everything processed. -/
theorem maskFast_inv : ∀ (es : List Entry) (n : Nat) (P : List (Entry × Nat)) (s : MaskState),
    Inv P n s → n + es.length ≤ s.dead.size →
    Inv (P ++ es.zipIdx n) (n + es.length) ((es.zipIdx n).foldl maskFastStep s)
  | [], n, P, s, h, _ => by simpa using h
  | e :: es, n, P, s, h, hsz => by
    rw [List.zipIdx_cons, List.foldl_cons]
    have hk : n < s.dead.size := by simp at hsz; omega
    obtain ⟨h1, hsize⟩ := h.step e n (Nat.le_refl n) hk
    have := maskFast_inv es (n + 1) _ _ h1 (by rw [hsize]; simp at hsz; omega)
    simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using this

/-- The fast pass's dead set is the complement of the stack's positions. -/
theorem maskFast_stack (es : List Entry) :
    (stackI es).reverse = es.zipIdx.filter (fun p => !deadAt (maskFast es) p.2) := by
  have h := maskFast_inv es 0 [] (MaskState.init es.length) (Inv.init _) (by simp [MaskState.init])
  simpa [stackI, maskFast] using h.stack

theorem cancelledAt_eq_deadAt (es : List Entry) (p : Entry × Nat) (hp : p ∈ es.zipIdx) :
    cancelledAt es p.2 = deadAt (maskFast es) p.2 := by
  unfold cancelledAt
  have hiff : (stackI es).any (fun q => q.2 == p.2) = !deadAt (maskFast es) p.2 := by
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨q, hq, hqe⟩
      have : q ∈ (stackI es).reverse := List.mem_reverse.2 hq
      rw [maskFast_stack] at this
      have := (List.mem_filter.1 this).2
      simp only [beq_iff_eq] at hqe
      rwa [← hqe]
    · intro halive
      refine ⟨p, ?_, by simp⟩
      have : p ∈ (stackI es).reverse := by rw [maskFast_stack]; exact List.mem_filter.2 ⟨hp, halive⟩
      exact List.mem_reverse.1 this
  rw [hiff]; simp

/-- **The survivors are the entries at the positions not cancelled**, in file order: what ties the
cancelled line set on the wire to `survivors`. -/
theorem survivors_are_the_uncancelled_entries (es : List Entry) :
    survivors es = (es.zipIdx.filter (fun p => !cancelledAt es p.2)).map Prod.fst := by
  unfold survivors
  rw [← stackI_map, ← List.map_reverse, maskFast_stack]
  congr 1
  apply List.filter_congr
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]

@[csimp] theorem survivors_eq_survivorsFast : @survivors = @survivorsFast := by
  funext es
  unfold survivorsFast
  rw [survivors_are_the_uncancelled_entries]
  congr 1
  apply List.filter_congr
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]

@[csimp] theorem cancelledLines_eq_cancelledLinesFast : @cancelledLines = @cancelledLinesFast := by
  funext es
  unfold cancelledLines cancelledLinesFast
  congr 1
  apply List.filter_congr
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]

/-- A line is in the cancelled set exactly when its entry does not survive: the cancelled lines and the
survivors partition the entries. -/
theorem cancelled_and_survivors_partition (es : List Entry) :
    (es.zipIdx.filter (fun p => cancelledAt es p.2)).length + (survivors es).length = es.length := by
  rw [survivors_are_the_uncancelled_entries, List.length_map]
  have := List.length_eq_countP_add_countP (fun p : Entry × Nat => cancelledAt es p.2) (l := es.zipIdx)
  rw [List.length_zipIdx, List.countP_eq_length_filter, List.countP_eq_length_filter] at this
  rw [this]
  congr 2
  apply List.filter_congr
  intro p _; simp

/-! ## Witnesses (C1)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 8 entries,
instants as `Nat` literals shared by every entry (the mask reads no time), no text parsed. -/

section Witnesses

/-- An entry at `line` whose instant and offset do not matter to the mask: 2026-09-07T06:05:00-05:00
(`Log.at0605`, `Log.cdt`). -/
def wEnt (line : Nat) (ev : Event) : Entry := ⟨line, Log.at0605, Log.cdt, ev⟩

def wDone (id : List Char) : Event :=
  .done id ⟨60, by decide⟩ ⟨60, by decide⟩ none [] ⟨3, by decide⟩ false

/-- **The mask ignores `isStateChange`** (inventory §2.2): a note is not a state change, and
`undo{of:"note"}` still cancels it. -/
theorem the_mask_ignores_isStateChange :
    Event.isStateChange (.note ['n']) = false ∧
    survivors [wEnt 1 (.note ['n']), wEnt 2 (.undo Log.Kind.note.tag none)] = [] := by
  decide

/-- The fork test `undo_mask_pairs_and_dangling`'s seven entries, lines 1–7: `done a`, `done b`,
`undo done a`, `undo done`, `undo done`, `note n`, `undo undo`. -/
def portedMask : List Entry :=
  [wEnt 1 (wDone ['a']), wEnt 2 (wDone ['b']), wEnt 3 (.undo Log.Kind.done.tag (some ['a'])),
   wEnt 4 (.undo Log.Kind.done.tag none), wEnt 5 (.undo Log.Kind.done.tag none), wEnt 6 (.note ['n']),
   wEnt 7 (.undo Log.Kind.undo.tag none)]

/-- **`undo_mask_pairs_and_dangling`, ported** (§7.1): `cancelled = [T,T,T,T,T,F,T]`, `dangling = [4, 6]`
(lines 5 and 7), `pairs() == 2`, and the one survivor is the note.  The cancelled line set the `log`
op answers is lines 1–5 and 7. -/
theorem undo_mask_pairs_and_dangling_ported :
    (List.range 7).map (cancelledAt portedMask) = [true, true, true, true, true, false, true] ∧
    (portedMask.filter (dangles portedMask)).map (·.line) = [5, 7] ∧
    ((List.range 7).countP (cancelledAt portedMask) - (portedMask.filter (dangles portedMask)).length) / 2 = 2 ∧
    (survivors portedMask).map (·.line) = [6] ∧
    cancelledLines portedMask = [1, 2, 3, 4, 5, 7] := by
  decide

/-- **Why `an_undo_of_an_undo_cancels_nothing_in_a_canonical_log` needs its hypothesis**: an `unknown`
event whose tag is `undo` (which no reader returns: `undo` is a known tag) is matched by
`undo{of:"undo"}`, exactly as the fork's `ev.name() == of` would match it. -/
theorem an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo :
    ∃ (es : List Entry) (u : Entry), u.ev = .undo Log.Kind.undo.tag none ∧
      survivors (es ++ [u]) ≠ survivors es :=
  ⟨[wEnt 1 (.unknown Log.Kind.undo.tag [])], wEnt 2 (.undo Log.Kind.undo.tag none), rfl, by decide⟩

/-- **An undo with an id passes over a later event of another id** and cancels the latest of its
own; an undo without one takes the latest of the tag. -/
theorem an_undo_with_an_id_passes_over_other_ids :
    (survivors [wEnt 1 (wDone ['a']), wEnt 2 (wDone ['b']), wEnt 3 (.undo Log.Kind.done.tag (some ['a']))]).map (·.line) = [2] ∧
    (survivors [wEnt 1 (wDone ['a']), wEnt 2 (wDone ['b']), wEnt 3 (.undo Log.Kind.done.tag none)]).map (·.line) = [1] := by
  decide

end Witnesses

/-! ## C2: the day index (§6.2) -/

section DayIndex

theorem instant_le_trans {a b c : Cal.Instant} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  rw [Cal.Instant.le_iff] at *; omega

theorem instant_le_refl (a : Cal.Instant) : a ≤ a := by
  rw [Cal.Instant.le_iff]; omega

theorem instant_le_of_not_le {a b : Cal.Instant} (h : ¬ a ≤ b) : b ≤ a := by
  rcases Cal.Instant.le_total a b with h' | h'
  · exact absurd h' h
  · exact h'

theorem instant_le_of_lt {a b : Cal.Instant} (h : a < b) : a ≤ b := by
  rw [Cal.Instant.le_iff]; rw [Cal.Instant.lt_iff] at h; omega

theorem instant_not_le_of_lt {a b : Cal.Instant} (h : a < b) : ¬ b ≤ a := by
  rw [Cal.Instant.le_iff]; rw [Cal.Instant.lt_iff] at h; omega

/-! ### `wakes.sort()` -/

/-- Insert into a list ascending in chrono's order, before the first element it is at or before. -/
def insertWake (w : Cal.Instant) : List Cal.Instant → List Cal.Instant
  | [] => [w]
  | x :: xs => if w ≤ x then w :: x :: xs else x :: insertWake w xs

/-- **`wakes.sort()`** in chrono's order (`DateTime`'s `Ord`, the UTC `(sec, ns)` pair): the
specification is an insertion sort, which `decide` evaluates; the code is core's merge sort
(`sortWakes_eq_sortWakesFast`). -/
def sortWakes (ws : List Cal.Instant) : List Cal.Instant := ws.foldr insertWake []

def sortWakesFast (ws : List Cal.Instant) : List Cal.Instant := ws.mergeSort (fun a b => decide (a ≤ b))

theorem insertWake_perm (w : Cal.Instant) : ∀ (l : List Cal.Instant), (insertWake w l).Perm (w :: l)
  | [] => List.Perm.refl _
  | x :: xs => by
    unfold insertWake
    split
    · exact List.Perm.refl _
    · exact ((insertWake_perm w xs).cons x).trans (List.Perm.swap w x xs)

theorem sortWakes_perm : ∀ (ws : List Cal.Instant), (sortWakes ws).Perm ws
  | [] => List.Perm.refl _
  | w :: ws => (insertWake_perm w _).trans ((sortWakes_perm ws).cons w)

theorem insertWake_sorted (w : Cal.Instant) : ∀ (l : List Cal.Instant), l.Pairwise (· ≤ ·) →
    (insertWake w l).Pairwise (· ≤ ·)
  | [], _ => List.pairwise_singleton _ _
  | x :: xs, h => by
    unfold insertWake
    split
    · rename_i hwx
      refine List.Pairwise.cons ?_ h
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hwx
      · exact instant_le_trans hwx (List.rel_of_pairwise_cons h hy)
    · rename_i hwx
      refine List.Pairwise.cons ?_ (insertWake_sorted w xs h.of_cons)
      intro y hy
      rcases List.mem_cons.1 ((insertWake_perm w xs).mem_iff.1 hy) with rfl | hy
      · exact instant_le_of_not_le hwx
      · exact List.rel_of_pairwise_cons h hy

theorem sortWakes_sorted : ∀ (ws : List Cal.Instant), (sortWakes ws).Pairwise (· ≤ ·)
  | [] => List.Pairwise.nil
  | w :: ws => insertWake_sorted w _ (sortWakes_sorted ws)

/-- **A list sorted in chrono's order is determined by its elements**: two sorted permutations of
one list are equal, because the order is antisymmetric on instants. -/
theorem eq_of_perm_of_sorted : ∀ {l₁ l₂ : List Cal.Instant}, l₁.Perm l₂ →
    l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) → l₁ = l₂
  | [], _, h, _, _ => h.nil_eq
  | _ :: _, [], h, _, _ => h.eq_nil
  | a :: t₁, b :: t₂, h, h₁, h₂ => by
    have hab : a ≤ b := by
      rcases List.mem_cons.1 (h.mem_iff.2 List.mem_cons_self) with hb | hb
      · rw [hb]; exact instant_le_refl _
      · exact List.rel_of_pairwise_cons h₁ hb
    have hba : b ≤ a := by
      rcases List.mem_cons.1 (h.mem_iff.1 List.mem_cons_self) with ha | ha
      · rw [ha]; exact instant_le_refl _
      · exact List.rel_of_pairwise_cons h₂ ha
    have := Cal.Instant.le_antisymm hab hba
    subst this
    rw [eq_of_perm_of_sorted (List.perm_cons a |>.1 h) h₁.of_cons h₂.of_cons]

@[csimp] theorem sortWakes_eq_sortWakesFast : @sortWakes = @sortWakesFast := by
  funext ws
  apply eq_of_perm_of_sorted ((sortWakes_perm ws).trans (List.mergeSort_perm ws _).symm)
    (sortWakes_sorted ws)
  have := List.pairwise_mergeSort (le := fun a b : Cal.Instant => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact instant_le_trans hab hbc)
    (fun a b => by rcases Cal.Instant.le_total a b with h | h <;> simp [h]) ws
  exact this.imp (fun h => by simpa using h)

/-- Two lists each sorted, every element of the first before every element of the second, sort as
their concatenation. -/
theorem sortWakes_append_of_later (ws₁ ws₂ : List Cal.Instant) (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a < b) :
    sortWakes (ws₁ ++ ws₂) = sortWakes ws₁ ++ sortWakes ws₂ := by
  apply eq_of_perm_of_sorted
  · exact (sortWakes_perm _).trans ((sortWakes_perm ws₁).append (sortWakes_perm ws₂)).symm
  · exact sortWakes_sorted _
  · rw [List.pairwise_append]
    refine ⟨sortWakes_sorted _, sortWakes_sorted _, fun a ha b hb => ?_⟩
    exact instant_le_of_lt (h a ((sortWakes_perm ws₁).mem_iff.1 ha) b ((sortWakes_perm ws₂).mem_iff.1 hb))

/-! ### `dedup_by` on the date: the first of each run of one date -/

/-- One step of fork `dedup_by(|later, kept| later's date == kept's date)`: the state is the last
kept wake and the kept wakes, most recent first.  A wake whose local date in `z` is the last kept
wake's is dropped; any other is kept. -/
def keptStep (z : Cal.Tz) (acc : Option Cal.Instant × List Cal.Instant) (w : Cal.Instant) :
    Option Cal.Instant × List Cal.Instant :=
  match acc.1 with
  | some k => if Cal.localDate z w = Cal.localDate z k then acc else (some w, w :: acc.2)
  | none => (some w, w :: acc.2)

/-- The dedup over `ws` in the order given, continuing a run whose last kept wake is `last`. -/
def dedupFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant) : List Cal.Instant :=
  (ws.foldl (keptStep z) (last, [])).2.reverse

/-- **Continue a day index**: sort `ws`, then dedup it continuing the run whose last kept wake is
`last` (§6.2's `keptFrom`, what `keptWakes_append_of_later` needs). -/
def keptFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant) : List Cal.Instant :=
  dedupFrom z last (sortWakes ws)

/-- **Fork `DayIndex::new`**: the wakes sorted in chrono's order, then **consecutive** dedup on the
local date in `z`, keeping the first of each run.  Not "the earliest wake per date": the two differ
when local dates are not monotone in instant order (a fold at midnight). -/
def keptWakes (z : Cal.Tz) (ws : List Cal.Instant) : List Cal.Instant := keptFrom z none ws

theorem foldl_keptStep_acc (z : Cal.Tz) : ∀ (xs : List Cal.Instant) (l : Option Cal.Instant)
    (acc : List Cal.Instant),
    xs.foldl (keptStep z) (l, acc)
      = ((xs.foldl (keptStep z) (l, [])).1, (xs.foldl (keptStep z) (l, [])).2 ++ acc)
  | [], _, _ => rfl
  | x :: xs, l, acc => by
    rw [List.foldl_cons, List.foldl_cons]
    cases l with
    | none =>
      simp only [keptStep]
      rw [foldl_keptStep_acc z xs (some x) (x :: acc), foldl_keptStep_acc z xs (some x) [x]]
      simp
    | some k =>
      simp only [keptStep]
      split
      · rw [foldl_keptStep_acc z xs (some k) acc]
      · rw [foldl_keptStep_acc z xs (some x) (x :: acc), foldl_keptStep_acc z xs (some x) [x]]
        simp

theorem foldl_keptStep_head (z : Cal.Tz) (l : Option Cal.Instant) : ∀ (xs : List Cal.Instant)
    (s : Option Cal.Instant × List Cal.Instant), s.1 = s.2.head?.or l →
    (xs.foldl (keptStep z) s).1 = (xs.foldl (keptStep z) s).2.head?.or l
  | [], _, h => h
  | x :: xs, s, h => by
    rw [List.foldl_cons]
    apply foldl_keptStep_head z l xs
    obtain ⟨s1, s2⟩ := s
    unfold keptStep
    cases s1 with
    | none => simp
    | some k =>
      simp only
      split
      · exact h
      · simp

theorem keptWakes_last (z : Cal.Tz) (ws : List Cal.Instant) :
    ((sortWakes ws).foldl (keptStep z) (none, [])).1 = (keptWakes z ws).getLast? := by
  rw [foldl_keptStep_head z none _ _ rfl]
  simp [keptWakes, keptFrom, dedupFrom]

/-- `keptWakes_append_of_later` (Goals, §15, C2), **restated in chrono's order** (carried note 1: the
fork sorts `DateTime`s, whose order is not `Instant.nanos`'s at a leap second): when every wake of
`ws₁` is before every wake of `ws₂`, the day index of both is `ws₁`'s continued by `ws₂`'s. -/
theorem keptWakes_append_of_later (z : Cal.Tz) (ws₁ ws₂ : List Cal.Instant)
    (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a < b) :
    keptWakes z (ws₁ ++ ws₂) = keptWakes z ws₁ ++ keptFrom z (keptWakes z ws₁).getLast? ws₂ := by
  unfold keptWakes keptFrom dedupFrom
  rw [sortWakes_append_of_later ws₁ ws₂ h, List.foldl_append]
  rw [foldl_keptStep_acc z (sortWakes ws₂)]
  simp only [List.reverse_append]
  have := keptWakes_last z ws₁
  unfold keptWakes keptFrom dedupFrom at this
  rw [this]

theorem mem_foldl_keptStep (z : Cal.Tz) : ∀ (xs : List Cal.Instant) (s : Option Cal.Instant × List Cal.Instant)
    (x : Cal.Instant), x ∈ (xs.foldl (keptStep z) s).2 → x ∈ s.2 ∨ x ∈ xs
  | [], _, _, h => Or.inl h
  | y :: xs, s, x, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_keptStep z xs _ x h with h | h
    · obtain ⟨s1, s2⟩ := s
      unfold keptStep at h
      cases s1 with
      | none =>
        rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr List.mem_cons_self
        · exact Or.inl h
      | some k =>
        simp only at h
        split at h
        · exact Or.inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Every wake the index keeps was one of the wakes. -/
theorem mem_of_mem_keptFrom (z : Cal.Tz) (last : Option Cal.Instant) (ws : List Cal.Instant)
    (x : Cal.Instant) (h : x ∈ keptFrom z last ws) : x ∈ ws := by
  unfold keptFrom dedupFrom at h
  rw [List.mem_reverse] at h
  rcases mem_foldl_keptStep z _ _ x h with h | h
  · simp at h
  · exact (sortWakes_perm ws).mem_iff.1 h

theorem foldl_keptStep_sublist (z : Cal.Tz) : ∀ (xs : List Cal.Instant) (l : Option Cal.Instant),
    (xs.foldl (keptStep z) (l, [])).2.reverse.Sublist xs
  | [], _ => List.Sublist.slnil
  | x :: xs, l => by
    rw [List.foldl_cons]
    cases l with
    | none =>
      simp only [keptStep]
      rw [foldl_keptStep_acc z xs (some x) [x]]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
      exact (foldl_keptStep_sublist z xs (some x)).cons_cons x
    | some k =>
      simp only [keptStep]
      split
      · exact (foldl_keptStep_sublist z xs (some k)).cons x
      · rw [foldl_keptStep_acc z xs (some x) [x]]
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append]
        exact (foldl_keptStep_sublist z xs (some x)).cons_cons x

/-- **The kept wakes are in chrono's order.** -/
theorem keptWakes_sorted (z : Cal.Tz) (ws : List Cal.Instant) : (keptWakes z ws).Pairwise (· ≤ ·) :=
  (sortWakes_sorted ws).sublist (foldl_keptStep_sublist z _ none)

/-! ### `last_wake_before` and `day_of` -/

/-- **Fork `DayIndex::last_wake_before`**: the last wake at or before `t` in chrono's order.  The fork
reads it with `partition_point` over its sorted vector; over a sorted list that is the last element
`≤ t` in list order, which is this fold (`lastWakeLeArr_eq_lastWakeLe`, the compiled bisection). -/
def lastWakeLe (kw : List Cal.Instant) (t : Cal.Instant) : Option Cal.Instant :=
  kw.foldl (fun acc w => if w ≤ t then some w else acc) none

/-- **Fork `DayIndex::day_of`**: the local date in `z` of the last wake at or before `t` when
`t.signed_duration_since(w) < Duration::hours(24)`, otherwise `t`'s own local date.  chrono's
duration is `Cal.durationBetween` (its leap-second rule), and a `TimeDelta` below 24 hours has fewer
than 86,400 whole seconds, whatever its nanoseconds. -/
def dayOf (z : Cal.Tz) (kw : List Cal.Instant) (t : Cal.Instant) : Nat :=
  match lastWakeLe kw t with
  | some w => if (Cal.durationBetween w t).1 < 86400 then Cal.localDate z w else Cal.localDate z t
  | none => Cal.localDate z t

theorem foldl_lastWake_or (t : Cal.Instant) : ∀ (kw : List Cal.Instant) (acc : Option Cal.Instant),
    kw.foldl (fun acc w => if w ≤ t then some w else acc) acc = (lastWakeLe kw t).or acc
  | [], acc => by simp [lastWakeLe]
  | w :: kw, acc => by
    unfold lastWakeLe
    rw [List.foldl_cons, List.foldl_cons, foldl_lastWake_or t kw, foldl_lastWake_or t kw]
    by_cases h : w ≤ t <;> simp [h]

/-- The wake found is at or before `t`, and one of the wakes. -/
theorem lastWakeLe_cons (w : Cal.Instant) (kw : List Cal.Instant) (t : Cal.Instant) :
    lastWakeLe (w :: kw) t = (lastWakeLe kw t).or (if w ≤ t then some w else none) := by
  unfold lastWakeLe
  rw [List.foldl_cons, foldl_lastWake_or]
  rfl

theorem lastWakeLe_le : ∀ (kw : List Cal.Instant) (t w : Cal.Instant), lastWakeLe kw t = some w →
    w ≤ t ∧ w ∈ kw
  | [], _, _, h => by simp [lastWakeLe] at h
  | x :: kw, t, w, h => by
    rw [lastWakeLe_cons] at h
    cases hl : lastWakeLe kw t with
    | some y =>
      rw [hl] at h
      simp only [Option.some_or, Option.some.injEq] at h
      subst h
      exact ⟨(lastWakeLe_le kw t y hl).1, List.mem_cons_of_mem _ (lastWakeLe_le kw t y hl).2⟩
    | none =>
      rw [hl] at h
      by_cases hx : x ≤ t
      · simp only [hx, if_true, Option.none_or, Option.some.injEq] at h
        subst h
        exact ⟨hx, List.mem_cons_self⟩
      · simp [hx] at h

/-- A later list of wakes, every one after `t`, does not move `t`'s last wake. -/
theorem lastWakeLe_append_of_later (l₁ l₂ : List Cal.Instant) (t : Cal.Instant)
    (h : ∀ b ∈ l₂, t < b) : lastWakeLe (l₁ ++ l₂) t = lastWakeLe l₁ t := by
  unfold lastWakeLe
  rw [List.foldl_append, foldl_lastWake_or]
  have : lastWakeLe l₂ t = none := by
    cases hl : lastWakeLe l₂ t with
    | none => rfl
    | some w =>
      obtain ⟨hle, hmem⟩ := lastWakeLe_le l₂ t w hl
      exact absurd hle (instant_not_le_of_lt (h w hmem))
  rw [this]
  rfl

/-- `dayOf_is_the_wake_date_within_a_day` (Goals, §15, C2), **restated in chrono's order**: the
hypothesis is chrono's `signed_duration_since(w) < 24 h`, not `t.nanos < w.nanos + 86400·10^9`
(`dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted`). -/
theorem dayOf_is_the_wake_date_within_a_day (z : Cal.Tz) (kw : List Cal.Instant) (t w : Cal.Instant)
    (hw : lastWakeLe kw t = some w) (h24 : (Cal.durationBetween w t).1 < 86400) :
    dayOf z kw t = Cal.localDate z w := by
  simp [dayOf, hw, h24]

theorem dayOf_without_a_recent_wake_is_the_local_date (z : Cal.Tz) (kw : List Cal.Instant)
    (t : Cal.Instant) (h : ∀ w, lastWakeLe kw t = some w → 86400 ≤ (Cal.durationBetween w t).1) :
    dayOf z kw t = Cal.localDate z t := by
  unfold dayOf
  cases hw : lastWakeLe kw t with
  | none => rfl
  | some w => simp [Int.not_lt.2 (h w hw)]

/-- `a_wake_day_is_shorter_than_a_day` (Goals, §15, C2), **restated in chrono's order**: an instant
attributed to its wake's date, which is not its own, is under 24 hours of chrono's duration after
that wake. -/
theorem a_wake_day_is_shorter_than_a_day (z : Cal.Tz) (ws : List Cal.Instant) (t w : Cal.Instant)
    (hw : lastWakeLe (keptWakes z ws) t = some w)
    (hd : dayOf z (keptWakes z ws) t = Cal.localDate z w)
    (hne : Cal.localDate z t ≠ Cal.localDate z w) :
    (Cal.durationBetween w t).1 < 86400 := by
  unfold dayOf at hd
  rw [hw] at hd
  simp only at hd
  split at hd
  · assumption
  · exact absurd hd hne

/-- **The locality W2 needs** (§6.2, §9.5): wakes appended later, all after `t`, do not change `t`'s
day. -/
theorem dayOf_agrees_below_a_later_wake (z : Cal.Tz) (ws₁ ws₂ : List Cal.Instant) (t : Cal.Instant)
    (h : ∀ a ∈ ws₁, ∀ b ∈ ws₂, a < b) (ht : ∀ b ∈ ws₂, t < b) :
    dayOf z (keptWakes z (ws₁ ++ ws₂)) t = dayOf z (keptWakes z ws₁) t := by
  rw [keptWakes_append_of_later z ws₁ ws₂ h]
  unfold dayOf
  rw [lastWakeLe_append_of_later _ _ t (fun b hb => ht b (mem_of_mem_keptFrom z _ ws₂ b hb))]

/-- **An instant off its own date belongs to a wake under a day before it**: whenever `dayOf` is not
`t`'s local date, there is a kept wake at or before `t`, of that date, under 24 hours of chrono's
duration earlier.  What "a day is never longer than 24 hours" says, for every index. -/
theorem an_instant_off_its_own_date_is_within_a_day_of_its_wake (z : Cal.Tz) (kw : List Cal.Instant)
    (t : Cal.Instant) (h : dayOf z kw t ≠ Cal.localDate z t) :
    ∃ w, lastWakeLe kw t = some w ∧ w ∈ kw ∧ w ≤ t ∧ dayOf z kw t = Cal.localDate z w ∧
      (Cal.durationBetween w t).1 < 86400 := by
  unfold dayOf at *
  cases hw : lastWakeLe kw t with
  | none => rw [hw] at h; exact absurd rfl h
  | some w =>
    rw [hw] at h
    simp only at h ⊢
    obtain ⟨hle, hmem⟩ := lastWakeLe_le kw t w hw
    by_cases h24 : (Cal.durationBetween w t).1 < 86400
    · exact ⟨w, rfl, hmem, hle, by simp [h24], h24⟩
    · simp [h24] at h

/-! ### The index of a log, and quirk Q6(a): two "first wake" rules -/

def isWake (e : Entry) : Bool :=
  match e.ev with
  | .wake _ _ => true
  | _ => false

/-- The survivors' wake instants, in file order (fork `refs.filter(Wake).map(t)`). -/
def wakeInstants (sv : List Entry) : List Cal.Instant := (sv.filter isWake).map (fun e => e.t.val)

/-- **The day index of a log**: the kept wakes of its surviving wakes (fork `replay_lines`'
`DayIndex::new(tz, refs…)`). -/
def dayIndexOf (z : Cal.Tz) (es : List Entry) : List Cal.Instant := keptWakes z (wakeInstants (survivors es))

/-- Fork `DayIndex::wake_of`: the first kept wake whose local date is `d`.  Not on the wire (§6.2: no
caller outside `log.rs`); it states quirk Q6(a). -/
def keptWakeOn (z : Cal.Tz) (kw : List Cal.Instant) (d : Nat) : Option Cal.Instant :=
  kw.find? (fun w => Cal.localDate z w == d)

/-- **The first logged wake of day `d`**: the first entry **in file order** that is a wake attributed to
`d` (fork `DayReplay.wake`'s `if d.wake.is_none()` and `slept_by_day`'s `or_insert`; C5 reads it). -/
def firstLoggedWakeOn (z : Cal.Tz) (kw : List Cal.Instant) (es : List Entry) (d : Nat) : Option Entry :=
  es.find? (fun e => isWake e && dayOf z kw e.t.val == d)

theorem dedupFrom_append (z : Cal.Tz) (l : Option Cal.Instant) (V U : List Cal.Instant) :
    dedupFrom z l (V ++ U) = dedupFrom z l V ++ dedupFrom z (V.foldl (keptStep z) (l, [])).1 U := by
  unfold dedupFrom
  rw [List.foldl_append]
  have : V.foldl (keptStep z) (l, []) = ((V.foldl (keptStep z) (l, [])).1, (V.foldl (keptStep z) (l, [])).2) := rfl
  rw [this, foldl_keptStep_acc z U]
  simp

theorem dedupFrom_last (z : Cal.Tz) (V : List Cal.Instant) :
    (V.foldl (keptStep z) (none, [])).1 = (dedupFrom z none V).getLast? := by
  rw [foldl_keptStep_head z none V _ rfl]
  simp [dedupFrom]

theorem dedupFrom_single (z : Cal.Tz) (L : Option Cal.Instant) (x : Cal.Instant) :
    dedupFrom z L [x]
      = (match L with | some k => if Cal.localDate z x = Cal.localDate z k then [] else [x] | none => [x]) := by
  cases L with
  | none => rfl
  | some k =>
    simp only [dedupFrom, List.foldl_cons, List.foldl_nil, keptStep]
    split <;> rfl

theorem lastWakeLe_snoc (l : List Cal.Instant) (x t : Cal.Instant) :
    lastWakeLe (l ++ [x]) t = if x ≤ t then some x else lastWakeLe l t := by
  unfold lastWakeLe
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem lastWakeLe_of_all_le (t : Cal.Instant) : ∀ (l : List Cal.Instant), (∀ y ∈ l, y ≤ t) →
    lastWakeLe l t = l.getLast?
  | [], _ => rfl
  | x :: xs, h => by
    rw [lastWakeLe_cons, lastWakeLe_of_all_le t xs (fun y hy => h y (List.mem_cons_of_mem _ hy)),
      if_pos (h x List.mem_cons_self), List.getLast?_cons]
    cases xs.getLast? <;> rfl

/-- **In a sorted list of wakes, each wake's last kept wake is of its own date**: the run a wake
belongs to began at a kept wake of its date, and a later kept wake at or before it equals it. -/
theorem lastWakeLe_dedup_same_date (z : Cal.Tz) : ∀ (R : List Cal.Instant), R.reverse.Pairwise (· ≤ ·) →
    ∀ w ∈ R.reverse, ∃ k, lastWakeLe (dedupFrom z none R.reverse) w = some k ∧
      Cal.localDate z k = Cal.localDate z w
  | [], _, w, hw => by simp at hw
  | x :: R, hs, w, hw => by
    simp only [List.reverse_cons] at hs hw ⊢
    obtain ⟨hsV, -, hVx⟩ := List.pairwise_append.1 hs
    have hle : ∀ v ∈ R.reverse, v ≤ x := fun v hv => hVx v hv x List.mem_cons_self
    have hK : ∀ y ∈ dedupFrom z none R.reverse, y ≤ x := fun y hy =>
      hle y ((foldl_keptStep_sublist z R.reverse none).subset hy)
    rw [dedupFrom_append, dedupFrom_last, dedupFrom_single]
    rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨k, hk, hkd⟩ := lastWakeLe_dedup_same_date z R hsV w hw
      have hkeep : ∀ (tail : List Cal.Instant), (tail = [] ∨ tail = [x]) →
          ∃ k, lastWakeLe (dedupFrom z none R.reverse ++ tail) w = some k ∧
            Cal.localDate z k = Cal.localDate z w := by
        intro tail ht
        rcases ht with rfl | rfl
        · exact ⟨k, by rw [List.append_nil]; exact hk, hkd⟩
        · rw [lastWakeLe_snoc]
          by_cases hxw : x ≤ w
          · rw [if_pos hxw]
            exact ⟨x, rfl, by rw [Cal.Instant.le_antisymm hxw (hle w hw)]⟩
          · rw [if_neg hxw]; exact ⟨k, hk, hkd⟩
      apply hkeep
      split
      · split
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact Or.inr rfl
    · simp only [List.mem_singleton] at hw
      subst hw
      cases hL : (dedupFrom z none R.reverse).getLast? with
      | none => exact ⟨w, by rw [lastWakeLe_snoc, if_pos (instant_le_refl w)], rfl⟩
      | some k =>
        simp only
        split
        · rename_i hdate
          refine ⟨k, ?_, hdate.symm⟩
          rw [List.append_nil, lastWakeLe_of_all_le w _ hK, hL]
        · exact ⟨w, by rw [lastWakeLe_snoc, if_pos (instant_le_refl w)], rfl⟩

/-- **A logged wake belongs to its own date** when the wakes are in chrono's order. -/
theorem a_wake_is_on_its_own_date (z : Cal.Tz) (W : List Cal.Instant) (hs : W.Pairwise (· ≤ ·))
    (w : Cal.Instant) (hw : w ∈ W) : dayOf z (keptWakes z W) w = Cal.localDate z w := by
  have hsort : sortWakes W = W := eq_of_perm_of_sorted (sortWakes_perm W) (sortWakes_sorted W) hs
  have := lastWakeLe_dedup_same_date z W.reverse (by rw [List.reverse_reverse]; exact hs) w
    (by rw [List.reverse_reverse]; exact hw)
  rw [List.reverse_reverse] at this
  obtain ⟨k, hk, hkd⟩ := this
  unfold dayOf keptWakes keptFrom
  rw [hsort, hk]
  simp only
  split <;> simp [hkd]

theorem find?_congr_mem {α : Type} : ∀ (l : List α) (p q : α → Bool), (∀ a ∈ l, p a = q a) →
    l.find? p = l.find? q
  | [], _, _, _ => rfl
  | x :: xs, p, q, h => by
    rw [List.find?_cons, List.find?_cons, h x List.mem_cons_self,
      find?_congr_mem xs p q (fun a ha => h a (List.mem_cons_of_mem _ ha))]

theorem find?_dedupFrom (z : Cal.Tz) (d : Nat) : ∀ (W : List Cal.Instant) (last : Option Cal.Instant),
    (∀ k, last = some k → Cal.localDate z k ≠ d) →
    (dedupFrom z last W).find? (fun w => Cal.localDate z w == d) = W.find? (fun w => Cal.localDate z w == d)
  | [], _, _ => rfl
  | x :: xs, last, h => by
    have hcons : dedupFrom z last (x :: xs)
        = dedupFrom z last [x] ++ dedupFrom z ((keptStep z (last, []) x).1) xs := by
      rw [show x :: xs = [x] ++ xs from rfl, dedupFrom_append]; rfl
    rw [hcons, dedupFrom_single, List.find?_append]
    cases last with
    | none =>
      simp only [keptStep]
      by_cases hx : Cal.localDate z x = d
      · simp [hx]
      · have ih := find?_dedupFrom z d xs (some x) (fun k hk => by cases hk; exact hx)
        simp [hx, ih]
    | some k =>
      simp only [keptStep]
      by_cases hxk : Cal.localDate z x = Cal.localDate z k
      · have hx : Cal.localDate z x ≠ d := by rw [hxk]; exact h k rfl
        have ih := find?_dedupFrom z d xs (some k) h
        rw [if_pos hxk, if_pos hxk, List.find?_nil, Option.none_or, ih, List.find?_cons,
          beq_eq_false_iff_ne.2 hx]
      · rw [if_neg hxk, if_neg hxk, List.find?_cons, List.find?_nil, List.find?_cons]
        by_cases hx : Cal.localDate z x = d
        · rw [beq_iff_eq.2 hx]; rfl
        · have ih := find?_dedupFrom z d xs (some x) (fun k hk => by cases hk; exact hx)
          rw [beq_eq_false_iff_ne.2 hx]
          simpa using ih

/-- **Quirk Q6(a)'s other direction: in-order wakes make the two rules one.**  When the surviving
wakes are logged in chrono's order, the first kept wake of a date is the first logged wake of that
day; the rules differ only on wakes appended out of time order
(`the_kept_wake_is_not_the_first_logged_wake`). -/
theorem the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order (z : Cal.Tz)
    (es : List Entry) (d : Nat) (hs : (wakeInstants (survivors es)).Pairwise (· ≤ ·)) :
    keptWakeOn z (dayIndexOf z es) d
      = (firstLoggedWakeOn z (dayIndexOf z es) (survivors es) d).map (fun e => e.t.val) := by
  have hsort : sortWakes (wakeInstants (survivors es)) = wakeInstants (survivors es) :=
    eq_of_perm_of_sorted (sortWakes_perm _) (sortWakes_sorted _) hs
  unfold keptWakeOn firstLoggedWakeOn
  have hl : (dayIndexOf z es).find? (fun w => Cal.localDate z w == d)
      = (wakeInstants (survivors es)).find? (fun w => Cal.localDate z w == d) := by
    unfold dayIndexOf keptWakes keptFrom
    rw [hsort]
    exact find?_dedupFrom z d _ none (fun k hk => by cases hk)
  rw [hl]
  have hr : (wakeInstants (survivors es)).find? (fun w => Cal.localDate z w == d)
      = (wakeInstants (survivors es)).find? (fun w => dayOf z (dayIndexOf z es) w == d) := by
    apply find?_congr_mem
    intro w hw
    rw [dayIndexOf, a_wake_is_on_its_own_date z _ hs w hw]
  rw [hr]
  unfold wakeInstants
  rw [List.find?_map, List.find?_filter]
  congr 1
  apply find?_congr_mem
  intro e _
  simp only [Function.comp_apply, Bool.decide_and, Bool.decide_eq_true]

/-! ### Every entry's day, on the wire, and its compiled twin -/

/-- **Every entry's day** (fork `ViewRow::day`): `(line, dayOf)` for every entry in file order,
cancelled entries and undos included, over the day index of the survivors' wakes. -/
def entryDays (z : Cal.Tz) (es : List Entry) : List (Nat × Nat) :=
  let kw := dayIndexOf z es
  es.map (fun e => (e.line, dayOf z kw e.t.val))

/-- **Fork `partition_point(|w| *w <= t)`**: the number of wakes at or before `t` in an ascending
array, by bisection of `[lo, hi)`. -/
def lePoint (a : Array Cal.Instant) (t : Cal.Instant) (lo hi : Nat) : Nat :=
  if _h : lo < hi then
    match a[(lo + hi) / 2]? with
    | some w => if w ≤ t then lePoint a t ((lo + hi) / 2 + 1) hi else lePoint a t lo ((lo + hi) / 2)
    | none => lo
  else lo
termination_by hi - lo
decreasing_by all_goals omega

def lastWakeLeArr (a : Array Cal.Instant) (t : Cal.Instant) : Option Cal.Instant :=
  match lePoint a t 0 a.size with
  | 0 => none
  | p + 1 => a[p]?

def dayOfArr (z : Cal.Tz) (a : Array Cal.Instant) (t : Cal.Instant) : Nat :=
  match lastWakeLeArr a t with
  | some w => if (Cal.durationBetween w t).1 < 86400 then Cal.localDate z w else Cal.localDate z t
  | none => Cal.localDate z t

def entryDaysFast (z : Cal.Tz) (es : List Entry) : List (Nat × Nat) :=
  let a := (dayIndexOf z es).toArray
  es.map (fun e => (e.line, dayOfArr z a e.t.val))

theorem lePoint_spec (l : List Cal.Instant) (hs : l.Pairwise (· ≤ ·)) (t : Cal.Instant) (lo hi : Nat)
    (hlh : lo ≤ hi) (hn : hi ≤ l.length)
    (hlo : ∀ i (hi' : i < l.length), i < lo → l[i] ≤ t)
    (hhi : ∀ i (hi' : i < l.length), hi ≤ i → ¬ l[i] ≤ t) :
    lePoint l.toArray t lo hi ≤ l.length ∧
    (∀ i (h : i < l.length), i < lePoint l.toArray t lo hi → l[i] ≤ t) ∧
    (∀ i (h : i < l.length), lePoint l.toArray t lo hi ≤ i → ¬ l[i] ≤ t) := by
  rw [lePoint]
  split
  · rename_i h
    have hm : (lo + hi) / 2 < l.length := by omega
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hm]
    simp only
    split
    · rename_i hle
      apply lePoint_spec l hs t _ hi (by omega) hn
      · intro i hi' hi2
        by_cases hlt : i < lo
        · exact hlo i hi' hlt
        · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi2) with hi3 | hi3
          · exact instant_le_trans (List.pairwise_iff_getElem.1 hs i _ hi' hm hi3) hle
          · simp only [hi3]; exact hle
      · exact hhi
    · rename_i hle
      apply lePoint_spec l hs t lo _ (by omega) (by omega) hlo
      intro i hi' hi2
      rcases Nat.lt_or_eq_of_le hi2 with hi3 | hi3
      · intro hc; exact hle (instant_le_trans (List.pairwise_iff_getElem.1 hs _ i hm hi' hi3) hc)
      · simp only [← hi3]; exact hle
  · refine ⟨by omega, fun i hi' hi2 => hlo i hi' hi2, fun i hi' hi2 => hhi i hi' (by omega)⟩
termination_by hi - lo
decreasing_by all_goals omega

theorem lastWakeLe_of_point (t : Cal.Instant) : ∀ (l : List Cal.Instant) (p : Nat), p ≤ l.length →
    (∀ i (h : i < l.length), i < p → l[i] ≤ t) →
    (∀ i (h : i < l.length), p ≤ i → ¬ l[i] ≤ t) →
    lastWakeLe l t = (match p with | 0 => none | q + 1 => l[q]?)
  | [], p, hp, _, _ => by
    simp at hp; subst hp; rfl
  | x :: xs, 0, _, _, h2 => by
    have ih := lastWakeLe_of_point t xs 0 (Nat.zero_le _) (fun i _ hi => absurd hi (Nat.not_lt_zero _))
      (fun i h _ => by have := h2 (i + 1) (by simp; omega) (Nat.zero_le _); rwa [List.getElem_cons_succ] at this)
    simp only at ih ⊢
    rw [lastWakeLe_cons, ih, if_neg (by have := h2 0 (by simp) (Nat.le_refl 0); rwa [List.getElem_cons_zero] at this)]
    rfl
  | x :: xs, q + 1, hp, h1, h2 => by
    have hx : x ≤ t := by have := h1 0 (by simp) (Nat.succ_pos _); rwa [List.getElem_cons_zero] at this
    have ih := lastWakeLe_of_point t xs q (by simp at hp; omega)
      (fun i h hi => by have := h1 (i + 1) (by simp; omega) (by omega); rwa [List.getElem_cons_succ] at this)
      (fun i h hi => by have := h2 (i + 1) (by simp; omega) (by omega); rwa [List.getElem_cons_succ] at this)
    rw [lastWakeLe_cons, ih, if_pos hx]
    cases q with
    | zero => rfl
    | succ r =>
      have hr : r < xs.length := by simp at hp; omega
      simp [List.getElem?_eq_getElem hr]

/-- **The bisection is the fold** on an ascending list. -/
theorem lastWakeLeArr_eq_lastWakeLe (l : List Cal.Instant) (hs : l.Pairwise (· ≤ ·)) (t : Cal.Instant) :
    lastWakeLeArr l.toArray t = lastWakeLe l t := by
  obtain ⟨hp, h1, h2⟩ := lePoint_spec l hs t 0 l.length (Nat.zero_le _) (Nat.le_refl _)
    (fun i _ h => absurd h (Nat.not_lt_zero _)) (fun i hi h => absurd hi (Nat.not_lt.2 h))
  rw [lastWakeLe_of_point t l _ hp h1 h2]
  unfold lastWakeLeArr
  simp only [List.size_toArray]
  split <;> simp_all

@[csimp] theorem entryDays_eq_entryDaysFast : @entryDays = @entryDaysFast := by
  funext z es
  unfold entryDays entryDaysFast
  simp only
  apply List.map_congr_left
  intro e _
  unfold dayOfArr dayOf dayIndexOf
  rw [lastWakeLeArr_eq_lastWakeLe _ (keptWakes_sorted z _)]

end DayIndex



/-! ## Witnesses (C2)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 3 entries
or 3 wakes, at most 2 zone transitions (`Cal.chicago`'s two, `foldZone`'s one, `utcZone`'s none),
instants as `Nat` literals, no text parsed. -/

section DayWitnesses

/-- UTC: no transitions. -/
def utcZone : Cal.Tz := ⟨⟨['U', 'T', 'C'], ⟨false, 0⟩, []⟩, by decide⟩

/-- **`day_index_wake_to_wake`, ported** (§6.2, inventory §2.3): Chicago, wakes at 2026-09-07T06:05-05:00
and 2026-09-08T06:40-05:00, both kept.  The first wake is on the 7th; 00:30 the next morning, before
the next wake, is the 7th; 06:20 on the 8th is the 8th (the wake is 24 h 15 min old, stale); the second
wake is the 8th; 00:30 on the 9th is the 8th; 07:00 on the 9th is the 9th (no wake that date); 05:00
on the 7th is the 7th (before the first wake).  With no wakes, 00:30 on the 8th is the 8th, and
`2026-09-08T03:00:00+00:00` is the 7th: the date is read in the zone, not the written offset.  Days
739865–739867 are 2026-09-07 to 09 (`Cal.toDay`). -/
theorem day_index_wake_to_wake_ported :
    let kw := keptWakes Cal.chicago [⟨63924375900, 0⟩, ⟨63924464400, 0⟩]
    kw = [⟨63924375900, 0⟩, ⟨63924464400, 0⟩] ∧
    dayOf Cal.chicago kw ⟨63924375900, 0⟩ = 739865 ∧
    dayOf Cal.chicago kw ⟨63924442200, 0⟩ = 739865 ∧
    dayOf Cal.chicago kw ⟨63924463200, 0⟩ = 739866 ∧
    dayOf Cal.chicago kw ⟨63924464400, 0⟩ = 739866 ∧
    dayOf Cal.chicago kw ⟨63924528600, 0⟩ = 739866 ∧
    dayOf Cal.chicago kw ⟨63924552000, 0⟩ = 739867 ∧
    dayOf Cal.chicago kw ⟨63924372000, 0⟩ = 739865 ∧
    dayOf Cal.chicago [] ⟨63924442200, 0⟩ = 739866 ∧
    dayOf Cal.chicago [] ⟨63924433200, 0⟩ = 739865 := by
  decide


/-- A wake entry of the witnesses, written at `-05:00`. -/
def wWake (line : Nat) (t : Cal.VInstant) : Entry := ⟨line, t, Log.cdt, .wake ⟨420, by decide⟩ none⟩

def wNote (line : Nat) (t : Cal.VInstant) : Entry := ⟨line, t, Log.cdt, .note ['n']⟩

/-- **Quirk Q6(a): two "first wake" rules** (gap 82).  Two wakes on 2026-09-07 in Chicago, appended out
of time order: 07:00 on line 1, then 06:05 on line 2.  The day index keeps the earlier **by instant**,
06:05; the first wake **in file order** attributed to that day is line 1's 07:00, which is what fork
`DayReplay.wake` and `slept_by_day` read.  Both rules are ported; this is what separates them. -/
theorem the_kept_wake_is_not_the_first_logged_wake :
    ∃ (z : Cal.Tz) (es : List Entry) (d : Nat) (w : Cal.Instant) (e : Entry),
      keptWakeOn z (dayIndexOf z es) d = some w ∧
      firstLoggedWakeOn z (dayIndexOf z es) (survivors es) d = some e ∧ e.t.val ≠ w :=
  ⟨Cal.chicago, [wWake 1 ⟨⟨63924379200, 0⟩, by decide⟩, wWake 2 ⟨⟨63924375900, 0⟩, by decide⟩], 739865,
    ⟨63924375900, 0⟩, wWake 1 ⟨⟨63924379200, 0⟩, by decide⟩, by decide, by decide, by decide⟩

/-- A zone whose clock falls back across midnight: UTC until 2026-09-08T00:30:00Z, `-01:00` from then
(the local clock goes from 00:30 on the 8th back to 23:30 on the 7th).  One transition. -/
def foldZone : Cal.Tz := ⟨⟨['F', 'o', 'l', 'd'], ⟨false, 0⟩, [(⟨63924424200, 0⟩, ⟨true, 3600⟩)]⟩, by decide⟩

/-- **The porting trap of §6.2: `dedup_by` is consecutive.**  In `foldZone`, wakes at 21:30 on the 7th,
00:29:59 on the 8th and, one second later, 23:30 on the 7th again have local dates 7, 8, 7 in instant
order.  The index keeps all three, since no two consecutive ones share a date, where "the earliest
wake per date" would keep two; and 23:45 on the 7th then belongs to the third wake's day, the 7th,
where the earliest-per-date index would put it on the 8th. -/
theorem the_day_index_dedups_runs_not_dates :
    keptWakes foldZone [⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩]
      = [⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩] ∧
    (([⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩] : List Cal.Instant).map (Cal.localDate foldZone))
      = [739865, 739866, 739865] ∧
    dayOf foldZone [⟨63924413400, 0⟩, ⟨63924424199, 0⟩, ⟨63924424200, 0⟩] ⟨63924425100, 0⟩ = 739865 ∧
    dayOf foldZone [⟨63924413400, 0⟩, ⟨63924424199, 0⟩] ⟨63924425100, 0⟩ = 739866 := by
  decide

/-- **Refuted as §15 wrote it** (carried note 1): with the 24-hour test on `Instant.nanos`,
`dayOf_is_the_wake_date_within_a_day` is false of the fork's day.  A wake at `03:00:59` plus 1.5 s of
leap nanoseconds on 2026-09-07 UTC and `03:01:00` on the 8th are 23 h 59 min 59.5 s apart by nanosecond
counts, and 24 h 0.5 s apart by chrono's `signed_duration_since`, which counts the leap second because
the later clock is past it in the day.  The fork gives the 8th. -/
theorem dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted :
    ∃ (kw : List Cal.Instant) (t w : Cal.Instant), lastWakeLe kw t = some w ∧
      t.nanos < w.nanos + 86400 * 1000000000 ∧ dayOf utcZone kw t ≠ Cal.localDate utcZone w :=
  ⟨[⟨63924346859, 1500000000⟩], ⟨63924433260, 0⟩, ⟨63924346859, 1500000000⟩, by decide⟩

/-- **Refuted as §15 wrote it** (carried note 1): `a_wake_day_is_shorter_than_a_day` with a nanosecond
conclusion is false of the fork's day.  A wake at 03:00:00 UTC on 2026-09-07 and the stamp
`2026-09-08T02:59:60.5Z` (second 59 with 1.5 s of leap nanoseconds, chrono's reading of `:60`): chrono
counts no leap second before a clock earlier in the day, so 23 h 59 min 59.5 s passed and the stamp is
on the wake's day, the 7th, a date not its own; by nanosecond counts 24 h 0.5 s passed. -/
theorem a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted :
    ∃ (ws : List Cal.Instant) (t w : Cal.Instant),
      lastWakeLe (keptWakes utcZone ws) t = some w ∧
      dayOf utcZone (keptWakes utcZone ws) t = Cal.localDate utcZone w ∧
      Cal.localDate utcZone t ≠ Cal.localDate utcZone w ∧
      Cal.durationBetween w t = (86399, 500000000) ∧
      ¬ t.nanos < w.nanos + 86400 * 1000000000 :=
  ⟨[⟨63924346800, 0⟩], ⟨63924433199, 1500000000⟩, ⟨63924346800, 0⟩, by decide⟩

/-- **Refuted as §15 wrote it** (carried note 1): `keptWakes_append_of_later` with its hypothesis on
`Instant.nanos` is false of the fork's index, which sorts in chrono's order.  `00:01:00` has fewer
nanoseconds than `00:00:59` plus 1.5 s of leap nanoseconds and is after it in chrono's order, so the
sort puts the leap second first and the date's run keeps it, not `00:01:00`. -/
theorem keptWakes_append_of_later_by_nanos_is_refuted :
    ∃ (ws₁ ws₂ : List Cal.Instant), (∀ a ∈ ws₁, ∀ b ∈ ws₂, a.nanos < b.nanos) ∧
      keptWakes utcZone (ws₁ ++ ws₂)
        ≠ keptWakes utcZone ws₁ ++ keptFrom utcZone (keptWakes utcZone ws₁).getLast? ws₂ :=
  ⟨[⟨60, 0⟩], [⟨59, 1500000000⟩], by decide⟩

/-- **`a_wake_day_is_shorter_than_a_day`'s hypotheses are satisfiable**: 00:30 on 2026-09-08 in Chicago
belongs to the 06:05 wake of the 7th, a date not its own. -/
theorem a_wake_day_is_shorter_than_a_day_is_not_vacuous :
    lastWakeLe (keptWakes Cal.chicago [⟨63924375900, 0⟩, ⟨63924464400, 0⟩]) ⟨63924442200, 0⟩
      = some ⟨63924375900, 0⟩ ∧
    dayOf Cal.chicago (keptWakes Cal.chicago [⟨63924375900, 0⟩, ⟨63924464400, 0⟩]) ⟨63924442200, 0⟩
      = Cal.localDate Cal.chicago ⟨63924375900, 0⟩ ∧
    Cal.localDate Cal.chicago ⟨63924442200, 0⟩ ≠ Cal.localDate Cal.chicago ⟨63924375900, 0⟩ := by
  decide

/-- **An undone wake indexes nothing, and every entry keeps a day**: a wake at 06:05 on the 7th, a note
at 00:30 on the 8th, and `undo{of:"wake"}` at 00:31.  With the wake cancelled the note is on its own
date, the 8th; the cancelled wake and the undo still have days (their own dates). -/
theorem an_undone_wake_indexes_nothing :
    entryDays Cal.chicago [wWake 1 ⟨⟨63924375900, 0⟩, by decide⟩, wNote 2 ⟨⟨63924442200, 0⟩, by decide⟩,
      ⟨3, ⟨⟨63924442260, 0⟩, by decide⟩, Log.cdt, .undo Log.Kind.wake.tag none⟩]
      = [(1, 739865), (2, 739866), (3, 739866)] ∧
    entryDays Cal.chicago [wWake 1 ⟨⟨63924375900, 0⟩, by decide⟩, wNote 2 ⟨⟨63924442200, 0⟩, by decide⟩]
      = [(1, 739865), (2, 739865)] := by
  decide

end DayWitnesses


/-! ## C3: the machine, its effects, and the block family (§8.1–§8.2)

Fork `Machine` (`tm-core/src/log.rs`; inventory §2.4) for the arms `start`, `pause`, `unpause`,
`interrupt`, `resume`, `stop`, `done` (partial included) and `extend`, with the helpers ported by name:
`close_sub` is `settle` (D99), `close_pause` `closePause`, `credit` `creditFx`, `uncredit_cut` `uncreditFx`
and `cut` `cut`.  The machine is written as **effects** (§8.2): `effects` reads the state before an
entry and returns what the entry changes, each effect naming the one key it writes (`Effect.key`), and
`applyEffects` applies them in order.  `applyEffects_touches_only_named_keys` is the frame law. -/

section Machine

open Log (Id U8 U32 Num)

/-! ### Maps -/

/-- **A map as an association list**, the specification's map (W4's tree maps are the gated lever).
`get` reads the first pair of a key.  `alter` rewrites that pair in place, or deletes every pair of the
key, or prepends a new pair when there is none; it is a tail-recursive loop (D9-21) that stops at the
key.  Its law, `KMap.get_alter`, holds for every list, duplicates included. -/
abbrev KMap (κ β : Type) := List (κ × β)

namespace KMap

variable {κ β : Type} [DecidableEq κ]

def get (m : KMap κ β) (k : κ) : Option β := (m.find? (fun p => decide (p.1 = k))).map Prod.snd

def alterGo (k : κ) (f : Option β → Option β) (orig : KMap κ β) : KMap κ β → KMap κ β → KMap κ β
  | _, [] =>
    match f none with
    | some v => (k, v) :: orig
    | none => orig
  | acc, p :: rest =>
    if p.1 = k then
      match f (some p.2) with
      | some v => acc.reverseAux ((k, v) :: rest)
      | none => acc.reverseAux (rest.filter (fun q => !decide (q.1 = k)))
    else alterGo k f orig (p :: acc) rest

/-- A key that is absent costs one scan and no allocation: only a present key is rewritten in place. -/
def alter (m : KMap κ β) (k : κ) (f : Option β → Option β) : KMap κ β :=
  match get m k with
  | none =>
    match f none with
    | some v => (k, v) :: m
    | none => m
  | some _ => alterGo k f m [] m

end KMap

/-- The hash of a key of a bucketed map; it chooses the bucket searched, never what is found. -/
class KeyHash (κ : Type) where
  hash : κ → Nat

instance : KeyHash (List Char) := ⟨keyHash⟩

/-- C5: a day's key (the days map, and `slept_by_day`'s compiled lookup). -/
instance : KeyHash Nat := ⟨fun n => n⟩

instance : KeyHash (Nat × List Char) := ⟨fun p => p.1 + keyHash p.2⟩

/-- C4: an instance's key, `(item, inst)`. -/
instance : KeyHash (List Char × List Char) := ⟨fun p => keyHash p.1 * 31 + keyHash p.2⟩

/-- C4: a named event's key, `(name, id?)`. -/
instance : KeyHash (List Char × Option (List Char)) :=
  ⟨fun p => keyHash p.1 * 31 + (match p.2 with | some i => keyHash i + 1 | none => 0)⟩

/-- **A map in buckets of association lists**, for keys with no locality in a log (item ids): each
lookup scans one bucket.  An array, not a structure around one, so an update of a uniquely held map is in
place.  Its law, `HMap.get_alter`, holds on every map, one with no bucket included (`alter` gives it
one). -/
abbrev HMap (κ β : Type) := Array (KMap κ β)

namespace HMap

variable {κ β : Type} [DecidableEq κ] [KeyHash κ]

def empty (n : Nat) : HMap κ β := Array.replicate (n + 1) []

def get (m : HMap κ β) (k : κ) : Option β :=
  match m[KeyHash.hash k % m.size]? with
  | some b => b.get k
  | none => none

def alter (m : HMap κ β) (k : κ) (f : Option β → Option β) : HMap κ β :=
  if m.size = 0 then #[KMap.alter [] k f]
  else m.modify (KeyHash.hash k % m.size) (fun b => b.alter k f)

/-- The values mapped, bucket by bucket (through the buckets' list: core's `Array.map` is well-founded
recursion, which `decide` does not evaluate). -/
def mapVals {γ : Type} (m : HMap κ β) (f : β → γ) : HMap κ γ :=
  ⟨(Array.toList m).map (fun b => b.map (fun p => (p.1, f p.2)))⟩

/-- Every pair, bucket by bucket (the facts read it as a map). -/
def pairs (m : HMap κ β) : KMap κ β := (Array.toList m).foldl (fun acc b => b ++ acc) []

end HMap

/-! ### The state (§8.1) -/

/-- A stamp as the fork keeps it, `DateTime<FixedOffset>`: the instant, and the offset it was written
at.  Every order and duration reads the instant (`.1`) only. -/
abbrev At := Cal.Instant × Cal.Offset

/-- Fork `StartRecord`. -/
structure StartRec where
  t : At
  id : Id
  pred : U8
  rep : Option U8
deriving DecidableEq, Repr

/-- Fork `SegmentKind`: the block family's three kinds, and (C5) the day family's `Break`, `Routine` and
`Idle`. -/
inductive SegKind
  | block (id : Id)
  | pause (id : Id)
  | interrupt (id : Option Id)
  | brk (where_ : Option (List Char))
  | routine (item inst : List Char)
  | idle (attributed : List Char)
deriving DecidableEq, Repr

/-- Fork `LogSegment`. -/
structure Segment where
  start : At
  stop : At
  kind : SegKind
deriving DecidableEq, Repr

/-- Fork `EnergyObs`, with the line of the entry it came from (a start's carries the start's). -/
structure EnergyObs where
  line : Nat
  t : At
  day : Nat
  pred : U8
  rep : U8
  hsw : Num
  loc : List Char
  sleptMin : Option Nat
  went : Option U8
  id : Option Id
  fromStart : Bool
deriving DecidableEq, Repr

/-- Fork `DurationObs`. -/
structure DurationObs where
  line : Nat
  t : At
  day : Nat
  id : Id
  ci : U8
  tags : List (List Char)
  estMin : Nat
  actualMin : Nat
  went : Option U8
  isPartial : Bool
deriving DecidableEq, Repr

/-- Fork `Interruption`, with (C6) the line of the `resume` that pushed it: the view hands interruptions back
per day, and Rust restores the fork's push order by it (design §11.2's rule for observations).  The open
interruption, which fork `finish` builds and no line pushes, carries line 0. -/
structure Interruption where
  line : Nat
  start : Option At
  stop : Option At
  day : Nat
  id : Option Id
  lostMin : Nat
  dropped : List Id
deriving DecidableEq, Repr

/-- **C5: fork `BreakRecord`.** -/
structure BreakRec where
  t : At
  day : Nat
  plannedMin : Nat
  actualMin : Option Nat
  where_ : Option (List Char)
deriving DecidableEq, Repr

/-- **C5: fork `IdleRecord`**: `t` ends the gap, and `day` is the day of its start. -/
structure IdleRec where
  t : At
  day : Nat
  attributed : List Char
  min : Nat
deriving DecidableEq, Repr

/-- **C5: fork `LeakRecord`.** -/
structure LeakRec where
  t : At
  day : Nat
  min : Nat
deriving DecidableEq, Repr

/-- **C5: fork `Demotion`**, its `stamp` fork `stamp_from_key(from)` (`Log.stampFromKey`), with (C6) its entry's
line: the view hands demotions back per day, and Rust restores each id's file order by it. -/
structure Demotion where
  line : Nat
  t : At
  id : Id
  from_ : List Char
  to : List Char
  estMin : Nat
  stamp : Option Field.Stamp
deriving DecidableEq, Repr

/-- **C5: fork `CloseRecord`**, with (C6) its entry's line, for the same reason as a demotion's. -/
structure CloseRec where
  line : Nat
  t : At
  period : List Char
  key : List Char
deriving DecidableEq, Repr

/-- **C4: fork `InstanceRecord`**: the stamp, the status (an unknown one read as `Pending`), the status as
logged, and the minutes. -/
structure InstRec where
  t : At
  status : Log.InstanceStatus
  raw : List Char
  actualMin : Option Nat
deriving DecidableEq, Repr

/-- **C4: a replay warning** (§8.3), named, not formatted (P15).  Fork `Replay.warnings` holds one message,
`"{t}: unknown routine status {status:?}"`; the kernel keeps the entry's line and the status as logged.

**Since stage 6 W-48 track K** two more, each a fact the machine meets as it steps and `tm check` names (the owner's
D18 family: a warning, the exit code unchanged):
* `breakPlace` (the owner's **D116**, README gap 5035), with a line and two places: the `break` line on that line ends a
  break whose `break_start` gave the first place, and it writes the second, another word — the break is read at the
  first (`brkPlace`), and the end line's word is named, never a second reading;
* `pastBound line day newest` (the owner's **D119**, README gaps 4913, 4917 and 5029): the late mark on `line` — a
  `break`, a `start` or an interruption's `resume`, each netted from the blocks the machine holds closed — is stepped on
  ledger day `day`, more than 31 ledger days behind `newest`, the newest day of a block it holds closed (`pastBound`), so a
  block closed on such a day that the mark lies across may no longer be held (`pruneClosed`, D100's bound, which stays)
  and is not netted. -/
inductive RWarn
  | unknownInstanceStatus (line : Nat) (raw : List Char)
  | breakPlace (line : Nat) (start end_ : Option (List Char))
  | pastBound (line day newest : Nat)
deriving DecidableEq, Repr

/-- The later of two candidates under a replacing relation `r`: `x` replaces `a` when `r a x`. -/
def pick {α : Type} (r : α → α → Bool) (a x : α) : α := if r a x then x else a

/-- **One step of a running maximum** under a replacing relation: the first element is taken, and each
later one replaces the candidate when `r candidate x`.  With `r` "strictly later" the first of equal
keys stays (fork `last_done`); with "at least as late" the last of equal keys wins (fork `LatestNamed`). -/
def lastMaxStep {α : Type} (r : α → α → Bool) (acc : Option α) (x : α) : Option α :=
  match acc with
  | none => some x
  | some a => some (pick r a x)

/-- The running maximum of a list, as a `foldl` (D9-21). -/
def lastMax? {α : Type} (r : α → α → Bool) (l : List α) : Option α := l.foldl (lastMaxStep r) none

/-- Strictly later by instant (chrono's order; the written offset is not compared). -/
def instLt (a b : At) : Bool := decide (a.1 < b.1)

/-- **Fork `last_done`'s rule** (`if t > *last { *last = t }`): the latest completion by instant, the
first of equal instants kept. -/
def maxByInstant? (l : List At) : Option At := lastMax? instLt l

/-- **C5: fork `longest_leak`'s rule** (`is_none_or(|l| min > l.min)`): strictly longer replaces, so the
first of equal maxima stays. -/
def leakLt (a b : LeakRec) : Bool := decide (a.min < b.min)

/-- `(line, stamp)` at least as late by instant: fork `LatestNamed.latest` (`t >= l.latest`). -/
def latestRel (a b : Nat × At) : Bool := decide (a.2.1 ≤ b.2.1)

/-- `(local date, line, stamp)` at least as late by date, then by instant: fork
`LatestNamed.latest_dated` (`(date, t) >= (date, latest_dated)`). -/
def datedRel (a b : Nat × Nat × At) : Bool := decide (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.2.1 ≤ b.2.2.1))

/-- **C4: fork `LatestNamed` of one `(name, id?)` key** (R3; carried note 3).  `latest` is the latest
occurrence by instant, with its line; `dated` the latest by local date in the zone, then by instant, with
its date and line.  A later line wins a tie in both, as in the fork.  They differ only when the zone's
clock went back across midnight between them, which is why a "since" filter does not commute with the
latest by instant (`a_since_filter_does_not_commute_with_the_latest_by_instant`) and the fork keeps
both. -/
structure NamedRec where
  latest : Nat × At
  dated : Nat × Nat × At
deriving DecidableEq, Repr

/-- An occurrence at `line`, stamp `t`, local date `date`, folded into a key's record. -/
def NamedRec.push (o : Option NamedRec) (line : Nat) (t : At) (date : Nat) : NamedRec :=
  match o with
  | none => ⟨(line, t), (date, line, t)⟩
  | some r => ⟨pick latestRel r.latest (line, t), pick datedRel r.dated (date, line, t)⟩

/-- Minutes per ci, `minutes_by_ci: [u32; 6]`. -/
structure Ci6 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
deriving DecidableEq, Repr

def Ci6.zero : Ci6 := ⟨0, 0, 0, 0, 0, 0⟩

/-- `minutes_by_ci[i] += m`, for an index already clamped to `0..5`. -/
def Ci6.add (c : Ci6) (i m : Nat) : Ci6 :=
  match i with
  | 0 => { c with c0 := c.c0 + m }
  | 1 => { c with c1 := c.c1 + m }
  | 2 => { c with c2 := c.c2 + m }
  | 3 => { c with c3 := c.c3 + m }
  | 4 => { c with c4 := c.c4 + m }
  | _ => { c with c5 := c.c5 + m }

def Ci6.sum (c : Ci6) : Nat := c.c0 + c.c1 + c.c2 + c.c3 + c.c4 + c.c5

def Ci6.toList (c : Ci6) : List Nat := [c.c0, c.c1, c.c2, c.c3, c.c4, c.c5]

/-- `minutes_by_ci[i]`, for an index already clamped to `0..5`. -/
def Ci6.get (c : Ci6) (i : Nat) : Nat :=
  match i with
  | 0 => c.c0
  | 1 => c.c1
  | 2 => c.c2
  | 3 => c.c3
  | 4 => c.c4
  | _ => c.c5

/-- `minutes_by_ci[i] -= m` (saturating), for an index already clamped to `0..5` — the owner's D100's netting of a
closed `done`'s credit (`DayOp.net`). -/
def Ci6.sub (c : Ci6) (i m : Nat) : Ci6 :=
  match i with
  | 0 => { c with c0 := c.c0 - m }
  | 1 => { c with c1 := c.c1 - m }
  | 2 => { c with c2 := c.c2 - m }
  | 3 => { c with c3 := c.c3 - m }
  | 4 => { c with c4 := c.c4 - m }
  | _ => { c with c5 := c.c5 - m }

/-- **Fork `DayReplay`**: the block family's fields (C3), then the day header and records (C5).  Lists are
newest first (a push is a cons); the facts put them back in file order.  Sums are `Nat` where the fork
saturates `u32` (parity P17). -/
structure DayAcc where
  firstStart : Option At
  starts : List StartRec
  blockMin : Nat
  blocksDone : Nat
  loadFifths : Nat
  byCi : Ci6
  ciUnknown : KMap Id Nat
  done : List Id
  lostMin : Nat
  dropped : List Id
  segments : List Segment
  /-- C5: the first `wake` in file order attributed to the day, with its `slept_min` and `onset_min` -/
  wake : Option At
  sleptMin : Option Nat
  onsetMin : Option Nat
  /-- C5: the first `arrive`, with its location, window and budget -/
  arrival : Option At
  loc : Option (List Char)
  window : Option (List Char × List Char)
  budget : Option Nat
  /-- C5: every location set (`arrive` and `loc`) -/
  locChanges : List (At × List Char)
  /-- C5: the `leak` minutes of the idle gaps begun on the day, and the longest -/
  leakMin : Nat
  longestLeak : Nat
  idle : List IdleRec
  breaks : List BreakRec
  /-- C5: `routine … done` minutes -/
  routineMin : Nat
  /-- C5: `plan` events, the highest `replans_today`, `drift_min` summed, the last hash -/
  plans : Nat
  replansToday : Nat
  driftMin : Nat
  lastPlanHash : Option (List Char)
  /-- **D100 (README gap 4520b, W-47 track K, parity P105): the minutes netted from a `done`'s duration observation**,
  by the line of the `done` that pushed it — a `break` logged after the `done` and stamped inside its block takes them
  from the block (`DayOp.net`), and every reading of the day's duration observations reads them net (`netDur`).  Fork
  `DayReplay` had no such field: a closed block was never read again. -/
  durNet : KMap Nat Nat
  /-- **The last `plan` line's stamp** (the W-48 repair, README gap 5210), beside `lastPlanHash`: `.tm/state.json`'s
  `last_plan_hash` is the host's by CALENDAR day, and a `plan` written after local midnight and before the wake is
  filed under the previous ledger day (`dayOf`), so D42's rebuild finds a calendar day's last plan by its stamp, over
  the two ledger days a calendar day's lines can be filed under.  **Since W-49 track L** (README gap 5300) it is the
  last `plan` line of the LATEST calendar date the ledger day's `plan` lines are stamped on (`notBefore`): a line
  stamped on an earlier date — a clock behind the log across midnight — no longer moves the later date's answer.
  Fork `DayReplay` had no such field. -/
  planAt : Option At
  /-- That line's hash (W-49 track L): the calendar day's last plan's, where `lastPlanHash` is the ledger day's last
  line's in file order, whatever its date (the fork's field). -/
  planHash : Option (List Char)
  /-- That line's line number (W-49 track L): two ledger days can hold one calendar day's lines, and the later line
  wins (the owner's D125). -/
  planLine : Option Nat
  /-- **The last `plan` line that carried a hysteresis input: its stamp** (README gaps 5210 and 5211) — §7.4's input,
  the map `.tm/state.json`'s `priorities_yesterday` caches (the owner's **D108**, parity P119).  The host writes it on a
  CALENDAR day's first `plan` and reads it back, for §7.4 and for D42's rebuild, by this stamp's local date.  **Since
  W-49 track L it is the day's ONE answer to that question** (README gap 5300): the first-of-the-ledger-day reading
  (`yesterday`) is gone, a later line carrying an input wins over an earlier one (the owner's **D125**), and a line
  stamped on an earlier calendar date than the slot's does not move it (`notBefore`).  `none` on a day no `plan`
  carried one. -/
  lateAt : Option At
  /-- That line's line number (W-49 track L, D125: the later line wins across the two ledger days). -/
  lateLine : Option Nat
  /-- That line's map (`late`, beside `lateAt`). -/
  late : List (Id × U8)
deriving DecidableEq, Repr

/-- `DayReplay::new(date)`. -/
def DayAcc.empty : DayAcc :=
  ⟨none, [], 0, 0, 0, Ci6.zero, [], [], 0, [], [], none, none, none, none, none, none, none, [], 0, 0, [], [],
    0, 0, 0, 0, none, [], none, none, none, none, none, []⟩

/-- **The block family's part of fork `ItemReplay`** (`minutes_by_day` is the map `State.itemDays`). -/
structure ItemAcc where
  minutes : Nat
  blocks : Nat
  doneAt : List At
  partialDoneAt : List At
  stops : Nat
  extendedMin : Nat
deriving DecidableEq, Repr

def ItemAcc.empty : ItemAcc := ⟨0, 0, [], [], 0, 0⟩

/-- **A drawn piece of a block** (the owner's **D99**, README gap 4520a, W-47 track K, parity P104): the span of a
`Block` segment the replay wrote into a day record, and the day it filed it under — the day index's `dy` of its start,
read once, when it was drawn. -/
structure Piece where
  s : At
  e : At
  day : Nat
deriving DecidableEq, Repr

/-- Fork `Block`.  The pending start observation lives in the block (§8.1) and is emitted when the
block closes or at `finish`, carrying the start's line.  **`day`** (the owner's D94, README gaps 4361 and 4506,
parity P92) is the ledger day its `start` was stepped on — the day the host's `Replay::idle_min_since` reads a
block's idle marks from (its `start` row's) — so the breaks its clock nets are the ones on its ledger days
(`spansFor`).  Fork `Block` had no such field: its clock netted no break. -/
structure Block where
  id : Id
  started : At
  since : Option At
  paused : Bool
  pausedAt : Option At
  workedMin : Nat
  obs : Option EnergyObs
  day : Nat
  /-- **The block's own closed idle spans** (the owner's **D99**, README gap 4520a, parity P104): every `Pause` segment
  it drew and every interruption that closed while it was open, each `[from, until)`.  With the breaks of its ledger
  days (`spansFor`) they are what its clock nets — wherever a mark that wrote one was logged (`settle`). -/
  idle : List (At × At)
  /-- **The pieces of it drawn so far** (D99): every `Block` segment written into a day record for it, each with the day
  it was filed under, so a later mark that moves one un-draws exactly what was written (`redraw`). -/
  drawn : List Piece
  /-- **The minutes its `extend`s have added since its `start`** (the owner's **D108**, README gaps 4876 and 4893, W-48
  track A): `tm extend` adds them to the block's planned minutes, so D42's rebuild of `.tm/state.json`'s
  `active.est_min` reads them here, as the verb computes them, and not off the item's line multiplied.  Fork `Block`
  had no such field: an `extend` wrote its item's `extended_min` alone. -/
  ext : Nat
deriving DecidableEq, Repr

/-- Fork `Cut`, with its day computed when stored (§8.1). -/
structure Cut where
  id : Id
  t : At
  day : Nat
  min : Nat
deriving DecidableEq, Repr

/-- **A break the machine holds** (the owner's D94, README gaps 4361 and 4506, parity P92): its span `[s, e)` — `s`
its stamp, `e` its end (`brkEnd`) — and the ledger day it was stepped on, the day the host files its idle mark
under (`DaySeam::idle_marks`). -/
structure HeldBrk where
  s : At
  e : At
  day : Nat
deriving DecidableEq, Repr

/-- **A block closed by a `stop`, a `done` or a `start` that cut it, held** (the owner's **D100**, README gap 4520b, W-47
track K, parity P105): its id, its ledger day (`Block.day` — a break filed on a ledger day before it is not its, as D94
reads an open block's), the day its credit was filed (`credDay`) with that credit's ci (`none` for a cut's, the `done`'s
for a `done`'s) and the minutes of it still standing (`min`), the pieces drawn for it, and the line of the duration
observation its `done` pushed, if it pushed one — so a `break` logged after it closed and stamped inside it is netted
from it (`netClosed`): its pieces re-drawn around the break, its credit and its duration observation taken down by what the break took.  Fork `Machine` held no closed block: a block's minutes and drawing were final when it closed.  **`started`** (README gap 5501, W-50 repair track R) is its `start`'s stamp, kept so that D129's stamp-order reading asks whether a late `break_start` was stamped BEFORE the block's `start` — only then does that start end it (`firstStart`); a break stamped after the start, inside the block, is D100's late break inside it, netted, and not one its first drawn piece ends.  Read by `firstStart`'s comparison alone, never by the day index, so it is no machine instant (`Seal.machineInstants`). -/
structure Closed where
  id : Id
  day : Nat
  credDay : Nat
  ci : Option U8
  min : Nat
  drawn : List Piece
  durLine : Option Nat
  started : At
  /-- **The pieces a running break took from it, as they stood** (the owner's **D137**, README gaps 5504 and 5302, W-51
  track K, parity **P134**): every drawn piece the running break's netting (`runNet`, gap 5180) met, whole, so that the
  `break` line that ends the break gives the block back what lies outside the break's own span (`giveOne`) — D100's
  netting of a late break inside a block, which nets the break's span and nothing after it.  `[]` when no running break
  has netted it.  Fork `Machine` held no closed block. -/
  ran : List Piece
  /-- **The minutes a running break took from its credit** (D137): what `runNet`'s netting took (`netMin`), given back
  with its pieces when the break's line ends the break (`giveOne`).  `0` when no running break has netted it. -/
  ranMin : Nat
deriving DecidableEq, Repr

/-- **The break running at the end of the log** (the owner's **D105**, README "Stage 6 — W-46 track K", parity
**P100**): the surviving `break_start` no `break` line has ended — its stamp `s` (the break's start), its planned
minutes, its place, and the ledger day it was stepped on, which is the day the `break` line that ends it will write
(its stamp is the start), so the cut rule keeps that day open (`Seal.machineDays`).  Fork `Machine` had no such field:
a running break lived in `.tm/state.json` alone. -/
structure OpenBrk where
  s : At
  planned : Nat
  where_ : Option (List Char)
  day : Nat
deriving DecidableEq, Repr

/-- Fork `Machine`'s block state: the open block, the last cut, and the open interruption (its start,
that start's day, and its id) — and, since the owner's **D94** (README gaps 4361 and 4506, parity P92), **every break
the machine has stepped within `Seal.maxKeepDays` ledger days of the newest one** (`brks`, newest first; D92's one
`brk` span, the last break stepped, was the head of it), so a block's clock nets every break on its ledger days as
the host's `Replay::idle_min_since` unions them: where the clock (re)starts and where a stretch is closed (one reading
since the owner's D99, `settle`), and the open block read at the end of the log (`openOf`).  Fork `Machine` had no such field: a break
stepped before a block began reached no block at all. -/
structure Machine where
  block : Option Block
  lastCut : Option Cut
  interrupt : Option (At × Nat × Option Id)
  brks : List HeldBrk
  /-- The running break (D105, `OpenBrk`): a `break_start` sets it, a `break` line clears it. -/
  brkOpen : Option OpenBrk
  /-- **The closed blocks held** (the owner's D100, `Closed`), the last closed first, within `Seal.maxKeepDays` ledger days
  of the newest held (`pruneClosed`, which never drops the first: the last cut is it). -/
  closed : List Closed
  /-- **The break a `start` ended whose own `break` line is still to come** (the owner's **D129**, README gap 5430, W-50
  track K): its stamp.  A `start` stamped at or after a running break's start ends it there (`endBrkFx`), as `tm start`
  ends one on one machine (D97) — so the `break` line the machine that took the break writes later, stamped at the same
  start (D105), is that break's own line and is not a second break (`arm`'s `break` arm).  `none` otherwise.  Fork
  `Machine` had no such field. -/
  brkEnded : Option At
deriving DecidableEq, Repr

/-- **D94's bound** (README gap 4506): the held breaks within 31 ledger days of the newest one held — `Seal.maxKeepDays`,
the most days a reseal leaves unfolded (§10.4), which this module cannot name (`Seal` imports it) and which
`Seal.pruneBrks_is_bounded_by_maxKeepDays` proves this is, by `rfl`.  The host's `Replay::idle_min_since` reads a
block's idle marks from the seams its replay loads, and a `Hot` read keeps those from the ledger day on, at most
`keepDays ≤ maxKeepDays` days behind a reseal's reach — so the machine, and the checkpoint that carries it, holds the
breaks of at most 32 ledger days, whatever the length of the log. -/
def pruneBrks (l : List HeldBrk) : List HeldBrk :=
  let hi := l.foldl (fun a k => max a k.day) 0
  l.filter (fun k => decide (hi ≤ k.day + 31))

/-- **D100's bound** (README gap 4520b): the closed blocks within 31 ledger days of the newest held — D94's bound for the
breaks that can net them — and, always, the last closed, which is the last cut while one stands (`Machine.lastCut`). -/
def pruneClosed : List Closed → List Closed
  | [] => []
  | c :: l =>
    let hi := l.foldl (fun a k => max a k.day) c.day
    c :: l.filter (fun k => decide (hi ≤ k.day + 31))

/-- **The spans a block's clock nets** (D94): the held breaks on its ledger days — stepped on its `start`'s day or
later, the days the host reads a block's idle marks from — as `[s, e)`. -/
def spansFor (l : List HeldBrk) (day : Nat) : List (At × At) :=
  (l.filter (fun k => decide (day ≤ k.day))).map (fun k => (k.s, k.e))

/-- A span `[s, e)` covers `t`. -/
def covers (p : At × At) (t : At) : Bool := decide (p.1.1 ≤ t.1 ∧ t.1 < p.2.1)

/-- `lift`, with its fuel: every jump lands on a span's end later than every instant before, so the spans bound the
jumps (`lift` gives each one). -/
def liftGo (H : List (At × At)) : Nat → At → At
  | 0, t => t
  | n + 1, t =>
    match H.find? (fun p => covers p t) with
    | some p => liftGo H n p.2
    | none => t

/-- **Where a clock (re)started at `t` runs from** (the owner's D94): `t`, or — when a span covers it — that span's
end, and on past every span the instant reached falls in. -/
def lift (H : List (At × At)) (t : At) : At := liftGo H H.length t

/-- The earliest start of a nonempty span strictly between `x` and `t`. -/
def nextStart (H : List (At × At)) (x t : At) : Option At :=
  H.foldl (fun acc p =>
    if x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1 then
      match acc with
      | some a => if p.1.1 < a.1 then some p.1 else acc
      | none => some p.1
    else acc) none

/-- `pieces`, with its fuel: every piece but the last ends at a nonempty span's start, which the next `lift` passes. -/
def piecesGo (H : List (At × At)) : Nat → At → At → List (At × At)
  | 0, _, _ => []
  | n + 1, x, t =>
    let x' := lift H x
    if H.any (fun p => covers p x') || decide (t.1 ≤ x'.1) then []
    else
      match nextStart H x' t with
      | none => [(x', t)]
      | some s => (x', s) :: piecesGo H n s t

/-- **The worked pieces of a running stretch `[x, t)`** (the owner's D94): from `x` lifted past any span covering it
to the earliest span start after it (or to `t`), then on from that start — so no piece lies across a span.  Each piece
is a sub-segment of its own: its minutes are its own seconds over 60 (site R8). -/
def pieces (H : List (At × At)) (x t : At) : List (At × At) := piecesGo H (H.length + 1) x t

/-! ### `pieces`, compiled (README gap 5027, W-48 track A)

`pieces` walks every span for every piece it draws (`lift`'s `find?`, `nextStart`'s fold), and `settle` asks it at
every mark of an open block, over the block's own idle spans — so `tm now` over a block with `k` pauses cost `k³`
(gap 5027: 1 s at 200 pause pairs, 5 s at 400).  `piecesFast` takes the nonempty spans as given, or sorted by start,
and when they are apart (each ending at or before the next one starts — what a block's own pauses always are) draws
the pieces in one pass (`sweep`); otherwise it is `pieces` itself.  `pieces_eq_piecesFast` proves the two equal on
every input, so every theorem keeps reading `pieces` and the compiled code runs the pass. -/

/-- A count under a stronger predicate is smaller when one element meets the weaker alone. -/
theorem countP_lt_of_witness {α : Type} (P Q : α → Bool) (hPQ : ∀ x, P x = true → Q x = true) :
    ∀ (l : List α) (w : α), w ∈ l → Q w = true → P w = false → l.countP P < l.countP Q
  | [], _, h, _, _ => by cases h
  | x :: l, w, hw, hq, hp => by
    rw [List.countP_cons, List.countP_cons]
    rcases List.mem_cons.1 hw with rfl | hw
    · have := List.countP_mono_left (l := l) (p := P) (q := Q) (fun a _ h => hPQ a h)
      simp only [hp, hq, Bool.false_eq_true, ↓reduceIte]; omega
    · have ih := countP_lt_of_witness P Q hPQ l w hw hq hp
      by_cases hx : P x = true
      · rw [if_pos hx, if_pos (hPQ x hx)]; omega
      · rw [if_neg hx]
        split <;> omega

/-- A span is nonempty: its start before its end. -/
def spanOk (p : At × At) : Bool := decide (p.1.1 < p.2.1)

/-- **Spans APART** (README gap 5027): each nonempty, each ending at or before the next one starts — so they are
sorted by start, pairwise disjoint, and no instant is covered twice. -/
def apart : List (At × At) → Bool
  | [] => true
  | [p] => spanOk p
  | p :: q :: l => spanOk p && decide (p.2.1 ≤ q.1.1) && apart (q :: l)

/-- **The pieces of `[x, t)` outside spans that are apart, in one pass** (README gap 5027): a span ending at or
before `x` is behind it; one covering `x` moves `x` to its end; one starting after `x` closes a piece at its start
(or `t`), and the pass goes on from its end. -/
def sweep : List (At × At) → At → At → List (At × At)
  | [], x, t => if x.1 < t.1 then [(x, t)] else []
  | p :: ps, x, t =>
    if p.2.1 ≤ x.1 then sweep ps x t
    else if p.1.1 ≤ x.1 then sweep ps p.2 t
    else if t.1 ≤ x.1 then []
    else if t.1 ≤ p.1.1 then [(x, t)]
    else (x, p.1) :: sweep ps p.2 t

/-! The sort is by start (`fun p q => decide (p.1.1 ≤ q.1.1)`), written in `piecesFast` itself: a named comparator
handed to `mergeSort` is reached through a static closure check 12 does not follow (gap 5165). -/

/-- **`pieces`, compiled** (README gap 5027): the nonempty spans as given, when they are apart — a block's own pauses
are, in the order the replay holds them — and else sorted by start; when either is apart, one pass (`sweep`);
otherwise `pieces` itself. -/
def piecesFast (H : List (At × At)) (x t : At) : List (At × At) :=
  if apart (H.filter spanOk) then sweep (H.filter spanOk) x t
  else if apart ((H.filter spanOk).mergeSort (fun p q => decide (p.1.1 ≤ q.1.1))) then sweep ((H.filter spanOk).mergeSort (fun p q => decide (p.1.1 ≤ q.1.1))) x t
  else pieces H x t

theorem apart_spec : ∀ (S : List (At × At)), apart S = true →
    (∀ p ∈ S, p.1.1 < p.2.1) ∧ S.Pairwise (fun p q => p.2.1 ≤ q.1.1)
  | [], _ => ⟨(fun _ h => absurd h List.not_mem_nil), List.Pairwise.nil⟩
  | [p], h => by
    simp only [apart, spanOk, decide_eq_true_eq] at h
    refine ⟨fun q hq => ?_, List.pairwise_singleton _ _⟩
    simp only [List.mem_singleton] at hq; subst hq; exact h
  | p :: q :: l, h => by
    simp only [apart, spanOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp, hpq⟩, hrest⟩ := h
    obtain ⟨h1, h2⟩ := apart_spec (q :: l) hrest
    refine ⟨fun r hr => ?_, List.Pairwise.cons (fun r hr => ?_) h2⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hp
      · exact h1 r hr
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hpq
      · have hq := h1 q List.mem_cons_self
        have hqr := List.rel_of_pairwise_cons h2 hr
        simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hpq hqr hq ⊢; omega

/-- `liftGo` at an instant no span covers stays there. -/
theorem liftGo_of_uncovered (H : List (At × At)) (y : At) (h : ∀ q ∈ H, covers q y = false) :
    ∀ n, liftGo H n y = y
  | 0 => rfl
  | n + 1 => by
    unfold liftGo
    rw [List.find?_eq_none.2 (fun q hq => by simp [h q hq])]

/-- **One more jump than spans still ending after the instant changes nothing.** -/
theorem liftGo_succ (H : List (At × At)) : ∀ (n : Nat) (y : At),
    H.countP (fun q => decide (y.1 < q.2.1)) ≤ n → liftGo H (n + 1) y = liftGo H n y
  | 0, y, hn => by
    have h0 : H.countP (fun q => decide (y.1 < q.2.1)) = 0 := by omega
    rw [List.countP_eq_zero] at h0
    have hu : ∀ q ∈ H, covers q y = false := by
      intro q hq
      have := h0 q hq
      unfold covers; simp only [decide_eq_true_eq] at this; simp [this]
    rw [liftGo_of_uncovered H y hu]; rfl
  | n + 1, y, hn => by
    show liftGo H (n + 2) y = liftGo H (n + 1) y
    unfold liftGo
    split
    · rename_i q hq
      have hqH : q ∈ H := List.mem_of_find?_eq_some hq
      have hqc : covers q y = true := List.find?_some (p := fun p => covers p y) hq
      unfold covers at hqc
      simp only [decide_eq_true_eq] at hqc
      apply liftGo_succ H n q.2
      have hlt := countP_lt_of_witness (fun p => decide (q.2.1 < p.2.1)) (fun p => decide (y.1 < p.2.1))
        (fun x hx => by
          simp only [decide_eq_true_eq] at hx ⊢
          exact Cal.Instant.lt_trans hqc.2 hx)
        H q hqH (by simpa using hqc.2) (by simp [Cal.Instant.lt_irrefl])
      omega
    · rfl

/-- `lift` from an instant one span covers, and no other, is `lift` from that span's end. -/
theorem lift_of_cover (H : List (At × At)) (p : At × At) (y : At) (hp : p ∈ H) (hc : covers p y = true)
    (hu : ∀ q ∈ H, covers q y = true → q = p) : lift H y = lift H p.2 := by
  unfold lift
  obtain ⟨L, hL⟩ : ∃ L, H.length = L + 1 := ⟨H.length - 1, by
    have := List.length_pos_of_mem hp; omega⟩
  rw [hL]
  have hf : H.find? (fun q => covers q y) = some p := by
    cases h : H.find? (fun q => covers q y) with
    | none => rw [List.find?_eq_none] at h; exact absurd hc (by simpa using h p hp)
    | some q => rw [hu q (List.mem_of_find?_eq_some h) (List.find?_some (p := fun q => covers q y) h)]
  have hstep : liftGo H (L + 1) y = liftGo H L p.2 := by
    simp only [liftGo, hf]
  rw [hstep, liftGo_succ H L p.2]
  unfold covers at hc
  simp only [decide_eq_true_eq] at hc
  have hlt := countP_lt_of_witness (fun q => decide (p.2.1 < q.2.1)) (fun q => decide (y.1 < q.2.1))
    (fun x hx => by
      simp only [decide_eq_true_eq] at hx ⊢
      exact Cal.Instant.lt_trans hc.2 hx)
    H p hp (by simpa using hc.2) (by simp [Cal.Instant.lt_irrefl])
  have := List.countP_le_length (p := fun q => decide (y.1 < q.2.1)) (l := H)
  omega

/-- A candidate of `nextStart`. -/
def cand (x t : At) (p : At × At) : Prop := x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1

/-- **`nextStart` with no candidate is `none`.** -/
theorem nextStart_none_of (H : List (At × At)) (x t : At) (h : ∀ q ∈ H, ¬ cand x t q) :
    nextStart H x t = none := by
  let f := fun (acc : Option At) (p : At × At) =>
    if x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1 then
      match acc with
      | some a => if p.1.1 < a.1 then some p.1 else acc
      | none => some p.1
    else acc
  have key : ∀ (l : List (At × At)), (∀ q ∈ l, ¬ cand x t q) → l.foldl f none = none := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons q l ih =>
      intro hl
      rw [List.foldl_cons]
      have : f none q = none := if_neg (hl q List.mem_cons_self)
      rw [this]
      exact ih (fun r hr => hl r (List.mem_cons_of_mem _ hr))
  exact key H h

/-- **`nextStart` is the start of a candidate every other candidate starts after.** -/
theorem nextStart_of_least (H : List (At × At)) (x t : At) (p : At × At) (hp : p ∈ H) (hc : cand x t p)
    (hlt : ∀ q ∈ H, cand x t q → q = p ∨ p.1.1 < q.1.1) : nextStart H x t = some p.1 := by
  let f := fun (acc : Option At) (p : At × At) =>
    if x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1 then
      match acc with
      | some a => if p.1.1 < a.1 then some p.1 else acc
      | none => some p.1
    else acc
  have key : ∀ (l : List (At × At)) (acc : Option At), (∀ q ∈ l, cand x t q → q = p ∨ p.1.1 < q.1.1) →
      (acc = some p.1 ∨ (p ∈ l ∧ (acc = none ∨ ∃ a, acc = some a ∧ p.1.1 < a.1))) → l.foldl f acc = some p.1 := by
    intro l
    induction l with
    | nil =>
      intro acc _ hacc
      rcases hacc with h | ⟨h, -⟩
      · exact h
      · exact absurd h List.not_mem_nil
    | cons q l ih =>
      intro acc hl hacc
      rw [List.foldl_cons]
      have hl' : ∀ r ∈ l, cand x t r → r = p ∨ p.1.1 < r.1.1 := fun r hr => hl r (List.mem_cons_of_mem _ hr)
      have step_none : cand x t q → f none q = some q.1 := fun hq => if_pos hq
      have step_some : ∀ a, cand x t q → f (some a) q = if q.1.1 < a.1 then some q.1 else some a :=
        fun a hq => if_pos hq
      by_cases hq : cand x t q
      · rcases hl q List.mem_cons_self hq with hqp | hpq
        · -- `q` is `p`: whatever came before, `p`'s start is now held
          subst hqp
          apply ih _ hl' (Or.inl ?_)
          rcases hacc with h | ⟨-, h | ⟨a, h, ha⟩⟩
          · subst h; rw [step_some _ hq, if_neg (Cal.Instant.lt_irrefl _)]
          · subst h; exact step_none hq
          · subst h; rw [step_some _ hq, if_pos ha]
        · -- `q` starts after `p`
          have hnot : ¬ q.1.1 < p.1.1 := by
            intro h; simp only [Cal.Instant.lt_iff] at h hpq; omega
          have hpl : p ∈ q :: l → p ∈ l := by
            intro hpm
            rcases List.mem_cons.1 hpm with h | h
            · subst h; exact absurd hpq (Cal.Instant.lt_irrefl _)
            · exact h
          apply ih _ hl'
          rcases hacc with h | ⟨hpm, h | ⟨a, h, ha⟩⟩
          · subst h; left; rw [step_some _ hq, if_neg hnot]
          · subst h
            exact Or.inr ⟨hpl hpm, Or.inr ⟨q.1, step_none hq, hpq⟩⟩
          · subst h
            refine Or.inr ⟨hpl hpm, Or.inr ?_⟩
            rw [step_some _ hq]
            split
            · exact ⟨q.1, rfl, hpq⟩
            · exact ⟨a, rfl, ha⟩
      · have hf : f acc q = acc := if_neg hq
        rw [hf]
        apply ih _ hl'
        rcases hacc with h | ⟨hpm, h⟩
        · exact Or.inl h
        · right
          refine ⟨?_, h⟩
          rcases List.mem_cons.1 hpm with h' | h'
          · subst h'; exact absurd hc hq
          · exact h'
  exact key H none hlt (Or.inr ⟨hp, Or.inl rfl⟩)

/-- `piecesGo` reads its start only through `lift`. -/
theorem piecesGo_congr (H : List (At × At)) (a b t : At) (h : lift H a = lift H b) :
    ∀ n, piecesGo H n a t = piecesGo H n b t
  | 0 => rfl
  | n + 1 => by simp only [piecesGo, h]

/-- **`piecesGo` from an instant no span covers.** -/
theorem piecesGo_of_uncovered (H : List (At × At)) (x t : At) (h : ∀ q ∈ H, covers q x = false) (n : Nat) :
    piecesGo H (n + 1) x t =
      if t.1 ≤ x.1 then [] else
        match nextStart H x t with
        | none => [(x, t)]
        | some s => (x, s) :: piecesGo H n s t := by
  have hl : lift H x = x := liftGo_of_uncovered H x h _
  have ha : H.any (fun p => covers p x) = false := by
    rw [List.any_eq_false]; intro q hq; simp [h q hq]
  simp only [piecesGo, hl, ha, Bool.false_or, decide_eq_true_eq]

/-- **`pieces` over spans that are apart is one pass** (README gap 5027): for `H` whose nonempty spans are, in some
order, the apart list `S`, `piecesGo` from any instant past every span of a prefix of `S`, with fuel for every
candidate start after it, is `sweep` over the rest. -/
theorem piecesGo_eq_sweep (H S : List (At × At)) (hmem : ∀ q, q ∈ S ↔ (q ∈ H ∧ q.1.1 < q.2.1))
    (hS : apart S = true) (t : At) :
    ∀ (S' pre : List (At × At)) (x : At) (n : Nat), S = pre ++ S' → (∀ q ∈ pre, q.2.1 ≤ x.1) →
      H.countP (fun q => decide (x.1 < q.1.1 ∧ q.1.1 < q.2.1)) + 1 ≤ n →
      piecesGo H n x t = sweep S' x t := by
  obtain ⟨hok, hpw⟩ := apart_spec S hS
  -- a span of `H` that covers an instant, or is a candidate, is one of `S`
  have inS_cov : ∀ q ∈ H, ∀ y, covers q y = true → q ∈ S := by
    intro q hq y hc
    unfold covers at hc; simp only [decide_eq_true_eq] at hc
    exact (hmem q).2 ⟨hq, by simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hc ⊢; omega⟩
  have inS_cand : ∀ q ∈ H, ∀ y u, cand y u q → q ∈ S := fun q hq y u hc => (hmem q).2 ⟨hq, hc.2.2⟩
  have anti : ∀ a b : At, a.1 ≤ b.1 →
      H.countP (fun q => decide (b.1 < q.1.1 ∧ q.1.1 < q.2.1)) ≤
        H.countP (fun q => decide (a.1 < q.1.1 ∧ q.1.1 < q.2.1)) := by
    intro a b hab
    apply List.countP_mono_left
    intro q _ hq
    simp only [decide_eq_true_eq] at hq ⊢
    simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hab hq ⊢; omega
  intro S'
  induction S' with
  | nil =>
    intro pre x n hpre hbehind hn
    rw [List.append_nil] at hpre
    subst hpre
    have hu : ∀ q ∈ H, covers q x = false := by
      intro q hq
      cases hc : covers q x with
      | false => rfl
      | true =>
        have hb := hbehind q (inS_cov q hq x hc)
        unfold covers at hc; simp only [decide_eq_true_eq] at hc
        simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hb hc; omega
    have hns : nextStart H x t = none := nextStart_none_of H x t (fun q hq hc => by
      have hb := hbehind q (inS_cand q hq x t hc)
      obtain ⟨h1, -, h3⟩ := hc
      simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hb h1 h3; omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [piecesGo_of_uncovered H x t hu m, hns]
    simp only [sweep]
    by_cases h : t.1 ≤ x.1
    · rw [if_pos h, if_neg (by rw [Cal.Instant.not_lt]; exact h)]
    · rw [if_neg h, if_pos (by rw [← Cal.Instant.not_lt] at h; simpa using h)]
  | cons p ps ih =>
    intro pre x n hpre hbehind hn
    subst hpre
    have hp : p ∈ pre ++ p :: ps := List.mem_append_right _ List.mem_cons_self
    have hpok := hok p hp
    have hpw' := List.pairwise_append.1 hpw
    have hbefore : ∀ a ∈ pre, a.2.1 ≤ p.1.1 := fun a ha => hpw'.2.2 a ha p List.mem_cons_self
    have hafter : ∀ b ∈ ps, p.2.1 ≤ b.1.1 := fun b hb => List.rel_of_pairwise_cons hpw'.2.1 hb
    have hpH : p ∈ H := ((hmem p).1 hp).1
    have hpre' : pre ++ p :: ps = (pre ++ [p]) ++ ps := by simp
    -- every span of `pre ++ [p]` ends at or before `p`'s end
    have hbehind_p : ∀ y : At, x.1 ≤ y.1 → p.2.1 ≤ y.1 → ∀ q ∈ pre ++ [p], q.2.1 ≤ y.1 := by
      intro y hxy hpy q hq
      rcases List.mem_append.1 hq with hq | hq
      · have := hbehind q hq; simp only [Cal.Instant.le_iff] at this hxy ⊢; omega
      · simp only [List.mem_singleton] at hq; subst hq; exact hpy
    -- the one span that covers an instant in `p`
    have only_p : ∀ y : At, p.1.1 ≤ y.1 → y.1 < p.2.1 → ∀ q ∈ H, covers q y = true → q = p := by
      intro y h1 h2 q hq hc
      have hqS := inS_cov q hq y hc
      unfold covers at hc; simp only [decide_eq_true_eq] at hc
      rcases List.mem_append.1 hqS with hq' | hq'
      · have := hbefore q hq'
        simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this hc h1; omega
      · rcases List.mem_cons.1 hq' with rfl | hq'
        · rfl
        · have := hafter q hq'
          simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this hc h2; omega
    have lift_p : ∀ y : At, p.1.1 ≤ y.1 → y.1 < p.2.1 → lift H y = lift H p.2 := by
      intro y h1 h2
      apply lift_of_cover H p y hpH _ (only_p y h1 h2)
      unfold covers; simp only [decide_eq_true_eq]; exact ⟨h1, h2⟩
    simp only [sweep]
    by_cases h1 : p.2.1 ≤ x.1
    · rw [if_pos h1]
      exact ih (pre ++ [p]) x n hpre' (hbehind_p x (instant_le_refl _) h1) hn
    · rw [if_neg h1]
      have hxp2 : x.1 < p.2.1 := by rw [← Cal.Instant.not_lt] at h1; simpa using h1
      by_cases h2 : p.1.1 ≤ x.1
      · -- `p` covers `x`
        rw [if_pos h2, piecesGo_congr H x p.2 t (lift_p x h2 hxp2) n]
        apply ih (pre ++ [p]) p.2 n hpre'
          (hbehind_p p.2 (by simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hxp2 ⊢; omega)
            (instant_le_refl _))
        have := anti x p.2 (by simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hxp2 ⊢; omega)
        omega
      · rw [if_neg h2]
        have hxp1 : x.1 < p.1.1 := by rw [← Cal.Instant.not_lt] at h2; simpa using h2
        -- nothing covers `x`
        have hu : ∀ q ∈ H, covers q x = false := by
          intro q hq
          cases hc : covers q x with
          | false => rfl
          | true =>
            exfalso
            have hqS := inS_cov q hq x hc
            unfold covers at hc; simp only [decide_eq_true_eq] at hc
            rcases List.mem_append.1 hqS with hq' | hq'
            · have := hbehind q hq'
              simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this hc; omega
            · rcases List.mem_cons.1 hq' with rfl | hq'
              · simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hc hxp1; omega
              · have := hafter q hq'
                simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this hc hxp1 hpok; omega
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [piecesGo_of_uncovered H x t hu m]
        by_cases h3 : t.1 ≤ x.1
        · rw [if_pos h3, if_pos h3]
        · rw [if_neg h3, if_neg h3]
          by_cases h4 : t.1 ≤ p.1.1
          · rw [if_pos h4]
            have hns : nextStart H x t = none := nextStart_none_of H x t (fun q hq hc => by
              obtain ⟨c1, c2, c3⟩ := hc
              have hqS := inS_cand q hq x t ⟨c1, c2, c3⟩
              rcases List.mem_append.1 hqS with hq' | hq'
              · have := hbehind q hq'
                simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this c1 c3; omega
              · rcases List.mem_cons.1 hq' with rfl | hq'
                · simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at h4 c2; omega
                · have := hafter q hq'
                  simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this h4 c2 hpok; omega)
            rw [hns]
          · rw [if_neg h4]
            have hpt : p.1.1 < t.1 := by rw [← Cal.Instant.not_lt] at h4; simpa using h4
            have hns : nextStart H x t = some p.1 := by
              apply nextStart_of_least H x t p hpH ⟨hxp1, hpt, hpok⟩
              intro q hq hc
              obtain ⟨c1, c2, c3⟩ := hc
              have hqS := inS_cand q hq x t ⟨c1, c2, c3⟩
              rcases List.mem_append.1 hqS with hq' | hq'
              · have := hbehind q hq'
                simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this c1 c3; omega
              · rcases List.mem_cons.1 hq' with rfl | hq'
                · exact Or.inl rfl
                · have := hafter q hq'
                  right
                  simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at this hpok ⊢; omega
            simp only [hns]
            congr 1
            rw [piecesGo_congr H p.1 p.2 t (lift_p p.1 (instant_le_refl _) hpok) m]
            apply ih (pre ++ [p]) p.2 m hpre'
              (hbehind_p p.2 (by simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hxp2 ⊢; omega)
                (instant_le_refl _))
            have h5 := anti p.1 p.2 (by simp only [Cal.Instant.le_iff, Cal.Instant.lt_iff] at hpok ⊢; omega)
            have h6 := countP_lt_of_witness (fun q => decide (p.1.1 < q.1.1 ∧ q.1.1 < q.2.1))
              (fun q => decide (x.1 < q.1.1 ∧ q.1.1 < q.2.1))
              (fun q hq => by
                simp only [decide_eq_true_eq] at hq ⊢
                simp only [Cal.Instant.lt_iff] at hq hxp1 ⊢; omega)
              H p hpH (by simp only [decide_eq_true_eq]; exact ⟨hxp1, hpok⟩)
              (by simp [Cal.Instant.lt_irrefl])
            omega

/-- **`pieces` is `piecesFast`** (README gap 5027): `@[csimp]` — the compiled code runs the one pass whenever the
spans, sorted, are apart. -/
@[csimp] theorem pieces_eq_piecesFast : @pieces = @piecesFast := by
  funext H x t
  have hfuel := List.countP_le_length (p := fun q => decide (x.1 < q.1.1 ∧ q.1.1 < q.2.1)) (l := H)
  unfold piecesFast
  split
  · rename_i h
    refine (piecesGo_eq_sweep H _ (fun q => ?_) h t _ [] x (H.length + 1) rfl (fun _ hq => absurd hq List.not_mem_nil)
      (by omega))
    rw [List.mem_filter]
    simp [spanOk]
  · split
    · rename_i h
      refine (piecesGo_eq_sweep H _ (fun q => ?_) h t _ [] x (H.length + 1) rfl (fun _ hq => absurd hq List.not_mem_nil)
        (by omega))
      rw [List.mem_mergeSort, List.mem_filter]
      simp [spanOk]
    · rfl


/-- **C5: `t + Duration::minutes(m)`** (a break's end): chrono's `NaiveTime::overflowing_add_signed`
with a positive whole-minute delta.  A leap second is left as its own second before adding
(`frac -= 1_000_000_000`); a zero delta leaves the instant, leap second and all.  No overflow: a stamp's
year is at most 9999 and `u32::MAX` minutes is under 8,200 years, inside chrono's range. -/
def addMinutes (t : Cal.Instant) (m : Nat) : Cal.Instant :=
  if m = 0 then t
  else if 1000000000 ≤ t.ns then ⟨t.sec + 60 * m, t.ns - 1000000000⟩
  else ⟨t.sec + 60 * m, t.ns⟩

/-- **An entry's line header** (§8.2's `header`; fork `ViewRow` less its entry): its physical line, its tag
(fork `Event::name`), its primary id (fork `Event::primary_id`), whether the undo mask cancels it, and (C6) its
stamp as written, from which the display (`LogStamp.displayStamp`, fork `ViewRow::display`) is rendered at
emission.  The day is the effect's (`Effect.header d h`). -/
structure HeaderRec where
  line : Nat
  tag : List Char
  id : Option Id
  cancelled : Bool
  t : Cal.VInstant
  off : Cal.VOffset
deriving DecidableEq, Repr

/-- **C6: an entry's header**, with the mask bit `c`. -/
def HeaderRec.of (e : Entry) (c : Bool) : HeaderRec := ⟨e.line, e.ev.tag, e.ev.primaryId, c, e.t, e.off⟩

/-- Not earlier by instant (fork `DaySeam.last_t`'s `t >= l`: a later line wins a tie). -/
def atLe (a b : At) : Bool := decide (a.1 ≤ b.1)

/-- **C6: a mark of a day's idle time** (fork `IdleMark`, R2): a `pause`, `interrupt`, `unpause` or `resume` at
its stamp, or a `break` at its stamp with the `actual_min` it was logged with. -/
inductive IdleMark
  | pause (t : At)
  | interrupt (t : At)
  | unpause (t : At)
  | resume (t : At)
  | brk (t : At) (actualMin : Option Nat)
deriving DecidableEq, Repr

/-- **C6: a day's seam facts** (fork `DaySeam`, Phase R's R1, R2 and R4): the since-break anchor (the last
`break`'s end, else the day's first `start`), the idle marks (newest first; the facts put them back in file
order), and `last_t`, the latest stamp by instant over the day's survivors of any kind, a later line winning a
tie.  Every surviving entry writes its day's seam, so a day holding only a `note` has a seam and no
`DayAcc`. -/
structure SeamAcc where
  sinceBreak : Option At
  idleMarks : List IdleMark
  lastT : Option At
deriving DecidableEq, Repr

def SeamAcc.empty : SeamAcc := ⟨none, [], none⟩

/-- What an entry's kind writes to its day's seam beyond `last_t` (a break: its planned and logged minutes, gap 4550). -/
inductive SeamKind
  | other
  | brk (planned : Nat) (actualMin : Option Nat)
  | start
  | pause
  | interrupt
  | unpause
  | resume
deriving DecidableEq, Repr

/-- **C6: one survivor's write to its day's seam**: its stamp and its kind's part. -/
structure SeamOp where
  t : At
  kind : SeamKind
deriving DecidableEq, Repr

/-- Fork `Machine::step`'s seam half, for one survivor whose stamp is `op.t` (a break's anchor: `seam_since_break_is_brkEnd`). -/
def SeamOp.apply (op : SeamOp) (a : SeamAcc) : SeamAcc :=
  let a := { a with lastT := lastMaxStep atLe a.lastT op.t }
  match op.kind with
  | .other => a
  | .brk pl am => { a with sinceBreak := some (addMinutes op.t.1 (am.getD pl), op.t.2), idleMarks := .brk op.t am :: a.idleMarks }
  | .start =>
    match a.sinceBreak with
    | none => { a with sinceBreak := some op.t }
    | some _ => a
  | .pause => { a with idleMarks := .pause op.t :: a.idleMarks }
  | .interrupt => { a with idleMarks := .interrupt op.t :: a.idleMarks }
  | .unpause => { a with idleMarks := .unpause op.t :: a.idleMarks }
  | .resume => { a with idleMarks := .resume op.t :: a.idleMarks }

/-- The seam kind of an event (fork `step`'s seam match). -/
def seamKindOf : Event → SeamKind
  | .brk planned actual _ => .brk planned.val (actual.map (·.val))
  | .start .. => .start
  | .pause _ => .pause
  | .interrupt _ => .interrupt
  | .unpause _ => .unpause
  | .resume _ _ => .resume
  | _ => .other

/-- The bookkeeping every surviving entry writes: fork `last_effective_t` (the last survivor's `t` in
file order) and how many survivors were stepped. -/
structure GlobalAcc where
  lastEffective : Option At
  entries : Nat
deriving DecidableEq, Repr

/-- **The replay state.**  `days` and `items` are fork `Replay.days` and `Replay.items`, `itemDays` is
every `ItemReplay.minutes_by_day` keyed `(day, id)`, and the observation lists are newest first.  Days,
items and item-days are bucketed (`HMap`): C5's wake arm creates a day per wake, and a log of wakes on
as many dates would make an association list's absent-key scan quadratic. -/
structure State where
  days : HMap Nat DayAcc
  items : HMap Id ItemAcc
  itemDays : HMap (Nat × Id) Nat
  energy : List EnergyObs
  durations : List DurationObs
  interrupts : List Interruption
  headers : List (Nat × HeaderRec)
  machine : Machine
  global : GlobalAcc
  /-- C4: fork `last_done` (its keys are fork `done_items`, which `mark_done` fills with it) -/
  lastDone : HMap Id At
  /-- C4: fork `done_dates`, one pair per `(date, id)` -/
  doneDates : HMap (Nat × Id) Unit
  /-- C4: fork `instances`, keyed `(item, inst)` -/
  instances : HMap (List Char × List Char) InstRec
  /-- C4: fork `LatestNamed` per `(name, id?)` of fork `events` -/
  named : HMap (List Char × Option Id) NamedRec
  /-- C4: fork `warnings`, newest first -/
  rwarns : List RWarn
  /-- C5: fork `demotions`, each with its day, newest first -/
  demotions : List (Nat × Demotion)
  /-- C5: fork `closes`, each with its day, newest first -/
  closes : List (Nat × CloseRec)
  /-- C5: fork `dropped_items` -/
  dropped : HMap Id Unit
  /-- C5: fork `Replay.longest_leak`, the first maximum -/
  longestLeak : Option LeakRec
  /-- C5: fork `Replay.unknown` -/
  unknown : Nat
  /-- C6: fork `Replay.seams`, per day -/
  seams : HMap Nat SeamAcc
deriving DecidableEq, Repr

/-- The empty state, its bucketed maps sized for `n` entries. -/
def State.init (n : Nat) : State :=
  ⟨HMap.empty n, HMap.empty n, HMap.empty n, [], [], [], [], ⟨none, none, none, [], none, [], none⟩, ⟨none, 0⟩,
    HMap.empty n, HMap.empty n, HMap.empty n, HMap.empty n, [], [], [], HMap.empty n, none, 0, HMap.empty n⟩

/-! ### Effects and keys (§8.2) -/

/-- What an effect does to one day's record. -/
inductive DayOp
  /-- `first_start` if unset, and a `StartRecord` pushed -/
  | start (r : StartRec)
  /-- fork `credit`'s day half: `block_min`, then `minutes_by_ci`/`load_fifths` or `ci_unknown` -/
  | credit (id : Id) (min : Nat) (ci : Option U8)
  /-- fork `uncredit_cut`'s day half; a day that does not exist is left absent -/
  | uncredit (id : Id) (min : Nat)
  | blockDone
  | done (id : Id)
  | segment (s : Segment)
  /-- **D99 (README gap 4520a): a segment un-drawn** — the first one equal to `s` is removed; a day that does not exist
  is left absent.  A late mark that moves a piece of a block drawn earlier writes it, and only for a segment the replay
  wrote there (`redraw`). -/
  | unsegment (s : Segment)
  /-- **D100 (README gap 4520b): a closed block's credit netted** — `k` of its minutes taken back from the day, from the
  ci's minutes (`some`, a `done`'s credit) or the id's ci-unknown minutes (`none`, a cut's), never more than the day
  holds there, so the day still balances; and, for a `done` that pushed a duration observation (`line`), `k` more of it
  netted (`DayAcc.durNet`).  A day that does not exist is left absent. -/
  | net (id : Id) (ci : Option U8) (k : Nat) (line : Option Nat)
  /-- **D137 (README gaps 5504 and 5302): a netting of a duration observation given back** — `k` of the minutes netted
  from the duration observation of the `done` at `line` (`DayAcc.durNet`) returned, never below none, when the `break`
  line that ends a running break gives a closed block back what the running break took (`giveOne`; its credit comes back
  as a `credit`).  A day that does not exist is left absent. -/
  | undur (line : Option Nat) (k : Nat)
  | lost (min : Nat) (dropped : List Id)
  /-- C5: `wake`, `slept_min` and `onset_min`, if the day has no wake yet -/
  | wake (t : At) (slept : Nat) (onset : Option Nat)
  /-- C5: the first `arrive` sets the arrival, location, window and budget; every one changes the location -/
  | arrive (t : At) (loc : List Char) (window : List Char × List Char) (budget : Nat)
  /-- C5: a `loc` -/
  | loc (t : At) (loc : List Char)
  /-- C5: a `BreakRecord` -/
  | brk (r : BreakRec)
  /-- C5: an `IdleRecord`, and a `leak`'s minutes and the day's longest -/
  | idle (r : IdleRec)
  /-- C5: `routine_min += m` -/
  | routineMin (m : Nat)
  /-- C5: a `plan`; D108: the hysteresis input it carries; W-49 track L: its stamp and its line, so the day keeps the
  latest calendar date's last `plan` and last input (`notBefore`, D125) -/
  | plan (hash : List Char) (replans drift : Nat) (yesterday : List (Id × U8)) (t : At) (line : Nat)
deriving DecidableEq, Repr

/-- **D100's credit half** (`DayOp.net`): `k` minutes off the day's block minutes and off the credit's own bucket — the
ci's minutes and their fifths for a `done`'s credit, the id's ci-unknown minutes for a cut's — never more than that
bucket holds. -/
def DayAcc.netCredit (id : Id) (ci : Option U8) (k : Nat) (a : DayAcc) : DayAcc :=
  match ci with
  | some c =>
    { a with blockMin := a.blockMin - min k (a.byCi.get (Nat.min c.val 5)),
             byCi := a.byCi.sub (Nat.min c.val 5) (min k (a.byCi.get (Nat.min c.val 5))),
             loadFifths := a.loadFifths - min k (a.byCi.get (Nat.min c.val 5)) * Nat.min c.val 5 }
  | none =>
    { a with blockMin := a.blockMin - min k ((a.ciUnknown.get id).getD 0),
             ciUnknown := a.ciUnknown.alter id (fun o =>
               match o with
               | some v => if v - min k v = 0 then none else some (v - min k v)
               | none => none) }

/-- **The calendar date a stamp is on**, by its own offset (README gap 5300): the date its local clock reads — what the
host's `with_timezone(&tz).date_naive()` reads of a line it wrote in its zone. -/
def stampDate (t : At) : Nat := Cal.localSecAt t.2 t.1 / 86400

/-- **A stamp no earlier in calendar date than a slot's** (README gap 5300, W-49 track L): an empty slot takes any
line, and a filled one is moved by a line of its date or a later one — never by a line of an earlier date, so a clock
behind the log across midnight moves no later date's answer. -/
def notBefore (o : Option At) (t : At) : Bool :=
  match o with
  | none => true
  | some u => decide (stampDate u ≤ stampDate t)

/-- **D100's duration half** (`DayOp.net`): `k` more minutes netted from the duration observation of the `done` at
`line`, when it pushed one. -/
def DayAcc.netDurOf (line : Option Nat) (k : Nat) (a : DayAcc) : DayAcc :=
  match line with
  | some l => { a with durNet := a.durNet.alter l (fun o => some (o.getD 0 + k)) }
  | none => a

/-- **D137's duration half** (`DayOp.undur`): `k` of the minutes netted from the duration observation of the `done` at
`line` given back, when it pushed one. -/
def DayAcc.undurOf (line : Option Nat) (k : Nat) (a : DayAcc) : DayAcc :=
  match line with
  | some l => { a with durNet := a.durNet.alter l (fun o => some (o.getD 0 - k)) }
  | none => a

def DayOp.apply : DayOp → DayAcc → DayAcc
  | .start r, a => { a with firstStart := a.firstStart.or (some r.t), starts := r :: a.starts }
  | .credit id min ci, a =>
    match ci with
    | some c =>
      { a with blockMin := a.blockMin + min, byCi := a.byCi.add (Nat.min c.val 5) min,
               loadFifths := a.loadFifths + min * Nat.min c.val 5 }
    | none =>
      if 0 < min then
        { a with blockMin := a.blockMin + min,
                 ciUnknown := a.ciUnknown.alter id (fun o => some (o.getD 0 + min)) }
      else { a with blockMin := a.blockMin + min }
  | .uncredit id min, a =>
    { a with blockMin := a.blockMin - min,
             ciUnknown := a.ciUnknown.alter id (fun o =>
               match o with
               | some v => if v - min = 0 then none else some (v - min)
               | none => none) }
  | .blockDone, a => { a with blocksDone := a.blocksDone + 1 }
  | .done id, a => { a with done := id :: a.done }
  | .segment s, a => { a with segments := s :: a.segments }
  | .unsegment s, a => { a with segments := a.segments.erase s }
  | .net id ci k line, a => DayAcc.netDurOf line k (DayAcc.netCredit id ci k a)
  | .undur line k, a => DayAcc.undurOf line k a
  | .lost min dropped, a => { a with lostMin := a.lostMin + min, dropped := dropped.reverse ++ a.dropped }
  | .wake t slept onset, a =>
    match a.wake with
    | none => { a with wake := some t, sleptMin := some slept, onsetMin := onset }
    | some _ => a
  | .arrive t lc w bu, a =>
    match a.arrival with
    | none => { a with arrival := some t, loc := some lc, window := some w, budget := some bu,
                       locChanges := (t, lc) :: a.locChanges }
    | some _ => { a with locChanges := (t, lc) :: a.locChanges }
  | .loc t lc, a => { a with locChanges := (t, lc) :: a.locChanges }
  | .brk r, a => { a with breaks := r :: a.breaks }
  | .idle r, a =>
    if r.attributed = "leak".toList then
      { a with idle := r :: a.idle, leakMin := a.leakMin + r.min, longestLeak := Nat.max a.longestLeak r.min }
    else { a with idle := r :: a.idle }
  | .routineMin m, a => { a with routineMin := a.routineMin + m }
  | .plan hash replans drift ys t line, a =>
    { a with plans := a.plans + 1, replansToday := Nat.max a.replansToday replans, driftMin := a.driftMin + drift,
             lastPlanHash := some hash,
             planAt := if notBefore a.planAt t then some t else a.planAt,
             planHash := if notBefore a.planAt t then some hash else a.planHash,
             planLine := if notBefore a.planAt t then some line else a.planLine,
             lateAt := if !ys.isEmpty && notBefore a.lateAt t then some t else a.lateAt,
             lateLine := if !ys.isEmpty && notBefore a.lateAt t then some line else a.lateLine,
             late := if !ys.isEmpty && notBefore a.lateAt t then ys else a.late }

/-- Fork `day_mut` creates the day; `uncredit_cut`'s `days.get_mut` does not. -/
def DayOp.alterFn (op : DayOp) : Option DayAcc → Option DayAcc
  | some a => some (op.apply a)
  | none =>
    match op with
    | .uncredit _ _ => none
    | .unsegment _ => none
    | .net _ _ _ _ => none
    | .undur _ _ => none
    | _ => some (op.apply DayAcc.empty)

/-- What an effect does to one item's record. -/
inductive ItemOp
  | credit (min : Nat)
  /-- `uncredit_cut`'s `items.get_mut`: an absent item stays absent -/
  | uncredit (min : Nat)
  | block
  | doneAt (t : At)
  | partialDoneAt (t : At)
  | stop
  | extend (min : Nat)
deriving DecidableEq, Repr

def ItemOp.apply : ItemOp → ItemAcc → ItemAcc
  | .credit min, a => { a with minutes := a.minutes + min }
  | .uncredit min, a => { a with minutes := a.minutes - min }
  | .block, a => { a with blocks := a.blocks + 1 }
  | .doneAt t, a => { a with doneAt := t :: a.doneAt }
  | .partialDoneAt t, a => { a with partialDoneAt := t :: a.partialDoneAt }
  | .stop, a => { a with stops := a.stops + 1 }
  | .extend min, a => { a with extendedMin := a.extendedMin + min }

def ItemOp.alterFn (op : ItemOp) : Option ItemAcc → Option ItemAcc
  | some a => some (op.apply a)
  | none =>
    match op with
    | .uncredit _ => none
    | _ => some (op.apply ItemAcc.empty)

/-- An observation effect (§11.2). -/
inductive Obs
  | energy (o : EnergyObs)
  | duration (o : DurationObs)
deriving DecidableEq, Repr

def Obs.day : Obs → Nat
  | .energy o => o.day
  | .duration o => o.day

/-- **An effect** (§8.2): one write, to the key `Effect.key` names. -/
inductive Effect
  | dayAdd (d : Nat) (op : DayOp)
  | header (d : Nat) (h : HeaderRec)
  | itemAdd (i : Id) (op : ItemOp)
  /-- `minutes_by_day[d] += m`, the key inserted even at 0 -/
  | itemDay (i : Id) (d : Nat) (m : Nat)
  /-- `uncredit_cut`: `minutes_by_day[d] -= m` (saturating), removed at 0, only if the item exists -/
  | itemDaySub (i : Id) (d : Nat) (m : Nat)
  | obs (o : Obs)
  | interruption (r : Interruption)
  | machine (m : Machine)
  | global (t : At)
  /-- C4, fork `mark_done`'s `done_items` and `last_done`: the latest by instant, the first of equal
  instants kept -/
  | markDone (i : Id) (t : At)
  /-- C4, fork `mark_done`'s `done_dates[id].insert(date)` -/
  | doneDate (i : Id) (d : Nat)
  /-- C4, `instances[item][inst] = r`: the last in file order wins -/
  | inst (item inst : List Char) (r : InstRec)
  /-- C4, a `tm event` occurrence: its line, its stamp and its local date in the zone -/
  | named (name : List Char) (id : Option Id) (line : Nat) (t : At) (date : Nat)
  /-- C4, a replay warning -/
  | rwarn (w : RWarn)
  /-- C5, a `demote` on its day -/
  | demote (d : Nat) (r : Demotion)
  /-- C5, a `close` on its day -/
  | close (d : Nat) (r : CloseRec)
  /-- C5, `dropped_items.insert(id)` -/
  | drop (i : Id)
  /-- C5, a `leak` idle gap: the global longest leak is replaced only by a longer one (the first maximum wins) -/
  | leak (r : LeakRec)
  /-- C5, `unknown += 1` -/
  | unknown
  /-- C6, a survivor's write to its day's seam (fork `DaySeam`) -/
  | seam (d : Nat) (op : SeamOp)
deriving DecidableEq, Repr

/-- **The keys** (§8.2's block-family and completion keys; C5 adds the record keys).  An instance is
keyed by the date its `inst` names (`instDate`, a window fact) or, when `inst` is not a date, by
`instOther` (an all-time fact). -/
inductive Key
  | day (d : Nat)
  | itemDay (i : Id) (d : Nat)
  | item (i : Id)
  | machine
  | global
  | doneDate (i : Id) (d : Nat)
  | instDate (item inst : List Char) (d : Nat)
  | instOther (item inst : List Char)
  | named (name : List Char) (id : Option Id)
deriving DecidableEq, Repr

/-- The key an effect writes.  Every dated output names its day (CRIT 9). -/
def Effect.key : Effect → Key
  | .dayAdd d _ => .day d
  | .header d _ => .day d
  | .itemAdd i _ => .item i
  | .itemDay i d _ => .itemDay i d
  | .itemDaySub i d _ => .itemDay i d
  | .obs o => .day o.day
  | .interruption r => .day r.day
  | .machine _ => .machine
  | .global _ => .global
  | .markDone i _ => .item i
  | .doneDate i d => .doneDate i d
  | .inst item ins _ =>
    match Log.instDate? ins with
    | some d => .instDate item ins d
    | none => .instOther item ins
  | .named name id _ _ _ => .named name id
  | .rwarn _ => .global
  | .demote d _ => .day d
  | .close d _ => .day d
  | .drop i => .item i
  | .leak _ => .global
  | .unknown => .global
  | .seam d _ => .day d

def Effect.isHeader : Effect → Bool
  | .header _ _ => true
  | _ => false

/-- What a day key holds: its record, and the observations, interruptions, headers, (C5) demotions and
closes dated to it. -/
structure DayView where
  acc : Option DayAcc
  /-- C6 -/
  seam : Option SeamAcc
  energy : List EnergyObs
  durations : List DurationObs
  interrupts : List Interruption
  headers : List HeaderRec
  demotions : List Demotion
  closes : List CloseRec
deriving DecidableEq, Repr

inductive Val
  | day (v : DayView)
  | item (a : Option ItemAcc) (lastDone : Option At) (dropped : Option Unit)
  | itemDay (m : Option Nat)
  | machine (m : Machine)
  | global (g : GlobalAcc) (warnings : List RWarn) (leak : Option LeakRec) (unknown : Nat)
  | doneDate (u : Option Unit)
  | inst (r : Option InstRec)
  | named (r : Option NamedRec)
deriving DecidableEq, Repr

/-- **The value at a key**: what a sealed day (G3) or a query reads. -/
def State.valueAt (st : State) : Key → Val
  | .day d => .day ⟨st.days.get d, st.seams.get d, st.energy.filter (fun o => decide (o.day = d)),
      st.durations.filter (fun o => decide (o.day = d)), st.interrupts.filter (fun r => decide (r.day = d)),
      (st.headers.filter (fun h => decide (h.1 = d))).map Prod.snd,
      (st.demotions.filter (fun p => decide (p.1 = d))).map Prod.snd,
      (st.closes.filter (fun p => decide (p.1 = d))).map Prod.snd⟩
  | .itemDay i d => .itemDay (st.itemDays.get (d, i))
  | .item i => .item (st.items.get i) (st.lastDone.get i) (st.dropped.get i)
  | .machine => .machine st.machine
  | .global => .global st.global st.rwarns st.longestLeak st.unknown
  | .doneDate i d => .doneDate (st.doneDates.get (d, i))
  | .instDate item inst d => .inst (if Log.instDate? inst = some d then st.instances.get (item, inst) else none)
  | .instOther item inst => .inst (if Log.instDate? inst = none then st.instances.get (item, inst) else none)
  | .named name id => .named (st.named.get (name, id))

def applyEffect (st : State) : Effect → State
  | .dayAdd d op => { st with days := st.days.alter d op.alterFn }
  | .header d h => { st with headers := (d, h) :: st.headers }
  | .itemAdd i op => { st with items := st.items.alter i op.alterFn }
  | .itemDay i d m => { st with itemDays := st.itemDays.alter (d, i) (fun o => some (o.getD 0 + m)) }
  | .itemDaySub i d m =>
    match st.items.get i with
    | some _ =>
      { st with itemDays := st.itemDays.alter (d, i) (fun o =>
          match o with
          | some v => if v - m = 0 then none else some (v - m)
          | none => none) }
    | none => st
  | .obs (.energy o) => { st with energy := o :: st.energy }
  | .obs (.duration o) => { st with durations := o :: st.durations }
  | .interruption r => { st with interrupts := r :: st.interrupts }
  | .machine m => { st with machine := m }
  | .global t => { st with global := ⟨some t, st.global.entries + 1⟩ }
  | .markDone i t => { st with lastDone := st.lastDone.alter i (fun o => lastMaxStep instLt o t) }
  | .doneDate i d => { st with doneDates := st.doneDates.alter (d, i) (fun _ => some ()) }
  | .inst item inst r => { st with instances := st.instances.alter (item, inst) (fun _ => some r) }
  | .named name id line t date =>
    { st with named := st.named.alter (name, id) (fun o => some (NamedRec.push o line t date)) }
  | .rwarn w => { st with rwarns := w :: st.rwarns }
  | .demote d r => { st with demotions := (d, r) :: st.demotions }
  | .close d r => { st with closes := (d, r) :: st.closes }
  | .drop i => { st with dropped := st.dropped.alter i (fun _ => some ()) }
  | .leak r => { st with longestLeak := lastMaxStep leakLt st.longestLeak r }
  | .unknown => { st with unknown := st.unknown + 1 }
  | .seam d op => { st with seams := st.seams.alter d (fun o => some (op.apply (o.getD SeamAcc.empty))) }

/-- Apply effects in order (a `foldl`, D9-21). -/
def applyEffects (st : State) (fx : List Effect) : State := fx.foldl applyEffect st

/-! ### The helpers, ported by name -/

/-- **The earlier of two instants**, the first on a tie. -/
def minAt (a b : At) : At := if a.1 ≤ b.1 then a else b

/-- **Where the open block's clock stopped and has not restarted** (the owner's **D99**, README gap 4520a, W-47 track
K, parity P104): the earlier of its open pause (`pausedAt` while `paused`) and the open interruption's start — `none`
while its clock runs. -/
def openStop (b : Block) (m : Machine) : Option At :=
  match (if b.paused then b.pausedAt else none), m.interrupt with
  | some p, some i => some (minAt p i.1)
  | some p, none => some p
  | none, some i => some i.1
  | none, none => none

/-- **The spans the block's clock nets** (D99): its own closed idle spans (`Block.idle`, every pause it drew and every
interruption that closed while it was open) and every break the machine holds on its ledger days (`spansFor`, the
owner's D94). -/
def blockSpans (b : Block) (m : Machine) : List (At × At) := b.idle ++ spansFor m.brks b.day

/-- **Where a clock begun at `x` runs from once every span is behind it** (D99): `x`, or the latest end of a nonempty
span after it, which no span covers. -/
def runFrom : List (At × At) → At → At
  | [], x => x | p :: H, x => runFrom H (if p.1.1 < p.2.1 ∧ x.1 < p.2.1 then p.2 else x)

/-- **The running break's span up to `E`** (README gap 5180, W-49 track L, the owner's D94 and D100: a block and a break
are read one way on every log): `[s, E)` for the break a `break_start` opened at `s` and no `break` line has ended
(`Machine.brkOpen`), on a ledger day at or after the block's own (`spansFor`'s rule, which the `break` line that ends it
will be held under) — so a block stopped while the break runs reads now what it will read once the break's line arrives:
nothing from `s` on.  Empty with no break running. -/
def runSpan (b : Block) (m : Machine) (E : At) : List (At × At) :=
  match m.brkOpen with
  | some o => if b.day ≤ o.day then [(o.s, E)] else []
  | none => []

/-- **Where an open block's drawing ends** (D99): its open stop, or, while its clock runs, where it runs from. -/
def openEnd (b : Block) (m : Machine) : At :=
  match openStop b m with
  | some q => q
  | none => runFrom (blockSpans b m) b.started

/-- **The pieces an open block has drawn** (D99): the complement of its spans from its start up to its open stop, or,
while its clock runs, up to where it runs from — so the stretch it is running is the one piece not drawn.  **Since README
gap 5180** (W-49 track L) the spans include the running break's, up to that end (`runSpan`): a block paused or
interrupted while a logged break runs draws nothing from the break's start on, as it will once the break's line is
logged (`brkFx` re-draws it then over the held break, and nothing moves). -/
def openPieces (b : Block) (m : Machine) : List (At × At) :=
  pieces (blockSpans b m ++ runSpan b m (openEnd b m)) b.started (openEnd b m)

/-- **The pieces a block cut at `t` worked** (D99): the complement of its spans from its start up to `t`, or up to its
open stop when that is earlier. -/
def cutPieces (b : Block) (m : Machine) (t : At) : List (At × At) :=
  pieces (blockSpans b m) b.started
    (match openStop b m with
     | some q => minAt q t
     | none => t)

/-- **Pieces' worked minutes** — site R8 (quirk Q6c, gap 83): each piece's own seconds over 60
(`Cal.minutesBetween`, `num_minutes().max(0)`), summed, as fork `close_sub` truncated each sub-segment. -/
def minutesOf (P : List (At × At)) : Nat := (P.map (fun p => Cal.minutesBetween p.1.1 p.2.1)).sum

/-- Two stamps are one: the same instant at the same offset, compared field by field. -/
def atEq (a b : At) : Bool :=
  a.1.sec == b.1.sec && a.1.ns == b.1.ns && a.2.west == b.2.west && a.2.sec == b.2.sec

theorem atEq_iff (a b : At) : atEq a b = true ↔ a = b := by
  obtain ⟨⟨as, an⟩, ⟨aw, ao⟩⟩ := a
  obtain ⟨⟨bs, bn⟩, ⟨bw, bo⟩⟩ := b
  simp [atEq, and_assoc]

/-- Whether a drawn piece is the span `q`. -/
def samePiece (p : Piece) (q : At × At) : Bool := atEq p.s q.1 && atEq p.e q.2

/-- **Re-draw a block's pieces as `P`** (the owner's D99): every piece drawn before that `P` does not hold is un-drawn
from the day it was filed under (`DayOp.unsegment`), every span of `P` not drawn before is drawn on the day of its
start, and the pieces drawn after are `P`'s — each one drawn before keeping the day it was filed under. -/
def redraw (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) : List Piece × List Effect :=
  (P.map (fun q => match old.find? (fun p => samePiece p q) with
      | some p => p
      | none => ⟨q.1, q.2, dy q.1.1⟩),
    (old.filter (fun p => !P.any (samePiece p))).map
        (fun p => Effect.dayAdd p.day (.unsegment ⟨p.s, p.e, .block id⟩)) ++
      (P.filter (fun q => !old.any (fun p => samePiece p q))).map
        (fun q => Effect.dayAdd (dy q.1.1) (.segment ⟨q.1, q.2, .block id⟩)))

/-! ### `redraw`, compiled (README gap 5027) -/

/-- Start instants strictly increasing: the shape `pieces` draws (`sweep`) and a block's drawn pieces keep. -/
def startsUp : List (At × At) → Bool
  | [] => true
  | [_] => true
  | p :: q :: l => decide (p.1.1 < q.1.1) && startsUp (q :: l)

/-- **`redraw`'s pieces, in one merge** (README gap 5027): over old pieces and new spans each with start instants
strictly increasing, the pieces drawn (in the new spans' order), the old pieces no new span is (in their order), and the
new spans no old piece is (in theirs).  `redrawWalkGo`'s fuel is one step per element, so it reduces (a `decide` reads
it) and is always enough (`redrawWalkGo_spec`). -/
def redrawWalkGo (dy : Cal.Instant → Nat) : Nat → List Piece → List (At × At) → List Piece × List Piece × List (At × At)
  | _, [], P => (P.map (fun q => ⟨q.1, q.2, dy q.1.1⟩), [], P)
  | _, old, [] => ([], old, [])
  | 0, old, P => ([], old, P)
  | n + 1, p :: os, q :: qs =>
    if p.s.1 < q.1.1 then
      let r := redrawWalkGo dy n os (q :: qs)
      (r.1, p :: r.2.1, r.2.2)
    else if q.1.1 < p.s.1 then
      let r := redrawWalkGo dy n (p :: os) qs
      (⟨q.1, q.2, dy q.1.1⟩ :: r.1, r.2.1, q :: r.2.2)
    else if samePiece p q then let r := redrawWalkGo dy n os qs; (p :: r.1, r.2.1, r.2.2)
    else let r := redrawWalkGo dy n os qs; (⟨q.1, q.2, dy q.1.1⟩ :: r.1, p :: r.2.1, q :: r.2.2)
def redrawWalk (dy : Cal.Instant → Nat) (old : List Piece) (P : List (At × At)) :
    List Piece × List Piece × List (At × At) := redrawWalkGo dy (old.length + P.length) old P

/-- **`redraw`, compiled** (README gap 5027): the one merge when both lists' starts strictly increase, `redraw`
itself otherwise. -/
def redrawFast (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) :
    List Piece × List Effect :=
  if startsUp (old.map (fun p => (p.s, p.e))) && startsUp P then
    let r := redrawWalk dy old P
    (r.1, r.2.1.map (fun p => Effect.dayAdd p.day (.unsegment ⟨p.s, p.e, .block id⟩)) ++
      r.2.2.map (fun q => Effect.dayAdd (dy q.1.1) (.segment ⟨q.1, q.2, .block id⟩)))
  else redraw dy id old P

theorem samePiece_start (p : Piece) (q : At × At) (h : samePiece p q = true) : p.s.1 = q.1.1 := by
  unfold samePiece at h
  simp only [Bool.and_eq_true] at h
  have := (atEq_iff _ _).1 h.1
  rw [this]

theorem startsUp_cons {p : At × At} {l : List (At × At)} (h : startsUp (p :: l) = true) :
    startsUp l = true ∧ ∀ q ∈ l, p.1.1 < q.1.1 := by
  induction l generalizing p with
  | nil => exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | cons q l ih =>
    simp only [startsUp, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨-, h3⟩ := ih h2
    refine ⟨h2, fun r hr => ?_⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h1
    · exact Cal.Instant.lt_trans h1 (h3 r hr)

/-- **The merge is `redraw`'s three lists** over starts strictly increasing, with fuel for every element. -/
theorem redrawWalkGo_spec (dy : Cal.Instant → Nat) : ∀ (n : Nat) (old : List Piece) (P : List (At × At)),
    old.length + P.length ≤ n → startsUp (old.map (fun p => (p.s, p.e))) = true → startsUp P = true →
    redrawWalkGo dy n old P =
      (P.map (fun q => match old.find? (fun p => samePiece p q) with
          | some p => p
          | none => ⟨q.1, q.2, dy q.1.1⟩),
       old.filter (fun p => !P.any (samePiece p)),
       P.filter (fun q => !old.any (fun p => samePiece p q)))
  | _, [], P, _, _, _ => by
    simp only [redrawWalkGo, List.find?_nil, List.filter_nil, List.any_nil, Bool.not_false, Prod.mk.injEq, true_and]
    exact (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | _, p :: os, [], _, _, _ => by
    simp only [redrawWalkGo, List.map_nil, List.filter_nil, List.any_nil, Bool.not_false, Prod.mk.injEq, true_and,
      and_true]
    exact (List.filter_eq_self.2 (fun _ _ => rfl)).symm
  | 0, p :: os, q :: qs, hlen, _, _ => by simp at hlen
  | n + 1, p :: os, q :: qs, hlen, ho, hP => by
    simp only [List.length_cons] at hlen
    rw [List.map_cons] at ho
    have ho' := startsUp_cons ho
    have hP' := startsUp_cons hP
    have hos : ∀ o ∈ os, p.s.1 < o.s.1 := fun o ho => ho'.2 (o.s, o.e) (List.mem_map.2 ⟨o, ho, rfl⟩)
    have hqs : ∀ r ∈ qs, q.1.1 < r.1.1 := hP'.2
    have hnm : ∀ (a : Piece) (b : At × At), a.s.1 ≠ b.1.1 → samePiece a b = false := by
      intro a b hne
      cases h : samePiece a b with
      | false => rfl
      | true => exact absurd (samePiece_start a b h) hne
    have neLt : ∀ a b : Cal.Instant, a < b → a ≠ b := fun a b h he => by
      subst he; exact Cal.Instant.lt_irrefl _ h
    have mapC : ∀ (A B : List Piece) (R : List (At × At)),
        (∀ r ∈ R, A.find? (fun a => samePiece a r) = B.find? (fun a => samePiece a r)) →
        R.map (fun r => match A.find? (fun a => samePiece a r) with
          | some a => a
          | none => ⟨r.1, r.2, dy r.1.1⟩) =
        R.map (fun r => match B.find? (fun a => samePiece a r) with
          | some a => a
          | none => ⟨r.1, r.2, dy r.1.1⟩) := by
      intro A B R h; apply List.map_congr_left; intro r hr; rw [h r hr]
    rw [redrawWalkGo]
    by_cases h1 : p.s.1 < q.1.1
    · rw [if_pos h1, redrawWalkGo_spec dy n os (q :: qs) (by simp; omega) ho'.1 hP]
      have hpq : ∀ r ∈ q :: qs, samePiece p r = false := by
        intro r hr
        apply hnm
        rcases List.mem_cons.1 hr with rfl | hr
        · exact neLt _ _ h1
        · exact neLt _ _ (Cal.Instant.lt_trans h1 (hqs r hr))
      have hany : (q :: qs).any (samePiece p) = false := by
        rw [List.any_eq_false]; intro r hr; simp [hpq r hr]
      have e1 := mapC (p :: os) os (q :: qs) (fun r hr => by rw [List.find?_cons, hpq r hr])
      have e2 : (p :: os).filter (fun a => !(q :: qs).any (samePiece a)) =
          p :: os.filter (fun a => !(q :: qs).any (samePiece a)) :=
        List.filter_cons_of_pos (by simp [hany])
      have e3 : (q :: qs).filter (fun r => !(p :: os).any (fun a => samePiece a r)) =
          (q :: qs).filter (fun r => !os.any (fun a => samePiece a r)) := by
        apply List.filter_congr; intro r hr; rw [List.any_cons, hpq r hr, Bool.false_or]
      rw [e1, e2, e3]
    · rw [if_neg h1]
      by_cases h2 : q.1.1 < p.s.1
      · rw [if_pos h2, redrawWalkGo_spec dy n (p :: os) qs (by simp; omega) (by rw [List.map_cons]; exact ho) hP'.1]
        have hqo : ∀ a ∈ p :: os, samePiece a q = false := by
          intro a ha
          apply hnm
          rcases List.mem_cons.1 ha with rfl | ha
          · exact (neLt _ _ h2).symm
          · exact (neLt _ _ (Cal.Instant.lt_trans h2 (hos a ha))).symm
        have hfind : (p :: os).find? (fun a => samePiece a q) = none := by
          rw [List.find?_eq_none]; intro a ha; simp [hqo a ha]
        have hany : (p :: os).any (fun a => samePiece a q) = false := by
          rw [List.any_eq_false]; intro a ha; simp [hqo a ha]
        have e1 : (q :: qs).map (fun r => match (p :: os).find? (fun a => samePiece a r) with
            | some a => a
            | none => ⟨r.1, r.2, dy r.1.1⟩) =
            ⟨q.1, q.2, dy q.1.1⟩ :: qs.map (fun r => match (p :: os).find? (fun a => samePiece a r) with
              | some a => a
              | none => ⟨r.1, r.2, dy r.1.1⟩) := by
          rw [List.map_cons, hfind]
        have e2 : (p :: os).filter (fun a => !(q :: qs).any (samePiece a)) =
            (p :: os).filter (fun a => !qs.any (samePiece a)) := by
          apply List.filter_congr; intro a ha; rw [List.any_cons, hqo a ha, Bool.false_or]
        have e3 : (q :: qs).filter (fun r => !(p :: os).any (fun a => samePiece a r)) =
            q :: qs.filter (fun r => !(p :: os).any (fun a => samePiece a r)) :=
          List.filter_cons_of_pos (by simp [hany])
        rw [e1, e2, e3]
      · rw [if_neg h2]
        have heq : p.s.1 = q.1.1 :=
          Cal.Instant.le_antisymm ((Cal.Instant.not_lt _ _).1 h2) ((Cal.Instant.not_lt _ _).1 h1)
        have hpr : ∀ r ∈ qs, samePiece p r = false := fun r hr => hnm p r (by rw [heq]; exact neLt _ _ (hqs r hr))
        have hoq : ∀ o ∈ os, samePiece o q = false := fun o ho => hnm o q (by
          rw [← heq]; exact (neLt _ _ (hos o ho)).symm)
        have em : qs.map (fun r => match (p :: os).find? (fun a => samePiece a r) with
              | some a => a
              | none => ⟨r.1, r.2, dy r.1.1⟩) =
            qs.map (fun r => match os.find? (fun a => samePiece a r) with
              | some a => a
              | none => ⟨r.1, r.2, dy r.1.1⟩) :=
          mapC (p :: os) os qs (fun r hr => by rw [List.find?_cons, hpr r hr])
        have ef1 : os.filter (fun a => !(q :: qs).any (samePiece a)) = os.filter (fun a => !qs.any (samePiece a)) := by
          apply List.filter_congr; intro o ho; rw [List.any_cons, hoq o ho, Bool.false_or]
        have ef2 : qs.filter (fun r => !(p :: os).any (fun a => samePiece a r)) =
            qs.filter (fun r => !os.any (fun a => samePiece a r)) := by
          apply List.filter_congr; intro r hr; rw [List.any_cons, hpr r hr, Bool.false_or]
        have hfind_q : os.find? (fun a => samePiece a q) = none := by
          rw [List.find?_eq_none]; intro a ha; simp [hoq a ha]
        have hany_q : os.any (fun a => samePiece a q) = false := by
          rw [List.any_eq_false]; intro a ha; simp [hoq a ha]
        have hany_p : qs.any (samePiece p) = false := by
          rw [List.any_eq_false]; intro r hr; simp [hpr r hr]
        by_cases hsp : samePiece p q = true
        · rw [if_pos hsp, redrawWalkGo_spec dy n os qs (by omega) ho'.1 hP'.1]
          have e1 : (q :: qs).map (fun r => match (p :: os).find? (fun a => samePiece a r) with
              | some a => a
              | none => ⟨r.1, r.2, dy r.1.1⟩) =
              p :: qs.map (fun r => match (p :: os).find? (fun a => samePiece a r) with
                | some a => a
                | none => ⟨r.1, r.2, dy r.1.1⟩) := by
            rw [List.map_cons, List.find?_cons_of_pos (p := fun a => samePiece a q) (l := os) hsp]
          have e2 : (p :: os).filter (fun a => !(q :: qs).any (samePiece a)) =
              os.filter (fun a => !(q :: qs).any (samePiece a)) :=
            List.filter_cons_of_neg (by simp [hsp])
          have e3 : (q :: qs).filter (fun r => !(p :: os).any (fun a => samePiece a r)) =
              qs.filter (fun r => !(p :: os).any (fun a => samePiece a r)) :=
            List.filter_cons_of_neg (by simp [hsp])
          rw [e1, e2, e3, em, ef1, ef2]
        · have hsp' : samePiece p q = false := by simpa using hsp
          rw [if_neg hsp, redrawWalkGo_spec dy n os qs (by omega) ho'.1 hP'.1]
          have e1 : (q :: qs).map (fun r => match (p :: os).find? (fun a => samePiece a r) with
              | some a => a
              | none => ⟨r.1, r.2, dy r.1.1⟩) =
              ⟨q.1, q.2, dy q.1.1⟩ :: qs.map (fun r => match (p :: os).find? (fun a => samePiece a r) with
                | some a => a
                | none => ⟨r.1, r.2, dy r.1.1⟩) := by
            rw [List.map_cons, List.find?_cons_of_neg (p := fun a => samePiece a q) (l := os) (by simp [hsp']), hfind_q]
          have e2 : (p :: os).filter (fun a => !(q :: qs).any (samePiece a)) =
              p :: os.filter (fun a => !(q :: qs).any (samePiece a)) :=
            List.filter_cons_of_pos (by simp [hsp', hany_p])
          have e3 : (q :: qs).filter (fun r => !(p :: os).any (fun a => samePiece a r)) =
              q :: qs.filter (fun r => !(p :: os).any (fun a => samePiece a r)) :=
            List.filter_cons_of_pos (by simp [hsp', hany_q])
          rw [e1, e2, e3, em, ef1, ef2]

/-- **`redraw` is `redrawFast`** (README gap 5027): `@[csimp]` — the compiled code runs the one merge whenever the old
pieces' and the new spans' starts strictly increase. -/
@[csimp] theorem redraw_eq_redrawFast : @redraw = @redrawFast := by
  funext dy id old P
  unfold redrawFast
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    rw [redrawWalk, redrawWalkGo_spec dy _ old P (Nat.le_refl _) h.1 h.2]
    rfl
  · rfl

/-! The witnesses' spans are `[a, b)` in whole seconds of 2026-09-07, UTC, written out: a fixture `def` would be
emitted and reached by nothing (check 12). -/

/-- **The one pass answers as `pieces` does** (README gap 5027): three spans apart — `[0, 300)`, `[600, 900)`,
`[1200, 1500)` — and `[x, t)` = `[100, 1800)` split into `[300, 600)`, `[900, 1200)` and `[1500, 1800)`, which `pieces`
answers too over the same spans given out of order with an empty one among them (what `piecesFast` sorts and
filters). -/
theorem the_one_pass_answers_as_pieces :
    apart [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩)) : At × At)] = true ∧
    sweep [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩)) : At × At)] ((((⟨63924364800 + 100, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 100, 0⟩, ⟨false, 0⟩)) : At × At)).1 ((((⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩)) : At × At)).1 =
      [(((((⟨63924364800 + 300, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : At × At)).1), (((((⟨63924364800 + 900, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩)) : At × At)).1), (((((⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩)) : At × At)).1)] ∧
    pieces [(((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 50, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 50, 0⟩, ⟨false, 0⟩)) : At × At)] ((((⟨63924364800 + 100, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 100, 0⟩, ⟨false, 0⟩)) : At × At)).1 ((((⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩)) : At × At)).1 =
      [(((((⟨63924364800 + 300, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : At × At)).1), (((((⟨63924364800 + 900, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1200, 0⟩, ⟨false, 0⟩)) : At × At)).1), (((((⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1500, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1800, 0⟩, ⟨false, 0⟩)) : At × At)).1)] := by
  decide

/-- **The pass's guard bites**: spans that overlap are not apart, nor is an empty one, and spans out of order are
not; `spanOk` drops an empty span and keeps a nonempty one. -/

theorem the_pass_is_guarded :
    apart [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 300, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)] = false ∧ apart [(((⟨63924364800 + 50, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 50, 0⟩, ⟨false, 0⟩)) : At × At)] = false ∧ apart [(((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)] = false ∧
    spanOk ((((⟨63924364800 + 50, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 50, 0⟩, ⟨false, 0⟩)) : At × At)) = false ∧ spanOk ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1, 0⟩, ⟨false, 0⟩)) : At × At)) = true := by
  decide

/-- **The merge's guard bites**: starts strictly increasing are up, starts out of order or equal are not. -/
theorem the_merge_is_guarded :
    startsUp [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)] = true ∧ startsUp [(((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)] = false ∧
    startsUp [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : At × At)] = false := by
  decide

/-- **Settle the open block** (the owner's **D99**, README gap 4520a, W-47 track K, parity P104) — fork `close_sub`'s
successor, run after every mark that moves what the block's clock nets: its pieces drawn so far are re-drawn as
`openPieces` (`redraw`), its worked minutes are theirs (site R8, per piece), and its clock runs from `runFrom` — or
not at all while it is stopped (`openStop`).  So a mark logged after a stretch it lies across was closed and drawn — a
`break`, a `pause` or an `interrupt` a clock behind the log wrote — is netted from that stretch where it lies, as the
host's `Replay::idle_min_since` nets it at its next reading.  Fork `close_sub` credited and drew each stretch when it
closed and never moved it again; D94's machine netted only the breaks its clock had not yet met (README gap 4520). -/
def settle (dy : Cal.Instant → Nat) (m : Machine) : Machine × List Effect :=
  match m.block with
  | some b =>
    ({ m with block := some { b with
        drawn := (redraw dy b.id b.drawn (openPieces b m)).1,
        workedMin := minutesOf (openPieces b m),
        since := match openStop b m with
          | some _ => none
          | none => some (runFrom (blockSpans b m) b.started) } },
      (redraw dy b.id b.drawn (openPieces b m)).2)
  | none => (m, [])

/-- **`close_pause(t)`'s machine** (the owner's D99): the pause start taken, and the span it closed — when it is
nonempty — one of the block's idle spans.  The day index is not read here (`closePause` reads it for the segment). -/
def closePauseM (m : Machine) (t : At) : Machine :=
  match m.block with
  | some b =>
    match b.pausedAt with
    | some p =>
      { m with block := some { b with pausedAt := none, idle := if p.1 < t.1 then b.idle ++ [(p, t)] else b.idle } }
    | none => m
  | none => m

/-- **Fork `close_pause(t)`**: take `paused_at` and emit a `Pause` segment if `t > p`.  **It does not
clear `paused`** (`close_pause_does_not_clear_paused`).  **Since the owner's D99** the span it draws is one of the
block's idle spans (`Block.idle`), which its clock nets wherever a later mark is stamped. -/
def closePause (dy : Cal.Instant → Nat) (m : Machine) (t : At) : Machine × List Effect :=
  (closePauseM m t,
    match m.block with
    | some b =>
      match b.pausedAt with
      | some p => if p.1 < t.1 then [.dayAdd (dy p.1) (.segment ⟨p, t, .pause b.id⟩)] else []
      | none => []
    | none => [])

/-- **Fork `credit(id, t, min, ci)`**, on the day of `t`, the closing event: the item's minutes, its
minutes on that day (the key inserted even at 0), and the day's sums. -/
def creditFx (dy : Cal.Instant → Nat) (id : Id) (t : At) (min : Nat) (ci : Option U8) : List Effect :=
  [.itemAdd id (.credit min), .itemDay id (dy t.1) min, .dayAdd (dy t.1) (.credit id min ci)]

/-- **Fork `uncredit_cut(cut)`**: nothing for a cut of 0 minutes; otherwise the cut's minutes come off
the item, the item's day and the day's ci-unknown minutes, each saturating and removed at 0. -/
def uncreditFx (c : Cut) : List Effect :=
  if c.min = 0 then []
  else [.itemAdd c.id (.uncredit c.min), .itemDaySub c.id c.day c.min, .dayAdd c.day (.uncredit c.id c.min)]

def obsFx : Option EnergyObs → List Effect
  | some o => [.obs (.energy o)]
  | none => []

/-- **Fork `cut(t)`**: take the block, draw its pieces to `t` (`cutPieces`, re-drawn over what it drew while open:
the owner's D99) and its pause, credit their minutes with no ci, and remember the cut.  The block's pending
observation is emitted. -/
def cut (dy : Cal.Instant → Nat) (m : Machine) (t : At) : Machine × List Effect :=
  match m.block with
  | some b =>
    ({ block := none, lastCut := some ⟨b.id, t, dy t.1, minutesOf (cutPieces b m t)⟩, interrupt := m.interrupt,
       brks := m.brks, brkOpen := m.brkOpen,
       closed := pruneClosed (⟨b.id, b.day, dy t.1, none, minutesOf (cutPieces b m t),
         (redraw dy b.id b.drawn (cutPieces b m t)).1, none, b.started, [], 0⟩ :: m.closed), brkEnded := m.brkEnded },
      (redraw dy b.id b.drawn (cutPieces b m t)).2 ++ (closePause dy m t).2 ++
        creditFx dy b.id t (minutesOf (cutPieces b m t)) none ++ obsFx b.obs)
  | none => (m, [])

/-- The observation a `done` closes: `went` written onto it when the `done` carries one. -/
def wentOn (went : Option U8) (o : EnergyObs) : EnergyObs :=
  match went with
  | some w => { o with went := some w }
  | none => o

/-- **The closing half of fork `step`'s `Done` arm**, the machine and what it writes.  A `done` whose id
is the open block's closes it: its pieces to `t` are drawn (`cutPieces`, D99) and its pause, the block is taken with
**its clock minutes discarded** (`actual_min` is authoritative), its observation gets `went`, and the last cut
is forgotten.  Otherwise, with no block open, minutes to give and the last cut this item's, the cut's
credit is taken back (**the stop-then-done replacement**, which ignores `partial`).  A `done` for another
id while a block is open changes nothing here. -/
def doneClose (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat) (went : Option U8) :
    Machine × List Effect :=
  match m.block with
  | some b =>
    if b.id = id then
      ({ m with block := none, lastCut := none },
        (redraw dy b.id b.drawn (cutPieces b m t)).2 ++ (closePause dy m t).2 ++ obsFx (b.obs.map (wentOn went)))
    else (m, [])
  | none =>
    match m.lastCut with
    | some c => if 0 < actual ∧ c.id = id then ({ m with lastCut := none }, uncreditFx c) else (m, [])
    | none => (m, [])

/-- **The closed blocks after a `done`** (the owner's D100, README gap 4520b): the open block it closes, held as the
`done`'s — its credit the `done`'s `actual_min` at its ci, on the `done`'s day, and its duration observation's line when
it pushes one; or, for the stop-then-done replacement, the last cut's block (the first held, `pruneClosed`) carrying the
`done`'s credit in place of the cut's — and nothing a running break took from the cut's credit to give back, since the
`done`'s `actual_min` replaces that credit whole (the owner's D137: `Closed.ranMin` cleared, the pieces it took kept, so the
break's line re-draws them and nets its own span from the `done`'s credit); otherwise as they were. -/
def doneClosed (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (id : Id) (actual : Nat) (ci : U8) :
    List Closed :=
  match m.block with
  | some b =>
    if b.id = id then
      pruneClosed (⟨id, b.day, dy t.1, some ci, actual, (redraw dy b.id b.drawn (cutPieces b m t)).1,
        if 0 < actual then some line else none, b.started, [], 0⟩ :: m.closed)
    else m.closed
  | none =>
    match m.lastCut, m.closed with
    | some c, C :: rest =>
      if 0 < actual ∧ c.id = id then
        { C with credDay := dy t.1, ci := some ci, min := actual, durLine := some line, ranMin := 0 } :: rest
      else m.closed
    | _, _ => m.closed

/-- **A block resumed after an interruption** (`span`, when one was open): the span is one of its idle spans (the
owner's D99), and a paused block stays paused, its pause restarting where the interruption left off
(`paused_at.get_or_insert(t)`).  Where its clock runs from is `settle`'s. -/
def resumeBlock (b : Block) (span : Option (At × At)) (t : At) : Block :=
  { b with pausedAt := if b.paused then b.pausedAt.or (some t) else b.pausedAt,
           idle := match span with
             | some sp => if sp.1.1 < sp.2.1 then b.idle ++ [sp] else b.idle
             | none => b.idle }

/-- **Where a break begun at `t` ends** — fork `step`'s `Break` arm, `t + actual_min.unwrap_or(planned_min)`:
the end of its `Break` segment (`dayArm`), and, since the owner's **D87**, the instant a block's clock it fell
inside restarts at (`brkFx`).  One definition of a break's span, so the segment drawn and the minutes netted
cannot disagree (AGENTS §5.3). -/
def brkEnd (t : At) (planned : Nat) (actual : Option Nat) : At := (addMinutes t.1 (actual.getD planned), t.2)

/-- A closed block's drawn pieces, as spans. -/
def Closed.spans (C : Closed) : List (At × At) := C.drawn.map (fun p => (p.s, p.e))

/-- **Pieces with a span `[s, e)` cut out of each** (the owner's D100): every piece on its own, as `pieces` cuts a
running stretch around the spans its clock nets. -/
def cutOut (s e : At) (P : List (At × At)) : List (At × At) := P.flatMap (fun q => pieces [(s, e)] q.1 q.2)

/-- **What a break `[s, e)` takes from a closed block** (D100): its pieces' minutes before the cut less after (site R8,
per piece), never more than its credit still standing. -/
def netMin (s e : At) (C : Closed) : Nat := min (minutesOf C.spans - minutesOf (cutOut s e C.spans)) C.min

/-- **One held closed block netted by a `break` `[s, e)` stepped on ledger day `d`** (the owner's **D100**, README gap
4520b, parity P105): a break filed on a ledger day before the block's nets nothing (D94's rule), nor one that meets
none of its pieces — there is nothing of it to cut (gap 4920's early exit); otherwise its pieces are cut around the break
(`pieces`, each on its own) and re-drawn (`redraw`), and what that took — the pieces' minutes before less after (site
R8, per piece), never more than its credit still standing — comes off its credit (`DayOp.net` on the day it was filed,
the item's minutes, its minutes on that day) and off its `done`'s duration observation.  Block, effects, minutes. -/
def netOne (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Closed) : Closed × List Effect × Nat :=
  if d < C.day ∨ C.drawn.all (fun p => decide (p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1)) then (C, [], 0)
  else
    ({ C with drawn := (redraw dy C.id C.drawn (cutOut s e C.spans)).1, min := C.min - netMin s e C },
      (redraw dy C.id C.drawn (cutOut s e C.spans)).2 ++
        (if 0 < netMin s e C then
          [.dayAdd C.credDay (.net C.id C.ci (netMin s e C) C.durLine), .itemAdd C.id (.uncredit (netMin s e C)),
           .itemDaySub C.id C.credDay (netMin s e C)]
         else []),
      netMin s e C)

/-- **Every held closed block netted by a `break`** (the owner's D100): each by `netOne`, in order, and the last cut —
the first held while it stands — taken down by what its block lost. -/
def netClosed (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (m : Machine) : Machine × List Effect :=
  ({ m with closed := m.closed.map (fun C => (netOne dy s e d C).1),
            lastCut := match m.lastCut, m.closed with
              | some c, C :: _ => some { c with min := c.min - (netOne dy s e d C).2.2 }
              | lc, _ => lc },
    (m.closed.map (fun C => (netOne dy s e d C).2.1)).flatten)

/-- **The latest end of a piece a held closed block has drawn**, or `s` when none ends later (README gap 5180): where the
span a running break begun at `s` nets from the closed blocks ends — past every piece they hold, so everything they drew
from `s` on is netted, as the `break` line that ends the break will net it (D100) once it is logged. -/
def runTo (s : At) : List Closed → At
  | [] => s
  | C :: l => runTo (C.drawn.foldl (fun b p => if b.1 < p.e.1 then p.e else b) s) l

/-- **Whether a span `[s, e)` meets a drawn piece** — the pieces `netOne` cuts (D137). -/
def meets (s e : At) (p : Piece) : Bool := !decide (p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1)

/-- **One held closed block netted by the running break, what it took remembered** (the owner's **D137**, README gaps 5504
and 5302): `netOne` over the running span, and the pieces it met, whole (`Closed.ran`), with the minutes it took
(`Closed.ranMin`) — so the `break` line that ends the break can give back what lies outside its own span (`giveOne`). -/
def runOne (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Closed) : Closed :=
  { (netOne dy s e d C).1 with
    ran := if d < C.day then C.ran else C.ran ++ C.drawn.filter (meets s e),
    ranMin := C.ranMin + (netOne dy s e d C).2.2 }

/-- **The held closed blocks netted by the running break** (README gap 5180, W-49 track L; the owner's **D94** and **D100**:
a block and a break are read one way on every log): when a `break_start` at `s` has no `break` line yet
(`Machine.brkOpen`), every held closed block is netted by `[s, runTo s)` — `netClosed`, D100's netting of a late `break`,
run now — so a block closed (a `done`, a `stop`, the `start` of another block) while the break runs, or held when a
`break_start` stamped before its end is logged, reads now what it will read once the break's line arrives: its pieces from
`s` on un-drawn, and what that took off its credit, its item and its `done`'s duration observation.  Nothing with no break
running, or with nothing held drawn after `s`. -/
def runNet (dy : Cal.Instant → Nat) (m : Machine) : Machine × List Effect :=
  match m.brkOpen with
  | some o =>
    if o.s.1 < (runTo o.s m.closed).1 then
      ({ (netClosed dy o.s (runTo o.s m.closed) o.day m).1 with
          closed := m.closed.map (runOne dy o.s (runTo o.s m.closed) o.day) },
        (netClosed dy o.s (runTo o.s m.closed) o.day m).2)
    else (m, [])
  | none => (m, [])

/-- **A held closed block's pieces with what a running break took put back** (the owner's **D137**, README gaps 5504 and
5302): its drawn pieces but the remainder of each piece the running break cut — the one beginning where a piece it took
began, which `Closed.ran` holds whole — and the pieces it took, whole: the block as it stood before the running break
netted it, its later nettings kept. -/
def Closed.restored (C : Closed) : List (At × At) :=
  (C.drawn.filter (fun p => !C.ran.any (fun r => atEq r.s p.s))).map (fun p => (p.s, p.e)) ++
    C.ran.map (fun p => (p.s, p.e))

/-- **One held closed block given back what a running break took** (the owner's **D137**, README gaps 5504 and 5302, W-51
track K, parity **P134**): nothing when no running break netted it (`Closed.ran` empty); otherwise its pieces re-drawn as
they stood (`Closed.restored`, `redraw`), and the minutes the running break took (`Closed.ranMin`) credited back — on the
day its credit was filed, at its ci (`DayOp.credit`), to its `done`'s duration observation (`DayOp.undur`), to the item
and its minutes on that day — so that the `break` line that ends the break nets it as D100 nets any late break inside a
block: its own span, and nothing after it (`brkArm`).  Block, effects, minutes. -/
def giveOne (dy : Cal.Instant → Nat) (C : Closed) : Closed × List Effect × Nat :=
  if C.ran.isEmpty then (C, [], 0)
  else
    ({ C with drawn := (redraw dy C.id C.drawn C.restored).1, min := C.min + C.ranMin, ran := [], ranMin := 0 },
      (redraw dy C.id C.drawn C.restored).2 ++
        (if 0 < C.ranMin then
          [.dayAdd C.credDay (.credit C.id C.ranMin C.ci), .dayAdd C.credDay (.undur C.durLine C.ranMin),
           .itemAdd C.id (.credit C.ranMin), .itemDay C.id C.credDay C.ranMin]
         else []),
      C.ranMin)

/-- **Every held closed block given back what the running break took** (the owner's **D137**): each by `giveOne`, and the
last cut — the first held while it stands — raised by what its block got back (`HeadOk`). -/
def giveBack (dy : Cal.Instant → Nat) (m : Machine) : Machine × List Effect :=
  ({ m with closed := m.closed.map (fun C => (giveOne dy C).1),
            lastCut := match m.lastCut, m.closed with
              | some c, C :: _ => some { c with min := c.min + (giveOne dy C).2.2 }
              | lc, _ => lc },
    (m.closed.map (fun C => (giveOne dy C).2.1)).flatten)

/-- **Fork `step`'s `Done` arm.**  `doneClose`, its machine first; then `actual_min` is always credited
with the event's ci, on the `done`'s day; with minutes, the item's and the day's block count and a
`DurationObs` (partials included); a partial pushes `partial_done_at`, a completion `done_at` and the
day's `done` (the done sets are `completionArm`'s). -/
def doneFx (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id)
    (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool) :
    List Effect :=
  let rc := doneClose dy m t id actual went
  .machine (runNet dy { rc.1 with closed := doneClosed dy m line t id actual ci }).1 :: rc.2 ++
    creditFx dy id t actual (some ci) ++
    (if 0 < actual then
      [.itemAdd id .block, .dayAdd d .blockDone, .obs (.duration ⟨line, t, d, id, ci, tags, est, actual, went, isPartial⟩)]
     else []) ++
    (if isPartial then [.itemAdd id (.partialDoneAt t)] else [.itemAdd id (.doneAt t), .dayAdd d (.done id)]) ++
    (runNet dy { rc.1 with closed := doneClosed dy m line t id actual ci }).2

/-- **Where a late `start` at `t` cuts a held closed block** (the owner's **D115**, README gap 5034, parity **P120**): the
end of its last piece when it has a piece begun before `t` — the block the `start` is stamped inside, a later `done` or
`stop` having closed it — and `t` otherwise, so the span `[t, startEnd t C)` the `start` nets from it is the part of it
after `t`, or empty.  On a log a forward clock writes, every held block ended by `t` and every span is empty. -/
def startEnd (t : At) (C : Closed) : At :=
  if C.drawn.any (fun p => decide (p.s.1 < t.1)) then C.drawn.foldl (fun b p => if b.1 < p.e.1 then p.e else b) t
  else t

/-- **The held closed blocks a late `start` at `t` cuts** (the owner's **D115**, README gap 5034, parity **P120**): each
by `netOne` over its own span `[t, startEnd t C)`, as a `break` nets them (D100), so a block the `start` is stamped
inside — closed by a `done` or a `stop` logged before it — ends at `t`: the later fact wins, as a `start` cuts the open
block (`cut`).  Its pieces after `t` are un-drawn, and what that took comes off its credit, its item and its `done`'s
duration observation; the last cut is taken down by what its block lost.  Fork 4748911 read the line as a start
stamped where it was and never moved the closed block: the day drew both blocks across one span and counted it twice. -/
def netStart (dy : Cal.Instant → Nat) (t : At) (d : Nat) (m : Machine) : Machine × List Effect :=
  ({ m with closed := m.closed.map (fun C => (netOne dy t (startEnd t C) d C).1),
            lastCut := match m.lastCut, m.closed with
              | some c, C :: _ => some { c with min := c.min - (netOne dy t (startEnd t C) d C).2.2 }
              | lc, _ => lc },
    (m.closed.map (fun C => (netOne dy t (startEnd t C) d C).2.1)).flatten)

/-- **The place a `break` line's break is read at** (the owner's **D116**, README gap 5035): the place its
`break_start` gave — the running break the line ends (`Machine.brkOpen`, D105's pairing in file order) — and the line's
own word only where no `break_start` opened it: a log fork 4748911 wrote, or one written before D105, has no
`break_start`, and there the end line is the break's one record, so its word is the place.  One reader of a break's
place: D111's table reads the start's, and the end line's word is never a second reading (`lateWarnList` names a
disagreement). -/
def brkPlace (m : Machine) (w : Option (List Char)) : Option (List Char) :=
  match m.brkOpen with
  | some o => o.where_
  | none => w

/-- **The entry a `break` line's day family reads** (D116): the line with its place read at its `break_start`'s
(`brkPlace`); any other entry as it is. -/
def placed (m : Machine) (e : Entry) : Entry :=
  match e.ev with
  | .brk p a w => { e with ev := .brk p a (brkPlace m w) }
  | _ => e

/-- **`placed` reads only a `break` line** (D116): every other entry is itself. -/
theorem placed_of_not_brk (m : Machine) (e : Entry) (h : ∀ p a w, e.ev ≠ .brk p a w) : placed m e = e := by
  unfold placed; split
  · rename_i p a w hb; exact absurd hb (h p a w)
  · rfl

/-- **A `break` line's place, read at its start** (D116): the line's event with `brkPlace` in its word's stead. -/
theorem placed_ev_of_brk (m : Machine) (e : Entry) {p : U32} {a : Option U32} {w : Option (List Char)}
    (h : e.ev = .brk p a w) : (placed m e).ev = .brk p a (brkPlace m w) := by
  unfold placed; rw [h]

/-- **`placed` keeps the line** (D116): only the place a `break` is read at moves. -/
theorem placed_line (m : Machine) (e : Entry) : (placed m e).line = e.line := by
  unfold placed; split <;> rfl

/-- The newest ledger day of a block the machine holds closed, `0` with none held. -/
def closedHi (l : List Closed) : Nat := l.foldl (fun a k => max a k.day) 0

/-- **A late mark past D100's bound** (the owner's **D119**, README gaps 4913, 4917 and 5029): the newest ledger day of a
closed block the machine holds, when a mark's ledger day `d` is more than 31 behind it — the bound `pruneClosed` keeps the
held blocks within, so a block of day `d` or before that the mark would net may have been dropped.  `none` within the
bound, and with nothing held. -/
def pastBound (d : Nat) (l : List Closed) : Option Nat :=
  if d + 31 < closedHi l then some (closedHi l) else none

/-- **A `break`'s machine effect** — the owner's **D87** (README gap 4137, parity P81: a break taken inside a block is
not block time), **D92** (gap 4241, P85: nor one run into its start), **D94** (gaps 4361 and 4506, P92: every break
on its ledger days, held — `Machine.brks`, within `maxKeepDays` ledger days of the newest by `pruneBrks` — and
netted wherever the clock meets it; one filed on a ledger day before the block's stops no clock) and **D99** (gap
4520a, P104: wherever it is logged).  The break is held with the ledger day `d` it was stepped on, and the open
block is settled over the breaks held (`settle`), so a stretch it lies across — the one running, or one closed and
drawn before it was logged — is netted where it lies.  Its own `Break` segment and record are the day family's
(`dayArm`).  Fork `step`'s `Break` arm touched no block, so a block cut across a break was credited its whole span
and drawn across it.

**Since the owner's D105** (parity P100) every machine it writes has no running break (`brkOpen := none`): a `break`
line ends the break a `break_start` opened, in file order. -/
def brkFx (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) : List Effect :=
  (settle dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).2 ++
    (netClosed dy t e d (settle dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).1).2 ++
    [.machine (netClosed dy t e d (settle dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).1).1]

/-- **With no block open a break nets only the closed blocks held** (the owner's D92 and D94, restated at the owner's
D100): the old machine with the break held, and — since D100 — every held closed block it lies across netted
(`netClosed`); `settle` has no block to settle.  D92 stated it of every machine whose clock was stopped, a paused block
included, and since the owner's D99 that is false (`brkFx_of_stopped_as_d92_stated_it_is_refuted`); D99 stated it as
"writes only its span", false since D100 (`brkFx_with_no_block_open_as_d99_stated_it_is_refuted`), true still when
nothing closed is held (`brkFx_with_nothing_open_or_held`). -/
theorem brkFx_with_no_block_open (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) (h : m.block = none) :
    brkFx dy m t e d =
      (netClosed dy t e d { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).2 ++
        [.machine (netClosed dy t e d { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).1] := by
  unfold brkFx settle
  simp [h]

/-- **With no block open and no closed block held, a break writes only its span** — W-47 track K's first commit's
statement, on the subdomain the name gives (the owner's D100 nets a held closed block). -/
theorem brkFx_with_nothing_open_or_held (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) (h : m.block = none)
    (hc : m.closed = []) :
    brkFx dy m t e d = [.machine { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }] := by
  rw [brkFx_with_no_block_open dy m t e d h]
  unfold netClosed
  rcases hlc : m.lastCut with _ | c <;> simp [hc]

/-! The machine the refutation below steps is written in its proof (`M`): as a definition it was emitted code no request
reaches (check 12, W-47 track K). -/


/-- **"With no block open a break writes only its span", as D99 stated it, refuted by D100** (README gap 4520b, parity
P105): after `a`'s cut at 09:00, a twenty-minute break at 08:30 — stamped inside the block the cut closed — writes the
re-drawing of its piece and the taking down of its credit beside the machine: seven effects, where D99's statement wrote
one. -/
theorem brkFx_with_no_block_open_as_d99_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat), m.block = none →
      brkFx dy m t e d = [.machine { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }] := by
  intro h
  let M : Machine := ⟨none, some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865, 60⟩, none, [], none,
    [⟨['a'], 739865, 739865, none, 60, [⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865⟩], none, (⟨63924364800, 0⟩, ⟨false, 0⟩), [], 0⟩], none⟩
  have hl : (brkFx (fun _ => 739865) M (⟨63924366600, 0⟩, ⟨false, 0⟩) (⟨63924367800, 0⟩, ⟨false, 0⟩)
      739865).length = 7 := by decide
  rw [h (fun _ => 739865) M (⟨63924366600, 0⟩, ⟨false, 0⟩) (⟨63924367800, 0⟩, ⟨false, 0⟩) 739865 rfl] at hl
  simp at hl

/-- **`brkFx_of_stopped` as D92 stated it is refuted** (the owner's D99, README gap 4520a; the class table's M2): `a`
started at 08:00 and paused at 09:00 — its clock stopped, the stretch `[08:00, 09:00]` drawn — then a twenty-minute
`break` at 08:30 logged after the pause.  The break re-draws the stretch around itself (one piece un-drawn, two drawn),
so `brkFx` writes four effects where D92's statement wrote the machine alone. -/
theorem brkFx_of_stopped_as_d92_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat), (m.block.bind (·.since)) = none →
      brkFx dy m t e d = [.machine { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }] := by
  intro h
  let m : Machine := ⟨some ⟨['a'], (⟨63924364800, 0⟩, ⟨false, 0⟩), none, true, some (⟨63924368400, 0⟩, ⟨false, 0⟩),
    60, none, 739865, [], [⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865⟩], 0⟩,
    none, none, [], none, [], none⟩
  have hl : (brkFx (fun _ => 739865) m (⟨63924366600, 0⟩, ⟨false, 0⟩) (⟨63924367800, 0⟩, ⟨false, 0⟩) 739865).length
      = 4 := by decide
  rw [h (fun _ => 739865) m (⟨63924366600, 0⟩, ⟨false, 0⟩) (⟨63924367800, 0⟩, ⟨false, 0⟩) 739865 rfl] at hl
  simp at hl

/-- **C5: the day header and records family's arms of fork `Machine::step`**, one per event (`wake`,
`arrive`, `loc`, `break`, `energy`, `idle`, `routine`'s day half, `plan`, `demote`, `drop`, `close` and
unknown events; `readopt`, `move`, `edit`, `note` and `undo` write nothing).  `sl` is fork `slept_by_day`,
the first logged wake's `slept_min` per day, read **late**: an `energy` line logged before its day's wake
still reads it.
* `wake`: on its day, if the day has no wake yet (the first wake **in file order**, quirk Q6(a));
* `arrive`: the first sets the arrival, location, window and budget, and every one changes the location;
* `break`: a `Break` segment `[t, t + actual_or_planned]` and a `BreakRecord`, on its day;
* `energy`: an `EnergyObs` (`from_start` false, `slept_min` read from `sl`); it creates no day;
* `idle`: a gap `[t − min, t]` on **the day of its start**: an `Idle` segment and an `IdleRecord` there,
  and for `leak` the day's leak minutes and longest, and the global longest leak (`leak`);
* `routine … done` with minutes: a `Routine` segment `[t − min, t]` on the day of its start, and
  `routine_min` on the routine's own day;
* `plan`: the day's count, highest replans, drift and last hash;
* `demote`: a `Demotion`, its stamp `stamp_from_key(from)`; `close`: a `CloseRecord`; `drop`:
  `dropped_items`; an unknown event: the count. -/
def dayArm (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat) : List Effect :=
  match e.ev with
  | .wake slept onset => [.dayAdd d (.wake t slept.val (onset.map (·.val)))]
  | .arrive loc window budget => [.dayAdd d (.arrive t loc window budget.val)]
  | .loc loc => [.dayAdd d (.loc t loc)]
  | .brk planned actual where_ =>
    [.dayAdd d (.segment ⟨t, brkEnd t planned.val (actual.map (·.val)), .brk where_⟩),
     .dayAdd d (.brk ⟨t, d, planned.val, actual.map (·.val), where_⟩)]
  | .energy pred rep hsw loc => [.obs (.energy ⟨e.line, t, d, pred, rep, hsw, loc, sl d, none, none, false⟩)]
  | .idle attributed min =>
    let sd := dy (Cal.subMinutes t.1 min.val)
    [.dayAdd sd (.segment ⟨(Cal.subMinutes t.1 min.val, t.2), t, .idle attributed⟩),
     .dayAdd sd (.idle ⟨t, sd, attributed, min.val⟩)] ++
    (if attributed = "leak".toList then [.leak ⟨t, sd, min.val⟩] else [])
  | .routine item inst status actual =>
    match Log.parseInstanceStatus status, actual with
    | some .done, some m =>
      [.dayAdd (dy (Cal.subMinutes t.1 m.val)) (.segment ⟨(Cal.subMinutes t.1 m.val, t.2), t, .routine item inst⟩),
       .dayAdd d (.routineMin m.val)]
    | _, _ => []
  | .plan hash replans drift ys => [.dayAdd d (.plan hash replans.val drift.val ys t e.line)]
  | .demote id from_ to est => [.demote d ⟨e.line, t, id, from_, to, est.val, Log.stampFromKey from_⟩]
  | .drop id => [.drop id]
  | .close period key => [.close d ⟨e.line, t, period, key⟩]
  | .unknown _ _ => [.unknown]
  | _ => []

/-- **What an `extend` writes to the machine** (the owner's **D108**, README gaps 4876 and 4893): when the open block is
the extended item's, its own `ext` grows by the minutes — the minutes `tm extend` adds to the block's planned minutes,
which D42's rebuild of `.tm/state.json`'s `active.est_min` reads (`OpenBlock.ext`) — and nothing else of the machine
moves; an `extend` of any other item writes no machine. -/
def extendFx (m : Machine) (id : Id) (by_ : Nat) : List Effect :=
  match m.block with
  | some b => if b.id = id then [.machine { m with block := some { b with ext := b.ext + by_ } }] else []
  | none => []

/-- **The machine a `start` opens its block in** (the owner's D99): the block begun at `t` on ledger day `d`, nothing
drawn and no idle span of its own, the last cut forgotten, and the machine's interruption, breaks and running break —
which the cut before it keeps (`cut_keeps`). -/
def startedMachine (m : Machine) (id : Id) (t : At) (d : Nat) (o : Option EnergyObs) : Machine :=
  { block := some { id := id, started := t, since := none, paused := false, pausedAt := none, workedMin := 0, obs := o,
                    day := d, idle := [], drawn := [], ext := 0 },
    lastCut := none, interrupt := m.interrupt, brks := m.brks, brkOpen := m.brkOpen, closed := m.closed,
    brkEnded := m.brkEnded }

/-- **The machine an `interrupt` leaves** (the owner's D99): the block's pause closed (`closePauseM`), and the
interruption opened at `t` on day `d` unless one is open already (fork `step`'s `Interrupt` arm). -/
def interruptMachine (m : Machine) (t : At) (d : Nat) (id : Option Id) : Machine :=
  match (closePauseM m t).interrupt with
  | none => { closePauseM m t with interrupt := some (t, d, id.or ((closePauseM m t).block.map (·.id))) }
  | some _ => closePauseM m t

/-! ### D129: a `start` ends a running break, in stamp order (README gaps 5430-5433, W-50 track K, parity P127) -/

/-- **The running break a `start` at `t` ends** (the owner's **D129**): the break `Machine.brkOpen` holds, when it began
at or before `t` — a `start` logged while a break runs ends it at the start's instant, as `tm start` ends one on one
machine (D97: it logs the `break` line first).  A start stamped before the break began is before it in stamp order and
ends nothing; with no break running, nothing. -/
def endsBrk (m : Machine) (t : At) : Option OpenBrk :=
  match m.brkOpen with
  | some o => if o.s.1 ≤ t.1 then some o else none
  | none => none

/-- **Whether a start met comes before the one held** (README gap 5502, W-50 repair track R): whether `firstStep` takes the start it meets over the one it holds — the EARLIEST, by `instLt` (one definition of "strictly later by instant", §5.3), and any start when it holds none — named at this site, so check 9 can fold it to `fun _ => true` (the LATEST start met wins, which the two-block witness logged `b` first refutes) and to `fun _ => false` (no start is ever taken); the reading "the first held block in file order wins" is cheat 514's. -/
def startBefore (x : At) : Option At → Bool := fun | some a => instLt x a | none => true
/-- The earlier of an instant held and one met, of those strictly after `s` (`firstStart`'s step).  STRICTLY (README gap 5500, W-50 repair track R): every start the machine holds was logged before the `break_start` being stepped, so a start whose stamp TIES the break's is earlier in the file, and D129 ends a break only at a start later in stamp order or, at a tie, later in the file — `endsBrk`'s `≤`, for a start logged after a running break, is that other half. -/
def firstStep (s : At) (acc : Option At) (x : At) : Option At :=
  if s.1 < x.1 then
    -- the earliest start met so far (`startBefore`, README gap 5502): a start
    -- met replaces the one held only when it came before it
    if startBefore x acc then some x else acc
  else acc

/-- **The first start the machine holds stamped after `s`** (the owner's **D129**, read in STAMP order): the open block's start, and each held closed block whose `start` was stamped after `s` (`Closed.started`, README gap 5501) read at its first drawn piece (where its clock first ran, a machine instant: a block with no piece is no start, README gap 5432) —
the earliest, the first of equal ones — for a break of ledger day `d` within the owner's D119 bound (`pastBound`: 31 ledger days behind the newest held block), and `none` for one past it, which nothing nets and `tm check` names (README gap 5438).  A closed block whose `start` came at or before `s` ends nothing: a break stamped inside it is D100's late break inside a block, netted (`brkStartArm`'s `runNet`), and not one its drawn piece ends (README gap 5501, the W-50 critic's finding 3).
A tie with a held start ends nothing either (`firstStep`, README gap 5500).  A `break_start` logged after such a block and stamped before its start is a break that start ended (`arm`'s `break_start` arm).  `none` when the machine holds none. -/
def firstStart (s : At) (d : Nat) (m : Machine) : Option At :=
  if (pastBound d m.closed).isSome then none else
    (m.closed.filterMap (fun C => if s.1 < C.started.1 then C.drawn.head?.map (·.s) else none)).foldl
    (firstStep s) ((m.block.map (·.started)).bind (fun x => firstStep s none x))

/-- `firstStep` answers what it held or the instant it met. -/
theorem firstStep_mem (s : At) (acc : Option At) (y x : At) (h : firstStep s acc y = some x) : acc = some x ∨ x = y := by
  unfold firstStep at h
  -- the stamp test, then `startBefore`'s
  -- (README gap 5502: the comparison is named)
  split at h
  · split at h
    · exact Or.inr (Option.some.inj h).symm
    · exact Or.inl h
  · exact Or.inl h

/-- A fold of `firstStep` answers what it started from or an instant of the list. -/
theorem foldl_firstStep_mem (s : At) : ∀ (L : List At) (acc : Option At) (x : At),
    L.foldl (firstStep s) acc = some x → acc = some x ∨ x ∈ L
  | [], _, _, h => Or.inl h
  | y :: L, acc, x, h => by
    rcases foldl_firstStep_mem s L _ x h with h1 | h1
    · rcases firstStep_mem s acc y x h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2 ▸ List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- **What `firstStart` answers, the machine holds** (D129): the open block's start, or a held closed block's first
drawn piece's start. -/
theorem firstStart_mem (s : At) (d : Nat) (m : Machine) (x : At) (h : firstStart s d m = some x) :
    (∃ b, m.block = some b ∧ b.started = x) ∨ ∃ C ∈ m.closed, ∃ p ∈ C.drawn, p.s = x := by
  unfold firstStart at h; split at h; contradiction
  rcases foldl_firstStep_mem s _ _ x h with h1 | h1
  · left
    cases hb : m.block with
    | none => rw [hb] at h1; cases h1
    | some b =>
      rw [hb] at h1
      simp only [Option.map_some, Option.bind_some] at h1
      rcases firstStep_mem s none b.started x h1 with h2 | h2
      · cases h2
      · exact ⟨b, rfl, h2.symm⟩
  · right
    obtain ⟨C, hC, hx⟩ := List.mem_filterMap.1 h1
    by_cases hs : s.1 < C.started.1
    · rw [if_pos hs] at hx; cases hd : C.drawn with
      | nil => rw [hd] at hx; cases hx
      | cons p ps => rw [hd] at hx; simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hx
                     exact ⟨C, hC, p, by rw [hd]; exact List.mem_cons_self .., hx⟩
    · rw [if_neg hs] at hx; cases hx

/-- **The segment and record a break ended at `t` writes** (the owner's **D129**): what the `break` line `tm start` logs on
one machine writes on the break's own ledger day (D97, D105: stamped at the break's start, its minutes the elapsed ones,
`dayArm`'s `break` arm) — the break's `Break` segment `[o.s, t)` and its record.  The span ends at `t` itself, the start's
instant; the record's minutes are `t − o.s` in whole minutes, as `tm start` writes them. -/
def endRecs (o : OpenBrk) (t : At) : List Effect :=
  [.dayAdd o.day (.segment ⟨o.s, t, .brk o.where_⟩),
   .dayAdd o.day (.brk ⟨o.s, o.day, o.planned, some (Cal.minutesBetween o.s.1 t.1), o.where_⟩)]

/-- **The machine a `start` ending the running break `o` at `t` starts from** (the owner's **D129**): the break held as
`[o.s, t)` on its own ledger day, as its `break` line would hold it (`brkFx`), no break running, and the break's start
remembered (`Machine.brkEnded`), so that break's own `break` line, when the machine that took it logs it later, is not
read as a second break.  Every clock the running break lay across was netted while it ran (README gap 5180: `runNet` for
the held closed blocks, `runSpan` for the open block's drawing), and the start's cut reads the held span (`cutPieces`), so
nothing is settled here — and nothing here reads the day index.  What the running break took from the held closed blocks
is forgotten (`Closed.ran`, `Closed.ranMin`; the owner's D137): its own `break` line, which alone gives it back, is the one
this start makes the machine skip, and on a forward clock the span `[o.s, t)` covers everything it took (README gap
5580). -/
def endMachine (m : Machine) (o : OpenBrk) (t : At) : Machine :=
  { m with brks := pruneBrks (⟨o.s, t, o.day⟩ :: m.brks), brkOpen := none, brkEnded := some o.s,
           closed := m.closed.map (fun C => { C with ran := [], ranMin := 0 }) }

/-- **What a `break_start` a held start ends writes** (the owner's **D129**, read in stamp order): a break logged after a
block and stamped before its start ends at the first such start (`firstStart`) — held as `[o.s, t)` with every clock it
lies across netted (`brkFx`, D87, D94, D100: nothing netted it while it ran, for it never ran), its segment and record
(`endRecs`), and its start remembered (`Machine.brkEnded`). -/
def endBrkFx (dy : Cal.Instant → Nat) (m : Machine) (o : OpenBrk) (t : At) : List Effect :=
  brkFx dy { m with brkEnded := some o.s } o.s t o.day ++ endRecs o t

/-- **Fork `step`'s `Start` arm** (C3), over the machine it starts from: a late start's cut of the held closed blocks
(`netStart`, D115), the open block's cut (`cut`), the running break's netting (`runNet`), the day's `StartRecord`, and the
block opened (`startedMachine`) and settled.  Since the owner's D129 `arm` runs it over the machine ending the running
break leaves (`endMachine`) when the start ends one. -/
def startArm (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id) (pred : U8)
    (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) : List Effect :=
  let n := netStart dy t d m
  let s := settle dy (startedMachine (runNet dy (cut dy n.1 t).1).1 id t d
    (rep.map (fun rp => ⟨line, t, d, pred, rp, hsw, loc, some sleptMin.val, none, some id, true⟩)))
  n.2 ++ (cut dy n.1 t).2 ++ (runNet dy (cut dy n.1 t).1).2 ++ [.dayAdd d (.start ⟨t, id, pred, rep⟩)] ++ s.2 ++
    [.machine s.1]

/-- **Fork `step`'s `break_start` arm, as D105 has it** (parity P100): the running break opened at `t`, the open block
settled over it, and every held closed block it lies across netted (`runNet`). -/
def brkStartArm (dy : Cal.Instant → Nat) (m : Machine) (t : At) (d : Nat) (planned : Nat) (where_ : Option (List Char)) :
    List Effect :=
  let st := settle dy { m with brkOpen := some ⟨t, planned, where_, d⟩ }
  st.2 ++ (runNet dy st.1).2 ++ [.machine (runNet dy st.1).1]

/-- **Fork `step`'s `break` arm** (D87, D92, D94, D99, D105, D116, D137): what the running break took from the held closed
blocks given back (`giveBack`, the owner's D137), then the break held and netted (`brkFx`) — so a block a running break
netted from its start is netted by the break's own span, as D100 nets any late break inside a block — and its `Break`
segment and record on its day (`dayArm`, its place read at its `break_start`'s). -/
def brkArm (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat)
    (planned : Nat) (actual : Option Nat) : List Effect :=
  (giveBack dy m).2 ++ brkFx dy (giveBack dy m).1 t (brkEnd t planned actual) d ++ dayArm dy sl (placed m e) t d

/-- **The machine's arms of fork `Machine::step`**, one per event: the block family's (C3) here, every other
event's the day family's (`dayArm`, C5); the completion family's are `completionArm`'s.  `dy` is the day
index's `day_of`, `sl` fork `slept_by_day`, `t` the entry's stamp and `d` its day.  **Since the owner's D105** (parity
P100) a `break_start` opens the running break (`Machine.brkOpen`, its stamp, planned minutes, place and day) and writes
nothing else, and a `break` line's arm ends whatever break is open (`brkFx` writes no running break) — so the pair is
matched in file order, whatever the `break` line's stamp (the binary writes the start's). -/
def arm (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    List Effect :=
  match e.ev with
  | .start id pred rep hsw sleptMin loc _ _ =>
    match endsBrk m t with
    | some o => endRecs o t ++ startArm dy (endMachine m o t) e.line t d id pred rep hsw sleptMin loc
    | none => startArm dy m e.line t d id pred rep hsw sleptMin loc
  | .pause id =>
    match m.block with
    | some b =>
      if b.id = id ∧ b.paused = false ∧ b.started.1 ≤ t.1 then
        let s := settle dy { m with block := some { b with paused := true, pausedAt := some t } }
        s.2 ++ [.machine s.1]
      else []
    | none => []
  | .unpause id =>
    match m.block with
    | some b =>
      if b.id = id ∧ b.paused = true then
        let s := settle dy { closePauseM m t with
          block := (closePauseM m t).block.map (fun b => { b with paused := false }) }
        (closePause dy m t).2 ++ s.2 ++ [.machine s.1]
      else []
    | none => []
  | .interrupt id =>
    let s := settle dy (interruptMachine m t d id)
    (closePause dy m t).2 ++ s.2 ++ [.machine s.1]
  | .resume lost dropped =>
    match m.interrupt with
    | some (s, sd, iid) =>
      let st := settle dy { m with block := m.block.map (fun b => resumeBlock b (some (s, t)) t), interrupt := none }
      [.dayAdd sd (.segment ⟨s, t, .interrupt iid⟩), .interruption ⟨e.line, some s, some t, sd, iid, lost.val, dropped⟩,
       .dayAdd sd (.lost lost.val dropped)] ++ st.2 ++ (netClosed dy s t sd st.1).2 ++
        [.machine (netClosed dy s t sd st.1).1]
    | none =>
      let st := settle dy { m with block := m.block.map (fun b => resumeBlock b none t) }
      [.interruption ⟨e.line, none, some t, d, none, lost.val, dropped⟩, .dayAdd d (.lost lost.val dropped)] ++
        st.2 ++ [.machine st.1]
  | .stop id _ =>
    match m.block with
    | some b =>
      if b.id = id then
        let r := cut dy m t
        r.2 ++ (runNet dy r.1).2 ++ [.itemAdd id .stop, .machine (runNet dy r.1).1]
      else []
    | none => []
  | .extend id by_ => .itemAdd id (.extend by_.val) :: extendFx m id by_.val
  | .done id est actual went tags ci isPartial =>
    doneFx dy m e.line t d id est.val actual.val went tags ci isPartial
  | .brk planned actual _ =>
    match m.brkEnded with
    | some s => if atEq s t then [.machine { m with brkEnded := none }] else brkArm dy sl m e t d planned.val (actual.map (·.val))
    | none => brkArm dy sl m e t d planned.val (actual.map (·.val))
  | .brkStart planned where_ =>
    match firstStart t d m with
    | some t0 => endBrkFx dy m ⟨t, planned.val, where_, d⟩ t0
    | none => brkStartArm dy m t d planned.val where_
  | _ => dayArm dy sl e t d

/-- **What a late mark names** (stage 6 W-48 track K): the replay warnings the machine meets as it steps an entry — a
`break` line whose word is not its `break_start`'s (the owner's **D116**, `brkPlace`), and a `break`, a `start` or an
interruption's `resume` stepped more than 31 ledger days behind the newest block the machine holds closed (the owner's
**D119**, `pastBound`: the `resume` read at its interruption's ledger day, the day its span is netted on).  Nothing
else warns here. -/
def lateWarnList (m : Machine) (e : Entry) (d : Nat) : List RWarn :=
  match e.ev with
  | .brk _ _ w =>
    ((pastBound d m.closed).map (fun hi => RWarn.pastBound e.line d hi)).toList ++
      (match m.brkOpen with
       | some o => if o.where_ = w then [] else [RWarn.breakPlace e.line o.where_ w]
       | none => [])
  | .start .. => ((pastBound d m.closed).map (fun hi => RWarn.pastBound e.line d hi)).toList
  | .resume .. =>
    match m.interrupt with
    | some (_, sd, _) => ((pastBound sd m.closed).map (fun hi => RWarn.pastBound e.line sd hi)).toList
    | none => []
  | _ => []

/-- **A late mark's warnings are only replay warnings.** -/
theorem lateWarns_rwarn (m : Machine) (e : Entry) (d : Nat) (x : Effect)
    (h : x ∈ (lateWarnList m e d).map Effect.rwarn) : ∃ w, x = .rwarn w := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 h
  exact ⟨w, rfl⟩

/-- What projects every replay warning to `none` projects a late mark's effects to nothing. -/
theorem lateWarns_filterMap {α : Type} (f : Effect → Option α) (hf : ∀ w, f (.rwarn w) = none) (m : Machine)
    (e : Entry) (d : Nat) : ((lateWarnList m e d).map Effect.rwarn).filterMap f = [] :=
  List.filterMap_eq_nil_iff.2 (fun x hx => by obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x hx; exact hf w)

/-- What no replay warning satisfies, no late mark's effect satisfies. -/
theorem lateWarns_any (P : Effect → Bool) (hP : ∀ w, P (.rwarn w) = false) (m : Machine) (e : Entry) (d : Nat) :
    ((lateWarnList m e d).map Effect.rwarn).any P = false :=
  List.any_eq_false.2 (fun x hx => by obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x hx; simp [hP w])

/-- What every replay warning satisfies, a late mark's effects satisfy. -/
theorem lateWarns_all (P : Effect → Bool) (hP : ∀ w, P (.rwarn w) = true) (m : Machine) (e : Entry) (d : Nat) :
    ((lateWarnList m e d).map Effect.rwarn).all P = true :=
  List.all_eq_true.2 (fun x hx => by obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x hx; exact hP w)

/-- **A late mark warns of no routine's status** (D116, D119): its warnings are the machine's, never fork
`Replay.warnings`' own kind. -/
theorem lateWarnList_not_status (m : Machine) (e : Entry) (d : Nat) :
    (lateWarnList m e d).filter (fun w => match w with | RWarn.unknownInstanceStatus .. => true | _ => false) = [] := by
  unfold lateWarnList pastBound
  split <;> (repeat' split) <;> simp

/-- **C4: the completion family's arms of fork `Machine::step`** (`done`'s `mark_done`, `routine`,
`skip`, `event`), one per event; they read no state and write none of the block family's.
* a non-partial `done` marks its id done on its day (fork `mark_done(id, t, day)`);
* a `routine` warns when its status is unknown (read as `Pending`, fork `parse_instance_status`),
  records the instance (**the last in file order wins**), and, when the status reads `done`, marks
  the item done on the date its `inst` names, else on its day (fork `parse_date(inst).unwrap_or(day)`).
  Its `Routine` segment and `routine_min` are day fields, C5's;
* a `skip` records the instance as `Skipped`, logged `"skipped"`;
* an `event` folds its occurrence into its `(name, id?)` key's `LatestNamed`, with its local date in
  the zone. -/
def completionCore (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) : List Effect :=
  match e.ev with
  | .done id _ _ _ _ _ isPartial => if isPartial then [] else [.markDone id t, .doneDate id d]
  | .routine item inst status actual =>
    (match Log.parseInstanceStatus status with
     | some _ => []
     | none => [.rwarn (.unknownInstanceStatus e.line status)]) ++
    .inst item inst ⟨t, (Log.parseInstanceStatus status).getD .pending, status, actual.map (·.val)⟩ ::
    (if Log.parseInstanceStatus status = some .done then
      [.markDone item t, .doneDate item ((Log.instDate? inst).getD d)] else [])
  | .skip item inst => [.inst item inst ⟨t, .skipped, "skipped".toList, none⟩]
  | .named name id => [.named name id e.line t (Cal.localDate z t.1)]
  | _ => []

/-- **C4's completion family, with the late marks the machine names first** (stage 6 W-48 track K, the owner's D116 and
D119): `lateWarnList`'s replay warnings, then the completion family's own arms (`completionCore`, C4's whole arm until
W-48).  The machine is the step's, read for the warnings alone. -/
def completionArm (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) : List Effect :=
  (lateWarnList m e d).map Effect.rwarn ++ completionCore z e t d

/-- **`effects` over a day function and a sleep lookup**: every entry's header (on its day, not cancelled:
C6's second pass heads the cancelled lines) and its bookkeeping, then its machine arm (the block or the day
family's) and its completion family's.  `sl` is fork `slept_by_day`, which the `energy` arm reads (C5). -/
def effectsWith (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    List Effect :=
  .header (dy e.t.val) (HeaderRec.of e false) :: .global (e.t.val, e.off.val) ::
    .seam (dy e.t.val) ⟨(e.t.val, e.off.val), seamKindOf e.ev⟩ ::
    (arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val) ++
      completionArm z st.machine e (e.t.val, e.off.val) (dy e.t.val))

/-- **Fork `Machine::step` as effects** (§8.2), over the day index `kw` and fork `slept_by_day` as the list
`slept` of `(day, slept_min)`, read by its first pair of a day. -/
def effects (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat)) (st : State) (e : Entry) :
    List Effect :=
  effectsWith z (dayOf z kw) (KMap.get slept) st e

def stepWith (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) : State :=
  applyEffects st (effectsWith z dy sl st e)

def step (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat)) (st : State) (e : Entry) : State :=
  applyEffects st (effects z kw slept st e)

/-- Fork `OpenBlock`, and — the owner's D99, README gap 4616 — `day`, its `start`'s ledger day (`Block.day`): the first of the days the host and D61's wall rule (`WallTimer.answer`) read its marks from, which fork `OpenBlock` had no field for. -/
structure OpenBlock where
  id : Id
  started : At
  workedMin : Nat
  since : Option At
  paused : Bool
  day : Nat
  /-- D108: the minutes its `extend`s have added since its `start` (`Block.ext`) — what `tm extend` added to its planned
  minutes, which D42's rebuild of `active.est_min` reads.  Fork `OpenBlock` had no such field. -/
  ext : Nat
deriving DecidableEq, Repr

/-- **The facts**: the state's maps, the observations in file order, the open block and interruption, (C4) the completion family and (C5) the day family's records. -/
structure Facts where
  days : HMap Nat DayAcc
  items : HMap Id ItemAcc
  itemDays : HMap (Nat × Id) Nat
  energy : List EnergyObs
  durations : List DurationObs
  interrupts : List Interruption
  headers : List (Nat × HeaderRec)
  openBlock : Option OpenBlock
  openInterrupt : Option Interruption
  /-- D105: the running break (`Machine.brkOpen` at the end of the log) -/
  openBreak : Option OpenBrk
  lastEffective : Option At
  entries : Nat
  /-- C4: fork `last_done` (and `done_items`, its keys) -/
  lastDoneMap : HMap Id At
  /-- C4: fork `done_dates` -/
  doneDates : HMap (Nat × Id) Unit
  /-- C4: fork `instances` -/
  instances : HMap (List Char × List Char) InstRec
  /-- C4: fork `LatestNamed` per `(name, id?)` -/
  named : HMap (List Char × Option Id) NamedRec
  /-- C4: fork `warnings`, in file order -/
  warnings : List RWarn
  /-- C5: fork `demotions`, each with its day, in file order -/
  demotions : List (Nat × Demotion)
  /-- C5: fork `closes`, each with its day, in file order -/
  closes : List (Nat × CloseRec)
  /-- C5: fork `dropped_items` -/
  dropped : HMap Id Unit
  /-- C5: fork `longest_leak` -/
  longestLeak : Option LeakRec
  /-- C5: fork `unknown` -/
  unknown : Nat
  /-- C6: fork `seams`, each day's idle marks in file order -/
  seams : HMap Nat SeamAcc
deriving DecidableEq, Repr

/-- Fork `Replay::last_done(id)`. -/
def Facts.lastDone (f : Facts) (i : Id) : Option At := f.lastDoneMap.get i

/-- Fork `Replay::instance(item, inst)`. -/
def Facts.instance (f : Facts) (item inst : List Char) : Option InstRec := f.instances.get (item, inst)

/-- The `LatestNamed` of one `(name, id?)` key. -/
def Facts.namedAt (f : Facts) (name : List Char) (id : Option Id) : Option NamedRec := f.named.get (name, id)

/-- Whether `(d, i)` is one of fork `done_dates`. -/
def Facts.doneOn (f : Facts) (i : Id) (d : Nat) : Bool := (f.doneDates.get (d, i)).isSome

/-- **An item's completion dates**, out of a `doneDates` map.  `factsView`'s
`doneFirst` and `doneCount` rows and `Seal.datesOf` were three spellings of this
one body; they are all this function now (AGENTS §5.3, stage 6 step K3b). -/
def doneDatesIn (m : HMap (Nat × Id) Unit) (i : Id) : List Nat :=
  (m.pairs.filter (fun p => decide (p.1.2 = i))).map (·.1.1)

/-- An item's completion dates in the facts. -/
def Facts.doneDatesOf (f : Facts) (i : Id) : List Nat := doneDatesIn f.doneDates i

/-- **Fork `Replay::is_done`**: `done_items` is the key set of `last_done` (C4),
so an item is done exactly when it has a last completion. -/
def Facts.isDone (f : Facts) (i : Id) : Bool := (f.lastDoneMap.get i).isSome

/-- **Fork `Replay::instances_of(item)`**: every `(inst, record)` the log has for
one item.  The fork iterates a `BTreeMap<String, _>`, so its order is the `inst`
string's; this is bucket order and every caller that depends on the order sorts
first (stage 6 step K3b's `loggedInstances`). -/
def Facts.instancesOf (f : Facts) (item : List Char) : List (List Char × InstRec) :=
  (f.instances.pairs.filter (fun p => decide (p.1.1 = item))).map (fun p => (p.1.2, p.2))

theorem mem_instancesOf (f : Facts) (item ins : List Char) (r : InstRec) :
    (ins, r) ∈ f.instancesOf item ↔ ((item, ins), r) ∈ f.instances.pairs := by
  unfold Facts.instancesOf
  constructor
  · intro h
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 h
    obtain ⟨hm, hf⟩ := List.mem_filter.1 hq
    have h1 : q.1.1 = item := of_decide_eq_true hf
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨h2, h3⟩ := hqe
    have : q = ((item, ins), r) := by
      obtain ⟨⟨a, b⟩, c⟩ := q
      simp_all
    exact this ▸ hm
  · intro h
    exact List.mem_map.2 ⟨((item, ins), r), List.mem_filter.2 ⟨h, by simp⟩, rfl⟩

/-! ### The two sorts of `finish` -/

/-- Insert before the first element `a` may precede. -/
def insBy {α : Type} (le : α → α → Bool) (a : α) : List α → List α
  | [] => [a]
  | b :: l => if le a b then a :: b :: l else b :: insBy le a l

/-- **Insertion sort**, the specification of a stable sort (`decide` evaluates it); compiled as core's
merge sort through `insSort_eq_mergeSort`. -/
def insSort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | a :: l => insBy le a (insSort le l)

theorem insBy_append {α : Type} (le : α → α → Bool) (a : α) :
    ∀ (l₁ l₂ : List α), (∀ b ∈ l₁, le a b = false) → (∀ b ∈ l₂, le a b = true) →
      insBy le a (l₁ ++ l₂) = l₁ ++ a :: l₂
  | [], [], _, _ => rfl
  | [], b :: l₂, _, h₂ => by simp [insBy, h₂ b (List.mem_cons_self ..)]
  | b :: l₁, l₂, h₁, h₂ => by
    simp only [List.cons_append, insBy, h₁ b (List.mem_cons_self ..), Bool.false_eq_true, if_false,
      List.cons.injEq, true_and]
    exact insBy_append le a l₁ l₂ (fun c hc => h₁ c (List.mem_cons_of_mem _ hc)) h₂

/-- **Every stable sort is merge sort**: for a transitive, total comparison, insertion sort and core's
`mergeSort` agree on every list (by `List.mergeSort_cons`). -/
theorem insSort_eq_mergeSort {α : Type} (le : α → α → Bool) (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) : ∀ (l : List α), insSort le l = l.mergeSort le
  | [] => by simp [insSort]
  | a :: l => by
    obtain ⟨l₁, l₂, h1, h2, h3⟩ := List.mergeSort_cons trans total a l
    have hs := List.pairwise_mergeSort trans total (a :: l)
    rw [h1] at hs
    have hl₂ : ∀ b ∈ l₂, le a b = true := fun b hb =>
      List.rel_of_pairwise_cons (List.pairwise_append.1 hs).2.1 hb
    rw [insSort, insSort_eq_mergeSort le trans total l, h2, h1]
    exact insBy_append le a l₁ l₂ (fun b hb => by simpa using h3 b hb) hl₂

def obsLe (a b : EnergyObs) : Bool := decide (a.line ≤ b.line)

/-- Observations by line (fork `energy.sort_by_key(|o| o.line)`, a stable sort). -/
def sortObs (l : List EnergyObs) : List EnergyObs := insSort obsLe l

def sortObsFast (l : List EnergyObs) : List EnergyObs := l.mergeSort obsLe

@[csimp] theorem sortObs_eq_sortObsFast : @sortObs = @sortObsFast := by
  funext l
  exact insSort_eq_mergeSort obsLe (fun a b c h₁ h₂ => by simp [obsLe] at *; omega)
    (fun a b => by simp [obsLe]; omega) l

def segLe (a b : Segment) : Bool := decide (a.start.1 ≤ b.start.1)

/-- A day's segments by start (fork `segments.sort_by_key(|s| s.start)`, a stable sort). -/
def sortSegs (l : List Segment) : List Segment := insSort segLe l

def sortSegsFast (l : List Segment) : List Segment := l.mergeSort segLe

@[csimp] theorem sortSegs_eq_sortSegsFast : @sortSegs = @sortSegsFast := by
  funext l
  exact insSort_eq_mergeSort segLe
    (fun a b c h₁ h₂ => by
      simp only [segLe, decide_eq_true_eq, Cal.Instant.le_iff] at *; omega)
    (fun a b => by
      simp only [segLe, Bool.or_eq_true, decide_eq_true_eq, Cal.Instant.le_iff]; omega) l

/-- A day in the fork's order: pushes in file order, segments sorted by start. -/
def DayAcc.finish (a : DayAcc) : DayAcc :=
  { a with starts := a.starts.reverse, done := a.done.reverse, dropped := a.dropped.reverse,
           segments := sortSegs a.segments.reverse, locChanges := a.locChanges.reverse, idle := a.idle.reverse,
           breaks := a.breaks.reverse }

def ItemAcc.finish (a : ItemAcc) : ItemAcc :=
  { a with doneAt := a.doneAt.reverse, partialDoneAt := a.partialDoneAt.reverse }

/-- **The open block, read at the end of the log** — fork `Machine::finish`'s, as the machine holds it: since the owner's
D99 the machine settles it at every mark (`settle`), so what it holds is already the reading every later mark agrees
with — its pieces drawn, its minutes theirs, its clock running from where every span it nets ends (README gaps 4520a
and 4525).  D94 read past a break held ahead of the clock here (lastEndAfter, deleted with it). -/
def openOf (m : Machine) : Option OpenBlock :=
  m.block.map (fun b => ⟨b.id, b.started, b.workedMin, b.since, b.paused, b.day, b.ext⟩)

/-- **A duration observation read net** (the owner's D100, README gap 4520b): its `actual_min` less what breaks logged
after its `done` took from its block (`DayAcc.durNet` on its day). -/
def netDur (a : Option DayAcc) (o : DurationObs) : DurationObs :=
  match a.bind (fun x => x.durNet.get o.line) with
  | some k => { o with actualMin := o.actualMin - k }
  | none => o

/-- Reading a duration observation net keeps its line. -/
theorem map_line_netDur (f : DurationObs → Option DayAcc) :
    ∀ (l : List DurationObs), (l.map (fun o => netDur (f o) o)).map (·.line) = l.map (·.line)
  | [] => rfl
  | o :: l => by
    simp only [List.map_cons, map_line_netDur f l, List.cons.injEq, and_true]
    unfold netDur; split <;> rfl

/-- Reading a duration observation net keeps its day. -/
theorem netDur_day (a : Option DayAcc) (o : DurationObs) : (netDur a o).day = o.day := by
  unfold netDur; split <;> rfl

/-- **One day's observations, read net** (the owner's D100): filtering a day out of the net reading is netting that day's
own, by that day's record. -/
theorem filter_map_netDur (f : Nat → Option DayAcc) (d : Nat) :
    ∀ (l : List DurationObs), (l.map (fun o => netDur (f o.day) o)).filter (fun o => decide (o.day = d)) =
      (l.filter (fun o => decide (o.day = d))).map (netDur (f d))
  | [] => rfl
  | o :: l => by
    simp only [List.map_cons, List.filter_cons, netDur_day]
    by_cases h : o.day = d
    · simp only [h, decide_true, if_true, List.map_cons, filter_map_netDur f d l]
    · simp only [h, decide_false, Bool.false_eq_true, if_false, filter_map_netDur f d l]

/-- **Fork `Machine::finish`**: the open block and interruption; the observations by line (a start's
pending observation is emitted here, and the sort puts it at its start's line, where the fork pushed it);
every day's segments sorted by start; every list back in file order.  Since the owner's D94 the open block is read
by `openOf`. -/
def finish (st : State) : Facts :=
  { days := st.days.mapVals DayAcc.finish, items := st.items.mapVals ItemAcc.finish,
    itemDays := st.itemDays,
    energy := sortObs (st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList),
    durations := st.durations.reverse.map (fun o => netDur (st.days.get o.day) o),
    interrupts := st.interrupts.reverse, headers := st.headers.reverse,
    openBlock := openOf st.machine,
    openInterrupt := st.machine.interrupt.map (fun i => ⟨0, some i.1, none, i.2.1, i.2.2, 0, []⟩),
    openBreak := st.machine.brkOpen,
    lastEffective := st.global.lastEffective, entries := st.global.entries,
    lastDoneMap := st.lastDone, doneDates := st.doneDates, instances := st.instances, named := st.named,
    warnings := st.rwarns.reverse, demotions := st.demotions.reverse, closes := st.closes.reverse,
    dropped := st.dropped, longestLeak := st.longestLeak, unknown := st.unknown,
    seams := st.seams.mapVals (fun a => { a with idleMarks := a.idleMarks.reverse }) }

/-- A wake's `slept_min`. -/
def sleptOf (e : Entry) : Option Nat :=
  match e.ev with
  | .wake s _ => some s.val
  | _ => none

/-- **C5: fork `slept_by_day`** (inventory §2.1 item 4): for each surviving wake in file order, its day and
its `slept_min`.  Read by its first pair of a day (`KMap.get`), so the first wake **in file order** wins
(`entry(day).or_insert(slept_min)`), built before the walk. -/
def sleptByDay (z : Cal.Tz) (kw : List Cal.Instant) (sv : List Entry) : List (Nat × Nat) :=
  sv.filterMap (fun e => (sleptOf e).map (fun s => (dayOf z kw e.t.val, s)))

/-- **The replay** (§8.2): the survivors of the mask, stepped in file order over the day index of their
wakes and fork `slept_by_day`, then `finish`. -/
def replay (z : Cal.Tz) (es : List Entry) : Facts :=
  finish ((survivors es).foldl (step z (dayIndexOf z es) (sleptByDay z (dayIndexOf z es) (survivors es)))
    (State.init es.length))

/-- One wake into the compiled `slept_by_day`: a day's first wake is kept (`o.or`). -/
def sleptStep (dy : Cal.Instant → Nat) (m : HMap Nat Nat) (e : Entry) : HMap Nat Nat :=
  match sleptOf e with
  | some s => m.alter (dy e.t.val) (fun o => o.or (some s))
  | none => m

/-- The compiled `slept_by_day`: a bucketed map, one `alter` a wake (a `foldl`, D9-21). -/
def sleptMap (dy : Cal.Instant → Nat) (sv : List Entry) (n : Nat) : HMap Nat Nat :=
  sv.foldl (sleptStep dy) (HMap.empty n)

/-- The compiled replay: the day index looked up by bisection (`dayOfArr`, as `entryDaysFast` does), and
`slept_by_day` in buckets. -/
def replayFast (z : Cal.Tz) (es : List Entry) : Facts :=
  let sv := survivors es
  let dy := dayOfArr z (keptWakes z (wakeInstants sv)).toArray
  let sm := sleptMap dy sv es.length
  finish (sv.foldl (stepWith z dy (fun d => sm.get d)) (State.init es.length))

/-- The replay's `slept_by_day` lookup (fork `slept_by_day.get(&day)`). -/
def slOf (z : Cal.Tz) (es : List Entry) : Nat → Option Nat :=
  KMap.get (sleptByDay z (dayIndexOf z es) (survivors es))

/-- The facts' accessors of `credit_conserves_the_day_minutes`. -/
def sumByCi (f : Facts) (d : Nat) : Nat :=
  match f.days.get d with
  | some a => a.byCi.sum
  | none => 0

def ciSum (m : KMap Id Nat) : Nat := (m.map Prod.snd).sum

def sumCiUnknown (f : Facts) (d : Nat) : Nat :=
  match f.days.get d with
  | some a => ciSum a.ciUnknown
  | none => 0

def blockMin (f : Facts) (d : Nat) : Nat :=
  match f.days.get d with
  | some a => a.blockMin
  | none => 0

end Machine

/-! ### The laws of the map -/

section MapLaws

namespace KMap

variable {κ β : Type} [DecidableEq κ]

theorem get_nil (j : κ) : get ([] : KMap κ β) j = none := rfl

theorem get_cons (p : κ × β) (m : KMap κ β) (j : κ) :
    get (p :: m) j = if p.1 = j then some p.2 else get m j := by
  unfold get
  by_cases h : p.1 = j <;> simp [h]

theorem get_append (l₁ l₂ : KMap κ β) (j : κ) : get (l₁ ++ l₂) j = (get l₁ j).or (get l₂ j) := by
  unfold get
  rw [List.find?_append]
  cases l₁.find? (fun p => decide (p.1 = j)) <;> simp

theorem get_eq_none_of_keys (l : KMap κ β) (j : κ) (h : ∀ q ∈ l, q.1 ≠ j) : get l j = none := by
  unfold get
  rw [List.find?_eq_none.2 (fun q hq => by simpa using h q hq)]
  rfl

theorem get_eq_none_iff_keys (l : KMap κ β) (j : κ) : get l j = none ↔ ∀ q ∈ l, q.1 ≠ j := by
  refine ⟨fun h q hq hqj => ?_, get_eq_none_of_keys l j⟩
  unfold get at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  exact h q hq (by simp [hqj])

theorem get_filter_key (l : KMap κ β) (k j : κ) :
    get (l.filter (fun q => !decide (q.1 = k))) j = if j = k then none else get l j := by
  induction l with
  | nil => simp [get_nil]
  | cons q l ih =>
    by_cases hq : q.1 = k
    · rw [List.filter_cons_of_neg (by simp [hq]), ih, get_cons]
      by_cases hj : j = k
      · simp [hj]
      · simp [hj, show q.1 ≠ j from fun h => hj (h.symm.trans hq)]
    · rw [List.filter_cons_of_pos (by simp [hq]), get_cons, ih, get_cons]
      by_cases hj : j = k
      · subst hj; simp [hq]
      · simp [hj]

theorem get_alterGo (k : κ) (f : Option β → Option β) (orig : KMap κ β) (j : κ) :
    ∀ (l acc : KMap κ β), orig = acc.reverse ++ l → (∀ q ∈ acc, q.1 ≠ k) →
      get (alterGo k f orig acc l) j = if j = k then f (get orig k) else get orig j := by
  intro l
  induction l with
  | nil =>
    intro acc ho hacc
    have hn : get orig k = none := by
      rw [ho, List.append_nil]; exact get_eq_none_of_keys _ _ (fun q hq => hacc q (List.mem_reverse.1 hq))
    unfold alterGo
    rw [hn]
    cases hf : f none with
    | some v =>
      simp only [get_cons]
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    | none =>
      by_cases hj : j = k
      · subst hj; simp [hn]
      · simp [hj]
  | cons p rest ih =>
    intro acc ho hacc
    have hacc' : get acc.reverse k = none :=
      get_eq_none_of_keys _ _ (fun q hq => hacc q (List.mem_reverse.1 hq))
    unfold alterGo
    by_cases hp : p.1 = k
    · have hok : get orig k = some p.2 := by
        rw [ho, get_append, hacc', get_cons, if_pos hp]; rfl
      rw [if_pos hp, hok]
      cases hf : f (some p.2) with
      | some v =>
        simp only [List.reverseAux_eq]
        rw [get_append, get_cons]
        by_cases hj : j = k
        · subst hj; simp [hacc']
        · rw [if_neg hj, if_neg (Ne.symm hj), ho, get_append, get_cons, if_neg (fun h : p.1 = j => hj (h.symm.trans hp))]
      | none =>
        simp only [List.reverseAux_eq]
        rw [get_append, get_filter_key]
        by_cases hj : j = k
        · subst hj; simp [hacc']
        · rw [if_neg hj, if_neg hj, ho, get_append, get_cons, if_neg (fun h : p.1 = j => hj (h.symm.trans hp))]
    · rw [if_neg hp]
      exact ih (p :: acc) (by rw [ho]; simp) (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hacc q hq)

/-- **The map's law**: altering a key changes what that key reads by `f` and nothing else, on every
list (duplicate keys included). -/
theorem get_alter (m : KMap κ β) (k j : κ) (f : Option β → Option β) :
    get (m.alter k f) j = if j = k then f (get m k) else get m j := by
  unfold alter
  split
  · rename_i hg
    cases hf : f none with
    | some v =>
      rw [get_cons]
      by_cases hj : j = k
      · subst hj; simp [hg, hf]
      · simp [hj, Ne.symm hj]
    | none =>
      by_cases hj : j = k
      · subst hj; simp [hg, hf]
      · simp [hj]
  · exact get_alterGo k f m j m [] (by simp) (by simp)

theorem get_map_snd {γ : Type} (m : KMap κ β) (f : β → γ) (j : κ) :
    get (m.map (fun p => (p.1, f p.2))) j = (get m j).map f := by
  induction m with
  | nil => rfl
  | cons p m ih =>
    rw [List.map_cons, get_cons, get_cons, ih]
    split <;> rfl

/-- The sum of a map's values. -/
def vsum (m : KMap κ Nat) : Nat := (m.map Prod.snd).sum

omit [DecidableEq κ] in
theorem vsum_append (l₁ l₂ : KMap κ Nat) : vsum (l₁ ++ l₂) = vsum l₁ + vsum l₂ := by
  simp [vsum, List.sum_append]

omit [DecidableEq κ] in
theorem vsum_cons (p : κ × Nat) (l : KMap κ Nat) : vsum (p :: l) = p.2 + vsum l := by
  simp [vsum]

omit [DecidableEq κ] in
theorem vsum_reverse (l : KMap κ Nat) : vsum l.reverse = vsum l := by
  simp [vsum, List.sum_reverse]

theorem get_le_vsum (l : KMap κ Nat) (k : κ) : (get l k).getD 0 ≤ vsum l := by
  induction l with
  | nil => simp [get_nil]
  | cons p l ih =>
    rw [get_cons, vsum_cons]
    split
    · simp
    · omega

theorem mem_keys_of_get (l : KMap κ β) (k : κ) (v : β) (h : get l k = some v) : k ∈ l.map Prod.fst := by
  unfold get at h
  cases hf : l.find? (fun p => decide (p.1 = k)) with
  | none => rw [hf] at h; cases h
  | some q =>
    have hm := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    simp only [decide_eq_true_eq] at hk
    exact List.mem_map.2 ⟨q, hm, hk⟩

theorem filter_key_of_not_mem (l : KMap κ β) (k : κ) (h : k ∉ l.map Prod.fst) :
    l.filter (fun q => !decide (q.1 = k)) = l := by
  apply List.filter_eq_self.2
  intro q hq
  have : q.1 ≠ k := fun he => h (List.mem_map.2 ⟨q, hq, he⟩)
  simp [this]

/-- **The sum after an alteration**, on a map whose keys are distinct (which it keeps). -/
theorem vsum_alterGo (k : κ) (f : Option Nat → Option Nat) (orig : KMap κ Nat)
    (hnd : (orig.map Prod.fst).Nodup) :
    ∀ (l acc : KMap κ Nat), orig = acc.reverse ++ l → (∀ q ∈ acc, q.1 ≠ k) →
      ((alterGo k f orig acc l).map Prod.fst).Nodup ∧
      vsum (alterGo k f orig acc l) + (get orig k).getD 0 = vsum orig + (f (get orig k)).getD 0 := by
  intro l
  induction l with
  | nil =>
    intro acc ho hacc
    have hn : get orig k = none := by
      rw [ho, List.append_nil]; exact get_eq_none_of_keys _ _ (fun q hq => hacc q (List.mem_reverse.1 hq))
    unfold alterGo
    rw [hn]
    cases hf : f none with
    | some v =>
      refine ⟨?_, ?_⟩
      · refine List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩
        obtain ⟨q, hq, hqk⟩ := List.mem_map.1 hm
        rw [ho, List.append_nil] at hq
        exact hacc q (List.mem_reverse.1 hq) hqk
      · simp [vsum_cons]; omega
    | none => exact ⟨hnd, rfl⟩
  | cons p rest ih =>
    intro acc ho hacc
    have hacc' : get acc.reverse k = none :=
      get_eq_none_of_keys _ _ (fun q hq => hacc q (List.mem_reverse.1 hq))
    unfold alterGo
    by_cases hp : p.1 = k
    · have hok : get orig k = some p.2 := by
        rw [ho, get_append, hacc', get_cons, if_pos hp]; rfl
      rw [if_pos hp, hok]
      have hnd' := hnd
      rw [ho, List.map_append] at hnd'
      cases hf : f (some p.2) with
      | some v =>
        simp only [List.reverseAux_eq]
        refine ⟨?_, ?_⟩
        · simpa [hp] using hnd'
        · rw [ho, vsum_append, vsum_append, vsum_cons, vsum_cons]; simp; omega
      | none =>
        simp only [List.reverseAux_eq]
        have hnk : k ∉ rest.map Prod.fst := by
          have h2 : ((p :: rest).map Prod.fst).Nodup := (List.nodup_append.1 hnd').2.1
          rw [List.map_cons, List.nodup_cons] at h2
          rw [← hp]; exact h2.1
        rw [filter_key_of_not_mem _ _ hnk]
        refine ⟨?_, ?_⟩
        · rw [List.map_append]
          exact (List.Sublist.append_left (List.Sublist.map Prod.fst (List.sublist_cons_self p rest)) _).nodup hnd'
        · rw [ho, vsum_append, vsum_append, vsum_cons]; simp; omega
    · rw [if_neg hp]
      exact ih (p :: acc) (by rw [ho]; simp) (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hacc q hq)

theorem vsum_alter (m : KMap κ Nat) (k : κ) (f : Option Nat → Option Nat) (hnd : (m.map Prod.fst).Nodup) :
    ((m.alter k f).map Prod.fst).Nodup ∧
      vsum (m.alter k f) + (get m k).getD 0 = vsum m + (f (get m k)).getD 0 := by
  unfold alter
  split
  · rename_i hg
    cases hf : f none with
    | some v =>
      refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, ?_⟩
      · obtain ⟨q, hq, hqk⟩ := List.mem_map.1 hm
        have := get_eq_none_iff_keys m k
        exact (this.1 hg) q hq hqk
      · simp [vsum_cons, hg, hf]; omega
    | none => simp [hg, hf]; exact hnd
  · exact vsum_alterGo k f m hnd m [] (by simp) (by simp)

end KMap

namespace HMap

variable {κ β : Type} [DecidableEq κ] [KeyHash κ]

/-- **The bucketed map's law**, on every map. -/
theorem get_alter (m : HMap κ β) (k j : κ) (f : Option β → Option β) :
    get (m.alter k f) j = if j = k then f (get m k) else get m j := by
  unfold alter
  by_cases h0 : m.size = 0
  · rw [if_pos h0]
    have hn : ∀ x : κ, get m x = none := fun x => by
      unfold get
      rw [show m[KeyHash.hash x % m.size]? = none from by rw [Array.getElem?_eq_none]; rw [h0]; exact Nat.zero_le _]
    rw [hn k, hn j]
    simp only [get, List.size_toArray, List.length_singleton, Nat.mod_one]
    simp [KMap.get_alter, KMap.get_nil]
  · rw [if_neg h0]
    have hpos : 0 < m.size := Nat.pos_of_ne_zero h0
    have hlt : ∀ x : κ, KeyHash.hash x % m.size < m.size := fun x => Nat.mod_lt _ hpos
    unfold get
    simp only [Array.size_modify, Array.getElem?_modify, Array.getElem?_eq_getElem (hlt j),
      Array.getElem?_eq_getElem (hlt k)]
    by_cases hjk : j = k
    · subst hjk; simp [KMap.get_alter]
    · by_cases hs : KeyHash.hash k % m.size = KeyHash.hash j % m.size
      · simp [hs, KMap.get_alter, hjk]
      · simp [hs, hjk]

theorem get_mapVals {γ : Type} (m : HMap κ β) (f : β → γ) (j : κ) :
    get (m.mapVals f) j = (get m j).map f := by
  unfold get mapVals
  have e1 : (⟨(Array.toList m).map (fun b => b.map (fun p => (p.1, f p.2)))⟩ : Array (KMap κ γ)).size = m.size := by simp
  rw [e1]
  have e2 : (⟨(Array.toList m).map (fun b => b.map (fun p => (p.1, f p.2)))⟩ : Array (KMap κ γ))[KeyHash.hash j % m.size]?
      = (m[KeyHash.hash j % m.size]?).map (fun b => b.map (fun p => (p.1, f p.2))) := by
    simp
  rw [e2]
  cases m[KeyHash.hash j % m.size]? with
  | none => rfl
  | some b => exact KMap.get_map_snd b f j

theorem get_empty (n : Nat) (j : κ) : get (empty n : HMap κ β) j = none := by
  unfold get empty
  simp only [Array.size_replicate, Array.getElem?_replicate]
  rw [if_pos (Nat.mod_lt _ (Nat.succ_pos n))]
  rfl

end HMap

end MapLaws

/-! ### The compiled replay (`@[csimp]`, D9-21) -/

section Compiled

open Log (Id U8 U32 Num)

/-- The compiled `slept_by_day` answers as the specification's list does: a map folded over the wakes,
each day's first kept, is the first pair of each day. -/
theorem foldl_sleptStep_get (dy : Cal.Instant → Nat) (d : Nat) : ∀ (sv : List Entry) (m : HMap Nat Nat),
    (sv.foldl (sleptStep dy) m).get d
      = (m.get d).or (KMap.get (sv.filterMap (fun e => (sleptOf e).map (fun s => (dy e.t.val, s)))) d)
  | [], m => by simp [KMap.get_nil]
  | e :: sv, m => by
    rw [List.foldl_cons, foldl_sleptStep_get dy d sv, List.filterMap_cons]
    unfold sleptStep
    cases h : sleptOf e with
    | none => rfl
    | some s =>
      simp only [Option.map_some, HMap.get_alter, KMap.get_cons]
      by_cases hd : d = dy e.t.val
      · subst hd; cases HMap.get m (dy e.t.val) <;> simp
      · simp [hd, Ne.symm hd]

@[csimp] theorem replay_eq_replayFast : @replay = @replayFast := by
  funext z es
  unfold replay replayFast step effects stepWith
  have h : dayOf z (dayIndexOf z es) = dayOfArr z (keptWakes z (wakeInstants (survivors es))).toArray := by
    funext t
    unfold dayOfArr dayOf dayIndexOf
    rw [lastWakeLeArr_eq_lastWakeLe _ (keptWakes_sorted z _)]
  have hs : KMap.get (sleptByDay z (dayIndexOf z es) (survivors es))
      = fun d => (sleptMap (dayOfArr z (keptWakes z (wakeInstants (survivors es))).toArray) (survivors es)
          es.length).get d := by
    funext d
    unfold sleptMap sleptByDay
    rw [foldl_sleptStep_get, HMap.get_empty, Option.none_or, h]
  simp only
  rw [hs, h]

end Compiled

/-! ### The frame law, and one header per entry -/

section MachineLaws

open Log (Id U8 U32 Num)

theorem valueAt_applyEffect (st : State) (e : Effect) (k : Key) (h : k ≠ e.key) :
    (applyEffect st e).valueAt k = st.valueAt k := by
  cases e with
  | dayAdd d op =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : d' ≠ d := fun e => h (by rw [e]; rfl)
    rw [HMap.get_alter, if_neg this]
  | header d hr =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : d ≠ d' := fun e => h (by rw [e]; rfl)
    simp [this]
  | itemAdd i op =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : i' ≠ i := fun e => h (by rw [e]; rfl)
    rw [HMap.get_alter, if_neg this]
  | itemDay i d m =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : (d', i') ≠ (d, i) := fun e => h (by simp only [Prod.mk.injEq] at e; rw [e.1, e.2]; rfl)
    rw [HMap.get_alter, if_neg this]
  | itemDaySub i d m =>
    simp only [applyEffect]
    split
    · rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
        simp only [State.valueAt]
      have : (d', i') ≠ (d, i) := fun e => h (by simp only [Prod.mk.injEq] at e; rw [e.1, e.2]; rfl)
      rw [HMap.get_alter, if_neg this]
    · rfl
  | obs o =>
    cases o with
    | energy o =>
      rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
        simp only [applyEffect, State.valueAt]
      have : o.day ≠ d' := fun e => h (by rw [← e]; rfl)
      simp [this]
    | duration o =>
      rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
        simp only [applyEffect, State.valueAt]
      have : o.day ≠ d' := fun e => h (by rw [← e]; rfl)
      simp [this]
  | interruption r =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : r.day ≠ d' := fun e => h (by rw [← e]; rfl)
    simp [this]
  | machine m =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    exact absurd rfl h
  | global t =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    exact absurd rfl h
  | markDone i t =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : i' ≠ i := fun e => h (by rw [e]; rfl)
    rw [HMap.get_alter, if_neg this]
  | doneDate i d =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : (d', i') ≠ (d, i) := fun e => h (by simp only [Prod.mk.injEq] at e; rw [e.1, e.2]; rfl)
    rw [HMap.get_alter, if_neg this]
  | inst item inst r =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    · by_cases hk : (it', is') = (item, inst)
      · simp only [Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        cases hd : Log.instDate? is' with
        | some d0 =>
          have hne : d0 ≠ d' := fun e => h (by simp only [Effect.key, hd, e])
          simp [hne]
        | none => simp
      · rw [HMap.get_alter, if_neg hk]
    · by_cases hk : (it', is') = (item, inst)
      · simp only [Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        cases hd : Log.instDate? is' with
        | some d0 => simp
        | none => exact absurd (by simp only [Effect.key, hd]) h
      · rw [HMap.get_alter, if_neg hk]
  | named name id line t date =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : (n', id') ≠ (name, id) := fun e => h (by simp only [Prod.mk.injEq] at e; rw [e.1, e.2]; rfl)
    rw [HMap.get_alter, if_neg this]
  | rwarn w =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    exact absurd rfl h
  | demote d r =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : d ≠ d' := fun e => h (by rw [e]; rfl)
    simp [this]
  | close d r =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : d ≠ d' := fun e => h (by rw [e]; rfl)
    simp [this]
  | drop i =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : i' ≠ i := fun e => h (by rw [e]; rfl)
    rw [HMap.get_alter, if_neg this]
  | leak r =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    exact absurd rfl h
  | unknown =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    exact absurd rfl h
  | seam d op =>
    rcases k with d' | ⟨i', d'⟩ | i' | _ | _ | ⟨i', d'⟩ | ⟨it', is', d'⟩ | ⟨it', is'⟩ | ⟨n', id'⟩ <;>
      simp only [applyEffect, State.valueAt]
    have : d' ≠ d := fun e => h (by rw [e]; rfl)
    rw [HMap.get_alter, if_neg this]

/-- **The frame law** (§8.2, Goals): applying effects changes only the keys they name. -/
theorem applyEffects_touches_only_named_keys (st : State) (fx : List Effect) (k : Key)
    (h : k ∉ fx.map Effect.key) : (applyEffects st fx).valueAt k = st.valueAt k := by
  induction fx generalizing st with
  | nil => rfl
  | cons e fx ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    exact (ih (applyEffect st e) h.2).trans (valueAt_applyEffect st e k h.1)

def Effect.energyOf? : Effect → Option EnergyObs
  | .obs (.energy o) => some o
  | _ => none

def Effect.durationOf? : Effect → Option DurationObs
  | .obs (.duration o) => some o
  | _ => none

def Effect.machineOf? : Effect → Option Machine
  | .machine m => some m
  | _ => none

/-- **The block family's plain effects**: a day's record other than an uncredit, an item's, an item-day's,
an observation, an interruption.  Not a header, the machine, the bookkeeping, a completion or (C5) a day
family's record outside a day (`Effect.isRec`). -/
def Effect.plain : Effect → Bool
  | .dayAdd _ (.uncredit _ _) => false
  | .dayAdd _ (.net _ _ _ _) => false
  | .dayAdd _ _ => true
  | .itemAdd _ _ => true
  | .itemDay _ _ _ => true
  | .itemDaySub _ _ _ => true
  | .obs _ => true
  | .interruption _ => true
  | _ => false

/-- **C5: the day family's records outside a day's record**: a demotion, a close, a drop, a leak, an
unknown event. -/
def Effect.isRec : Effect → Bool
  | .demote _ _ => true
  | .close _ _ => true
  | .drop _ => true
  | .leak _ => true
  | .unknown => true
  | _ => false

/-- **What a re-draw writes is plain** (D99): segments drawn and un-drawn, nothing else. -/
theorem redraw_plain (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) :
    ∀ x ∈ (redraw dy id old P).2, x.plain = true := by
  intro x hx
  unfold redraw at hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨p, -, rfl⟩ | ⟨q, -, rfl⟩ <;> rfl

theorem settle_plain (dy : Cal.Instant → Nat) (m : Machine) :
    ∀ x ∈ (settle dy m).2, x.plain = true := by
  unfold settle
  split
  · exact redraw_plain dy _ _ _
  · simp

theorem closePause_plain (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    ∀ x ∈ (closePause dy m t).2, x.plain = true := by
  unfold closePause
  split
  · split
    · split <;> simp [Effect.plain]
    · simp
  · simp

theorem creditFx_plain (dy : Cal.Instant → Nat) (id : Id) (t : At) (min : Nat) (ci : Option U8) :
    ∀ x ∈ creditFx dy id t min ci, x.plain = true := by
  simp [creditFx, Effect.plain]

theorem obsFx_plain (o : Option EnergyObs) : ∀ x ∈ obsFx o, x.plain = true := by
  cases o <;> simp [obsFx, Effect.plain]

theorem cut_plain (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    ∀ x ∈ (cut dy m t).2, x.plain = true := by
  unfold cut
  split
  · intro x hx
    simp only [List.mem_append] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact redraw_plain dy _ _ _ x hx
    · exact closePause_plain dy _ t x hx
    · exact creditFx_plain dy _ t _ none x hx
    · exact obsFx_plain _ x hx
  · simp

theorem not_header_of_plain (x : Effect) (h : x.plain = true) : x.isHeader = false := by
  cases x <;> simp_all [Effect.plain, Effect.isHeader]

theorem uncreditFx_no_header (c : Cut) : ∀ x ∈ uncreditFx c, x.isHeader = false := by
  unfold uncreditFx; split <;> simp [Effect.isHeader]

theorem doneClose_no_header (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat)
    (went : Option U8) : ∀ x ∈ (doneClose dy m t id actual went).2, x.isHeader = false := by
  intro x hx
  unfold doneClose at hx
  split at hx
  · split at hx
    · simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact not_header_of_plain x (redraw_plain dy _ _ _ x hx)
      · exact not_header_of_plain x (closePause_plain dy _ t x hx)
      · exact not_header_of_plain x (obsFx_plain _ x hx)
    · simp at hx
  · split at hx
    · split at hx
      · exact uncreditFx_no_header _ x hx
      · simp at hx
    · simp at hx

/-- **C4: the block family's effects**: neither a header, nor the bookkeeping, nor a completion effect.
Every effect `arm` returns is one (`arm_ofBlock`), so the completion family's state is `completionArm`'s
alone. -/
def Effect.ofBlock : Effect → Bool
  | .header _ _ => false
  | .global _ => false
  | .markDone _ _ => false
  | .doneDate _ _ => false
  | .inst _ _ _ => false
  | .named _ _ _ _ _ => false
  | .rwarn _ => false
  | _ => true

theorem ofBlock_of_plain (x : Effect) (h : x.plain = true) : x.ofBlock = true := by
  cases x <;> simp_all [Effect.plain, Effect.ofBlock]

theorem header_of_ofBlock (x : Effect) (h : x.ofBlock = true) : x.isHeader = false := by
  cases x <;> simp_all [Effect.ofBlock, Effect.isHeader]

/-- **C5: the block family's effects, as a whitelist**: a day's record, an item's, an item-day's, an
observation, an interruption, the machine.  Never a header, the bookkeeping, a completion effect or a day
family record outside a day's (`Effect.isRec`). -/
def Effect.blockOnly : Effect → Bool
  | .dayAdd _ _ => true
  | .itemAdd _ _ => true
  | .itemDay _ _ _ => true
  | .itemDaySub _ _ _ => true
  | .obs _ => true
  | .interruption _ => true
  | .machine _ => true
  | _ => false

theorem blockOnly_of_plain (x : Effect) (h : x.plain = true) : x.blockOnly = true := by
  cases x <;> simp_all [Effect.plain, Effect.blockOnly]

theorem ofBlock_of_blockOnly (x : Effect) (h : x.blockOnly = true) : x.ofBlock = true := by
  cases x <;> simp_all [Effect.blockOnly, Effect.ofBlock]

theorem isRec_of_blockOnly (x : Effect) (h : x.blockOnly = true) : x.isRec = false := by
  cases x <;> simp_all [Effect.blockOnly, Effect.isRec]

theorem uncreditFx_blockOnly (c : Cut) : ∀ x ∈ uncreditFx c, x.blockOnly = true := by
  unfold uncreditFx; split <;> simp [Effect.blockOnly]

theorem uncreditFx_ofBlock (c : Cut) : ∀ x ∈ uncreditFx c, x.ofBlock = true :=
  fun x hx => ofBlock_of_blockOnly x (uncreditFx_blockOnly c x hx)

theorem doneClose_blockOnly (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat)
    (went : Option U8) : ∀ x ∈ (doneClose dy m t id actual went).2, x.blockOnly = true := by
  intro x hx
  unfold doneClose at hx
  split at hx
  · split at hx
    · simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact blockOnly_of_plain x (redraw_plain dy _ _ _ x hx)
      · exact blockOnly_of_plain x (closePause_plain dy _ t x hx)
      · exact blockOnly_of_plain x (obsFx_plain _ x hx)
    · simp at hx
  · split at hx
    · split at hx
      · exact uncreditFx_blockOnly _ x hx
      · simp at hx
    · simp at hx

theorem doneClose_ofBlock (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat)
    (went : Option U8) : ∀ x ∈ (doneClose dy m t id actual went).2, x.ofBlock = true :=
  fun x hx => ofBlock_of_blockOnly x (doneClose_blockOnly dy m t id actual went x hx)

theorem netOne_mem (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (C : Closed) (x : Effect)
    (hx : x ∈ (netOne dy s e dd C).2.1) :
    x ∈ (redraw dy C.id C.drawn (cutOut s e C.spans)).2 ∨
      x = .dayAdd C.credDay (.net C.id C.ci (netMin s e C) C.durLine) ∨
      x = .itemAdd C.id (.uncredit (netMin s e C)) ∨ x = .itemDaySub C.id C.credDay (netMin s e C) := by
  unfold netOne at hx
  split at hx
  · simp at hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl hx
    · split at hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      · simp at hx

theorem netClosed_mem (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) (x : Effect)
    (hx : x ∈ (netClosed dy s e dd m).2) : ∃ C, x ∈ (netOne dy s e dd C).2.1 := by
  unfold netClosed at hx
  simp only [List.mem_flatten, List.mem_map] at hx
  obtain ⟨l, ⟨C, -, rfl⟩, hx⟩ := hx
  exact ⟨C, hx⟩

/-- **A late break's netting is the block family's** (the owner's D100). -/
theorem netClosed_blockOnly (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) :
    ∀ x ∈ (netClosed dy s e dd m).2, x.blockOnly = true := by
  intro x hx
  obtain ⟨C, hC⟩ := netClosed_mem dy s e dd m x hx
  rcases netOne_mem dy s e dd C x hC with h | rfl | rfl | rfl
  · exact blockOnly_of_plain x (redraw_plain dy _ _ _ x h)
  · rfl
  · rfl
  · rfl

/-- **The running break's netting is a late break's, or nothing** (README gap 5180) — **restated at the owner's D137**
(README gaps 5504 and 5302, W-51 track K): its effects are a late break's netting over the running span, and its machine
that netting's with each held closed block remembering what the running break took (`runOne`, `Closed.ran`); every
field of a held block but `ran` and `ranMin` is the netting's (`runOne_netOne`). -/
theorem runNet_cases (dy : Cal.Instant → Nat) (m : Machine) :
    runNet dy m = (m, []) ∨ ∃ o, m.brkOpen = some o ∧
      runNet dy m = ({ (netClosed dy o.s (runTo o.s m.closed) o.day m).1 with
          closed := m.closed.map (runOne dy o.s (runTo o.s m.closed) o.day) },
        (netClosed dy o.s (runTo o.s m.closed) o.day m).2) := by
  unfold runNet
  split
  · rename_i o h
    split
    · exact Or.inr ⟨o, h, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **`runOne` is `netOne`'s block with what the running break took remembered** (D137): every field but `ran` and
`ranMin` is the netting's. -/
theorem runOne_netOne (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Closed) :
    runOne dy s e d C = { (netOne dy s e d C).1 with
      ran := if d < C.day then C.ran else C.ran ++ C.drawn.filter (meets s e),
      ranMin := C.ranMin + (netOne dy s e d C).2.2 } := rfl

/-- **`netOne` leaves what a running break took alone** (D137). -/
theorem netOne_ran (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Closed) :
    (netOne dy s e d C).1.ran = C.ran ∧ (netOne dy s e d C).1.ranMin = C.ranMin := by
  unfold netOne; split <;> exact ⟨rfl, rfl⟩

theorem runNet_mem (dy : Cal.Instant → Nat) (m : Machine) (x : Effect) (hx : x ∈ (runNet dy m).2) :
    ∃ s e dd, x ∈ (netClosed dy s e dd m).2 := by
  rcases runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h] at hx; cases hx
  · rw [h] at hx; exact ⟨_, _, _, hx⟩

/-- **The running break's netting is the block family's** (README gap 5180). -/
theorem runNet_blockOnly (dy : Cal.Instant → Nat) (m : Machine) : ∀ x ∈ (runNet dy m).2, x.blockOnly = true := by
  intro x hx
  obtain ⟨s, e, dd, h⟩ := runNet_mem dy m x hx
  exact netClosed_blockOnly dy s e dd m x h

theorem giveOne_mem (dy : Cal.Instant → Nat) (C : Closed) (x : Effect) (hx : x ∈ (giveOne dy C).2.1) :
    x ∈ (redraw dy C.id C.drawn C.restored).2 ∨ x = .dayAdd C.credDay (.credit C.id C.ranMin C.ci) ∨
      x = .dayAdd C.credDay (.undur C.durLine C.ranMin) ∨ x = .itemAdd C.id (.credit C.ranMin) ∨
      x = .itemDay C.id C.credDay C.ranMin := by
  unfold giveOne at hx
  split at hx
  · simp at hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact Or.inl hx
    · split at hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · simp at hx

theorem giveBack_mem (dy : Cal.Instant → Nat) (m : Machine) (x : Effect) (hx : x ∈ (giveBack dy m).2) :
    ∃ C, x ∈ (giveOne dy C).2.1 := by
  unfold giveBack at hx
  simp only [List.mem_flatten, List.mem_map] at hx
  obtain ⟨l, ⟨C, -, rfl⟩, hx⟩ := hx
  exact ⟨C, hx⟩

/-- **A give-back writes only plain effects** (D137): re-drawn pieces and credits — never a machine, an uncredit or a
net. -/
theorem giveBack_plain (dy : Cal.Instant → Nat) (m : Machine) : ∀ x ∈ (giveBack dy m).2, x.plain = true := by
  intro x hx
  obtain ⟨C, hC⟩ := giveBack_mem dy m x hx
  rcases giveOne_mem dy C x hC with h | rfl | rfl | rfl | rfl
  · exact redraw_plain dy _ _ _ x h
  all_goals rfl

/-- **A give-back moves only the held closed blocks and the last cut's minutes** (D137), as a netting does
(`netClosed_keeps`). -/
theorem giveBack_keeps (dy : Cal.Instant → Nat) (m : Machine) :
    (giveBack dy m).1.block = m.block ∧ (giveBack dy m).1.interrupt = m.interrupt ∧
      (giveBack dy m).1.brks = m.brks ∧ (giveBack dy m).1.brkOpen = m.brkOpen ∧
      (giveBack dy m).1.brkEnded = m.brkEnded ∧
      (giveBack dy m).1.lastCut.map (fun c => (c.id, c.t, c.day)) = m.lastCut.map (fun c => (c.id, c.t, c.day)) := by
  unfold giveBack
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only
  split <;> simp_all

theorem giveOne_keeps (dy : Cal.Instant → Nat) (C : Closed) :
    (giveOne dy C).1.id = C.id ∧ (giveOne dy C).1.credDay = C.credDay ∧ (giveOne dy C).1.ci = C.ci ∧
      (giveOne dy C).1.min = C.min + (giveOne dy C).2.2 ∧ (giveOne dy C).1.day = C.day := by
  unfold giveOne; split
  · simp
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem noMachine_of_plain (x : Effect) (h : x.plain = true) : x.machineOf? = none := by
  cases x <;> simp_all [Effect.plain, Effect.machineOf?]

/-- **A `done`'s closing effects write no machine** (README gap 5180). -/
theorem doneClose_noMachine (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat)
    (went : Option U8) : ∀ x ∈ (doneClose dy m t id actual went).2, x.machineOf? = none := by
  intro x hx
  unfold doneClose at hx
  split at hx
  · split at hx
    · simp only [List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact noMachine_of_plain x (redraw_plain dy _ _ _ x hx)
      · exact noMachine_of_plain x (closePause_plain dy _ t x hx)
      · exact noMachine_of_plain x (obsFx_plain _ x hx)
    · simp at hx
  · split at hx
    · split at hx
      · revert hx; unfold uncreditFx; split
        · simp
        · intro hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> rfl
      · simp at hx
    · simp at hx

/-- **The running break's netting writes no machine** (README gap 5180). -/
theorem runNet_noMachine (dy : Cal.Instant → Nat) (m : Machine) : ∀ x ∈ (runNet dy m).2, x.machineOf? = none := by
  intro x hx
  obtain ⟨s, e, dd, h⟩ := runNet_mem dy m x hx
  obtain ⟨C, hC⟩ := netClosed_mem dy s e dd m x h
  rcases netOne_mem dy s e dd C x hC with h | rfl | rfl | rfl
  · exact noMachine_of_plain x (redraw_plain dy _ _ _ x h)
  · rfl
  · rfl
  · rfl

theorem doneFx_blockOnly (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id)
    (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool) :
    ∀ x ∈ doneFx dy m line t d id est actual went tags ci isPartial, x.blockOnly = true := by
  intro x hx
  unfold doneFx at hx
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | ((((hx | hx) | hx) | hx) | hx)
  · rfl
  · exact doneClose_blockOnly dy m t id actual went x hx
  · exact blockOnly_of_plain x (creditFx_plain dy id t actual (some ci) x hx)
  · split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> rfl
    · simp at hx
  · split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
  · exact runNet_blockOnly dy _ x hx

theorem doneFx_ofBlock (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id)
    (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool) :
    ∀ x ∈ doneFx dy m line t d id est actual went tags ci isPartial, x.ofBlock = true :=
  fun x hx => ofBlock_of_blockOnly x (doneFx_blockOnly dy m line t d id est actual went tags ci isPartial x hx)

/-- **C5: the day family's effects are never a completion effect, a header or the bookkeeping.** -/
theorem dayArm_ofBlock (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat) :
    (dayArm dy sl e t d).all Effect.ofBlock = true := by
  unfold dayArm
  split <;> (repeat' split) <;> simp [Effect.ofBlock]

/-- **What netting one held closed block writes** (the owner's D100): each effect re-draws one of its pieces, or takes
its credit down — on the day it was filed (`DayOp.net`), from its item, and from its item's minutes on that day. -/
theorem doneFx_no_header (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id)
    (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool) :
    ∀ x ∈ doneFx dy m line t d id est actual went tags ci isPartial, x.isHeader = false :=
  fun x hx => header_of_ofBlock x (ofBlock_of_blockOnly x (doneFx_blockOnly dy m line t d id est actual went tags ci
    isPartial x hx))

theorem netStart_mem (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (m : Machine) (x : Effect)
    (hx : x ∈ (netStart dy t dd m).2) : ∃ C, x ∈ (netOne dy t (startEnd t C) dd C).2.1 := by
  unfold netStart at hx
  simp only [List.mem_flatten, List.mem_map] at hx
  obtain ⟨l, ⟨C, -, rfl⟩, hx⟩ := hx
  exact ⟨C, hx⟩

/-- **A late start's cut of the closed blocks is the block family's** (the owner's D115). -/
theorem netStart_blockOnly (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (m : Machine) :
    ∀ x ∈ (netStart dy t dd m).2, x.blockOnly = true := by
  intro x hx
  obtain ⟨C, hC⟩ := netStart_mem dy t dd m x hx
  rcases netOne_mem dy t _ dd C x hC with h | rfl | rfl | rfl
  · exact blockOnly_of_plain x (redraw_plain dy _ _ _ x h)
  · rfl
  · rfl
  · rfl

/-- A `break`'s block family half is block family effects (D87): `settle`'s and one machine. -/
theorem brkFx_blockOnly (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) :
    ∀ x ∈ brkFx dy m t e d, x.blockOnly = true := by
  intro x hx
  unfold brkFx at hx
  rcases List.mem_append.1 hx with hx | hx
  · rcases List.mem_append.1 hx with hx | hx
    · exact blockOnly_of_plain x (settle_plain dy _ x hx)
    · exact netClosed_blockOnly dy _ _ _ _ x hx
  · simp only [List.mem_singleton] at hx; subst hx; rfl

/-- **Ending a running break is block family effects** (D129): `brkFx`'s, and the break's segment and record on its day. -/
theorem endBrkFx_blockOnly (dy : Cal.Instant → Nat) (m : Machine) (o : OpenBrk) (t : At) :
    ∀ x ∈ endBrkFx dy m o t, x.blockOnly = true := by
  intro x hx
  unfold endBrkFx endRecs at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact brkFx_blockOnly dy _ _ _ _ x hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> rfl

/-- **A break ended at a start writes block family effects** (D129): a segment and a record. -/
theorem endRecs_blockOnly (o : OpenBrk) (t : At) : ∀ x ∈ endRecs o t, x.blockOnly = true := by
  intro x hx
  unfold endRecs at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

/-- **A start's arm is block family effects** (C3). -/
theorem startArm_blockOnly (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id) (pred : U8)
    (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) :
    ∀ x ∈ startArm dy m line t d id pred rep hsw sleptMin loc, x.blockOnly = true := by
  unfold startArm
  simp only [List.forall_mem_append, List.forall_mem_singleton]
  exact ⟨⟨⟨⟨⟨netStart_blockOnly dy _ _ _, fun x hx => blockOnly_of_plain x (cut_plain dy _ t x hx)⟩,
    runNet_blockOnly dy _⟩, rfl⟩, fun x hx => blockOnly_of_plain x (settle_plain dy _ x hx)⟩, rfl⟩

/-- **A `break_start`'s arm, as D105 has it, is block family effects.** -/
theorem brkStartArm_blockOnly (dy : Cal.Instant → Nat) (m : Machine) (t : At) (d : Nat) (planned : Nat)
    (where_ : Option (List Char)) : ∀ x ∈ brkStartArm dy m t d planned where_, x.blockOnly = true := by
  intro x hx
  unfold brkStartArm at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (hx | hx) | rfl
  · exact blockOnly_of_plain x (settle_plain dy _ x hx)
  · exact runNet_blockOnly dy _ x hx
  · rfl

/-- **C5's split, on every event but a `break`**: an entry's machine arm is its day family's, or else only block
family effects with no day family arm.  `arm` is one match: the block family's eight events have their own arms (and
`dayArm` gives them nothing), and every other event's but a `break`'s is `dayArm`'s.  This was `arm_split`'s
statement over EVERY event until the owner's D87 (README gap 4137, parity P81) gave a `break` a block family half
(`brkFx`) beside its day family records; over every event it is refuted
(`arm_split_as_c5_stated_it_is_refuted`), and `arm_split` is the form that holds. -/
theorem arm_split_of_not_brk (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At)
    (d : Nat) (hb : ∀ p a w, e.ev ≠ .brk p a w) :
    arm dy sl m e t d = dayArm dy sl e t d ∨
      ((∀ x ∈ arm dy sl m e t d, x.blockOnly = true) ∧ dayArm dy sl e t d = []) := by
  unfold arm
  cases hev : e.ev <;> simp only
  case brk p a w => exact absurd hev (hb p a w)
  case start =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    split at hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact endRecs_blockOnly _ t x hx
      · exact startArm_blockOnly dy _ _ t d _ _ _ _ _ _ x hx
    · exact startArm_blockOnly dy _ _ t d _ _ _ _ _ _ x hx
  case pause =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    split at hx
    · split at hx
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | rfl
        · exact blockOnly_of_plain x (settle_plain dy _ x hx)
        · rfl
      · simp at hx
    · simp at hx
  case unpause =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    split at hx
    · split at hx
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with (hx | hx) | rfl
        · exact blockOnly_of_plain x (closePause_plain dy m t x hx)
        · exact blockOnly_of_plain x (settle_plain dy _ x hx)
        · rfl
      · simp at hx
    · simp at hx
  case interrupt =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (hx | hx) | rfl
    · exact blockOnly_of_plain x (closePause_plain dy m t x hx)
    · exact blockOnly_of_plain x (settle_plain dy _ x hx)
    · rfl
  case resume =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    split at hx
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (((rfl | rfl | rfl) | hx) | hx) | rfl
      · rfl
      · rfl
      · rfl
      · exact blockOnly_of_plain x (settle_plain dy _ x hx)
      · exact netClosed_blockOnly dy _ _ _ _ x hx
      · rfl
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | rfl) | hx) | rfl
      · rfl
      · rfl
      · exact blockOnly_of_plain x (settle_plain dy _ x hx)
      · rfl
  case stop =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    split at hx
    · split at hx
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with (hx | hx) | rfl | rfl
        · exact blockOnly_of_plain x (cut_plain dy m t x hx)
        · exact runNet_blockOnly dy _ x hx
        · rfl
        · rfl
      · simp at hx
    · simp at hx
  case extend =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · unfold extendFx at hx
      split at hx
      · split at hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; subst hx; rfl
        · simp at hx
      · simp at hx
  case brkStart =>
    refine Or.inr ⟨fun x hx => ?_, by simp [dayArm, hev]⟩
    split at hx
    · exact endBrkFx_blockOnly dy m _ _ x hx
    · exact brkStartArm_blockOnly dy m t d _ _ x hx
  case done =>
    exact Or.inr ⟨fun x hx => doneFx_blockOnly dy m _ t d _ _ _ _ _ _ _ x hx, by simp [dayArm, hev]⟩
  all_goals first | exact Or.inl rfl | exact Or.inl trivial

theorem mem_pruneClosed {l : List Closed} {C : Closed} (h : C ∈ pruneClosed l) : C ∈ l := by
  cases l with
  | nil => simp [pruneClosed] at h
  | cons c l =>
    unfold pruneClosed at h
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_filter.1 h).1

/-- **A re-drawn piece begins where one of the spans it was drawn for begins** (the owner's D99). -/
theorem redraw_fst_starts (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) (p : Piece)
    (hp : p ∈ (redraw dy id old P).1) : ∃ q ∈ P, p.s = q.1 := by
  unfold redraw at hp
  obtain ⟨q, hq, hpq⟩ := List.mem_map.1 hp
  refine ⟨q, hq, ?_⟩
  split at hpq
  · rename_i p' hf
    have h1 := List.find?_some hf
    subst hpq
    simp only [samePiece, Bool.and_eq_true] at h1
    exact (atEq_iff _ _).1 h1.1
  · subst hpq; rfl

/-- **A late break's netting moves only the closed blocks and the last cut's minutes** (the owner's D100): the open block,
the interruption, the breaks held and the running break are the machine's, and the last cut keeps its block, its stamp
and its day. -/
theorem netClosed_keeps (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) :
    (netClosed dy s e dd m).1.block = m.block ∧ (netClosed dy s e dd m).1.interrupt = m.interrupt ∧
      (netClosed dy s e dd m).1.brks = m.brks ∧ (netClosed dy s e dd m).1.brkOpen = m.brkOpen ∧
      (netClosed dy s e dd m).1.lastCut.map (fun c => (c.id, c.t, c.day)) = m.lastCut.map (fun c => (c.id, c.t, c.day)) := by
  unfold netClosed
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only
  split <;> simp_all

/-- **A late start's cut moves only the closed blocks and the last cut's minutes** (the owner's D115), as a late break's
netting does (`netClosed_keeps`). -/
theorem netStart_keeps (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (m : Machine) :
    (netStart dy t dd m).1.block = m.block ∧ (netStart dy t dd m).1.interrupt = m.interrupt ∧
      (netStart dy t dd m).1.brks = m.brks ∧ (netStart dy t dd m).1.brkOpen = m.brkOpen ∧
      (netStart dy t dd m).1.lastCut.map (fun c => (c.id, c.t, c.day)) = m.lastCut.map (fun c => (c.id, c.t, c.day)) := by
  unfold netStart
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  simp only
  split <;> simp_all

/-- **The running break's netting moves only the closed blocks and the last cut's minutes** (README gap 5180). -/
theorem runNet_keeps (dy : Cal.Instant → Nat) (m : Machine) :
    (runNet dy m).1.block = m.block ∧ (runNet dy m).1.interrupt = m.interrupt ∧
      (runNet dy m).1.brks = m.brks ∧ (runNet dy m).1.brkOpen = m.brkOpen ∧
      (runNet dy m).1.lastCut.map (fun c => (c.id, c.t, c.day)) = m.lastCut.map (fun c => (c.id, c.t, c.day)) := by
  rcases runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [h]; exact netClosed_keeps dy _ _ _ m

/-- **C5: an entry's machine arm is block family effects, then its day family's** — the block family's eight
events have no day family arm, every other event's is its day family's alone, and (the owner's D87, README gap
4137, parity P81) a `break`'s is both: `brkFx`, which stops the open block's clock across it, then its own
segment and record.  Restated at D87 from C5's two cases (`arm_split_of_not_brk`), which it implies on every
event but a `break`.  **Restated at the owner's D116** (stage 6 W-48 track K, README gap 5035): a `break` line's day
family is read at its `break_start`'s place (`placed`), so the day family half is `dayArm` of `placed m e` — which is `e`
itself on every event but a `break` (`placed_of_not_brk`), where the statement as D87 wrote it holds unchanged; on a
`break` line whose word is not its start's it is refuted (`arm_split_as_d87_stated_it_is_refuted`). -/
theorem arm_split (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∃ fx : List Effect, (∀ x ∈ fx, x.blockOnly = true) ∧
      (arm dy sl m e t d = fx ++ dayArm dy sl (placed m e) t d ∨
        ((∃ p a w, e.ev = .brk p a w) ∧ arm dy sl m e t d = fx)) := by
  by_cases hb : ∃ p a w, e.ev = .brk p a w
  · obtain ⟨p, a, w, h⟩ := hb
    have hbf : ∀ x ∈ (giveBack dy m).2 ++ brkFx dy (giveBack dy m).1 t (brkEnd t p.val (a.map (·.val))) d,
        x.blockOnly = true := fun x hx => by
      rcases List.mem_append.1 hx with hx | hx
      · exact blockOnly_of_plain x (giveBack_plain dy m x hx)
      · exact brkFx_blockOnly dy _ t _ d x hx
    unfold arm
    simp only [h]
    rcases hE : m.brkEnded with _ | s
    · exact ⟨_, hbf, Or.inl rfl⟩
    · by_cases hs : atEq s t = true
      · refine ⟨[.machine { m with brkEnded := none }], ?_, Or.inr ⟨⟨p, a, w, rfl⟩, by simp [hs]⟩⟩
        intro x hx; simp only [List.mem_singleton] at hx; subst hx; rfl
      · exact ⟨_, hbf, Or.inl (if_neg hs)⟩
  · rw [placed_of_not_brk m e (fun p a w h => hb ⟨p, a, w, h⟩)]
    rcases arm_split_of_not_brk dy sl m e t d (fun p a w h => hb ⟨p, a, w, h⟩) with h | ⟨h, h0⟩
    · exact ⟨[], by simp, Or.inl (by rw [h, List.nil_append])⟩
    · exact ⟨_, h, Or.inl (by rw [h0, List.append_nil])⟩

/-- **D116 moves a `break`'s day family by its place alone**: projected onto the effects that are records outside a day,
`dayArm` of `placed m e` is `dayArm` of `e`. -/
theorem dayArm_placed_rec {α : Type} (ρ : Effect → Option α) (hρ : ∀ x, x.isRec = false → ρ x = none)
    (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    (dayArm dy sl (placed m e) t d).filterMap ρ = (dayArm dy sl e t d).filterMap ρ := by
  have h1 : ∀ d' op, ρ (.dayAdd d' op) = none := fun d' op => hρ _ rfl
  unfold placed
  split
  · rename_i p a w h
    simp only [dayArm, h, List.filterMap_cons, List.filterMap_nil, h1]
  · rfl

theorem arm_ofBlock (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ arm dy sl m e t d, x.ofBlock = true := by
  intro x hx
  obtain ⟨fx, hfx, h | ⟨-, h⟩⟩ := arm_split dy sl m e t d
  · rw [h] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ofBlock_of_blockOnly x (hfx x hx)
    · exact List.all_eq_true.1 (dayArm_ofBlock dy sl _ t d) x hx
  · rw [h] at hx; exact ofBlock_of_blockOnly x (hfx x hx)

/-- **C5: an entry's machine arm, projected onto the day family's records, is its day family arm's.** -/
theorem arm_filterMap_rec {α : Type} (ρ : Effect → Option α) (hρ : ∀ x, x.isRec = false → ρ x = none)
    (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    (arm dy sl m e t d).filterMap ρ = (dayArm dy sl e t d).filterMap ρ := by
  obtain ⟨fx, hfx, h | ⟨⟨p, a, w, hb⟩, h⟩⟩ := arm_split dy sl m e t d
  · rw [h, List.filterMap_append,
      List.filterMap_eq_nil_iff.2 (fun x hx => hρ x (isRec_of_blockOnly x (hfx x hx))), List.nil_append,
      dayArm_placed_rec ρ hρ]
  · have h1 : ∀ d' op, ρ (.dayAdd d' op) = none := fun d' op => hρ _ rfl
    rw [h, List.filterMap_eq_nil_iff.2 (fun x hx => hρ x (isRec_of_blockOnly x (hfx x hx)))]
    simp only [dayArm, hb, List.filterMap_cons, List.filterMap_nil, h1]

theorem arm_no_header (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ arm dy sl m e t d, x.isHeader = false :=
  fun x hx => header_of_ofBlock x (arm_ofBlock dy sl m e t d x hx)

/-- **C4: the completion family's effects are never headers.** -/
theorem completionCore_no_header (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ completionCore z e t d, x.isHeader = false := by
  intro x hx
  unfold completionCore at hx
  cases hev : e.ev <;> simp only [hev] at hx
  case done =>
    split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  case routine =>
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; rfl
    · subst hx; rfl
    · split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
  case skip =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; rfl
  case named =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; rfl
  all_goals simp at hx

theorem completionArm_no_header (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ completionArm z m e t d, x.isHeader = false := by
  intro x hx
  unfold completionArm at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x hx; rfl
  · exact completionCore_no_header z e t d x hx

/-- **Every entry, whatever its kind, produces exactly one header effect** (Goals; CRIT 21).  `arm` is
one match over `Event`'s 27 constructors, so every known event has an arm by exhaustiveness; this is the
law the header pass relies on. -/
theorem every_known_event_has_an_arm (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat))
    (st : State) (e : Entry) :
    ((effects z kw slept st e).filter Effect.isHeader).length = 1 := by
  unfold effects effectsWith
  rw [List.filter_cons, List.filter_cons, List.filter_cons]
  simp only [Effect.isHeader, if_true, Bool.false_eq_true, if_false, List.length_cons]
  rw [List.filter_eq_nil_iff.2 (fun x hx => by
    rcases List.mem_append.1 hx with hx | hx
    · simp [arm_no_header _ _ _ _ _ _ x hx]
    · simp [completionArm_no_header _ _ _ _ _ x hx])]
  rfl

end MachineLaws

/-- The replay as a fold of `stepWith` over the survivors (its definition, by `rfl`). -/
theorem replay_state (z : Cal.Tz) (es : List Entry) :
    replay z es = finish ((survivors es).foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es))
      (State.init es.length)) :=
  rfl

/-! ### Credit conserves the day's minutes -/

section Conservation

open Log (Id U8 U32 Num)

theorem Ci6.sum_add (c : Ci6) (i m : Nat) : (c.add i m).sum = c.sum + m := by
  unfold Ci6.add Ci6.sum
  split <;> simp <;> omega

/-- A day's minutes balance: its ci minutes and its ci-unknown minutes add up to its block minutes, and
its ci-unknown map has one pair per id. -/
def DayAcc.Bal (a : DayAcc) : Prop :=
  a.byCi.sum + KMap.vsum a.ciUnknown = a.blockMin ∧ (a.ciUnknown.map Prod.fst).Nodup

/-- The ci-unknown minutes of `i` on day `d`. -/
def unk (st : State) (d : Nat) (i : Id) : Nat :=
  match st.days.get d with
  | some a => (a.ciUnknown.get i).getD 0
  | none => 0

def Balanced (st : State) : Prop := ∀ d a, st.days.get d = some a → a.Bal

/-! **The ci-unknown minutes the held closed blocks of item `i` still stand for on day `d`** (the owner's D100, README
gap 4520b) — the credits of the cuts among them (`Closed.ci = none`) filed on `d` — are written in place below, as the
sum `((l.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum`: as a definition the sum
was emitted code no request reaches (check 12, W-47 track K). -/

/-- **The last cut is the first closed block held** (D100): while a cut stands, the first held is its block, its credit
the cut's. -/
def HeadOk (m : Machine) : Prop :=
  ∀ c, m.lastCut = some c → ∃ C rest, m.closed = C :: rest ∧ C.id = c.id ∧ C.credDay = c.day ∧ C.ci = none ∧ C.min = c.min

/-- **The machine's invariant**: every day balances; the cuts' credits the held closed blocks still stand for are on
their days' ci-unknown minutes (the sum, in place); and the last cut is the first held (`HeadOk`) — so the stop-then-done
replacement takes back exactly what the cut gave (`lastCut_le_unk`), and a break logged after a block closed takes back
no more than the block still stands for (the owner's D100, `netClosed`).  Until W-47 track K the second half read "the
last cut's minutes are still on its day's ci-unknown minutes", which `lastCut_le_unk` derives from these. -/
def Conserves (st : State) : Prop :=
  Balanced st ∧ (∀ d i, ((st.machine.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk st d i) ∧ HeadOk st.machine

theorem heldOf_cons (C : Closed) (l : List Closed) (d : Nat) (i : Id) :
    (((C :: l).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum = (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min else 0) + ((l.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum := by
  skip
  by_cases h : C.ci = none ∧ C.credDay = d ∧ C.id = i
  · simp only [List.filter_cons, decide_eq_true h, if_true, List.map_cons, List.sum_cons, if_pos h]
  · simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, if_false, Nat.zero_add]

theorem heldOf_filter_le (p : Closed → Bool) : ∀ (l : List Closed) (d : Nat) (i : Id),
    (((l.filter p).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ ((l.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum
  | [], _, _ => Nat.le_refl _
  | C :: l, d, i => by
    rw [List.filter_cons]
    have ih := heldOf_filter_le p l d i
    split
    · rw [heldOf_cons, heldOf_cons]; omega
    · rw [heldOf_cons]; omega

/-- **Pruning never raises a held credit** and never drops the last closed (D100's bound). -/
theorem pruneClosed_held (l : List Closed) (d : Nat) (i : Id) : (((pruneClosed l).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ ((l.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum := by
  cases l with
  | nil => exact Nat.le_refl _
  | cons C l =>
    unfold pruneClosed
    rw [heldOf_cons, heldOf_cons]
    have := heldOf_filter_le (fun k => decide (l.foldl (fun a k => max a k.day) C.day ≤ k.day + 31)) l d i
    omega

theorem pruneClosed_cons (C : Closed) (l : List Closed) : ∃ rest, pruneClosed (C :: l) = C :: rest :=
  ⟨_, rfl⟩

/-- **The last cut's minutes are still on its day** (the stop-then-done replacement's precondition), from the invariant. -/
theorem lastCut_le_unk (st : State) (h : Conserves st) (c : Cut) (hc : st.machine.lastCut = some c) :
    c.min ≤ unk st c.day c.id := by
  obtain ⟨C, rest, hcl, hid, hday, hci, hmin⟩ := h.2.2 c hc
  have := h.2.1 c.day c.id
  rw [hcl, heldOf_cons, if_pos ⟨hci, hday, hid⟩] at this
  omega

/-- Effects that leave every balance and the machine alone, and never lower a ci-unknown minute. -/
def Effect.safe : Effect → Bool
  | .machine _ => false
  | .dayAdd _ (.uncredit _ _) => false
  | .dayAdd _ (.net _ _ _ _) => false
  | _ => true

theorem noMachine_of_safe (x : Effect) (h : x.safe = true) : x.machineOf? = none := by
  cases x <;> simp_all [Effect.safe, Effect.machineOf?]

theorem safe_of_plain (x : Effect) (h : x.plain = true) : x.safe = true := by
  cases x with
  | dayAdd d op => cases op <;> simp_all [Effect.plain, Effect.safe]
  | _ => simp_all [Effect.plain, Effect.safe]

theorem DayAcc.bal_empty : DayAcc.empty.Bal := by
  simp [DayAcc.Bal, DayAcc.empty, Ci6.zero, Ci6.sum, KMap.vsum]

theorem DayOp.bal_apply (op : DayOp) (hop : ∀ i m, op ≠ .uncredit i m) (hnet : ∀ i c k l, op ≠ .net i c k l)
    (a : DayAcc) (ha : a.Bal) :
    (op.apply a).Bal ∧ ∀ i, (a.ciUnknown.get i).getD 0 ≤ ((op.apply a).ciUnknown.get i).getD 0 := by
  obtain ⟨hs, hn⟩ := ha
  cases op with
  | start r => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | credit id min ci =>
    cases ci with
    | some c =>
      refine ⟨⟨?_, hn⟩, fun _ => Nat.le_refl _⟩
      simp only [DayOp.apply, Ci6.sum_add]; omega
    | none =>
      simp only [DayOp.apply]
      split
      · obtain ⟨hn', hsum⟩ := KMap.vsum_alter a.ciUnknown id (fun o => some (o.getD 0 + min)) hn
        refine ⟨⟨?_, hn'⟩, fun i => ?_⟩
        · simp only [Option.getD_some] at hsum ⊢; omega
        · rw [KMap.get_alter]
          split
          · rename_i hi; subst hi; simp
          · exact Nat.le_refl _
      · exact ⟨⟨by simp only; omega, hn⟩, fun _ => Nat.le_refl _⟩
  | uncredit i m => exact absurd rfl (hop i m)
  | net i c k l => exact absurd rfl (hnet i c k l)
  | undur l k =>
    simp only [DayOp.apply]; unfold DayAcc.undurOf
    split <;> exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | blockDone => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | done id => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | segment s => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | unsegment s => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | lost min dropped => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | wake t sl on => simp only [DayOp.apply]; split <;> exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | arrive t lc w bu => simp only [DayOp.apply]; split <;> exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | loc t lc => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | brk r => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | idle r => simp only [DayOp.apply]; split <;> exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | routineMin m => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩
  | plan h r dr => exact ⟨⟨hs, hn⟩, fun _ => Nat.le_refl _⟩

/-- **An uncredit keeps the balance** when the day holds at least the minutes taken back. -/
theorem DayAcc.bal_uncredit (a : DayAcc) (i : Id) (m : Nat) (ha : a.Bal)
    (hm : m ≤ (a.ciUnknown.get i).getD 0) : ((DayOp.uncredit i m).apply a).Bal := by
  obtain ⟨hs, hn⟩ := ha
  let f : Option Nat → Option Nat := fun o =>
    match o with
    | some v => if v - m = 0 then none else some (v - m)
    | none => none
  obtain ⟨hn', hsum⟩ := KMap.vsum_alter a.ciUnknown i f hn
  have hle := KMap.get_le_vsum a.ciUnknown i
  have hf : (f (a.ciUnknown.get i)).getD 0 = (a.ciUnknown.get i).getD 0 - m := by
    cases hg : a.ciUnknown.get i with
    | none => simp [f]
    | some v =>
      show (if v - m = 0 then none else some (v - m)).getD 0 = v - m
      split <;> simp_all
  refine ⟨?_, hn'⟩
  simp only [DayOp.apply]
  show a.byCi.sum + KMap.vsum (a.ciUnknown.alter i f) = a.blockMin - m
  omega

theorem Ci6.get_le_sum (c : Ci6) (i : Nat) : c.get i ≤ c.sum := by
  unfold Ci6.get Ci6.sum
  split <;> omega

theorem Ci6.sum_sub (c : Ci6) (i m : Nat) (h : m ≤ c.get i) : (c.sub i m).sum + m = c.sum := by
  unfold Ci6.get at h
  unfold Ci6.sub Ci6.sum
  split <;> (simp only at h ⊢) <;> omega

/-- **D100's net keeps a day's balance**, whatever it is asked to take: its credit half takes no more than the credit's
own bucket holds, from that bucket and the block minutes alike, and its duration half touches neither. -/
theorem DayAcc.bal_net (a : DayAcc) (id : Id) (ci : Option U8) (k : Nat) (line : Option Nat) (ha : a.Bal) :
    ((DayOp.net id ci k line).apply a).Bal := by
  have hd : ∀ b : DayAcc, b.Bal → (DayAcc.netDurOf line k b).Bal := by
    intro b hb; unfold DayAcc.netDurOf; split
    · exact hb
    · exact hb
  apply hd
  obtain ⟨hs, hn⟩ := ha
  unfold DayAcc.netCredit
  cases ci with
  | some c =>
    refine ⟨?_, hn⟩
    have hget := Ci6.get_le_sum a.byCi (Nat.min c.val 5)
    have hsub := Ci6.sum_sub a.byCi (Nat.min c.val 5) (min k (a.byCi.get (Nat.min c.val 5)))
      (Nat.min_le_right _ _)
    have hm := Nat.min_le_right k (a.byCi.get (Nat.min c.val 5))
    show (a.byCi.sub (Nat.min c.val 5) (min k (a.byCi.get (Nat.min c.val 5)))).sum + KMap.vsum a.ciUnknown =
      a.blockMin - min k (a.byCi.get (Nat.min c.val 5))
    omega
  | none =>
    let f : Option Nat → Option Nat := fun o =>
      match o with
      | some v => if v - min k v = 0 then none else some (v - min k v)
      | none => none
    obtain ⟨hn', hsum⟩ := KMap.vsum_alter a.ciUnknown id f hn
    have hle := KMap.get_le_vsum a.ciUnknown id
    have hf : (f (a.ciUnknown.get id)).getD 0 =
        (a.ciUnknown.get id).getD 0 - min k ((a.ciUnknown.get id).getD 0) := by
      cases hg : a.ciUnknown.get id with
      | none => simp [f]
      | some v =>
        show (if v - min k v = 0 then none else some (v - min k v)).getD 0 = v - min k v
        split <;> simp_all
    have hm := Nat.min_le_right k ((a.ciUnknown.get id).getD 0)
    refine ⟨?_, hn'⟩
    show a.byCi.sum + KMap.vsum (a.ciUnknown.alter id f) = a.blockMin - min k ((a.ciUnknown.get id).getD 0)
    omega

/-- **What D100's net does to the ci-unknown minutes** (`unk`): for a cut's credit it takes `min k` of what its own day
and item hold there, and nothing anywhere else; for a `done`'s credit, nothing. -/
theorem unk_net (st : State) (d : Nat) (id : Id) (ci : Option U8) (k : Nat) (l : Option Nat) (d' : Nat) (i' : Id) :
    unk (applyEffect st (.dayAdd d (.net id ci k l))) d' i' +
      (if ci = none ∧ d' = d ∧ i' = id then min k (unk st d id) else 0) = unk st d' i' := by
  simp only [unk, applyEffect, HMap.get_alter]
  by_cases hd : d' = d
  · subst hd
    simp only [if_true]
    cases hg : st.days.get d' with
    | none =>
      simp only [DayOp.alterFn]
      split <;> simp
    | some a =>
      simp only [DayOp.alterFn, DayOp.apply, DayAcc.netDurOf]
      cases ci with
      | some c =>
        simp only [DayAcc.netCredit]
        split <;> simp
      | none =>
        simp only [DayAcc.netCredit]
        by_cases hi : i' = id
        · subst hi
          split
          · simp only [KMap.get_alter, if_true]
            cases hv : a.ciUnknown.get i' with
            | none => simp
            | some v =>
              simp only [true_and, if_true]
              split <;> simp_all <;> omega
          · simp only [KMap.get_alter, if_true]
            cases hv : a.ciUnknown.get i' with
            | none => simp
            | some v =>
              simp only [true_and, if_true]
              split <;> simp_all <;> omega
        · split
          · simp [KMap.get_alter, hi]
          · simp [KMap.get_alter, hi]
  · simp [hd]

/-- A ci-unknown credit raises its own day and item by exactly its minutes. -/
theorem unk_credit_none_eq (st : State) (d : Nat) (i : Id) (w : Nat) :
    unk (applyEffect st (.dayAdd d (.credit i w none))) d i = unk st d i + w := by
  simp only [unk, applyEffect, HMap.get_alter, if_true]
  cases st.days.get d with
  | some a =>
    simp only [DayOp.alterFn, DayOp.apply]
    split
    · simp [KMap.get_alter]
    · rename_i hw; simp; omega
  | none =>
    simp only [DayOp.alterFn, DayOp.apply]
    split
    · rw [KMap.get_alter, if_pos rfl]; simp [DayAcc.empty, KMap.get]
    · rename_i hw; simp [DayAcc.empty, KMap.get]; omega

/-- An uncredit of what its day and item hold takes exactly that, and nothing elsewhere. -/
theorem unk_uncredit_eq (st : State) (d : Nat) (i : Id) (m : Nat) (hm : m ≤ unk st d i) (d' : Nat) (i' : Id) :
    unk (applyEffect st (.dayAdd d (.uncredit i m))) d' i' + (if d' = d ∧ i' = i then m else 0) = unk st d' i' := by
  simp only [unk, applyEffect, HMap.get_alter]
  by_cases hd : d' = d
  · subst hd
    simp only [if_true]
    cases hg : st.days.get d' with
    | none =>
      simp only [unk, hg] at hm
      simp only [DayOp.alterFn]
      split <;> simp_all
    | some a =>
      simp only [unk, hg] at hm
      simp only [DayOp.alterFn, DayOp.apply]
      by_cases hi : i' = i
      · subst hi
        have hf : ∀ o : Option Nat, m ≤ o.getD 0 →
            ((match o with
              | some v => if v - m = 0 then none else some (v - m)
              | none => none) : Option Nat).getD 0 + m = o.getD 0 := by
          intro o ho
          cases o with
          | none => simp at ho ⊢; omega
          | some v =>
            simp only [Option.getD_some] at ho ⊢
            split <;> simp_all <;> omega
        simp only [KMap.get_alter, if_true, and_self]
        exact hf _ hm
      · simp [KMap.get_alter, hi]
  · simp [hd]

theorem applyEffects_append (st : State) (fx gx : List Effect) :
    applyEffects st (fx ++ gx) = applyEffects (applyEffects st fx) gx := by
  unfold applyEffects; exact List.foldl_append

theorem applyEffects_cons (st : State) (e : Effect) (fx : List Effect) :
    applyEffects st (e :: fx) = applyEffects (applyEffect st e) fx := rfl

/-- **A safe effect** keeps every balance and the machine, and lowers no ci-unknown minute. -/
theorem safe_apply (st : State) (e : Effect) (hs : e.safe = true) (hb : Balanced st) :
    Balanced (applyEffect st e) ∧ (∀ d i, unk st d i ≤ unk (applyEffect st e) d i) ∧
      (applyEffect st e).machine = st.machine := by
  cases e with
  | dayAdd d op =>
    have hop : ∀ i m, op ≠ .uncredit i m := by
      intro i m h; subst h; simp [Effect.safe] at hs
    have hnet : ∀ i c k l, op ≠ .net i c k l := by
      intro i c k l h; subst h; simp [Effect.safe] at hs
    have hfn : ∀ o, (∀ a, o = some a → a.Bal) →
        (∀ a, op.alterFn o = some a → a.Bal) ∧
        ∀ i, (match o with | some a => (a.ciUnknown.get i).getD 0 | none => 0)
          ≤ (match op.alterFn o with | some a => (a.ciUnknown.get i).getD 0 | none => 0) := by
      intro o ho
      cases o with
      | some a =>
        obtain ⟨h1, h2⟩ := op.bal_apply hop hnet a (ho a rfl)
        exact ⟨fun a' h => by simp only [DayOp.alterFn, Option.some.injEq] at h; subst h; exact h1,
          fun i => h2 i⟩
      | none =>
        by_cases hu : ∃ g, op = .unsegment g
        · obtain ⟨g, rfl⟩ := hu
          exact ⟨fun a' h => by simp [DayOp.alterFn] at h, fun i => Nat.le_refl _⟩
        by_cases hv : ∃ l k, op = .undur l k
        · obtain ⟨l, k, rfl⟩ := hv
          exact ⟨fun a' h => by simp [DayOp.alterFn] at h, fun i => Nat.le_refl _⟩
        · have hne : op.alterFn none = some (op.apply DayAcc.empty) := by
            cases op <;> first | rfl | (exact absurd rfl (hop _ _)) | (exact absurd rfl (hnet _ _ _ _)) | (exact absurd ⟨_, rfl⟩ hu) | (exact absurd ⟨_, _, rfl⟩ hv)
          obtain ⟨h1, _⟩ := op.bal_apply hop hnet _ DayAcc.bal_empty
          refine ⟨fun a' h => by rw [hne] at h; cases h; exact h1, fun i => ?_⟩
          exact Nat.zero_le _
    refine ⟨?_, ?_, rfl⟩
    · intro d' a h
      simp only [applyEffect, HMap.get_alter] at h
      split at h
      · exact (hfn _ (hb d)).1 a h
      · exact hb d' a h
    · intro d' i
      by_cases hd : d' = d
      · subst hd
        have := (hfn _ (hb d')).2 i
        simp only [unk, applyEffect, HMap.get_alter, if_true]
        cases hg : st.days.get d' <;> simp only [hg] at this <;> exact this
      · simp only [unk, applyEffect, HMap.get_alter, if_neg hd]
        exact Nat.le_refl _
  | machine m => simp [Effect.safe] at hs
  | itemDaySub i d m =>
    simp only [applyEffect]
    split
    · exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
    · exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | obs o => cases o <;> exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | header d h => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | itemAdd i op => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | itemDay i d m => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | interruption r => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | global t => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | markDone i t => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | doneDate i d => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | inst item inst r => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | named name id line t date => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | rwarn w => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | demote d r => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | close d r => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | drop i => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | leak r => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | unknown => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | seam d op => exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩

theorem safe_list (fx : List Effect) (hs : ∀ x ∈ fx, x.safe = true) : ∀ (st : State), Balanced st →
    Balanced (applyEffects st fx) ∧ (∀ d i, unk st d i ≤ unk (applyEffects st fx) d i) ∧
      (applyEffects st fx).machine = st.machine := by
  induction fx with
  | nil => intro st hb; exact ⟨hb, fun _ _ => Nat.le_refl _, rfl⟩
  | cons e fx ih =>
    intro st hb
    obtain ⟨h1, h2, h3⟩ := safe_apply st e (hs e (List.mem_cons_self ..)) hb
    obtain ⟨g1, g2, g3⟩ := ih (fun x hx => hs x (List.mem_cons_of_mem _ hx)) _ h1
    rw [applyEffects_cons]
    exact ⟨g1, fun d i => Nat.le_trans (h2 d i) (g2 d i), g3.trans h3⟩

theorem machine_apply (st : State) (m : Machine) :
    (applyEffect st (.machine m)).days = st.days ∧ (applyEffect st (.machine m)).machine = m :=
  ⟨rfl, rfl⟩

/-- Safe effects keep the invariant. -/
theorem conserves_safe (st : State) (fx : List Effect) (hs : ∀ x ∈ fx, x.safe = true) (h : Conserves st) :
    Conserves (applyEffects st fx) := by
  obtain ⟨g1, g2, g3⟩ := safe_list fx hs st h.1
  exact ⟨g1, fun d i => by rw [g3]; exact Nat.le_trans (h.2.1 d i) (g2 d i), by rw [g3]; exact h.2.2⟩

/-- Safe effects, then a machine whose held credits are no more than the old machine's and whose last cut is its
first held, keep the invariant. -/
theorem conserves_safe_then_machine (st : State) (fx : List Effect) (m : Machine)
    (hs : ∀ x ∈ fx, x.safe = true) (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ ((st.machine.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum) (ho : HeadOk m)
    (h : Conserves st) : Conserves (applyEffects st (fx ++ [.machine m])) := by
  rw [applyEffects_append]
  obtain ⟨g1, g2, -⟩ := safe_list fx hs st h.1
  exact ⟨g1, fun d i => Nat.le_trans (hh d i) (Nat.le_trans (h.2.1 d i) (g2 d i)), ho⟩

/-- Safe effects, then a machine keeping the closed blocks and the last cut, keep the invariant. -/
theorem conserves_safe_then_kept (st : State) (fx : List Effect) (m : Machine)
    (hs : ∀ x ∈ fx, x.safe = true) (hc : m.closed = st.machine.closed) (hl : m.lastCut = st.machine.lastCut)
    (h : Conserves st) : Conserves (applyEffects st (fx ++ [.machine m])) :=
  conserves_safe_then_machine st fx m hs (fun d i => by rw [hc]; exact Nat.le_refl _)
    (fun c hcm => by rw [hc]; rw [hl] at hcm; exact h.2.2 c hcm) h

/-- **Settling moves only the open block's drawing** (the owner's D99): the last cut, the interruption, the breaks held
and the running break are the machine's, and the block keeps its id, start, day, pause, pending observation and idle
spans. -/
theorem settle_keeps (dy : Cal.Instant → Nat) (m : Machine) :
    (settle dy m).1.lastCut = m.lastCut ∧ (settle dy m).1.interrupt = m.interrupt ∧
      (settle dy m).1.brks = m.brks ∧ (settle dy m).1.brkOpen = m.brkOpen ∧
      (settle dy m).1.block.map (fun b => (b.id, b.started, b.day, b.paused, b.pausedAt, b.obs, b.idle)) =
        m.block.map (fun b => (b.id, b.started, b.day, b.paused, b.pausedAt, b.obs, b.idle)) := by
  unfold settle
  split
  · rename_i b hb
    simp [hb]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Settling keeps the pending observation** (D99). -/
theorem settle_obs (dy : Cal.Instant → Nat) (m : Machine) :
    (settle dy m).1.block.bind (·.obs) = m.block.bind (·.obs) := by
  unfold settle
  split
  · rename_i b hb; simp [hb]
  · rfl

/-- **Settling an open block leaves one open** (D99), and none where there was none. -/
theorem settle_block_isSome (dy : Cal.Instant → Nat) (m : Machine) :
    (settle dy m).1.block.isSome = m.block.isSome := by
  unfold settle
  split
  · rename_i b hb; simp [hb]
  · rfl

theorem closePauseM_keeps (m : Machine) (t : At) :
    (closePauseM m t).lastCut = m.lastCut ∧ (closePauseM m t).interrupt = m.interrupt ∧
      (closePauseM m t).brks = m.brks ∧ (closePauseM m t).brkOpen = m.brkOpen := by
  unfold closePauseM; repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem closePause_lastCut (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    (closePause dy m t).1.lastCut = m.lastCut ∧ (closePause dy m t).1.interrupt = m.interrupt :=
  ⟨(closePauseM_keeps m t).1, (closePauseM_keeps m t).2.1⟩

/-- **Closing a pause keeps the breaks held** (the owner's D92; D94's `brks`). -/
theorem closePause_brk (dy : Cal.Instant → Nat) (m : Machine) (t : At) : (closePause dy m t).1.brks = m.brks := by
  unfold closePause closePauseM; repeat' split
  all_goals rfl

/-- **A cut keeps the breaks held** (the owner's D92; D94's `brks`): the next block's clock reads them. -/
theorem cut_brk (dy : Cal.Instant → Nat) (m : Machine) (t : At) : (cut dy m t).1.brks = m.brks := by
  unfold cut; split <;> rfl

/-- **Closing a pause, a block or a `done`'s block keeps the running break** (the owner's D105): only a `break_start`
opens it and only a `break` line ends it. -/
theorem closePause_brkOpen (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    (closePause dy m t).1.brkOpen = m.brkOpen := by
  unfold closePause closePauseM; repeat' split
  all_goals rfl

theorem cut_brkOpen (dy : Cal.Instant → Nat) (m : Machine) (t : At) : (cut dy m t).1.brkOpen = m.brkOpen := by
  unfold cut; split <;> rfl

theorem doneClose_brkOpen (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat)
    (went : Option U8) : (doneClose dy m t id actual went).1.brkOpen = m.brkOpen := by
  unfold doneClose
  repeat' split
  all_goals rfl

/-- **`liftGo` answers its instant or the end of one of its spans.** -/
theorem liftGo_cases (H : List (At × At)) : ∀ (n : Nat) (t : At), liftGo H n t = t ∨ liftGo H n t ∈ H.map (·.2)
  | 0, t => Or.inl rfl
  | n + 1, t => by
    unfold liftGo
    split
    · rename_i p hp
      rcases liftGo_cases H n p.2 with h | h
      · rw [h]; exact Or.inr (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hp, rfl⟩)
      · exact Or.inr h
    · exact Or.inl rfl

/-- **The bound keeps only breaks it was given.** -/
theorem mem_pruneBrks {l : List HeldBrk} {k : HeldBrk} (h : k ∈ pruneBrks l) : k ∈ l := by
  unfold pruneBrks at h
  exact (List.mem_filter.1 h).1

/-- **A span of a block's days is the span of a break the machine holds.** -/
theorem mem_spansFor {l : List HeldBrk} {day : Nat} {p : At × At} (h : p ∈ spansFor l day) :
    ∃ k ∈ l, day ≤ k.day ∧ p = (k.s, k.e) := by
  unfold spansFor at h
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
  obtain ⟨hk, hd⟩ := List.mem_filter.1 hk
  exact ⟨k, hk, by simpa using hd, rfl⟩

/-- **The ends of a block's spans are ends of breaks the machine holds.** -/
theorem spansFor_end {l : List HeldBrk} {day : Nat} {q : At} (h : q ∈ (spansFor l day).map (·.2)) :
    q ∈ l.map (·.e) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
  obtain ⟨k, hk, -, rfl⟩ := mem_spansFor hp
  exact List.mem_map.2 ⟨k, hk, rfl⟩

/-- **`nextStart` answers the start of a nonempty span, which that span covers.** -/
theorem nextStart_covers (H : List (At × At)) (x t s : At) (h : nextStart H x t = some s) :
    ∃ p ∈ H, covers p s = true := by
  have key : ∀ (l : List (At × At)) (acc : Option At), (∀ p ∈ l, p ∈ H) →
      (∀ a, acc = some a → ∃ p ∈ H, covers p a = true) →
      ∀ a, l.foldl (fun acc p =>
        if x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1 then
          match acc with
          | some a => if p.1.1 < a.1 then some p.1 else acc
          | none => some p.1
        else acc) acc = some a → ∃ p ∈ H, covers p a = true := by
    intro l
    induction l with
    | nil => intro acc _ hacc a ha; exact hacc a ha
    | cons p l ih =>
      intro acc hl hacc a ha
      rw [List.foldl_cons] at ha
      refine ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) ?_ a ha
      intro a' ha'
      have hp : p ∈ H := hl p List.mem_cons_self
      have hcov : (x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1) → covers p p.1 = true := by
        intro hc
        unfold covers
        simp only [decide_eq_true_eq]
        refine ⟨?_, hc.2.2⟩
        rw [Cal.Instant.le_iff]; omega
      split at ha'
      · rename_i hc
        cases hacc' : acc with
        | none =>
          rw [hacc'] at ha'
          simp only [Option.some.injEq] at ha'
          subst ha'
          exact ⟨p, hp, hcov hc⟩
        | some a0 =>
          rw [hacc'] at ha'
          simp only at ha'
          split at ha'
          · simp only [Option.some.injEq] at ha'
            subst ha'
            exact ⟨p, hp, hcov hc⟩
          · exact hacc a' (hacc'.trans ha')
      · exact hacc a' ha'
  exact key H none (fun p hp => hp) (fun a h => by cases h) s h

/-- **Every piece starts at the stretch's own start, which no span covers, or at a span's end** — so a piece's start is
an instant the machine holds or the clock's, where `redraw` reads the day index. -/
theorem piecesGo_starts (H : List (At × At)) : ∀ (n : Nat) (x t : At) (q : At × At), q ∈ piecesGo H n x t →
    (q.1 = x ∧ ∀ p ∈ H, covers p x = false) ∨ q.1 ∈ H.map (·.2)
  | 0, _, _, _, h => by simp [piecesGo] at h
  | n + 1, x, t, q, h => by
    unfold piecesGo at h
    simp only at h
    split at h
    · simp at h
    · rename_i hg
      have hunc : ∀ p ∈ H, covers p (lift H x) = false := by
        intro p hp
        cases hc : covers p (lift H x) with
        | false => rfl
        | true =>
          exfalso; apply hg
          simp only [Bool.or_eq_true, List.any_eq_true]
          exact Or.inl ⟨p, hp, hc⟩
      have hfirst : ((lift H x) = x ∧ ∀ p ∈ H, covers p x = false) ∨ lift H x ∈ H.map (·.2) := by
        rcases liftGo_cases H H.length x with h1 | h1
        · left
          refine ⟨h1, fun p hp => ?_⟩
          have := hunc p hp
          unfold lift at this
          rwa [h1] at this
        · exact Or.inr h1
      split at h
      · simp only [List.mem_singleton] at h
        subst h
        exact hfirst
      · rename_i s hs
        rcases List.mem_cons.1 h with h | h
        · subst h; exact hfirst
        · rcases piecesGo_starts H n s t q h with ⟨-, hcov⟩ | h2
          · exfalso
            obtain ⟨p, hp, hc⟩ := nextStart_covers H _ _ s hs
            rw [hcov p hp] at hc; cases hc
          · exact Or.inr h2

/-- **A piece a break cuts out of a closed block's pieces begins where one of them began, or at the break's end** (the
owner's D100). -/
theorem cutOut_starts (s e : At) (P : List (At × At)) (q : At × At) (hq : q ∈ cutOut s e P) :
    (∃ r ∈ P, q.1 = r.1) ∨ q.1 = e := by
  unfold cutOut at hq
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 hq
  unfold pieces at hq
  rcases piecesGo_starts [(s, e)] _ r.1 r.2 q hq with ⟨h1, -⟩ | h1
  · exact Or.inl ⟨r, hr, h1⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at h1
    exact Or.inr h1

/-- **Every piece of a stretch begins before the stretch ends** (the owner's D115). -/
theorem piecesGo_lt (H : List (At × At)) : ∀ (n : Nat) (x t : At) (q : At × At), q ∈ piecesGo H n x t → q.1.1 < t.1
  | 0, _, _, _, h => by simp [piecesGo] at h
  | n + 1, x, t, q, h => by
    unfold piecesGo at h
    simp only at h
    split at h
    · simp at h
    · rename_i hg
      have hx : (lift H x).1 < t.1 := by
        have hn : ¬ t.1 ≤ (lift H x).1 := fun h' => hg (by simp [h'])
        rcases Cal.Instant.le_total t.1 (lift H x).1 with h' | h'
        · exact absurd h' hn
        · rw [Cal.Instant.lt_iff]; rw [Cal.Instant.le_iff] at h'
          have hn' := hn
          rw [Cal.Instant.le_iff] at hn'
          omega
      split at h
      · simp only [List.mem_singleton] at h; subst h; exact hx
      · rcases List.mem_cons.1 h with h | h
        · subst h; exact hx
        · exact piecesGo_lt H n _ t q h

/-- **A piece `cutOut` leaves begins before the piece it was cut from ends** (the owner's D115). -/
theorem cutOut_lt (s e : At) (P : List (At × At)) (q : At × At) (hq : q ∈ cutOut s e P) :
    ∃ r ∈ P, q.1.1 < r.2.1 := by
  unfold cutOut at hq
  obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 hq
  exact ⟨r, hr, piecesGo_lt _ _ r.1 r.2 q hq⟩

/-- The `foldl` `startEnd` takes is at or after where it began and every piece's end (the owner's D115). -/
theorem foldl_end_ge : ∀ (l : List Piece) (b : At),
    b.1 ≤ (l.foldl (fun b p => if b.1 < p.e.1 then p.e else b) b).1 ∧
      ∀ p ∈ l, p.e.1 ≤ (l.foldl (fun b p => if b.1 < p.e.1 then p.e else b) b).1
  | [], b => ⟨by simp only [List.foldl_nil]; rw [Cal.Instant.le_iff]; omega, by simp⟩
  | p :: l, b => by
    simp only [List.foldl_cons]
    by_cases hc : b.1 < p.e.1
    · simp only [hc, if_true]
      obtain ⟨h1, h2⟩ := foldl_end_ge l p.e
      refine ⟨?_, fun p' hp' => ?_⟩
      · rw [Cal.Instant.lt_iff] at hc; rw [Cal.Instant.le_iff] at h1 ⊢; omega
      · rcases List.mem_cons.1 hp' with rfl | hp'
        · exact h1
        · exact h2 p' hp'
    · simp only [hc, if_false]
      obtain ⟨h1, h2⟩ := foldl_end_ge l b
      refine ⟨h1, fun p' hp' => ?_⟩
      rcases List.mem_cons.1 hp' with rfl | hp'
      · have := (Cal.Instant.not_lt _ _).1 hc
        rw [Cal.Instant.le_iff] at h1 this ⊢; omega
      · exact h2 p' hp'

/-- **A late start's span lies past every piece of a block it is stamped inside** (the owner's D115). -/
theorem startEnd_ge (t : At) (C : Closed) (h : C.drawn.any (fun p => decide (p.s.1 < t.1)) = true) :
    ∀ p ∈ C.drawn, p.e.1 ≤ (startEnd t C).1 := by
  unfold startEnd; rw [if_pos h]; exact (foldl_end_ge C.drawn t).2

/-- **A block with no piece begun before a `start` is not cut by it** (the owner's D115): `netOne`'s guard holds. -/
theorem startEnd_guard (t : At) (C : Closed) (h : C.drawn.any (fun p => decide (p.s.1 < t.1)) = false) :
    C.drawn.all (fun p => decide (p.e.1 ≤ t.1 ∨ (startEnd t C).1 ≤ p.s.1)) = true := by
  unfold startEnd; rw [if_neg (by simp [h])]
  rw [List.all_eq_true]
  intro p hp
  have := List.any_eq_false.1 h p hp
  simp only [decide_eq_true_eq] at this ⊢
  exact Or.inr ((Cal.Instant.not_lt _ _).1 this)

/-- **A late start's cut draws no piece beginning anywhere new** (the owner's D115): with a piece of `C` begun before
`t`, every piece `cutOut t (startEnd t C)` leaves begins where one of `C`'s began — never at the span's end, which lies
past every piece of `C` (`startEnd_ge`). -/
theorem cutOut_startEnd_starts (t : At) (C : Closed) (h : C.drawn.any (fun p => decide (p.s.1 < t.1)) = true)
    (q : At × At) (hq : q ∈ cutOut t (startEnd t C) C.spans) : ∃ r ∈ C.spans, q.1 = r.1 := by
  rcases cutOut_starts t (startEnd t C) C.spans q hq with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨r, hr, hlt⟩ := cutOut_lt t (startEnd t C) C.spans q hq
    unfold Closed.spans at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    have hge := startEnd_ge t C h p hp
    rw [h1] at hlt
    rw [Cal.Instant.lt_iff] at hlt; rw [Cal.Instant.le_iff] at hge; simp only at hlt; omega

/-- **The running break's span lies past every piece a held closed block drew** (README gap 5180): `runTo s l` is at or
after `s` and every held piece's end. -/
theorem runTo_ge : ∀ (l : List Closed) (a : At),
    a.1 ≤ (runTo a l).1 ∧ ∀ C ∈ l, ∀ p ∈ C.drawn, p.e.1 ≤ (runTo a l).1
  | [], a => ⟨by simp only [runTo]; rw [Cal.Instant.le_iff]; omega, by simp⟩
  | C :: l, a => by
    have h1 := foldl_end_ge C.drawn a
    have h2 := runTo_ge l (C.drawn.foldl (fun b p => if b.1 < p.e.1 then p.e else b) a)
    have e : runTo a (C :: l) = runTo (C.drawn.foldl (fun b p => if b.1 < p.e.1 then p.e else b) a) l := rfl
    rw [e]
    refine ⟨?_, fun C' hC' p hp => ?_⟩
    · have := h1.1; have := h2.1; rw [Cal.Instant.le_iff] at *; omega
    · rcases List.mem_cons.1 hC' with rfl | hC'
      · have := h1.2 p hp; have := h2.1; rw [Cal.Instant.le_iff] at *; omega
      · exact h2.2 C' hC' p hp

/-- **The running break's netting draws no piece beginning anywhere new** (README gap 5180): every piece
`cutOut s (runTo s l)` leaves of a held block begins where one of the block's own began — never at the span's end, which
lies past every held piece (`runTo_ge`). -/
theorem cutOut_runTo_starts (s : At) (l : List Closed) (C : Closed) (hC : C ∈ l) (q : At × At)
    (hq : q ∈ cutOut s (runTo s l) C.spans) : ∃ r ∈ C.spans, q.1 = r.1 := by
  rcases cutOut_starts s (runTo s l) C.spans q hq with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨r, hr, hlt⟩ := cutOut_lt s (runTo s l) C.spans q hq
    unfold Closed.spans at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    have hge := (runTo_ge l s).2 C hC p hp
    rw [h1] at hlt
    rw [Cal.Instant.lt_iff] at hlt; rw [Cal.Instant.le_iff] at hge; simp only at hlt; omega

/-- **`lift` lands where no span covers** (the owner's D94), given a jump for every span still ending after its
instant: each jump lands on a covering span's end, later than the instant, and leaves that span behind. -/
theorem liftGo_uncovered (H : List (At × At)) : ∀ (n : Nat) (t : At),
    H.countP (fun p => decide (t.1 < p.2.1)) ≤ n → ∀ p ∈ H, covers p (liftGo H n t) = false
  | 0, t, hn, p, hp => by
    unfold liftGo covers
    have h0 : H.countP (fun p => decide (t.1 < p.2.1)) = 0 := by omega
    rw [List.countP_eq_zero] at h0
    have := h0 p hp
    simp only [decide_eq_true_eq] at this
    simp only [decide_eq_false_iff_not, not_and]
    intro _; exact this
  | n + 1, t, hn, p, hp => by
    unfold liftGo
    split
    · rename_i q hq
      have hqH : q ∈ H := List.mem_of_find?_eq_some hq
      have hqc : (fun p => covers p t) q = true := List.find?_some (p := fun p => covers p t) hq
      simp only at hqc
      unfold covers at hqc
      simp only [decide_eq_true_eq] at hqc
      apply liftGo_uncovered H n q.2 _ p hp
      have hlt := countP_lt_of_witness (fun p => decide (q.2.1 < p.2.1)) (fun p => decide (t.1 < p.2.1))
        (fun x hx => by
          simp only [decide_eq_true_eq] at hx ⊢
          exact Cal.Instant.lt_trans hqc.2 hx)
        H q hqH (by simpa using hqc.2) (by simp [Cal.Instant.lt_irrefl])
      omega
    · rename_i hnone
      cases hc : covers p t with
      | false => rfl
      | true =>
        exfalso
        rw [List.find?_eq_none] at hnone
        exact absurd hc (by simpa using hnone p hp)

/-- **Where `lift` lands, no span covers.** -/
theorem lift_uncovered (H : List (At × At)) (t : At) : ∀ p ∈ H, covers p (lift H t) = false :=
  liftGo_uncovered H H.length t (List.countP_le_length)

/-- `runFrom` lands at or after its start and after every nonempty span's end. -/
theorem runFrom_step_ge (H : List (At × At)) : ∀ (x : At),
    x.1 ≤ (runFrom H x).1 ∧ ∀ p ∈ H, p.1.1 < p.2.1 → p.2.1 ≤ (runFrom H x).1 := by
  induction H with
  | nil =>
    intro x
    refine ⟨?_, fun p hp => by cases hp⟩
    show x.1 ≤ x.1
    rw [Cal.Instant.le_iff]; omega
  | cons q H ih =>
    intro x
    show x.1 ≤ (runFrom H (if q.1.1 < q.2.1 ∧ x.1 < q.2.1 then q.2 else x)).1 ∧
      ∀ p ∈ q :: H, p.1.1 < p.2.1 → p.2.1 ≤ (runFrom H (if q.1.1 < q.2.1 ∧ x.1 < q.2.1 then q.2 else x)).1
    generalize hy : (if q.1.1 < q.2.1 ∧ x.1 < q.2.1 then q.2 else x) = y
    obtain ⟨k1, k2⟩ := ih y
    have hxy : x.1 ≤ y.1 ∧ (q.1.1 < q.2.1 → q.2.1 ≤ y.1) := by
      subst hy
      split
      · rename_i hq
        have h2 := hq.2
        refine ⟨?_, fun _ => ?_⟩
        · rw [Cal.Instant.lt_iff] at h2; rw [Cal.Instant.le_iff]; omega
        · rw [Cal.Instant.le_iff]; omega
      · rename_i hq
        refine ⟨by rw [Cal.Instant.le_iff]; omega, fun hne => ?_⟩
        have : ¬ x.1 < q.2.1 := fun h => hq ⟨hne, h⟩
        rw [Cal.Instant.lt_iff] at this; rw [Cal.Instant.le_iff]; omega
    refine ⟨?_, fun p hp hne => ?_⟩
    · have h1 := hxy.1
      rw [Cal.Instant.le_iff] at h1 k1 ⊢; omega
    · rcases List.mem_cons.1 hp with rfl | hp
      · have h1 := hxy.2 hne
        rw [Cal.Instant.le_iff] at h1 k1 ⊢; omega
      · exact k2 p hp hne

/-- **Where `runFrom` lands, no span covers** (the owner's D99): it is at least every nonempty span's end. -/
theorem runFrom_uncovered (H : List (At × At)) (x : At) : ∀ p ∈ H, covers p (runFrom H x) = false := by
  intro p hp
  unfold covers
  simp only [decide_eq_false_iff_not, not_and]
  intro h1 h2
  have hne : p.1.1 < p.2.1 := by
    have h1' := h1; have h2' := h2
    rw [Cal.Instant.le_iff] at h1'; rw [Cal.Instant.lt_iff] at h2' ⊢; omega
  have := (runFrom_step_ge H x).2 p hp hne
  rw [Cal.Instant.le_iff] at this; rw [Cal.Instant.lt_iff] at h2; omega

/-- **A settled block's clock runs from outside every span it nets** (the owner's D94, README gap 4506; D99): no break
of its ledger days the machine holds and none of its own idle spans covers the instant its clock runs from — the
start, the `unpause` and the `resume`, and every mark logged after the stretch it lies across, read the union. -/
theorem settle_runs_outside_every_span_it_nets (dy : Cal.Instant → Nat) (m : Machine) (b : Block)
    (hb : m.block = some b) (x : At) (hx : (settle dy m).1.block.bind (·.since) = some x) :
    ∀ p ∈ blockSpans b m, covers p x = false := by
  unfold settle at hx
  rw [hb] at hx
  simp only [Option.bind_some] at hx
  split at hx
  · cases hx
  · cases hx; exact runFrom_uncovered _ _

/-- **`nextStart` answers the earliest nonempty span start strictly inside, or `none` when there is none.** -/
theorem nextStart_spec (H : List (At × At)) (x t : At) :
    (nextStart H x t = none → ∀ p ∈ H, ¬ (x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1)) ∧
    (∀ s, nextStart H x t = some s → ∀ p ∈ H, x.1 < p.1.1 → p.1.1 < t.1 → p.1.1 < p.2.1 → s.1 ≤ p.1.1) := by
  let f := fun (acc : Option At) (p : At × At) =>
    if x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1 then
      match acc with
      | some a => if p.1.1 < a.1 then some p.1 else acc
      | none => some p.1
    else acc
  have key : ∀ (l : List (At × At)) (acc : Option At),
      (l.foldl f acc = none → acc = none ∧ ∀ p ∈ l, ¬ (x.1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1)) ∧
      (∀ s, l.foldl f acc = some s → (∀ a, acc = some a → s.1 ≤ a.1) ∧
        ∀ p ∈ l, x.1 < p.1.1 → p.1.1 < t.1 → p.1.1 < p.2.1 → s.1 ≤ p.1.1) := by
    intro l
    induction l with
    | nil =>
      intro acc
      constructor
      · intro h
        simp only [List.foldl_nil] at h
        exact ⟨h, fun p hp => absurd hp List.not_mem_nil⟩
      · intro s h
        simp only [List.foldl_nil] at h
        refine ⟨fun a ha => ?_, fun p hp => absurd hp List.not_mem_nil⟩
        rw [h] at ha
        simp only [Option.some.injEq] at ha
        subst ha
        rw [Cal.Instant.le_iff]; omega
    | cons p l ih =>
      intro acc
      rw [List.foldl_cons]
      obtain ⟨ih1, ih2⟩ := ih (f acc p)
      refine ⟨fun h => ?_, fun s h => ?_⟩
      · obtain ⟨hf, hl⟩ := ih1 h
        simp only [f] at hf
        split at hf
        · split at hf <;> (try split at hf) <;> cases hf
        · refine ⟨hf, fun q hq => ?_⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · assumption
          · exact hl q hq
      · obtain ⟨hacc, hl⟩ := ih2 s h
        simp only [f] at hacc
        split at hacc
        · rename_i hc
          cases ha : acc with
          | none =>
            rw [ha] at hacc
            have hs := hacc p.1 rfl
            refine ⟨fun a h' => (by cases h'), fun q hq => ?_⟩
            rcases List.mem_cons.1 hq with rfl | hq
            · intro _ _ _; exact hs
            · exact hl q hq
          | some a0 =>
            rw [ha] at hacc
            simp only at hacc
            split at hacc
            · rename_i hpa
              have hs := hacc p.1 rfl
              refine ⟨fun a h' => ?_, fun q hq => ?_⟩
              · simp only [Option.some.injEq] at h'; subst h'
                rw [Cal.Instant.le_iff] at hs ⊢; rw [Cal.Instant.lt_iff] at hpa; omega
              · rcases List.mem_cons.1 hq with rfl | hq
                · intro _ _ _; exact hs
                · exact hl q hq
            · rename_i hpa
              have hs := hacc a0 rfl
              refine ⟨fun a h' => by simp only [Option.some.injEq] at h'; subst h'; exact hs, fun q hq => ?_⟩
              rcases List.mem_cons.1 hq with rfl | hq
              · intro _ _ _
                rw [Cal.Instant.not_lt] at hpa
                rw [Cal.Instant.le_iff] at hs hpa ⊢; omega
              · exact hl q hq
        · rename_i hc
          refine ⟨hacc, fun q hq => ?_⟩
          rcases List.mem_cons.1 hq with rfl | hq
          · intro h1 h2 h3; exact absurd ⟨h1, h2, h3⟩ hc
          · exact hl q hq
  refine ⟨fun h => (key H none).1 h |>.2, fun s h => (key H none).2 s h |>.2⟩

/-- **No piece lies across a nonempty span** (the owner's D94): every piece of a closed stretch ends at or before a
span's start, or starts at or after its end. -/
theorem piecesGo_avoids (H : List (At × At)) : ∀ (n : Nat) (x t : At) (q : At × At), q ∈ piecesGo H n x t →
    ∀ p ∈ H, p.1.1 < p.2.1 → q.2.1 ≤ p.1.1 ∨ p.2.1 ≤ q.1.1
  | 0, _, _, _, h => by simp [piecesGo] at h
  | n + 1, x, t, q, h => by
    unfold piecesGo at h
    simp only at h
    split at h
    · simp at h
    · rename_i hg
      have hunc : ∀ p ∈ H, covers p (lift H x) = false := by
        intro p hp
        cases hc : covers p (lift H x) with
        | false => rfl
        | true =>
          exfalso; apply hg
          simp only [Bool.or_eq_true, List.any_eq_true]
          exact Or.inl ⟨p, hp, hc⟩
      have hxt : (lift H x).1 < t.1 := by
        have : ¬ t.1 ≤ (lift H x).1 := fun h' => hg (by simp [h'])
        rw [Cal.Instant.le_iff] at this; rw [Cal.Instant.lt_iff]; omega
      -- the first piece starts at an uncovered `lift H x` and ends at the first span start after it, or at `t`
      have hfirst : ∀ y : At, (∀ p ∈ H, p.1.1 < p.2.1 → (lift H x).1 < p.1.1 → y.1 ≤ p.1.1) →
          ∀ p ∈ H, p.1.1 < p.2.1 → y.1 ≤ p.1.1 ∨ p.2.1 ≤ (lift H x).1 := by
        intro y hy p hp hne
        by_cases hlt : (lift H x).1 < p.1.1
        · exact Or.inl (hy p hp hne hlt)
        · right
          have hc := hunc p hp
          unfold covers at hc
          simp only [decide_eq_false_iff_not, not_and] at hc
          rw [Cal.Instant.not_lt] at hlt
          have := hc hlt
          rwa [Cal.Instant.not_lt] at this
      split at h
      · rename_i hns
        simp only [List.mem_singleton] at h
        subst h
        refine hfirst t (fun p hp hne hlt => ?_)
        by_cases hpt : p.1.1 < t.1
        · exact absurd ⟨hlt, hpt, hne⟩ ((nextStart_spec H _ t).1 hns p hp)
        · rwa [Cal.Instant.not_lt] at hpt
      · rename_i s hs
        rcases List.mem_cons.1 h with h | h
        · subst h
          refine hfirst s (fun p hp hne hlt => ?_)
          by_cases hpt : p.1.1 < t.1
          · exact (nextStart_spec H _ t).2 s hs p hp hlt hpt hne
          · rw [Cal.Instant.not_lt] at hpt
            have := (nextStart_spec H _ t).2 s hs
            obtain ⟨p0, hp0, hc0⟩ := nextStart_covers H _ _ s hs
            -- `s` is before `t`
            have hst : s.1 < t.1 := by
              have hfold : ∀ (l : List (At × At)) (acc : Option At), (∀ a, acc = some a → a.1 < t.1) →
                  ∀ a, l.foldl (fun acc p =>
                    if (lift H x).1 < p.1.1 ∧ p.1.1 < t.1 ∧ p.1.1 < p.2.1 then
                      match acc with
                      | some a => if p.1.1 < a.1 then some p.1 else acc
                      | none => some p.1
                    else acc) acc = some a → a.1 < t.1 := by
                intro l
                induction l with
                | nil => intro acc h a ha; exact h a ha
                | cons p l ih =>
                  intro acc hacc a ha
                  rw [List.foldl_cons] at ha
                  refine ih _ ?_ a ha
                  intro a' ha'
                  split at ha'
                  · rename_i hc
                    split at ha'
                    · split at ha'
                      · simp only [Option.some.injEq] at ha'; subst ha'; exact hc.2.1
                      · exact hacc a' ha'
                    · simp only [Option.some.injEq] at ha'; subst ha'; exact hc.2.1
                  · exact hacc a' ha'
              exact hfold H none (fun a h => by cases h) s hs
            rw [Cal.Instant.le_iff] at hpt ⊢; rw [Cal.Instant.lt_iff] at hst; omega
        · exact piecesGo_avoids H n s t q h

/-- **Every segment a re-draw draws is a span it was given** (D99). -/
theorem redraw_draws_its_spans (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) :
    ∀ x ∈ (redraw dy id old P).2, ∀ d g, x = .dayAdd d (.segment g) → (g.start, g.stop) ∈ P ∧ g.kind = .block id := by
  intro x hx d g hxg
  unfold redraw at hx
  simp only [List.mem_append, List.mem_map, List.mem_filter] at hx
  rcases hx with ⟨p, -, rfl⟩ | ⟨q, ⟨hq, -⟩, rfl⟩
  · simp at hxg
  · simp only [Effect.dayAdd.injEq, DayOp.segment.injEq] at hxg
    obtain ⟨-, rfl⟩ := hxg
    exact ⟨hq, rfl⟩

/-- **No Block a settled block draws lies across a span it nets** (the owner's D94, README gap 4361; D99, gap 4520a):
every `Block` segment `settle` emits ends at or before a nonempty break of the block's ledger days the machine holds,
or one of its own idle spans, or starts at or after its end — wherever the mark that brought the span was logged.  Its
minutes are those pieces' (site R8), so what the replay draws and what it credits read the block one way. -/
theorem settle_avoids_every_span_it_nets (dy : Cal.Instant → Nat) (m : Machine) (b : Block)
    (hb : m.block = some b) :
    ∀ x ∈ (settle dy m).2, ∀ d g, x = .dayAdd d (.segment g) →
      ∀ p ∈ blockSpans b m, p.1.1 < p.2.1 → g.stop.1 ≤ p.1.1 ∨ p.2.1 ≤ g.start.1 := by
  intro x hx d g hxg p hp hne
  unfold settle at hx
  rw [hb] at hx
  obtain ⟨hq, -⟩ := redraw_draws_its_spans dy b.id b.drawn _ x hx d g hxg
  exact piecesGo_avoids _ _ _ _ (g.start, g.stop) hq p (List.mem_append_left _ hp) hne

/-- **No Block a settled block draws lies across the running break** (README gap 5180, W-49 track L): every `Block`
segment `settle` emits ends at or before the start of the break a `break_start` opened and no `break` line has ended
(`Machine.brkOpen`), or starts at or after the end the block's drawing reaches (`openEnd`) — when the break is on a
ledger day at or after the block's own, the day its `break` line will be held under. -/
theorem settle_avoids_the_running_break (dy : Cal.Instant → Nat) (m : Machine) (b : Block) (o : OpenBrk)
    (hb : m.block = some b) (ho : m.brkOpen = some o) (hd : b.day ≤ o.day) (hne : o.s.1 < (openEnd b m).1) :
    ∀ x ∈ (settle dy m).2, ∀ d g, x = .dayAdd d (.segment g) →
      g.stop.1 ≤ o.s.1 ∨ (openEnd b m).1 ≤ g.start.1 := by
  intro x hx d g hxg
  unfold settle at hx
  rw [hb] at hx
  obtain ⟨hq, -⟩ := redraw_draws_its_spans dy b.id b.drawn _ x hx d g hxg
  have hp : (o.s, openEnd b m) ∈ blockSpans b m ++ runSpan b m (openEnd b m) :=
    List.mem_append_right _ (by simp [runSpan, ho, hd])
  exact piecesGo_avoids _ _ _ _ (g.start, g.stop) hq _ hp hne

/-- **No Block a cut draws lies across a span the block nets** (D99): the same, for the pieces a block is closed with. -/
theorem cut_avoids_every_span_it_nets (dy : Cal.Instant → Nat) (m : Machine) (b : Block)
    (t : At) : ∀ x ∈ (redraw dy b.id b.drawn (cutPieces b m t)).2, ∀ d g, x = .dayAdd d (.segment g) →
      ∀ p ∈ blockSpans b m, p.1.1 < p.2.1 → g.stop.1 ≤ p.1.1 ∨ p.2.1 ≤ g.start.1 := by
  intro x hx d g hxg p hp hne
  obtain ⟨hq, -⟩ := redraw_draws_its_spans dy b.id b.drawn _ x hx d g hxg
  exact piecesGo_avoids _ _ _ _ (g.start, g.stop) hq p hp hne

theorem all_safe_of_plain (fx : List Effect) (h : ∀ x ∈ fx, x.plain = true) : ∀ x ∈ fx, x.safe = true :=
  fun x hx => safe_of_plain x (h x hx)

/-- A credit of ci-unknown minutes leaves at least those minutes on its day. -/
theorem unk_credit_none (st : State) (d : Nat) (i : Id) (w : Nat) :
    w ≤ unk (applyEffect st (.dayAdd d (.credit i w none))) d i := by
  by_cases hw : w = 0
  · rw [hw]; exact Nat.zero_le _
  · have hpos : 0 < w := Nat.pos_of_ne_zero hw
    simp only [unk, applyEffect, HMap.get_alter, if_true]
    cases st.days.get d with
    | some a =>
      simp only [DayOp.alterFn, DayOp.apply, if_pos hpos, KMap.get_alter, if_true]
      simp
    | none =>
      simp only [DayOp.alterFn, DayOp.apply, if_pos hpos, KMap.get_alter, if_true]
      simp

/-- **Settling keeps the closed blocks** (the owner's D100): it moves only the open block's drawing. -/
theorem settle_closed (dy : Cal.Instant → Nat) (m : Machine) : (settle dy m).1.closed = m.closed := by
  unfold settle; split <;> rfl

theorem closePauseM_closed (m : Machine) (t : At) : (closePauseM m t).closed = m.closed := by
  unfold closePauseM; repeat' split
  all_goals rfl

theorem interruptMachine_closed (m : Machine) (t : At) (d : Nat) (id : Option Id) :
    (interruptMachine m t d id).closed = m.closed ∧ (interruptMachine m t d id).lastCut = m.lastCut := by
  unfold interruptMachine
  have e1 := closePauseM_closed m t
  have e2 := (closePauseM_keeps m t).1
  split <;> exact ⟨e1, e2⟩

/-- **A cut of any machine whose held credits the days cover keeps every balance and covers its held credits** — the
proof of `conserves_cut`, over a machine given beside the state (the owner's D115: a `start` cuts the machine its
netting of the closed blocks left). -/
theorem conserves_cut_of (dy : Cal.Instant → Nat) (st : State) (m : Machine) (t : At) (hb0 : Balanced st)
    (hh0 : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) :
    Balanced (applyEffects st (cut dy m t).2) ∧
      (∀ d i, (((cut dy m t).1.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk (applyEffects st (cut dy m t).2) d i) ∧
      (∀ d i, unk st d i ≤ unk (applyEffects st (cut dy m t).2) d i) := by
  unfold cut
  split
  · rename_i b _
    let w := minutesOf (cutPieces b m t)
    let fx0 := (redraw dy b.id b.drawn (cutPieces b m t)).2 ++ (closePause dy m t).2
    have hs0 : ∀ x ∈ fx0, x.safe = true := fun x hx => by
      simp only [fx0, List.mem_append] at hx
      rcases hx with hx | hx
      · exact safe_of_plain x (redraw_plain dy _ _ _ x hx)
      · exact safe_of_plain x (closePause_plain dy _ t x hx)
    obtain ⟨b1, m1, -⟩ := safe_list fx0 hs0 st hb0
    generalize hs0e : applyEffects st fx0 = s0 at b1 m1
    obtain ⟨b2, m2, -⟩ := safe_list [Effect.itemAdd b.id (.credit w), .itemDay b.id (dy t.1) w]
      (by simp [Effect.safe]) s0 b1
    generalize hs1e : applyEffects s0 [Effect.itemAdd b.id (.credit w), .itemDay b.id (dy t.1) w] = s1 at b2 m2
    obtain ⟨b3, m3, -⟩ := safe_apply s1 (.dayAdd (dy t.1) (.credit b.id w none)) rfl b2
    have hex := unk_credit_none_eq s1 (dy t.1) b.id w
    generalize hs2e : applyEffect s1 (.dayAdd (dy t.1) (.credit b.id w none)) = s2 at b3 m3 hex
    obtain ⟨b4, m4, -⟩ := safe_list (obsFx b.obs) (all_safe_of_plain _ (obsFx_plain _)) s2 b3
    have heq : applyEffects st (fx0 ++ creditFx dy b.id t w none ++ obsFx b.obs) = applyEffects s2 (obsFx b.obs) := by
      rw [applyEffects_append, applyEffects_append, hs0e, ← hs2e, ← hs1e]; rfl
    show Balanced (applyEffects st (fx0 ++ creditFx dy b.id t w none ++ obsFx b.obs)) ∧
      (∀ d i, (((pruneClosed (⟨b.id, b.day, dy t.1, none, w, (redraw dy b.id b.drawn (cutPieces b m t)).1,
        none, b.started, [], 0⟩ :: m.closed)).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk (applyEffects st (fx0 ++ creditFx dy b.id t w none ++ obsFx b.obs)) d i) ∧
      (∀ d i, unk st d i ≤ unk (applyEffects st (fx0 ++ creditFx dy b.id t w none ++ obsFx b.obs)) d i)
    rw [heq]
    refine ⟨b4, fun d i => ?_, fun d i => Nat.le_trans (m1 d i) (Nat.le_trans (m2 d i)
      (Nat.le_trans (m3 d i) (m4 d i)))⟩
    refine Nat.le_trans (pruneClosed_held _ d i) ?_
    rw [heldOf_cons]
    have hold := hh0 d i
    by_cases hk : d = dy t.1 ∧ i = b.id
    · obtain ⟨rfl, rfl⟩ := hk
      rw [if_pos ⟨rfl, rfl, rfl⟩]
      have e1 := m1 (dy t.1) b.id
      have e2 := m2 (dy t.1) b.id
      have e4 := m4 (dy t.1) b.id
      show w + ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = (dy t.1) ∧ C.id = b.id))).map (·.min)).sum ≤ unk (applyEffects s2 (obsFx b.obs)) (dy t.1) b.id
      omega
    · have hc : ¬ ((none : Option U8) = none ∧ dy t.1 = d ∧ b.id = i) := by
        rintro ⟨-, h1, h2⟩; exact hk ⟨h1.symm, h2.symm⟩
      rw [if_neg hc, Nat.zero_add]
      exact Nat.le_trans hold (Nat.le_trans (m1 d i) (Nat.le_trans (m2 d i) (Nat.le_trans (m3 d i) (m4 d i))))
  · exact ⟨hb0, hh0, fun _ _ => Nat.le_refl _⟩

/-- **A cut's effects put its credit on its day** (the owner's D100): every balance kept, every ci-unknown minute kept or
raised, and the closed blocks the cut holds — the cut block first, its credit what the effects just filed — stand for no
more than the ci-unknown minutes after it.  Until W-47 track K this read "a cut keeps the invariant, the cut it records
included", over the one last cut the invariant then named. -/
theorem conserves_cut (dy : Cal.Instant → Nat) (st : State) (t : At) (h : Conserves st) :
    Balanced (applyEffects st (cut dy st.machine t).2) ∧
      (∀ d i, (((cut dy st.machine t).1.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk (applyEffects st (cut dy st.machine t).2) d i) ∧
      (∀ d i, unk st d i ≤ unk (applyEffects st (cut dy st.machine t).2) d i) :=
  conserves_cut_of dy st st.machine t h.1 h.2.1

/-- **A cut leaves the last cut its first held block** (D100's `HeadOk`): the cut it records is the block it holds first. -/
theorem cut_headOk (dy : Cal.Instant → Nat) (m : Machine) (t : At) (h : HeadOk m) : HeadOk (cut dy m t).1 := by
  unfold cut
  split
  · intro c hc
    simp only [Option.some.injEq] at hc
    subst hc
    exact ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩
  · exact h

/-- **Safe effects, then any machine whose held credits the days cover and whose last cut is its first held, conserve.** -/
theorem conserves_after (st : State) (fx : List Effect) (m : Machine) (hb : Balanced st)
    (hs : ∀ x ∈ fx, x.safe = true) (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk st d i) (ho : HeadOk m) :
    Conserves (applyEffects st (fx ++ [.machine m])) := by
  rw [applyEffects_append]
  obtain ⟨g1, g2, -⟩ := safe_list fx hs st hb
  exact ⟨g1, fun d i => Nat.le_trans (hh d i) (g2 d i), ho⟩

/-- An uncredit keeps every balance when its day holds the minutes it takes back. -/
theorem bal_apply_uncredit (st : State) (d : Nat) (i : Id) (m : Nat) (hb : Balanced st)
    (hm : m ≤ unk st d i) : Balanced (applyEffect st (.dayAdd d (.uncredit i m))) := by
  intro d' a h'
  simp only [applyEffect, HMap.get_alter] at h'
  split at h'
  · rename_i hd
    subst hd
    cases hg : st.days.get d' with
    | none => rw [hg] at h'; cases h'
    | some a0 =>
      rw [hg] at h'
      simp only [DayOp.alterFn, Option.some.injEq] at h'
      subst h'
      have : m ≤ (a0.ciUnknown.get i).getD 0 := by simpa [unk, hg] using hm
      exact DayAcc.bal_uncredit a0 i m (hb d' a0 hg) this
  · exact hb d' a h'

/-- **D100's net keeps every balance** (`DayAcc.bal_net`), on the day it names, whatever it is asked to take. -/
theorem bal_apply_net (st : State) (d : Nat) (id : Id) (ci : Option U8) (k : Nat) (l : Option Nat) (hb : Balanced st) :
    Balanced (applyEffect st (.dayAdd d (.net id ci k l))) := by
  intro d' a h'
  simp only [applyEffect, HMap.get_alter] at h'
  split at h'
  · rename_i hd
    subst hd
    cases hg : st.days.get d' with
    | none => rw [hg] at h'; cases h'
    | some a0 =>
      rw [hg] at h'
      simp only [DayOp.alterFn, Option.some.injEq] at h'
      subst h'
      exact DayAcc.bal_net a0 id ci k l (hb d' a0 hg)
  · exact hb d' a h'

/-- A machine keeping the closed blocks and the last cut, written alone, keeps the invariant. -/
theorem conserves_machine_kept (st : State) (m : Machine) (hc : m.closed = st.machine.closed)
    (hl : m.lastCut = st.machine.lastCut) (h : Conserves st) :
    Conserves (applyEffects (applyEffect st (.machine m)) []) :=
  ⟨h.1, fun d i => by
      show ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk st d i
      rw [hc]; exact h.2.1 d i,
    fun c hc' => by
      change m.lastCut = some c at hc'
      rw [hl] at hc'
      obtain ⟨C, rest, h1, h2⟩ := h.2.2 c hc'
      exact ⟨C, rest, by show m.closed = C :: rest; rw [hc]; exact h1, h2⟩⟩

/-- **The closing half of a `done` keeps the invariant** (`doneFx`'s machine and its closing effects), the stop-then-done
replacement included: the last cut's minutes are still on its day when they are taken back (`lastCut_le_unk`), and the
block the replacement converts — the first held — stops standing for them as they go.  Until W-47 track K this was
conserves_doneClose, over the machine `doneClose` writes; since the owner's D100 the machine `doneFx` writes holds the
closed blocks `doneClosed` leaves. -/
theorem conserves_doneClosed (dy : Cal.Instant → Nat) (st : State) (line : Nat) (t : At) (id : Id) (actual : Nat)
    (went : Option U8) (ci : U8) (h : Conserves st) :
    Conserves (applyEffects (applyEffect st (.machine { (doneClose dy st.machine t id actual went).1 with
      closed := doneClosed dy st.machine line t id actual ci })) (doneClose dy st.machine t id actual went).2) := by
  rcases hbk : st.machine.block with _ | b
  · rcases hlc : st.machine.lastCut with _ | c
    · simp only [doneClose, doneClosed, hbk, hlc]
      exact conserves_machine_kept st _ rfl hlc.symm h
    · obtain ⟨C, rest, hcl, hid, hday, hci, hmin⟩ := h.2.2 c hlc
      by_cases hcond : 0 < actual ∧ c.id = id
      · simp only [doneClose, doneClosed, hbk, hlc, hcl, if_pos hcond]
        have hle := lastCut_le_unk st h c hlc
        have hheld := h.2.1 c.day c.id
        rw [hcl, heldOf_cons, if_pos ⟨hci, hday, hid⟩] at hheld
        have hrest : ∀ d i, ((rest.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min else 0) ≤
            unk st d i := by
          intro d i; have := h.2.1 d i; rw [hcl, heldOf_cons] at this; omega
        have hC' : ∀ d i, ((({ C with credDay := dy t.1, ci := some ci, min := actual, durLine := some line, ranMin := 0 } ::
            rest).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum = ((rest.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum := by
          intro d i; rw [heldOf_cons, if_neg (fun hc => by cases hc.1)]; omega
        unfold uncreditFx
        split
        · rename_i h0
          refine ⟨h.1, fun d i => ?_, fun c' hc' => ?_⟩
          · show ((({ C with credDay := dy t.1, ci := some ci, min := actual, durLine := some line, ranMin := 0 } :: rest).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum
              ≤ unk st d i
            rw [hC']; have := hrest d i; omega
          · simp [applyEffects, applyEffect] at hc'
        · rename_i h0
          rw [show ∀ (a b c : Effect), [a, b, c] = [a, b] ++ [c] from fun _ _ _ => rfl, applyEffects_append]
          generalize hs0 : applyEffect st _ = s0
          have hs0b : Balanced s0 := by rw [← hs0]; exact h.1
          have hs0u : ∀ d i, unk s0 d i = unk st d i := by intro d i; rw [← hs0]; rfl
          have hs0m : s0.machine.closed =
              { C with credDay := dy t.1, ci := some ci, min := actual, durLine := some line, ranMin := 0 } :: rest ∧
              s0.machine.lastCut = none := by rw [← hs0]; exact ⟨rfl, rfl⟩
          obtain ⟨g1, g2, g3⟩ := safe_list [Effect.itemAdd c.id (.uncredit c.min), .itemDaySub c.id c.day c.min]
            (by simp [Effect.safe]) s0 hs0b
          generalize hs1 : applyEffects s0 [Effect.itemAdd c.id (.uncredit c.min), .itemDaySub c.id c.day c.min] = s1
          rw [hs1] at g1 g2 g3
          have hu : c.min ≤ unk s1 c.day c.id := by have := g2 c.day c.id; rw [hs0u] at this; omega
          refine ⟨bal_apply_uncredit _ c.day c.id c.min g1 hu, fun d i => ?_, fun c' hc' => ?_⟩
          · have he := unk_uncredit_eq s1 c.day c.id c.min hu d i
            have hg2 := g2 d i
            rw [hs0u] at hg2
            show (((applyEffect s1 (.dayAdd c.day (.uncredit c.id c.min))).machine.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
              unk (applyEffect s1 (.dayAdd c.day (.uncredit c.id c.min))) d i
            rw [show (applyEffect s1 (.dayAdd c.day (.uncredit c.id c.min))).machine = s1.machine from rfl, g3,
              hs0m.1, hC']
            have hr := hrest d i
            by_cases hk : d = c.day ∧ i = c.id
            · obtain ⟨rfl, rfl⟩ := hk
              rw [if_pos ⟨rfl, rfl⟩] at he
              rw [if_pos ⟨hci, hday, hid⟩] at hr
              omega
            · rw [if_neg hk] at he
              split at hr <;> omega
          · change (applyEffect s1 (.dayAdd c.day (.uncredit c.id c.min))).machine.lastCut = some c' at hc'
            rw [show (applyEffect s1 (.dayAdd c.day (.uncredit c.id c.min))).machine = s1.machine from rfl, g3,
              hs0m.2] at hc'
            cases hc'
      · simp only [doneClose, doneClosed, hbk, hlc, hcl, if_neg hcond]
        exact conserves_machine_kept st _ hcl.symm hlc.symm h
  · by_cases hid : b.id = id
    · simp only [doneClose, doneClosed, hbk, if_pos hid]
      have hs : ∀ x ∈ (redraw dy b.id b.drawn (cutPieces b st.machine t)).2 ++ (closePause dy st.machine t).2 ++
          obsFx (b.obs.map (wentOn went)), x.safe = true := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact safe_of_plain x (redraw_plain dy _ _ _ x hx)
        · exact safe_of_plain x (closePause_plain dy _ t x hx)
        · exact safe_of_plain x (obsFx_plain _ x hx)
      refine conserves_safe _ _ hs ⟨h.1, fun d i => ?_, fun c hc => ?_⟩
      · show (((pruneClosed (_ :: st.machine.closed)).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk st d i
        refine Nat.le_trans (pruneClosed_held _ d i) ?_
        rw [heldOf_cons, if_neg (fun hc => by cases hc.1)]
        have := h.2.1 d i
        omega
      · simp [applyEffect] at hc
    · simp only [doneClose, doneClosed, hbk, if_neg hid]
      exact conserves_machine_kept st _ rfl rfl h

/-- **C5: the day family's effects are safe**: no machine, no uncredit. -/
theorem dayArm_safe (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat) :
    (dayArm dy sl e t d).all Effect.safe = true := by
  unfold dayArm
  split <;> (repeat' split) <;> simp [Effect.safe]

/-- **One held closed block's netting keeps the balance and its credits standing** (the owner's D100): applied after
whatever else stands for a day's ci-unknown minutes (`X`), its effects leave every day balanced and the netted block,
with `X`, standing for no more than they hold — the net takes from a cut's credit at most what its block stands for,
which the day holds. -/
theorem netOne_conserves (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (C : Closed) (st : State)
    (X : Nat → Id → Nat) (hb : Balanced st)
    (hh : ∀ d i, (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min else 0) + X d i ≤ unk st d i) :
    Balanced (applyEffects st (netOne dy s e dd C).2.1) ∧
      ∀ d i, (if (netOne dy s e dd C).1.ci = none ∧ (netOne dy s e dd C).1.credDay = d ∧ (netOne dy s e dd C).1.id = i
          then (netOne dy s e dd C).1.min else 0) + X d i ≤ unk (applyEffects st (netOne dy s e dd C).2.1) d i := by
  unfold netOne
  split
  · exact ⟨hb, hh⟩
  · obtain ⟨b1, m1, -⟩ := safe_list (redraw dy C.id C.drawn (cutOut s e C.spans)).2
      (all_safe_of_plain _ (redraw_plain dy _ _ _)) st hb
    have hk : netMin s e C ≤ C.min := Nat.min_le_right _ _
    split
    · rename_i hpos
      have heq : applyEffects st ((redraw dy C.id C.drawn (cutOut s e C.spans)).2 ++
          [.dayAdd C.credDay (.net C.id C.ci (netMin s e C) C.durLine), .itemAdd C.id (.uncredit (netMin s e C)),
           .itemDaySub C.id C.credDay (netMin s e C)]) =
          applyEffects (applyEffect (applyEffects st (redraw dy C.id C.drawn (cutOut s e C.spans)).2)
            (.dayAdd C.credDay (.net C.id C.ci (netMin s e C) C.durLine)))
            [Effect.itemAdd C.id (.uncredit (netMin s e C)), .itemDaySub C.id C.credDay (netMin s e C)] := by
        rw [applyEffects_append]; rfl
      rw [heq]
      generalize hs0e : applyEffects st (redraw dy C.id C.drawn (cutOut s e C.spans)).2 = s0 at b1 m1 ⊢
      have hb1 := bal_apply_net s0 C.credDay C.id C.ci (netMin s e C) C.durLine b1
      have hn0 := unk_net s0 C.credDay C.id C.ci (netMin s e C) C.durLine
      generalize hs1e : applyEffect s0 (.dayAdd C.credDay (.net C.id C.ci (netMin s e C) C.durLine)) = s1 at hb1 hn0 ⊢
      obtain ⟨b2, m2, -⟩ := safe_list [Effect.itemAdd C.id (.uncredit (netMin s e C)),
        .itemDaySub C.id C.credDay (netMin s e C)] (by simp [Effect.safe]) s1 hb1
      generalize hs2e : applyEffects s1 [Effect.itemAdd C.id (.uncredit (netMin s e C)),
        .itemDaySub C.id C.credDay (netMin s e C)] = s2 at b2 m2 ⊢
      refine ⟨b2, fun d i => ?_⟩
      have hn := hn0 d i
      have hm1 := m1 d i
      have hm2 := m2 d i
      have hd := hh d i
      show (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min - netMin s e C else 0) + X d i ≤ unk s2 d i
      by_cases hc : C.ci = none ∧ C.credDay = d ∧ C.id = i
      · obtain ⟨hci, rfl, rfl⟩ := hc
        rw [if_pos ⟨hci, rfl, rfl⟩] at hd ⊢
        rw [if_pos ⟨hci, rfl, rfl⟩] at hn
        have hmin : min (netMin s e C) (unk s0 C.credDay C.id) = netMin s e C := by
          rw [Nat.min_def]; split <;> omega
        rw [hmin] at hn
        omega
      · rw [if_neg hc] at hd ⊢
        have hc2 : ¬ (C.ci = none ∧ d = C.credDay ∧ i = C.id) := fun h2 => hc ⟨h2.1, h2.2.1.symm, h2.2.2.symm⟩
        rw [if_neg hc2] at hn
        omega
    · have b1' : Balanced (applyEffects st ((redraw dy C.id C.drawn (cutOut s e C.spans)).2 ++ [])) := by
        rw [List.append_nil]; exact b1
      refine ⟨b1', fun d i => ?_⟩
      have hm1 := m1 d i
      have hd := hh d i
      have h0 : netMin s e C = 0 := by omega
      show (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min - netMin s e C else 0) + X d i ≤
        unk (applyEffects st ((redraw dy C.id C.drawn (cutOut s e C.spans)).2 ++ [])) d i
      rw [List.append_nil, h0, Nat.sub_zero]
      omega

/-- **Netting the held closed blocks keeps the balance and their credits standing** (the owner's D100), by `netOne` in
order, over whatever else stands for the days (`X`). -/
theorem netAll_conserves (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) :
    ∀ (L : List Closed) (st : State) (X : Nat → Id → Nat), Balanced st →
      (∀ d i, ((L.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i ≤ unk st d i) →
      Balanced (applyEffects st (L.map (fun C => (netOne dy s e dd C).2.1)).flatten) ∧
        ∀ d i, (((L.map (fun C => (netOne dy s e dd C).1)).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i ≤
          unk (applyEffects st (L.map (fun C => (netOne dy s e dd C).2.1)).flatten) d i
  | [], st, X, hb, hh => ⟨hb, hh⟩
  | C :: L, st, X, hb, hh => by
    simp only [List.map_cons, List.flatten_cons]
    rw [applyEffects_append]
    have h1 := netOne_conserves dy s e dd C st (fun d i => ((L.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i) hb
      (fun d i => by have := hh d i; rw [heldOf_cons] at this; omega)
    obtain ⟨g1, g2⟩ := netAll_conserves dy s e dd L _
      (fun d i => (if (netOne dy s e dd C).1.ci = none ∧ (netOne dy s e dd C).1.credDay = d ∧
        (netOne dy s e dd C).1.id = i then (netOne dy s e dd C).1.min else 0) + X d i) h1.1
      (fun d i => by have := h1.2 d i; omega)
    refine ⟨g1, fun d i => ?_⟩
    rw [heldOf_cons]
    have := g2 d i
    omega

/-- **A late break's netting keeps the invariant** (the owner's D100): after the safe effects of settling the open block,
the held closed blocks netted (`netClosed`) stand for no more than the days hold, and the last cut is still the first
held, taken down by what its block lost. -/
theorem netOne_keeps (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (C : Closed) :
    (netOne dy s e dd C).1.id = C.id ∧ (netOne dy s e dd C).1.credDay = C.credDay ∧ (netOne dy s e dd C).1.ci = C.ci ∧
      (netOne dy s e dd C).1.min = C.min - (netOne dy s e dd C).2.2 := by
  unfold netOne; split
  · simp
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem conserves_netClosed (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (st : State) (m : Machine)
    (hb : Balanced st) (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ unk st d i) (ho : HeadOk m) :
    Conserves (applyEffects st ((netClosed dy s e dd m).2 ++ [.machine (netClosed dy s e dd m).1])) := by
  rw [applyEffects_append]
  obtain ⟨g1, g2⟩ := netAll_conserves dy s e dd m.closed st (fun _ _ => 0) hb (fun d i => by have := hh d i; omega)
  refine ⟨?_, fun d i => ?_, fun c hc => ?_⟩
  · show Balanced (applyEffects st (m.closed.map (fun C => (netOne dy s e dd C).2.1)).flatten)
    exact g1
  · have := g2 d i
    show (((m.closed.map (fun C => (netOne dy s e dd C).1)).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk (applyEffects st (m.closed.map (fun C => (netOne dy s e dd C).2.1)).flatten) d i
    omega
  · change (netClosed dy s e dd m).1.lastCut = some c at hc
    show ∃ C rest, (netClosed dy s e dd m).1.closed = C :: rest ∧ C.id = c.id ∧ C.credDay = c.day ∧ C.ci = none ∧
      C.min = c.min
    rcases hlc : m.lastCut with _ | c0
    · simp [netClosed, hlc] at hc
    · obtain ⟨C, rest, hcl, hid, hday, hci, hmin⟩ := ho c0 hlc
      simp only [netClosed, hlc, hcl, Option.some.injEq] at hc
      subst hc
      obtain ⟨k1, k2, k3, k4⟩ := netOne_keeps dy s e dd C
      refine ⟨(netOne dy s e dd C).1, rest.map (fun C => (netOne dy s e dd C).1), ?_, ?_, ?_, ?_, ?_⟩
      · show m.closed.map (fun C => (netOne dy s e dd C).1) = _
        rw [hcl]; rfl
      · rw [k1]; exact hid
      · rw [k2]; exact hday
      · rw [k3]; exact hci
      · rw [k4, hmin]

/-- **A netting keeps every balance and leaves the held credits it nets on their days** (the owner's D100, read
before a machine is written): `netAll_conserves` over the held blocks, with nothing beside them. -/
theorem netClosed_conserves (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (st : State) (m : Machine)
    (hb : Balanced st)
    (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) :
    Balanced (applyEffects st (netClosed dy s e dd m).2) ∧
      ∀ d i, (((netClosed dy s e dd m).1.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map
        (·.min)).sum ≤ unk (applyEffects st (netClosed dy s e dd m).2) d i := by
  obtain ⟨g1, g2⟩ := netAll_conserves dy s e dd m.closed st (fun _ _ => 0) hb (fun d i => by have := hh d i; omega)
  exact ⟨g1, fun d i => by have := g2 d i; simp only [Nat.add_zero] at this; exact this⟩

/-- `netAll_conserves` with a span for each block (the owner's D115: a late `start` nets each block over its own span). -/
theorem netEachAll_conserves (dy : Cal.Instant → Nat) (t : At) (dd : Nat) :
    ∀ (L : List Closed) (st : State) (X : Nat → Id → Nat), Balanced st →
      (∀ d i, ((L.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i ≤ unk st d i) →
      Balanced (applyEffects st (L.map (fun C => (netOne dy t (startEnd t C) dd C).2.1)).flatten) ∧
        ∀ d i, (((L.map (fun C => (netOne dy t (startEnd t C) dd C).1)).filter
          (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i ≤
          unk (applyEffects st (L.map (fun C => (netOne dy t (startEnd t C) dd C).2.1)).flatten) d i
  | [], st, X, hb, hh => ⟨hb, hh⟩
  | C :: L, st, X, hb, hh => by
    simp only [List.map_cons, List.flatten_cons]
    rw [applyEffects_append]
    have h1 := netOne_conserves dy t (startEnd t C) dd C st
      (fun d i => ((L.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i) hb
      (fun d i => by have := hh d i; rw [heldOf_cons] at this; omega)
    obtain ⟨g1, g2⟩ := netEachAll_conserves dy t dd L _
      (fun d i => (if (netOne dy t (startEnd t C) dd C).1.ci = none ∧ (netOne dy t (startEnd t C) dd C).1.credDay = d ∧
        (netOne dy t (startEnd t C) dd C).1.id = i then (netOne dy t (startEnd t C) dd C).1.min else 0) + X d i) h1.1
      (fun d i => by have := h1.2 d i; omega)
    refine ⟨g1, fun d i => ?_⟩
    rw [heldOf_cons]
    have := g2 d i
    omega

/-- **A late start's cut keeps every balance and leaves the held credits it cuts on their days** (the owner's D115). -/
theorem netStart_conserves (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (st : State) (m : Machine)
    (hb : Balanced st)
    (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) :
    Balanced (applyEffects st (netStart dy t dd m).2) ∧
      ∀ d i, (((netStart dy t dd m).1.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map
        (·.min)).sum ≤ unk (applyEffects st (netStart dy t dd m).2) d i := by
  obtain ⟨g1, g2⟩ := netEachAll_conserves dy t dd m.closed st (fun _ _ => 0) hb (fun d i => by have := hh d i; omega)
  exact ⟨g1, fun d i => by have := g2 d i; simp only [Nat.add_zero] at this; exact this⟩

/-- **The held credits are read off a block's id, its credit's day and ci, and its minutes alone** (D137): two maps of
the held blocks that agree on those four stand for the same minutes. -/
theorem heldOf_map_congr (f g : Closed → Closed)
    (h : ∀ C, (f C).ci = (g C).ci ∧ (f C).credDay = (g C).credDay ∧ (f C).id = (g C).id ∧ (f C).min = (g C).min) :
    ∀ (l : List Closed) (d : Nat) (i : Id),
      (((l.map f).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum =
      (((l.map g).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum
  | [], _, _ => rfl
  | C :: l, d, i => by
    simp only [List.map_cons]
    rw [heldOf_cons, heldOf_cons, heldOf_map_congr f g h l d i]
    obtain ⟨h1, h2, h3, h4⟩ := h C
    rw [h1, h2, h3, h4]

/-- **The running break's netting keeps every balance and leaves the held credits it nets on their days** (README gap
5180): `netClosed_conserves`, or nothing. -/
theorem runNet_conserves (dy : Cal.Instant → Nat) (st : State) (m : Machine) (hb : Balanced st)
    (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) :
    Balanced (applyEffects st (runNet dy m).2) ∧
      ∀ d i, (((runNet dy m).1.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map
        (·.min)).sum ≤ unk (applyEffects st (runNet dy m).2) d i := by
  rcases runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h]; exact ⟨hb, hh⟩
  · rw [h]
    obtain ⟨g1, g2⟩ := netClosed_conserves dy o.s (runTo o.s m.closed) o.day st m hb hh
    refine ⟨g1, fun d i => ?_⟩
    have := g2 d i
    show (((m.closed.map (runOne dy o.s (runTo o.s m.closed) o.day)).filter
      (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤ _
    rw [heldOf_map_congr (runOne dy o.s (runTo o.s m.closed) o.day) (fun C => (netOne dy o.s (runTo o.s m.closed) o.day C).1)
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩)]
    exact this

/-- **A netting leaves the last cut its first held block** (D100's `HeadOk`). -/
theorem netClosed_headOk (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) (ho : HeadOk m) :
    HeadOk (netClosed dy s e dd m).1 := by
  intro c hc
  change (netClosed dy s e dd m).1.lastCut = some c at hc
  rcases hlc : m.lastCut with _ | c0
  · simp [netClosed, hlc] at hc
  · obtain ⟨C, rest, hcl, hid, hday, hci, hmin⟩ := ho c0 hlc
    simp only [netClosed, hlc, hcl, Option.some.injEq] at hc
    subst hc
    obtain ⟨k1, k2, k3, k4⟩ := netOne_keeps dy s e dd C
    refine ⟨(netOne dy s e dd C).1, rest.map (fun C => (netOne dy s e dd C).1), ?_, ?_, ?_, ?_, ?_⟩
    · show m.closed.map (fun C => (netOne dy s e dd C).1) = _
      rw [hcl]; rfl
    · rw [k1]; exact hid
    · rw [k2]; exact hday
    · rw [k3]; exact hci
    · rw [k4, hmin]

/-- **The running break's netting leaves the last cut its first held block** (README gap 5180; D100's `HeadOk`). -/
theorem runNet_headOk (dy : Cal.Instant → Nat) (m : Machine) (ho : HeadOk m) : HeadOk (runNet dy m).1 := by
  rcases runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h]; exact ho
  · rw [h]
    intro c hc
    obtain ⟨C, rest, hcl, k⟩ := netClosed_headOk dy o.s (runTo o.s m.closed) o.day m ho c hc
    cases hm : m.closed with
    | nil => simp [netClosed, hm] at hcl
    | cons C0 l =>
      simp only [netClosed, hm, List.map_cons, List.cons.injEq] at hcl
      obtain ⟨rfl, rfl⟩ := hcl
      exact ⟨_, _, rfl, k⟩

/-- **The running break's netting, then its machine, keep the invariant** (README gap 5180). -/
theorem conserves_runNet (dy : Cal.Instant → Nat) (st : State) (m : Machine) (hb : Balanced st)
    (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) (ho : HeadOk m) :
    Conserves (applyEffects st ((runNet dy m).2 ++ [.machine (runNet dy m).1])) := by
  rw [applyEffects_append]
  obtain ⟨g1, g2⟩ := runNet_conserves dy st m hb hh
  exact ⟨g1, g2, runNet_headOk dy m ho⟩

/-- **A start that ends a running break forgets what the running break took, and nothing else of its credits** (D137:
`endMachine` clears `Closed.ran` and `Closed.ranMin`, which the held credits do not read). -/
theorem endMachine_held (m : Machine) (o : OpenBrk) (t : At) (d : Nat) (i : Id) :
    (((endMachine m o t).closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum =
      ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum := by
  show (((m.closed.map (fun C => { C with ran := [], ranMin := 0 })).filter _).map _).sum = _
  rw [heldOf_map_congr (fun C => { C with ran := [], ranMin := 0 }) id (fun _ => ⟨rfl, rfl, rfl, rfl⟩), List.map_id]

/-! ### D137: what the running break took, given back (README gaps 5504 and 5302, W-51 track K, parity P134) -/

/-- **One held closed block's give-back keeps the balance and its credits standing** (D137): its re-drawing is safe, and
what it gives back to a cut's credit (`ranMin`, ci-unknown minutes) it gives back to that day's ci-unknown minutes too. -/
theorem giveOne_conserves (dy : Cal.Instant → Nat) (C : Closed) (st : State) (X : Nat → Id → Nat) (hb : Balanced st)
    (hh : ∀ d i, (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min else 0) + X d i ≤ unk st d i) :
    Balanced (applyEffects st (giveOne dy C).2.1) ∧
      ∀ d i, (if (giveOne dy C).1.ci = none ∧ (giveOne dy C).1.credDay = d ∧ (giveOne dy C).1.id = i
          then (giveOne dy C).1.min else 0) + X d i ≤ unk (applyEffects st (giveOne dy C).2.1) d i := by
  unfold giveOne
  split
  · exact ⟨hb, hh⟩
  · obtain ⟨b1, m1, -⟩ := safe_list (redraw dy C.id C.drawn C.restored).2
      (all_safe_of_plain _ (redraw_plain dy _ _ _)) st hb
    split
    · rw [show ∀ (R : List Effect) (a b c e : Effect), R ++ [a, b, c, e] = R ++ [a] ++ [b, c, e] from
        fun _ _ _ _ _ => by simp, applyEffects_append, applyEffects_append]
      generalize hs0e : applyEffects st (redraw dy C.id C.drawn C.restored).2 = s0 at b1 m1 ⊢
      obtain ⟨b2, m2, -⟩ := safe_list [Effect.dayAdd C.credDay (.credit C.id C.ranMin C.ci)] (by simp [Effect.safe]) s0 b1
      generalize hs1e : applyEffects s0 [Effect.dayAdd C.credDay (.credit C.id C.ranMin C.ci)] = s1 at b2 m2 ⊢
      obtain ⟨b3, m3, -⟩ := safe_list [Effect.dayAdd C.credDay (.undur C.durLine C.ranMin),
        .itemAdd C.id (.credit C.ranMin), .itemDay C.id C.credDay C.ranMin] (by simp [Effect.safe]) s1 b2
      refine ⟨b3, fun d i => ?_⟩
      have hd := hh d i
      have h1 := m1 d i
      have h2 := m2 d i
      have h3 := m3 d i
      show (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min + C.ranMin else 0) + X d i ≤ _
      by_cases hc : C.ci = none ∧ C.credDay = d ∧ C.id = i
      · obtain ⟨hci, rfl, rfl⟩ := hc
        rw [if_pos ⟨hci, rfl, rfl⟩] at hd ⊢
        have he : unk s1 C.credDay C.id = unk s0 C.credDay C.id + C.ranMin := by
          rw [← hs1e]
          show unk (applyEffect s0 (.dayAdd C.credDay (.credit C.id C.ranMin C.ci))) C.credDay C.id = _
          rw [hci]
          exact unk_credit_none_eq s0 C.credDay C.id C.ranMin
        have h3' := m3 C.credDay C.id
        have h1' := m1 C.credDay C.id
        omega
      · rw [if_neg hc] at hd ⊢
        omega
    · rename_i hpos
      rw [List.append_nil]
      refine ⟨b1, fun d i => ?_⟩
      have hd := hh d i
      have h1 := m1 d i
      have h0 : C.ranMin = 0 := by omega
      show (if C.ci = none ∧ C.credDay = d ∧ C.id = i then C.min + C.ranMin else 0) + X d i ≤ _
      rw [h0, Nat.add_zero]
      exact Nat.le_trans hd h1

/-- **Giving every held closed block back keeps the balance and their credits standing** (D137), by `giveOne` in order,
over whatever else stands for the days (`X`). -/
theorem giveAll_conserves (dy : Cal.Instant → Nat) :
    ∀ (L : List Closed) (st : State) (X : Nat → Id → Nat), Balanced st →
      (∀ d i, ((L.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i ≤ unk st d i) →
      Balanced (applyEffects st (L.map (fun C => (giveOne dy C).2.1)).flatten) ∧
        ∀ d i, (((L.map (fun C => (giveOne dy C).1)).filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i ≤
          unk (applyEffects st (L.map (fun C => (giveOne dy C).2.1)).flatten) d i
  | [], st, X, hb, hh => ⟨hb, hh⟩
  | C :: L, st, X, hb, hh => by
    simp only [List.map_cons, List.flatten_cons]
    rw [applyEffects_append]
    have h1 := giveOne_conserves dy C st (fun d i => ((L.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum + X d i) hb
      (fun d i => by have := hh d i; rw [heldOf_cons] at this; omega)
    obtain ⟨g1, g2⟩ := giveAll_conserves dy L _
      (fun d i => (if (giveOne dy C).1.ci = none ∧ (giveOne dy C).1.credDay = d ∧
        (giveOne dy C).1.id = i then (giveOne dy C).1.min else 0) + X d i) h1.1
      (fun d i => by have := h1.2 d i; omega)
    refine ⟨g1, fun d i => ?_⟩
    rw [heldOf_cons]
    have := g2 d i
    omega

/-- **A give-back keeps every balance and leaves the held credits it raises on their days** (D137). -/
theorem giveBack_conserves (dy : Cal.Instant → Nat) (st : State) (m : Machine) (hb : Balanced st)
    (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) :
    Balanced (applyEffects st (giveBack dy m).2) ∧
      ∀ d i, (((giveBack dy m).1.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map
        (·.min)).sum ≤ unk (applyEffects st (giveBack dy m).2) d i := by
  obtain ⟨g1, g2⟩ := giveAll_conserves dy m.closed st (fun _ _ => 0) hb (fun d i => by have := hh d i; omega)
  exact ⟨g1, fun d i => by have := g2 d i; simp only [Nat.add_zero] at this; exact this⟩

/-- **A give-back leaves the last cut its first held block** (D100's `HeadOk`), raised by what that block got back. -/
theorem giveBack_headOk (dy : Cal.Instant → Nat) (m : Machine) (ho : HeadOk m) : HeadOk (giveBack dy m).1 := by
  intro c hc
  change (giveBack dy m).1.lastCut = some c at hc
  rcases hlc : m.lastCut with _ | c0
  · simp [giveBack, hlc] at hc
  · obtain ⟨C, rest, hcl, hid, hday, hci, hmin⟩ := ho c0 hlc
    simp only [giveBack, hlc, hcl, Option.some.injEq] at hc
    subst hc
    obtain ⟨k1, k2, k3, k4, -⟩ := giveOne_keeps dy C
    refine ⟨(giveOne dy C).1, rest.map (fun C => (giveOne dy C).1), ?_, ?_, ?_, ?_, ?_⟩
    · show m.closed.map (fun C => (giveOne dy C).1) = _
      rw [hcl]; rfl
    · rw [k1]; exact hid
    · rw [k2]; exact hday
    · rw [k3]; exact hci
    · rw [k4, hmin]

/-- **An effect that is not a machine never reads the machine** (README gap 5180): applying it under another machine is
applying it, then writing that machine. -/
theorem applyEffect_machine_comm (st : State) (m : Machine) (x : Effect) (h : x.machineOf? = none) :
    applyEffect { st with machine := m } x = { applyEffect st x with machine := m } := by
  cases x with
  | itemDaySub i d k =>
    unfold applyEffect
    cases hg : st.items.get i <;> simp [hg]
  | obs o => cases o <;> rfl
  | machine _ => simp [Effect.machineOf?] at h
  | _ => rfl

theorem applyEffects_machine_comm (m : Machine) : ∀ (fx : List Effect) (st : State),
    fx.filterMap Effect.machineOf? = [] →
      applyEffects { st with machine := m } fx = { applyEffects st fx with machine := m }
  | [], _, _ => rfl
  | x :: fx, st, h => by
    have hx : x.machineOf? = none := by
      cases hx : x.machineOf? with
      | none => rfl
      | some _ => simp [hx] at h
    have hfx : fx.filterMap Effect.machineOf? = [] := by simpa [List.filterMap_cons, hx] using h
    rw [applyEffects_cons, applyEffects_cons, applyEffect_machine_comm st m x hx]
    exact applyEffects_machine_comm m fx _ hfx

/-- **A `done`'s effects keep the invariant** (README gap 5180): the closing half (`conserves_doneClosed`) and its safe
credits, under the machine `doneClosed` leaves; then the running break's netting of it (`conserves_runNet`).  `doneFx`
writes the netted machine first — no other effect it writes reads or writes the machine (`applyEffects_machine_comm`). -/
theorem conserves_doneFx (dy : Cal.Instant → Nat) (st : State) (line : Nat) (t : At) (d : Nat) (id : Id)
    (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool) (h : Conserves st) :
    Conserves (applyEffects st (doneFx dy st.machine line t d id est actual went tags ci isPartial)) := by
  generalize hM : ({ (doneClose dy st.machine t id actual went).1 with
    closed := doneClosed dy st.machine line t id actual ci } : Machine) = M
  generalize hX : (if 0 < actual then
      [Effect.itemAdd id .block, .dayAdd d .blockDone,
        .obs (.duration ⟨line, t, d, id, ci, tags, est, actual, went, isPartial⟩)]
     else []) = X
  generalize hY : (if isPartial then [Effect.itemAdd id (.partialDoneAt t)]
     else [.itemAdd id (.doneAt t), .dayAdd d (.done id)]) = Y
  have e : doneFx dy st.machine line t d id est actual went tags ci isPartial =
      .machine (runNet dy M).1 :: ((doneClose dy st.machine t id actual went).2 ++ creditFx dy id t actual (some ci) ++ X ++ Y ++
        (runNet dy M).2) := by
    rw [← hM, ← hX, ← hY]; rfl
  have hXs : ∀ x ∈ creditFx dy id t actual (some ci) ++ X ++ Y, x.safe = true := by
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · exact safe_of_plain x (creditFx_plain dy _ t _ _ x hx)
    · rw [← hX] at hx
      split at hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> rfl
      · simp at hx
    · rw [← hY] at hx
      split at hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        subst hx; rfl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
  have hRm : ((doneClose dy st.machine t id actual went).2 ++ creditFx dy id t actual (some ci) ++ X ++ Y ++
      (runNet dy M).2).filterMap Effect.machineOf? = [] := by
    apply List.filterMap_eq_nil_iff.2
    intro x hx
    simp only [List.mem_append] at hx
    rcases hx with (((hx | hx) | hx) | hx) | hx
    · exact doneClose_noMachine dy _ t id actual went x hx
    · exact noMachine_of_safe x (hXs x (by simp [hx]))
    · exact noMachine_of_safe x (hXs x (by simp [hx]))
    · exact noMachine_of_safe x (hXs x (by simp [hx]))
    · exact runNet_noMachine dy M x hx
  rw [e, applyEffects_cons]
  have hS : applyEffect st (.machine (runNet dy M).1) =
      { applyEffect st (.machine M) with machine := (runNet dy M).1 } := rfl
  rw [hS, applyEffects_machine_comm _ _ _ hRm, applyEffects_append]
  have h1 := conserves_doneClosed dy st line t id actual went ci h
  rw [hM] at h1
  have h2 := conserves_safe _ _ hXs h1
  rw [← applyEffects_append] at h2
  have hm : (applyEffects (applyEffect st (.machine M))
      ((doneClose dy st.machine t id actual went).2 ++ (creditFx dy id t actual (some ci) ++ X ++ Y))).machine = M := by
    show (applyEffects { st with machine := M } _).machine = M
    rw [applyEffects_machine_comm _ _ _ (List.filterMap_eq_nil_iff.2 (fun x hx => by
      simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · exact doneClose_noMachine dy _ t id actual went x hx
      · exact noMachine_of_safe x (hXs x (by rcases hx with (h | h) | h <;> simp [h]))))]
  have h21 := h2.2.1
  have h22 := h2.2.2
  rw [hm] at h21 h22
  have h3 := conserves_runNet dy _ M h2.1 h21 h22
  rw [applyEffects_append] at h3
  simp only [List.append_assoc] at h3 ⊢
  exact h3

/-- **A break ended at a start writes safe effects** (D129): a segment and a record. -/
theorem endRecs_safe (o : OpenBrk) (t : At) : ∀ x ∈ endRecs o t, x.safe = true := by
  intro x hx; unfold endRecs at hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

/-- **A `break`'s block family half keeps the invariant** (D87, D100), over any machine holding the state's closed
blocks and a last cut that is its first held. -/
theorem conserves_brkFx (dy : Cal.Instant → Nat) (st : State) (m : Machine) (hc : m.closed = st.machine.closed)
    (hl : HeadOk m) (t e : At) (d : Nat) (h : Conserves st) : Conserves (applyEffects st (brkFx dy m t e d)) := by
  unfold brkFx
  rw [List.append_assoc, applyEffects_append]
  apply conserves_netClosed
  · exact (safe_list _ (all_safe_of_plain _ (settle_plain dy _)) st h.1).1
  · intro d' i'
    rw [settle_closed]
    dsimp only
    rw [hc]
    exact Nat.le_trans (h.2.1 d' i') ((safe_list _ (all_safe_of_plain _ (settle_plain dy _)) st h.1).2.1 d' i')
  · intro c hc'
    rw [(settle_keeps dy _).1] at hc'
    rw [settle_closed]
    exact hl c hc'

/-- **`brkFx` keeps the invariant over any machine whose held credits the days hold** (D137: the `break` line nets the
machine its give-back leaves, whose held blocks are not the state's): `conserves_brkFx`, with its machine's held
credits and `HeadOk` stated of the machine itself. -/
theorem conserves_brkFx_of (dy : Cal.Instant → Nat) (st : State) (m : Machine) (hb : Balanced st)
    (hh : ∀ d i, ((m.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i)
    (hl : HeadOk m) (t e : At) (d : Nat) : Conserves (applyEffects st (brkFx dy m t e d)) := by
  unfold brkFx
  rw [List.append_assoc, applyEffects_append]
  apply conserves_netClosed
  · exact (safe_list _ (all_safe_of_plain _ (settle_plain dy _)) st hb).1
  · intro d' i'
    rw [settle_closed]
    dsimp only
    exact Nat.le_trans (hh d' i') ((safe_list _ (all_safe_of_plain _ (settle_plain dy _)) st hb).2.1 d' i')
  · intro c hc'
    rw [(settle_keeps dy _).1] at hc'
    rw [settle_closed]
    exact hl c hc'

/-- **Ending a running break keeps the invariant** (D129): `brkFx`'s, then a segment and a record, both safe. -/
theorem conserves_endBrkFx (dy : Cal.Instant → Nat) (st : State) (o : OpenBrk) (t : At) (h : Conserves st) :
    Conserves (applyEffects st (endBrkFx dy st.machine o t)) := by
  unfold endBrkFx endRecs
  rw [applyEffects_append]
  refine conserves_safe _ _ ?_ (conserves_brkFx dy st { st.machine with brkEnded := some o.s } rfl h.2.2 o.s t o.day h)
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

/-- **A start's arm keeps the invariant** (C3, D99, D100, D115). -/
theorem conserves_startArm (dy : Cal.Instant → Nat) (st : State) (M : Machine) (line : Nat) (t : At) (d : Nat) (id : Id)
    (pred : U8) (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) (hb : Balanced st)
    (hh : ∀ d i, ((M.closed.filter (fun C => decide (C.ci = none ∧ C.credDay = d ∧ C.id = i))).map (·.min)).sum ≤
      unk st d i) :
    Conserves (applyEffects st (startArm dy M line t d id pred rep hsw sleptMin loc)) := by
  unfold startArm
  rw [show ∀ (a b c d f g : List Effect), a ++ b ++ c ++ d ++ f ++ g = a ++ (b ++ (c ++ ((d ++ f) ++ g))) by simp,
    applyEffects_append, applyEffects_append, applyEffects_append]
  obtain ⟨n1, n2⟩ := netStart_conserves dy t d st M hb hh
  obtain ⟨c1, c2, -⟩ := conserves_cut_of dy _ _ t n1 n2
  obtain ⟨r1, r2⟩ := runNet_conserves dy _ _ c1 c2
  refine conserves_after _ _ _ r1 ?_ (fun d' i' => ?_) (fun c hc => ?_)
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · simp only [List.mem_singleton] at hx; subst hx; rfl
    · exact safe_of_plain x (settle_plain dy _ x hx)
  · rw [settle_closed]
    exact r2 d' i'
  · rw [(settle_keeps dy _).1] at hc
    simp [startedMachine] at hc

/-- **A `break_start`'s arm, as D105 has it, keeps the invariant** (README gap 5180). -/
theorem conserves_brkStartArm (dy : Cal.Instant → Nat) (st : State) (t : At) (d : Nat) (planned : Nat)
    (where_ : Option (List Char)) (h : Conserves st) :
    Conserves (applyEffects st (brkStartArm dy st.machine t d planned where_)) := by
  unfold brkStartArm
  rw [List.append_assoc, applyEffects_append]
  apply conserves_runNet
  · exact (safe_list _ (all_safe_of_plain _ (settle_plain dy _)) st h.1).1
  · intro d' i'
    rw [settle_closed]
    exact Nat.le_trans (h.2.1 d' i') ((safe_list _ (all_safe_of_plain _ (settle_plain dy _)) st h.1).2.1 d' i')
  · intro c hc
    rw [(settle_keeps dy _).1] at hc
    rw [settle_closed]
    exact h.2.2 c hc

/-- **Each arm keeps the invariant.** -/
theorem conserves_arm (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) (t : At) (d : Nat)
    (h : Conserves st) : Conserves (applyEffects st (arm dy sl st.machine e t d)) := by
  unfold arm
  cases hev : e.ev <;> simp only
  case start =>
    split
    · rw [applyEffects_append]
      obtain ⟨g1, g2, -⟩ := safe_list _ (endRecs_safe _ t) st h.1
      exact conserves_startArm dy _ _ _ t d _ _ _ _ _ _ g1
        (fun d' i' => by rw [endMachine_held]; exact Nat.le_trans (h.2.1 d' i') (g2 d' i'))
    · exact conserves_startArm dy st _ _ t d _ _ _ _ _ _ h.1 h.2.1
  case pause =>
    split
    · split
      · exact conserves_safe_then_kept st _ _ (all_safe_of_plain _ (settle_plain _ _))
          (settle_closed dy _) (settle_keeps dy _).1 h
      · exact h
    · exact h
  case unpause =>
    split
    · split
      · refine conserves_safe_then_kept st _ _ ?_ ?_ ?_ h
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact safe_of_plain x (closePause_plain dy _ t x hx)
          · exact safe_of_plain x (settle_plain dy _ x hx)
        · rw [settle_closed]; exact closePauseM_closed _ _
        · rw [(settle_keeps dy _).1]; exact (closePause_lastCut dy st.machine t).1
      · exact h
    · exact h
  case interrupt =>
    refine conserves_safe_then_kept st _ _ ?_ ?_ ?_ h
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact safe_of_plain x (closePause_plain dy _ t x hx)
      · exact safe_of_plain x (settle_plain dy _ x hx)
    · rw [settle_closed]; exact (interruptMachine_closed _ _ _ _).1
    · rw [(settle_keeps dy _).1]; exact (interruptMachine_closed _ _ _ _).2
  case resume =>
    split
    · rw [show ∀ (a b c f : List Effect), a ++ b ++ c ++ f = (a ++ b) ++ (c ++ f) by simp, applyEffects_append]
      apply conserves_netClosed
      · refine (safe_list _ (fun x hx => ?_) st h.1).1
        rcases List.mem_append.1 hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> rfl
        · exact safe_of_plain x (settle_plain dy _ x hx)
      · intro d' i'
        rw [settle_closed]
        refine Nat.le_trans (h.2.1 d' i') ((safe_list _ (fun x hx => ?_) st h.1).2.1 d' i')
        rcases List.mem_append.1 hx with hx | hx
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> rfl
        · exact safe_of_plain x (settle_plain dy _ x hx)
      · intro c hc
        rw [(settle_keeps dy _).1] at hc
        rw [settle_closed]
        exact h.2.2 c hc
    · refine conserves_safe_then_kept st _ _ ?_ (by rw [settle_closed]) (settle_keeps dy _).1 h
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> rfl
      · exact safe_of_plain x (settle_plain dy _ x hx)
  case stop i rem =>
    split
    · split
      · obtain ⟨c1, c2, c3⟩ := conserves_cut dy st t h
        obtain ⟨r1, r2⟩ := runNet_conserves dy _ (cut dy st.machine t).1 c1 c2
        rw [show ∀ (a b : List Effect) (x y : Effect), a ++ b ++ [x, y] = ((a ++ b) ++ [x]) ++ [y] by simp]
        rw [applyEffects_append, applyEffects_append, applyEffects_append]
        have hs1 := safe_list [Effect.itemAdd i .stop] (by simp [Effect.safe]) _ r1
        exact ⟨hs1.1, fun d' i' => Nat.le_trans (r2 d' i') (hs1.2.1 _ _),
          runNet_headOk dy _ (cut_headOk dy st.machine t h.2.2)⟩
      · exact h
    · exact h
  case extend id by_ =>
    -- D108: the item's write, then — when the open block is the item's — one machine, its last cut and closed blocks
    -- untouched.
    unfold extendFx
    split
    · split
      · exact conserves_safe_then_kept st [.itemAdd id (.extend by_.val)] _ (by simp [Effect.safe]) rfl rfl h
      · exact conserves_safe st _ (by simp [Effect.safe]) h
    · exact conserves_safe st _ (by simp [Effect.safe]) h
  case done id est actual went tags ci isPartial =>
    exact conserves_doneFx dy st e.line t d id est.val actual.val went tags ci isPartial h
  case brk planned actual where_ =>
    have hb : Conserves (applyEffects st (brkArm dy sl st.machine e t d planned.val (actual.map (·.val)))) := by
      unfold brkArm
      rw [applyEffects_append]
      refine conserves_safe _ _ (fun x hx => List.all_eq_true.1 (dayArm_safe dy sl _ t d) x hx) ?_
      rw [applyEffects_append]
      obtain ⟨g1, g2⟩ := giveBack_conserves dy st st.machine h.1 h.2.1
      exact conserves_brkFx_of dy _ _ g1 g2 (giveBack_headOk dy _ h.2.2) t _ d
    split
    · split
      · exact conserves_safe_then_kept st [] _ (by simp) rfl rfl h
      · exact hb
    · exact hb
  case brkStart planned where_ =>
    split
    · rename_i t0 _
      exact conserves_endBrkFx dy st ⟨t, planned.val, where_, d⟩ t0 h
    · exact conserves_brkStartArm dy st t d _ _ h
  all_goals exact conserves_safe st _ (fun x hx => List.all_eq_true.1 (dayArm_safe dy sl e t d) x hx) h

/-- **C4: the completion family's effects are safe**: they touch no day, no machine and no item. -/
theorem completionCore_safe (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ completionCore z e t d, x.safe = true := by
  intro x hx
  unfold completionCore at hx
  cases hev : e.ev <;> simp only [hev] at hx
  case done =>
    split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  case routine =>
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | hx | hx
    · split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; rfl
    · subst hx; rfl
    · split at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
  case skip =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; rfl
  case named =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; rfl
  all_goals simp at hx

theorem completionArm_safe (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ completionArm z m e t d, x.safe = true := by
  intro x hx
  unfold completionArm at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x hx; rfl
  · exact completionCore_safe z e t d x hx

theorem conserves_init (n : Nat) : Conserves (State.init n) := by
  refine ⟨fun d a h => ?_, fun d i => ?_, fun c hc => ?_⟩
  · simp [State.init, HMap.get_empty] at h
  · simp [State.init]
  · simp [State.init] at hc

theorem conserves_step (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) (h : Conserves st) : Conserves (stepWith z dy sl st e) := by
  unfold stepWith effectsWith
  rw [applyEffects_cons, applyEffects_cons, applyEffects_cons, applyEffects_append]
  have h2 : Conserves (applyEffect (applyEffect (applyEffect st (.header (dy e.t.val) (HeaderRec.of e false)))
      (.global (e.t.val, e.off.val))) (.seam (dy e.t.val) ⟨(e.t.val, e.off.val), seamKindOf e.ev⟩)) :=
    conserves_safe st [.header _ _, .global _, .seam _ _] (by simp [Effect.safe]) h
  exact conserves_safe _ _ (completionArm_safe z _ e _ _) (conserves_arm dy sl _ e _ _ h2)

theorem conserves_foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (es : List Entry) (st : State), Conserves st → Conserves (es.foldl (stepWith z dy sl) st)
  | [], _, h => h
  | e :: es, st, h => conserves_foldl z dy sl es _ (conserves_step z dy sl st e h)

/-- **Credit conserves the day's minutes** (§8.2, Goals): on every day of every replay, the minutes of
known ci and the minutes of unknown ci add up to the day's block minutes, the stop-then-done
replacement and the removal of emptied ci-unknown entries included. -/
theorem credit_conserves_the_day_minutes (z : Cal.Tz) (es : List Entry) (d : Nat) :
    sumByCi (replay z es) d + sumCiUnknown (replay z es) d = blockMin (replay z es) d := by
  have h := conserves_foldl z (dayOf z (dayIndexOf z es)) (slOf z es) (survivors es) _ (conserves_init es.length)
  rw [replay_state]
  unfold sumByCi sumCiUnknown blockMin finish ciSum
  simp only
  rw [HMap.get_mapVals]
  cases hg : ((survivors es).foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) (State.init es.length)).days.get d with
  | none => rfl
  | some a => exact (h.1 d a hg).1

end Conservation

/-! ### Site R9: a day's load is exact fifths -/

section Fifths

open Log (Id U8 U32 Num)

/-- The fifths a day's ci minutes weigh: each minute at ci `i` counts `i`. -/
def Ci6.fifths (c : Ci6) : Nat := c.c1 + 2 * c.c2 + 3 * c.c3 + 4 * c.c4 + 5 * c.c5

theorem Ci6.fifths_sub (c : Ci6) (j m : Nat) (h : j ≤ 5) (hm : m ≤ c.get j) :
    (c.sub j m).fifths + m * j = c.fifths := by
  match j, h with
  | 0, _ => simp only [Ci6.sub, Ci6.fifths]; omega
  | 1, _ => simp only [Ci6.get] at hm; simp only [Ci6.sub, Ci6.fifths]; omega
  | 2, _ => simp only [Ci6.get] at hm; simp only [Ci6.sub, Ci6.fifths]; omega
  | 3, _ => simp only [Ci6.get] at hm; simp only [Ci6.sub, Ci6.fifths]; omega
  | 4, _ => simp only [Ci6.get] at hm; simp only [Ci6.sub, Ci6.fifths]; omega
  | 5, _ => simp only [Ci6.get] at hm; simp only [Ci6.sub, Ci6.fifths]; omega
  | n + 6, h => omega

theorem Ci6.fifths_ge (c : Ci6) (j : Nat) (h : j ≤ 5) : c.get j * j ≤ c.fifths := by
  match j, h with
  | 0, _ => simp only [Ci6.get, Ci6.fifths]; omega
  | 1, _ => simp only [Ci6.get, Ci6.fifths]; omega
  | 2, _ => simp only [Ci6.get, Ci6.fifths]; omega
  | 3, _ => simp only [Ci6.get, Ci6.fifths]; omega
  | 4, _ => simp only [Ci6.get, Ci6.fifths]; omega
  | 5, _ => simp only [Ci6.get, Ci6.fifths]; omega
  | n + 6, h => omega

theorem Ci6.fifths_add (c : Ci6) (j m : Nat) (h : j ≤ 5) : (c.add j m).fifths = c.fifths + m * j := by
  match j, h with
  | 0, _ => simp [Ci6.add, Ci6.fifths]
  | 1, _ => simp [Ci6.add, Ci6.fifths]; omega
  | 2, _ => simp [Ci6.add, Ci6.fifths]; omega
  | 3, _ => simp [Ci6.add, Ci6.fifths]; omega
  | 4, _ => simp [Ci6.add, Ci6.fifths]; omega
  | 5, _ => simp [Ci6.add, Ci6.fifths]; omega
  | n + 6, h => omega

/-- A day's load is its ci minutes, each weighed by its ci. -/
def DayAcc.Fifths (a : DayAcc) : Prop := a.loadFifths = a.byCi.fifths

theorem DayOp.fifths_apply (op : DayOp) (a : DayAcc) (ha : a.Fifths) : (op.apply a).Fifths := by
  unfold DayAcc.Fifths at *
  cases op with
  | credit id min ci =>
    cases ci with
    | some c =>
      have h2 := Ci6.fifths_add a.byCi (Nat.min c.val 5) min (Nat.min_le_right _ _)
      simp only [DayOp.apply]
      simp only [Nat.min_def] at h2 ⊢
      split <;> split at h2 <;> omega
    | none =>
      simp only [DayOp.apply]
      split <;> exact ha
  | wake t sl on => simp only [DayOp.apply]; split <;> exact ha
  | arrive t lc w bu => simp only [DayOp.apply]; split <;> exact ha
  | idle r => simp only [DayOp.apply]; split <;> exact ha
  | net id ci k line =>
    simp only [DayOp.apply]
    have hd : ∀ b : DayAcc, b.loadFifths = b.byCi.fifths → (DayAcc.netDurOf line k b).loadFifths =
        (DayAcc.netDurOf line k b).byCi.fifths := by
      intro b hb; unfold DayAcc.netDurOf; split
      · exact hb
      · exact hb
    apply hd
    unfold DayAcc.netCredit
    cases ci with
    | some c =>
      simp only
      have hj : Nat.min c.val 5 ≤ 5 := Nat.min_le_right _ _
      have hm := Nat.min_le_right k (a.byCi.get (Nat.min c.val 5))
      have h1 := Ci6.fifths_sub a.byCi (Nat.min c.val 5) (min k (a.byCi.get (Nat.min c.val 5))) hj hm
      have h2 := Ci6.fifths_ge a.byCi (Nat.min c.val 5) hj
      have h3 : min k (a.byCi.get (Nat.min c.val 5)) * Nat.min c.val 5 ≤
          a.byCi.get (Nat.min c.val 5) * Nat.min c.val 5 := Nat.mul_le_mul_right _ hm
      omega
    | none => exact ha
  | undur line k => simp only [DayOp.apply]; unfold DayAcc.undurOf; split <;> exact ha
  | _ => exact ha

theorem DayOp.fifths_alterFn (op : DayOp) (o : Option DayAcc) (ho : ∀ a, o = some a → a.Fifths) :
    ∀ a, op.alterFn o = some a → a.Fifths := by
  intro a h
  cases o with
  | some b =>
    simp only [DayOp.alterFn, Option.some.injEq] at h
    subst h; exact op.fifths_apply b (ho b rfl)
  | none =>
    cases op <;> simp only [DayOp.alterFn, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      exact DayOp.fifths_apply _ _ rfl

/-- Every day of a state weighs its load exactly. -/
def AllFifths (st : State) : Prop := ∀ d a, st.days.get d = some a → a.Fifths

theorem allFifths_apply (st : State) (e : Effect) (h : AllFifths st) : AllFifths (applyEffect st e) := by
  intro d a hd
  cases e with
  | dayAdd d' op =>
    simp only [applyEffect, HMap.get_alter] at hd
    split at hd
    · exact op.fifths_alterFn _ (h d') a hd
    · exact h d a hd
  | itemDaySub i d' m =>
    simp only [applyEffect] at hd
    split at hd <;> exact h d a hd
  | obs o => cases o <;> exact h d a hd
  | _ => exact h d a hd

theorem allFifths_foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (es : List Entry) (st : State), AllFifths st → AllFifths (es.foldl (stepWith z dy sl) st)
  | [], _, h => h
  | e :: es, st, h => by
    refine allFifths_foldl z dy sl es _ ?_
    unfold stepWith applyEffects
    generalize effectsWith z dy sl st e = fx
    induction fx generalizing st with
    | nil => exact h
    | cons x fx ih => exact ih _ (allFifths_apply st x h)

/-- **Site R9: a day's load is exact fifths** (§8.2): on every day of every replay, `load_fifths` is
the day's ci minutes, each minute weighed by its ci clamped to 5, so fork `DayReplay::load()` divides
one exact integer by 5 (P21), never an accumulated double.  The stop-then-done replacement takes back
only ci-unknown minutes, which weigh nothing. -/
theorem load_is_exact_fifths (z : Cal.Tz) (es : List Entry) (d : Nat) (a : DayAcc)
    (h : (replay z es).days.get d = some a) :
    a.loadFifths = a.byCi.c1 + 2 * a.byCi.c2 + 3 * a.byCi.c3 + 4 * a.byCi.c4 + 5 * a.byCi.c5 := by
  have hf := allFifths_foldl z (dayOf z (dayIndexOf z es)) (slOf z es) (survivors es) (State.init es.length)
    (fun d a h => by simp [State.init, HMap.get_empty] at h)
  rw [replay_state] at h
  unfold finish at h
  simp only at h
  rw [HMap.get_mapVals] at h
  cases hg : ((survivors es).foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) (State.init es.length)).days.get d with
  | none => simp [hg] at h
  | some b =>
    rw [hg] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact hf d b hg

end Fifths

/-! ### Site R8, and what an `extend` changes -/

section BlockLaws

open Log (Id U8 U32 Num)

/-- **Site R8 (quirk Q6c, gap 83), the law**: a cut credits the floor of **each piece's own** seconds over 60
(`num_minutes().max(0)` of its span), summed — so a block paused `k` times can lose up to `k` minutes against the floor
of its total (`worked_minutes_is_not_the_floor_of_the_block`).  Since the owner's D94 a block's pieces are cut around
the breaks its ledger days hold (README gap 4361, parity P92), and since the owner's D99 around its own idle spans
wherever the marks that wrote them were logged (gap 4520a, parity P104): `cutPieces`.  Where no span lies in the block
the one piece is its stretch (`worked_minutes_floor_each_subsegment_with_no_break_held`, R8's statement as C3 wrote
it), and over one the statement C3 wrote is refuted (`worked_minutes_floor_each_subsegment_as_c3_stated_it_is_refuted`).
Restated at W-47 from closeSub (deleted with D99: a block's credit is computed where it is cut). -/
theorem worked_minutes_floor_each_subsegment (dy : Cal.Instant → Nat) (m : Machine) (t : At) (b : Block)
    (hb : m.block = some b) :
    (cut dy m t).1.lastCut.map (·.min) =
      some (((cutPieces b m t).map (fun p => (Cal.secondsBetween p.1.1 p.2.1).toNat / 60)).sum) := by
  simp [cut, hb, minutesOf, Cal.minutesBetween]

/-- **The open block's minutes are its drawn pieces' floors** (site R8 over `settle`, the owner's D99). -/
theorem worked_minutes_of_the_open_block_floor_each_piece (dy : Cal.Instant → Nat) (m : Machine) (b : Block)
    (hb : m.block = some b) :
    (settle dy m).1.block.map (·.workedMin) =
      some (((openPieces b m).map (fun p => (Cal.secondsBetween p.1.1 p.2.1).toNat / 60)).sum) := by
  simp [settle, hb, minutesOf, Cal.minutesBetween]

/-- **R8 as C3 stated it is refuted** (the owner's D94): `a` started at 09:00 with a twenty-minute break at 09:30
held, cut at 10:00 — its two pieces credit 30 + 10 = 40 minutes, not the stretch's 60. -/
theorem worked_minutes_floor_each_subsegment_as_c3_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (m : Machine) (t : At) (b : Block), m.block = some b →
      (cut dy m t).1.lastCut.map (·.min) = some ((Cal.secondsBetween b.started.1 t.1).toNat / 60) := by
  intro h
  let b : Block := ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none, 0, none,
    739865, [], [], 0⟩
  let m : Machine := ⟨some b, none, none, [⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), (⟨63924371400, 0⟩, ⟨false, 0⟩), 739865⟩], none,
    [], none⟩
  have := h (fun _ => 739865) m (⟨63924372000, 0⟩, ⟨false, 0⟩) b rfl
  revert this
  decide

/-- **R8 as C3 stated it, where the block nets no span and its clock runs**: the one piece is the stretch from its
start — for every stretch an entry's instants can close (a closing stamp the decoder reads is a representable instant,
and a stretch that runs backwards has no minutes either way, `Cal.minutesBetween_zero_of_le`). -/
theorem worked_minutes_floor_each_subsegment_with_no_break_held (dy : Cal.Instant → Nat) (m : Machine) (t : At)
    (b : Block) (hb : m.block = some b) (h0 : blockSpans b m = []) (hrun : openStop b m = none)
    (hwf : t.1.wf = true) :
    (cut dy m t).1.lastCut.map (·.min) = some ((Cal.secondsBetween b.started.1 t.1).toNat / 60) := by
  rw [worked_minutes_floor_each_subsegment dy m t b hb]
  unfold cutPieces
  rw [h0, hrun]
  simp only [pieces, List.length_nil, piecesGo, lift, liftGo, List.any_nil, Bool.false_or]
  by_cases h : t.1 ≤ b.started.1
  · have h' : (Cal.secondsBetween b.started.1 t.1).toNat / 60 = 0 := Cal.minutesBetween_zero_of_le b.started.1 t.1 hwf h
    simp [h, h']
  · simp [h, nextStart]

/-- **What an `extend` writes to the machine, by key** (D108): nothing, or the machine alone. -/
theorem extendFx_keys (m : Machine) (id : Id) (by_ : Nat) :
    (extendFx m id by_).map Effect.key = [] ∨ (extendFx m id by_).map Effect.key = [.machine] := by
  unfold extendFx
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **What an `extend` leaves of the machine** (D108): nothing, when `extendFx` writes none; else the old machine with
its open block's `ext` grown, that block the extended item's.  Stated over `extendFx`'s own effects, not a second
definition of that machine: a proof-only `def` of it was emitted and reached by nothing (check 12, W-48 track A). -/
theorem applyEffects_extendFx (st : State) (id : Id) (by_ : Nat) :
    (extendFx st.machine id by_ = [] ∧ applyEffects st (extendFx st.machine id by_) = st) ∨
      ∃ b, st.machine.block = some b ∧ b.id = id ∧ applyEffects st (extendFx st.machine id by_) =
        { st with machine := { st.machine with block := some { b with ext := b.ext + by_ } } } := by
  unfold extendFx
  split
  · rename_i b hb
    split
    · rename_i hid
      exact Or.inr ⟨b, hb, hid, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- **An `extend` changes only the bookkeeping, its item's extended minutes and its open block's own** (the law under
the owner's D14, restated under **D108**, README gaps 4876 and 4893).  Its effects are its header (on its day), the
bookkeeping, one write to its item — the item's `extended_min` grows by `by_min` (the item created if absent, as fork
`item_mut` does) — and, when the open block is the item's, one write to the machine: that block's `ext` grows by the same
minutes (`extendFx_machines`).  By the frame law nothing at any other key moves. -/
theorem an_extend_changes_only_the_bookkeeping_its_extended_minutes_and_its_blocks (z : Cal.Tz) (kw : List Cal.Instant)
    (slept : List (Nat × Nat)) (st : State) (e : Entry) (id : Id) (by_ : U32) (h : e.ev = .extend id by_) :
    (effects z kw slept st e).map Effect.key
      = [.day (dayOf z kw e.t.val), .global, .day (dayOf z kw e.t.val), .item id] ++
          (extendFx st.machine id by_.val).map Effect.key ∧
    (step z kw slept st e).items.get id =
      some { (st.items.get id).getD ItemAcc.empty with
             extendedMin := ((st.items.get id).getD ItemAcc.empty).extendedMin + by_.val } ∧
    ((extendFx st.machine id by_.val = [] ∧ (step z kw slept st e).machine = st.machine) ∨
      ∃ b, st.machine.block = some b ∧ b.id = id ∧
        (step z kw slept st e).machine = { st.machine with block := some { b with ext := b.ext + by_.val } }) ∧
    ∀ k, k ∉ [Key.day (dayOf z kw e.t.val), .global, .item id, .machine] →
      (step z kw slept st e).valueAt k = st.valueAt k := by
  have hfx : effects z kw slept st e = [.header (dayOf z kw e.t.val) (HeaderRec.of e false),
      .global (e.t.val, e.off.val), .seam (dayOf z kw e.t.val) ⟨(e.t.val, e.off.val), .other⟩,
      .itemAdd id (.extend by_.val)] ++ extendFx st.machine id by_.val := by
    simp [effects, effectsWith, arm, completionArm, completionCore, lateWarnList, h, seamKindOf]
  let st1 := applyEffects st [.header (dayOf z kw e.t.val) (HeaderRec.of e false),
      .global (e.t.val, e.off.val), .seam (dayOf z kw e.t.val) ⟨(e.t.val, e.off.val), .other⟩,
      .itemAdd id (.extend by_.val)]
  have hstep : step z kw slept st e = applyEffects st1 (extendFx st1.machine id by_.val) := by
    unfold step; rw [hfx, applyEffects_append]; rfl
  have hitem : st1.items.get id = some { (st.items.get id).getD ItemAcc.empty with
      extendedMin := ((st.items.get id).getD ItemAcc.empty).extendedMin + by_.val } := by
    simp only [st1, applyEffects, List.foldl, applyEffect, HMap.get_alter, if_true]
    cases st.items.get id <;> rfl
  refine ⟨by rw [hfx]; simp [Effect.key], ?_, ?_, fun k hk => ?_⟩
  · rw [hstep]
    rcases applyEffects_extendFx st1 id by_.val with ⟨-, h1⟩ | ⟨b, -, -, h1⟩ <;> rw [h1] <;> exact hitem
  · rw [hstep]
    rcases applyEffects_extendFx st1 id by_.val with ⟨h0, h1⟩ | ⟨b, hb, hid, h1⟩
    · exact Or.inl ⟨h0, by rw [h1]; rfl⟩
    · exact Or.inr ⟨b, hb, hid, by rw [h1]; rfl⟩
  · unfold step
    apply applyEffects_touches_only_named_keys
    rw [hfx]
    simp only [List.map_append, List.mem_append, not_or] at hk ⊢
    simp only [List.map, Effect.key, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢
    refine ⟨⟨hk.1, hk.2.1, hk.1, hk.2.2.1⟩, fun hm => ?_⟩
    rcases extendFx_keys st.machine id by_.val with h0 | h0 <;> rw [h0] at hm
    · cases hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm; exact hk.2.2.2 hm

/-- **The D14 statement, on the logs where it still holds** (D108): with no open block of the extended item, an
`extend` writes no machine, and the law stands as D14 stated it. -/
theorem an_extend_changes_only_the_bookkeeping_and_its_extended_minutes_with_no_block_of_it_open (z : Cal.Tz)
    (kw : List Cal.Instant) (slept : List (Nat × Nat)) (st : State) (e : Entry) (id : Id) (by_ : U32)
    (h : e.ev = .extend id by_) (hb : ∀ b, st.machine.block = some b → b.id ≠ id) :
    (effects z kw slept st e).map Effect.key
      = [.day (dayOf z kw e.t.val), .global, .day (dayOf z kw e.t.val), .item id] ∧
    (step z kw slept st e).items.get id =
      some { (st.items.get id).getD ItemAcc.empty with
             extendedMin := ((st.items.get id).getD ItemAcc.empty).extendedMin + by_.val } ∧
    ∀ k, k ∉ [Key.day (dayOf z kw e.t.val), .global, .item id] →
      (step z kw slept st e).valueAt k = st.valueAt k := by
  have h0 : extendFx st.machine id by_.val = [] := by
    unfold extendFx
    split
    · rename_i b hbm
      rw [if_neg (hb b hbm)]
    · rfl
  obtain ⟨k1, k2, k3, k4⟩ := an_extend_changes_only_the_bookkeeping_its_extended_minutes_and_its_blocks z kw slept st e id
    by_ h
  rw [h0] at k1
  refine ⟨by simpa using k1, k2, fun k hk => ?_⟩
  by_cases hkm : k = .machine
  · subst hkm
    have hme : (step z kw slept st e).machine = st.machine := by
      rcases k3 with ⟨-, h3⟩ | ⟨b, hbm, hid, -⟩
      · exact h3
      · exact absurd hid (hb b hbm)
    show State.valueAt _ Key.machine = State.valueAt _ Key.machine
    simp only [State.valueAt, hme]
  · apply k4
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk ⊢
    exact ⟨hk.1, hk.2.1, hk.2.2, hkm⟩

end BlockLaws

/-! ### C4: the completion family — the last record in file order, the latest done by instant

Quirk Q6(b), ported faithfully: fork `instances[item][inst]` keeps the **last record in file order**
(`an_instance_is_its_last_record_in_file_order`), and fork `last_done` keeps the **latest by instant**, the
first of equal instants (`last_done_is_the_latest_by_instant`, `last_done_is_the_first_of_the_latest`).
On a retro append the two disagree (`instances_and_last_done_order_differently`).  Fork `LatestNamed`
keeps two instants per `(name, id?)` (carried note 3;
`named_keeps_the_latest_by_instant_and_the_latest_by_local_date`). -/

section CompletionLaws

open Log (Id U8 U32 Num)

theorem foldl_lastMaxStep_some {α : Type} (r : α → α → Bool) :
    ∀ (l : List α) (a : α), (l.foldl (lastMaxStep r) (some a)).isSome = true
  | [], _ => rfl
  | x :: l, a => foldl_lastMaxStep_some r l (pick r a x)

/-- A running maximum is `none` only on the empty list. -/
theorem lastMax?_eq_none_iff {α : Type} (r : α → α → Bool) (l : List α) : lastMax? r l = none ↔ l = [] := by
  cases l with
  | nil => simp [lastMax?]
  | cons x l =>
    constructor
    · intro h
      have hs := foldl_lastMaxStep_some r l x
      unfold lastMax? at h
      rw [List.foldl_cons] at h
      simp only [lastMaxStep] at h
      rw [h] at hs
      simp at hs
    · intro h; cases h

/-- The decomposition a running maximum keeps as it goes (`lastMax?_spec`'s invariant). -/
def MaxSplit {α : Type} (r : α → α → Bool) (p : List α) (b : α) : Prop :=
  ∃ l₁ l₂, p = l₁ ++ b :: l₂ ∧ (∀ x ∈ l₁, r x b = true) ∧ (∀ x ∈ l₂, r b x = false)

theorem maxSplit_step {α : Type} (r : α → α → Bool)
    (trans : ∀ a b c, r a b = true → r b c = true → r a c = true)
    (skip : ∀ a b c, r a b = false → r a c = true → r b c = true)
    (p : List α) (a x : α) (h : MaxSplit r p a) : MaxSplit r (p ++ [x]) (pick r a x) := by
  obtain ⟨l₁, l₂, hp, h1, h2⟩ := h
  unfold pick
  split
  · rename_i hax
    refine ⟨p, [], rfl, fun y hy => ?_, by simp⟩
    rw [hp] at hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy | rfl | hy
    · exact trans _ _ _ (h1 y hy) hax
    · exact hax
    · exact skip _ _ _ (h2 y hy) hax
  · rename_i hax
    refine ⟨l₁, l₂ ++ [x], by rw [hp]; simp, h1, fun y hy => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with hy | rfl
    · exact h2 y hy
    · simpa using hax

theorem maxSplit_foldl {α : Type} (r : α → α → Bool)
    (trans : ∀ a b c, r a b = true → r b c = true → r a c = true)
    (skip : ∀ a b c, r a b = false → r a c = true → r b c = true) :
    ∀ (l p : List α) (a b : α), MaxSplit r p a → l.foldl (lastMaxStep r) (some a) = some b →
      MaxSplit r (p ++ l) b
  | [], p, a, b, h, hf => by
    simp only [List.foldl_nil, Option.some.injEq] at hf
    subst hf; simpa using h
  | x :: l, p, a, b, h, hf => by
    rw [List.foldl_cons] at hf
    have := maxSplit_foldl r trans skip l (p ++ [x]) (pick r a x) b (maxSplit_step r trans skip p a x h) hf
    simpa using this

/-- **What a running maximum returns**: the list splits at it, every element before it is replaced by
it (`r x b`), and no element after it replaces it (`r b x = false`).  It needs `r` transitive, and a
candidate that does not replace `a` to be replaced by whatever replaces `a`. -/
theorem lastMax?_spec {α : Type} (r : α → α → Bool)
    (trans : ∀ a b c, r a b = true → r b c = true → r a c = true)
    (skip : ∀ a b c, r a b = false → r a c = true → r b c = true)
    (l : List α) (b : α) (h : lastMax? r l = some b) :
    ∃ l₁ l₂, l = l₁ ++ b :: l₂ ∧ (∀ x ∈ l₁, r x b = true) ∧ (∀ x ∈ l₂, r b x = false) := by
  cases l with
  | nil => simp [lastMax?] at h
  | cons x l =>
    unfold lastMax? at h
    rw [List.foldl_cons] at h
    exact maxSplit_foldl r trans skip l [x] x b ⟨[], [], rfl, by simp, by simp⟩ h

/-! #### `last_done` -/

theorem filterMap_cons_toList {α β : Type} (f : α → Option β) (x : α) (l : List α) :
    (x :: l).filterMap f = (f x).toList ++ l.filterMap f := by
  simp only [List.filterMap_cons]; cases f x <;> rfl

/-- An entry's stamp as the fork keeps it. -/
def stampOf (e : Entry) : At := (e.t.val, e.off.val)

/-- **Whether an entry completes `i`** (fork `mark_done`'s two callers): a non-partial `done` of `i`, or a
`routine` of `i` whose status reads `done`. -/
def completes (i : Id) (e : Entry) : Bool :=
  match e.ev with
  | .done id _ _ _ _ _ isPartial => decide (id = i) && !isPartial
  | .routine item _ status _ => decide (item = i) && decide (Log.parseInstanceStatus status = some .done)
  | _ => false

/-- **The stamps at which entries complete `i`**, in file order.  §15 gives it the zone, which a
completion's instant does not read; it is left out. -/
def doneInstants (i : Id) (es : List Entry) : List At := (es.filter (completes i)).map stampOf

/-- A completion effect's instant for `i`. -/
def Effect.markOf (i : Id) : Effect → Option At
  | .markDone j t => if j = i then some t else none
  | _ => none

theorem applyEffect_lastDone (st : State) (x : Effect) (i : Id) :
    (applyEffect st x).lastDone.get i
      = match x.markOf i with
        | some t => lastMaxStep instLt (st.lastDone.get i) t
        | none => st.lastDone.get i := by
  cases x with
  | markDone j t =>
    simp only [applyEffect, Effect.markOf, HMap.get_alter]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  | itemDaySub i' d m => simp only [applyEffect, Effect.markOf]; split <;> rfl
  | obs o => cases o <;> rfl
  | _ => rfl

theorem lastDone_applyEffects (st : State) (fx : List Effect) (i : Id) :
    (applyEffects st fx).lastDone.get i
      = (fx.filterMap (Effect.markOf i)).foldl (lastMaxStep instLt) (st.lastDone.get i) := by
  induction fx generalizing st with
  | nil => rfl
  | cons x fx ih =>
    rw [applyEffects_cons, ih, applyEffect_lastDone, List.filterMap_cons]
    cases hm : x.markOf i <;> rfl

theorem markOf_of_ofBlock (i : Id) (x : Effect) (h : x.ofBlock = true) : x.markOf i = none := by
  cases x <;> simp_all [Effect.ofBlock, Effect.markOf]

theorem arm_markOf (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) (i : Id) :
    (arm dy sl m e t d).filterMap (Effect.markOf i) = [] :=
  List.filterMap_eq_nil_iff.2 (fun x hx => markOf_of_ofBlock i x (arm_ofBlock dy sl m e t d x hx))

theorem completionCore_markOf (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) (i : Id) :
    (completionCore z e t d).filterMap (Effect.markOf i) = if completes i e then [t] else [] := by
  unfold completionCore completes
  cases e.ev <;> simp only [List.filterMap_nil, Bool.false_eq_true, if_false]
  case done id _ _ _ _ _ isPartial =>
    cases isPartial <;> by_cases h : id = i <;> simp [h, Effect.markOf]
  case routine item ins status actual =>
    rw [List.filterMap_append, List.filterMap_cons]
    have hw : (match Log.parseInstanceStatus status with
        | some _ => ([] : List Effect)
        | none => [.rwarn (.unknownInstanceStatus e.line status)]).filterMap (Effect.markOf i) = [] := by
      split <;> rfl
    rw [hw]
    by_cases hs : Log.parseInstanceStatus status = some .done <;> by_cases h : item = i <;>
      simp [hs, h, Effect.markOf]
  case skip => rfl
  case named => rfl

theorem completionArm_markOf (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) (i : Id) :
    (completionArm z m e t d).filterMap (Effect.markOf i) = if completes i e then [t] else [] := by
  unfold completionArm
  rw [List.filterMap_append, lateWarns_filterMap _ (fun _ => rfl), List.nil_append, completionCore_markOf]

theorem stepWith_lastDone (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) (i : Id) :
    (stepWith z dy sl st e).lastDone.get i
      = (if completes i e then [stampOf e] else []).foldl (lastMaxStep instLt) (st.lastDone.get i) := by
  unfold stepWith effectsWith
  rw [lastDone_applyEffects, List.filterMap_cons, List.filterMap_cons, List.filterMap_cons, List.filterMap_append, arm_markOf,
    completionArm_markOf]
  rfl

theorem foldl_stepWith_lastDone (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (i : Id) :
    ∀ (es : List Entry) (st : State),
      (es.foldl (stepWith z dy sl) st).lastDone.get i
        = (doneInstants i es).foldl (lastMaxStep instLt) (st.lastDone.get i)
  | [], _ => rfl
  | e :: es, st => by
    rw [List.foldl_cons, foldl_stepWith_lastDone z dy sl i es, stepWith_lastDone]
    unfold doneInstants
    rw [List.filter_cons]
    split <;> simp_all

/-- **`last_done` is the latest by instant** (§15, Goals; quirk Q6(b)): the running maximum by chrono's
order of the stamps at which the survivors complete the item, file order breaking no tie in favour of a
later line. -/
theorem last_done_is_the_latest_by_instant (z : Cal.Tz) (es : List Entry) (i : Id) :
    (replay z es).lastDone i = maxByInstant? (doneInstants i (survivors es)) := by
  rw [replay_state]
  unfold Facts.lastDone finish maxByInstant? lastMax?
  simp only
  rw [foldl_stepWith_lastDone, State.init, HMap.get_empty]

theorem instLt_trans (a b c : At) (h₁ : instLt a b = true) (h₂ : instLt b c = true) : instLt a c = true := by
  simp only [instLt, decide_eq_true_eq] at *; exact Cal.Instant.lt_trans h₁ h₂

theorem instLt_skip (a b c : At) (h₁ : instLt a b = false) (h₂ : instLt a c = true) : instLt b c = true := by
  simp only [instLt, decide_eq_true_eq, decide_eq_false_iff_not, Cal.Instant.lt_iff] at *; omega

/-- **What `last_done` is**: the first of the latest completions by instant.  Every completion logged
before it is strictly earlier, and none logged after it is later. -/
theorem last_done_is_the_first_of_the_latest (z : Cal.Tz) (es : List Entry) (i : Id) (b : At)
    (h : (replay z es).lastDone i = some b) :
    ∃ l₁ l₂, doneInstants i (survivors es) = l₁ ++ b :: l₂ ∧ (∀ x ∈ l₁, x.1 < b.1) ∧ (∀ x ∈ l₂, ¬ b.1 < x.1) := by
  rw [last_done_is_the_latest_by_instant] at h
  obtain ⟨l₁, l₂, he, h1, h2⟩ := lastMax?_spec instLt instLt_trans instLt_skip _ b h
  exact ⟨l₁, l₂, he, fun x hx => by simpa [instLt] using h1 x hx, fun x hx => by simpa [instLt] using h2 x hx⟩

/-- An item has a `last_done` exactly when some survivor completes it (fork `done_items`). -/
theorem last_done_isSome_iff (z : Cal.Tz) (es : List Entry) (i : Id) :
    ((replay z es).lastDone i).isSome = true ↔ ∃ e ∈ survivors es, completes i e = true := by
  rw [last_done_is_the_latest_by_instant, maxByInstant?, Option.isSome_iff_ne_none, ne_eq,
    lastMax?_eq_none_iff]
  unfold doneInstants
  simp [List.filter_eq_nil_iff]

/-! #### Instances -/

/-- **The record an entry writes to `(item, inst)`** (§15's `instRecordOf`): fork `routine` (an unknown
status read as `Pending`, the status kept as logged) or `skip` (`Skipped`, logged `"skipped"`). -/
def instRecordOf (item ins : List Char) (e : Entry) : Option InstRec :=
  match e.ev with
  | .routine it is status actual =>
    if it = item ∧ is = ins then
      some ⟨stampOf e, (Log.parseInstanceStatus status).getD .pending, status, actual.map (·.val)⟩
    else none
  | .skip it is => if it = item ∧ is = ins then some ⟨stampOf e, .skipped, "skipped".toList, none⟩ else none
  | _ => none

/-- An instance effect's record for `(item, inst)`. -/
def Effect.instOf (item ins : List Char) : Effect → Option InstRec
  | .inst it is r => if it = item ∧ is = ins then some r else none
  | _ => none

theorem applyEffect_instances (st : State) (x : Effect) (item ins : List Char) :
    (applyEffect st x).instances.get (item, ins) = (x.instOf item ins).or (st.instances.get (item, ins)) := by
  cases x with
  | inst it is r =>
    simp only [applyEffect, Effect.instOf, HMap.get_alter, Prod.mk.injEq]
    by_cases h : it = item ∧ is = ins
    · obtain ⟨rfl, rfl⟩ := h; simp
    · have h' : ¬ (item = it ∧ ins = is) := fun ⟨a, b⟩ => h ⟨a.symm, b.symm⟩
      simp [h, h']
  | itemDaySub i' d m => simp only [applyEffect, Effect.instOf]; split <;> rfl
  | obs o => cases o <;> rfl
  | _ => rfl

theorem instances_applyEffects (st : State) (fx : List Effect) (item ins : List Char) :
    (applyEffects st fx).instances.get (item, ins)
      = (fx.reverse.findSome? (Effect.instOf item ins)).or (st.instances.get (item, ins)) := by
  induction fx generalizing st with
  | nil => rfl
  | cons x fx ih =>
    rw [applyEffects_cons, ih, applyEffect_instances, List.reverse_cons, List.findSome?_append,
      Option.or_assoc]
    congr 1
    simp only [List.findSome?_cons, List.findSome?_nil]
    cases x.instOf item ins <;> rfl

theorem instOf_of_ofBlock (item ins : List Char) (x : Effect) (h : x.ofBlock = true) : x.instOf item ins = none := by
  cases x <;> simp_all [Effect.ofBlock, Effect.instOf]

/-- **A late mark's warnings record no instance** (D116, D119): the completion family's instance is its core's. -/
theorem completionArm_instOf (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) (item ins : List Char) :
    (completionArm z m e t d).reverse.findSome? (Effect.instOf item ins) =
      (completionCore z e t d).reverse.findSome? (Effect.instOf item ins) := by
  have hL : ((lateWarnList m e d).map Effect.rwarn).reverse.findSome? (Effect.instOf item ins) = none :=
    List.findSome?_eq_none_iff.2 (fun x hx => by
      obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x (List.mem_reverse.1 hx); rfl)
  unfold completionArm
  rw [List.reverse_append, List.findSome?_append, hL, Option.or_none]

theorem stepWith_instances (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) (item ins : List Char) :
    (stepWith z dy sl st e).instances.get (item, ins) = (instRecordOf item ins e).or (st.instances.get (item, ins)) := by
  unfold stepWith effectsWith
  rw [instances_applyEffects]
  congr 1
  simp only [List.reverse_cons, List.reverse_append, List.findSome?_append]
  have ha : (arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).reverse.findSome? (Effect.instOf item ins) = none :=
    List.findSome?_eq_none_iff.2 (fun x hx => instOf_of_ofBlock item ins x
      (arm_ofBlock _ _ _ _ _ _ x (List.mem_reverse.1 hx)))
  rw [ha]
  simp only [List.findSome?_cons, List.findSome?_nil, Effect.instOf, Option.or_none]
  rw [completionArm_instOf]
  unfold completionCore instRecordOf stampOf
  cases e.ev <;> simp only [List.reverse_nil, List.findSome?_nil]
  case done id _ _ _ _ _ isPartial => cases isPartial <;> rfl
  case routine it is status actual =>
    simp only [List.reverse_append, List.reverse_cons, List.findSome?_append, List.append_assoc]
    have hm : (if Log.parseInstanceStatus status = some .done then
        [Effect.markDone it (e.t.val, e.off.val), .doneDate it ((Log.instDate? is).getD (dy e.t.val))]
        else []).reverse.findSome? (Effect.instOf item ins) = none := by
      split <;> rfl
    rw [hm]
    have hw : (match Log.parseInstanceStatus status with
        | some _ => ([] : List Effect)
        | none => [.rwarn (.unknownInstanceStatus e.line status)]).reverse.findSome? (Effect.instOf item ins) = none := by
      split <;> rfl
    simp only [List.findSome?_cons, List.findSome?_nil, Effect.instOf, hw]
    by_cases h : it = item ∧ is = ins <;> simp [h]
  case skip it is =>
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.findSome?_cons, List.findSome?_nil,
      Effect.instOf]
    by_cases h : it = item ∧ is = ins <;> simp [h]
  case named => rfl

theorem foldl_stepWith_instances (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat)
    (item ins : List Char) : ∀ (es : List Entry) (st : State),
      (es.foldl (stepWith z dy sl) st).instances.get (item, ins)
        = (es.reverse.findSome? (instRecordOf item ins)).or (st.instances.get (item, ins))
  | [], _ => rfl
  | e :: es, st => by
    rw [List.foldl_cons, foldl_stepWith_instances z dy sl item ins es, stepWith_instances,
      List.reverse_cons, List.findSome?_append, Option.or_assoc]
    congr 1
    simp only [List.findSome?_cons, List.findSome?_nil]
    cases instRecordOf item ins e <;> rfl

/-- **An instance is its last record in file order** (§15, Goals; quirk Q6(b)): fork `instances[item][inst]`
is overwritten by every surviving `routine` or `skip` of that instance, so it holds the last one logged,
whatever its stamp. -/
theorem an_instance_is_its_last_record_in_file_order (z : Cal.Tz) (es : List Entry) (item ins : List Char) :
    (replay z es).instance item ins = (survivors es).reverse.findSome? (instRecordOf item ins) := by
  rw [replay_state]
  unfold Facts.instance finish
  simp only
  rw [foldl_stepWith_instances, State.init, HMap.get_empty, Option.or_none]

/-! #### `LatestNamed` -/

/-- The occurrences of `tm event name` addressed to `id?` (fork `events[name]` filtered to that key), in
file order: each one's line, stamp and local date in the zone. -/
def namedOccurrences (z : Cal.Tz) (name : List Char) (id : Option Id) (es : List Entry) : List (Nat × At × Nat) :=
  es.filterMap (fun e =>
    match e.ev with
    | .named n i => if n = name ∧ i = id then some (e.line, stampOf e, Cal.localDate z e.t.val) else none
    | _ => none)

def Effect.namedOf (name : List Char) (id : Option Id) : Effect → Option (Nat × At × Nat)
  | .named n i line t date => if n = name ∧ i = id then some (line, t, date) else none
  | _ => none

/-- One occurrence folded into a key's record. -/
def pushStep (o : Option NamedRec) (x : Nat × At × Nat) : Option NamedRec := some (NamedRec.push o x.1 x.2.1 x.2.2)

theorem applyEffect_named (st : State) (x : Effect) (name : List Char) (id : Option Id) :
    (applyEffect st x).named.get (name, id)
      = match x.namedOf name id with
        | some o => pushStep (st.named.get (name, id)) o
        | none => st.named.get (name, id) := by
  cases x with
  | named n i line t date =>
    simp only [applyEffect, Effect.namedOf, HMap.get_alter, Prod.mk.injEq]
    by_cases h : n = name ∧ i = id
    · obtain ⟨rfl, rfl⟩ := h; simp [pushStep]
    · have h' : ¬ (name = n ∧ id = i) := fun ⟨a, b⟩ => h ⟨a.symm, b.symm⟩
      simp [h, h']
  | itemDaySub i' d m => simp only [applyEffect, Effect.namedOf]; split <;> rfl
  | obs o => cases o <;> rfl
  | _ => rfl

theorem named_applyEffects (st : State) (fx : List Effect) (name : List Char) (id : Option Id) :
    (applyEffects st fx).named.get (name, id)
      = (fx.filterMap (Effect.namedOf name id)).foldl pushStep (st.named.get (name, id)) := by
  induction fx generalizing st with
  | nil => rfl
  | cons x fx ih =>
    rw [applyEffects_cons, ih, applyEffect_named, List.filterMap_cons]
    cases x.namedOf name id <;> rfl

theorem completionCore_namedOf (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) (name : List Char) (id : Option Id) :
    (completionCore z e t d).filterMap (Effect.namedOf name id)
      = (match e.ev with
         | .named n i => if n = name ∧ i = id then some (e.line, t, Cal.localDate z t.1) else none
         | _ => none).toList := by
  unfold completionCore
  cases e.ev <;> try rfl
  case done _ _ _ _ _ _ p => cases p <;> rfl
  case routine it is status actual =>
    rw [List.filterMap_append, List.filterMap_cons]
    have hw : (match Log.parseInstanceStatus status with
        | some _ => ([] : List Effect)
        | none => [.rwarn (.unknownInstanceStatus e.line status)]).filterMap (Effect.namedOf name id) = [] := by
      split <;> rfl
    have hm : (if Log.parseInstanceStatus status = some .done then
        [Effect.markDone it t, .doneDate it ((Log.instDate? is).getD d)]
        else []).filterMap (Effect.namedOf name id) = [] := by
      split <;> rfl
    rw [hw, hm]; rfl

theorem completionArm_namedOf (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) (name : List Char)
    (id : Option Id) :
    (completionArm z m e t d).filterMap (Effect.namedOf name id)
      = (match e.ev with
         | .named n i => if n = name ∧ i = id then some (e.line, t, Cal.localDate z t.1) else none
         | _ => none).toList := by
  unfold completionArm
  rw [List.filterMap_append, lateWarns_filterMap _ (fun _ => rfl), List.nil_append, completionCore_namedOf]

theorem stepWith_named (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) (name : List Char) (id : Option Id) :
    (stepWith z dy sl st e).named.get (name, id)
      = (namedOccurrences z name id [e]).foldl pushStep (st.named.get (name, id)) := by
  unfold stepWith effectsWith
  rw [named_applyEffects, List.filterMap_cons, List.filterMap_cons, List.filterMap_cons, List.filterMap_append]
  have ha : (arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap (Effect.namedOf name id) = [] :=
    List.filterMap_eq_nil_iff.2 (fun x hx => by
      have := arm_ofBlock _ _ _ _ _ _ x hx
      cases x <;> simp_all [Effect.ofBlock, Effect.namedOf])
  rw [ha, completionArm_namedOf]
  unfold namedOccurrences stampOf
  simp only [Effect.namedOf, List.nil_append, List.filterMap_cons, List.filterMap_nil]
  cases (match e.ev with
    | .named n i => if n = name ∧ i = id then some (e.line, (e.t.val, e.off.val), Cal.localDate z e.t.val) else none
    | _ => none) <;> rfl

theorem foldl_stepWith_named (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat)
    (name : List Char) (id : Option Id) : ∀ (es : List Entry) (st : State),
      (es.foldl (stepWith z dy sl) st).named.get (name, id)
        = (namedOccurrences z name id es).foldl pushStep (st.named.get (name, id))
  | [], _ => rfl
  | e :: es, st => by
    rw [List.foldl_cons, foldl_stepWith_named z dy sl name id es, stepWith_named]
    have : namedOccurrences z name id (e :: es) = namedOccurrences z name id [e] ++ namedOccurrences z name id es := by
      unfold namedOccurrences
      rw [filterMap_cons_toList, filterMap_cons_toList, List.filterMap_nil, List.append_nil]
    rw [this, List.foldl_append]

theorem foldl_pushStep_latest : ∀ (l : List (Nat × At × Nat)) (o : Option NamedRec),
    (l.foldl pushStep o).map (·.latest) = (l.map (fun x => (x.1, x.2.1))).foldl (lastMaxStep latestRel) (o.map (·.latest))
  | [], _ => rfl
  | x :: l, o => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, foldl_pushStep_latest l]
    cases o <;> rfl

theorem foldl_pushStep_dated : ∀ (l : List (Nat × At × Nat)) (o : Option NamedRec),
    (l.foldl pushStep o).map (·.dated) = (l.map (fun x => (x.2.2, x.1, x.2.1))).foldl (lastMaxStep datedRel) (o.map (·.dated))
  | [], _ => rfl
  | x :: l, o => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, foldl_pushStep_dated l]
    cases o <;> rfl

/-- **Fork `LatestNamed` of every `(name, id?)` key** (carried note 3; R3's `latest_named`): the record keeps
the latest occurrence by instant, with its line, and the latest by local date in the zone and then by
instant, with its date and line, a later line winning a tie in both. -/
theorem named_keeps_the_latest_by_instant_and_the_latest_by_local_date (z : Cal.Tz) (es : List Entry)
    (name : List Char) (id : Option Id) :
    ((replay z es).namedAt name id).map (·.latest)
      = lastMax? latestRel ((namedOccurrences z name id (survivors es)).map (fun x => (x.1, x.2.1))) ∧
    ((replay z es).namedAt name id).map (·.dated)
      = lastMax? datedRel ((namedOccurrences z name id (survivors es)).map (fun x => (x.2.2, x.1, x.2.1))) := by
  rw [replay_state]
  unfold Facts.namedAt finish lastMax?
  simp only
  rw [foldl_stepWith_named, State.init, HMap.get_empty]
  exact ⟨foldl_pushStep_latest _ none, foldl_pushStep_dated _ none⟩

/-! #### Replay warnings and done dates -/

theorem applyEffect_ofBlock_keeps (s : State) (x : Effect) (h : x.ofBlock = true) :
    (applyEffect s x).rwarns = s.rwarns ∧ (applyEffect s x).doneDates = s.doneDates := by
  cases x with
  | itemDaySub i d m => simp only [applyEffect]; split <;> exact ⟨rfl, rfl⟩
  | obs o => cases o <;> exact ⟨rfl, rfl⟩
  | rwarn w => simp [Effect.ofBlock] at h
  | doneDate i d => simp [Effect.ofBlock] at h
  | _ => exact ⟨rfl, rfl⟩

/-- The replay warning an entry raises: a `routine` whose status the fork does not know. -/
def warnOf (e : Entry) : Option RWarn :=
  match e.ev with
  | .routine _ _ status _ =>
    match Log.parseInstanceStatus status with
    | some _ => none
    | none => some (.unknownInstanceStatus e.line status)
  | _ => none

theorem completionCore_rwarns (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) (s : State) :
    (applyEffects s (completionCore z e t d)).rwarns = (warnOf e).toList ++ s.rwarns := by
  unfold completionCore warnOf
  cases e.ev <;> try rfl
  case done _ _ _ _ _ _ p => cases p <;> rfl
  case routine it is status actual =>
    rw [applyEffects_append]
    cases hs : Log.parseInstanceStatus status with
    | none => simp [applyEffects, applyEffect, hs]
    | some s' => cases s' <;> simp [applyEffects, applyEffect, hs]

/-- **A late mark's warnings, applied** (D116, D119): they push onto the state's warnings, newest first. -/
theorem applyEffects_lateWarns_rwarns (l : List RWarn) (s : State) :
    (applyEffects s (l.map Effect.rwarn)).rwarns = l.reverse ++ s.rwarns := by
  induction l generalizing s with
  | nil => rfl
  | cons w l ih => rw [List.map_cons, applyEffects_cons, ih]; simp [applyEffect]

/-- **What the completion family warns** — its own routine warning, after the late marks the machine names (stage 6
W-48 track K: D116, D119). -/
theorem completionArm_rwarns (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) (s : State) :
    (applyEffects s (completionArm z m e t d)).rwarns =
      (warnOf e).toList ++ ((lateWarnList m e d).reverse ++ s.rwarns) := by
  unfold completionArm
  rw [applyEffects_append, completionCore_rwarns, applyEffects_lateWarns_rwarns]

theorem stepWith_rwarns (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) : (stepWith z dy sl st e).rwarns =
      (warnOf e).toList ++ ((lateWarnList st.machine e (dy e.t.val)).reverse ++ st.rwarns) := by
  have hgen : ∀ (fx : List Effect) (s : State), (∀ x ∈ fx, x.ofBlock = true) →
      (applyEffects s fx).rwarns = s.rwarns := by
    intro fx
    induction fx with
    | nil => intro s _; rfl
    | cons x fx ih =>
      intro s hx
      rw [applyEffects_cons, ih _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))]
      exact (applyEffect_ofBlock_keeps s x (hx x (List.mem_cons_self ..))).1
  unfold stepWith effectsWith
  rw [applyEffects_cons, applyEffects_cons, applyEffects_cons, applyEffects_append, completionArm_rwarns,
    hgen _ _ (arm_ofBlock _ _ _ _ _ _)]
  rfl

/-- **The replay warnings that are fork `Replay.warnings`' own are the unknown routine statuses, in file order** (§8.3;
fork `Replay.warnings`, which only `routine` pushes).  **Restated at the owner's D116 and D119** (stage 6 W-48 track K):
the replay also names a `break` line whose word is not its `break_start`'s and a late mark past D100's bound
(`lateWarnList`), so the statement over every warning is refuted
(`the_replay_warnings_are_the_unknown_statuses_in_file_order_as_c4_stated_it_is_refuted`); the routine statuses are the
warnings `(fun w => match w with | RWarn.unknownInstanceStatus .. => true | _ => false)` reads, unchanged. -/
theorem the_replay_warnings_are_the_unknown_statuses_in_file_order (z : Cal.Tz) (es : List Entry) :
    (replay z es).warnings.filter (fun w => match w with | RWarn.unknownInstanceStatus .. => true | _ => false) = (survivors es).filterMap warnOf := by
  have hs : ∀ e, (warnOf e).toList.filter (fun w => match w with | RWarn.unknownInstanceStatus .. => true | _ => false) = (warnOf e).toList := by
    intro e; unfold warnOf; split
    · split <;> rfl
    · rfl
  have h : ∀ (l : List Entry) (st : State),
      (l.foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) st).rwarns.filter (fun w => match w with | RWarn.unknownInstanceStatus .. => true | _ => false) =
        (l.filterMap warnOf).reverse ++ st.rwarns.filter (fun w => match w with | RWarn.unknownInstanceStatus .. => true | _ => false) := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons e l ih =>
      intro st
      rw [List.foldl_cons, ih, stepWith_rwarns, List.filter_append, List.filter_append, hs, List.filter_reverse,
        lateWarnList_not_status, List.reverse_nil, List.nil_append, List.filterMap_cons]
      cases warnOf e <;> simp
  rw [replay_state]
  unfold finish
  simp only
  rw [List.filter_reverse, h, State.init]
  simp

/-- **The date a completion is recorded on** (fork `mark_done`'s `date`): a `done`'s day, or the date a
`routine`'s `inst` names, else its day. -/
def doneDateOf (dy : Cal.Instant → Nat) (e : Entry) : Nat :=
  match e.ev with
  | .routine _ ins _ _ => (Log.instDate? ins).getD (dy e.t.val)
  | _ => dy e.t.val

/-- A completion effect's date for `i`. -/
def Effect.dateOf (i : Id) : Effect → Option Nat
  | .doneDate j d => if j = i then some d else none
  | _ => none

theorem applyEffect_doneDates (s : State) (x : Effect) (i : Id) (d : Nat) :
    ((applyEffect s x).doneDates.get (d, i)).isSome
      = ((s.doneDates.get (d, i)).isSome || x.dateOf i == some d) := by
  cases x with
  | doneDate j dd =>
    simp only [applyEffect, Effect.dateOf, HMap.get_alter, Prod.mk.injEq]
    by_cases h1 : j = i <;> by_cases h2 : dd = d
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
    · simp [h1, Ne.symm h1]
    · simp [h1, Ne.symm h1]
  | itemDaySub i' d' m => simp only [applyEffect, Effect.dateOf]; split <;> simp
  | obs o => cases o <;> simp [applyEffect, Effect.dateOf]
  | _ => simp [applyEffect, Effect.dateOf]

theorem applyEffects_doneDates (s : State) (fx : List Effect) (i : Id) (d : Nat) :
    ((applyEffects s fx).doneDates.get (d, i)).isSome
      = ((s.doneDates.get (d, i)).isSome || fx.any (fun x => x.dateOf i == some d)) := by
  induction fx generalizing s with
  | nil => simp [applyEffects]
  | cons x fx ih => rw [applyEffects_cons, ih, applyEffect_doneDates, List.any_cons, Bool.or_assoc]

theorem completionCore_doneDates (z : Cal.Tz) (dy : Cal.Instant → Nat) (e : Entry) (t : At) (i : Id) (d : Nat) :
    (completionCore z e t (dy e.t.val)).any (fun x => x.dateOf i == some d)
      = (completes i e && decide (doneDateOf dy e = d)) := by
  unfold completionCore completes doneDateOf
  cases e.ev <;> try rfl
  case done id _ _ _ _ _ isPartial =>
    cases isPartial
    · by_cases h1 : id = i <;> by_cases h2 : dy e.t.val = d <;> simp [h1, h2, Effect.dateOf]
    · simp
  case routine it is status actual =>
    rw [List.any_append, List.any_cons]
    have hw : (match Log.parseInstanceStatus status with
        | some _ => ([] : List Effect)
        | none => [.rwarn (.unknownInstanceStatus e.line status)]).any (fun x => x.dateOf i == some d) = false := by
      split <;> rfl
    rw [hw]
    by_cases hs : Log.parseInstanceStatus status = some .done <;>
      by_cases h1 : it = i <;> by_cases h2 : (Log.instDate? is).getD (dy e.t.val) = d <;>
      simp [hs, h1, h2, Effect.dateOf]

theorem completionArm_doneDates (z : Cal.Tz) (dy : Cal.Instant → Nat) (m : Machine) (e : Entry) (t : At) (i : Id)
    (d : Nat) :
    (completionArm z m e t (dy e.t.val)).any (fun x => x.dateOf i == some d)
      = (completes i e && decide (doneDateOf dy e = d)) := by
  unfold completionArm
  rw [List.any_append, lateWarns_any _ (fun _ => rfl), Bool.false_or, completionCore_doneDates]

theorem stepWith_doneDates (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State)
    (e : Entry) (i : Id) (d : Nat) :
    ((stepWith z dy sl st e).doneDates.get (d, i)).isSome
      = ((st.doneDates.get (d, i)).isSome || (completes i e && decide (doneDateOf dy e = d))) := by
  unfold stepWith effectsWith
  rw [applyEffects_doneDates, List.any_cons, List.any_cons, List.any_cons, List.any_append, completionArm_doneDates]
  have ha : (arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)).any (fun x => x.dateOf i == some d) = false :=
    List.any_eq_false.2 (fun x hx => by
      have := arm_ofBlock _ _ _ _ _ _ x hx
      cases x <;> simp_all [Effect.ofBlock, Effect.dateOf])
  rw [ha]
  simp [Effect.dateOf]

/-- **A done date is recorded exactly when a survivor completes the item on that date** (fork
`done_dates`, which nothing but an undo removes from: a later `pending` does not). -/
theorem a_done_date_is_a_survivors_completion_date (z : Cal.Tz) (es : List Entry) (i : Id) (d : Nat) :
    (replay z es).doneOn i d = true ↔
      ∃ e ∈ survivors es, completes i e = true ∧ doneDateOf (dayOf z (dayIndexOf z es)) e = d := by
  have h : ∀ (l : List Entry) (st : State),
      ((l.foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) st).doneDates.get (d, i)).isSome
        = ((st.doneDates.get (d, i)).isSome ||
            l.any (fun e => completes i e && decide (doneDateOf (dayOf z (dayIndexOf z es)) e = d))) := by
    intro l
    induction l with
    | nil => intro st; simp
    | cons e l ih =>
      intro st
      rw [List.foldl_cons, ih, stepWith_doneDates, List.any_cons, Bool.or_assoc]
  rw [replay_state]
  unfold Facts.doneOn finish
  simp only
  rw [h, State.init, HMap.get_empty]
  simp

end CompletionLaws

/-! ### C5: the day header and records family

Fork `Machine::step`'s remaining arms (`dayArm`): the day header (`wake`, `arrive`, `loc`), the day's records
(`break`, `idle`, `routine`'s day half, `plan`), the energy event's observation, and the records outside a day
(`demote`, `drop`, `close`, the global longest leak, unknown events).  **Late binding**: an `energy` line reads
fork `slept_by_day`, built from every surviving wake before the walk, so a wake logged after it still counts
(`energy_obs_slept_is_the_days_first_logged_sleep`).  **The first leak maximum wins**
(`the_first_leak_maximum_wins`).  **A demotion's stamp is its `from` key's** (`a_demote_stamp_reads_the_week_or_date_key`),
and the demotions and closes are the survivors' in file order. -/

section DayLaws

open Log (Id U8 U32 Num)

/-! #### Late-bound sleep -/

/-- **An effect keeps late binding**: an energy observation that is not a start's reads `sl` on its own day,
and the machine's pending observation is a start's. -/
def Effect.sleptOk (sl : Nat → Option Nat) : Effect → Bool
  | .obs (.energy o) => o.fromStart || decide (o.sleptMin = sl o.day)
  | .machine m => (m.block.bind (·.obs)).all (·.fromStart)
  | _ => true

/-- **The late-binding invariant** of a state: every energy observation that is not a start's reads `sl` on
its day, and the open block's pending observation is a start's. -/
def SleptInv (sl : Nat → Option Nat) (st : State) : Prop :=
  (∀ o ∈ st.energy, o.fromStart = false → o.sleptMin = sl o.day) ∧
  (∀ o, st.machine.block.bind (·.obs) = some o → o.fromStart = true)

theorem sleptInv_apply (sl : Nat → Option Nat) (st : State) (x : Effect) (hx : x.sleptOk sl = true)
    (h : SleptInv sl st) : SleptInv sl (applyEffect st x) := by
  cases x with
  | obs o =>
    cases o with
    | energy o =>
      refine ⟨fun o' ho' hf => ?_, h.2⟩
      simp only [applyEffect, List.mem_cons] at ho'
      rcases ho' with rfl | ho'
      · simpa [Effect.sleptOk, hf] using hx
      · exact h.1 o' ho' hf
    | duration o => exact h
  | machine m =>
    refine ⟨h.1, fun o ho => ?_⟩
    simp only [applyEffect] at ho
    simp only [Effect.sleptOk, ho] at hx
    simpa using hx
  | itemDaySub i d m => simp only [applyEffect]; split <;> exact h
  | _ => exact h

theorem sleptInv_applyEffects (sl : Nat → Option Nat) : ∀ (fx : List Effect) (st : State),
    (∀ x ∈ fx, x.sleptOk sl = true) → SleptInv sl st → SleptInv sl (applyEffects st fx)
  | [], _, _, h => h
  | x :: fx, st, hx, h => sleptInv_applyEffects sl fx _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (sleptInv_apply sl st x (hx x (List.mem_cons_self ..)) h)

theorem closePauseM_pending (m : Machine) (t : At) :
    (closePauseM m t).block.bind (·.obs) = m.block.bind (·.obs) := by
  unfold closePauseM; repeat' split
  all_goals simp_all

theorem closePause_pending (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    (closePause dy m t).1.block.bind (·.obs) = m.block.bind (·.obs) := closePauseM_pending m t

theorem redraw_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (id : Id) (old : List Piece)
    (P : List (At × At)) : (redraw dy id old P).2.all (Effect.sleptOk sl) = true :=
  List.all_eq_true.2 (fun x hx => by
    unfold redraw at hx
    simp only [List.mem_append, List.mem_map] at hx
    rcases hx with ⟨p, -, rfl⟩ | ⟨q, -, rfl⟩ <;> rfl)

theorem settle_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) :
    (settle dy m).2.all (Effect.sleptOk sl) = true := by
  unfold settle; split
  · exact redraw_sleptOk sl dy _ _ _
  · rfl

theorem closePause_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    (closePause dy m t).2.all (Effect.sleptOk sl) = true := by
  unfold closePause; split <;> (repeat' split) <;> simp [Effect.sleptOk]

theorem creditFx_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (id : Id) (t : At) (min : Nat)
    (ci : Option U8) : (creditFx dy id t min ci).all (Effect.sleptOk sl) = true := by
  simp [creditFx, Effect.sleptOk]

theorem uncreditFx_sleptOk (sl : Nat → Option Nat) (c : Cut) : (uncreditFx c).all (Effect.sleptOk sl) = true := by
  unfold uncreditFx; split <;> simp [Effect.sleptOk]

theorem obsFx_sleptOk (sl : Nat → Option Nat) (o : Option EnergyObs) (h : ∀ o', o = some o' → o'.fromStart = true) :
    (obsFx o).all (Effect.sleptOk sl) = true := by
  cases o with
  | none => rfl
  | some o => simp [obsFx, Effect.sleptOk, h o rfl]

/-- **A late break's netting is late-binding safe** (the owner's D100): it observes nothing and writes no machine. -/
theorem netClosed_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) :
    (netClosed dy s e dd m).2.all (Effect.sleptOk sl) = true :=
  List.all_eq_true.2 (fun x hx => by
    obtain ⟨C, hC⟩ := netClosed_mem dy s e dd m x hx
    rcases netOne_mem dy s e dd C x hC with h | rfl | rfl | rfl
    · exact List.all_eq_true.1 (redraw_sleptOk sl dy _ _ _) x h
    · rfl
    · rfl
    · rfl)

/-- **A give-back observes nothing** (D137): `sleptOk` holds of every effect it writes. -/
theorem giveBack_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) :
    (giveBack dy m).2.all (Effect.sleptOk sl) = true :=
  List.all_eq_true.2 (fun x hx => by
    obtain ⟨C, hC⟩ := giveBack_mem dy m x hx
    rcases giveOne_mem dy C x hC with h | rfl | rfl | rfl | rfl
    · exact List.all_eq_true.1 (redraw_sleptOk sl dy _ _ _) x h
    all_goals rfl)

theorem netStart_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (m : Machine) :
    (netStart dy t dd m).2.all (Effect.sleptOk sl) = true :=
  List.all_eq_true.2 (fun x hx => by
    obtain ⟨C, hC⟩ := netStart_mem dy t dd m x hx
    rcases netOne_mem dy t _ dd C x hC with h | rfl | rfl | rfl
    · exact List.all_eq_true.1 (redraw_sleptOk sl dy _ _ _) x h
    · rfl
    · rfl
    · rfl)

theorem runNet_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) :
    (runNet dy m).2.all (Effect.sleptOk sl) = true := by
  rcases runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h]; rfl
  · rw [h]; exact netClosed_sleptOk sl dy _ _ _ m

theorem machine_sleptOk (sl : Nat → Option Nat) (m' m : Machine)
    (he : m'.block.bind (·.obs) = m.block.bind (·.obs))
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) : (Effect.machine m').sleptOk sl = true := by
  simp only [Effect.sleptOk, he]
  cases hb : m.block.bind (·.obs) with
  | none => rfl
  | some o => simpa using hm o hb

theorem cut_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (t : At)
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (cut dy m t).2.all (Effect.sleptOk sl) = true ∧ (cut dy m t).1.block = none := by
  unfold cut
  split
  · rename_i b hb
    refine ⟨?_, rfl⟩
    simp only [List.all_append, Bool.and_eq_true]
    refine ⟨⟨⟨redraw_sleptOk sl dy _ _ _, closePause_sleptOk sl dy _ t⟩, creditFx_sleptOk sl dy _ t _ _⟩,
      obsFx_sleptOk sl _ (fun o ho => hm o ?_)⟩
    rw [hb]; exact ho
  · rename_i hb
    exact ⟨rfl, hb⟩

theorem wentOn_fromStart (w : Option U8) (o : EnergyObs) : (wentOn w o).fromStart = o.fromStart := by
  cases w <;> rfl

theorem doneClose_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id)
    (actual : Nat) (went : Option U8) (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (doneClose dy m t id actual went).2.all (Effect.sleptOk sl) = true ∧
      (∀ o, (doneClose dy m t id actual went).1.block.bind (·.obs) = some o → o.fromStart = true) := by
  unfold doneClose
  split
  · rename_i b hb
    split
    · refine ⟨?_, fun o ho => by simp at ho⟩
      simp only [List.all_append, Bool.and_eq_true]
      refine ⟨⟨redraw_sleptOk sl dy _ _ _, closePause_sleptOk sl dy _ t⟩, obsFx_sleptOk sl _ (fun o ho => ?_)⟩
      cases hbo : b.obs with
      | none => rw [hbo] at ho; cases ho
      | some o0 =>
        rw [hbo] at ho
        simp only [Option.map_some, Option.some.injEq] at ho
        subst ho
        rw [wentOn_fromStart]
        exact hm o0 (by rw [hb]; exact hbo)
    · exact ⟨rfl, hm⟩
  · split
    · split
      · exact ⟨uncreditFx_sleptOk sl _, hm⟩
      · exact ⟨rfl, hm⟩
    · exact ⟨rfl, hm⟩

theorem doneFx_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At)
    (d : Nat) (id : Id) (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool)
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (doneFx dy m line t d id est actual went tags ci isPartial).all (Effect.sleptOk sl) = true := by
  obtain ⟨h1, h2⟩ := doneClose_sleptOk sl dy m t id actual went hm
  apply List.all_eq_true.2
  intro x hx
  unfold doneFx at hx
  simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | ((((hx | hx) | hx) | hx) | hx)
  · simp only [Effect.sleptOk]
    rw [(runNet_keeps dy _).1]
    cases hb : (doneClose dy m t id actual went).1.block.bind (·.obs) with
    | none => rfl
    | some o => simpa using h2 o hb
  · exact List.all_eq_true.1 h1 x hx
  · exact List.all_eq_true.1 (creditFx_sleptOk sl dy id t actual (some ci)) x hx
  · split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> rfl
    · simp at hx
  · split at hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
  · exact List.all_eq_true.1 (runNet_sleptOk sl dy _) x hx

/-- **C5: the day family's effects keep late binding**: its energy observation reads `sl` on its own day. -/
theorem dayArm_sleptOk (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat) :
    (dayArm dy sl e t d).all (Effect.sleptOk sl) = true := by
  unfold dayArm
  split <;> (repeat' split) <;> simp [Effect.sleptOk]

theorem completionCore_sleptOk (sl : Nat → Option Nat) (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) :
    (completionCore z e t d).all (Effect.sleptOk sl) = true := by
  unfold completionCore
  split <;> (repeat' split) <;> simp [Effect.sleptOk]

theorem completionArm_sleptOk (sl : Nat → Option Nat) (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    (completionArm z m e t d).all (Effect.sleptOk sl) = true := by
  unfold completionArm
  rw [List.all_append, lateWarns_all _ (fun _ => rfl), Bool.true_and, completionCore_sleptOk]

theorem resumeBlock_obs (b : Block) (span : Option (At × At)) (t : At) : (resumeBlock b span t).obs = b.obs := rfl

/-- **A `break`'s block family half keeps late binding** (D87): it moves no pending observation. -/
theorem brkFx_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat)
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (brkFx dy m t e d).all (Effect.sleptOk sl) = true := by
  unfold brkFx
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨settle_sleptOk sl dy _, netClosed_sleptOk sl dy _ _ _ _⟩,
    machine_sleptOk sl _ m (by rw [(netClosed_keeps dy _ _ _ _).1, settle_obs]) hm⟩

/-- **A break ended at a start keeps late binding** (D129): a segment and a record. -/
theorem endRecs_sleptOk (sl : Nat → Option Nat) (o : OpenBrk) (t : At) : (endRecs o t).all (Effect.sleptOk sl) = true :=
  rfl

/-- **Ending a running break keeps late binding** (D129). -/
theorem endBrkFx_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (o : OpenBrk) (t : At)
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (endBrkFx dy m o t).all (Effect.sleptOk sl) = true := by
  unfold endBrkFx endRecs
  rw [List.all_append, brkFx_sleptOk sl dy { m with brkEnded := some o.s } _ _ _ hm]
  simp [Effect.sleptOk]

/-- **A start's arm keeps late binding**, given the pending observation of the machine it starts from. -/
theorem startArm_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat)
    (id : Id) (pred : U8) (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char)
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (startArm dy m line t d id pred rep hsw sleptMin loc).all (Effect.sleptOk sl) = true := by
  unfold startArm
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨netStart_sleptOk sl dy _ _ _,
    (cut_sleptOk sl dy _ t (by rw [(netStart_keeps dy _ _ _).1]; exact hm)).1⟩, runNet_sleptOk sl dy _⟩, rfl⟩,
    settle_sleptOk sl dy _⟩, ?_⟩
  simp only [Effect.sleptOk, settle_obs, startedMachine, Option.bind_some]
  cases rep <;> simp

/-- **A `break_start`'s arm, as D105 has it, keeps late binding.** -/
theorem brkStartArm_sleptOk (sl : Nat → Option Nat) (dy : Cal.Instant → Nat) (m : Machine) (t : At) (d : Nat)
    (planned : Nat) (where_ : Option (List Char)) (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (brkStartArm dy m t d planned where_).all (Effect.sleptOk sl) = true := by
  unfold brkStartArm
  simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨⟨settle_sleptOk sl dy _, runNet_sleptOk sl dy _⟩,
    machine_sleptOk sl _ m (by rw [(runNet_keeps dy _).1, settle_obs]) hm⟩

/-- **Every machine arm keeps late binding**, given a start's pending observation. -/
theorem arm_sleptOk (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat)
    (hm : ∀ o, m.block.bind (·.obs) = some o → o.fromStart = true) :
    (arm dy sl m e t d).all (Effect.sleptOk sl) = true := by
  unfold arm
  cases hev : e.ev <;> simp only
  case start id pred rep hsw sleptMin loc _ _ =>
    split
    · rename_i o _
      rw [List.all_append, endRecs_sleptOk sl o t, Bool.true_and]
      exact startArm_sleptOk sl dy _ _ t d _ _ _ _ _ _ hm
    · exact startArm_sleptOk sl dy m _ t d _ _ _ _ _ _ hm
  case pause id =>
    split
    · split
      · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
        refine ⟨settle_sleptOk sl dy _, machine_sleptOk sl _ m ?_ hm⟩
        rw [settle_obs]
        rename_i b hb _
        simp [hb]
      · rfl
    · rfl
  case unpause id =>
    split
    · split
      · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
        refine ⟨⟨closePause_sleptOk sl dy m t, settle_sleptOk sl dy _⟩, machine_sleptOk sl _ m ?_ hm⟩
        rw [settle_obs, ← closePauseM_pending m t]
        cases (closePauseM m t).block <;> rfl
      · rfl
    · rfl
  case interrupt id =>
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    refine ⟨⟨closePause_sleptOk sl dy m t, settle_sleptOk sl dy _⟩, machine_sleptOk sl _ m ?_ hm⟩
    rw [settle_obs]
    have e2 := closePauseM_pending m t
    unfold interruptMachine
    split <;> simp only [e2]
  case resume lost dropped =>
    split
    · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      refine ⟨⟨⟨⟨rfl, rfl, rfl⟩, settle_sleptOk sl dy _⟩, netClosed_sleptOk sl dy _ _ _ _⟩, machine_sleptOk sl _ m ?_ hm⟩
      rw [(netClosed_keeps dy _ _ _ _).1, settle_obs]
      show (m.block.map (fun b => resumeBlock b _ t)).bind (·.obs) = _
      cases m.block <;> simp [resumeBlock_obs]
    · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
      refine ⟨⟨⟨rfl, rfl⟩, settle_sleptOk sl dy _⟩, machine_sleptOk sl _ m ?_ hm⟩
      rw [settle_obs]
      show (m.block.map (fun b => resumeBlock b _ t)).bind (·.obs) = _
      cases m.block <;> simp [resumeBlock_obs]
  case stop id rem =>
    split
    · split
      · obtain ⟨h1, h2⟩ := cut_sleptOk sl dy m t hm
        simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
        refine ⟨⟨h1, runNet_sleptOk sl dy _⟩, rfl, ?_⟩
        simp [Effect.sleptOk, (runNet_keeps dy _).1, h2]
      · rfl
    · rfl
  case extend id by_ =>
    simp only [List.all_cons, Effect.sleptOk, Bool.true_and]
    unfold extendFx
    split
    · split
      · rename_i b hb _
        simp only [List.all_cons, List.all_nil, Bool.and_true]
        exact machine_sleptOk sl _ m (by simp [hb]) hm
      · rfl
    · rfl
  case done => exact doneFx_sleptOk sl dy m _ t d _ _ _ _ _ _ _ hm
  case brk planned actual where_ =>
    have hb : (brkArm dy sl m e t d planned.val (actual.map (·.val))).all (Effect.sleptOk sl) = true := by
      unfold brkArm
      rw [List.all_append, List.all_append, giveBack_sleptOk sl dy m,
        brkFx_sleptOk sl dy _ t _ d (by rw [(giveBack_keeps dy m).1]; exact hm), dayArm_sleptOk dy sl _ t d]; rfl
    split
    · split
      · simp only [List.all_cons, List.all_nil, Bool.and_true]
        exact machine_sleptOk sl _ m rfl hm
      · exact hb
    · exact hb
  case brkStart planned where_ =>
    split
    · exact endBrkFx_sleptOk sl dy m _ _ hm
    · exact brkStartArm_sleptOk sl dy m t d _ _ hm
  all_goals exact dayArm_sleptOk dy sl e t d

theorem sleptInv_step (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry)
    (h : SleptInv sl st) : SleptInv sl (stepWith z dy sl st e) := by
  unfold stepWith effectsWith
  apply sleptInv_applyEffects sl _ st _ h
  intro x hx
  simp only [List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | rfl | rfl | hx | hx
  · rfl
  · rfl
  · rfl
  · exact List.all_eq_true.1 (arm_sleptOk dy sl st.machine e _ _ h.2) x hx
  · exact List.all_eq_true.1 (completionArm_sleptOk sl z _ e _ _) x hx

theorem sleptInv_foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (es : List Entry) (st : State), SleptInv sl st → SleptInv sl (es.foldl (stepWith z dy sl) st)
  | [], _, h => h
  | e :: es, st, h => sleptInv_foldl z dy sl es _ (sleptInv_step z dy sl st e h)

theorem sleptInv_init (sl : Nat → Option Nat) (n : Nat) : SleptInv sl (State.init n) :=
  ⟨fun o ho => by simp [State.init] at ho, fun o ho => by simp [State.init] at ho⟩

theorem insBy_perm {α : Type} (le : α → α → Bool) (a : α) : ∀ (l : List α), (insBy le a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    unfold insBy
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons b (insBy_perm le a l)).trans (List.Perm.swap a b l)

theorem insSort_perm {α : Type} (le : α → α → Bool) : ∀ (l : List α), (insSort le l).Perm l
  | [] => List.Perm.refl _
  | a :: l => (insBy_perm le a _).trans (List.Perm.cons a (insSort_perm le l))

/-- **The first logged sleep of a day**: the `slept_min` of the first surviving wake **in file order**
attributed to the day on the survivors' own index (fork `slept_by_day`'s `or_insert`). -/
def firstLoggedSleep (z : Cal.Tz) (sv : List Entry) (d : Nat) : Option Nat :=
  (firstLoggedWakeOn z (keptWakes z (wakeInstants sv)) sv d).bind sleptOf

/-- `slept_by_day` is the first logged wake's sleep of each day. -/
theorem isWake_eq_sleptOf (e : Entry) : isWake e = (sleptOf e).isSome := by
  unfold isWake sleptOf; cases e.ev <;> rfl

theorem sleptByDay_get (z : Cal.Tz) (kw : List Cal.Instant) (d : Nat) : ∀ (sv : List Entry),
    KMap.get (sleptByDay z kw sv) d = (firstLoggedWakeOn z kw sv d).bind sleptOf
  | [] => rfl
  | e :: sv => by
    have ih := sleptByDay_get z kw d sv
    unfold sleptByDay firstLoggedWakeOn at ih ⊢
    rw [filterMap_cons_toList, List.find?_cons, isWake_eq_sleptOf]
    cases hs : sleptOf e with
    | none => simpa using ih
    | some s =>
      simp only [Option.map_some, Option.toList_some, List.singleton_append, KMap.get_cons, Option.isSome_some,
        Bool.true_and]
      by_cases hd : dayOf z kw e.t.val = d
      · simp [hd, hs]
      · have hb : (dayOf z kw e.t.val == d) = false := by simp [hd]
        rw [if_neg hd, hb]
        exact ih

/-- **An energy observation's sleep is its day's first logged sleep** (§15, Goals; late binding): every
`EnergyObs` of the replay that is not a start's carries the `slept_min` of the first surviving wake in file
order attributed to its day, even a wake logged after the `energy` line. -/
theorem energy_obs_slept_is_the_days_first_logged_sleep (z : Cal.Tz) (es : List Entry) (o : EnergyObs)
    (ho : o ∈ (replay z es).energy) (hfs : o.fromStart = false) :
    o.sleptMin = firstLoggedSleep z (survivors es) o.day := by
  have hinv := sleptInv_foldl z (dayOf z (dayIndexOf z es)) (slOf z es) (survivors es) (State.init es.length)
    (sleptInv_init _ _)
  rw [replay_state] at ho
  unfold finish sortObs at ho
  simp only [(insSort_perm obsLe _).mem_iff, List.mem_append, List.mem_reverse] at ho
  rcases ho with ho | ho
  · rw [hinv.1 o ho hfs]
    exact sleptByDay_get z _ o.day (survivors es)
  · have := hinv.2 o (by simpa using ho)
    rw [this] at hfs; cases hfs

/-! #### The records outside a day: the longest leak, demotions, closes, unknown events -/

theorem completionCore_noRec (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) :
    (completionCore z e t d).all (fun x => !x.isRec) = true := by
  unfold completionCore
  split <;> (repeat' split) <;> simp [Effect.isRec]

theorem completionArm_noRec (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    (completionArm z m e t d).all (fun x => !x.isRec) = true := by
  unfold completionArm
  rw [List.all_append, lateWarns_all _ (fun _ => rfl), Bool.true_and, completionCore_noRec]

/-- **An entry's effects, projected onto the day family's records outside a day, are its day family arm's.** -/
theorem effectsWith_filterMap_rec {α : Type} (ρ : Effect → Option α) (hρ : ∀ x, x.isRec = false → ρ x = none)
    (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (effectsWith z dy sl st e).filterMap ρ = (dayArm dy sl e (e.t.val, e.off.val) (dy e.t.val)).filterMap ρ := by
  have hc : (completionArm z st.machine e (e.t.val, e.off.val) (dy e.t.val)).filterMap ρ = [] :=
    List.filterMap_eq_nil_iff.2 (fun x hx => hρ x (by simpa using List.all_eq_true.1 (completionArm_noRec z _ e _ _) x hx))
  unfold effectsWith
  simp only [List.filterMap_cons, hρ (.header (dy e.t.val) (HeaderRec.of e false)) rfl,
    hρ (.global (e.t.val, e.off.val)) rfl, hρ (.seam (dy e.t.val) ⟨(e.t.val, e.off.val), seamKindOf e.ev⟩) rfl,
    List.filterMap_append, arm_filterMap_rec ρ hρ, hc, List.append_nil]

def Effect.leakOf? : Effect → Option LeakRec
  | .leak r => some r
  | _ => none

theorem applyEffects_longestLeak : ∀ (fx : List Effect) (st : State),
    (applyEffects st fx).longestLeak = (fx.filterMap Effect.leakOf?).foldl (lastMaxStep leakLt) st.longestLeak
  | [], _ => rfl
  | x :: fx, st => by
    rw [applyEffects_cons, applyEffects_longestLeak fx, filterMap_cons_toList, List.foldl_append]
    congr 1
    cases x with
    | itemDaySub i d m => simp only [applyEffect, Effect.leakOf?]; split <;> rfl
    | obs o => cases o <;> rfl
    | _ => rfl

/-- **The leak record an entry offers** (fork `idle`'s `longest_leak` candidate): a `leak` idle gap, its stamp, the
day of its start, and its minutes. -/
def leakOf (dy : Cal.Instant → Nat) (e : Entry) : Option LeakRec :=
  match e.ev with
  | .idle attributed min =>
    if attributed = "leak".toList then some ⟨stampOf e, dy (Cal.subMinutes e.t.val min.val), min.val⟩ else none
  | _ => none

theorem dayArm_leaks (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) :
    (dayArm dy sl e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.leakOf? = (leakOf dy e).toList := by
  unfold dayArm leakOf stampOf
  split <;> (repeat' split) <;> simp_all [Effect.leakOf?.eq_def]

/-- **The first leak maximum wins** (§8.2; Goals): fork `Replay.longest_leak` is the running maximum of the
survivors' `leak` gaps by minutes, replaced only by a strictly longer one, so the first of equal maxima stays. -/
theorem the_first_leak_maximum_wins (z : Cal.Tz) (es : List Entry) :
    (replay z es).longestLeak = lastMax? leakLt ((survivors es).filterMap (leakOf (dayOf z (dayIndexOf z es)))) := by
  have h : ∀ (l : List Entry) (st : State),
      (l.foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) st).longestLeak
        = (l.filterMap (leakOf (dayOf z (dayIndexOf z es)))).foldl (lastMaxStep leakLt) st.longestLeak := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons e l ih =>
      intro st
      rw [List.foldl_cons, ih, filterMap_cons_toList, List.foldl_append]
      congr 1
      unfold stepWith
      rw [applyEffects_longestLeak, effectsWith_filterMap_rec _ (fun x hx => by
        cases x <;> simp_all [Effect.isRec, Effect.leakOf?]), dayArm_leaks]
  rw [replay_state]
  unfold finish lastMax?
  simp only
  rw [h]
  rfl

theorem leakLt_trans (a b c : LeakRec) (h₁ : leakLt a b = true) (h₂ : leakLt b c = true) : leakLt a c = true := by
  simp only [leakLt, decide_eq_true_eq] at *; omega

theorem leakLt_skip (a b c : LeakRec) (h₁ : leakLt a b = false) (h₂ : leakLt a c = true) : leakLt b c = true := by
  simp only [leakLt, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega

/-- **What the longest leak is**: every leak logged before it is strictly shorter, and none logged after it is
longer. -/
theorem the_longest_leak_is_the_first_of_the_longest (z : Cal.Tz) (es : List Entry) (b : LeakRec)
    (h : (replay z es).longestLeak = some b) :
    ∃ l₁ l₂, (survivors es).filterMap (leakOf (dayOf z (dayIndexOf z es))) = l₁ ++ b :: l₂ ∧
      (∀ x ∈ l₁, x.min < b.min) ∧ (∀ x ∈ l₂, ¬ b.min < x.min) := by
  rw [the_first_leak_maximum_wins] at h
  obtain ⟨l₁, l₂, he, h1, h2⟩ := lastMax?_spec leakLt leakLt_trans leakLt_skip _ b h
  exact ⟨l₁, l₂, he, fun x hx => by simpa [leakLt] using h1 x hx, fun x hx => by simpa [leakLt] using h2 x hx⟩

def Effect.demoteOf? : Effect → Option (Nat × Demotion)
  | .demote d r => some (d, r)
  | _ => none

def Effect.closeOf? : Effect → Option (Nat × CloseRec)
  | .close d r => some (d, r)
  | _ => none

def Effect.unknownOf? : Effect → Option Unit
  | .unknown => some ()
  | _ => none

theorem applyEffects_records : ∀ (fx : List Effect) (st : State),
    (applyEffects st fx).demotions = (fx.filterMap Effect.demoteOf?).reverse ++ st.demotions ∧
    (applyEffects st fx).closes = (fx.filterMap Effect.closeOf?).reverse ++ st.closes ∧
    (applyEffects st fx).unknown = st.unknown + (fx.filterMap Effect.unknownOf?).length
  | [], _ => by simp [applyEffects]
  | x :: fx, st => by
    rw [applyEffects_cons]
    obtain ⟨h1, h2, h3⟩ := applyEffects_records fx (applyEffect st x)
    rw [h1, h2, h3, filterMap_cons_toList, filterMap_cons_toList, filterMap_cons_toList]
    cases x with
    | demote d r => exact ⟨by simp [applyEffect, Effect.demoteOf?], rfl, rfl⟩
    | close d r => exact ⟨rfl, by simp [applyEffect, Effect.closeOf?], rfl⟩
    | unknown =>
      refine ⟨rfl, rfl, ?_⟩
      simp only [applyEffect, Effect.unknownOf?, Option.toList_some, List.singleton_append, List.length_cons]
      omega
    | itemDaySub i d m =>
      simp only [applyEffect]
      split <;> exact ⟨rfl, rfl, rfl⟩
    | obs o => cases o <;> exact ⟨rfl, rfl, rfl⟩
    | _ => exact ⟨rfl, rfl, rfl⟩

/-- **The demotion an entry records** (fork `demote`): its day, stamp, id, keys, estimate and fork
`stamp_from_key(from)`. -/
def demotionOf (dy : Cal.Instant → Nat) (e : Entry) : Option (Nat × Demotion) :=
  match e.ev with
  | .demote id from_ to est => some (dy e.t.val, ⟨e.line, stampOf e, id, from_, to, est.val, Log.stampFromKey from_⟩)
  | _ => none

/-- **The close an entry records** (fork `close`): its day, stamp, period and key. -/
def closeOf (dy : Cal.Instant → Nat) (e : Entry) : Option (Nat × CloseRec) :=
  match e.ev with
  | .close period key => some (dy e.t.val, ⟨e.line, stampOf e, period, key⟩)
  | _ => none

/-- An unknown event (fork `Event::Unknown`). -/
def isUnknownEv (e : Entry) : Bool :=
  match e.ev with
  | .unknown _ _ => true
  | _ => false

theorem dayArm_records (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) :
    (dayArm dy sl e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.demoteOf? = (demotionOf dy e).toList ∧
    (dayArm dy sl e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.closeOf? = (closeOf dy e).toList ∧
    ((dayArm dy sl e (e.t.val, e.off.val) (dy e.t.val)).filterMap Effect.unknownOf?).length
      = if isUnknownEv e then 1 else 0 := by
  unfold dayArm demotionOf closeOf isUnknownEv stampOf
  cases hev : e.ev <;> simp only [hev] <;> (try split) <;> (try split) <;>
    simp_all [Effect.demoteOf?.eq_def, Effect.closeOf?.eq_def, Effect.unknownOf?.eq_def]

theorem stepWith_records (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (stepWith z dy sl st e).demotions = (demotionOf dy e).toList ++ st.demotions ∧
    (stepWith z dy sl st e).closes = (closeOf dy e).toList ++ st.closes ∧
    (stepWith z dy sl st e).unknown = st.unknown + (if isUnknownEv e then 1 else 0) := by
  obtain ⟨h1, h2, h3⟩ := applyEffects_records (effectsWith z dy sl st e) st
  obtain ⟨g1, g2, g3⟩ := dayArm_records dy sl e
  have r1 := effectsWith_filterMap_rec Effect.demoteOf? (fun x hx => by cases x <;> simp_all [Effect.isRec, Effect.demoteOf?]) z dy sl st e
  have r2 := effectsWith_filterMap_rec Effect.closeOf? (fun x hx => by cases x <;> simp_all [Effect.isRec, Effect.closeOf?]) z dy sl st e
  have r3 := effectsWith_filterMap_rec Effect.unknownOf? (fun x hx => by cases x <;> simp_all [Effect.isRec, Effect.unknownOf?]) z dy sl st e
  unfold stepWith
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, r1, g1]; cases demotionOf dy e <;> rfl
  · rw [h2, r2, g2]; cases closeOf dy e <;> rfl
  · rw [h3, r3, g3]

theorem foldl_stepWith_records (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (l : List Entry) (st : State),
      (l.foldl (stepWith z dy sl) st).demotions = (l.filterMap (demotionOf dy)).reverse ++ st.demotions ∧
      (l.foldl (stepWith z dy sl) st).closes = (l.filterMap (closeOf dy)).reverse ++ st.closes ∧
      (l.foldl (stepWith z dy sl) st).unknown = st.unknown + (l.filter isUnknownEv).length
  | [], st => by simp
  | e :: l, st => by
    obtain ⟨h1, h2, h3⟩ := foldl_stepWith_records z dy sl l (stepWith z dy sl st e)
    obtain ⟨g1, g2, g3⟩ := stepWith_records z dy sl st e
    rw [List.foldl_cons, h1, h2, h3, g1, g2, g3, filterMap_cons_toList, filterMap_cons_toList, List.filter_cons]
    refine ⟨?_, ?_, ?_⟩
    · cases demotionOf dy e <;> simp
    · cases closeOf dy e <;> simp
    · split <;> simp_all <;> omega

/-- **The demotions are the survivors' `demote`s, in file order** (fork `demotions`), each on its day. -/
theorem the_demotions_are_the_survivors_demotes_in_file_order (z : Cal.Tz) (es : List Entry) :
    (replay z es).demotions = (survivors es).filterMap (demotionOf (dayOf z (dayIndexOf z es))) := by
  rw [replay_state]
  unfold finish
  simp only
  rw [(foldl_stepWith_records z _ _ _ _).1]
  simp [State.init]

/-- **The closes are the survivors' `close`s, in file order** (fork `closes`), each on its day. -/
theorem the_closes_are_the_survivors_closes_in_file_order (z : Cal.Tz) (es : List Entry) :
    (replay z es).closes = (survivors es).filterMap (closeOf (dayOf z (dayIndexOf z es))) := by
  rw [replay_state]
  unfold finish
  simp only
  rw [(foldl_stepWith_records z _ _ _ _).2.1]
  simp [State.init]

/-- **The unknown count is the surviving unknown events** (fork `Replay.unknown`). -/
theorem the_unknown_count_is_the_surviving_unknown_events (z : Cal.Tz) (es : List Entry) :
    (replay z es).unknown = ((survivors es).filter isUnknownEv).length := by
  rw [replay_state]
  unfold finish
  simp only
  rw [(foldl_stepWith_records z _ _ _ _).2.2]
  simp [State.init]

/-- **A demotion's stamp reads its `from` key** (§8.2; Goals): every demotion of the replay carries fork
`stamp_from_key(from)`: an ISO week key's week, a date key's day of the month, and none for anything else. -/
theorem a_demote_stamp_reads_the_week_or_date_key (z : Cal.Tz) (es : List Entry) (p : Nat × Demotion)
    (hp : p ∈ (replay z es).demotions) : p.2.stamp = Log.stampFromKey p.2.from_ := by
  rw [the_demotions_are_the_survivors_demotes_in_file_order, List.mem_filterMap] at hp
  obtain ⟨e, -, he⟩ := hp
  unfold demotionOf at he
  split at he
  · cases he; rfl
  · cases he

/-! #### `lastT`: the latest instant of a day, beside `lastEffective`, the last line -/

/-- **§8.4's `lastT` of a day** (fork `DaySeam.last_t`, the TUI's `idle_since`; C6 derives the seam): the latest
stamp by instant over the survivors of any kind attributed to the day, a later line winning a tie. -/
def lastTOn (z : Cal.Tz) (es : List Entry) (d : Nat) : Option At :=
  lastMax? atLe (((survivors es).filter (fun e => decide (dayOf z (dayIndexOf z es) e.t.val = d))).map stampOf)

end DayLaws

/-! ## C6: every line's header, the seams, the observations in file order, and the view (§8.2, §8.4, §11)

**Every line has one header effect** (§8.2): a survivor's is in its `effects` (`HeaderRec.of e false`), and a
cancelled line's is the **second pass**, `cancelledHeaderFx`, over the whole list with `cancelled := true`.
`entryHeaders` is every entry's header in file order, and the two passes partition it
(`the_survivors_headers_are_the_uncancelled_entry_headers`, `the_two_header_passes_are_every_entrys_header`).
**The seams** (fork `DaySeam`, R1–R4) are an effect of every survivor on its day (`Effect.seam`), and a day's
`last_t` is C5's specification `lastTOn` (`a_days_last_t_is_the_latest_stamp_of_its_survivors`).
**Observations are in file order** over the log op's entries, whose lines strictly increase
(`observations_are_in_file_order_on_increasing_lines`; §15's statement without that hypothesis is refuted by a
repeated line, `observations_are_not_in_file_order_when_a_line_repeats`).  **Every dated output names its day
key** (`every_dated_output_names_its_day_key`, CRIT 9).  **The view** (§8.4) is `ask`, one total query per
reading, over `replayDoc`; `factsView` is it without the line bookkeeping. -/

section Facts6

open Log (Id U8 U32 Num)

/-! ### Every line's header -/

/-- **Every entry's header** (fork `Replay::view`'s rows, §11.4): per entry in file order, cancelled entries and
undos included, its wake-attributed day on the survivors' index and its header with the undo mask's bit. -/
def entryHeaders (z : Cal.Tz) (es : List Entry) : List (Nat × HeaderRec) :=
  let dy := dayOf z (dayIndexOf z es)
  es.zipIdx.map (fun p => (dy p.1.t.val, HeaderRec.of p.1 (cancelledAt es p.2)))

/-- The compiled headers: the fast mask's dead array read once, and the day index by bisection. -/
def entryHeadersFast (z : Cal.Tz) (es : List Entry) : List (Nat × HeaderRec) :=
  let dead := maskFast es
  let a := (dayIndexOf z es).toArray
  es.zipIdx.map (fun p => (dayOfArr z a p.1.t.val, HeaderRec.of p.1 (deadAt dead p.2)))

@[csimp] theorem entryHeaders_eq_entryHeadersFast : @entryHeaders = @entryHeadersFast := by
  funext z es
  unfold entryHeaders entryHeadersFast
  simp only
  apply List.map_congr_left
  intro p hp
  rw [cancelledAt_eq_deadAt es p hp]
  unfold dayOfArr dayOf dayIndexOf
  rw [lastWakeLeArr_eq_lastWakeLe _ (keptWakes_sorted z _)]

theorem entryHeaders_length (z : Cal.Tz) (es : List Entry) : (entryHeaders z es).length = es.length := by
  simp [entryHeaders]

/-- **The second pass** (§8.2): a `header` effect for every cancelled line, on its day, `cancelled := true`. -/
def cancelledHeaderFx (z : Cal.Tz) (es : List Entry) : List Effect :=
  ((entryHeaders z es).filter (fun p => p.2.cancelled)).map (fun p => .header p.1 p.2)

def Effect.headerOf? : Effect → Option (Nat × HeaderRec)
  | .header d h => some (d, h)
  | _ => none

theorem headerOf?_of_not_isHeader (x : Effect) (h : x.isHeader = false) : x.headerOf? = none := by
  cases x <;> simp_all [Effect.isHeader, Effect.headerOf?]

theorem applyEffects_headers : ∀ (fx : List Effect) (st : State),
    (applyEffects st fx).headers = (fx.filterMap Effect.headerOf?).reverse ++ st.headers
  | [], _ => rfl
  | x :: fx, st => by
    rw [applyEffects_cons, applyEffects_headers fx, filterMap_cons_toList, List.reverse_append, List.append_assoc]
    congr 1
    cases x with
    | header d h => rfl
    | itemDaySub i d m => simp only [applyEffect, Effect.headerOf?]; split <;> rfl
    | obs o => cases o <;> rfl
    | _ => rfl

theorem effectsWith_headers (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (effectsWith z dy sl st e).filterMap Effect.headerOf? = [(dy e.t.val, HeaderRec.of e false)] := by
  unfold effectsWith
  rw [List.filterMap_cons, List.filterMap_cons, List.filterMap_cons, List.filterMap_append,
    List.filterMap_eq_nil_iff.2 (fun x hx => headerOf?_of_not_isHeader x (arm_no_header _ _ _ _ _ _ x hx)),
    List.filterMap_eq_nil_iff.2 (fun x hx => headerOf?_of_not_isHeader x (completionArm_no_header _ _ _ _ _ x hx))]
  rfl

theorem foldl_stepWith_headers (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (l : List Entry) (st : State),
      (l.foldl (stepWith z dy sl) st).headers = (l.map (fun e => (dy e.t.val, HeaderRec.of e false))).reverse ++ st.headers
  | [], _ => rfl
  | e :: l, st => by
    rw [List.foldl_cons, foldl_stepWith_headers z dy sl l, List.map_cons, List.reverse_cons, List.append_assoc]
    congr 1
    unfold stepWith
    rw [applyEffects_headers, effectsWith_headers]
    rfl

/-- **The survivors' header effects are the uncancelled entries' headers**, in file order (for every list of
entries): what the replay's own header effects hold is exactly the part of `entryHeaders` the mask keeps. -/
theorem the_survivors_headers_are_the_uncancelled_entry_headers (z : Cal.Tz) (es : List Entry) :
    (replay z es).headers = (entryHeaders z es).filter (fun p => !p.2.cancelled) := by
  rw [replay_state]
  unfold finish
  simp only
  rw [foldl_stepWith_headers]
  simp only [State.init, List.append_nil, List.reverse_reverse]
  rw [survivors_are_the_uncancelled_entries]
  unfold entryHeaders
  simp only
  rw [List.filter_map, List.map_map]
  have hf : (es.zipIdx.filter ((fun p : Nat × HeaderRec => !p.2.cancelled) ∘
      (fun p => (dayOf z (dayIndexOf z es) p.1.t.val, HeaderRec.of p.1 (cancelledAt es p.2)))))
      = es.zipIdx.filter (fun p => !cancelledAt es p.2) := rfl
  rw [hf]
  apply List.map_congr_left
  intro p hp
  have hc : cancelledAt es p.2 = false := by simpa using (List.mem_filter.1 hp).2
  simp [HeaderRec.of, hc]

/-- **The two header passes are every entry's header** (§8.2, CRIT 9): the survivors' header effects and the second
pass's, together, are `entryHeaders` up to order, one per entry. -/
theorem the_two_header_passes_are_every_entrys_header (z : Cal.Tz) (es : List Entry) :
    ((replay z es).headers ++ (cancelledHeaderFx z es).filterMap Effect.headerOf?).Perm (entryHeaders z es) := by
  rw [the_survivors_headers_are_the_uncancelled_entry_headers]
  have h2 : (cancelledHeaderFx z es).filterMap Effect.headerOf? = (entryHeaders z es).filter (fun p => p.2.cancelled) := by
    unfold cancelledHeaderFx
    generalize (entryHeaders z es).filter (fun p => p.2.cancelled) = l
    induction l with
    | nil => rfl
    | cons a l ih => simp [Effect.headerOf?, ih]
  rw [h2]
  exact List.perm_append_comm.trans (List.filter_append_perm _ _)

/-! ### The seams -/

def Effect.seamOf? : Effect → Option (Nat × SeamOp)
  | .seam d op => some (d, op)
  | _ => none

theorem seamOp_lastT (op : SeamOp) (a : SeamAcc) : (op.apply a).lastT = lastMaxStep atLe a.lastT op.t := by
  unfold SeamOp.apply
  cases op.kind <;> simp only
  split <;> rfl

theorem applyEffects_seam_lastT (d : Nat) : ∀ (fx : List Effect) (st : State),
    ((applyEffects st fx).seams.get d).bind (·.lastT)
      = (((fx.filterMap Effect.seamOf?).filter (fun p => decide (p.1 = d))).map (·.2.t)).foldl (lastMaxStep atLe)
          ((st.seams.get d).bind (·.lastT))
  | [], _ => rfl
  | x :: fx, st => by
    rw [applyEffects_cons, applyEffects_seam_lastT d fx, filterMap_cons_toList, List.filter_append, List.map_append,
      List.foldl_append]
    congr 1
    cases x with
    | seam d' op =>
      simp only [Effect.seamOf?, Option.toList_some, applyEffect, HMap.get_alter]
      by_cases h : d = d'
      · subst h
        simp only [if_true, decide_true, List.filter_cons_of_pos, List.filter_nil, List.map_cons, List.map_nil,
          List.foldl_cons, List.foldl_nil, Option.bind_some, seamOp_lastT]
        cases st.seams.get d <;> rfl
      · simp [h, Ne.symm h]
    | itemDaySub i d m => simp only [applyEffect]; split <;> rfl
    | obs o => cases o <;> rfl
    | _ => rfl

theorem dayArm_noSeam (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ dayArm dy sl e t d, x.seamOf? = none := by
  have h : (dayArm dy sl e t d).filterMap Effect.seamOf? = [] := by
    unfold dayArm
    split <;> (repeat' split) <;> simp [Effect.seamOf?]
  exact List.filterMap_eq_nil_iff.1 h

theorem arm_noSeam (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ arm dy sl m e t d, x.seamOf? = none := by
  intro x hx
  obtain ⟨fx, hfx, h | ⟨-, h⟩⟩ := arm_split dy sl m e t d
  · rw [h] at hx
    rcases List.mem_append.1 hx with hx | hx
    · have := hfx x hx
      cases x <;> simp_all [Effect.blockOnly, Effect.seamOf?]
    · exact dayArm_noSeam dy sl _ t d x hx
  · rw [h] at hx
    have := hfx x hx
    cases x <;> simp_all [Effect.blockOnly, Effect.seamOf?]

theorem completionCore_noSeam (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ completionCore z e t d, x.seamOf? = none := by
  have h : (completionCore z e t d).filterMap Effect.seamOf? = [] := by
    unfold completionCore
    split <;> (repeat' split) <;> simp [Effect.seamOf?]
  exact List.filterMap_eq_nil_iff.1 h

theorem completionArm_noSeam (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∀ x ∈ completionArm z m e t d, x.seamOf? = none := by
  intro x hx
  unfold completionArm at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨w, rfl⟩ := lateWarns_rwarn m e d x hx; rfl
  · exact completionCore_noSeam z e t d x hx

theorem effectsWith_seams (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    (effectsWith z dy sl st e).filterMap Effect.seamOf? = [(dy e.t.val, ⟨(e.t.val, e.off.val), seamKindOf e.ev⟩)] := by
  unfold effectsWith
  rw [List.filterMap_cons, List.filterMap_cons, List.filterMap_cons, List.filterMap_append,
    List.filterMap_eq_nil_iff.2 (arm_noSeam _ _ _ _ _ _), List.filterMap_eq_nil_iff.2 (completionArm_noSeam _ _ _ _ _)]
  rfl

theorem foldl_stepWith_seam_lastT (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (d : Nat) :
    ∀ (l : List Entry) (st : State),
      ((l.foldl (stepWith z dy sl) st).seams.get d).bind (·.lastT)
        = ((l.filter (fun e => decide (dy e.t.val = d))).map stampOf).foldl (lastMaxStep atLe) ((st.seams.get d).bind (·.lastT))
  | [], _ => rfl
  | e :: l, st => by
    rw [List.foldl_cons, foldl_stepWith_seam_lastT z dy sl d l, List.filter_cons]
    unfold stepWith
    rw [applyEffects_seam_lastT, effectsWith_seams]
    by_cases h : dy e.t.val = d <;> simp [h, stampOf]

/-- **A day's `last_t` is the latest stamp of its survivors** (fork `DaySeam.last_t`, R4; C5's owed equation): the
derived seam's `lastT` is C5's specification `lastTOn`, the running maximum by instant over the survivors of any
kind attributed to the day, a later line winning a tie. -/
theorem a_days_last_t_is_the_latest_stamp_of_its_survivors (z : Cal.Tz) (es : List Entry) (d : Nat) :
    ((replay z es).seams.get d).bind (·.lastT) = lastTOn z es d := by
  rw [replay_state]
  unfold finish lastTOn lastMax?
  simp only
  rw [HMap.get_mapVals]
  have hm : ∀ (o : Option SeamAcc), (o.map (fun a => { a with idleMarks := a.idleMarks.reverse })).bind (·.lastT)
      = o.bind (·.lastT) := by intro o; cases o <;> rfl
  rw [hm, foldl_stepWith_seam_lastT]
  simp [State.init, HMap.get_empty]

/-! ### Every dated output names its day key (CRIT 9) -/

/-- The date a key names, if any: a day's record, an item's minutes on a day, a done date, a date-keyed instance. -/
def Key.date? : Key → Option Nat
  | .day d => some d
  | .itemDay _ d => some d
  | .doneDate _ d => some d
  | .instDate _ _ d => some d
  | _ => none

/-- **The day of the dated record an effect writes** (§8.4's O, DR, W and WR): a day's record, header, seam,
observation, interruption, demotion or close; an item's minutes on a day; a done date; an instance whose `inst`
names a date.  An all-time aggregate (A) carries dates as values and writes no dated record: the global longest
leak's day (its gap's day is named by its `IdleRecord`, `every_leak_is_on_a_day_its_idle_record_names`), a named
event's local date (the `LatestNamed` since-filter's), `last_done`'s stamp, the bookkeeping. -/
def Effect.day? : Effect → Option Nat
  | .dayAdd d _ => some d
  | .header d _ => some d
  | .itemDay _ d _ => some d
  | .itemDaySub _ d _ => some d
  | .obs o => some o.day
  | .interruption r => some r.day
  | .doneDate _ d => some d
  | .inst _ ins _ => Log.instDate? ins
  | .demote d _ => some d
  | .close d _ => some d
  | .seam d _ => some d
  | _ => none

/-- **Every dated output names its day key** (§15, Goals; CRIT 9): an effect that writes a dated record names that
date in its key, so a guard reading keys (G3, G3w) sees every write to a sealed day or window date.  Proved for every
effect; §15's statement, over the effects of an entry, is this theorem given fewer arguments. -/
theorem every_dated_output_names_its_day_key (fx : Effect) (d : Nat) (hd : fx.day? = some d) :
    fx.key.date? = some d := by
  cases fx with
  | inst item ins r =>
    simp only [Effect.day?] at hd
    simp [Effect.key, hd, Key.date?]
  | obs o => cases o <;> simp_all [Effect.day?, Effect.key, Key.date?, Obs.day]
  | _ => simp_all [Effect.day?, Effect.key, Key.date?]

/-- **Every leak is on a day its idle record names**: the global longest leak's candidate (keyed `global`, an
all-time aggregate) is emitted beside the `IdleRecord` of the same gap on the same day, whose `dayAdd` effect names
that day, so the day of the gap is seen by a guard even though the aggregate's key is not dated. -/
theorem every_leak_is_on_a_day_its_idle_record_names (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat))
    (st : State) (e : Entry) (r : LeakRec) (h : Effect.leak r ∈ effects z kw slept st e) :
    ∃ ir : IdleRec, Effect.dayAdd r.day (.idle ir) ∈ effects z kw slept st e ∧ ir.t = r.t ∧ ir.min = r.min := by
  have hc : Effect.leak r ∉ completionArm z st.machine e (e.t.val, e.off.val) (dayOf z kw e.t.val) := by
    intro hm
    have : (completionArm z st.machine e (e.t.val, e.off.val) (dayOf z kw e.t.val)).all (fun x => !x.isRec) = true :=
      completionArm_noRec z _ e _ _
    simpa [Effect.isRec] using List.all_eq_true.1 this _ hm
  have ha : Effect.leak r ∈ arm (dayOf z kw) (KMap.get slept) st.machine e (e.t.val, e.off.val) (dayOf z kw e.t.val) := by
    unfold effects effectsWith at h
    simp only [List.mem_cons, List.mem_append, reduceCtorEq, false_or] at h
    rcases h with h | h
    · exact h
    · exact absurd h hc
  suffices hs : ∃ ir : IdleRec, Effect.dayAdd r.day (.idle ir) ∈ arm (dayOf z kw) (KMap.get slept) st.machine e
      (e.t.val, e.off.val) (dayOf z kw e.t.val) ∧ ir.t = r.t ∧ ir.min = r.min by
    obtain ⟨ir, hm, h1, h2⟩ := hs
    refine ⟨ir, ?_, h1, h2⟩
    unfold effects effectsWith
    simp only [List.mem_cons, List.mem_append, reduceCtorEq, false_or]
    exact Or.inl hm
  obtain ⟨fx, hfx, hs | ⟨-, hs⟩⟩ :=
    arm_split (dayOf z kw) (KMap.get slept) st.machine e (e.t.val, e.off.val) (dayOf z kw e.t.val)
  rotate_left
  · rw [hs] at ha; have := hfx _ ha; simp [Effect.blockOnly] at this
  rw [hs] at ha ⊢
  rcases List.mem_append.1 ha with ha | ha
  · have := hfx _ ha; simp [Effect.blockOnly] at this
  · by_cases hb : ∃ p a w, e.ev = .brk p a w
    · obtain ⟨p, a, w, hb⟩ := hb
      simp [placed, dayArm, hb] at ha
    rw [placed_of_not_brk st.machine e (fun p a w h => hb ⟨p, a, w, h⟩)] at ha ⊢
    suffices hd : ∃ ir : IdleRec, Effect.dayAdd r.day (.idle ir) ∈ dayArm (dayOf z kw) (KMap.get slept) e
        (e.t.val, e.off.val) (dayOf z kw e.t.val) ∧ ir.t = r.t ∧ ir.min = r.min by
      obtain ⟨ir, hm, h1, h2⟩ := hd
      exact ⟨ir, List.mem_append_right _ hm, h1, h2⟩
    unfold dayArm at ha ⊢
    cases hev : e.ev <;> simp only [hev] at ha ⊢ <;> try simp at ha
    case idle attributed min =>
      by_cases hl : attributed = "leak".toList
      · obtain ⟨-, rfl⟩ := ha
        exact ⟨⟨(e.t.val, e.off.val), dayOf z kw (Cal.subMinutes e.t.val min.val), attributed, min.val⟩, by simp, rfl, rfl⟩
      · simp_all
    all_goals (repeat' split at ha) <;> simp at ha

/-! ### Observations in file order -/

theorem applyEffects_obs : ∀ (fx : List Effect) (st : State),
    (applyEffects st fx).energy = (fx.filterMap Effect.energyOf?).reverse ++ st.energy ∧
    (applyEffects st fx).durations = (fx.filterMap Effect.durationOf?).reverse ++ st.durations ∧
    (applyEffects st fx).machine = ((fx.filterMap Effect.machineOf?).getLast?).getD st.machine
  | [], _ => ⟨rfl, rfl, rfl⟩
  | x :: fx, st => by
    obtain ⟨h1, h2, h3⟩ := applyEffects_obs fx (applyEffect st x)
    rw [applyEffects_cons, h1, h2, h3, filterMap_cons_toList, filterMap_cons_toList, filterMap_cons_toList]
    cases x with
    | obs o => cases o <;> simp [applyEffect, Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]
    | machine m =>
      refine ⟨rfl, rfl, ?_⟩
      simp only [applyEffect, Effect.machineOf?, Option.toList_some, List.singleton_append, List.getLast?_cons]
      rfl
    | itemDaySub i d m =>
      simp only [applyEffect]
      split <;> exact ⟨rfl, rfl, rfl⟩
    | _ => exact ⟨rfl, rfl, rfl⟩

/-- The line of the machine's pending start observation, if any. -/
def pendLines (m : Machine) : List Nat := ((m.block.bind (·.obs)).map (·.line)).toList

/-- The lines of a state's energy observations, emitted and pending. -/
def obsLines (st : State) : List Nat := st.energy.map (·.line) ++ pendLines st.machine

/-- **An `extend` writes no observation** (the owner's D108): at most one machine, its block's own minutes grown. -/
theorem extendFx_obs (m : Machine) (id : Id) (by_ : Nat) :
    (extendFx m id by_).filterMap Effect.energyOf? = [] ∧ (extendFx m id by_).filterMap Effect.durationOf? = [] := by
  unfold extendFx
  split
  · split <;> simp [List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.durationOf?]
  · simp

/-- **The machine an `extend` writes** (the owner's D108): the old machine, its open block's `ext` grown — and only when
a block is open. -/
theorem extendFx_machines (m : Machine) (id : Id) (by_ : Nat) (m' : Machine)
    (h : m' ∈ (extendFx m id by_).filterMap Effect.machineOf?) :
    ∃ b, m.block = some b ∧ m' = { m with block := some { b with ext := b.ext + by_ } } := by
  unfold extendFx at h
  split at h
  · rename_i b hb
    split at h
    · simp only [List.filterMap_cons, List.filterMap_nil, Effect.machineOf?, List.mem_singleton] at h
      exact ⟨b, hb, h⟩
    · simp at h
  · simp at h

theorem redraw_obs (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) :
    (redraw dy id old P).2.filterMap Effect.energyOf? = [] ∧ (redraw dy id old P).2.filterMap Effect.durationOf? = [] ∧
    (redraw dy id old P).2.filterMap Effect.machineOf? = [] := by
  unfold redraw
  simp only [List.filterMap_append, List.filterMap_map]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [List.filterMap_eq_nil_iff, Function.comp_def, Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]

/-- **A late break's netting observes nothing and writes no machine** (the owner's D100). -/
theorem netClosed_obs (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) :
    (netClosed dy s e dd m).2.filterMap Effect.energyOf? = [] ∧ (netClosed dy s e dd m).2.filterMap Effect.durationOf? = [] ∧
    (netClosed dy s e dd m).2.filterMap Effect.machineOf? = [] := by
  have h : ∀ x ∈ (netClosed dy s e dd m).2, x.energyOf? = none ∧ x.durationOf? = none ∧ x.machineOf? = none := by
    intro x hx
    obtain ⟨C, hC⟩ := netClosed_mem dy s e dd m x hx
    rcases netOne_mem dy s e dd C x hC with h | rfl | rfl | rfl
    · obtain ⟨h1, h2, h3⟩ := redraw_obs dy C.id C.drawn (cutOut s e C.spans)
      exact ⟨List.filterMap_eq_nil_iff.1 h1 x h, List.filterMap_eq_nil_iff.1 h2 x h, List.filterMap_eq_nil_iff.1 h3 x h⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  exact ⟨List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).1), List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).2.1),
    List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).2.2)⟩

/-- **A give-back observes nothing and writes no machine** (D137). -/
theorem giveBack_obs (dy : Cal.Instant → Nat) (m : Machine) :
    (giveBack dy m).2.filterMap Effect.energyOf? = [] ∧ (giveBack dy m).2.filterMap Effect.durationOf? = [] ∧
    (giveBack dy m).2.filterMap Effect.machineOf? = [] := by
  have h : ∀ x ∈ (giveBack dy m).2, x.energyOf? = none ∧ x.durationOf? = none ∧ x.machineOf? = none := by
    intro x hx
    obtain ⟨C, hC⟩ := giveBack_mem dy m x hx
    rcases giveOne_mem dy C x hC with h | rfl | rfl | rfl | rfl
    · obtain ⟨h1, h2, h3⟩ := redraw_obs dy C.id C.drawn C.restored
      exact ⟨List.filterMap_eq_nil_iff.1 h1 x h, List.filterMap_eq_nil_iff.1 h2 x h, List.filterMap_eq_nil_iff.1 h3 x h⟩
    all_goals exact ⟨rfl, rfl, rfl⟩
  exact ⟨List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).1), List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).2.1),
    List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).2.2)⟩

theorem netStart_obs (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (m : Machine) :
    (netStart dy t dd m).2.filterMap Effect.energyOf? = [] ∧ (netStart dy t dd m).2.filterMap Effect.durationOf? = [] ∧
    (netStart dy t dd m).2.filterMap Effect.machineOf? = [] := by
  have h : ∀ x ∈ (netStart dy t dd m).2, x.energyOf? = none ∧ x.durationOf? = none ∧ x.machineOf? = none := by
    intro x hx
    obtain ⟨C, hC⟩ := netStart_mem dy t dd m x hx
    rcases netOne_mem dy t _ dd C x hC with h | rfl | rfl | rfl
    · obtain ⟨h1, h2, h3⟩ := redraw_obs dy C.id C.drawn (cutOut t (startEnd t C) C.spans)
      exact ⟨List.filterMap_eq_nil_iff.1 h1 x h, List.filterMap_eq_nil_iff.1 h2 x h, List.filterMap_eq_nil_iff.1 h3 x h⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  exact ⟨List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).1), List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).2.1),
    List.filterMap_eq_nil_iff.2 (fun x hx => (h x hx).2.2)⟩

theorem runNet_obs (dy : Cal.Instant → Nat) (m : Machine) :
    (runNet dy m).2.filterMap Effect.energyOf? = [] ∧ (runNet dy m).2.filterMap Effect.durationOf? = [] ∧
    (runNet dy m).2.filterMap Effect.machineOf? = [] := by
  rcases runNet_cases dy m with h | ⟨o, -, h⟩
  · rw [h]; exact ⟨rfl, rfl, rfl⟩
  · rw [h]; exact netClosed_obs dy _ _ _ m

theorem runNet_pendLines (dy : Cal.Instant → Nat) (m : Machine) : pendLines (runNet dy m).1 = pendLines m := by
  unfold pendLines; rw [(runNet_keeps dy m).1]

theorem runNet_energy (dy : Cal.Instant → Nat) (m : Machine) : (runNet dy m).2.filterMap Effect.energyOf? = [] :=
  (runNet_obs dy m).1

theorem runNet_duration (dy : Cal.Instant → Nat) (m : Machine) : (runNet dy m).2.filterMap Effect.durationOf? = [] :=
  (runNet_obs dy m).2.1

theorem runNet_machines (dy : Cal.Instant → Nat) (m : Machine) : (runNet dy m).2.filterMap Effect.machineOf? = [] :=
  (runNet_obs dy m).2.2

theorem settle_fx_obs (dy : Cal.Instant → Nat) (m : Machine) :
    (settle dy m).2.filterMap Effect.energyOf? = [] ∧ (settle dy m).2.filterMap Effect.durationOf? = [] ∧
    (settle dy m).2.filterMap Effect.machineOf? = [] := by
  unfold settle; split
  · exact redraw_obs dy _ _ _
  · exact ⟨rfl, rfl, rfl⟩

theorem settle_energy (dy : Cal.Instant → Nat) (m : Machine) : (settle dy m).2.filterMap Effect.energyOf? = [] :=
  (settle_fx_obs dy m).1
theorem settle_duration (dy : Cal.Instant → Nat) (m : Machine) : (settle dy m).2.filterMap Effect.durationOf? = [] :=
  (settle_fx_obs dy m).2.1
theorem settle_machines (dy : Cal.Instant → Nat) (m : Machine) : (settle dy m).2.filterMap Effect.machineOf? = [] :=
  (settle_fx_obs dy m).2.2

theorem closePause_obs (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    (closePause dy m t).2.filterMap Effect.energyOf? = [] ∧ (closePause dy m t).2.filterMap Effect.durationOf? = [] ∧
    (closePause dy m t).2.filterMap Effect.machineOf? = [] := by
  unfold closePause; repeat' split
  all_goals simp [Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]

/-- **A break's machine keeps the last cut, the interruption and the pending observation** (D87): it moves only the
open block's drawing (`settle`, D99). -/
theorem brkFx_machine (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) :
    ∀ m' ∈ (brkFx dy m t e d).filterMap Effect.machineOf?,
      m'.lastCut.map (fun c => (c.id, c.t, c.day)) = m.lastCut.map (fun c => (c.id, c.t, c.day)) ∧
        m'.interrupt = m.interrupt ∧ m'.block.bind (·.obs) = m.block.bind (·.obs) := by
  intro m' hm
  unfold brkFx at hm
  simp only [List.filterMap_append, (settle_fx_obs dy _).2.2, (netClosed_obs dy _ _ _ _).2.2, List.nil_append,
    List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
  subst hm
  obtain ⟨h1, h2, -, -, -⟩ := settle_keeps dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }
  obtain ⟨k1, k2, -, -, k5⟩ := netClosed_keeps dy t e d
    (settle dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).1
  exact ⟨by rw [k5, h1], by rw [k2, h2], by rw [k1, settle_obs]⟩


/-- **A `break` line's machine after its give-back keeps the last cut's stamp, the interruption and the pending
observation** (the owner's D137): `brkFx_machine` over the give-back's machine, which moves neither (`giveBack_keeps`). -/
theorem giveBack_brkFx_machine (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) :
    ∀ m' ∈ (brkFx dy (giveBack dy m).1 t e d).filterMap Effect.machineOf?,
      m'.lastCut.map (fun c => (c.id, c.t, c.day)) = m.lastCut.map (fun c => (c.id, c.t, c.day)) ∧
        m'.interrupt = m.interrupt ∧ m'.block.bind (·.obs) = m.block.bind (·.obs) := by
  intro m' hm
  obtain ⟨h1, h2, h3⟩ := brkFx_machine dy _ t e d m' hm
  obtain ⟨k1, k2, -, -, -, k6⟩ := giveBack_keeps dy m
  exact ⟨h1.trans k6, h2.trans k2, by rw [h3, k1]⟩

/-- **A break's block family half observes nothing** (D87): no energy and no duration observation. -/
theorem brkFx_obs (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) :
    (brkFx dy m t e d).filterMap Effect.energyOf? = [] ∧ (brkFx dy m t e d).filterMap Effect.durationOf? = [] := by
  unfold brkFx
  obtain ⟨a1, a2, -⟩ := settle_fx_obs dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }
  obtain ⟨n1, n2, -⟩ := netClosed_obs dy t e d
    (settle dy { m with brks := pruneBrks (⟨t, e, d⟩ :: m.brks), brkOpen := none }).1
  simp [List.filterMap_append, a1, a2, n1, n2, Effect.energyOf?, Effect.durationOf?]

/-- **A break's machine holds it** (the owner's D92, README gap 4241; D94): every machine `brkFx` writes holds the
breaks held before with this one at their head, pruned to `maxKeepDays` ledger days of the newest (`pruneBrks`),
whether a clock ran or not. -/
theorem brkFx_brk (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) :
    ∀ m' ∈ (brkFx dy m t e d).filterMap Effect.machineOf?, m'.brks = pruneBrks (⟨t, e, d⟩ :: m.brks) := by
  intro m' hm
  unfold brkFx at hm
  simp only [List.filterMap_append, (settle_fx_obs dy _).2.2, (netClosed_obs dy _ _ _ _).2.2, List.nil_append,
    List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
  subst hm
  rw [(netClosed_keeps dy _ _ _ _).2.2.1]
  exact (settle_keeps dy _).2.2.1

/-- **A break line ends the running break** (the owner's D105, parity P100): every machine `brkFx` writes has none,
whatever break a `break_start` opened before it — the pair is matched in file order. -/
theorem brkFx_brkOpen (dy : Cal.Instant → Nat) (m : Machine) (t e : At) (d : Nat) :
    ∀ m' ∈ (brkFx dy m t e d).filterMap Effect.machineOf?, m'.brkOpen = none := by
  intro m' hm
  unfold brkFx at hm
  simp only [List.filterMap_append, (settle_fx_obs dy _).2.2, (netClosed_obs dy _ _ _ _).2.2, List.nil_append,
    List.filterMap_cons, Effect.machineOf?, List.filterMap_nil, List.mem_singleton] at hm
  subst hm
  rw [(netClosed_keeps dy _ _ _ _).2.2.2.1]
  exact (settle_keeps dy _).2.2.2.1

theorem creditFx_obs (dy : Cal.Instant → Nat) (id : Id) (t : At) (min : Nat) (ci : Option U8) :
    (creditFx dy id t min ci).filterMap Effect.energyOf? = [] ∧ (creditFx dy id t min ci).filterMap Effect.durationOf? = [] ∧
    (creditFx dy id t min ci).filterMap Effect.machineOf? = [] := by
  simp [creditFx, Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]

theorem uncreditFx_obs (c : Cut) :
    (uncreditFx c).filterMap Effect.energyOf? = [] ∧ (uncreditFx c).filterMap Effect.durationOf? = [] ∧
    (uncreditFx c).filterMap Effect.machineOf? = [] := by
  unfold uncreditFx; split <;> simp [Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]

theorem obsFx_obs (o : Option EnergyObs) :
    ((obsFx o).filterMap Effect.energyOf?) = o.toList ∧ (obsFx o).filterMap Effect.durationOf? = [] ∧
    (obsFx o).filterMap Effect.machineOf? = [] := by
  cases o <;> simp [obsFx, Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]

/-- **A cut emits the pending observation**, and leaves no block. -/
theorem cut_obs (dy : Cal.Instant → Nat) (m : Machine) (t : At) :
    ((cut dy m t).2.filterMap Effect.energyOf?).map (·.line) = pendLines m ∧
    (cut dy m t).2.filterMap Effect.durationOf? = [] ∧ (cut dy m t).2.filterMap Effect.machineOf? = [] ∧
    pendLines (cut dy m t).1 = [] := by
  obtain ⟨b1, b2, b3⟩ := closePause_obs dy m t
  unfold cut
  split
  · rename_i b hb
    have hp : pendLines m = (b.obs.map (·.line)).toList := by
      unfold pendLines; rw [hb]; rfl
    obtain ⟨a1, a2, a3⟩ := redraw_obs dy b.id b.drawn (cutPieces b m t)
    obtain ⟨c1, c2, c3⟩ := creditFx_obs dy b.id t (minutesOf (cutPieces b m t)) none
    obtain ⟨d1, d2, d3⟩ := obsFx_obs b.obs
    simp only [List.filterMap_append, a1, a2, a3, b1, b2, b3, c1, c2, c3, d1, d2, d3, List.nil_append, hp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases b.obs <;> rfl
    all_goals first | rfl | trivial
  · rename_i hb
    have hp : pendLines m = [] := by unfold pendLines; rw [hb]; rfl
    refine ⟨?_, rfl, rfl, ?_⟩
    · simp [hp]
    · exact hp

/-- **A `done` closing its block emits the pending observation** (with `went`); otherwise nothing is emitted and
the pending observation stays. -/
theorem doneClose_obs (dy : Cal.Instant → Nat) (m : Machine) (t : At) (id : Id) (actual : Nat) (went : Option U8) :
    ((doneClose dy m t id actual went).2.filterMap Effect.energyOf?).map (·.line) ++ pendLines (doneClose dy m t id actual went).1
      = pendLines m ∧
    (doneClose dy m t id actual went).2.filterMap Effect.durationOf? = [] ∧
    (doneClose dy m t id actual went).2.filterMap Effect.machineOf? = [] := by
  obtain ⟨b1, b2, b3⟩ := closePause_obs dy m t
  unfold doneClose
  split
  · rename_i b hb
    split
    · obtain ⟨a1, a2, a3⟩ := redraw_obs dy b.id b.drawn (cutPieces b m t)
      obtain ⟨d1, d2, d3⟩ := obsFx_obs (b.obs.map (wentOn went))
      have hp : pendLines m = (b.obs.map (·.line)).toList := by unfold pendLines; rw [hb]; rfl
      simp only [List.filterMap_append, a1, a2, a3, b1, b2, b3, d1, d2, d3, List.nil_append, hp]
      refine ⟨?_, ?_, ?_⟩
      · have hw : ∀ o : EnergyObs, (wentOn went o).line = o.line := fun o => by cases went <;> rfl
        cases b.obs with
        | none => rfl
        | some o => simp [pendLines, hw]
      all_goals first | rfl | trivial
    · exact ⟨by simp, rfl, rfl⟩
  · split
    · split
      · obtain ⟨u1, u2, u3⟩ := uncreditFx_obs _
        refine ⟨?_, u2, u3⟩
        simp only [u1, List.map_nil, List.nil_append]
        rfl
      · exact ⟨by simp, rfl, rfl⟩
    · exact ⟨by simp, rfl, rfl⟩

theorem doneFx_obs (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id)
    (est actual : Nat) (went : Option U8) (tags : List (List Char)) (ci : U8) (isPartial : Bool) :
    ((doneFx dy m line t d id est actual went tags ci isPartial).filterMap Effect.energyOf?).map (·.line) ++
      pendLines (((doneFx dy m line t d id est actual went tags ci isPartial).filterMap Effect.machineOf?).getLast?.getD m)
      = pendLines m ∧
    List.Sublist (((doneFx dy m line t d id est actual went tags ci isPartial).filterMap Effect.durationOf?).map (·.line)) [line] := by
  obtain ⟨h1, h2, h3⟩ := doneClose_obs dy m t id actual went
  obtain ⟨c1, c2, c3⟩ := creditFx_obs dy id t actual (some ci)
  unfold doneFx
  by_cases ha : 0 < actual <;> by_cases hp : isPartial = true <;>
    simp only [ha, hp, if_true, if_false, List.filterMap_cons, List.filterMap_append, List.filterMap_nil,
      Effect.machineOf?, Effect.energyOf?, Effect.durationOf?, h2, h3, c1, c2, c3, List.nil_append, List.append_nil,
      List.getLast?_singleton, Option.getD_some, Bool.false_eq_true, runNet_energy, runNet_duration, runNet_machines,
      runNet_pendLines] <;>
    exact ⟨h1, by simp⟩

theorem dayArm_obs (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (e : Entry) (t : At) (d : Nat) :
    (dayArm dy sl e t d).filterMap Effect.machineOf? = [] ∧ (dayArm dy sl e t d).filterMap Effect.durationOf? = [] ∧
    List.Sublist (((dayArm dy sl e t d).filterMap Effect.energyOf?).map (·.line)) [e.line] := by
  unfold dayArm
  split <;> (repeat' split) <;> simp [Effect.machineOf?, Effect.durationOf?, Effect.energyOf?]

/-- **Settling keeps what is pending** (D99). -/
theorem settle_pendLines (dy : Cal.Instant → Nat) (m : Machine) : pendLines (settle dy m).1 = pendLines m := by
  unfold pendLines; rw [settle_obs]

/-- **A settle and one machine after it observe nothing, and leave what was pending** (D99): the shape every arm that
moves the open block's drawing ends with. -/
theorem settle_then_machine_obs (dy : Cal.Instant → Nat) (m0 : Machine) (pre : List Effect)
    (h1 : pre.filterMap Effect.energyOf? = []) (h2 : pre.filterMap Effect.durationOf? = [])
    (h3 : pre.filterMap Effect.machineOf? = []) :
    ((pre ++ (settle dy m0).2 ++ [Effect.machine (settle dy m0).1]).filterMap Effect.energyOf?) = [] ∧
    ((pre ++ (settle dy m0).2 ++ [Effect.machine (settle dy m0).1]).filterMap Effect.durationOf?) = [] ∧
    pendLines (((pre ++ (settle dy m0).2 ++ [Effect.machine (settle dy m0).1]).filterMap Effect.machineOf?).getLast?.getD m0)
      = pendLines m0 := by
  obtain ⟨a1, a2, a3⟩ := settle_fx_obs dy m0
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.durationOf?,
    Effect.machineOf?, h1, h2, h3, a1, a2, a3, List.nil_append, List.append_nil, List.getLast?_singleton,
    Option.getD_some]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl | exact settle_pendLines dy m0

/-- **A late break's netting keeps the open block's pending observation** (the owner's D100). -/
theorem netClosed_pendLines (dy : Cal.Instant → Nat) (s e : At) (dd : Nat) (m : Machine) :
    pendLines (netClosed dy s e dd m).1 = pendLines m := by
  unfold pendLines; rw [(netClosed_keeps dy s e dd m).1]

/-- **A late start's cut keeps the open block's pending observation** (the owner's D115). -/
theorem netStart_pendLines (dy : Cal.Instant → Nat) (t : At) (dd : Nat) (m : Machine) :
    pendLines (netStart dy t dd m).1 = pendLines m := by
  unfold pendLines; rw [(netStart_keeps dy t dd m).1]

/-- **A break ended at a start observes nothing and writes no machine** (D129). -/
theorem endRecs_obs (o : OpenBrk) (t : At) :
    (endRecs o t).filterMap Effect.energyOf? = [] ∧ (endRecs o t).filterMap Effect.durationOf? = [] ∧
    (endRecs o t).filterMap Effect.machineOf? = [] := ⟨rfl, rfl, rfl⟩

/-- **A `break_start` a held start ends observes nothing and writes one machine** (D129, the one `brkFx` writes). -/
theorem endBrkFx_obs (dy : Cal.Instant → Nat) (m : Machine) (o : OpenBrk) (t : At) :
    (endBrkFx dy m o t).filterMap Effect.energyOf? = [] ∧ (endBrkFx dy m o t).filterMap Effect.durationOf? = [] ∧
    (endBrkFx dy m o t).filterMap Effect.machineOf? =
      [(netClosed dy o.s t o.day (settle dy { { m with brkEnded := some o.s } with
        brks := pruneBrks (⟨o.s, t, o.day⟩ :: m.brks), brkOpen := none }).1).1] := by
  unfold endBrkFx brkFx endRecs
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.durationOf?,
    Effect.machineOf?, settle_energy, settle_duration, settle_machines, (netClosed_obs dy _ _ _ _).1,
    (netClosed_obs dy _ _ _ _).2.1, (netClosed_obs dy _ _ _ _).2.2, List.nil_append, List.append_nil]
  simp

/-- **A start ending a running break writes its own arm's machines alone** (D129): the break's segment and record write
none. -/
theorem startEnds_mem (dy : Cal.Instant → Nat) (m : Machine) (o : OpenBrk) (line : Nat) (t : At) (d : Nat)
    (id : Id) (pred : U8) (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) (m' : Machine)
    (hm : m' ∈ (endRecs o t ++ startArm dy (endMachine m o t) line t d id pred rep hsw sleptMin loc).filterMap
      Effect.machineOf?) :
    m' ∈ (startArm dy (endMachine m o t) line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf? := by
  rwa [List.filterMap_append, (endRecs_obs o t).2.2, List.nil_append] at hm

/-- **A `break_start` a held start ends writes one machine, the one `brkFx` writes** (D129). -/
theorem endBrkFx_mem (dy : Cal.Instant → Nat) (m : Machine) (o : OpenBrk) (t : At) (m' : Machine)
    (hm : m' ∈ (endBrkFx dy m o t).filterMap Effect.machineOf?) :
    m' ∈ (brkFx dy { m with brkEnded := some o.s } o.s t o.day).filterMap Effect.machineOf? := by
  unfold endBrkFx endRecs at hm
  rw [List.filterMap_append] at hm
  simpa [Effect.machineOf?] using hm

/-- **A start's arm writes one machine** (C3): the block it opens, settled. -/
theorem startArm_machines (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id) (pred : U8)
    (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) :
    (startArm dy m line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf? =
      [(settle dy (startedMachine (runNet dy (cut dy (netStart dy t d m).1 t).1).1 id t d
        (rep.map (fun rp => ⟨line, t, d, pred, rp, hsw, loc, some sleptMin.val, none, some id, true⟩)))).1] := by
  unfold startArm
  simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.machineOf?,
    (cut_obs dy _ t).2.2.1, settle_machines, (netStart_obs dy _ _ _).2.2, runNet_machines, List.nil_append,
    List.append_nil]

/-- **A start's arm emits what was pending, and at most its own observation, on its own line** (C3). -/
theorem startArm_obs (dy : Cal.Instant → Nat) (m : Machine) (line : Nat) (t : At) (d : Nat) (id : Id) (pred : U8)
    (rep : Option U8) (hsw : Num) (sleptMin : U32) (loc : List Char) :
    ∃ X : List Nat, List.Sublist X [line] ∧
      (((startArm dy m line t d id pred rep hsw sleptMin loc).filterMap Effect.energyOf?).map (·.line) ++
        pendLines (((startArm dy m line t d id pred rep hsw sleptMin loc).filterMap Effect.machineOf?).getLast?.getD m)).Perm
          (pendLines m ++ X) ∧
      List.Sublist (((startArm dy m line t d id pred rep hsw sleptMin loc).filterMap Effect.durationOf?).map (·.line))
        [line] := by
  unfold startArm
  obtain ⟨c1, c2, c3, c4⟩ := cut_obs dy (netStart dy t d m).1 t
  rw [netStart_pendLines] at c1
  refine ⟨(rep.map (fun _ => line)).toList, ?_, ?_, ?_⟩
  · cases rep <;> simp
  · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?,
      c3, List.append_nil, c1, settle_energy, settle_machines, List.nil_append, List.getLast?_singleton,
      Option.getD_some, settle_pendLines, (netStart_obs dy _ _ _).1, (netStart_obs dy _ _ _).2.2, runNet_energy,
      runNet_machines]
    refine List.Perm.append_left _ ?_
    unfold pendLines
    cases rep <;> exact List.Perm.refl _
  · simp [List.filterMap_append, List.filterMap_cons, c2, settle_duration, Effect.durationOf?,
      (netStart_obs dy _ _ _).2.1, runNet_duration]

/-- **Each machine arm emits what was pending, and at most one new observation, on its own line.** -/
theorem arm_obs (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    ∃ X : List Nat, List.Sublist X [e.line] ∧
      (((arm dy sl m e t d).filterMap Effect.energyOf?).map (·.line) ++
        pendLines (((arm dy sl m e t d).filterMap Effect.machineOf?).getLast?.getD m)).Perm (pendLines m ++ X) ∧
      List.Sublist (((arm dy sl m e t d).filterMap Effect.durationOf?).map (·.line)) [e.line] := by
  unfold arm
  cases hev : e.ev <;> simp only
  case start id pred rep hsw sleptMin loc _ _ =>
    split
    · rename_i o _
      obtain ⟨X, h1, h2, h3⟩ := startArm_obs dy (endMachine m o t) e.line t d id pred rep hsw sleptMin loc
      obtain ⟨g1, g2, g3⟩ := endRecs_obs o t
      rw [startArm_machines] at h2
      refine ⟨X, h1, ?_, ?_⟩
      · rw [List.filterMap_append, List.filterMap_append, g1, g3, startArm_machines, List.nil_append, List.nil_append]
        simpa [pendLines, endMachine] using h2
      · rw [List.filterMap_append, g2, List.nil_append]; exact h3
    · exact startArm_obs dy m e.line t d id pred rep hsw sleptMin loc
  case pause id =>
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · split
      · split
        · rename_i b hb _
          simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?,
            Effect.machineOf?, settle_energy, settle_machines, List.nil_append, List.map_nil, List.getLast?_singleton,
            Option.getD_some, List.append_nil, settle_pendLines]
          unfold pendLines
          rw [hb]
          exact List.Perm.refl _
        · simp
      · simp
    · split
      · split
        · simp [List.filterMap_append, settle_duration, Effect.durationOf?]
        · simp
      · simp
  case unpause id =>
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · split
      · split
        · obtain ⟨a1, a2, a3⟩ := closePause_obs dy m t
          simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?,
            Effect.machineOf?, a1, a3, settle_energy, settle_machines, List.nil_append, List.map_nil,
            List.getLast?_singleton, Option.getD_some, List.append_nil, settle_pendLines]
          have hp := closePauseM_pending m t
          unfold pendLines
          rw [← hp]
          cases (closePauseM m t).block <;> exact List.Perm.refl _
        · simp
      · simp
    · split
      · split
        · simp [List.filterMap_append, (closePause_obs dy m t).2.1, settle_duration, Effect.durationOf?]
        · simp
      · simp
  case interrupt id =>
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · obtain ⟨a1, a2, a3⟩ := closePause_obs dy m t
      simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?,
        a1, a3, settle_energy, settle_machines, List.nil_append, List.map_nil, List.getLast?_singleton,
        Option.getD_some, List.append_nil, settle_pendLines]
      have e2 := closePauseM_pending m t
      unfold pendLines interruptMachine
      split <;> simp only [e2] <;> exact List.Perm.refl _
    · simp [List.filterMap_append, (closePause_obs dy m t).2.1, settle_duration, Effect.durationOf?]
  case resume lost dropped =>
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · split
      · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?,
          Effect.machineOf?, settle_energy, settle_machines, List.map_nil, List.nil_append, List.getLast?_singleton,
          Option.getD_some, List.append_nil, settle_pendLines, (netClosed_obs dy _ _ _ _).1,
          (netClosed_obs dy _ _ _ _).2.2, netClosed_pendLines]
        unfold pendLines
        cases m.block <;> simp [resumeBlock_obs]
      · simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?,
          Effect.machineOf?, settle_energy, settle_machines, List.map_nil, List.nil_append, List.getLast?_singleton,
          Option.getD_some, List.append_nil, settle_pendLines]
        unfold pendLines
        cases m.block <;> simp [resumeBlock_obs]
    · split <;> simp [List.filterMap_append, List.filterMap_cons, settle_duration, Effect.durationOf?,
        (netClosed_obs dy _ _ _ _).2.1]
  case stop id rem =>
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · split
      · split
        · obtain ⟨c1, c2, c3, c4⟩ := cut_obs dy m t
          simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?,
            c3, List.append_nil, c1, List.nil_append, List.getLast?_singleton, Option.getD_some, c4, runNet_energy,
            runNet_machines, runNet_pendLines]
          exact List.Perm.refl _
        · simp
      · simp
    · split
      · split
        · simp [List.filterMap_append, (cut_obs dy m t).2.1, Effect.durationOf?, runNet_duration]
        · simp
      · simp
  case extend id by_ =>
    -- D108: at most one machine, its block's pending observation untouched.
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · unfold extendFx
      split
      · split
        · rename_i b hb _
          simp [List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?, pendLines, hb]
        · simp [List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?]
      · simp [List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?]
    · unfold extendFx
      split
      · split <;> simp [Effect.durationOf?]
      · simp [Effect.durationOf?]
  case brkStart planned where_ =>
    -- D105: one machine, its block (and so its pending observation) untouched; D129: ending it at a held start, the
    -- same.
    refine ⟨[], List.nil_sublist _, ?_, ?_⟩
    · split
      · obtain ⟨g1, -, g3⟩ := endBrkFx_obs dy m ⟨t, planned.val, where_, d⟩ _
        rw [g1, g3]
        simp only [List.map_nil, List.nil_append, List.getLast?_singleton, Option.getD_some, netClosed_pendLines,
          settle_pendLines, List.append_nil]
        exact List.Perm.refl _
      · unfold brkStartArm
        simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?,
          settle_energy, settle_machines, runNet_energy, runNet_machines, List.nil_append, List.append_nil,
          List.getLast?_singleton, Option.getD_some, runNet_pendLines, settle_pendLines, List.map_nil]
        exact List.Perm.refl _
    · split
      · rw [(endBrkFx_obs dy m _ _).2.1]; exact List.nil_sublist _
      · unfold brkStartArm
        simp [List.filterMap_append, List.filterMap_cons, settle_duration, runNet_duration, Effect.durationOf?]
  case done id est actual went tags ci isPartial =>
    obtain ⟨h1, h2⟩ := doneFx_obs dy m e.line t d id est.val actual.val went tags ci isPartial
    exact ⟨[], List.nil_sublist _, by rw [h1]; simp, h2⟩
  case brk planned actual where_ =>
    have hb : ∃ X : List Nat, List.Sublist X [e.line] ∧
        (((brkArm dy sl m e t d planned.val (actual.map (·.val))).filterMap Effect.energyOf?).map (·.line) ++
          pendLines (((brkArm dy sl m e t d planned.val (actual.map (·.val))).filterMap Effect.machineOf?).getLast?.getD
            m)).Perm (pendLines m ++ X) ∧
        List.Sublist (((brkArm dy sl m e t d planned.val (actual.map (·.val))).filterMap Effect.durationOf?).map
          (·.line)) [e.line] := by
      obtain ⟨g1, g2, g3⟩ := dayArm_obs dy sl (placed m e) t d
      rw [placed_line] at g3
      refine ⟨((dayArm dy sl (placed m e) t d).filterMap Effect.energyOf?).map (·.line), g3, ?_, ?_⟩
      · unfold brkArm brkFx
        simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?,
          settle_energy, settle_machines, g1, List.nil_append, List.append_nil, List.getLast?_singleton,
          Option.getD_some, (netClosed_obs dy _ _ _ _).1, (netClosed_obs dy _ _ _ _).2.2, netClosed_pendLines,
          settle_pendLines, (giveBack_obs dy _).1, (giveBack_obs dy _).2.2]
        unfold pendLines
        simp only [(giveBack_keeps dy m).1]
        exact List.perm_append_comm
      · unfold brkArm brkFx
        simp only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Effect.durationOf?, settle_duration,
          (netClosed_obs dy _ _ _ _).2.1, g2, List.append_nil, List.map_nil, (giveBack_obs dy _).2.1]
        exact List.nil_sublist _
    split
    · split
      · refine ⟨[], List.nil_sublist _, ?_, ?_⟩
        · simp only [List.filterMap_cons, List.filterMap_nil, Effect.energyOf?, Effect.machineOf?, List.map_nil,
            List.nil_append, List.getLast?_singleton, Option.getD_some, List.append_nil]
          exact List.Perm.refl _
        · simp [Effect.durationOf?]
      · exact hb
    · exact hb
  all_goals
    obtain ⟨g1, g2, g3⟩ := dayArm_obs dy sl e t d
    exact ⟨_, g3, by rw [g1]; exact List.perm_append_comm, by rw [g2]; exact List.nil_sublist _⟩

theorem completionCore_obs (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) :
    (completionCore z e t d).filterMap Effect.energyOf? = [] ∧ (completionCore z e t d).filterMap Effect.durationOf? = [] ∧
    (completionCore z e t d).filterMap Effect.machineOf? = [] := by
  unfold completionCore
  split <;> (repeat' split) <;> simp [Effect.energyOf?, Effect.durationOf?, Effect.machineOf?]

theorem completionArm_obs (z : Cal.Tz) (m : Machine) (e : Entry) (t : At) (d : Nat) :
    (completionArm z m e t d).filterMap Effect.energyOf? = [] ∧
    (completionArm z m e t d).filterMap Effect.durationOf? = [] ∧
    (completionArm z m e t d).filterMap Effect.machineOf? = [] := by
  obtain ⟨c1, c2, c3⟩ := completionCore_obs z e t d
  unfold completionArm
  rw [List.filterMap_append, List.filterMap_append, List.filterMap_append, c1, c2, c3,
    lateWarns_filterMap Effect.energyOf? (fun _ => rfl), lateWarns_filterMap Effect.durationOf? (fun _ => rfl),
    lateWarns_filterMap Effect.machineOf? (fun _ => rfl)]
  exact ⟨rfl, rfl, rfl⟩

theorem stepWith_obs (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (st : State) (e : Entry) :
    ∃ X D : List Nat, List.Sublist X [e.line] ∧ List.Sublist D [e.line] ∧ (obsLines (stepWith z dy sl st e)).Perm (obsLines st ++ X) ∧
      ((stepWith z dy sl st e).durations.map (·.line)).reverse = (st.durations.map (·.line)).reverse ++ D := by
  obtain ⟨X, hX, hp, hd⟩ := arm_obs dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)
  obtain ⟨c1, c2, c3⟩ := completionArm_obs z st.machine e (e.t.val, e.off.val) (dy e.t.val)
  obtain ⟨h1, h2, h3⟩ := applyEffects_obs (effectsWith z dy sl st e) st
  refine ⟨X, _, hX, hd, ?_, ?_⟩
  · unfold obsLines stepWith
    rw [h1, h3]
    unfold effectsWith
    simp only [List.filterMap_cons, List.filterMap_append, Effect.energyOf?, Effect.machineOf?, c1, c3, List.append_nil]
    rw [List.map_append, List.map_reverse]
    have := (List.perm_append_comm (l₁ := (List.map (·.line) (List.filterMap Effect.energyOf? (arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val)))).reverse)
      (l₂ := st.energy.map (·.line))).append_right
      (pendLines ((List.filterMap Effect.machineOf? (arm dy sl st.machine e (e.t.val, e.off.val) (dy e.t.val))).getLast?.getD st.machine))
    refine this.trans ?_
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ (((List.reverse_perm _).append_right _).trans hp)
  · unfold stepWith
    rw [h2]
    unfold effectsWith
    simp only [List.filterMap_cons, List.filterMap_append, Effect.durationOf?, c2, List.append_nil, List.map_append,
      List.map_reverse, List.reverse_append, List.reverse_reverse]

theorem foldl_stepWith_obs (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (l : List Entry) (st : State), ∃ Y D : List Nat, List.Sublist Y (l.map (·.line)) ∧ List.Sublist D (l.map (·.line)) ∧
      (obsLines (l.foldl (stepWith z dy sl) st)).Perm (obsLines st ++ Y) ∧
      ((l.foldl (stepWith z dy sl) st).durations.map (·.line)).reverse = (st.durations.map (·.line)).reverse ++ D
  | [], st => ⟨[], [], List.nil_sublist _, List.nil_sublist _, by simp, by simp⟩
  | e :: l, st => by
    obtain ⟨X, D₁, hX, hD₁, hp₁, hd₁⟩ := stepWith_obs z dy sl st e
    obtain ⟨Y, D₂, hY, hD₂, hp₂, hd₂⟩ := foldl_stepWith_obs z dy sl l (stepWith z dy sl st e)
    refine ⟨X ++ Y, D₁ ++ D₂, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons]; exact (hX.append hY).trans (by simp)
    · rw [List.map_cons]; exact (hD₁.append hD₂).trans (by simp)
    · rw [List.foldl_cons]
      exact hp₂.trans (by rw [← List.append_assoc]; exact hp₁.append_right Y)
    · rw [List.foldl_cons, hd₂, hd₁, List.append_assoc]

theorem sublist_nodup_of_pairwise_lt {l : List Nat} (h : l.Pairwise (· < ·)) {Y : List Nat} (hY : List.Sublist Y l) : Y.Nodup :=
  (h.sublist hY).imp (fun hab => Nat.ne_of_lt hab)

theorem survivors_lines_pairwise (es : List Entry) (hl : Log.linesIncreasing es = true) :
    ((survivors es).map (·.line)).Pairwise (· < ·) := by
  rw [survivors_are_the_uncancelled_entries, List.map_map, List.pairwise_map]
  have hp := Log.linesIncreasing_pairwise es hl
  have hs : List.Sublist ((es.zipIdx.filter (fun p => !cancelledAt es p.2)).map Prod.fst) es := by
    have : es.zipIdx.map Prod.fst = es := by simp
    conv => rhs; rw [← this]
    exact List.Sublist.map _ List.filter_sublist
  have := hp.sublist hs
  rw [List.pairwise_map] at this
  exact this

/-- **Refuted: §15's `observations_are_in_file_order` over every list of entries.**  A list holding one `energy`
entry twice (as no reader builds: the log op's entries have strictly increasing lines,
`the_tail_entries_have_increasing_lines`) replays to two observations on one line, which are not strictly
increasing.  The law holds on increasing lines: `observations_are_in_file_order_on_increasing_lines`. -/
theorem observations_are_not_in_file_order_when_a_line_repeats :
    ∃ es : List Entry, ¬ ((replay utcZone es).energy.map (·.line)).Pairwise (· < ·) := by
  refine ⟨[⟨1, ⟨⟨63924368400, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩, .energy 3 4 (.nat 2) ['h']⟩,
    ⟨1, ⟨⟨63924368400, 0⟩, by decide⟩, ⟨⟨false, 0⟩, by decide⟩, .energy 3 4 (.nat 2) ['h']⟩], ?_⟩
  decide

/-- **Observations are in file order** (§11.2, §15 restated on increasing lines, Goals): over a log whose lines
strictly increase (every list the log op builds, `the_tail_entries_have_increasing_lines`), the replay's energy
observations, a start's carrying its start's line, and its duration observations are in strictly increasing line
order, so Rust's sort by line is the fork's push order. -/
theorem observations_are_in_file_order_on_increasing_lines (z : Cal.Tz) (es : List Entry)
    (hl : Log.linesIncreasing es = true) :
    ((replay z es).energy.map (·.line)).Pairwise (· < ·) ∧
    ((replay z es).durations.map (·.line)).Pairwise (· < ·) := by
  have hsv := survivors_lines_pairwise es hl
  obtain ⟨Y, D, hY, hD, hp, hd⟩ :=
    foldl_stepWith_obs z (dayOf z (dayIndexOf z es)) (slOf z es) (survivors es) (State.init es.length)
  rw [replay_state]
  unfold finish
  simp only
  constructor
  · generalize hst : (survivors es).foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) (State.init es.length) = st at hp
    have hinit : obsLines (State.init es.length) = [] := rfl
    rw [hinit, List.nil_append] at hp
    have hnd : (obsLines st).Nodup := hp.nodup_iff.2 (sublist_nodup_of_pairwise_lt hsv hY)
    have hperm : ((sortObs (st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList)).map (·.line)).Perm (obsLines st) := by
      refine ((insSort_perm obsLe _).map _).trans ?_
      unfold obsLines pendLines
      rw [List.map_append, List.map_reverse]
      refine ((List.reverse_perm _).append_right _).trans ?_
      cases st.machine.block.bind (·.obs) <;> simp
    have hsorted : ((sortObs (st.energy.reverse ++ (st.machine.block.bind (·.obs)).toList)).map (·.line)).Pairwise (· ≤ ·) := by
      unfold sortObs
      rw [insSort_eq_mergeSort obsLe (fun a b c h₁ h₂ => by simp [obsLe] at *; omega) (fun a b => by simp [obsLe]; omega)]
      rw [List.pairwise_map]
      exact (List.pairwise_mergeSort (fun a b c h₁ h₂ => by simp [obsLe] at *; omega) (fun a b => by simp [obsLe]; omega) _).imp
        (fun h => by simpa [obsLe] using h)
    have hnd' := hperm.nodup_iff.2 hnd
    exact (hsorted.and hnd').imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  · rw [map_line_netDur]
    have hinit : ((State.init es.length).durations.map (·.line)).reverse = [] := rfl
    rw [hinit, List.nil_append] at hd
    have hr : (((survivors es).foldl (stepWith z (dayOf z (dayIndexOf z es)) (slOf z es)) (State.init es.length)).durations.reverse.map (·.line)) = D := by
      rw [List.map_reverse, hd]
    rw [hr]
    exact hsv.sublist hD

/-! ### The view (§8.4): every reading as a total query -/

/-- **A replayed log** (§8.4's "view"): the facts, every entry's header in file order, and the entry count (fork
`Replay::entry_count`, `tm log`'s `total`). -/
structure Doc where
  facts : Facts
  headers : List (Nat × HeaderRec)
  entryCount : Nat

/-- **The replay of a log with its line bookkeeping** (W1's laws read it through `ask`). -/
def replayDoc (z : Cal.Tz) (es : List Entry) : Doc := ⟨replay z es, entryHeaders z es, es.length⟩

/-- **The compiled `replayDoc`**: the undo mask computed once and read twice (the survivors and every header's
bit), the day index built once and bisected for the replay and for every header. -/
def replayDocFast (z : Cal.Tz) (es : List Entry) : Doc :=
  let dead := maskFast es
  let sv := (es.zipIdx.filter (fun p => !deadAt dead p.2)).map Prod.fst
  let a := (keptWakes z (wakeInstants sv)).toArray
  let dy := dayOfArr z a
  let sm := sleptMap dy sv es.length
  ⟨finish (sv.foldl (stepWith z dy (fun d => sm.get d)) (State.init es.length)),
   es.zipIdx.map (fun p => (dy p.1.t.val, HeaderRec.of p.1 (deadAt dead p.2))), es.length⟩

@[csimp] theorem replayDoc_eq_replayDocFast : @replayDoc = @replayDocFast := by
  funext z es
  unfold replayDoc
  rw [replay_eq_replayFast, entryHeaders_eq_entryHeadersFast]
  unfold replayFast entryHeadersFast dayIndexOf
  rw [survivors_eq_survivorsFast]
  rfl


/-- A reading of one day (O, and DR once sealed). -/
inductive DayQ
  | record
  | seam
  | energy
  | durations
  | interrupts
  | demotions
  | closes
  | headers
deriving DecidableEq, Repr

/-- A reading of one date's window facts (W, and WR once sealed). -/
inductive WinQ
  | itemMin (i : Id)
  | done (i : Id)
  | inst (item inst : List Char)
deriving DecidableEq, Repr

/-- **A query** (§8.4's rows, one per reading).  `day` and `win` name a date; the rest are all-time (A). -/
inductive Q
  | day (d : Nat) (q : DayQ)
  | win (d : Nat) (q : WinQ)
  | item (i : Id)
  | lastDone (i : Id)
  | doneFirst (i : Id)
  | doneCount (i : Id)
  | dropped (i : Id)
  | instOther (item inst : List Char)
  | named (name : List Char) (id : Option Id)
  | openBlock
  | openInterrupt
  | openBreak
  | lastDay
  | lastEffective
  | unknown
  | longestLeak
  | replayWarnings
  | entryCount
deriving DecidableEq, Repr

/-- What a query answers. `lines` is the answer `factsView` gives a query about line bookkeeping. -/
inductive Answer
  | lines
  | dayRecord (a : Option DayAcc)
  | seam (a : Option SeamAcc)
  | energy (l : List EnergyObs)
  | durations (l : List DurationObs)
  | interrupts (l : List Interruption)
  | demotions (l : List Demotion)
  | closes (l : List CloseRec)
  | headers (l : List HeaderRec)
  | minutes (m : Option Nat)
  | bool (b : Bool)
  | inst (r : Option InstRec)
  | item (a : Option ItemAcc)
  | stamp (t : Option At)
  | date (d : Option Nat)
  | count (n : Nat)
  | named (r : Option NamedRec)
  | openBlock (b : Option OpenBlock)
  | openInterrupt (r : Option Interruption)
  | openBreak (r : Option OpenBrk)
  | leak (r : Option LeakRec)
  | warnings (l : List RWarn)
deriving DecidableEq, Repr

/-- The smallest of a list of days. -/
def minDay? (l : List Nat) : Option Nat := l.foldl (fun acc d => some (match acc with | none => d | some a => Nat.min a d)) none

/-- The largest of a list of days. -/
def maxDay? (l : List Nat) : Option Nat := l.foldl (fun acc d => some (match acc with | none => d | some a => Nat.max a d)) none

/-- **The facts' view** (§8.4 without the line bookkeeping): every fact reading, as a total query; a header query
and the entry count answer `lines`.  Maps are read through `get`, so the answer does not depend on how many
buckets the replay sized them with. -/
def factsView (f : Facts) : Q → Answer
  | .day d .record => .dayRecord (f.days.get d)
  | .day d .seam => .seam (f.seams.get d)
  | .day d .energy => .energy (f.energy.filter (fun o => decide (o.day = d)))
  | .day d .durations => .durations (f.durations.filter (fun o => decide (o.day = d)))
  | .day d .interrupts => .interrupts (f.interrupts.filter (fun r => decide (r.day = d)))
  | .day d .demotions => .demotions ((f.demotions.filter (fun p => decide (p.1 = d))).map Prod.snd)
  | .day d .closes => .closes ((f.closes.filter (fun p => decide (p.1 = d))).map Prod.snd)
  | .day _ .headers => .lines
  | .win d (.itemMin i) => .minutes (f.itemDays.get (d, i))
  | .win d (.done i) => .bool (f.doneOn i d)
  | .win d (.inst item inst) => .inst (if Log.instDate? inst = some d then f.instance item inst else none)
  | .item i => .item (f.items.get i)
  | .lastDone i => .stamp (f.lastDone i)
  | .doneFirst i => .date (minDay? (f.doneDatesOf i))
  | .doneCount i => .count (f.doneDatesOf i).length
  | .dropped i => .bool (f.dropped.get i).isSome
  | .instOther item inst => .inst (if Log.instDate? inst = none then f.instance item inst else none)
  | .named name id => .named (f.namedAt name id)
  | .openBlock => .openBlock f.openBlock
  | .openInterrupt => .openInterrupt f.openInterrupt
  | .openBreak => .openBreak f.openBreak
  | .lastDay => .date (maxDay? (f.days.pairs.map Prod.fst))
  | .lastEffective => .stamp f.lastEffective
  | .unknown => .count f.unknown
  | .longestLeak => .leak f.longestLeak
  | .replayWarnings => .warnings f.warnings
  | .entryCount => .lines

/-- **The view** (§8.4): `factsView`, and the line bookkeeping (a day's headers, cancelled ones included, and the
entry count). -/
def ask (doc : Doc) : Q → Answer
  | .day d .headers => .headers ((doc.headers.filter (fun p => decide (p.1 = d))).map Prod.snd)
  | .entryCount => .count doc.entryCount
  | q => factsView doc.facts q

/-- **`ask` is `factsView` on every fact reading**: only the line bookkeeping reads the headers. -/
theorem ask_reads_the_facts (doc : Doc) (q : Q) (hh : ∀ d, q ≠ .day d .headers) (he : q ≠ .entryCount) :
    ask doc q = factsView doc.facts q := by
  unfold ask
  split
  · rename_i d; exact absurd rfl (hh d)
  · exact absurd rfl he
  · rfl

/-! ### The view, grouped for the wire (D9-21: one `foldl` per list, into buckets) -/

/-- **One day's view**, as the wire hands it back: the fork's record (if the day has one), its seam (if a survivor
is on it), and its observations, interruptions, demotions, closes and headers, each list in file order. -/
structure DayOut where
  record : Option DayAcc
  seam : Option SeamAcc
  energy : List EnergyObs
  durations : List DurationObs
  interrupts : List Interruption
  demotions : List Demotion
  closes : List CloseRec
  headers : List HeaderRec

def DayOut.empty : DayOut := ⟨none, none, [], [], [], [], [], []⟩

/-- Write one day's view in its bucket. -/
def upDay (m : HMap Nat DayOut) (d : Nat) (g : DayOut → DayOut) : HMap Nat DayOut :=
  m.alter d (fun o => some (g (o.getD DayOut.empty)))

/-- **Every day's view** (§8.4's O): one `foldl` per list into day buckets; a list is folded from its end, so each
day's list keeps file order. -/
def dayOuts (doc : Doc) : HMap Nat DayOut :=
  let f := doc.facts
  let m : HMap Nat DayOut := HMap.empty doc.entryCount
  let m := f.days.pairs.foldl (fun m p => upDay m p.1 (fun o => { o with record := some p.2 })) m
  let m := f.seams.pairs.foldl (fun m p => upDay m p.1 (fun o => { o with seam := some p.2 })) m
  let m := f.energy.reverse.foldl (fun m x => upDay m x.day (fun o => { o with energy := x :: o.energy })) m
  let m := f.durations.reverse.foldl (fun m x => upDay m x.day (fun o => { o with durations := x :: o.durations })) m
  let m := f.interrupts.reverse.foldl (fun m x => upDay m x.day (fun o => { o with interrupts := x :: o.interrupts })) m
  let m := f.demotions.reverse.foldl (fun m p => upDay m p.1 (fun o => { o with demotions := p.2 :: o.demotions })) m
  let m := f.closes.reverse.foldl (fun m p => upDay m p.1 (fun o => { o with closes := p.2 :: o.closes })) m
  doc.headers.reverse.foldl (fun m p => upDay m p.1 (fun o => { o with headers := p.2 :: o.headers })) m

/-- **One date's window view** (§8.4's W): its item minutes, done ids and date-keyed instances. -/
structure WinOut where
  itemMin : List (Id × Nat)
  done : List Id
  inst : List (List Char × List Char × InstRec)

def WinOut.empty : WinOut := ⟨[], [], []⟩

def upWin (m : HMap Nat WinOut) (d : Nat) (g : WinOut → WinOut) : HMap Nat WinOut :=
  m.alter d (fun o => some (g (o.getD WinOut.empty)))

/-- **Every date's window view**: one `foldl` per map. -/
def winOuts (f : Facts) (n : Nat) : HMap Nat WinOut :=
  let m : HMap Nat WinOut := HMap.empty n
  let m := f.itemDays.pairs.foldl (fun m p => upWin m p.1.1 (fun o => { o with itemMin := (p.1.2, p.2) :: o.itemMin })) m
  let m := f.doneDates.pairs.foldl (fun m p => upWin m p.1.1 (fun o => { o with done := p.1.2 :: o.done })) m
  f.instances.pairs.foldl (fun m p =>
    match Log.instDate? p.1.2 with
    | some d => upWin m d (fun o => { o with inst := (p.1.1, p.1.2, p.2) :: o.inst })
    | none => m) m

/-- The instances whose `inst` names no date (§8.4's A). -/
def instOthers (f : Facts) : List ((List Char × List Char) × InstRec) :=
  f.instances.pairs.filter (fun p => (Log.instDate? p.1.2).isNone)

/-- **One item's all-time view** (§8.4's A): its record, `last_done`, whether it was dropped, and its first done date
and count of done dates. -/
structure ItemOut where
  acc : Option ItemAcc
  lastDone : Option At
  dropped : Bool
  doneFirst : Option Nat
  doneCount : Nat

def ItemOut.empty : ItemOut := ⟨none, none, false, none, 0⟩

def upItem (m : HMap Id ItemOut) (i : Id) (g : ItemOut → ItemOut) : HMap Id ItemOut :=
  m.alter i (fun o => some (g (o.getD ItemOut.empty)))

/-- **Every item's view**: one `foldl` per map. -/
def itemOuts (f : Facts) (n : Nat) : HMap Id ItemOut :=
  let m : HMap Id ItemOut := HMap.empty n
  let m := f.items.pairs.foldl (fun m p => upItem m p.1 (fun o => { o with acc := some p.2 })) m
  let m := f.lastDoneMap.pairs.foldl (fun m p => upItem m p.1 (fun o => { o with lastDone := some p.2 })) m
  let m := f.dropped.pairs.foldl (fun m p => upItem m p.1 (fun o => { o with dropped := true })) m
  f.doneDates.pairs.foldl (fun m p => upItem m p.1.2 (fun o =>
    { o with doneFirst := some (match o.doneFirst with | none => p.1.1 | some a => Nat.min a p.1.1),
             doneCount := o.doneCount + 1 })) m

end Facts6


/-! ## Witnesses (C3)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 4 entries,
`utcZone` (no transition), instants as `Nat` literals, no text parsed.  2026-09-07T09:00:00Z is second
63924368400, and the day is 739865. -/

section BlockWitnesses

open Log (Id U8 U32 Num)

/-- An entry of the witnesses, written in UTC at a whole second. -/
def bE (line sec : Nat) (ev : Event) (h : Cal.Instant.wf ⟨sec, 0⟩ = true := by decide) : Entry :=
  ⟨line, ⟨⟨sec, 0⟩, h⟩, ⟨⟨false, 0⟩, by decide⟩, ev⟩

/-- **"The replay warnings are the unknown routine statuses", as C4 stated it, refuted by the owner's D116** (README gap
5035): a `break_start` at `walk`, then the `break` line that ends it hand-edited to `moon` — the replay names the end
line's word beside its start's (`RWarn.breakPlace`), and no routine status is among them. -/
theorem the_replay_warnings_are_the_unknown_statuses_in_file_order_as_c4_stated_it_is_refuted :
    ¬ ∀ (z : Cal.Tz) (es : List Entry), (replay z es).warnings = (survivors es).filterMap warnOf := by
  intro h
  have := h utcZone [bE 1 63924368400 (.brkStart 10 (some ['w','a','l','k'])),
    bE 2 63924368400 (.brk 10 (some 10) (some ['m','o','o','n']))]
  revert this; decide

/-- A `start` with a reported energy (so it carries an observation). -/
def bStart (id : Id) : Event := .start id 3 (some 3) (.nat 2) 420 ['h'] 0 0

/-- A `done` at ci 3 with `went` 2. -/
def bDone (id : Id) (actual : U32) (isPartial : Bool) : Event := .done id 50 actual (some 2) [] 3 isPartial

/-- **A `start` cuts any open block, even one of the same id**: `start a` at 09:00 and again at 09:30.
The first block is credited 30 clock minutes of unknown ci, and the open block is the second. -/
theorem a_start_cuts_any_open_block_even_the_same_id :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (bStart ['a'])]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧
    (f.days.get 739865).map (·.ciUnknown) = some [(['a'], 30)] ∧
    f.openBlock.map (fun b => (b.id, b.started.1, b.workedMin)) = some (['a'], ⟨63924370200, 0⟩, 0) := by
  decide

/-- **A block cut by the next `start` is never replaced by a `done`**: `start a` 09:00, `start b` 09:30
(cutting `a` at 30 minutes), `done b` 09:40, then `done a` with 40 minutes at 09:50.  No block is open
and `a`'s `done` has minutes, but the start of `b` ended the cut's claim: `a` keeps its 30 clock minutes
and gains 40. -/
theorem a_block_cut_by_start_is_never_replaced_by_done :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (bStart ['b']),
      bE 3 63924370800 (bDone ['b'] 10 false), bE 4 63924371400 (bDone ['a'] 40 false)]
    (f.items.get ['a']).map (·.minutes) = some 70 ∧
    (f.days.get 739865).map (·.ciUnknown) = some [(['a'], 30)] := by
  decide

/-- **A `stop` then a `done` replaces the cut's credit**: `start a` 09:00, `stop a` 09:30, `done a` with
45 minutes at 09:31.  The 30 clock minutes are taken back and the 45 credited at ci 3: the day holds 45
block minutes, all at ci 3, none of unknown ci. -/
theorem a_stop_then_done_replaces_the_cut_credit :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.stop ['a'] 20),
      bE 3 63924370260 (bDone ['a'] 45 false)]
    (f.items.get ['a']).map (·.minutes) = some 45 ∧ (f.items.get ['a']).map (·.stops) = some 1 ∧
    (f.days.get 739865).map (·.blockMin) = some 45 ∧ (f.days.get 739865).map (·.byCi.c3) = some 45 ∧
    (f.days.get 739865).map (·.ciUnknown.length) = some 0 ∧ (f.days.get 739865).map (·.loadFifths) = some 135 ∧
    f.itemDays.get (739865, ['a']) = some 45 := by
  decide

/-- **A `stop` for another id is ignored**: `start a` 09:00, `stop b` 09:30.  Nothing is credited, and `a`
is still running from 09:00. -/
theorem a_stop_for_another_id_is_ignored :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.stop ['b'] 20)]
    f.items.pairs = [] ∧
    f.openBlock.map (fun b => (b.id, b.since.map (·.1), b.workedMin)) = some (['a'], some ⟨63924368400, 0⟩, 0) := by
  decide

/-- **A matched `done` discards the clock minutes**: `start a` 09:00, `done a` with 50 minutes at 09:30.
The block's segment runs 09:00–09:30, but the item is credited the 50 minutes the `done` carries, not
30 and not 80; the start's observation is emitted with the `done`'s `went`. -/
theorem a_matched_done_discards_the_clock_minutes :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (bDone ['a'] 50 false)]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun s => (s.start.1, s.stop.1)))
      = some [(⟨63924368400, 0⟩, ⟨63924370200, 0⟩)] ∧
    f.energy.map (fun o => (o.line, o.went)) = [(1, some 2)] := by
  decide

/-- **`close_pause` does not clear `paused`**: `start a` 09:00, `pause a` 09:10, `interrupt` 09:20,
`resume` 09:30.  The interruption closes the pause's segment (09:10–09:20) and the block stays paused
through it; `resume` restarts the pause where the interruption left off, so the open block is still
paused.  The interruption takes the open block's id. -/
theorem close_pause_does_not_clear_paused :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369000 (.pause ['a']),
      bE 3 63924369600 (.interrupt none), bE 4 63924370200 (.resume 5 [])]
    f.openBlock.map (fun b => (b.paused, b.workedMin)) = some (true, 10) ∧
    (f.days.get 739865).map (fun a => a.segments.map (·.kind))
      = some [.block ['a'], .pause ['a'], .interrupt (some ['a'])] ∧
    f.interrupts.map (fun r => (r.lostMin, r.id)) = [(5, some ['a'])] := by
  decide

/-- **A partial `done` credits but does not complete** (CRIT 22): `start a` 09:00, a partial `done a`
with 30 minutes at 09:30.  The minutes, the block and a `DurationObs` are recorded and the time goes to
`partial_done_at`; no completion time is pushed and the day's `done` list stays empty (nor is the item
done: `completionArm` marks only a non-partial `done`). -/
theorem a_partial_done_credits_but_does_not_complete :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (bDone ['a'] 30 true)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.items.get ['a']).map (·.blocks) = some 1 ∧
    (f.items.get ['a']).map (·.doneAt.length) = some 0 ∧
    (f.items.get ['a']).map (fun i => i.partialDoneAt.map (·.1)) = some [⟨63924370200, 0⟩] ∧
    (f.days.get 739865).map (·.done.length) = some 0 ∧
    f.durations.map (fun o => (o.actualMin, o.isPartial)) = [(30, true)] := by
  decide

/-- **A partial `done` after `stop` replaces the cut** (CRIT 22; fork `uncredit_cut` ignores `partial`):
`start a` 09:00, `stop a` 09:20, a partial `done a` with 30 minutes at 09:21.  The 20 clock minutes are
taken back: the item holds 30, none of unknown ci. -/
theorem a_partial_done_after_stop_replaces_the_cut :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369600 (.stop ['a'] 20),
      bE 3 63924369660 (bDone ['a'] 30 true)]
    (f.items.get ['a']).map (fun i => (i.minutes, i.partialDoneAt.map (·.1))) = some (30, [⟨63924369660, 0⟩]) ∧
    (f.days.get 739865).map (fun a => (a.blockMin, a.ciUnknown)) = some (30, ([] : KMap Id Nat)) := by
  decide

/-- **A block started during an interruption runs from `resume`**: `interrupt` 09:00, `start a` 09:10,
`resume` 09:20, `stop a` 09:40.  The clock starts at the resume, so 20 minutes are credited; the
interruption, opened with no block, has no id. -/
theorem a_block_started_during_an_interruption_runs_from_resume :
    let f := replay utcZone [bE 1 63924368400 (.interrupt none), bE 2 63924369000 (bStart ['a']),
      bE 3 63924369600 (.resume 0 []), bE 4 63924370800 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 20 ∧
    f.interrupts.map (fun r => (r.start.map (·.1), r.id)) = [(some ⟨63924368400, 0⟩, none)] := by
  decide

/-- **Site R8's refutation twin** (gap 83): `start a` 09:00:00, `pause a` 09:01:30, `unpause a` 09:02:00,
`stop a` 09:03:30.  The block ran two sub-segments of 90 seconds: each floors to 1 minute, so 2 minutes
are credited, where the floor of the block's 180 running seconds is 3. -/
theorem worked_minutes_is_not_the_floor_of_the_block :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924368490 (.pause ['a']),
      bE 3 63924368520 (.unpause ['a']), bE 4 63924368610 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 2 ∧
    ((Cal.secondsBetween ⟨63924368400, 0⟩ ⟨63924368490, 0⟩).toNat
      + (Cal.secondsBetween ⟨63924368520, 0⟩ ⟨63924368610, 0⟩).toNat) / 60 = 3 := by
  decide

/-- **Refuted under the owner's D14**: §8.2's `an_extend_changes_only_the_bookkeeping` says an `extend`'s
arm emits exactly its header and the bookkeeping.  That was design Q7's option (a), which deletes
`extended_min`; the owner took (b), which ports it, so the arm also writes its item.  The law is
`an_extend_changes_only_the_bookkeeping_its_extended_minutes_and_its_blocks` (D14's form, refuted under D108). -/
theorem an_extend_changes_more_than_the_bookkeeping :
    ∃ (e : Entry) (id : Id) (by_ : U32), e.ev = .extend id by_ ∧
      (effects utcZone [] [] (State.init 1) e).map Effect.key ≠ [.day (dayOf utcZone [] e.t.val), .global] ∧
      (step utcZone [] [] (State.init 1) e).items.get id ≠ (State.init 1).items.get id :=
  ⟨bE 1 63924368400 (.extend ['a'] 15), ['a'], 15, rfl, by decide, by decide⟩

/-- **D14's statement of what an `extend` changes is refuted** (the owner's D108): with `a`'s block open, an `extend`
of `a` writes the machine too — the block's `ext` — so its effects are not the four D14 named.  The law is
`an_extend_changes_only_the_bookkeeping_its_extended_minutes_and_its_blocks`, and D14's statement holds with no block
of the item open (`…_with_no_block_of_it_open`). -/
theorem an_extend_changes_only_the_bookkeeping_and_its_extended_minutes_is_refuted :
    ¬ ∀ (z : Cal.Tz) (kw : List Cal.Instant) (slept : List (Nat × Nat)) (st : State) (e : Entry) (id : Id) (by_ : U32),
      e.ev = .extend id by_ →
      (effects z kw slept st e).map Effect.key
        = [.day (dayOf z kw e.t.val), .global, .day (dayOf z kw e.t.val), .item id] := by
  intro h
  let st : State := { State.init 1 with
    machine := ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none, 0, none,
      739865, [], [], 0⟩, none, none, [], none, [], none⟩ }
  have := h utcZone [] [] st (bE 2 63924370200 (.extend ['a'] 15)) ['a'] 15 rfl
  have hl := congrArg List.length this
  revert hl
  decide

/-- **D108: an open block's `extend`s are its own** (README gaps 4876 and 4893): `a` started at 09:00, extended 15 and
then 10 minutes, and `b` — not the open block — extended 5.  The open block's `ext` is 25, the minutes `tm extend` added
to its planned minutes; the item's all-time `extended_min` is 25 too, and `b`'s 5 reached no block. -/
theorem an_open_blocks_extends_are_its_own :
    (replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369300 (.extend ['a'] 15),
      bE 3 63924370200 (.extend ['a'] 10), bE 4 63924371100 (.extend ['b'] 5)]).openBlock.map (·.ext) = some 25 := by
  decide

/-- **D108: a `start` begins the count again** — `ext` is the extends since the block's OWN `start`: `a` extended 15,
stopped, started again and extended 10 holds 10. -/
theorem a_start_begins_the_extends_again :
    (replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369300 (.extend ['a'] 15),
      bE 3 63924370200 (.stop ['a'] 30), bE 4 63924371100 (bStart ['a']),
      bE 5 63924372000 (.extend ['a'] 10)]).openBlock.map (·.ext) = some 10 := by
  decide

/-- **D108's one answer, through the replay** (W-49 track L, README gap 5300; the owner's D125): `plan h1` carrying `a 6`,
then `plan h2` carrying `b 3` on the same date — the later line wins.  Until W-49 the day kept two answers to this
question, the first (`yesterday`, `a 6`) and the latest (`late`, `b 3`); the first is gone. -/
theorem a_day_keeps_its_latest_plans_hysteresis_input :
    ((replay utcZone [bE 1 63924368400 (.plan ['h','1'] 0 0 [(['a'], 6)]),
      bE 2 63924370200 (.plan ['h','2'] 1 0 [(['b'], 3)])]).days.get 739865).map (·.late) = some [(['b'], 3)] := by
  decide

/-- **Every `plan` on the slot's calendar date or a later one records its stamp, its hash and its line** (the W-48
repair, README gap 5210; restated at W-49 track L, gap 5300): the day's `planAt`, `planHash` and `planLine` are the
latest date's last `plan`'s, beside the fork's `lastPlanHash`, which every `plan` sets. -/
theorem a_plan_records_its_stamp (h : List Char) (r d : Nat) (ys : List (Id × U8)) (t : At) (n : Nat) (a : DayAcc)
    (hn : notBefore a.planAt t = true) :
    ((DayOp.plan h r d ys t n).apply a).planAt = some t ∧ ((DayOp.plan h r d ys t n).apply a).planHash = some h ∧
      ((DayOp.plan h r d ys t n).apply a).planLine = some n ∧ ((DayOp.plan h r d ys t n).apply a).lastPlanHash = some h := by
  simp [DayOp.apply, hn]

/-- **…and a `plan` stamped on an earlier date than the slot's leaves it** (W-49 track L, gap 5300; AGENTS §5.8). -/
theorem a_plan_of_an_earlier_date_keeps_the_slot (h : List Char) (r d : Nat) (ys : List (Id × U8)) (t : At) (n : Nat)
    (a : DayAcc) (hn : notBefore a.planAt t = false) :
    ((DayOp.plan h r d ys t n).apply a).planAt = a.planAt ∧ ((DayOp.plan h r d ys t n).apply a).planHash = a.planHash ∧
      ((DayOp.plan h r d ys t n).apply a).planLine = a.planLine := by
  simp [DayOp.apply, hn]

/-- **A `plan` that carries a hysteresis input, on the slot's date or a later one, is the day's latest, at its stamp and
line; any other leaves the latest where it was** (the W-48 repair, README gaps 5210 and 5211; restated at W-49 track
L, gap 5300 — the input's date condition is new, and the statement as the repair wrote it is refuted by
`a_plan_with_an_input_is_the_latest_as_the_w48_repair_stated_it_is_refuted`) — both directions (AGENTS §5.8). -/
theorem a_plan_with_an_input_is_the_latest_and_one_without_keeps_it (h : List Char) (r d : Nat) (ys : List (Id × U8))
    (t : At) (n : Nat) (a : DayAcc) :
    (ys ≠ [] → notBefore a.lateAt t = true → ((DayOp.plan h r d ys t n).apply a).late = ys ∧
        ((DayOp.plan h r d ys t n).apply a).lateAt = some t ∧ ((DayOp.plan h r d ys t n).apply a).lateLine = some n) ∧
    ((ys = [] ∨ notBefore a.lateAt t = false) → ((DayOp.plan h r d ys t n).apply a).late = a.late ∧
        ((DayOp.plan h r d ys t n).apply a).lateAt = a.lateAt ∧
        ((DayOp.plan h r d ys t n).apply a).lateLine = a.lateLine) := by
  refine ⟨fun hy hn => ?_, fun hy => ?_⟩
  · cases ys with
    | nil => exact absurd rfl hy
    | cons _ _ => simp [DayOp.apply, hn]
  · rcases hy with hy | hn
    · subst hy; simp [DayOp.apply]
    · simp [DayOp.apply, hn]

/-- **"A `plan` that carries an input is the day's latest", as the W-48 repair stated it, refuted** (W-49 track L,
README gap 5300): `plan h1` at 00:30 UTC on 2026-09-08 carrying `a 6`, then a line a clock behind the log wrote at 23:50
the evening before carrying `b 3` — the later date's input stays `a 6`. -/
theorem a_plan_with_an_input_is_the_latest_as_the_w48_repair_stated_it_is_refuted :
    ¬ ∀ (h : List Char) (r d : Nat) (ys : List (Id × U8)) (t : At) (n : Nat) (a : DayAcc), ys ≠ [] →
      ((DayOp.plan h r d ys t n).apply a).late = ys := by
  intro hall
  have := hall ['h'] 0 0 [(['b'], 3)] (⟨63924421800, 0⟩, ⟨false, 0⟩) 2
    ((DayOp.plan ['h'] 0 0 [(['a'], 6)] (⟨63924424200, 0⟩, ⟨false, 0⟩) 1).apply DayAcc.empty) (by simp)
  revert this; decide

/-- **The latest input and the last plan, through the replay** (README gap 5210; restated at W-49 track L): `plan h1` at
09:00 carrying `a 6`, `plan h2` at 09:30 carrying `b 3`, `plan h3` at 10:00 carrying none, one date.  The day keeps
`b 3` at 09:30 (line 2) as its input (`late`, `lateAt`, `lateLine`), and 10:00 (line 3, `h3`) as its last plan. -/
theorem the_latest_input_and_the_last_plan_are_read_at_their_stamps :
    let d := (replay utcZone [bE 1 63924368400 (.plan ['h','1'] 0 0 [(['a'], 6)]),
      bE 2 63924370200 (.plan ['h','2'] 1 0 [(['b'], 3)]), bE 3 63924372000 (.plan ['h','3'] 2 0 [])]).days.get 739865
    d.map (·.late) = some [(['b'], 3)] ∧ d.map (·.lateLine) = some (some 2) ∧
      d.map (fun a => a.lateAt.map (·.1.sec)) = some (some 63924370200) ∧
      d.map (fun a => a.planAt.map (·.1.sec)) = some (some 63924372000) ∧ d.map (·.planLine) = some (some 3) ∧
      d.map (·.planHash) = some (some ['h','3']) ∧ d.map (·.lastPlanHash) = some (some ['h','3']) := by
  decide

/-- **A clock behind the log across midnight moves no later date's answer** (W-49 track L, README gap 5300; the W-48
recheck's world): one ledger day (woken 2026-09-07 07:00 UTC) holds `plan h1` at 00:26 on the 8th carrying `a 6` and
then, logged after it, `plan h2` stamped 23:59 on the 7th carrying `b 3` — the slot keeps the 8th's: `a 6`, `h1`, line
2.  Until W-49 the 7th's line took both slots, so the host found no input and no plan for the 8th and wrote both again
with no forward cause. -/
theorem a_clock_behind_the_log_moves_no_later_dates_answer :
    let d := (replay utcZone [bE 1 63924361200 (.wake 0 none),
      bE 2 63924423960 (.plan ['h','1'] 0 0 [(['a'], 6)]), bE 3 63924422340 (.plan ['h','2'] 1 0 [(['b'], 3)])]).days.get 739865
    d.map (·.late) = some [(['a'], 6)] ∧ d.map (·.lateLine) = some (some 2) ∧ d.map (·.planHash) = some (some ['h','1'])
      ∧ d.map (·.lastPlanHash) = some (some ['h','2']) := by
  decide

end BlockWitnesses

/-! ## Witnesses (C4)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 2 entries,
`utcZone` or `foldZone` (one transition), instants as `Nat` literals, no stamp text parsed (an `inst`
naming a date is read by `Log.instDate?`, ten characters).  2026-09-07T09:00:00Z is second 63924368400,
and the day is 739865. -/

section CompletionWitnesses

open Log (Id U8 U32 Num)

/-- An entry written at a chosen offset, `west` of UTC by `off` seconds. -/
def bEo (line sec : Nat) (west : Bool) (off : Nat) (ev : Event) (h : Cal.Instant.wf ⟨sec, 0⟩ = true := by decide)
    (ho : Cal.Offset.wf ⟨west, off⟩ = true := by decide) : Entry :=
  ⟨line, ⟨⟨sec, 0⟩, h⟩, ⟨⟨west, off⟩, ho⟩, ev⟩

/-- A `routine` logged `done`, without minutes. -/
def rDone (item ins : List Char) : Event := .routine item ins ['d', 'o', 'n', 'e'] none

/-- **Quirk Q6(b): instances and `last_done` order differently** (§15, Goals; gap 118): `routine s #1 done` at 10:00
on line 1, then the same instance `done` again at 08:00 on line 2 (a retro append).  The instance is the
last record in file order, the 08:00 one; `last_done` is the latest by instant, 10:00. -/
theorem instances_and_last_done_order_differently :
    ∃ (es : List Entry) (item ins : List Char) (r : InstRec) (t : At),
      Log.linesIncreasing es = true ∧ (replay utcZone es).instance item ins = some r ∧
      (replay utcZone es).lastDone item = some t ∧ r.status = .done ∧ r.t.1 < t.1 :=
  ⟨[bE 1 63924372000 (rDone ['s'] ['#', '1']), bE 2 63924364800 (rDone ['s'] ['#', '1'])], ['s'], ['#', '1'],
    ⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), .done, ['d', 'o', 'n', 'e'], none⟩, (⟨63924372000, 0⟩, ⟨false, 0⟩),
    by decide, by decide, by decide, rfl, by decide⟩

/-- **A retro `done` marks done and credits nothing** (§8.2): `done a` with 0 minutes and no block open.
The item is done on the day, with `last_done` at the `done`; it is credited 0 minutes and no block, the
day's block minutes stay 0, and no `DurationObs` is pushed. -/
theorem a_retro_done_marks_done_and_credits_nothing :
    let f := replay utcZone [bE 1 63924368400 (bDone ['a'] 0 false)]
    f.lastDone ['a'] = some (⟨63924368400, 0⟩, ⟨false, 0⟩) ∧ f.doneOn ['a'] 739865 = true ∧
    (f.items.get ['a']).map (fun i => (i.minutes, i.blocks)) = some (0, 0) ∧
    (f.days.get 739865).map (·.blockMin) = some 0 ∧ f.durations = [] := by
  decide

/-- **A later `pending` does not undo a done date** (§8.2): `routine s 2026-09-01 done` at 09:00, then the
same instance `pending` at 09:30.  The instance reads `Pending` (the last record), but the item stays done
on 2026-09-01, the date its `inst` names (not the 7th, its day), with `last_done` at 09:00. -/
theorem a_later_pending_does_not_undo_a_done_date :
    let f := replay utcZone [bE 1 63924368400 (rDone ['s'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '1']),
      bE 2 63924370200 (.routine ['s'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '1']
        ['p', 'e', 'n', 'd', 'i', 'n', 'g'] none)]
    (f.instance ['s'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '1']).map (·.status) = some .pending ∧
    f.doneOn ['s'] (Cal.toDay ⟨2026, 9, 1⟩) = true ∧ f.doneOn ['s'] 739865 = false ∧
    f.lastDone ['s'] = some (⟨63924368400, 0⟩, ⟨false, 0⟩) := by
  decide

/-- **An unknown status warns and is pending** (§8.3): `routine s #1 Done` (a capital `D`, which fork
`parse_instance_status` does not read) with 5 minutes.  One replay warning names line 1 and the status as
logged; the instance is `Pending`, keeps `"Done"` and its minutes, and the item is not done. -/
theorem an_unknown_status_warns_and_is_pending :
    let f := replay utcZone [bE 1 63924368400 (.routine ['s'] ['#', '1'] ['D', 'o', 'n', 'e'] (some 5))]
    f.warnings = [.unknownInstanceStatus 1 ['D', 'o', 'n', 'e']] ∧
    f.instance ['s'] ['#', '1'] = some ⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), .pending, ['D', 'o', 'n', 'e'], some 5⟩ ∧
    f.lastDone ['s'] = none := by
  decide

/-- **`last_done` keeps the first of equal instants** (fork `if t > *last`, not `>=`): two `done a` at the
same instant, line 1 written `+00:00` and line 2 written `-01:00`.  `last_done` keeps line 1's written
offset; both completions are in `done_at`. -/
theorem last_done_keeps_the_first_of_equal_instants :
    let f := replay utcZone [bE 1 63924368400 (bDone ['a'] 30 false), bEo 2 63924368400 true 3600 (bDone ['a'] 30 false)]
    f.lastDone ['a'] = some (⟨63924368400, 0⟩, ⟨false, 0⟩) ∧
    (f.items.get ['a']).map (fun i => i.doneAt.map (·.2)) = some [⟨false, 0⟩, ⟨true, 3600⟩] := by
  decide

/-- **A routine's done date is its `inst` only when that is a date `parse_date` reads**: `routine r #2 done`
is done on its day; `routine q` on `2026-9-` + no-break space + `01` (10 characters, 11 bytes, which the
fork's `s.len() != 10` refuses) is done on its day too, not on 2026-09-01. -/
theorem a_routine_done_is_dated_by_its_inst_only_when_it_is_a_date :
    let f := replay utcZone [bE 1 63924368400 (rDone ['r'] ['#', '2']),
      bE 2 63924368460 (rDone ['q'] ['2', '0', '2', '6', '-', '9', '-', ' ', '0', '1'])]
    f.doneOn ['r'] 739865 = true ∧ f.doneOn ['q'] 739865 = true ∧ f.doneOn ['q'] (Cal.toDay ⟨2026, 9, 1⟩) = false := by
  decide

/-- **Refuted: design §8.4's "a `≥ since` filter commutes with max"** (R3; carried note 3).  In `foldZone`,
whose clock goes back an hour at 00:30 UTC on 2026-09-08, `event x` at 00:29:30 (dated the 8th) and again
at 23:50 local an instant later (dated the 7th).  Filtered to dates on or after the 8th, the latest is line
1; the latest by instant, line 2, is dated the 7th, so "the latest, then the filter" answers nothing.  The
kernel keeps both, as fork `LatestNamed` does: `latest` is line 2 and `dated` line 1. -/
theorem a_since_filter_does_not_commute_with_the_latest_by_instant :
    let es := [bE 1 63924424170 (.named ['x'] none), bE 2 63924425400 (.named ['x'] none)]
    let occ := (namedOccurrences foldZone ['x'] none es)
    ((replay foldZone es).namedAt ['x'] none).map (fun r => (r.latest.1, r.dated.2.1)) = some (2, 1) ∧
    occ.map (·.2.2) = [739866, 739865] ∧
    lastMax? latestRel ((occ.filter (fun o => decide (739866 ≤ o.2.2))).map (fun o => (o.1, o.2.1)))
      = some (1, (⟨63924424170, 0⟩, ⟨false, 0⟩)) ∧
    (lastMax? latestRel (occ.map (fun o => (o.1, o.2.1)))).filter
      (fun p => decide (739866 ≤ Cal.localDate foldZone p.2.1)) = none := by
  decide

end CompletionWitnesses

/-! ## Witnesses (C5)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 6 entries,
`utcZone` (no transition), instants as `Nat` literals, no stamp text parsed.  2026-09-07T00:00:00Z is second
63924336000, and the day is 739865. -/

section DayWitnesses5

open Log (Id U8 U32 Num)

/-- **Quirk Q6(a) in the day's own fields** (gap 82): `wake` at 07:00 slept 400 on line 1, then `wake` at 06:00
slept 300 on line 2, one date.  The day index keeps 06:00, the earliest by instant; the day's `wake` and
`slept_min`, and `slept_by_day`, are the first logged: 07:00 and 400. -/
theorem the_days_wake_is_its_first_logged_wake :
    let es := [bE 1 63924361200 (.wake 400 none), bE 2 63924357600 (.wake 300 none)]
    ((replay utcZone es).days.get 739865).map (fun a => (a.wake.map (·.1), a.sleptMin))
      = some (some ⟨63924361200, 0⟩, some 400) ∧
    keptWakeOn utcZone (dayIndexOf utcZone es) 739865 = some ⟨63924357600, 0⟩ ∧
    slOf utcZone es 739865 = some 400 := by
  decide

/-- **Late binding** (`energy_obs_slept_is_the_days_first_logged_sleep`): `energy` at 09:00 on line 1, then the
day's `wake` at 06:00, slept 420, on line 2 (`tm wake 06:05` typed after `tm energy 4`).  The observation reads
420, and is not a start's. -/
theorem an_energy_line_before_its_wake_reads_the_wakes_sleep :
    let f := replay utcZone [bE 1 63924368400 (.energy 3 4 (.nat 2) ['h']), bE 2 63924357600 (.wake 420 none)]
    f.energy.map (fun o => (o.line, o.day, o.sleptMin, o.fromStart)) = [(1, 739865, some 420, false)] := by
  decide

/-- **A gap is on the day it began**: wakes at 06:00 on the 7th and the 8th, then on the 8th a `leak` idle gap of
60 minutes answered at 06:30 and a routine `done` of 60 minutes at 06:31.  Both began before the 8th's wake and
under 24 hours after the 7th's, so the `Idle` and `Routine` segments, the `IdleRecord` (its `day` the 7th) and
the leak minutes are the 7th's, and so is the global longest leak; `routine_min` is the routine's own day, the
8th. -/
theorem a_gap_is_on_the_day_it_began :
    let f := replay utcZone [bE 1 63924357600 (.wake 420 none), bE 2 63924444000 (.wake 420 none),
      bE 3 63924445800 (.idle ['l', 'e', 'a', 'k'] 60),
      bE 4 63924445860 (.routine ['s'] ['#', '1'] ['d', 'o', 'n', 'e'] (some 60))]
    (f.days.get 739865).map (fun a => (a.idle.map (·.day), a.leakMin, a.longestLeak, a.segments.map (·.kind),
      a.routineMin)) = some ([739865], 60, 60, [.idle ['l', 'e', 'a', 'k'], .routine ['s'] ['#', '1']], 0) ∧
    (f.days.get 739866).map (fun a => (a.idle.length, a.segments.length, a.routineMin)) = some (0, 0, 60) ∧
    f.longestLeak.map (fun r => (r.day, r.min)) = some (739865, 60) := by
  decide

/-- The log of `a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan` (a `def`, so the instance
search for `decide` sees its name, not six entries three times). -/
def arrivalsAndPlans : List Entry :=
  [bE 1 63924364800 (.arrive ['a'] (['8'], ['9']) 6), bE 2 63924365400 (.plan ['h', '1'] 3 5 []),
   bE 3 63924366000 (.arrive ['b'] (['7'], ['9']) 4), bE 4 63924366600 (.plan ['h', '2'] 1 2 []),
   bE 5 63924367200 (.loc ['c']), bE 6 63924367800 (.unknown ['m', 'o', 'o', 'd'] [])]

/-- **A day keeps its first arrival, its highest replans and its last plan**: `arrive a` (window 8–9, budget 6),
`plan h1` (3 replans, 5 minutes' drift), `arrive b`, `plan h2` (1 replan, 2 minutes), `loc c`, and an unknown
`mood` event (`arrivalsAndPlans`).  The arrival is the first's, every location change is kept in order, the
plans count 2 with the highest replans 3, the drift sums to 7 and the last hash is `h2`; the unknown event is
counted. -/
theorem a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan :
    ((replay utcZone arrivalsAndPlans).days.get 739865).map (fun a => (a.loc, a.window))
      = some (some ['a'], some (['8'], ['9'])) ∧
    ((replay utcZone arrivalsAndPlans).days.get 739865).map (fun a => (a.budget, a.locChanges.map (·.2)))
      = some (some 6, [['a'], ['b'], ['c']]) ∧
    ((replay utcZone arrivalsAndPlans).days.get 739865).map (fun a => (a.plans, a.replansToday)) = some (2, 3) ∧
    ((replay utcZone arrivalsAndPlans).days.get 739865).map (fun a => (a.driftMin, a.lastPlanHash)) = some (7, some ['h', '2']) ∧
    (replay utcZone arrivalsAndPlans).unknown = 1 := by
  decide

/-- **A break lasts its actual minutes, else its planned**: a `break` planned 10 minutes at 09:00 with no actual,
and one planned 10 with 12 actual at 10:00.  The segments end at 09:10 and 10:12. -/
theorem a_break_lasts_its_actual_minutes_else_its_planned :
    let f := replay utcZone [bE 1 63924368400 (.brk 10 none none), bE 2 63924372000 (.brk 10 (some 12) (some ['w']))]
    (f.days.get 739865).map (fun a => (a.segments.map (fun g => (g.start.1, g.stop.1)), a.breaks.map (·.actualMin)))
      = some ([(⟨63924368400, 0⟩, ⟨63924369000, 0⟩), (⟨63924372000, 0⟩, ⟨63924372720, 0⟩)], [none, some 12]) := by
  decide

/-- **The first of equal leaks is the longest** (`the_first_leak_maximum_wins`; fork `min > l.min`): `leak` gaps
of 30 minutes at 09:00 and at 10:00, a `work` gap of 90 at 11:00, and a `leak` of 20 at 12:00.  The global
longest leak is the 09:00 one; the day's leak minutes are 80 and its longest 30; all four gaps are recorded. -/
theorem the_first_of_equal_leaks_is_the_longest :
    let f := replay utcZone [bE 1 63924368400 (.idle ['l', 'e', 'a', 'k'] 30), bE 2 63924372000 (.idle ['l', 'e', 'a', 'k'] 30),
      bE 3 63924375600 (.idle ['w'] 90), bE 4 63924379200 (.idle ['l', 'e', 'a', 'k'] 20)]
    f.longestLeak.map (fun r => r.t.1) = some ⟨63924368400, 0⟩ ∧
    (f.days.get 739865).map (fun a => (a.leakMin, a.longestLeak, a.idle.length)) = some (80, 30, 4) := by
  decide

/-- **The demote stamps of a week, a date and a month key** (`a_demote_stamp_reads_the_week_or_date_key`): `demote a`
from `2026-W37` (week 37), from `2026-09-07` (day 7) and `demote b` from `2026-09` (none); a `drop a` and a
`close week`, each recorded on its day.  None of the five creates a day. -/
theorem the_demote_stamps_of_a_week_a_date_and_a_month_key :
    let f := replay utcZone [bE 1 63924368400 (.demote ['a'] ['2', '0', '2', '6', '-', 'W', '3', '7'] ['x'] 50),
      bE 2 63924368460 (.demote ['a'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '7'] ['y'] 30),
      bE 3 63924368520 (.demote ['b'] ['2', '0', '2', '6', '-', '0', '9'] ['z'] 20),
      bE 4 63924368580 (.drop ['a']), bE 5 63924368640 (.close ['w', 'e', 'e', 'k'] ['k'])]
    f.demotions.map (fun p => (p.1, p.2.id, p.2.stamp))
      = [(739865, ['a'], some (.week 37)), (739865, ['a'], some (.day 7)), (739865, ['b'], none)] ∧
    f.dropped.get ['a'] = some () ∧ f.closes.map (fun p => (p.1, p.2.period)) = [(739865, ['w', 'e', 'e', 'k'])] ∧
    f.days.get 739865 = none := by
  decide

/-- **Quirk Q6(f), fixed** (gap 86; owner answer Q6's last column, "fix, after the switch"; W-12).
A close now carries `period:key` as its primary id, so `tm undo` of a week close writes
`undo{of:"close", id:"week:2026-W37"}` and cancels **the week's** close — leaving the automatic
`close day` that a later verb's housekeeping appended standing, which is what the undo meant.

Before this, `close` had no id, and the undo cancelled whichever close was latest: the automatic
one.  The rule this replaces is the second conjunct, kept verbatim and still true, because **a log
written before this step must still read as it did** — the bare `undo{of:"close", id:null}` an
older `tm` wrote matches on the tag alone (`matches` quantifies its `id` with `Option.all`, which
is vacuous at `none`), so it still cancels the latest close.  One mask reads both spellings, and a
log that mixes them reads each line as it was meant (`a_silent_verb_undo_cancels_nothing_while_the_old_spelling_still_cancels`
is the same shape for Q6(d)).

The fork writes `null` for a close's id, so this is parity entry **P36** (renumbered from P32 at
stage 5's close: P32 was already D10 step L8's candidate-bounds row, README gap 226). -/
theorem an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest :
    (Log.Event.close ['w'] ['k']).primaryId = some ['w', ':', 'k'] ∧
    (replay utcZone [bE 1 63924368400 (.close ['w', 'e', 'e', 'k'] ['2', '0', '2', '6', '-', 'W', '3', '7']),
        bE 2 63924368460 (.close ['d', 'a', 'y'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '7']),
        bE 3 63924368520 (.undo ['c', 'l', 'o', 's', 'e']
          (some ['w', 'e', 'e', 'k', ':', '2', '0', '2', '6', '-', 'W', '3', '7']))]).closes.map (·.2.period)
      = [['d', 'a', 'y']] ∧
    (replay utcZone [bE 1 63924368400 (.close ['w', 'e', 'e', 'k'] ['2', '0', '2', '6', '-', 'W', '3', '7']),
        bE 2 63924368460 (.close ['d', 'a', 'y'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '7']),
        bE 3 63924368520 (.undo ['c', 'l', 'o', 's', 'e'] none)]).closes.map (·.2.period) = [['w', 'e', 'e', 'k']] ∧
    (replay utcZone [bE 2 63924368460 (.close ['d', 'a', 'y'] ['2', '0', '2', '6', '-', '0', '9', '-', '0', '7'])]).closes.map
      (·.2.period) = [['d', 'a', 'y']] := by
  decide

/-- **Quirk Q6(g), ported faithfully** (gap 87): a `wake` at 06:00 on the 7th, `start a` at 23:30 and its `done` at
00:30 on the 8th.  The calendar date of 00:30 is the 8th (fork `Ctx::today`), but the replay's day of it is the
7th: the 8th has no day, so `blocks_done(today)` reads 0 after midnight, and the block is the 7th's. -/
theorem the_calendar_today_is_not_the_replays_day_after_midnight :
    let es := [bE 1 63924357600 (.wake 420 none), bE 2 63924420600 (bStart ['a']), bE 3 63924424200 (bDone ['a'] 30 false)]
    Cal.localDate utcZone ⟨63924424200, 0⟩ = 739866 ∧ dayOf utcZone (dayIndexOf utcZone es) ⟨63924424200, 0⟩ = 739865 ∧
    ((replay utcZone es).days.get 739866).map (·.blocksDone) = none ∧
    ((replay utcZone es).days.get 739865).map (·.blocksDone) = some 1 := by
  decide

/-- **`idle` and `idle_since` read different orders** (§8.4, CRIT 24; Goals): on `[note 09:00, plan 08:00]`
`lastEffective` (fork `last_effective_t`, `tm idle`) is the last line, 08:00, and the day's `lastT` (fork
`DaySeam.last_t`, the TUI's `idle_since`) the latest instant, 09:00. -/
theorem idle_and_idle_since_read_different_orders :
    ∃ (es : List Entry) (d : Nat) (a b : At), Log.linesIncreasing es = true ∧
      (replay utcZone es).lastEffective = some a ∧ lastTOn utcZone es d = some b ∧ a.1 < b.1 :=
  ⟨[bE 1 63924368400 (.note ['n']), bE 2 63924364800 (.plan ['h'] 0 0 [])], 739865,
    (⟨63924364800, 0⟩, ⟨false, 0⟩), (⟨63924368400, 0⟩, ⟨false, 0⟩), by decide, by decide, by decide, by decide⟩

end DayWitnesses5

/-! ## Witnesses (C6)

Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 6 entries, `utcZone` (no
transition), instants as `Nat` literals, no stamp text parsed.  2026-09-07T09:00:00Z is second 63924368400, and the day
is 739865. -/

section FactsWitnesses6

open Log (Id U8 U32 Num)

/-- **The seam of a day** (R1, R2, R4): `start a` 09:00, a `break` at 10:00 with 15 minutes actual, `start b`
11:00, `pause b` 11:30, `unpause b` 11:40, and a `note` at 08:00 logged last.  The since-break anchor is the
break's end, 10:15 (a later `start` does not move it); the idle marks are the break, the pause and the unpause
in file order; `last_t` is the latest stamp, 11:40, not the last line's 08:00.  The note's day has a seam, and
so does every survivor's. -/
theorem a_days_seam_holds_its_break_its_marks_and_its_latest_stamp :
    let s := (replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924372000 (.brk 10 (some 15) none),
      bE 3 63924375600 (bStart ['b']), bE 4 63924377400 (.pause ['b']), bE 5 63924378000 (.unpause ['b']),
      bE 6 63924364800 (.note ['n'])]).seams.get 739865
    s.map (·.sinceBreak) = some (some (⟨63924372900, 0⟩, ⟨false, 0⟩)) ∧
    s.map (fun a => a.idleMarks) = some [.brk (⟨63924372000, 0⟩, ⟨false, 0⟩) (some 15),
      .pause (⟨63924377400, 0⟩, ⟨false, 0⟩), .unpause (⟨63924378000, 0⟩, ⟨false, 0⟩)] ∧
    s.map (·.lastT) = some (some (⟨63924378000, 0⟩, ⟨false, 0⟩)) := by
  decide

/-- **Without a break the anchor is the day's first start**, and a day holding only a `note` has a seam and no
record: `start a` at 09:00 and `start b` at 09:30 on the 7th, a `note` at 09:00 on the 8th. -/
theorem the_since_break_anchor_is_the_first_start_without_a_break :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (bStart ['b']),
      bE 3 63924454800 (.note ['n'])]
    (f.seams.get 739865).map (·.sinceBreak) = some (some (⟨63924368400, 0⟩, ⟨false, 0⟩)) ∧
    (f.seams.get 739866).map (·.lastT) = some (some (⟨63924454800, 0⟩, ⟨false, 0⟩)) ∧ f.days.get 739866 = none := by
  decide

/-- **A cancelled line has a header on its day**: a `note`, its `undo`, and a `drop a`.  Every entry has a header
in file order; the note and the undo are cancelled; the survivors' header effects hold the `drop` alone. -/
theorem every_line_has_a_header_and_a_cancelled_one_is_marked :
    let es := [bE 1 63924368400 (.note ['n']), bE 2 63924368460 (.undo ['n', 'o', 't', 'e'] none),
      bE 3 63924368520 (.drop ['a'])]
    (entryHeaders utcZone es).map (fun p => (p.1, p.2.line, p.2.id, p.2.cancelled))
      = [(739865, 1, none, true), (739865, 2, none, true), (739865, 3, some ['a'], false)] ∧
    (replay utcZone es).headers.map (·.2.line) = [3] := by
  decide

/-- **A start's observation is in its start's place**: `start a` (with a reported energy) at 09:00 on line 1, an
`energy` report at 09:30 on line 2, `done a` at 10:00 on line 3.  The start's observation is emitted at the `done`,
after the report's, and the replay's observations are in line order, 1 then 2. -/
theorem a_start_observation_is_in_its_starts_place :
    (replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.energy 3 4 (.nat 2) ['h']),
      bE 3 63924372000 (bDone ['a'] 60 false)]).energy.map (fun o => (o.line, o.fromStart)) = [(1, true), (2, false)] := by
  decide

/-- **The view reads a small log**: `wake` at 06:00, `note` at 09:00 and its `undo`, `drop a`.  The last day is the
7th, the log has four entries, the day's headers are four (the cancelled two included), `a` is dropped, and the
view without the line bookkeeping does not answer the headers. -/
theorem the_view_reads_a_small_log :
    let doc := replayDoc utcZone [bE 1 63924357600 (.wake 420 none), bE 2 63924368400 (.note ['n']),
      bE 3 63924368460 (.undo ['n', 'o', 't', 'e'] none), bE 4 63924368520 (.drop ['a'])]
    ask doc .lastDay = .date (some 739865) ∧ ask doc .entryCount = .count 4 ∧
    (match ask doc (.day 739865 .headers) with | .headers l => l.length | _ => 0) = 4 ∧
    ask doc (.dropped ['a']) = .bool true ∧ factsView doc.facts (.day 739865 .headers) = .lines := by
  decide

end FactsWitnesses6

/-! ## C7: the undo law, with housekeeping in between (§7.3)

`tm undo` of a command `X` whose events are `E` sees the log `L ++ E ++ M`, where `M` holds what `X` did not
write (the next verb's automatic `close`, `tm now`'s and the TUI's appends, later commands), and appends
`undosFor E`: one `undo{of: tag, id: primary id}` per event of `E`, most recent first, each stamped `ctx.now`
(`tm/src/cli/undo.rs`).  **The law**: when no event of `M` is an undo or matches one of those undos
(`untouchedBy`), the replay's view of the log is the view of `L ++ M`
(`undoing_a_command_replays_the_log_without_it`).  It is what "`tm undo` must replay the log, never apply an
inverse command" (Boundary.lean's `move_has_no_inverse_command`, L22) always pointed at: an inverse command does
not exist, and the replay of the log with the command's undos is the replay without the command.

**Why it holds**, in two halves:
* **the mask** (`undoing_a_command_leaves_the_survivors_of_the_log_without_it`): taken most recent first, each
  undo finds its own event, because the later events of `E` are already cancelled and `untouchedBy` rules out
  `M`; so the survivors are those of `L ++ M`, entry for entry;
* **the view reads only the survivors** (`the_view_reads_only_the_survivors`): the replay folds the survivors
  over the day index of their wakes, and only its maps' bucket counts see the whole log's length.  The view
  reads every map through `HMap.get` (`SameReadings`), and its three readings of a map's pairs (`lastDay`,
  `doneFirst`, `doneCount`) through the keys, which are one set up to order whatever the bucket count
  (`HMap.Keyed`, `HMap.perm_keys_pairs`).

**Not the line bookkeeping**: a header, the entry count and the cancelled lines see the appended lines, and
`factsView` answers them `lines`.

**The two quirks the hypothesis excludes, ported faithfully** (Q6):
* **(d), the silent verb** (gap 84): a command that logged nothing is undone by `undo{of: verb}`, which cancels the
  latest surviving event named like the verb (`a_silent_verb_undo_cancels_the_latest_event_of_its_name`); it
  cancels nothing exactly when no survivor carries the name
  (`a_silent_verb_undo_cancels_nothing_iff_no_survivor_has_its_name`).  §15's witness:
  `undo_of_a_silent_verb_cancels_an_older_event`.
* **(f), housekeeping in between** (gap 86): `close` has no primary id, so the undo of a week close cancels the
  automatic close after it (`undo_after_housekeeping_cancels_the_housekeeping`), and the law's conclusion fails
  (`the_undo_law_fails_without_untouchedBy`).

Nothing here is on the wire: `undosFor` and `untouchedBy` are specification (D9-21). -/

section UndoLaw

open Log (Id U8 U32 Num)

/-- **What `tm undo` appends for a command's events `E`** (fork `undo`, `tm/src/cli/undo.rs`): one
`undo{of: tag, id: primary id}` per event, **most recent first**, at lines `n, n + 1, …`, every one stamped
`ctx.now`, the instant `t` written at offset `o`.  The tag and id are `Event.tag` and `Event.primaryId`, the
functions `«matches»` reads (fork `Recorder::finish` records `ev.name()` and `ev.primary_id()`).  A command that
logged nothing gets `undo{of: verb}` instead, quirk Q6(d), below. -/
def undosFor (E : List Entry) (n : Nat) (t : Cal.VInstant) (o : Cal.VOffset) : List Entry :=
  (E.reverse.zipIdx n).map (fun p => ⟨p.2, t, o, .undo p.1.ev.tag p.1.ev.primaryId⟩)

/-- **No event of `M` is an undo, and none matches the pattern of any undo `tm undo` writes for `E`.** -/
def untouchedBy (E M : List Entry) : Bool :=
  M.all (fun m => !m.ev.isUndo && E.all (fun e => !«matches» e.ev.tag e.ev.primaryId m))

/-- An event matches the undo written for it. -/
theorem matches_its_own_undo (e : Entry) : «matches» e.ev.tag e.ev.primaryId e = true := by
  unfold «matches»
  cases e.ev.primaryId <;> simp

/-- Events that are not undos are pushed onto the stack in order. -/
theorem foldl_maskStep_of_no_undo : ∀ (xs st : List Entry), xs.all (fun e => !e.ev.isUndo) = true →
    xs.foldl maskStep st = xs.reverse ++ st
  | [], _, _ => rfl
  | x :: xs, st, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.foldl_cons, foldl_maskStep_of_no_undo xs _ h.2]
    have : maskStep st x = x :: st := by
      unfold maskStep; split
      · rename_i of_ id hev; simp [hev, Event.isUndo] at h
      · rfl
    rw [this]; simp

/-- **The undos of `D`, most recent first, over a stack `R ++ D ++ S`** in which no entry of `R` matches any of
them: each takes its own event, and `R ++ S` is left. -/
theorem foldl_maskStep_undos (R S : List Entry) (t : Cal.VInstant) (o : Cal.VOffset) :
    ∀ (D : List Entry) (n : Nat), (∀ m ∈ R, ∀ e ∈ D, «matches» e.ev.tag e.ev.primaryId m = false) →
      ((D.zipIdx n).map (fun p => (⟨p.2, t, o, .undo p.1.ev.tag p.1.ev.primaryId⟩ : Entry))).foldl maskStep
        (R ++ D ++ S) = R ++ S
  | [], _, _ => by simp
  | e :: D, n, h => by
    rw [List.zipIdx_cons, List.map_cons, List.foldl_cons]
    have hstep : maskStep (R ++ e :: D ++ S) ⟨n, t, o, .undo e.ev.tag e.ev.primaryId⟩ = R ++ D ++ S := by
      simp only [maskStep]
      rw [List.append_assoc, List.eraseP_append_right _ (fun b hb => by
        simp [h b hb e List.mem_cons_self])]
      rw [List.cons_append, List.eraseP_cons_of_pos (matches_its_own_undo e)]
      simp
    rw [hstep]
    exact foldl_maskStep_undos R S t o D (n + 1) (fun m hm e' he' => h m hm e' (List.mem_cons_of_mem _ he'))

/-- **The mask's half of the undo law**: the survivors of `L ++ E ++ M ++ undosFor E n t o` are those of
`L ++ M`, entry for entry. -/
theorem undoing_a_command_leaves_the_survivors_of_the_log_without_it (L E M : List Entry) (n : Nat)
    (t : Cal.VInstant) (o : Cal.VOffset)
    (hE : E.all (fun e => !e.ev.isUndo) = true) (hM : untouchedBy E M = true) :
    survivors (L ++ E ++ M ++ undosFor E n t o) = survivors (L ++ M) := by
  have hM1 : M.all (fun e => !e.ev.isUndo) = true := by
    unfold untouchedBy at hM
    simp only [List.all_eq_true, Bool.and_eq_true] at hM ⊢
    exact fun m hm => (hM m hm).1
  have hM2 : ∀ m ∈ M.reverse, ∀ e ∈ E.reverse, «matches» e.ev.tag e.ev.primaryId m = false := by
    intro m hm e he
    unfold untouchedBy at hM
    simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hM
    exact (hM m (List.mem_reverse.1 hm)).2 e (List.mem_reverse.1 he)
  unfold survivors undosFor
  rw [List.foldl_append, List.foldl_append, List.foldl_append, List.foldl_append,
    foldl_maskStep_of_no_undo E _ hE, foldl_maskStep_of_no_undo M _ hM1, foldl_maskStep_of_no_undo M _ hM1,
    ← List.append_assoc, foldl_maskStep_undos _ _ t o E.reverse n hM2]

end UndoLaw

/-! ### The view reads only the survivors: maps compared by their keys, whatever their bucket counts -/

section BucketFree

/-- **Two states that answer every reading alike**: every list and scalar equal, and every bucketed map equal key
by key (`HMap.get`), whatever its bucket count. -/
structure SameReadings (a b : State) : Prop where
  days : ∀ k, a.days.get k = b.days.get k
  items : ∀ k, a.items.get k = b.items.get k
  itemDays : ∀ k, a.itemDays.get k = b.itemDays.get k
  lastDone : ∀ k, a.lastDone.get k = b.lastDone.get k
  doneDates : ∀ k, a.doneDates.get k = b.doneDates.get k
  instances : ∀ k, a.instances.get k = b.instances.get k
  named : ∀ k, a.named.get k = b.named.get k
  dropped : ∀ k, a.dropped.get k = b.dropped.get k
  seams : ∀ k, a.seams.get k = b.seams.get k
  energy : a.energy = b.energy
  durations : a.durations = b.durations
  interrupts : a.interrupts = b.interrupts
  headers : a.headers = b.headers
  machine : a.machine = b.machine
  global : a.global = b.global
  rwarns : a.rwarns = b.rwarns
  demotions : a.demotions = b.demotions
  closes : a.closes = b.closes
  longestLeak : a.longestLeak = b.longestLeak
  unknown : a.unknown = b.unknown

/-- The empty states of any two sizes answer alike. -/
theorem sameReadings_init (n m : Nat) : SameReadings (State.init n) (State.init m) := by
  constructor <;> first | rfl | (intro k; simp [State.init, HMap.get_empty])

/-- Every effect keeps two states answering alike: it writes a map through `alter`, whose law is `get_alter`
(`itemDaySub` reads `items` through `get` first). -/
theorem SameReadings.apply {a b : State} (h : SameReadings a b) (x : Effect) :
    SameReadings (applyEffect a x) (applyEffect b x) := by
  cases x with
  | obs ob =>
    cases ob <;>
    exact ⟨h.days, h.items, h.itemDays, h.lastDone, h.doneDates, h.instances, h.named, h.dropped, h.seams,
      by simp [applyEffect, h.energy], by simp [applyEffect, h.durations], h.interrupts, h.headers, h.machine,
      h.global, h.rwarns, h.demotions, h.closes, h.longestLeak, h.unknown⟩
  | itemDaySub i d m =>
    simp only [applyEffect]
    rw [h.items i]
    split
    · exact { h with itemDays := fun k => by simp only [HMap.get_alter, h.itemDays] }
    · exact h
  | _ =>
    constructor <;>
      first
      | (intro k; simp only [applyEffect, HMap.get_alter, h.days, h.items, h.itemDays, h.lastDone, h.doneDates,
          h.instances, h.named, h.dropped, h.seams])
      | simp only [applyEffect, h.energy, h.durations, h.interrupts, h.headers, h.machine, h.global, h.rwarns,
          h.demotions, h.closes, h.longestLeak, h.unknown]

theorem SameReadings.applyEffects {a b : State} (h : SameReadings a b) :
    ∀ (fx : List Effect), SameReadings (applyEffects a fx) (applyEffects b fx)
  | [] => h
  | x :: fx => by
    unfold Replay.applyEffects
    rw [List.foldl_cons, List.foldl_cons]
    exact SameReadings.applyEffects (h.apply x) fx

/-- An entry's effects read the state only through its machine, so two states answering alike step alike. -/
theorem SameReadings.stepWith {a b : State} (h : SameReadings a b) (z : Cal.Tz) (dy : Cal.Instant → Nat)
    (sl : Nat → Option Nat) (e : Entry) :
    SameReadings (Replay.stepWith z dy sl a e) (Replay.stepWith z dy sl b e) := by
  unfold Replay.stepWith
  have : effectsWith z dy sl a e = effectsWith z dy sl b e := by unfold effectsWith; rw [h.machine]
  rw [this]
  exact h.applyEffects _

theorem SameReadings.foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) {a b : State}, SameReadings a b →
      SameReadings (sv.foldl (Replay.stepWith z dy sl) a) (sv.foldl (Replay.stepWith z dy sl) b)
  | [], _, _, h => h
  | e :: sv, _, _, h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact SameReadings.foldl z dy sl sv (h.stepWith z dy sl e)

namespace KMap
variable {κ β : Type} [DecidableEq κ]

theorem mem_alterGo (k : κ) (f : Option β → Option β) (orig : KMap κ β) (q : κ × β) :
    ∀ (l acc : KMap κ β), orig = acc.reverse ++ l →
      q ∈ alterGo k f orig acc l → q.1 = k ∨ q ∈ orig := by
  intro l
  induction l with
  | nil =>
    intro acc ho hq
    unfold alterGo at hq
    split at hq
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr hq
    · exact Or.inr hq
  | cons p rest ih =>
    intro acc ho hq
    unfold alterGo at hq
    split at hq
    · split at hq
      · simp only [List.reverseAux_eq, List.mem_append, List.mem_cons, List.mem_reverse] at hq
        rcases hq with hq | rfl | hq
        · exact Or.inr (by rw [ho]; simp [hq])
        · exact Or.inl rfl
        · exact Or.inr (by rw [ho]; simp [hq])
      · simp only [List.reverseAux_eq, List.mem_append, List.mem_reverse, List.mem_filter] at hq
        rcases hq with hq | hq
        · exact Or.inr (by rw [ho]; simp [hq])
        · exact Or.inr (by rw [ho]; simp [hq.1])
    · exact ih (p :: acc) (by rw [ho]; simp) hq

/-- A pair of an altered map has the altered key or was in the map. -/
theorem mem_alter (m : KMap κ β) (k : κ) (f : Option β → Option β) (q : κ × β)
    (hq : q ∈ m.alter k f) : q.1 = k ∨ q ∈ m := by
  unfold alter at hq
  split at hq
  · split at hq
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr hq
    · exact Or.inr hq
  · exact mem_alterGo k f m q m [] (by simp) hq

theorem nodup_alterGo (k : κ) (f : Option β → Option β) (orig : KMap κ β)
    (hnd : (orig.map Prod.fst).Nodup) :
    ∀ (l acc : KMap κ β), orig = acc.reverse ++ l → (∀ q ∈ acc, q.1 ≠ k) →
      ((alterGo k f orig acc l).map Prod.fst).Nodup := by
  intro l
  induction l with
  | nil =>
    intro acc ho hacc
    unfold alterGo
    cases hf : f none with
    | some v =>
      refine List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩
      obtain ⟨q, hq, hqk⟩ := List.mem_map.1 hm
      rw [ho, List.append_nil] at hq
      exact hacc q (List.mem_reverse.1 hq) hqk
    | none => exact hnd
  | cons p rest ih =>
    intro acc ho hacc
    unfold alterGo
    by_cases hp : p.1 = k
    · rw [if_pos hp]
      have hnd' := hnd
      rw [ho, List.map_append] at hnd'
      cases hf : f (some p.2) with
      | some v =>
        simp only [List.reverseAux_eq]
        simpa [hp] using hnd'
      | none =>
        simp only [List.reverseAux_eq]
        have hnk : k ∉ rest.map Prod.fst := by
          have h2 : ((p :: rest).map Prod.fst).Nodup := (List.nodup_append.1 hnd').2.1
          rw [List.map_cons, List.nodup_cons] at h2
          rw [← hp]; exact h2.1
        rw [filter_key_of_not_mem _ _ hnk, List.map_append]
        exact (List.Sublist.append_left (List.Sublist.map Prod.fst (List.sublist_cons_self p rest)) _).nodup hnd'
    · rw [if_neg hp]
      exact ih (p :: acc) (by rw [ho]; simp) (fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp
        · exact hacc q hq)

/-- `alter` keeps a map's keys distinct, on every value type. -/
theorem nodup_alter (m : KMap κ β) (k : κ) (f : Option β → Option β) (hnd : (m.map Prod.fst).Nodup) :
    ((m.alter k f).map Prod.fst).Nodup := by
  unfold alter
  split
  · rename_i hg
    cases hf : f none with
    | some v =>
      refine List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩
      obtain ⟨q, hq, hqk⟩ := List.mem_map.1 hm
      exact ((get_eq_none_iff_keys m k).1 hg) q hq hqk
    | none => simpa using hnd
  · exact nodup_alterGo k f m hnd m [] (by simp) (by simp)

end KMap

namespace HMap
variable {κ β : Type} [DecidableEq κ] [KeyHash κ]

/-- **Every pair sits in its key's bucket, and no bucket holds a key twice**: what `empty`, `alter` and `mapVals`
keep. -/
def Keyed (m : HMap κ β) : Prop :=
  ∀ (i : Nat) (b : KMap κ β), m[i]? = some b →
    (b.map Prod.fst).Nodup ∧ ∀ q ∈ b, KeyHash.hash q.1 % m.size = i

omit [DecidableEq κ] in
theorem keyed_empty (n : Nat) : (empty n : HMap κ β).Keyed := by
  intro i b hb
  unfold empty at hb
  rw [Array.getElem?_replicate] at hb
  split at hb
  · cases hb; simp
  · cases hb

theorem keyed_alter (m : HMap κ β) (k : κ) (f : Option β → Option β) (hm : m.Keyed) : (m.alter k f).Keyed := by
  intro i b hb
  unfold alter at hb ⊢
  by_cases h0 : m.size = 0
  · rw [if_pos h0] at hb ⊢
    have hi : i = 0 := by
      rcases Nat.lt_or_ge i 1 with h | h
      · omega
      · rw [Array.getElem?_eq_none (by simpa using h)] at hb; cases hb
    subst hi
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hb
    subst hb
    refine ⟨KMap.nodup_alter _ k f (by simp), fun q _ => by simp [Nat.mod_one]⟩
  · rw [if_neg h0] at hb ⊢
    rw [Array.size_modify]
    rw [Array.getElem?_modify] at hb
    split at hb
    · rename_i hik
      cases hb0 : m[i]? with
      | none => rw [hb0] at hb; cases hb
      | some b0 =>
        rw [hb0] at hb
        simp only [Option.map_some, Option.some.injEq] at hb
        subst hb
        obtain ⟨hnd, hk⟩ := hm i b0 hb0
        refine ⟨KMap.nodup_alter b0 k f hnd, fun q hq => ?_⟩
        rcases KMap.mem_alter b0 k f q hq with hq | hq
        · rw [hq]; exact hik
        · exact hk q hq
    · exact hm i b hb

omit [DecidableEq κ] in
theorem keyed_mapVals {γ : Type} (m : HMap κ β) (f : β → γ) (hm : m.Keyed) : (m.mapVals f).Keyed := by
  intro i b hb
  unfold mapVals at hb ⊢
  simp only [List.getElem?_toArray, List.getElem?_map, Array.getElem?_toList] at hb
  cases hb0 : m[i]? with
  | none => rw [hb0] at hb; cases hb
  | some b0 =>
    rw [hb0] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    obtain ⟨hnd, hk⟩ := hm i b0 hb0
    refine ⟨by rw [List.map_map]; exact hnd, fun q hq => ?_⟩
    simp only [List.size_toArray, List.length_map, Array.length_toList]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact hk p hp

omit [DecidableEq κ] [KeyHash κ] in
theorem mem_foldl_pairs : ∀ (l : List (KMap κ β)) (acc : KMap κ β) (q : κ × β),
    q ∈ l.foldl (fun acc b => b ++ acc) acc ↔ q ∈ acc ∨ ∃ b ∈ l, q ∈ b
  | [], acc, q => by simp
  | b :: l, acc, q => by
    rw [List.foldl_cons, mem_foldl_pairs l (b ++ acc) q]
    simp only [List.mem_append, List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

omit [DecidableEq κ] in
theorem nodup_foldl_pairs (s : Nat) : ∀ (l : List (KMap κ β)) (j : Nat) (acc : KMap κ β),
    (∀ (i : Nat) (b : KMap κ β), l[i]? = some b →
      (b.map Prod.fst).Nodup ∧ ∀ q ∈ b, KeyHash.hash q.1 % s = j + i) →
    (acc.map Prod.fst).Nodup → (∀ q ∈ acc, KeyHash.hash q.1 % s < j) →
    ((l.foldl (fun acc b => b ++ acc) acc).map Prod.fst).Nodup
  | [], _, _, _, hacc, _ => hacc
  | b :: l, j, acc, hl, hacc, hlt => by
    rw [List.foldl_cons]
    obtain ⟨hb, hbk⟩ := hl 0 b rfl
    refine nodup_foldl_pairs s l (j + 1) (b ++ acc) (fun i c hc => ?_) ?_ ?_
    · obtain ⟨h1, h2⟩ := hl (i + 1) c (by simpa using hc)
      exact ⟨h1, fun q hq => by rw [h2 q hq]; omega⟩
    · rw [List.map_append, List.nodup_append]
      refine ⟨hb, hacc, fun x hx y hy hxy => ?_⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
      have h1 := hbk p hp
      have h2 := hlt r hr
      rw [hxy] at h1
      omega
    · intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · rw [hbk q hq]; omega
      · have := hlt q hq; omega

omit [DecidableEq κ] in
/-- A keyed map's pairs hold each key once. -/
theorem nodup_keys_pairs (m : HMap κ β) (hm : m.Keyed) : (m.pairs.map Prod.fst).Nodup := by
  unfold pairs
  exact nodup_foldl_pairs m.size m.toList 0 [] (fun i b hb => by
    rw [Array.getElem?_toList] at hb
    obtain ⟨h1, h2⟩ := hm i b hb
    exact ⟨h1, fun q hq => by rw [h2 q hq]; omega⟩) (by simp) (by simp)

/-- A keyed map's pairs hold exactly the keys `get` finds. -/
theorem mem_keys_pairs_iff (m : HMap κ β) (hm : m.Keyed) (k : κ) :
    k ∈ m.pairs.map Prod.fst ↔ (m.get k).isSome := by
  unfold pairs
  constructor
  · intro hk
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hk
    rcases (mem_foldl_pairs _ _ q).1 hq with hq | ⟨b, hb, hqb⟩
    · cases hq
    · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hb
      rw [Array.getElem?_toList] at hi
      have hh := (hm i b hi).2 q hqb
      unfold get
      rw [hh, hi]
      show (b.get q.1).isSome = true
      cases hg : KMap.get b q.1 with
      | some _ => rfl
      | none => exact absurd rfl ((KMap.get_eq_none_iff_keys b q.1).1 hg q hqb)
  · intro hk
    unfold get at hk
    cases hb : m[KeyHash.hash k % m.size]? with
    | none => rw [hb] at hk; cases hk
    | some b =>
      rw [hb] at hk
      change (b.get k).isSome = true at hk
      cases hg : KMap.get b k with
      | none => rw [hg] at hk; cases hk
      | some v =>
        obtain ⟨q, hq, hqk⟩ := List.mem_map.1 (KMap.mem_keys_of_get b k v hg)
        refine List.mem_map.2 ⟨q, (mem_foldl_pairs _ _ q).2 (Or.inr ⟨b, ?_, hq⟩), hqk⟩
        exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hb)

/-- **Two keyed maps that read alike hold one set of keys**, in whatever order their buckets give. -/
theorem perm_keys_pairs (m m' : HMap κ β) (hm : m.Keyed) (hm' : m'.Keyed) (h : ∀ k, m.get k = m'.get k) :
    (m.pairs.map Prod.fst).Perm (m'.pairs.map Prod.fst) :=
  (List.perm_ext_iff_of_nodup (nodup_keys_pairs m hm) (nodup_keys_pairs m' hm')).2 (fun k => by
    rw [mem_keys_pairs_iff m hm, mem_keys_pairs_iff m' hm', h k])

omit [DecidableEq κ] [KeyHash κ] in
theorem keys_pairs_mapVals {γ : Type} (m : HMap κ β) (f : β → γ) :
    (m.mapVals f).pairs.map Prod.fst = m.pairs.map Prod.fst := by
  unfold pairs mapVals
  suffices ∀ (l : List (KMap κ β)) (acc : KMap κ γ) (acc' : KMap κ β), acc.map Prod.fst = acc'.map Prod.fst →
      (((l.map (fun b => b.map (fun p => (p.1, f p.2)))).foldl (fun acc b => b ++ acc) acc).map Prod.fst)
        = ((l.foldl (fun acc b => b ++ acc) acc').map Prod.fst) from this _ [] [] rfl
  intro l
  induction l with
  | nil => intro acc acc' h; exact h
  | cons b l ih =>
    intro acc acc' h
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    simp [List.map_append, h, List.map_map]

end HMap

theorem minDay?_perm {l₁ l₂ : List Nat} (p : l₁.Perm l₂) : minDay? l₁ = minDay? l₂ := by
  unfold minDay?
  exact p.foldl_eq' (fun x _ y _ z => by cases z <;> simp [Nat.min_comm, Nat.min_left_comm]) none

theorem maxDay?_perm {l₁ l₂ : List Nat} (p : l₁.Perm l₂) : maxDay? l₁ = maxDay? l₂ := by
  unfold maxDay?
  exact p.foldl_eq' (fun x _ y _ z => by cases z <;> simp [Nat.max_comm, Nat.max_left_comm]) none

/-- The two maps the view reads by their pairs (`lastDay`; `doneFirst` and `doneCount`) are keyed. -/
def PairsKeyed (st : State) : Prop := st.days.Keyed ∧ st.doneDates.Keyed

theorem pairsKeyed_init (n : Nat) : PairsKeyed (State.init n) := ⟨HMap.keyed_empty n, HMap.keyed_empty n⟩

theorem PairsKeyed.apply {a : State} (h : PairsKeyed a) (x : Effect) : PairsKeyed (applyEffect a x) := by
  cases x with
  | dayAdd d op => exact ⟨HMap.keyed_alter _ _ _ h.1, h.2⟩
  | doneDate i d => exact ⟨h.1, HMap.keyed_alter _ _ _ h.2⟩
  | obs ob => cases ob <;> exact h
  | itemDaySub i d m =>
    simp only [applyEffect]
    split
    · exact h
    · exact h
  | _ => exact h

theorem PairsKeyed.foldl (z : Cal.Tz) (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) :
    ∀ (sv : List Entry) {a : State}, PairsKeyed a → PairsKeyed (sv.foldl (Replay.stepWith z dy sl) a)
  | [], _, h => h
  | e :: sv, a, h => by
    rw [List.foldl_cons]
    refine PairsKeyed.foldl z dy sl sv ?_
    unfold Replay.stepWith Replay.applyEffects
    generalize effectsWith z dy sl a e = fx
    induction fx generalizing a with
    | nil => exact h
    | cons x fx ih => rw [List.foldl_cons]; exact ih (a := applyEffect a x) (h.apply x)

theorem doneKeys_filter (l : KMap (Nat × Log.Id) Unit) (i : Log.Id) :
    (l.filter (fun p => decide (p.1.2 = i))).map (·.1.1)
      = ((l.map Prod.fst).filter (fun k => decide (k.2 = i))).map (·.1) := by
  rw [List.filter_map, List.map_map]; rfl

theorem doneCount_filter (l : KMap (Nat × Log.Id) Unit) (i : Log.Id) :
    (l.filter (fun p => decide (p.1.2 = i))).length
      = ((l.map Prod.fst).filter (fun k => decide (k.2 = i))).length := by
  rw [List.filter_map, List.length_map]; rfl

/-- **Two states answering alike finish to one view**, whatever their maps' bucket counts: every reading goes through
`get`, and the three readings of a map's pairs through its keys, one set up to order (`HMap.perm_keys_pairs`),
folded by a minimum, a maximum or a count. -/
theorem factsView_finish_of_sameReadings {a b : State} (h : SameReadings a b) (ha : PairsKeyed a)
    (hb : PairsKeyed b) : factsView (finish a) = factsView (finish b) := by
  funext q
  cases q with
  | day d dq =>
    cases dq <;> simp only [factsView, finish, HMap.get_mapVals, h.days, h.seams, h.energy, h.durations,
      h.interrupts, h.demotions, h.closes, h.machine]
  | win d wq =>
    cases wq <;> simp only [factsView, finish, Facts.doneOn, Facts.instance, h.itemDays, h.doneDates, h.instances]
  | lastDay =>
    simp only [factsView, finish]
    rw [HMap.keys_pairs_mapVals, HMap.keys_pairs_mapVals,
      maxDay?_perm (HMap.perm_keys_pairs _ _ ha.1 hb.1 h.days)]
  | doneFirst i =>
    simp only [factsView, finish, Facts.doneDatesOf, doneDatesIn]
    rw [doneKeys_filter, doneKeys_filter,
      minDay?_perm (((HMap.perm_keys_pairs _ _ ha.2 hb.2 h.doneDates).filter _).map _)]
  | doneCount i =>
    simp only [factsView, finish, Facts.doneDatesOf, doneDatesIn, List.length_map]
    rw [doneCount_filter, doneCount_filter, ((HMap.perm_keys_pairs _ _ ha.2 hb.2 h.doneDates).filter _).length_eq]
  | _ =>
    simp only [factsView, finish, HMap.get_mapVals, Facts.lastDone, Facts.instance, Facts.namedAt, h.items,
      h.lastDone, h.dropped, h.instances, h.named, h.machine, h.global, h.unknown, h.longestLeak, h.rwarns]

/-- **The replay's view reads only the survivors**: two logs with one list of survivors have one view, however many
lines each holds (the replay sizes its maps by the log's length, and the view does not see it). -/
theorem the_view_reads_only_the_survivors (z : Cal.Tz) (es es' : List Entry) (h : survivors es = survivors es') :
    factsView (replay z es) = factsView (replay z es') := by
  have hs : ∀ kw sl, step z kw sl = Replay.stepWith z (dayOf z kw) (KMap.get sl) := fun _ _ => rfl
  unfold replay dayIndexOf
  rw [h, hs]
  exact factsView_finish_of_sameReadings (SameReadings.foldl _ _ _ _ (sameReadings_init _ _))
    (PairsKeyed.foldl _ _ _ _ (pairsKeyed_init _)) (PairsKeyed.foldl _ _ _ _ (pairsKeyed_init _))

end BucketFree

/-! ### The law, its corollaries, and the two quirks -/

section UndoLaws

/-- **`undoing_a_command_replays_the_log_without_it`** (Goals, §15, C7; §7.3): `tm undo` of a command whose events
`E` are followed by events `M` it did not write replays, fact for fact, as the log without the command.  Stated
without §15's `hl`, which the law does not need (the mask's half is about entries, not lines); §15's statement is
this theorem given fewer arguments.  `o`, the offset `ctx.now` is written at, is §15's `undosFor` made total. -/
theorem undoing_a_command_replays_the_log_without_it (z : Cal.Tz) (L E M : List Entry) (n : Nat)
    (t : Cal.VInstant) (o : Cal.VOffset)
    (hE : E.all (fun e => !e.ev.isUndo) = true) (hM : untouchedBy E M = true) :
    factsView (replay z (L ++ E ++ M ++ undosFor E n t o)) = factsView (replay z (L ++ M)) :=
  the_view_reads_only_the_survivors z _ _ (undoing_a_command_leaves_the_survivors_of_the_log_without_it L E M n t o hE hM)

/-- **The first draft's law** (§7.3): with nothing after the command, its undo replays the log without it. -/
theorem undoing_the_last_command_replays_the_log_without_it (z : Cal.Tz) (L E : List Entry) (n : Nat)
    (t : Cal.VInstant) (o : Cal.VOffset) (hE : E.all (fun e => !e.ev.isUndo) = true) :
    factsView (replay z (L ++ E ++ undosFor E n t o)) = factsView (replay z L) := by
  have h := undoing_a_command_replays_the_log_without_it z L E [] n t o hE (by simp [untouchedBy])
  simpa using h

/-- **Every query but the line bookkeeping** (W1's laws read `ask`): the undone log and the log without the command
answer it alike. -/
theorem undoing_a_command_answers_every_fact_query_as_the_log_without_it (z : Cal.Tz) (L E M : List Entry)
    (n : Nat) (t : Cal.VInstant) (o : Cal.VOffset)
    (hE : E.all (fun e => !e.ev.isUndo) = true) (hM : untouchedBy E M = true)
    (q : Q) (hh : ∀ d, q ≠ .day d .headers) (he : q ≠ .entryCount) :
    ask (replayDoc z (L ++ E ++ M ++ undosFor E n t o)) q = ask (replayDoc z (L ++ M)) q := by
  rw [ask_reads_the_facts _ q hh he, ask_reads_the_facts _ q hh he]
  exact congrFun (undoing_a_command_replays_the_log_without_it z L E M n t o hE hM) q

/-- **Quirk Q6(d), ported faithfully** (gap 84): a command that logged nothing (`tm rank`; a `move` or `readopt` on
an id-less line; a `close` that closed nothing) is undone by `undo{of: verb}` with no id, which cancels the latest
surviving event whose tag is the verb's name, an older command's. -/
theorem a_silent_verb_undo_cancels_the_latest_event_of_its_name (es : List Entry) (u : Entry) (verb : List Char)
    (h : u.ev = .undo verb none) :
    survivors (es ++ [u]) = ((survivors es).reverse.eraseP (fun e => e.ev.tag == verb)).reverse := by
  rw [survivors_snoc_undo es u verb none h]
  congr 2
  funext e
  simp [«matches»]

/-- **The separation of quirk Q6(d) from its fix** (`of: "verb:<name>"`, which names no event, so cancels nothing):
the silent-verb undo leaves the survivors alone exactly when no survivor carries the verb's name. -/
theorem a_silent_verb_undo_cancels_nothing_iff_no_survivor_has_its_name (es : List Entry) (u : Entry)
    (verb : List Char) (h : u.ev = .undo verb none) :
    survivors (es ++ [u]) = survivors es ↔ ∀ e ∈ survivors es, e.ev.tag ≠ verb := by
  rw [a_silent_verb_undo_cancels_the_latest_event_of_its_name es u verb h]
  constructor
  · intro heq
    have h2 : (survivors es).reverse.eraseP (fun e => e.ev.tag == verb) = (survivors es).reverse := by
      have := congrArg List.reverse heq
      simpa using this
    intro e he hte
    exact (List.eraseP_eq_self_iff.1 h2) e (List.mem_reverse.2 he) (by simp [hte])
  · intro hall
    rw [List.eraseP_eq_self_iff.2 (fun e he hte => hall e (List.mem_reverse.1 he) (by simpa using hte)),
      List.reverse_reverse]

end UndoLaws

/-! ## Witnesses (C7)

Probed in a scratch copy under `MemoryMax=8G timeout 120` (§14.0 item 4): at most 3 entries, `utcZone`, instants as
`Nat` literals.  2026-09-07T09:00:00Z is second 63924368400, and the day is 739865. -/

section UndoWitnesses7

/-- The stamp of the witnesses' undos: 09:02 UTC. -/
def undoStamp : Cal.VInstant := ⟨⟨63924368520, 0⟩, by decide⟩

def undoOffset : Cal.VOffset := ⟨⟨false, 0⟩, by decide⟩

theorem move_toList : "move".toList = ['m', 'o', 'v', 'e'] := by decide

/-- `undo_of_a_silent_verb_cancels_an_older_event` (Goals, §15, C7; §7.3's witness): `L = [move a]`, and the undo
of a silent `tm move` writes `undo{of:"move"}`, which takes `L`'s move. -/
theorem undo_of_a_silent_verb_cancels_an_older_event :
    ∃ (L : List Entry) (u : Entry), u.ev = .undo "move".toList none ∧ survivors (L ++ [u]) ≠ survivors L :=
  ⟨[bE 1 63924368400 (.move ['a'] ['w'] ['b'])], bE 2 63924368460 (.undo ['m', 'o', 'v', 'e'] none),
    by rw [move_toList]; rfl, by decide⟩

/-- `undo_after_housekeeping_cancels_the_housekeeping` (Goals, §15, C7, with `undosFor`'s offset): `E` is a close,
`M` is a later verb's automatic close of **the same period**, and `undosFor E = [undo{of:"close", id:"week:k"}]`.
`M`'s close matches the undo, so `untouchedBy` fails, and the survivors are `E`'s close, not `M`'s.

**The witness changed at W-12, and the reason is quirk Q6(f) being fixed** (gap 86).  It used to be
`E = [close week]` against `M = [close day]` — a close of a *different* period — because `close` had no primary
id and an undo of one close cancelled whichever close was latest.  Now a close carries `period:key`, so those two
no longer match and that pair satisfies `untouchedBy`: the law applies to it, which is exactly the fix.  The law
still needs its hypothesis, so the witness is the case that still bites — the **same** period closed twice, which
is what `tm close week` followed by a sweep of the same ended week leaves.  The statement is unchanged; only the
log that exhibits it is (AGENTS §3.1: re-proved, never weakened). -/
theorem undo_after_housekeeping_cancels_the_housekeeping :
    ∃ (L E M : List Entry) (n : Nat) (t : Cal.VInstant) (o : Cal.VOffset),
      E.all (fun e => !e.ev.isUndo) = true ∧ untouchedBy E M = false ∧
      survivors (L ++ E ++ M ++ undosFor E n t o) ≠ survivors (L ++ M) :=
  ⟨[], [bE 1 63924368400 (.close ['w', 'e', 'e', 'k'] ['k'])], [bE 2 63924368460 (.close ['w', 'e', 'e', 'k'] ['k'])], 3,
    undoStamp, undoOffset, by decide, by decide, by decide⟩

/-- **Q6(f)'s fix, stated as the law reaching further** (gap 86): the pair that used to be the counterexample —
a week close and the next verb's automatic **day** close — now satisfies `untouchedBy`, so the undo law applies to
it and `tm undo` of the week close leaves the automatic one alone. -/
theorem an_automatic_close_of_another_period_is_untouched :
    untouchedBy [bE 1 63924368400 (.close ['w', 'e', 'e', 'k'] ['k'])]
      [bE 2 63924368460 (.close ['d', 'a', 'y'] ['k'])] = true := by
  decide

/-- **The refutation twin: the law fails without `untouchedBy`**, in its conclusion, not only in the survivors.  On
the housekeeping witness the undone log's closes on 2026-09-07 are the week's, and the log without the command's
are the day's. -/
theorem the_undo_law_fails_without_untouchedBy :
    ∃ (z : Cal.Tz) (L E M : List Entry) (n : Nat) (t : Cal.VInstant) (o : Cal.VOffset),
      E.all (fun e => !e.ev.isUndo) = true ∧ untouchedBy E M = false ∧
      factsView (replay z (L ++ E ++ M ++ undosFor E n t o)) ≠ factsView (replay z (L ++ M)) := by
  refine ⟨utcZone, [], [bE 1 63924368400 (.close ['w', 'e', 'e', 'k'] ['k'])],
    [bE 2 63924368460 (.close ['w', 'e', 'e', 'k'] ['k'])], 3, undoStamp, undoOffset, by decide, by decide, fun h => ?_⟩
  have := congrFun h (.day 739865 .closes)
  revert this
  decide

/-- **The hypothesis holds of the common case**: `tm done a` (a `done` and a routine `done`), the next verb's
automatic `close day`, then `tm undo`.  Neither undo matches the close, so the law applies. -/
theorem a_done_undone_over_an_automatic_close_is_untouched :
    untouchedBy [bE 1 63924368400 (bDone ['a'] 30 false), bE 2 63924368460 (rDone ['s'] ['#', '1'])]
      [bE 3 63924368520 (.close ['d', 'a', 'y'] ['k'])] = true := by
  decide

end UndoWitnesses7

/-! ## The owner's D87 (README gap 4137, parity P81): a break taken inside a block is not block time

`tm stop` nets a break that fell inside the block it stops ("after 40m"), and so does the `actual_min` `tm done` logs;
fork `Machine::step`'s `Break` arm touched no block, so the replay credited a block cut by `stop` (or by the next
`start`) its whole span and drew its `Block` segment across the `Break` one — `tm review day` read 60 where `tm stop`
said 40, and the heat grid counted the break as break and as block.  `brkFx` is the one definition now: a `break`
stepped while the open block's clock runs closes the running sub-segment at the break's start and restarts the clock
at its end (`brkEnd`), so every reader of the day — the credit, the segments, the open block — reads the block's
worked minutes.  Each witness was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most four
entries, `utcZone`, instants as `Nat` literals.  2026-09-07T09:00:00Z is second 63924368400; the day is 739865. -/

section BreakWitnesses87

open Log (Id U8 U32 Num)

/-- **A break inside a stopped block is not block time**: `start a` 09:00, a twenty-minute `break` at 09:30, `stop a`
10:00.  The block is credited its 40 worked minutes — the item, its day, the day's block minutes and its ci-unknown
minutes — and drawn as `[09:00, 09:30]` and `[09:50, 10:00]` beside the break's `[09:30, 09:50]`.  Fork `step`
credited 60 and drew one block `[09:00, 10:00]` across the break (parity P81). -/
theorem a_break_inside_a_stopped_block_is_not_block_time :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.brk 20 (some 20) none),
      bE 3 63924372000 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 40 ∧ f.itemDays.get (739865, ['a']) = some 40 ∧
    (f.days.get 739865).map (fun a => (a.blockMin, a.ciUnknown)) = some (40, [(['a'], 40)]) ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924368400, 63924370200, .block ['a']), (63924370200, 63924371400, .brk none),
              (63924371400, 63924372000, .block ['a'])] := by
  decide

/-- **A `done` still credits what it logs, and its block is still split**: `start a` 09:00, a twenty-minute `break`
at 09:30, `done a` with 40 minutes at 10:00.  The 40 the `done` carries is credited (the logged minutes are
authoritative, as before D87), at its ci; what moved is the drawing — no `Block` segment lies across the break. -/
theorem a_done_after_a_break_credits_its_minutes_and_splits_its_block :
    let f := replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.brk 20 (some 20) none),
      bE 3 63924372000 (bDone ['a'] 40 false)]
    (f.items.get ['a']).map (·.minutes) = some 40 ∧
    (f.days.get 739865).map (fun a => (a.blockMin, a.byCi.c3)) = some (40, 40) ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924368400, 63924370200), (63924370200, 63924371400), (63924371400, 63924372000)] := by
  decide

/-- **The open block restarts at the break's end**: `start a` 09:00 and a twenty-minute `break` at 09:30, and nothing
after.  The open block has banked the 30 minutes before the break and runs again from 09:50, so its worked minutes at
any instant are net of the break — the reading `tm now` and `tm stop` already print. -/
theorem the_open_block_restarts_at_the_breaks_end :
    (replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.brk 20 (some 20) none)]).openBlock.map
        (fun b => (b.workedMin, b.since.map (·.1.sec), b.paused))
      = some (30, some 63924371400, false) := by
  decide

/-- **A break with no `actual_min` nets its planned minutes** — the span its `Break` segment is drawn over
(`brkEnd`): `start a` 09:00, a `break` planned 15 at 09:30 with no actual, `stop a` 10:00.  Credited 45. -/
theorem a_break_with_no_actual_nets_its_planned_minutes :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.brk 15 none none),
        bE 3 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 45 := by
  decide

/-- **A break while the block is paused changes nothing**: `start a` 09:00, `pause a` 09:10, a ten-minute `break` at
09:20, `unpause a` 09:40, `stop a` 10:00.  The clock was stopped by the pause, so the break nets nothing more: 10 +
20 = 30 minutes, the pause's segment `[09:10, 09:40]` and the break's `[09:20, 09:30]` both drawn. -/
theorem a_break_while_the_block_is_paused_changes_nothing :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369000 (.pause ['a']),
        bE 3 63924369600 (.brk 10 (some 10) none), bE 4 63924370800 (.unpause ['a']),
        bE 5 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 30 := by
  decide

/-- **D87's edge (README gap 4241), as D87 left it, is refuted** — the owner's D92 closed it (parity P85).  The
statement W-42 track R proved: a ten-minute `break` at 08:55, `start a` 09:00, `stop a` 10:00 credited 60 minutes,
the two segments overlapping by five, while the host's `Replay::idle_min_since` netted the five.  It now credits 55
(`a_break_logged_before_its_blocks_start_is_netted`, in the section of the D92 witnesses below). -/
theorem a_break_logged_before_its_blocks_start_is_not_netted_is_refuted :
    ¬ ((replay utcZone [bE 1 63924368100 (.brk 10 (some 10) none), bE 2 63924368400 (bStart ['a']),
        bE 3 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/-- **C5's `arm_split` over every event is refuted** (D87): with a block running, a `break`'s arm is neither its day
family arm alone (it also stops the block's clock) nor block family effects alone (its own segment and record are a
day family's).  `arm_split` is the form that holds, and `arm_split_of_not_brk` keeps C5's statement on every other
event. -/
theorem arm_split_as_c5_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat),
      arm dy sl m e t d = dayArm dy sl e t d ∨
        ((∀ x ∈ arm dy sl m e t d, x.blockOnly = true) ∧ dayArm dy sl e t d = []) := by
  intro h
  let m : Machine := ⟨some ⟨['a'], (⟨63924368400, 0⟩, ⟨false, 0⟩), some (⟨63924368400, 0⟩, ⟨false, 0⟩), false, none,
    0, none, 739865, [], [], 0⟩, none, none, [], none, [], none⟩
  let e := bE 2 63924370200 (.brk 20 (some 20) none)
  rcases h (fun _ => 739865) (fun _ => none) m e (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865 with h1 | ⟨-, h2⟩
  · revert h1; decide
  · revert h2; decide

end BreakWitnesses87

/-! ## The owner's D92 (README gap 4241, parity P85): a break that runs into a block's start is not block time

A `break` line is written when the break ends, so a block begun after it can only begin inside it if the log was
written by something other than the binary — `tm start` ends a running break before it logs its `start` — and
generated logs do (`loggen`'s breaks outlast its 22-minute gap: 22 in the generated month).  The host's
`Replay::idle_min_since` clipped every break's span to the block's and the replay credited and drew the overlap; the
machine now remembers the last break's span (`Machine.brk`) and every place a clock starts — a `start`, an `unpause`,
a `resume` — starts it at the break's end when it falls inside (restartAt; `settle` since D99).  Each witness was probed in a scratch
copy under `MemoryMax=8G timeout 120` (§5.10a): at most five entries, `utcZone`, instants as `Nat` literals.
2026-09-07T09:00:00Z is second 63924368400; the day is 739865. -/

section BreakWitnesses92

open Log (Id U8 U32 Num)

/-- **A break logged before a block's `start` and lasting into it is netted** (gap 4241's edge, closed): a ten-minute
`break` at 08:55, `start a` 09:00, `stop a` 10:00.  The block is credited its 55 minutes after the break — the item,
its day, the day's block minutes and ci-unknown minutes — and drawn as `[09:05, 10:00]` beside the break's
`[08:55, 09:05]`.  Fork `step` credited 60 and drew `[09:00, 10:00]` across the break (parity P85). -/
theorem a_break_logged_before_its_blocks_start_is_netted :
    let f := replay utcZone [bE 1 63924368100 (.brk 10 (some 10) none), bE 2 63924368400 (bStart ['a']),
      bE 3 63924372000 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 55 ∧ f.itemDays.get (739865, ['a']) = some 55 ∧
    (f.days.get 739865).map (fun a => (a.blockMin, a.ciUnknown)) = some (55, [(['a'], 55)]) ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924368100, 63924368700, .brk none), (63924368700, 63924372000, .block ['a'])] := by
  decide

/-- **The open block begins at the break's end**: a ten-minute `break` at 08:55 and `start a` 09:00, nothing after.
The open block has banked nothing and runs from 09:05 — the reading `tm now` and `tm stop` already print. -/
theorem an_open_block_begun_inside_a_break_runs_from_its_end :
    (replay utcZone [bE 1 63924368100 (.brk 10 (some 10) none), bE 2 63924368400 (bStart ['a'])]).openBlock.map
        (fun b => (b.workedMin, b.since.map (·.1.sec), b.paused))
      = some (0, some 63924368700, false) := by
  decide

/-- **A `done` still credits what it logs, and its block is drawn after the break**: a ten-minute `break` at 08:55,
`start a` 09:00, `done a` with 55 minutes at 10:00.  The 55 the `done` carries is credited at its ci; what moved is
the drawing — no `Block` segment lies across the break. -/
theorem a_done_begun_inside_a_break_credits_its_minutes_and_is_drawn_after_it :
    let f := replay utcZone [bE 1 63924368100 (.brk 10 (some 10) none), bE 2 63924368400 (bStart ['a']),
      bE 3 63924372000 (bDone ['a'] 55 false)]
    (f.items.get ['a']).map (·.minutes) = some 55 ∧
    (f.days.get 739865).map (fun a => (a.blockMin, a.byCi.c3)) = some (55, 55) ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924368100, 63924368700), (63924368700, 63924372000)] := by
  decide

/-- **An `unpause` inside a break restarts the clock at the break's end** — the one rule at every place a clock
starts: `start a` 09:00, `pause a` 09:10, a twenty-minute `break` at 09:15 (stepped while paused: no clock to stop),
`unpause a` 09:30, `stop a` 10:00.  Credited 10 + 25 = 35, the host's reading (its union of `[09:10, 09:30]` and
`[09:15, 09:35]`); before D92 the clock restarted at 09:30 and credited 40. -/
theorem an_unpause_inside_a_break_restarts_the_clock_at_its_end :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369000 (.pause ['a']),
        bE 3 63924369300 (.brk 20 (some 20) none), bE 4 63924370200 (.unpause ['a']),
        bE 5 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 35 := by
  decide

/-- **A `resume` inside a break restarts the clock at the break's end**: `start a` 09:00, `interrupt` 09:10, a
twenty-minute `break` at 09:15, `resume` 09:30, `stop a` 10:00.  Credited 10 + 25 = 35; before D92, 40. -/
theorem a_resume_inside_a_break_restarts_the_clock_at_its_end :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369000 (.interrupt none),
        bE 3 63924369300 (.brk 20 (some 20) none), bE 4 63924370200 (.resume 15 []),
        bE 5 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 35 := by
  decide

/-- **A break the `start` itself ended nets nothing** — the binary's own log (`tm start` ends a running break at its
own instant, so the break ends where the block begins): a twenty-minute `break` at 08:40, `start a` 09:00, `stop a`
10:00.  Credited 60. -/
theorem a_break_the_start_ended_nets_nothing :
    ((replay utcZone [bE 1 63924367200 (.brk 20 (some 20) none), bE 2 63924368400 (bStart ['a']),
        bE 3 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/-- **D92's edge (README gap 4361), as D92 left it, is refuted** — the owner's D94 closed it (parity P92).  The
statement W-43 track K proved: a ten-minute `break` at 09:05 logged ahead of `start a` 09:00, `stop a` 10:00 credited
60 minutes while the host's `Replay::idle_min_since` netted the ten.  It now credits 50
(`a_break_logged_before_a_start_but_begun_after_it_is_netted`, in the section of the D94 witnesses below). -/
theorem a_break_logged_before_a_start_but_begun_after_it_is_not_netted_is_refuted :
    ¬ ((replay utcZone [bE 1 63924368700 (.brk 10 (some 10) none), bE 2 63924368400 (bStart ['a']),
        bE 3 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

end BreakWitnesses92

/-! ## The owner's D94 (README gaps 4361 and 4506, parity P92): every break on a block's ledger days is netted

A clock behind the log — a `--now` moved backwards, or two machines syncing one plan directory (D78's world) — leaves a
`break` stepped before a `start` it began after (gap 4361), or a block's clock (re)started inside a break that is not
the last one stepped (gap 4506), or two breaks overlapping.  The host's `Replay::idle_min_since` unions every break of
the block's ledger days; D92's machine remembered the last break stepped and read it only where a clock starts.  The
machine now holds every break within `maxKeepDays` ledger days of the newest (`Machine.brks`, `pruneBrks`), and every
clock read nets the ones on the block's ledger days (`spansFor`): where the clock (re)starts (restartAt then, `lift`),
where a stretch is closed (closeSub then, `pieces`; both `settle` since D99), and the open block read at the end of the log (`openOf`).  A break
filed on a ledger day before the block's `start`'s — a wake between them — is not one of the block's, for the host
or the replay.  Each witness was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most six
entries, `utcZone`, instants as `Nat` literals.  2026-09-07T09:00:00Z is second 63924368400; the day is 739865, and
2026-09-07T07:00:00Z is 63924361200. -/

section BreakWitnesses94

open Log (Id U8 U32 Num)

/-- **A break logged ahead of a start but begun after it is netted** (gap 4361, closed): a ten-minute `break` at
09:05 logged ahead of `start a` 09:00, `stop a` 10:00.  Credited 50, the host's union; drawn `[09:00, 09:05]` and
`[09:15, 10:00]` beside the break's `[09:05, 09:15]`.  D92 credited 60 and drew one block across the break. -/
theorem a_break_logged_before_a_start_but_begun_after_it_is_netted :
    let f := replay utcZone [bE 1 63924368700 (.brk 10 (some 10) none), bE 2 63924368400 (bStart ['a']),
      bE 3 63924372000 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧
    (f.days.get 739865).map (fun a => (a.blockMin, a.ciUnknown)) = some (50, [(['a'], 50)]) ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924368400, 63924368700, .block ['a']), (63924368700, 63924369300, .brk none),
              (63924369300, 63924372000, .block ['a'])] := by
  decide

/-- **A clock started inside an earlier break, a later one stepped between, nets both** (gap 4506, closed): a
thirty-minute `break` at 09:00, a five-minute one at 09:40, `start a` 09:10, `stop a` 10:00.  The clock starts at the
first break's end (09:30) and the stretch is cut around the second: 10 + 15 = 25, the host's union (driven: `tm stop`
"after 25m").  D92 credited 50. -/
theorem a_start_inside_an_earlier_break_nets_every_break_held :
    let f := replay utcZone [bE 1 63924368400 (.brk 30 (some 30) none), bE 2 63924370800 (.brk 5 (some 5) none),
      bE 3 63924369000 (bStart ['a']), bE 4 63924372000 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 25 ∧
    (f.days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .block ['a'])).map
      (fun g => (g.start.1.sec, g.stop.1.sec))) = some [(63924370200, 63924370800), (63924371100, 63924372000)] := by
  decide

/-- **Overlapping breaks are netted as their union**: a thirty-minute `break` at 09:00, a ten-minute one at 09:10
inside it, `start a` 09:15 (inside both), `stop a` 10:00.  The clock starts past both — 09:30 — and credits 30, the host's
union (driven: `tm stop` "after 30m"); D92 restarted it at the later-stepped break's end, 09:20, and credited 40. -/
theorem a_start_inside_overlapping_breaks_runs_from_their_union_end :
    ((replay utcZone [bE 1 63924368400 (.brk 30 (some 30) none), bE 2 63924369000 (.brk 10 (some 10) none),
        bE 3 63924369300 (bStart ['a']), bE 4 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 30 := by
  decide

/-- **An `unpause` inside an earlier break, a later one stepped between, nets both**: `start a` 09:00, `pause a`
09:05, a fifteen-minute `break` at 10:00, a five-minute one at 10:30, `unpause a` 10:05, `stop a` 11:00.  Credited
5 + 15 + 25 = 45, the host's union (driven); D92 credited 60. -/
theorem an_unpause_inside_an_earlier_break_nets_every_break_held :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924368700 (.pause ['a']),
        bE 3 63924372000 (.brk 15 (some 15) none), bE 4 63924373800 (.brk 5 (some 5) none),
        bE 5 63924372300 (.unpause ['a']), bE 6 63924375600 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 45 := by
  decide

/-- **A `resume` inside an earlier break, a later one stepped between, nets both**: `start a` 09:00, `interrupt`
09:05, a fifteen-minute `break` at 10:00, a five-minute one at 10:30, `resume` 10:05, `stop a` 11:00.  Credited 45,
the host's union (driven); D92 credited 60. -/
theorem a_resume_inside_an_earlier_break_nets_every_break_held :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924368700 (.interrupt none),
        bE 3 63924372000 (.brk 15 (some 15) none), bE 4 63924373800 (.brk 5 (some 5) none),
        bE 5 63924372300 (.resume 60 []), bE 6 63924375600 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 45 := by
  decide

/-- **The open block is read past a break its clock has not yet been closed across** (gap 4361 while the block runs):
a fifteen-minute `break` at 10:00 logged ahead of `start a` 09:50, and nothing after.  The open block has banked the
ten minutes before the break and runs from its end, 10:15 — so at 10:30 it reads 25, `tm now`'s header (driven), and
its row is drawn from 10:15.  D92 read it as running from 09:50, 40 at 10:30, its row across the break. -/
theorem the_open_block_is_read_past_a_break_held_ahead_of_its_clock :
    (replay utcZone [bE 1 63924372000 (.brk 15 (some 15) none), bE 2 63924371400 (bStart ['a'])]).openBlock.map
        (fun b => (b.workedMin, b.since.map (·.1.sec), b.paused))
      = some (10, some 63924372900, false) := by
  decide

/-- **A break filed on the ledger day before the block's is not the block's** (README gap 4363, closed): a wake on
2026-09-06 at 07:00, a thirty-minute `break` at 06:50 on the 7th (before that day's wake, so filed on the 6th), the
7th's wake at 07:00, `start a` 07:10, `stop a` 08:00.  The host reads the block's idle marks from the 7th on and nets
nothing: 50 (driven).  D92 restarted the clock at the break's end and credited 40. -/
theorem a_break_on_the_ledger_day_before_the_blocks_is_not_netted :
    ((replay utcZone [bE 1 63924274800 (.wake 420 none), bE 2 63924360600 (.brk 30 (some 30) none),
        bE 3 63924361200 (.wake 420 none), bE 4 63924361800 (bStart ['a']),
        bE 5 63924364800 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 50 := by
  decide

/-- **…and a running clock does not stop for one** (README gap 4363 with D87's arm): the 6th's and the 7th's wakes,
`start a` 07:10, then a thirty-minute `break` at 06:50 on the 7th (filed on the 6th) logged while the block runs,
`stop a` 08:00.  50, the host's reading (driven); D87's arm restarted the clock at the break's end and credited 40. -/
theorem a_break_on_the_ledger_day_before_a_running_block_stops_no_clock :
    ((replay utcZone [bE 1 63924274800 (.wake 420 none), bE 2 63924361200 (.wake 420 none),
        bE 3 63924361800 (bStart ['a']), bE 4 63924360600 (.brk 30 (some 30) none),
        bE 5 63924364800 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes) = some 50 := by
  decide

/-- **D94's bound bites**: a break more than `maxKeepDays` ledger days older than the newest one held is dropped, and
one within it is kept. -/
theorem pruneBrks_drops_a_break_past_the_bound :
    (pruneBrks [⟨(⟨0, 0⟩, ⟨false, 0⟩), (⟨60, 0⟩, ⟨false, 0⟩), 40⟩, ⟨(⟨0, 0⟩, ⟨false, 0⟩), (⟨60, 0⟩, ⟨false, 0⟩), 9⟩,
      ⟨(⟨0, 0⟩, ⟨false, 0⟩), (⟨60, 0⟩, ⟨false, 0⟩), 8⟩]).map (·.day) = [40, 9] := by
  decide

end BreakWitnesses94

/-- **A break's since-break anchor is its END as `brkEnd` reads it** (the W-44 repair, README gap 4550, parity P97): its
`actual_min`, else its planned minutes — the one definition of a break's span the replay's segment (`dayArm`), its clock
(`brkFx`, `settle`) and, since the owner's D95, the host's worked minutes read, so `tm start`'s `since_break_min`
measures from where every other reader ends the break.  Fork 4748911's seam anchored at `t + actual_min.unwrap_or(0)`,
so a `break` line logged without `actual_min` anchored at its START.  `rfl`: the seam's anchor is `brkEnd`, written
inline only because `SeamOp.apply` is defined above it. -/
theorem seam_since_break_is_brkEnd (t : At) (pl : Nat) (am : Option Nat) (a : SeamAcc) :
    (SeamOp.apply ⟨t, .brk pl am⟩ a).sinceBreak = some (brkEnd t pl am) := rfl

/-- **The anchor of a break logged without `actual_min` is its planned end** (not its start, fork 4748911's): a break
stamped at second 1000 planned 20 anchors at 2200; logged with `actual_min` 5, at 1300. -/
theorem a_planned_only_break_anchors_since_break_at_its_planned_end :
    (SeamOp.apply ⟨(⟨1000, 0⟩, ⟨false, 0⟩), .brk 20 none⟩ SeamAcc.empty).sinceBreak = some (⟨2200, 0⟩, ⟨false, 0⟩) ∧
    (SeamOp.apply ⟨(⟨1000, 0⟩, ⟨false, 0⟩), .brk 20 (some 5)⟩ SeamAcc.empty).sinceBreak = some (⟨1300, 0⟩, ⟨false, 0⟩) := by
  decide

/-! ## The owner's D105 (README "Stage 6 — W-46 track K", gaps 1034, 1085 and 4740, parity P100): the break's start is logged

Until D105 a break had ONE line, the `break` appended when it ENDED, stamped at its start; a break still running was
`.tm/state.json`'s alone, so deleting that file mid-break lost it, and once R3's planner draws a running break (P45) the
deletion moved the day and wrote a `plan` event (gap 4740).  `tm break` now logs a `break_start` when the break begins —
`t` its start, its planned minutes and its place (`Log.Event.brkStart`) — and the machine holds it (`Machine.brkOpen`)
until a `break` line ends it, in file order (`brkFx`, whatever that line's stamp).  The facts carry it (`Facts.openBreak`,
the `log` answer's `open.break`), the checkpoint carries it across a cut (`Seal.cMachine`), and its day holds the ledger
day (`Seal.machineDays`), because the `break` line that ends it is stamped at its start.  Everything else a
`break_start` could touch it leaves alone: no segment, no record, no clock, no observation, no completion
(`the_break_start_arm_opens_the_running_break`, `the_break_start_has_no_completion_arm`), so a log with no `break_start`
— every log fork 4748911 wrote — replays exactly as before.  **Fork 4748911 reads the line as an unknown event**
(its `Event::Unknown`, counted in `unknown`): that is P100, separated by `a_break_start_is_not_an_unknown_event`.  Each
witness was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most three entries, `utcZone`, instants
as `Nat` literals; 2026-09-07T09:30:00Z is second 63924370200, and the day is 739865. -/

section BreakWitnesses105

open Log (Id U8 U32 Num)

/-- **A `break_start` opens the running break** (D105) — and, since README gap 5180 (W-49 track L), settles the open block
over it and nets the held closed blocks by it (`runNet`), as the `break` line that ends it will: its machine arm is the
settling's effects, the netting's, then one machine — the old one with `brkOpen` set to its stamp, planned minutes, place
and day, the open block settled and the held closed blocks netted — and its day family writes nothing.  *Restated at W-49
track L*: D105 stated it as "one machine and nothing else", which is refuted
(`the_break_start_arm_as_d105_stated_it_is_refuted`) and holds where nothing is open and nothing held is drawn after the
break's start (`the_break_start_arm_writes_only_the_running_break_with_nothing_open_or_drawn_after_it`). -/
theorem the_break_start_arm_opens_the_running_break (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine)
    (e : Entry) (t : At) (d : Nat) (p : U32) (w : Option (List Char)) (h : e.ev = .brkStart p w)
    (hf : firstStart t d m = none) :
    arm dy sl m e t d =
        (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).2 ++
          (runNet dy (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).1).2 ++
          [.machine (runNet dy (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).1).1] ∧
      (runNet dy (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).1).1.brkOpen = some ⟨t, p.val, w, d⟩ ∧
      dayArm dy sl e t d = [] := by
  refine ⟨?_, ?_, ?_⟩
  · unfold arm; rw [h]; simp only [hf]; rfl
  · rw [(runNet_keeps dy _).2.2.2.1, (settle_keeps dy _).2.2.2.1]
  · unfold dayArm; rw [h]

/-- **D105's statement, on the subdomain it holds on** (README gap 5180): with no block open and no piece a held closed
block drew ending after the break's start, a `break_start` writes one machine — the old one with `brkOpen` set — and
nothing else. -/
theorem the_break_start_arm_writes_only_the_running_break_with_nothing_open_or_drawn_after_it (dy : Cal.Instant → Nat)
    (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) (p : U32) (w : Option (List Char))
    (h : e.ev = .brkStart p w) (hb : m.block = none) (hc : (runTo t m.closed).1 ≤ t.1) (hf : firstStart t d m = none) :
    arm dy sl m e t d = [.machine { m with brkOpen := some ⟨t, p.val, w, d⟩ }] := by
  unfold arm; rw [h]; simp only [hf]; unfold brkStartArm
  have hs : settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ } = ({ m with brkOpen := some ⟨t, p.val, w, d⟩ }, []) := by
    unfold settle; simp [hb]
  have hn : ¬ t.1 < (runTo t m.closed).1 := (Cal.Instant.not_lt _ _).2 hc
  simp only [hs, runNet, if_neg hn, List.nil_append]

/-- **"A `break_start` writes only the running break", as D105 stated it, refuted** (README gap 5180): `a` held closed
with one piece 09:00–10:00 (a `done` a clock behind the log, or another machine, wrote before the break's line arrived),
then a `break_start` at 09:30 — the netting re-draws the piece around the running break and takes its minutes off, so the
arm writes more than the one machine D105's statement wrote. -/
theorem the_break_start_arm_as_d105_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) (p : U32)
      (w : Option (List Char)), e.ev = .brkStart p w →
        arm dy sl m e t d = [.machine { m with brkOpen := some ⟨t, p.val, w, d⟩ }] := by
  intro h
  let M : Machine := ⟨none, none, none, [], none,
    [⟨['a'], 739865, 739865, none, 60, [⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), (⟨63924372000, 0⟩, ⟨false, 0⟩), 739865⟩],
      none, (⟨63924368400, 0⟩, ⟨false, 0⟩), [], 0⟩], none⟩
  have hl : (arm (fun _ => 739865) (fun _ => none) M (bE 1 63924370200 (.brkStart 20 none))
      (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865).length ≠ 1 := by decide
  exact hl (by rw [h _ _ M _ _ _ 20 none rfl]; rfl)

/-- **…and no completion** (D105): a `break_start` marks nothing done, records no instance and no named event. -/
theorem the_break_start_has_no_completion_arm (z : Cal.Tz) (e : Entry) (t : At) (d : Nat) (p : U32)
    (w : Option (List Char)) (h : e.ev = .brkStart p w) (m : Machine) : completionArm z m e t d = [] := by
  unfold completionArm completionCore lateWarnList; rw [h]; rfl

/-- **A `break_start` is the running break** (D105): `break_start` at 09:30, planned twenty minutes, at `walk`, and
nothing after — the facts' running break is its stamp, twenty, `walk`, and its day. -/
theorem a_break_start_is_the_running_break :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 (some ['w','a','l','k']))]).openBreak
      = some ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), 20, some ['w','a','l','k'], 739865⟩ := by
  decide

/-- **A `break` line ends it** (D105, the pairing): `break_start` at 09:30 and the `break` that ends it, stamped at its
start — the line every verb that ends a break writes (`day::end_break_at`).  No break runs. -/
theorem a_break_line_ends_the_running_break :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 none), bE 2 63924370200 (.brk 20 (some 15) none)]).openBreak
      = none := by
  decide

/-- **…in file order, whatever its stamp** (D105): a `break` line stamped an hour before the `break_start` it follows
still ends it.  The pair is matched by order, not by instant: the binary stamps the end at the start, and a line a
binary before D105 wrote, at the cache's minute, ends the break as well. -/
theorem a_break_line_ends_the_running_break_whatever_its_stamp :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 none), bE 2 63924366600 (.brk 20 (some 15) none)]).openBreak
      = none := by
  decide

/-- **An undone `break_start` leaves no break running** (D105, the undo mask): `tm undo` of `tm break` appends
`undo{of: "break_start"}`, which cancels the start. -/
theorem an_undone_break_start_leaves_no_break_running :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 none), bE 2 63924370260 (.undo Log.Kind.brkStart.tag none)]).openBreak
      = none := by
  decide

/-- **An undone `break` line leaves the break running again** (D105): `tm undo` of the verb that ended the break cancels
its `break` line, and the `break_start` before it is the running break once more — as the cache `tm undo` restores
says. -/
theorem an_undone_break_line_leaves_the_break_running :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 none), bE 2 63924370200 (.brk 20 (some 15) none),
        bE 3 63924371200 (.undo Log.Kind.brk.tag none)]).openBreak
      = some ⟨(⟨63924370200, 0⟩, ⟨false, 0⟩), 20, none, 739865⟩ := by
  decide

/-- **A second `break_start` before an end replaces the first** (D105): the later one is the running break.  The binary
never writes it — `tm break` with a break running ends it — so only a hand edit or a verb cut off between its two
writes reaches this. -/
theorem a_second_break_start_replaces_the_first :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 none), bE 2 63924371400 (.brkStart 10 (some ['b','e','d']))]).openBreak
      = some ⟨(⟨63924371400, 0⟩, ⟨false, 0⟩), 10, some ['b','e','d'], 739865⟩ := by
  decide

/-- **A `break_start` is not an unknown event** — parity **P100**, separated: the kernel's replay of the line counts no
unknown event, while the same line read as fork 4748911 reads it (an unknown event tagged `break_start`, its fields in
`rest`) counts one and opens no break. -/
theorem a_break_start_is_not_an_unknown_event :
    (replay utcZone [bE 1 63924370200 (.brkStart 20 none)]).unknown = 0 ∧
    (replay utcZone [bE 1 63924370200 (.unknown Log.Kind.brkStart.tag
        [(['p','l','a','n','n','e','d','_','m','i','n'], .num 20)])]).unknown = 1 ∧
    (replay utcZone [bE 1 63924370200 (.unknown Log.Kind.brkStart.tag
        [(['p','l','a','n','n','e','d','_','m','i','n'], .num 20)])]).openBreak = none := by
  decide

/-- **A running break holds nothing else** (D105): with `start a` at 09:00 and a `break_start` at 09:30 and nothing
after, the open block is read as it would be without the `break_start` — still running since 09:00, nothing banked —
because the block's clock nets a break when the `break` line that ends it arrives (`brkFx`), as before D105. -/
theorem a_running_break_moves_no_clock :
    (replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.brkStart 20 none)]).openBlock
      = (replay utcZone [bE 1 63924368400 (bStart ['a'])]).openBlock := by
  decide

end BreakWitnesses105

/-! ## The owner's D99 (README gap 4520a, parity P104): a mark logged out of its stamp's order is netted where it lies

The host's worked minutes (`Replay::idle_min_since`) read a block as its elapsed time less the union of every idle span
of its ledger days, whatever order the marks were logged in; the replay credited and drew each stretch when its clock
stopped and never moved it again, so a `break`, a `pause` or an `interrupt` a clock behind the log wrote after a stretch
it lies across had closed reached nothing (driven at `49186d7`: README "Stage 6 — W-47 track K", the class table's
M1–M8).  `settle` re-draws the open block over every span it nets at every mark that moves one, and a cut credits the
pieces it is left with (`cutPieces`) — so each witness below credits the host's number, and draws no Block across a
span.  Each was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most seven entries, `utcZone`,
instants as `Nat` literals.  2026-09-07T09:00:00Z is second 63924368400; the day is 739865. -/

section MarkWitnesses99

open Log (Id U8 U32 Num)

/-- **M1: a break logged after a pause closed the stretch it lies across is netted from it**: `start a` 08:00, `pause`
09:00, `unpause` 09:10, then a twenty-minute `break` at 08:30 (logged after), `stop` 10:00 — credited 90, the host's
union (driven: `tm stop` "after 90m"); drawn `[08:00, 08:30]`, `[08:50, 09:00]`, `[09:10, 10:00]`.  D94 credited 110
and drew `[08:00, 09:00]` across the break. -/
theorem a_break_logged_behind_a_closed_stretch_is_netted :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.pause ['a']),
      bE 3 63924369000 (.unpause ['a']), bE 4 63924366600 (.brk 20 (some 20) none), bE 5 63924372000 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 90 ∧
    (f.days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .block ['a'])).map
      (fun g => (g.start.1.sec, g.stop.1.sec)))
      = some [(63924364800, 63924366600), (63924367800, 63924368400), (63924369000, 63924372000)] := by
  decide

/-- **M3: two breaks logged out of order while the block runs are each netted once**: `start a` 09:00, a ten-minute
`break` at 09:10, then a five-minute one at 09:00 (logged after), `stop` 10:00 — 45, the host's union (driven); D94 50. -/
theorem two_breaks_logged_out_of_order_are_each_netted :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924369000 (.brk 10 (some 10) none),
        bE 3 63924368400 (.brk 5 (some 5) none), bE 4 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 45 := by
  decide

/-- **M4: a pause stamped inside a stretch a later break closed is netted from it**: `start a` 09:00, a ten-minute `break`
at 09:30, then `pause` 09:10 and `unpause` 09:20 (logged after), `stop` 10:00 — 40, the host's union (driven); D94
credited 60, the stretch `[09:20, 09:30]` twice. -/
theorem a_pause_logged_behind_a_closed_stretch_is_netted :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924370200 (.brk 10 (some 10) none),
        bE 3 63924369000 (.pause ['a']), bE 4 63924369600 (.unpause ['a']), bE 5 63924372000 (.stop ['a'] 0)]).items.get
        ['a']).map (·.minutes)
      = some 40 := by
  decide

/-- **M5: an interruption logged behind a closed stretch is netted from it**: `start a` 08:00, `pause` 09:00, `unpause`
09:10, then `interrupt` 08:30 and `resume` 08:40 (logged after), `stop` 10:00 — 100, the host's union (driven); D94
restarted the clock at the 08:40 `resume` and credited 140. -/
theorem an_interruption_logged_behind_a_closed_stretch_is_netted :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.pause ['a']),
        bE 3 63924369000 (.unpause ['a']), bE 4 63924366600 (.interrupt none), bE 5 63924367200 (.resume 10 []),
        bE 6 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 100 := by
  decide

/-- **M6: an `unpause` stamped before its pause idles nothing**: `start a` 08:00, `pause` 09:10, `unpause` 09:00 (logged
after), `stop` 10:00 — 120, the host's union (driven); D94 credited 130, more than the block's span. -/
theorem an_unpause_stamped_before_its_pause_idles_nothing :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924369000 (.pause ['a']),
        bE 3 63924368400 (.unpause ['a']), bE 4 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 120 := by
  decide

/-- **M7: a pause stamped before the block's start was another block's** (the host's rule, `idle_spans`): `start a`
09:00, `pause` 08:50 and `unpause` 09:30 (logged after), `stop` 10:00 — 60, the host's union (driven); D94 credited 30
and drew a `Pause` from 08:50. -/
theorem a_pause_stamped_before_the_start_is_not_the_blocks :
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924367800 (.pause ['a']),
        bE 3 63924370200 (.unpause ['a']), bE 4 63924372000 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 60 := by
  decide

/-- **M8: a stop stamped before a pause logged ahead of it credits the stretch to the stop**: `start a` 08:00, `pause`
09:00, then `stop` 08:30 (logged after) — 30, the host's union at the stop (driven); D94 credited the 60 the pause had
banked. -/
theorem a_stop_stamped_before_a_logged_pause_credits_to_the_stop :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.pause ['a']),
        bE 3 63924366600 (.stop ['a'] 0)]).items.get ['a']).map (·.minutes)
      = some 30 := by
  decide

/-- **The open block is re-drawn while it runs** (gap 4525 closed): a fifteen-minute `break` at 10:00 logged ahead of
`start a` 09:50 — the piece before the break is DRAWN at once (`[09:50, 10:00]`) and the clock runs from 10:15, so the
planner's past rows and the open row read the host's union at any later instant.  D94 banked the ten minutes without
drawing them. -/
theorem the_open_blocks_banked_piece_is_drawn :
    let f := replay utcZone [bE 1 63924372000 (.brk 15 (some 15) none), bE 2 63924371400 (bStart ['a'])]
    f.openBlock.map (fun b => (b.workedMin, b.since.map (·.1.sec))) = some (10, some 63924372900) ∧
    (f.days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .block ['a'])).map
      (fun g => (g.start.1.sec, g.stop.1.sec))) = some [(63924371400, 63924372000)] := by
  decide

/-- **A paused stretch is drawn between the block's two pieces** (D99's `redraw` and `closePause`): `start a` 08:00,
`pause` 09:00, `unpause` 09:10, `stop` 10:00 — the day holds the Block `[08:00, 09:00]`, the Pause `[09:00, 09:10]` and
the Block `[09:10, 10:00]`, each once (the unpause's settle re-draws the first piece over itself and writes nothing,
`redraw_of_its_own_pieces_writes_nothing`), in the order of their starts (`DayAcc.finish`). -/
theorem a_paused_stretch_is_drawn_between_the_blocks_pieces :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.pause ['a']),
        bE 3 63924369000 (.unpause ['a']), bE 4 63924372000 (.stop ['a'] 0)]).days.get 739865).map
      (fun a => a.segments.map (fun g => (g.kind, g.start.1.sec)))
      = some [(.block ['a'], 63924364800), (.pause ['a'], 63924368400), (.block ['a'], 63924369000)] := by
  decide

/-- **An open block whose clock a pause or an interruption stopped is not running** (`openStop`, D99): `start a` 08:00
then `pause` 09:00 — sixty minutes worked, no clock, the stretch `[08:00, 09:00]` drawn; `start a` 08:00 then `interrupt`
09:00 — sixty, no clock; and paused at 09:00 then interrupted at 09:30, the earlier stop holds — sixty.  Read at any
later instant the host's union says sixty as well. -/
theorem an_open_block_a_pause_or_an_interruption_stopped_is_not_running :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.pause ['a'])]
    f.openBlock.map (fun b => (b.workedMin, b.since, b.paused)) = some (60, none, true) ∧
    (f.days.get 739865).map (fun a => (a.segments.filter (fun g => g.kind == .block ['a'])).map
      (fun g => (g.start.1.sec, g.stop.1.sec))) = some [(63924364800, 63924368400)] ∧
    (replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.interrupt none)]).openBlock.map
      (fun b => (b.workedMin, b.since)) = some (60, none) ∧
    (replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.pause ['a']),
        bE 3 63924370200 (.interrupt none)]).openBlock.map (fun b => (b.workedMin, b.since)) = some (60, none) := by
  decide

/-- **A re-draw that moves no piece writes nothing** (`samePiece`, D99's `redraw`): over the very spans a block drew, its
re-draw un-draws and draws nothing — the pieces a mark does not move stay where they were filed, so `settle` can run at
every mark without churning its days (a churned piece would be re-filed by the day index at its start, and a day's
segments of one start keep the order they were drawn in, `DayAcc.finish`'s stable sort). -/
theorem redraw_of_its_own_pieces_writes_nothing (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) :
    (redraw dy id old (old.map (fun p => (p.s, p.e)))).2 = [] := by
  have hs : ∀ p : Piece, samePiece p (p.s, p.e) = true := fun p => by
    simp [samePiece, (atEq_iff p.s p.s).2 rfl, (atEq_iff p.e p.e).2 rfl]
  have h1 : old.filter (fun p => !(old.map (fun p => (p.s, p.e))).any (samePiece p)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    have : (old.map (fun p => (p.s, p.e))).any (samePiece p) = true :=
      List.any_eq_true.2 ⟨(p.s, p.e), List.mem_map_of_mem hp, hs p⟩
    simp [this]
  have h2 : (old.map (fun p => (p.s, p.e))).filter (fun q => !old.any (fun p => samePiece p q)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    have : old.any (fun p' => samePiece p' (p.s, p.e)) = true := List.any_eq_true.2 ⟨p, hp, hs p⟩
    simp [this]
  simp only [redraw, h1, h2, List.map_nil, List.append_nil]

/-- `redraw_of_its_own_pieces_writes_nothing`, run (AGENTS §5.2): `a`'s one piece `[08:00, 09:00]` re-drawn as itself. -/
theorem redraw_of_its_own_pieces_writes_nothing_run :
    (redraw (fun _ => 739865) ['a'] [⟨(⟨63924364800, 0⟩, Cal.Offset.utc), (⟨63924368400, 0⟩, Cal.Offset.utc), 739865⟩]
      [((⟨63924364800, 0⟩, Cal.Offset.utc), (⟨63924368400, 0⟩, Cal.Offset.utc))]).2 = [] := by
  decide

/-- `atEq_iff`, run (AGENTS §5.2): one stamp is itself, and a stamp a second later, or the same instant at another
offset, is not. -/
theorem atEq_run :
    atEq (⟨63924364800, 0⟩, Cal.Offset.utc) (⟨63924364800, 0⟩, Cal.Offset.utc) = true ∧
    atEq (⟨63924364800, 0⟩, Cal.Offset.utc) (⟨63924364801, 0⟩, Cal.Offset.utc) = false ∧
    atEq (⟨63924364800, 0⟩, Cal.Offset.utc) (⟨63924364800, 0⟩, ⟨true, 18000⟩) = false := by
  decide

end MarkWitnesses99

/-! ## The owner's D100 (README gap 4520b, parity P105): a break logged after a block closed, stamped inside it, wins

A `break` a clock behind the log writes after a `done` or a `stop` closed the block it lies across reached nothing
until D100: the block's credit, its drawing and its `done`'s duration observation were final when it closed, so the
day read sixty minutes of block and twenty of break in one hour (driven at `49186d7`, the class table's M11, M12 and
M15).  Since D100 the machine holds every block closed within `maxKeepDays` ledger days of the newest held (`Closed`,
`pruneClosed`), and a `break` nets each one it lies across (`netClosed`): its pieces re-drawn around the break, and
what that took off its credit, its item's minutes and its duration observation (`DayOp.net`, `netDur`).  Each witness
was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most five entries, `utcZone`, instants as
`Nat` literals.  2026-09-07T08:00:00Z is second 63924364800; the day is 739865. -/

section ClosedWitnesses100

open Log (Id U8 U32 Num)

/-- **M11: a break logged after a `done`, stamped inside the block, is netted from it**: `start a` 08:00, `done a` 09:00
(sixty minutes), then a twenty-minute `break` at 08:30 logged after — the block is forty minutes: its credit, the day's
block minutes and the duration observation the fit reads; and it is drawn `[08:00, 08:30]` and `[08:50, 09:00]` with the
Break between.  Fork 4748911, and the replay until D100, kept sixty and drew `[08:00, 09:00]` across the Break. -/
theorem a_break_logged_after_a_done_is_netted_from_the_block :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 40 ∧
    (f.days.get 739865).map (·.blockMin) = some 40 ∧
    f.durations.map (·.actualMin) = [40] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a']), (63924366600, 63924367800, .brk none),
              (63924367800, 63924368400, .block ['a'])] := by
  decide

/-- **M12: the same after a `stop`**: `start a` 08:00, `stop` 09:00, then the twenty-minute `break` at 08:30 logged
after — forty minutes credited and on the day, the block drawn around the Break, and no duration observation (a `stop`
pushes none). -/
theorem a_break_logged_after_a_stop_is_netted_from_the_block :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.stop ['a'] 0),
      bE 3 63924366600 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 40 ∧
    (f.days.get 739865).map (·.blockMin) = some 40 ∧
    f.durations = [] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a']), (63924366600, 63924367800, .brk none),
              (63924367800, 63924368400, .block ['a'])] := by
  decide

/-- **M15: a block closed in between is not the last cut and is still netted, and the one it does not cross is not**:
`a` 08:00-09:00 (`done`, sixty), `b` 09:10-09:40 (`done`, thirty), then the twenty-minute `break` at 08:30 logged after —
`a` forty, `b` thirty, the day seventy, each `done`'s duration observation its own block's net minutes. -/
theorem a_late_break_nets_the_block_it_crosses_and_not_the_next :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924369000 (bStart ['b']), bE 4 63924370800 (bDone ['b'] 30 false),
      bE 5 63924366600 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 40 ∧ (f.items.get ['b']).map (·.minutes) = some 30 ∧
    (f.days.get 739865).map (·.blockMin) = some 70 ∧
    f.durations.map (fun o => (o.id, o.actualMin)) = [(['a'], 40), (['b'], 30)] := by
  decide

/-- **The stop-then-done replacement is netted too**: `start a` 08:00, `stop` 09:00, `done a` 09:05 with fifty minutes
(the `done` replaces the stop's credit), then the twenty-minute `break` at 08:30 logged after — thirty, on the item, the
day and the duration observation: the later break wins over the `done`'s fifty as it does over a `done` that closed the
block itself. -/
theorem a_late_break_nets_a_done_that_replaced_a_stop :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.stop ['a'] 0),
      bE 3 63924368700 (bDone ['a'] 50 false), bE 4 63924366600 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧
    (f.days.get 739865).map (·.blockMin) = some 30 ∧
    f.durations.map (·.actualMin) = [30] := by
  decide

/-- **A break that runs past the block's end takes only what it covers**: `start a` 08:00, `done a` 09:00 (sixty), then a
twenty-minute `break` at 08:50 logged after — fifty, and the block drawn `[08:00, 08:50]` with the Break from 08:50. -/
theorem a_late_break_past_the_blocks_end_takes_what_it_covers :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924367800 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924367800, .block ['a']), (63924367800, 63924369000, .brk none)] := by
  decide

/-- **A late break takes no more than the block's own credit** (`netMin`'s bound): `a` worked twice — 08:00-09:00 with a
`done` of ten minutes, 10:00-11:00 with a `done` of sixty — then a forty-minute `break` at 08:10 logged after.  It
covers forty of the first block's drawn minutes and takes its ten, not forty: the item keeps sixty, the second block's,
and the first `done`'s duration observation reads zero. -/
theorem a_late_break_takes_no_more_than_the_blocks_credit :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 10 false),
      bE 3 63924372000 (bStart ['a']), bE 4 63924375600 (bDone ['a'] 60 false),
      bE 5 63924365400 (.brk 40 (some 40) none)]
    (f.items.get ['a']).map (·.minutes) = some 60 ∧
    (f.days.get 739865).map (·.blockMin) = some 60 ∧
    f.durations.map (·.actualMin) = [0, 60] := by
  decide

/-- **The bound, from both sides** (`pruneClosed`, D100's — `Seal.maxKeepDays`, as D94's for the breaks): a block closed
thirty-one ledger days before the newest one held is netted by a late break across it (forty), and one closed
thirty-two days before is not — it was dropped from the machine when the newer block closed, and its sixty minutes and
its drawing across the Break stand (README gap 4917). -/
theorem a_late_break_nets_a_block_held_and_not_one_pruned :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
        bE 3 63927043200 (bStart ['b']), bE 4 63927046800 (bDone ['b'] 60 false),
        bE 5 63924366600 (.brk 20 (some 20) none)]).items.get ['a']).map (·.minutes) = some 40 ∧
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
        bE 3 63927129600 (bStart ['b']), bE 4 63927133200 (bDone ['b'] 60 false),
        bE 5 63924366600 (.brk 20 (some 20) none)]).items.get ['a']).map (·.minutes) = some 60 := by
  decide

/-- **A break filed on a ledger day before the block's nets nothing from it** (D94's rule for an open block, which
D100 keeps for a closed one): `a` 00:05-01:00 on the 7th (`done`, fifty-five), then a thirty-minute `break` at 23:50 on
the 6th logged after — fifty-five, and the 7th's record draws `a` whole (README gap 4917). -/
theorem a_late_break_filed_the_day_before_nets_nothing :
    let f := replay utcZone [bE 1 63924336300 (bStart ['a']), bE 2 63924339600 (bDone ['a'] 55 false),
      bE 3 63924335400 (.brk 30 (some 30) none)]
    (f.items.get ['a']).map (·.minutes) = some 55 ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924336300, 63924339600, .block ['a'])] := by
  decide

/-- **Two late breaks net their union, once** (`netClosed` cuts pieces already cut): `a` 08:00-09:00 (`done`, sixty), then
twenty-minute `break`s at 08:30 and 08:40 logged after — together they cover 08:30-09:00, and `a` is thirty: the second
takes only the ten minutes the first left, as the host's union of idle spans reads them. -/
theorem two_late_breaks_net_their_union_once :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (.brk 20 (some 20) none), bE 4 63924367200 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ f.durations.map (·.actualMin) = [30] := by
  decide

/-- **A break netted while the block ran is not netted again after its `done`**: `start a` 08:00, the twenty-minute
`break` at 08:30 logged while it runs (D87: the clock nets it), `done a` 09:00 with the host's forty, then the same
`break` logged again after — still forty, the block's pieces already cut around it. -/
theorem a_break_netted_while_open_is_not_netted_again_after_the_done :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brk 20 (some 20) none),
        bE 3 63924368400 (bDone ['a'] 40 false), bE 4 63924366600 (.brk 20 (some 20) none)]).items.get ['a']).map
        (·.minutes) = some 40 := by
  decide

/-- **A `done` logged after a `stop` and a late break credits its own minutes, once**: `start a` 08:00, `stop` 09:00, the
twenty-minute `break` at 08:30 logged after, then `done a` 09:05 with the host's forty (its reading then holds the
break) — forty: the break netted the stop's credit, and the `done` replaced that credit with its own. -/
theorem a_done_after_a_stop_and_a_late_break_credits_its_own_minutes :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.stop ['a'] 0),
      bE 3 63924366600 (.brk 20 (some 20) none), bE 4 63924368700 (bDone ['a'] 40 false)]
    (f.items.get ['a']).map (·.minutes) = some 40 ∧ f.durations.map (·.actualMin) = [40] := by
  decide

end ClosedWitnesses100

/-! ## D100's re-draw draws no Block across the break it nets

The laws D99 proved of a settle and a cut (`settle_avoids_every_span_it_nets`, `cut_avoids_every_span_it_nets`), for the
re-draw a late break makes of a block already closed: every `Block` segment it writes, and every piece the machine keeps
for a block it nets, lies outside the break.  Appended at the module's end so no line the mutation roster pins moves
(README "Stage 6 — W-47 track K" §11.6). -/

/-- **Every piece a re-draw keeps or draws is a span it was given** (D99): its start and end are a span of `P`. -/
theorem redraw_fst_spans (dy : Cal.Instant → Nat) (id : Id) (old : List Piece) (P : List (At × At)) (p : Piece)
    (hp : p ∈ (redraw dy id old P).1) : (p.s, p.e) ∈ P := by
  unfold redraw at hp
  obtain ⟨q, hq, hpq⟩ := List.mem_map.1 hp
  split at hpq
  · rename_i p' hf
    have h1 := List.find?_some hf
    subst hpq
    unfold samePiece at h1
    simp only [Bool.and_eq_true] at h1
    rw [(atEq_iff _ _).1 h1.1, (atEq_iff _ _).1 h1.2]
    exact hq
  · subst hpq
    exact hq

/-- **A span cut out of pieces leaves none across it** (D100): every span of `cutOut s e P` ends at or before `s` or
starts at or after `e`, when `[s, e)` is nonempty. -/
theorem cutOut_avoids (s e : At) (P : List (At × At)) (hne : s.1 < e.1) :
    ∀ q ∈ cutOut s e P, q.2.1 ≤ s.1 ∨ e.1 ≤ q.1.1 := by
  intro q hq
  unfold cutOut at hq
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hq
  unfold pieces at hr
  exact piecesGo_avoids [(s, e)] _ _ _ q hr (s, e) (List.mem_singleton.2 rfl) hne

/-- **No Block a late break re-draws lies across it** (the owner's D100, README gap 4520b): every `Block` segment
`netOne` emits for a held closed block — the pieces it draws anew — lies outside the nonempty break `[s, e)` it nets,
so what a late break re-draws and what it takes off the credit read the block one way (D99's
`cut_avoids_every_span_it_nets`, for a block already closed). -/
theorem netOne_avoids_the_break (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Closed) (hne : s.1 < e.1) :
    ∀ x ∈ (netOne dy s e d C).2.1, ∀ dd g, x = .dayAdd dd (.segment g) → g.stop.1 ≤ s.1 ∨ e.1 ≤ g.start.1 := by
  intro x hx dd g hxg
  unfold netOne at hx
  split at hx
  · simp at hx
  · simp only [List.mem_append] at hx
    rcases hx with hx | hx
    · obtain ⟨hq, -⟩ := redraw_draws_its_spans dy C.id C.drawn _ x hx dd g hxg
      exact cutOut_avoids s e _ hne _ hq
    · split at hx
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> simp at hxg
      · simp at hx

/-- **And the block it leaves holds no piece across it**: a held block of a ledger day at or before the break's, once
netted, draws nothing across the nonempty break — the pieces the machine keeps for it are the re-draw's. -/
theorem netOne_leaves_no_piece_across_the_break (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (C : Closed)
    (hne : s.1 < e.1) (hd : C.day ≤ d) :
    ∀ p ∈ (netOne dy s e d C).1.drawn, p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1 := by
  intro p hp
  unfold netOne at hp
  split at hp
  · rename_i hc
    have hall := hc.resolve_left (Nat.not_lt.2 hd)
    exact of_decide_eq_true (List.all_eq_true.1 hall p hp)
  · exact cutOut_avoids s e _ hne _ (redraw_fst_spans dy C.id C.drawn _ p hp)

/-- **Every Block segment a late break writes lies outside it** (D100): `netClosed`'s effects over every held block. -/
theorem netClosed_avoids_the_break (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (m : Machine) (hne : s.1 < e.1) :
    ∀ x ∈ (netClosed dy s e d m).2, ∀ dd g, x = .dayAdd dd (.segment g) → g.stop.1 ≤ s.1 ∨ e.1 ≤ g.start.1 := by
  intro x hx dd g hxg
  unfold netClosed at hx
  simp only [List.mem_flatten, List.mem_map] at hx
  obtain ⟨l, ⟨C, -, rfl⟩, hx⟩ := hx
  exact netOne_avoids_the_break dy s e d C hne x hx dd g hxg

/-- **And every held block it reaches keeps no piece across it** (D100): after a late break, no block the machine
holds from a ledger day at or before the break's has a piece across it. -/
theorem netClosed_leaves_no_piece_across_the_break (dy : Cal.Instant → Nat) (s e : At) (d : Nat) (m : Machine)
    (hne : s.1 < e.1) :
    ∀ C' ∈ (netClosed dy s e d m).1.closed, C'.day ≤ d → ∀ p ∈ C'.drawn, p.e.1 ≤ s.1 ∨ e.1 ≤ p.s.1 := by
  intro C' hC' hd p hp
  unfold netClosed at hC'
  simp only [List.mem_map] at hC'
  obtain ⟨C, -, rfl⟩ := hC'
  have hday : (netOne dy s e d C).1.day = C.day := by
    unfold netOne; split <;> rfl
  rw [hday] at hd
  exact netOne_leaves_no_piece_across_the_break dy s e d C hne hd p hp


/-! ## Two definitions D40 found told from a constant by nothing but a proof (README "Stage 6 — W-47 track K" §11.6)

`Effect.safe` (`fun _ => true`) and the held credit (`0`) each came back ALONE: one theorem's proof failed, and with it
`sorry`ed the package built.  Each now has a statement the constant falsifies.  (The held credit was a definition then;
check 12 then found it, and the witness machine cutMachineWit that came back ALONE beside them, emitted and reached by
nothing, and both are written in place now — the sum in `Conserves` and its lemmas, the machine in the refutation's
proof.)  Appended at the module's end, as the section before, so no pinned line moves. -/

section D40Witnesses100

open Log (Id U8 U32 Num)

/-- **What `Effect.safe` excludes** (the owner's D100; D40 found `fun _ => true` told from it by nothing but a proof):
the machine, a credit taken back (`uncredit`) and a late break's `net` — the three effects that can replace the machine
or lower a day's ci-unknown minutes — and nothing else among a day's credit, a segment, an item's minutes. -/
theorem the_unsafe_effects_are_the_machine_an_uncredit_and_a_net :
    (Effect.machine ⟨none, none, none, [], none, [], none⟩).safe = false ∧
    (Effect.dayAdd 739865 (.uncredit ['a'] 60)).safe = false ∧
    (Effect.dayAdd 739865 (.net ['a'] none 20 none)).safe = false ∧
    (Effect.dayAdd 739865 (.credit ['a'] 60 none)).safe = true ∧ (Effect.itemDay ['a'] 739865 60).safe = true := by
  decide

/-- **The held credit counts what a held block still stands for** (the owner's D100; D40 found `0` told from it by
nothing but a proof): `a`'s cut on the 7th, sixty minutes at no ci, stands for sixty on the 7th, and for nothing for `b`
or on another day; a `done`'s (its ci set) stands for nothing — its minutes are on a ci, not the unknown ones. -/
theorem the_held_credit_counts_a_cut_and_not_a_done :
    let l : List Closed := [⟨['a'], 739865, 739865, none, 60, [], none, (⟨63924364800, 0⟩, ⟨false, 0⟩), [], 0⟩, ⟨['a'], 739865, 739865, some ⟨3, by decide⟩, 40, [], none, (⟨63924364800, 0⟩, ⟨false, 0⟩), [], 0⟩]
    ((l.filter (fun C => decide (C.ci = none ∧ C.credDay = 739865 ∧ C.id = ['a']))).map (·.min)).sum = 60 ∧
    ((l.filter (fun C => decide (C.ci = none ∧ C.credDay = 739865 ∧ C.id = ['b']))).map (·.min)).sum = 0 ∧
    ((l.filter (fun C => decide (C.ci = none ∧ C.credDay = 739866 ∧ C.id = ['a']))).map (·.min)).sum = 0 := by
  decide

end D40Witnesses100

section D40WitnessesGap5027

/-! The compiled twins' own witnesses (README gap 5027, W-48 track A): `mutate.py` found each of `piecesFast`,
`redrawWalk`, `redrawFast` told from a constant by its `@[csimp]` proof ALONE, so each is run here, on a branch a
`decide` can read. -/

/-- **`piecesFast` answers through the pass** on spans already apart. -/
theorem piecesFast_answers_through_the_pass :
    piecesFast [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)] ((((⟨63924364800 + 100, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 100, 0⟩, ⟨false, 0⟩)) : At × At)).1 ((((⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)).1 =
      [(((((⟨63924364800 + 300, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 600, 0⟩, ⟨false, 0⟩)) : At × At)).1), (((((⟨63924364800 + 900, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)).1)] := by
  decide

/-- **The merge keeps an unmoved piece, un-draws a moved one and draws the new one**: old `[0, 300)` (day 7) and
`[600, 900)` (day 7), new `[0, 300)` and `[600, 1000)` — the first kept with its day, the second's old piece left over,
the new span drawn on day 8. -/
theorem the_merge_keeps_unmoved_pieces_and_redraws_moved_ones :
    (redrawWalk (fun _ => 8) [⟨((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩, ⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩]
        [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)]) =
      ([⟨((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩, ⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)).2, 8⟩],
       [⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩], [(((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)]) := by
  decide

/-- **`redrawFast` answers through the merge, and else through `redraw`**: the merge's case above writes one
un-draw and one draw; old pieces out of order fall back, and draw every new span. -/
theorem redrawFast_answers_through_the_merge_and_else_through_redraw :
    ((redrawFast (fun _ => 8) ['a'] [⟨((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩, ⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩]
        [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At), (((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 1000, 0⟩, ⟨false, 0⟩)) : At × At)]).2.length = 2) ∧
    ((redrawFast (fun _ => 8) ['a'] [⟨((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 600, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 900, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩, ⟨((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).1, ((((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)).2, 7⟩]
        [(((⟨63924364800 + 0, 0⟩, ⟨false, 0⟩), (⟨63924364800 + 300, 0⟩, ⟨false, 0⟩)) : At × At)]).1.map (·.day) = [7]) := by
  decide

end D40WitnessesGap5027

/-! ### Stage 6 W-48 track K: the late-mark decisions D115, D116 and D119 (README "Stage 6 — W-48 track K")

Each witness was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most five entries, `utcZone`,
instants as `Nat` literals; 2026-09-07T08:00:00Z is second 63924364800, and the day is 739865. -/

/-- **D115: a late `start` stamped inside a block a later `done` closed cuts it** (README gap 5034): `start a` 08:00,
`done a` 09:00 (sixty), then `start b` stamped 08:30 and `stop` 09:30 — `a` is thirty (its piece after 08:30 un-drawn,
its credit, its item and its `done`'s duration observation taken down by thirty), `b` sixty, the day ninety: the later
fact wins, and the two blocks share no span.  Until W-48 `a` kept sixty and the day counted 120 minutes inside ninety. -/
theorem a_late_start_cuts_the_block_it_is_stamped_inside :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (bStart ['b']), bE 4 63924370200 (.stop ['b'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.items.get ['b']).map (·.minutes) = some 60 ∧
    (f.days.get 739865).map (·.blockMin) = some 90 ∧ f.durations.map (·.actualMin) = [30] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a']), (63924366600, 63924370200, .block ['b'])] := by
  decide

/-- **D115's boundary: a `start` cuts nothing of a block it is not stamped inside** — after it (a forward clock, the
`start` at 09:30 after `a` closed at 09:00) or before it (`start b` stamped 08:00, before `a`'s 09:00 start): `a` keeps
its sixty either way. -/
theorem a_start_cuts_no_block_it_is_not_stamped_inside :
    ((replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
        bE 3 63924370200 (bStart ['b']), bE 4 63924372000 (.stop ['b'] 0)]).items.get ['a']).map (·.minutes)
      = some 60 ∧
    ((replay utcZone [bE 1 63924368400 (bStart ['a']), bE 2 63924372000 (bDone ['a'] 60 false),
        bE 3 63924364800 (bStart ['b']), bE 4 63924366600 (.stop ['b'] 0)]).items.get ['a']).map (·.minutes)
      = some 60 := by
  decide

/-- **D119: a late interruption logged after a `done`, stamped inside the block, is netted from it** (README gaps 4913
and 5029): `start a` 08:00, `done a` 09:00 (sixty), then `interrupt` stamped 08:30 and `resume` 08:40 — `a` fifty, the
day fifty, the `done`'s duration observation fifty, as D100 nets a late break.  Until W-48 `a` kept sixty beside the
interruption's ten. -/
theorem a_late_interruption_nets_the_block_it_crosses :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (.interrupt none), bE 4 63924367200 (.resume 10 [])]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧ (f.days.get 739865).map (·.blockMin) = some 50 ∧
    f.durations.map (·.actualMin) = [50] := by
  decide

/-- **D119: a late mark past the bound is named** (README gap 4917): `a` closed on day 739865, `b` forty days later, then
a `break` stamped across `a` and logged after — `a` was dropped from the machine (`pruneClosed`) and keeps its sixty, and
the replay names line 5, its day and the newest held, `RWarn.pastBound`. -/
theorem a_late_mark_past_the_bound_is_named :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63927820800 (bStart ['b']), bE 4 63927824400 (bDone ['b'] 60 false),
      bE 5 63924366600 (.brk 20 (some 20) none)]
    (f.items.get ['a']).map (·.minutes) = some 60 ∧ f.warnings = [.pastBound 5 739865 739905] := by
  decide

/-- **D116: a break is read at its `break_start`'s place, and a different word on the line that ends it is named**
(README gap 5035): `break_start` at `walk`, then the `break` line that ends it hand-edited to `moon` — the day's break
record and its segment read `walk`, and the replay names line 2 with both words, `RWarn.breakPlace`.  With no
`break_start` (a log fork 4748911 wrote) the `break` line's own word is the place, and nothing is named. -/
theorem a_break_is_read_at_its_starts_place :
    let f := replay utcZone [bE 1 63924364800 (.brkStart 10 (some ['w','a','l','k'])),
      bE 2 63924364800 (.brk 10 (some 10) (some ['m','o','o','n']))]
    (f.days.get 739865).map (fun a => a.breaks.map (·.where_)) = some [some ['w','a','l','k']] ∧
    f.warnings = [.breakPlace 2 (some ['w','a','l','k']) (some ['m','o','o','n'])] ∧
    let g := replay utcZone [bE 1 63924364800 (.brk 10 (some 10) (some ['m','o','o','n']))]
    (g.days.get 739865).map (fun a => a.breaks.map (·.where_)) = some [some ['m','o','o','n']] ∧ g.warnings = [] := by
  decide

/-- **C5's split as the owner's D87 stated it, refuted by the owner's D116** (README gap 5035): a running break opened
at `walk` and the `break` line that ends it written `moon` — the entry's day family half is read at `walk` (`placed`), so
no prefix of block family effects makes the arm `dayArm` of the line as written. -/
theorem arm_split_as_d87_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat),
      ∃ fx : List Effect, (∀ x ∈ fx, x.blockOnly = true) ∧ arm dy sl m e t d = fx ++ dayArm dy sl e t d := by
  intro h
  let M : Machine := ⟨none, none, none, [], some ⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), 10, some ['w','a','l','k'], 739865⟩, [], none⟩
  let E : Entry := bE 2 63924369000 (.brk 10 (some 10) (some ['m','o','o','n']))
  let T : At := (⟨63924368400, 0⟩, ⟨false, 0⟩)
  obtain ⟨fx, -, hfx⟩ := h (fun _ => 739865) (fun _ => none) M E T 739865
  have hfx' : arm (fun _ => 739865) (fun _ => none) M E T 739865 =
      brkFx (fun _ => 739865) M T (brkEnd T 10 (some 10)) 739865 ++
        dayArm (fun _ => 739865) (fun _ => none) (placed M E) T 739865 := rfl
  have hl : (dayArm (fun _ => 739865) (fun _ => none) (placed M E) T 739865).length =
      (dayArm (fun _ => 739865) (fun _ => none) E T 739865).length := by decide
  have hne : dayArm (fun _ => 739865) (fun _ => none) (placed M E) T 739865 ≠
      dayArm (fun _ => 739865) (fun _ => none) E T 739865 := by decide
  exact hne (List.append_inj' (hfx'.symm.trans hfx) hl).2


/-! ## README gap 5180 (W-49 track L): a block closed or stopped while a logged break runs reads what it will read once
the break's line arrives

A `break_start` with no `break` line yet is a break running from its stamp (`Machine.brkOpen`, D105).  A block closed
under it (a `done`, a `stop`, the `start` of another block) is netted by it at the close (`runNet`, D100's netting), a
held block a `break_start` stamped before its end is logged after is netted at the `break_start`, and a block paused or
interrupted under it draws nothing from its start (`openPieces`' `runSpan`) — so the block and the break are read one way
on every log (the owner's D94 and D100), and the break's own line, when it arrives, moves nothing it netted.  Each witness
was probed in a scratch copy under `MemoryMax=8G timeout 120` (§5.10a): at most five entries, `utcZone`, instants as `Nat`
literals; 2026-09-07T08:00:00Z is second 63924364800 and the day is 739865. -/

section RunWitnesses5180

open Log (Id U8 U32 Num)

/-- **A `done` under a running break is netted by it**: `start a` 08:00, a `break_start` at 08:30, `done a` 09:00 with
sixty minutes — thirty, on the item, the day and the duration observation, and the block drawn `[08:00, 08:30]`.  Until
W-49 it was sixty and drawn to 09:00, across the running break. -/
theorem a_done_under_a_running_break_is_netted_by_it :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brkStart 20 none),
      bE 3 63924368400 (bDone ['a'] 60 false)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.days.get 739865).map (·.blockMin) = some 30 ∧
    f.durations.map (·.actualMin) = [30] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a'])] := by
  decide

/-- **…and the break's line, when it arrives, moves nothing it netted**: the same log with the `break` that ends it — forty
five minutes, to 09:15 — logged after the `done`: still thirty, the block still `[08:00, 08:30]`, and the Break drawn
beside it.  The block read at the `done` is the block read once the break ended. -/
theorem the_running_breaks_line_moves_nothing_it_netted :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brkStart 20 none),
      bE 3 63924368400 (bDone ['a'] 60 false), bE 4 63924366600 (.brk 20 (some 45) none)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.days.get 739865).map (·.blockMin) = some 30 ∧
    f.durations.map (·.actualMin) = [30] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a']), (63924366600, 63924369300, .brk none)] := by
  decide

/-- **A `stop` under a running break is netted by it**: `start a` 08:00, a `break_start` at 08:30, `stop` 09:00 — the cut
credits thirty. -/
theorem a_stop_under_a_running_break_is_netted_by_it :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brkStart 20 none),
      bE 3 63924368400 (.stop ['a'] 0)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.days.get 739865).map (·.blockMin) = some 30 := by
  decide

/-- **The `start` of another block under a running break cuts the first at the break**: `start a` 08:00, a `break_start`
at 08:30, `start b` 09:00 — `a` thirty, and `b` open from 09:00 with nothing worked yet. -/
theorem a_start_under_a_running_break_cuts_the_open_block_at_the_break :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brkStart 20 none),
      bE 3 63924368400 (bStart ['b'])]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ f.openBlock.map (fun b => (b.id, b.workedMin)) = some (['b'], 0) := by
  decide

/-- **A block paused under a running break draws nothing from the break's start**: `start a` 08:00, a `break_start` at
08:30, `pause` 09:00 — the open block has worked thirty, and is drawn `[08:00, 08:30]`. -/
theorem a_pause_under_a_running_break_draws_up_to_its_start :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brkStart 20 none),
      bE 3 63924368400 (.pause ['a'])]
    f.openBlock.map (·.workedMin) = some 30 ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a'])] := by
  decide

/-- **A `break_start` logged after a `done` and stamped inside its block nets it** — the order a sync can append the two
machines' lines in: `start a` 08:00, `done a` 09:00 with sixty, then a `break_start` at 08:30 — thirty, as if the break's
start had been logged first. -/
theorem a_break_start_logged_after_a_done_nets_it :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (.brkStart 20 none)]
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.days.get 739865).map (·.blockMin) = some 30 ∧
    f.durations.map (·.actualMin) = [30] := by
  decide

/-- **A running break begun after a block closed nets nothing of it** (the rule bites only where the break lies inside the
block, AGENTS §5.8): `start a` 08:00, `done a` 09:00 with sixty, a `break_start` at 09:30 — sixty. -/
theorem a_running_break_after_a_done_nets_nothing :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924370200 (.brkStart 20 none)]
    (f.items.get ['a']).map (·.minutes) = some 60 ∧ (f.days.get 739865).map (·.blockMin) = some 60 := by
  decide

end RunWitnesses5180

/-- **"Every `plan` records its stamp", as the W-48 repair stated it, refuted** (W-49 track L, README gap 5300; appended at
the module's end so no line the mutation roster pins moves): the day's last-plan slot holds 00:30 on the 8th, and a
`plan` a clock behind the log stamped 23:50 on the 7th leaves it — the later date's last plan stays the slot's. -/
theorem a_plan_records_its_stamp_as_the_w48_repair_stated_it_is_refuted :
    ¬ ∀ (h : List Char) (r d : Nat) (ys : List (Log.Id × Log.U8)) (t : At) (n : Nat) (a : DayAcc),
      ((DayOp.plan h r d ys t n).apply a).planAt = some t := by
  intro hall
  have := hall ['h'] 0 0 [] (⟨63924421800, 0⟩, ⟨false, 0⟩) 2
    ((DayOp.plan ['h'] 0 0 [] (⟨63924424200, 0⟩, ⟨false, 0⟩) 1).apply DayAcc.empty)
  revert this; decide

/-! ## D129: a `start` ends a running break, in stamp order (stage 6, W-50 track K; README gaps 5430-5433, parity P127)

The owner's **D129**: a `start` logged while a break runs ends that break at the start's instant (`endsBrk`), and the
reading is in STAMP order — a `break_start` logged after a block and stamped before its start ends at the first start the
machine holds at or after it (`firstStart`: the open block's start, a held closed block's first drawn piece).  Either way the ending writes what the `break` line `tm
start` logs on one machine writes (`endBrkFx`, D97), and that break's own `break` line, when it comes, is not a second
break (`Machine.brkEnded`).  Each witness: `utcZone`, at most four entries, instants as `Nat` literals (08:00 on
2026-09-07 is second 63924364800, the day 739865; 23:00 the day before is 63924332400, day 739864), probed in a scratch
build under `MemoryMax=8G timeout 120` (§5.10a). -/

section D129Witnesses

open Log (Id U8 U32 Num)

/-- **A `start` ends a running break at its instant** (D129) — two machines on one synced directory: machine A's
`break_start` 08:00, never ended, then machine B's `start a` 08:30 and `done a` 09:30 (sixty).  No break runs; the day
draws the break 08:00–08:30 and `a`'s block 08:30–09:30, records the break's thirty minutes, and credits `a` sixty.  Until
D129 the break ran on: it netted all sixty minutes of `a` (gap 5180's netting) and the plan drew it across the block. -/
theorem a_start_ends_the_running_break :
    let f := replay utcZone [bE 1 63924364800 (.brkStart 20 none), bE 2 63924366600 (bStart ['a']),
      bE 3 63924370200 (bDone ['a'] 60 false)]
    f.openBreak = none ∧ (f.items.get ['a']).map (·.minutes) = some 60 ∧
    (f.days.get 739865).map (fun a => a.breaks.map (·.actualMin)) = some [some 30] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .brk none), (63924366600, 63924370200, .block ['a'])] := by
  decide

/-- **…in stamp order: a `break_start` logged after a block ends at its start** (D129, README "Stage 6 — W-49 repair"
§2's route 2, one machine): `start a` 08:30, `done a` 09:30, then `tm --now 08:00 break` — the break is 08:00–08:30, no
break runs, and `a` keeps its sixty.  Until D129 the late break ran from 08:00 to the end of the log and netted the whole
block: `tm review day` counted load 0.0 for a block `tm done` had reported 60m/60m. -/
theorem a_late_break_start_ends_at_the_first_start_after_it :
    let f := replay utcZone [bE 1 63924366600 (bStart ['a']), bE 2 63924370200 (bDone ['a'] 60 false),
      bE 3 63924364800 (.brkStart 20 none)]
    f.openBreak = none ∧ (f.items.get ['a']).map (·.minutes) = some 60 ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .brk none), (63924366600, 63924370200, .block ['a'])] := by
  decide


/-- **…on an earlier ledger day too** (D129, route 1, gap 5341's picture): `start a` 08:30 and `done a` 09:30 on the 7th,
then a `break_start` stamped 23:00 on the 6th — the break is filed on the 6th and ends at 08:30 on the 7th, no break
runs, and `a` keeps its sixty.  Until D129 the plan drew it from the day's start across `a`'s block (P45). -/
theorem a_break_from_the_day_before_ends_at_the_next_start :
    let f := replay utcZone [bE 1 63924366600 (bStart ['a']), bE 2 63924370200 (bDone ['a'] 60 false),
      bE 3 63924332400 (.brkStart 15 none)]
    f.openBreak = none ∧ (f.items.get ['a']).map (·.minutes) = some 60 ∧
    (f.days.get 739864).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924332400, 63924366600, .brk none)] := by
  decide

/-- **The break's own `break` line is not a second break** (D129, `Machine.brkEnded`): machine A's `break_start` 08:00,
machine B's `start a` 08:30 and `done a` 09:30, then A's own `break` line, stamped at its start and claiming ninety
minutes — one break, 08:00–08:30, one record, and `a` keeps its sixty: the start ended the break first in stamp order. -/
theorem a_breaks_own_line_after_a_start_ended_it_is_not_a_second_break :
    let f := replay utcZone [bE 1 63924364800 (.brkStart 20 none), bE 2 63924366600 (bStart ['a']),
      bE 3 63924370200 (bDone ['a'] 60 false), bE 4 63924364800 (.brk 20 (some 90) none)]
    f.openBreak = none ∧ (f.items.get ['a']).map (·.minutes) = some 60 ∧
    (f.days.get 739865).map (fun a => a.breaks.length) = some 1 ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .brk none), (63924366600, 63924370200, .block ['a'])] := by
  decide

/-- **A `start` stamped at the break's own instant ends it there** (D129's edge, the reading W-50 track K took — README
gap 5431): `break_start` 08:30, `start a` 08:30 — a break of no length, as `tm start` at the same minute writes one with
`actual_min` 0 (D97), and `a` keeps its sixty.  The other reading (a start strictly after) would leave the break running
and net all of `a`. -/
theorem a_start_at_the_breaks_instant_ends_it_there :
    let f := replay utcZone [bE 1 63924366600 (.brkStart 20 none), bE 2 63924366600 (bStart ['a']),
      bE 3 63924370200 (bDone ['a'] 60 false)]
    f.openBreak = none ∧ (f.items.get ['a']).map (·.minutes) = some 60 ∧
    (f.days.get 739865).map (fun a => a.breaks.map (·.actualMin)) = some [some 0] := by
  decide

/-- **A `start` stamped before the break ends nothing** (D129's boundary): `break_start` 09:00, then a `start a` stamped
08:30 logged after it — before the break in stamp order, so the break still runs. -/
theorem a_start_stamped_before_the_break_ends_nothing :
    (replay utcZone [bE 1 63924368400 (.brkStart 20 none), bE 2 63924366600 (bStart ['a'])]).openBreak
      = some ⟨(⟨63924368400, 0⟩, ⟨false, 0⟩), 20, none, 739865⟩ := by
  decide

/-- **D100 unchanged: a late break stamped inside a closed block, with no start after it, still runs and nets the block**
(D129's boundary): `start a` 08:00, `done a` 09:00 (sixty), then a `break_start` stamped 08:30 — no start at or after
08:30 is held, so the break runs and `a` keeps thirty, as gap 5180 nets it. -/
theorem a_late_break_inside_a_block_with_no_start_after_it_still_runs :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (.brkStart 20 none)]
    f.openBreak.isSome = true ∧ (f.items.get ['a']).map (·.minutes) = some 30 := by
  decide

/-- **"A `break_start` opens the running break", as W-49 track L stated it, refuted by D129** (README gap 5430): `a` held
closed with one piece 10:00–11:00 (it started at 10:00), then a `break_start` at 09:30 — the start at 10:00 ends the
break, so the arm writes the ending (`endBrkFx`, three effects), not the settling, the netting and one machine (five).
`the_break_start_arm_opens_the_running_break` holds where the machine holds no start at or after the stamp. -/
theorem the_break_start_arm_as_w49_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) (p : U32)
      (w : Option (List Char)), e.ev = .brkStart p w →
        arm dy sl m e t d =
            (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).2 ++
              (runNet dy (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).1).2 ++
              [.machine (runNet dy (settle dy { m with brkOpen := some ⟨t, p.val, w, d⟩ }).1).1] := by
  intro h
  let M : Machine := ⟨none, none, none, [], none,
    [⟨['a'], 739865, 739865, none, 60, [⟨(⟨63924372000, 0⟩, ⟨false, 0⟩), (⟨63924375600, 0⟩, ⟨false, 0⟩), 739865⟩],
      none, (⟨63924372000, 0⟩, ⟨false, 0⟩), [], 0⟩], none⟩
  have := congrArg List.length (h (fun _ => 739865) (fun _ => none) M (bE 1 63924370200 (.brkStart 20 none))
    (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865 20 none rfl)
  revert this
  decide

/-- **"With nothing open or drawn after it, a `break_start` writes only the running break", as W-49 track L stated it,
refuted by D129** (README gap 5430): the statement quantifies over every machine, and on one holding `a` closed with an
inverted piece — begun 10:00, ended 09:00, so it ends before the break's 09:30 and `runTo` passes nothing — the piece's
start at 10:00 ends the break (`firstStart`): three effects, not one machine.  No replay draws an inverted piece; the
restated theorem names the hypothesis the arm's new branch needs (`firstStart t d m = none`). -/
theorem the_break_start_arm_with_nothing_open_or_drawn_after_it_as_w49_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat) (p : U32)
      (w : Option (List Char)), e.ev = .brkStart p w → m.block = none → (runTo t m.closed).1 ≤ t.1 →
        arm dy sl m e t d = [.machine { m with brkOpen := some ⟨t, p.val, w, d⟩ }] := by
  intro h
  let M : Machine := ⟨none, none, none, [], none,
    [⟨['a'], 739865, 739865, none, 0,
      [⟨(⟨63924372000, 0⟩, ⟨false, 0⟩), (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865⟩], none, (⟨63924372000, 0⟩, ⟨false, 0⟩), [], 0⟩], none⟩
  have := congrArg List.length (h (fun _ => 739865) (fun _ => none) M (bE 1 63924370200 (.brkStart 20 none))
    (⟨63924370200, 0⟩, ⟨false, 0⟩) 739865 20 none rfl rfl (by decide))
  revert this
  decide

/-- **C5's split as the owner's D116 restated it, refuted by D129** (README gap 5430): the `break` line a start already
ended its break for (`Machine.brkEnded`) writes one machine and no day family — so no prefix of block family effects makes
the arm `dayArm` of the line, whose day family is a segment and a record.  `arm_split` is restated with that case. -/
theorem arm_split_as_d116_stated_it_is_refuted :
    ¬ ∀ (dy : Cal.Instant → Nat) (sl : Nat → Option Nat) (m : Machine) (e : Entry) (t : At) (d : Nat),
      ∃ fx : List Effect, (∀ x ∈ fx, x.blockOnly = true) ∧ arm dy sl m e t d = fx ++ dayArm dy sl (placed m e) t d := by
  intro h
  let T : At := (⟨63924364800, 0⟩, ⟨false, 0⟩)
  let M : Machine := ⟨none, none, none, [], none, [], some T⟩
  let E : Entry := bE 4 63924364800 (.brk 20 (some 90) none)
  obtain ⟨fx, -, hfx⟩ := h (fun _ => 739865) (fun _ => none) M E T 739865
  have h1 : (arm (fun _ => 739865) (fun _ => none) M E T 739865).length = 1 := by decide
  have h2 : (dayArm (fun _ => 739865) (fun _ => none) (placed M E) T 739865).length = 2 := by decide
  have := congrArg List.length hfx
  rw [List.length_append, h1, h2] at this
  omega

end D129Witnesses

/-! ## D129 within D119's bound (W-50 track K; README gap 5438) -/

/-- **A late `break_start` past D119's bound is not ended by a start** (README gap 5438): `start a` 08:00 and `done a`
09:00 on the 7th, `start b` 08:00 and `stop b` 09:00 forty days later, then a `break_start` stamped 08:30 on the 7th —
past the 31 ledger days a late mark is read within (`pastBound`), so `firstStart` holds none, no start ends it, and it
runs, as every late mark past the bound is left unread and named.  Without the bound `b`'s start forty days on would end
it, a break forty days long. -/
theorem a_late_break_past_the_bound_is_not_ended_by_a_start :
    (replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63927820800 (bStart ['b']), bE 4 63927824400 (.stop ['b'] 0),
      bE 5 63924366600 (.brkStart 20 none)]).openBreak.isSome = true := by
  decide

/-! ## D129's stamp-order edges (stage 6, W-50 repair track R; README gaps 5500-5502)

Three edges W-50 track K's witnesses left unpinned, each found by the W-50 audit or critic.  Instants as before: 08:00 on
2026-09-07 is second 63924364800 (day 739865); probed in a scratch build under `MemoryMax=8G timeout 120` (§5.10a). -/

section D129Edges

/-- **A start that TIES the break's stamp and was logged BEFORE it ends nothing** (README gap 5500, the W-50 critic's
finding 2): `start a` 08:30, then a `break_start` stamped 08:30 — the start is earlier in the file, and D129 ends a
break at a start later in stamp order or, at a tie, later in the file, so the break runs over the open block.  Until the
W-50 repair `firstStep`'s `≤` ended it at once (`tm break` said it "ended at 10:20, at the `start` the log already holds
after it"). -/
theorem a_start_tying_the_break_logged_before_it_ends_nothing :
    (replay utcZone [bE 1 63924366600 (bStart ['a']), bE 2 63924366600 (.brkStart 15 none)]).openBreak.isSome = true := by
  decide

/-- **A drawn piece is not a `start`** (README gap 5501, the W-50 critic's finding 3): `start a` 08:30, paused at once
until 10:00 (D110's shape: begun inside a meeting), `done a` 10:30, then a late `break_start` stamped 09:00.  The block's
`start` (08:30) came before the break, so no start ends it: it runs (and nets the held block from 09:00 on, gap 5180's
reading of a running break); its own ten-minute `break` line, when it comes, ends it there and is recorded as ten minutes,
not swallowed.  Until the W-50 repair the block's first drawn piece (10:00) was read as a start: the break was "ended" at
10:00, recorded sixty minutes long, and its own line read as that break's (`Machine.brkEnded`).  What the break's line
does not give back to `a` is README gap 5302's (gap 5504). -/
theorem a_drawn_piece_is_not_a_start :
    let L := [bE 1 63924366600 (bStart ['a']), bE 2 63924366600 (.pause ['a']),
      bE 3 63924372000 (.unpause ['a']), bE 4 63924373800 (bDone ['a'] 30 false),
      bE 5 63924368400 (.brkStart 10 none)]
    (replay utcZone L).openBreak.isSome = true ∧
    (replay utcZone (L ++ [bE 6 63924368400 (.brk 10 (some 10) none)])).openBreak = none ∧
    ((replay utcZone (L ++ [bE 6 63924368400 (.brk 10 (some 10) none)])).days.get 739865).map
      (fun a => a.breaks.map (·.actualMin)) = some [some 10] := by
  decide

/-- **The EARLIEST start after a late break ends it, whatever order the blocks were logged in** (README gap 5502, the
W-50 audit's finding 2): two closed blocks, `a` 08:30–09:00 and `b` 10:00–10:30, logged `a` first, then a `break_start`
stamped 08:00 — it ends at `a`'s 08:30, thirty minutes, and both keep their thirty.  A `firstStep` keeping the latest
start would end it at 10:00 and net `a` away. -/
theorem the_earliest_start_ends_a_late_break :
    let f := replay utcZone [bE 1 63924366600 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 30 false),
      bE 3 63924372000 (bStart ['b']), bE 4 63924373800 (bDone ['b'] 30 false),
      bE 5 63924364800 (.brkStart 20 none)]
    f.openBreak = none ∧ (f.days.get 739865).map (fun a => a.breaks.map (·.actualMin)) = some [some 30] ∧
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.items.get ['b']).map (·.minutes) = some 30 := by
  decide

/-- **…and logged `b` first** (README gap 5502): the same two blocks, `b` 10:00–10:30 logged before `a` 08:30–09:00 (a
late block, D115), then the `break_start` stamped 08:00 — it still ends at 08:30, the earliest start, not at the first
held block in file order. -/
theorem the_earliest_start_ends_a_late_break_logged_in_either_order :
    let f := replay utcZone [bE 1 63924372000 (bStart ['b']), bE 2 63924373800 (bDone ['b'] 30 false),
      bE 3 63924366600 (bStart ['a']), bE 4 63924368400 (bDone ['a'] 30 false),
      bE 5 63924364800 (.brkStart 20 none)]
    f.openBreak = none ∧ (f.days.get 739865).map (fun a => a.breaks.map (·.actualMin)) = some [some 30] ∧
    (f.items.get ['a']).map (·.minutes) = some 30 ∧ (f.items.get ['b']).map (·.minutes) = some 30 := by
  decide

end D129Edges

/-! ### D137: a running break's line gives back what lies outside its span (README gaps 5504 and 5302, W-51 track K,
parity P134; appended at the module's end so no line the mutation roster pins moves) -/

section GiveBack137

open Log (Id U8 U32 Num)

/-- **A block no running break netted is given nothing back** (the owner's D137; AGENTS §5.8, the give-back bites only
where a running break took something). -/
theorem giveOne_of_no_run (dy : Cal.Instant → Nat) (C : Closed) (h : C.ran = []) : giveOne dy C = (C, [], 0) := by
  unfold giveOne; simp [h]

/-- **A late break's line gives back what lies after it** (the owner's D137, README gap 5504): `start a` 08:00, `done a`
09:00 with sixty, then — one machine, a clock behind the log — a `break_start` stamped 08:30, which runs and nets `a`
from 08:30 on (thirty: `a_break_start_logged_after_a_done_nets_it`), then its ten-minute `break` line: `a` reads fifty,
the block less the break's span, on the item, the day and the duration observation, drawn `[08:00, 08:30]` and
`[08:40, 09:00]` around the Break.  Until D137 it stayed at thirty (cheat 591). -/
theorem a_late_breaks_line_gives_back_what_lies_after_it :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (bDone ['a'] 60 false),
      bE 3 63924366600 (.brkStart 20 none), bE 4 63924366600 (.brk 20 (some 10) none)]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧ (f.days.get 739865).map (·.blockMin) = some 50 ∧
    f.durations.map (·.actualMin) = [50] ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun g => (g.start.1.sec, g.stop.1.sec, g.kind)))
      = some [(63924364800, 63924366600, .block ['a']), (63924366600, 63924367200, .brk none),
        (63924367200, 63924368400, .block ['a'])] := by
  decide

/-- **…and a running break's line gives back the close it did not reach** (README gap 5302: two machines whose lines a
sync interleaves): `start a` 08:00, a `break_start` at 08:30 — the break runs — `done a` 09:00 with sixty, netted to
thirty at the close, then the `break` line saying the break lasted ten minutes: fifty. -/
theorem a_running_breaks_line_gives_back_the_close_it_did_not_reach :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924366600 (.brkStart 20 none),
      bE 3 63924368400 (bDone ['a'] 60 false), bE 4 63924366600 (.brk 20 (some 10) none)]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧ (f.days.get 739865).map (·.blockMin) = some 50 ∧
    f.durations.map (·.actualMin) = [50] := by
  decide

/-- **…and a stopped block's credit comes back to its day's ci-unknown minutes** (D137 over a cut's credit, which has no
ci): `start a` 08:00, `stop` 09:00, the late `break_start` at 08:30 and its ten-minute line — fifty. -/
theorem a_late_breaks_line_gives_back_a_stopped_block :
    let f := replay utcZone [bE 1 63924364800 (bStart ['a']), bE 2 63924368400 (.stop ['a'] 0),
      bE 3 63924366600 (.brkStart 20 none), bE 4 63924366600 (.brk 20 (some 10) none)]
    (f.items.get ['a']).map (·.minutes) = some 50 ∧ (f.days.get 739865).map (·.blockMin) = some 50 := by
  decide

/-- **The running break remembers exactly the pieces it met** (the owner's D137; README gap 5585's pin for `meets`): a
held block drawn `[07:00, 07:30]` and `[08:00, 09:00]`, netted by a running break from 08:30 — `Closed.ran` holds the
second piece whole and not the first, which the break never reached (so the give-back re-draws only what it took), and
`Closed.ranMin` the thirty minutes it took. -/
theorem runOne_remembers_only_the_pieces_it_met :
    let C : Closed := ⟨['a'], 739865, 739865, none, 90,
      [⟨(⟨63924361200, 0⟩, ⟨false, 0⟩), (⟨63924363000, 0⟩, ⟨false, 0⟩), 739865⟩,
       ⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865⟩],
      none, (⟨63924361200, 0⟩, ⟨false, 0⟩), [], 0⟩
    let R := runOne (fun _ => 739865) (⟨63924366600, 0⟩, ⟨false, 0⟩) (⟨63924368400, 0⟩, ⟨false, 0⟩) 739865 C
    R.ran = [⟨(⟨63924364800, 0⟩, ⟨false, 0⟩), (⟨63924368400, 0⟩, ⟨false, 0⟩), 739865⟩] ∧ R.ranMin = 30 ∧
      R.min = 60 := by
  decide

end GiveBack137

end Replay
end Tm
