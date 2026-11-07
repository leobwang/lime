import LimeKernel.SealLaw6Ctx
import LimeKernel.SealCutState
import LimeKernel.SealCutHeaders
import LimeKernel.SealCutTags2
import LimeKernel.SealCutSlept
import LimeKernel.SealCutWakes
import LimeKernel.SealCutGroup
import LimeKernel.SealCutStep
/-!
# SealLaw6Ckpt — a reseal's checkpoint and records are the seal's (stage 5, D9, W2: law 6)

At a valid cut `j`, the resealed checkpoint is the checkpoint of the lines up to the cut knowing the rest, at the new
ledger day, and the day and window records it emits are those lines' records of `[L, L')` and `[H, H')`
(`rs_state_parts`).  Field by field: the state at the cut agrees above the horizons (`cut_state_agrees`), the stored
wakes, `slept_by_day`, tag lines and settled undos compose (`storedWakes_at_cut`, `storedSlept_congr_get`,
`keptTags_append`, `tagOverflow_append`, `settled_at_cut`), and the unfolded lines cancel nothing folded
(`survivors_at_cut`).  Specification only (D9-21).
-/
namespace Lime
namespace Seal

open Replay (State survivors wakeInstants keptWakes dayOf)
open Log (Entry)

/-- **The resealed checkpoint and records are the seal's.** -/
theorem rs_state_parts (z : Cal.Tz) (T₀ T L : Nat) (a r b : List Log.Line) (term : Bool) (p : Policy) (run : Run)
    (j : Nat) (hc : Log.contiguousFrom 1 (a ++ b) = true) (hr : r <+: b)
    (hrun : resumeRun z T (ckptOf z T₀ L a r) b = .ok run)
    (hmig : migrationOk (ckptOf z T₀ L a r) T = true)
    (hcut : cutOk z T (ckptOf z T₀ L a r) b term p run j = true) :
    rsCkpt z T (ckptOf z T₀ L a r) b p run j
        = ckptOf z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) (b.drop j) ∧
    rsDays z T (ckptOf z T₀ L a r) p run j
        = dayRecordsBetween z T L (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) ∧
    rsWindow z T (ckptOf z T₀ L a r) p run j
        = windowRecordsBetween z T (horizonOf L) (horizonOf (sealDayOf z T (ckptOf z T₀ L a r) p run j))
            (a ++ b.take j) := by
  obtain ⟨B', n, sv, kw, sl, Bj, Brest, svj, svr, hbE, hd, hent, hNq, hsvq, hsv, hidxq, hkw, hslq, hsl, hn, hz, hLT,
    hg, hsteps, hhdr, hjle, hBj, hBrest, hsplit, hsvj, hsvr, hsvs, hsvjB, hsvrB, hsep, hsettled, hvi, hAc, hBjc,
    hBrestc, hTake, hDrop, hWs⟩ := rs_context z T₀ T L a r b term p run j hc hr hrun hmig hcut
  have hLE : ∀ x y : List Log.Line, Log.lineEntries (x ++ y) = Log.lineEntries x ++ Log.lineEntries y :=
    fun x y => List.filterMap_append
  have hLW : ∀ x y : List Log.Line, Log.lineWarnings (x ++ y) = Log.lineWarnings x ++ Log.lineWarnings y :=
    fun x y => List.filterMap_append
  have hlen : (a ++ b.take j).length = a.length + j := by
    simp only [List.length_append, List.length_take]; omega
  have hspec : ckptOf z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j) (b.drop j)
      = ckptOfEntries z T (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a.length + j) (Log.lineEntries a ++ Bj) Brest
          (Log.lineWarnings a ++ (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ a.length + j))) := by
    unfold ckptOf; rw [hlen, hLE, hTake, hDrop, hLW, hWs]
  have hdays : dayRecordsBetween z T L (sealDayOf z T (ckptOf z T₀ L a r) p run j) (a ++ b.take j)
      = dayRecordsOfEntries z L (sealDayOf z T (ckptOf z T₀ L a r) p run j) (Log.lineEntries a ++ Bj) := by
    unfold dayRecordsBetween; rw [hLE, hTake]
  have hwin : windowRecordsBetween z T (horizonOf L) (horizonOf (sealDayOf z T (ckptOf z T₀ L a r) p run j))
        (a ++ b.take j)
      = windowRecordsOfEntries z (horizonOf L) (horizonOf (sealDayOf z T (ckptOf z T₀ L a r) p run j))
          (Log.lineEntries a ++ Bj) := by
    unfold windowRecordsBetween; rw [hLE, hTake]
  rw [hspec, hdays, hwin]
  have hKe : ckptOf z T₀ L a r = ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r)
      (Log.lineWarnings a) := rfl
  have hKcut : (ckptOf z T₀ L a r).cut = a.length := rfl
  have hKL : (ckptOf z T₀ L a r).ledgerDay = L := rfl
  have hLL : L ≤ sealDayOf z T (ckptOf z T₀ L a r) p run j := le_sealDayOf z T (ckptOf z T₀ L a r) p run j
  -- the reseal's parts, on the context's entries
  have hSvj : rsSvj (ckptOf z T₀ L a r) run j = svj := by unfold rsSvj; rw [hsvq, hKcut, hsvj]
  have hBjE : rsBj (ckptOf z T₀ L a r) run j = Bj := by unfold rsBj; rw [hent, hKcut, hBj]
  have hN : rsN (ckptOf z T₀ L a r) run = n := by unfold rsN; rw [hent, hn]
  have hSlept : rsSlept z (ckptOf z T₀ L a r) run j = (ckptOf z T₀ L a r).sleptByDay
      ++ Replay.sleptByDay z (keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj)) svj := by
    unfold rsSlept rsKwj; rw [hSvj]
  have hSt : rsSt z (ckptOf z T₀ L a r) run j
      = rebindState (Replay.KMap.get ((ckptOf z T₀ L a r).sleptByDay
          ++ Replay.sleptByDay z (keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj)) svj))
        (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) := by
    unfold rsSt rsRj; rw [hSlept, hSvj, hidxq, hslq, hN]
  have hHs : rsHs z (ckptOf z T₀ L a r) run j = storedHeaders (ckptOf z T₀ L a r)
      ++ (tailHeaders (dayOf z kw) (ckptOf z T₀ L a r).settled (Log.lineEntries r ++ B')).take Bj.length := by
    unfold rsHs; rw [hidxq, hent, hBjE]
  have hQA : rsQA (ckptOf z T₀ L a r) run j = Bj.flatMap entryInstants := by unfold rsQA; rw [hBjE]
  have hMerged : rsMerged (ckptOf z T₀ L a r) run j = mergeTagLines (ckptOf z T₀ L a r).tagLast (tagLines svj) := by
    unfold rsMerged; rw [hSvj]
  have hKwj : rsKwj z (ckptOf z T₀ L a r) run j = keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj) := by
    unfold rsKwj; rw [hSvj]
  have hWsE : rsWs (ckptOf z T₀ L a r) b j = (Log.lineWarnings b).filter (fun w => decide (w.1 ≤ a.length + j)) := by
    unfold rsWs; rw [hKcut]
  have hSettled : settledAt (ckptOf z T₀ L a r) run j
      = (((Replay.danglingOf (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries r ++ B'))).2.filter
          (fun u => decide (a.length + j < u.line))).map (·.line)).reverse := by
    unfold settledAt; rw [hNq, hKcut]; rfl
  unfold rsCkpt rsDays rsWindow
  rw [hSt, hHs, hQA, hMerged, hKwj, hSlept, hWsE, hBjE, hSettled]
  generalize hsd : sealDayOf z T (ckptOf z T₀ L a r) p run j = L' at hLL ⊢
  -- the state at the cut
  have hstepsj : ∀ pre e post, svj = pre ++ e :: post →
      (stepCheck z (dayOf z kw) sl (ckptOf z T₀ L a r)
        (pre.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) e).2 = none :=
    fun pre e post hs => hsteps pre e (post ++ svr) (by rw [hsvs, hs]; simp)
  have hg' : g1 (ckptOfEntries z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a))
      (unsettled (settledOf (Log.lineEntries a) (Log.lineEntries r)) (Log.lineEntries r ++ B')) = none := hg
  obtain ⟨hAgree, hfs, hIdx, hbd, hbdd, hkd, hki, hkl, hkdr, hkdd, hRd, hRdd, hSl⟩ :=
    cut_state_agrees z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) n hd
      (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps Bj Brest svj svr hsplit hsvs hsvjB hsvrB
      (fun q => !isFuture T q) hsep
  have hsurvCut := survivors_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) hd
    hg' (a.length + j) hAc hsettled hvi Bj Brest hsplit hBjc hBrestc
  have hd1 : ((Log.lineEntries a ++ Bj) ++ Brest).Pairwise (fun (x y : Entry) => x.line < y.line) := by
    rw [List.append_assoc, ← hsplit]; exact hd
  have hd0 : ((Log.lineEntries a ++ Bj) ++ ([] : List Entry)).Pairwise (fun (x y : Entry) => x.line < y.line) := by
    rw [List.append_nil]; exact hd1.sublist (List.sublist_append_left _ _)
  have hfsnil : foldedSurvivors (Log.lineEntries a ++ Bj) [] = foldedSurvivors (Log.lineEntries a ++ Bj) Brest := by
    rw [foldedSurvivors_nil, hsurvCut]
  have hcongrS := foldedState_congr_er z (Log.lineEntries a ++ Bj) [] Brest hfsnil
  have hcongrH := foldedHeaders_congr_er z (Log.lineEntries a ++ Bj) [] Brest hd0 hd1 hfsnil
  generalize hx : rebindState (Replay.KMap.get ((ckptOf z T₀ L a r).sleptByDay
      ++ Replay.sleptByDay z (keptWakes z ((ckptOf z T₀ L a r).wakes ++ wakeInstants svj)) svj))
      (svj.foldl (Replay.stepWith z (dayOf z kw) sl) (restore (ckptOf z T₀ L a r) n)) = x at hAgree ⊢
  have hxk : AllKeyed x := by
    rw [← hx]; exact (AllKeyed.foldl z _ _ svj (allKeyed_restore _ n)).rebind _
  have hyk := allKeyed_foldedState z (Log.lineEntries a ++ Bj) Brest
  have hpk := allKeyed_foldedState z (Log.lineEntries a) (Log.lineEntries r)
  have hxd : ∀ d, d < L → x.days.get d = none := fun d hd' => by rw [← hx]; exact hRd d hd'
  have hxdd : ∀ d i, d < horizonOf L → x.doneDates.get (d, i) = none := fun d i hd' => by rw [← hx]; exact hRdd d i hd'
  -- the headers
  have hFH := foldedHeaders_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) n hd
    (ckptOf z T₀ L a r) hKe sv hsv hg kw hkw sl hsteps hhdr Bj Brest hsplit hIdx
  have hhs : ∀ d, L ≤ d →
      (storedHeaders (ckptOf z T₀ L a r) ++ (tailHeaders (dayOf z kw) (ckptOf z T₀ L a r).settled
        (Log.lineEntries r ++ B')).take Bj.length).filter (fun p => decide (p.1 = d))
      = (foldedHeaders z (Log.lineEntries a ++ Bj) Brest).filter (fun p => decide (p.1 = d)) := by
    intro d hd'
    have hst : (storedHeaders (ckptOf z T₀ L a r)).filter (fun p => decide (p.1 = d))
        = (foldedHeaders z (Log.lineEntries a) (Log.lineEntries r)).filter (fun p => decide (p.1 = d)) :=
      storedHeaders_filter z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a) d hd'
    rw [hFH, List.filter_append, List.filter_append, hst]
  -- the stored checkpoint's fields
  have hmaxT : (ckptOf z T₀ L a r).maxT
      = maxInstant? (((Log.lineEntries a).flatMap entryInstants).filter (fun q => !isFuture T₀ q)) :=
    ckpt_maxT z T₀ L a.length _ _ _
  have hff : (ckptOf z T₀ L a r).futureFloor
      = minInstant? (((Log.lineEntries a).flatMap entryInstants).filter (isFuture T₀)) :=
    ckpt_futureFloor z T₀ L a.length _ _ _
  have hKtag : (ckptOf z T₀ L a r).tagLast = keptTags (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) :=
    ckpt_tagLast z T₀ L a.length _ _ _
  have hKover : (ckptOf z T₀ L a r).tagOverflow
      = decide ((keptTags (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))).length
          < (tagLines (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r))).length) :=
    ckpt_tagOverflow z T₀ L a.length _ _ _
  have hKlast : (ckptOf z T₀ L a r).lastDay
      = Replay.maxDay? ((foldedState z (Log.lineEntries a) (Log.lineEntries r)).days.pairs.map Prod.fst) :=
    ckpt_lastDay z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hKcount : (ckptOf z T₀ L a r).entryCount = (Log.lineEntries a).length :=
    ckpt_entryCount z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hKwarn : (ckptOf z T₀ L a r).warnings = (Log.lineWarnings a).take maxWarnings :=
    ckpt_warnings z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  have hKwov : (ckptOf z T₀ L a r).warnOverflow = (Log.lineWarnings a).length - maxWarnings :=
    ckpt_warnOverflow z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) (Log.lineWarnings a)
  refine ⟨?_, ?_, ?_⟩
  · unfold ckptOfEntries
    dsimp only
    rw [Ckpt.mk.injEq]
    refine ⟨rfl, hz, by rw [hKcut], rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hAgree.machine, ?_, ?_, ?_, ?_, ?_, ?_,
      hAgree.lastEff, ?_, hAgree.unknown, hAgree.longestLeak, by rw [hAgree.rwarns], ?_, ?_⟩
    · rw [List.flatMap_append]; exact resealed_maxT T₀ T _ _ _ hmaxT hff hmig
    · rw [List.flatMap_append]; exact resealed_futureFloor T₀ T _ _ _ hmaxT hff hmig
    · rw [typedOf_append]; exact resealed_maxTyped T₀ T _ _ _ _ (typedOf_sub _) hmaxT hff hmig (ckpt_maxTyped z T₀ L a.length _ _ _)
    · -- the stored wakes
      have hKw : (ckptOf z T₀ L a r).wakes
          = storedWakes L (keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)))) :=
        ckpt_wakes z T₀ L a.length _ _ _
      have hFI : foldedIndex z (Log.lineEntries a ++ Bj) Brest
          = keptWakes z (wakeInstants (foldedSurvivors (Log.lineEntries a) (Log.lineEntries r)) ++ wakeInstants svj) := by
        unfold foldedIndex; rw [hfs, wakeInstants_append]
      obtain ⟨hsepA, hheadA⟩ := resume_sep z (dayOf z kw) sl (ckptOf z T₀ L a r) (restore _ n) T₀
        ((Log.lineEntries a).flatMap entryInstants) svj hmaxT hff hstepsj
      rw [hKL] at hheadA
      rw [hKw, hFI]
      refine storedWakes_at_cut z L L' hLL (fun q => !isFuture T₀ q) ((Log.lineEntries a).flatMap entryInstants) _ _
        (fun w hw => ?_) hsepA hheadA
      obtain ⟨e, he, _, rfl⟩ := mem_wakeInstants hw
      exact List.mem_flatMap.2 ⟨e, (foldedSurvivors_sublist _ _).subset he, by simp [entryInstants]⟩
    · exact storedSlept_congr_get _ _ L' (fun d hd' => hSl d (Nat.le_trans hLL hd'))
    · rw [hfs, keptTags_append, hKtag]
    · rw [hfs, tagOverflow_append, hKtag, hKover]
    · exact settled_at_cut z T₀ L a.length (Log.lineEntries a) (Log.lineEntries r) B' (Log.lineWarnings a) hd hg'
        (a.length + j) hAc hsettled hvi Bj Brest hsplit hBjc hBrestc
    · exact items_merged_eq_raw (ckptOf z T₀ L a r) hpk hxk hyk (ckpt_items z T₀ L a.length _ _ _)
        (ckpt_window z T₀ L a.length _ _ _) hAgree hbdd hki hkl hkdr hkdd hxdd
    · exact windowsFrom_eq hxk hyk (hAgree.mono hLL (horizonOf_mono hLL))
    · exact instOtherOf_eq hxk hyk hAgree
    · exact namedOf_eq hxk hyk hAgree
    · exact daysFrom_eq_raw hxk hyk (hAgree.mono hLL (horizonOf_mono hLL)) _ _
        (fun d hd' => hhs d (Nat.le_trans hLL hd'))
    · rw [hKlast]
      exact lastDay_union hpk hxk hyk hkd hAgree.days hbd hxd
    · rw [hKcount, List.length_append]
    · rw [hKwarn]
      exact take_take_append _ _ _
    · rw [hKwarn, hKwov, List.length_take, List.length_append]
      omega
  · unfold dayRecordsOfEntries
    rw [hKL, hcongrS, hcongrH, daysIn_eq_filter, daysIn_eq_filter, daysFrom_eq_raw hxk hyk hAgree _ _ hhs,
      hAgree.machine]
  · unfold windowRecordsOfEntries
    rw [hKL, hcongrS, windowsIn_eq_filter, windowsIn_eq_filter, windowsFrom_eq hxk hyk hAgree]

/-- **The fact across a checkpoint and a resume is the whole log's** (the owner's D154, W-54 third repair track K, README gap 6023): where the fence `f` separates the folded instants as the seal did — every one not future at the seal at or before it, every future one after it (`K.maxT`, `K.futureFloor`) — the checkpoint's latest typed stamp and the tail's are the whole log's latest at or before `f`, wherever the cut fell.  So a far-future line hides nothing, and a cold rebuild answers what a resume does.  Past that subdomain `f` has reached a line fenced as future when it was folded, and the fact is short of it until a rebuild (gap 6026). -/
theorem latestTyped_is_the_whole_logs (z : Cal.Tz) (T₀ L cut : Nat) (es er bs : List Entry) (ws : List (Nat × Log.LWarn)) (f : Cal.Instant)
    (hm : (ckptOfEntries z T₀ L cut es er ws).maxT.all (fun q => decide (q ≤ f)) = true)
    (hff : (ckptOfEntries z T₀ L cut es er ws).futureFloor.all (fun q => decide (f < q)) = true) :
    latestTyped (ckptOfEntries z T₀ L cut es er ws) bs f = maxInstant? ((typedOf (es ++ bs)).filter (fun q => decide (q ≤ f))) := by
  have h1 : ∀ q ∈ typedOf es, decide (q ≤ f) = !isFuture T₀ q := by
    intro q hq
    have hQ := typedOf_sub es q hq
    cases hc : isFuture T₀ q
    · have hmem : q ∈ (es.flatMap entryInstants).filter (fun q => !isFuture T₀ q) := List.mem_filter.2 ⟨hQ, by simp [hc]⟩
      rw [ckpt_maxT] at hm
      cases hmx : maxInstant? ((es.flatMap entryInstants).filter (fun q => !isFuture T₀ q)) with
      | none => rw [maxInstant?_none _ hmx] at hmem; cases hmem
      | some m =>
        rw [hmx] at hm
        have hle := maxInstant?_spec _ m hmx q hmem
        simp only [Option.all_some, decide_eq_true_eq] at hm
        have : q ≤ f := by rw [Cal.Instant.le_iff] at hle hm ⊢; omega
        simp [this]
    · have hmem : q ∈ (es.flatMap entryInstants).filter (isFuture T₀) := List.mem_filter.2 ⟨hQ, hc⟩
      rw [ckpt_futureFloor] at hff
      cases hmn : minInstant? ((es.flatMap entryInstants).filter (isFuture T₀)) with
      | none => rw [minInstant?_none _ hmn] at hmem; cases hmem
      | some m =>
        rw [hmn] at hff
        have hle := minInstant?_spec _ m hmn q hmem
        simp only [Option.all_some, decide_eq_true_eq] at hff
        have : ¬ q ≤ f := by rw [Cal.Instant.le_iff] at hle ⊢; rw [Cal.Instant.lt_iff] at hff; omega
        simp [this]
  have h2 : (typedOf es).filter (fun q => decide (q ≤ f)) = (typedOf es).filter (fun q => !isFuture T₀ q) :=
    List.filter_congr h1
  unfold latestTyped
  rw [ckpt_maxTyped, typedOf_append, List.filter_append, maxInstant?_append, h2]
  congr 1
  cases hmx : maxInstant? ((typedOf es).filter (fun q => !isFuture T₀ q)) with
  | none => rfl
  | some m =>
    have hmem := maxInstant?_mem _ m hmx
    have hl := (List.mem_filter.1 hmem)
    have : decide (m ≤ f) = true := by rw [h1 m hl.1]; exact hl.2
    simp [Option.filter, this]

set_option maxRecDepth 8000 in
/-- **The fact skips a far-future line and counts an undone one** (the owner's D154, README gap 6023): a `note` at 09:00 undone at 09:01, an `energy` line ahead, a `note` in 2028 past the fence: 09:01. -/
theorem latestTyped_skips_a_far_future_line_and_counts_an_undone_one :
    latestTyped (Ckpt.empty Replay.utcZone) [Replay.bE 1 63924368400 (.note ['n']), Replay.bE 2 63924368460 (.undo ['n', 'o', 't', 'e'] none), Replay.bE 3 63924400000 (.energy 3 4 (.nat 2) ['h']), Replay.bE 4 63987526800 (.note ['f'])] ⟨63924454800, 0⟩ = some ⟨63924368460, 0⟩ := by
  decide

end Seal
end Lime
