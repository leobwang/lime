import LimeKernel
/-!
Axiom audit.  Every theorem this stage claims must depend only on Lean's three
standard axioms — never `sorryAx`.  Run with:

    LEAN_PATH=.lake/build/lib/lean lean Check.lean
-/
open Lime

-- the horizon order, derived
#print axioms Lime.coarsen_month
#print axioms Lime.coarsen_saturates_only_at_month
#print axioms Lime.demote_is_one_step
#print axioms Lime.closeTo_target_is_open
#print axioms Lime.impl_day_rule_disagrees
#print axioms Lime.containing_can_target_a_closed_region
#print axioms Lime.horizonPrecedes_asymm
#print axioms Lime.demotion_target_follows_the_closed_region

-- entity versus observation
#print axioms Lime.archive_elsewhere
#print axioms Lime.one_line_per_file
#print axioms Lime.exactly_one_live
#print axioms Lime.archive_line_is_demoted

-- the plan as one object
#print axioms Lime.no_two_lines_of_one_id_in_one_file
#print axioms Lime.lines_per_id_le_two
#print axioms Lime.no_two_lines_of_one_id_in_one_path
#print axioms Lime.no_line_is_lost
#print axioms Lime.the_tombstone_is_behind_the_live_line
#print axioms Lime.a_backwards_demotion_is_refused
#print axioms Lime.a_reopened_record_needs_no_horizon
#print axioms Lime.transform_closed

-- the grammar
#print axioms Lime.readNat_digitsOf
#print axioms Lime.tokenize_raw
#print axioms Lime.tokenize_toks
#print axioms Lime.serialize_parse
#print axioms Lime.parse_serialize_box_ended
#print axioms Lime.renderSplit_splitDoc
#print axioms Lime.view_set_is_not_silent
#print axioms Lime.lead_edit_is_silent
#print axioms Lime.setEst_canonical_box_ended
#print axioms Lime.setEst_line_reparses

-- the commands
#print axioms Lime.move_into_archive_file_is_rejected
#print axioms Lime.plan_move_into_archive_file_is_rejected
#print axioms Lime.move_idem
#print axioms Lime.move_last_wins
#print axioms Lime.move_last_wins_refuted_globally
#print axioms Lime.move_back_restores
#print axioms Lime.move_back_at_a_fresh_rank_is_not_the_inverse
#print axioms Lime.drop_idem
#print axioms Lime.drop_preserves_archive_glyph
#print axioms Lime.readopt_reopens
#print axioms Lime.set_is_not_silent
#print axioms Lime.set_last_wins
#print axioms Lime.stamps_accumulate_across_readopt
#print axioms Lime.demote_twice_is_not_a_thing
#print axioms Lime.demote_on_a_standing_tombstone_is_refused
#print axioms Lime.demote_roundtrips
#print axioms Lime.demote_archive_none
#print axioms Lime.readopt_demote_not_id
#print axioms Lime.readopt_demote_id_mod_stamps
#print axioms Lime.readopt_of_a_live_record_is_refused
#print axioms Lime.readopt_after_demote_succeeds
#print axioms Lime.floor_and_respect_are_incompatible
#print axioms Lime.demoteEst_conserves
#print axioms Lime.demoteEst_respects_user
#print axioms Lime.mapAt_ok_of_inRange
#print axioms Lime.mapAt_rejects_unoriented
#print axioms Lime.cmdMove_succeeds
#print axioms Lime.demote_into_a_horizon_that_does_not_follow_is_rejected
#print axioms Lime.resolveDest_rejects

-- the glyph is a function of placement, and the loader is its inverse
#print axioms Lime.glyphOfStatus_statusOfGlyph
#print axioms Lime.statusOfGlyph_glyphOfStatus
#print axioms Lime.glyphAt_live
#print axioms Lime.glyphAt_statusOfGlyph
#print axioms Lime.glyphAt_statusOfGlyph_paired
#print axioms Lime.every_glyph_has_a_state
#print axioms Lime.a_differing_demotion_pair_renders_back

-- the boundary
#print axioms Lime.grain_rejects_99
#print axioms Lime.lone_placement_renders_back
#print axioms Lime.orientPair_comm
#print axioms Lime.pairedEntity_order_independent
#print axioms Lime.unordered_horizons_are_rejected
#print axioms Lime.paired_placement_renders_back
#print axioms Lime.paired_renders_each_placement
#print axioms Lime.the_kernel_can_read_the_pairs_it_writes
#print axioms Lime.load_render_line
#print axioms Lime.freshRank_gt
#print axioms Lime.move_out_and_back_is_not_the_inverse
#print axioms Lime.move_to_a_document_that_does_not_exist_is_rejected
#print axioms Lime.dedupIds_nodup
#print axioms Lime.firstDupPath_none

-- §6.3's three close rows, generated from one rule at three grains, and the rule
-- horizon.rs:1323 uses versus the derived one on a Sunday closed on Monday.  Both
-- stood here as `#eval` — a PRINT, read by a human and by no gate — until W-31's
-- repair found that `#eval` is `run_cmd` by another spelling and walked a new
-- axiom past every gate (README gap 2255).  The second was already a theorem —
-- `impl_day_rule_disagrees`, audited at the head of this file — and the first is
-- one now, audited here.
#print axioms Lime.the_three_close_rows_at_day_250

-- ===========================================================================
-- APPENDED: §3.1's item fields and the rest of the plan-level tier.
-- ===========================================================================

-- the bounded types and their smart constructors
#print axioms Lime.clock_rejects_25h
#print axioms Lime.clock_rejects_minute_60
#print axioms Lime.weekday_rejects_7
#print axioms Lime.monthDay_rejects_0
#print axioms Lime.monthDay_rejects_32
#print axioms Lime.monthDay_roundtrips
#print axioms Lime.TagSet.no_duplicates
#print axioms Lime.TagSet.mem_ofList

-- widening the entity leaves the tier structure alone
#print axioms Lime.wf_ignores_the_item_fields

-- §5.3's default `on_miss`, derived
#print axioms Lime.onMiss_interval
#print axioms Lime.onMiss_point
#print axioms Lime.onMiss_window
#print axioms Lime.effectiveOnMiss_override
#print axioms Lime.effectiveOnMiss_default

-- `@parent`: the walk, sound and complete, and the check bites
#print axioms Lime.anc_add
#print axioms Lime.chain_dup_gives_cycle
#print axioms Lime.parentsAcyclic_sound
#print axioms Lime.parentsAcyclic_complete
#print axioms Lime.self_parent_is_rejected
#print axioms Lime.climb_reaches_a_root
#print axioms Lime.every_item_has_a_root
#print axioms Lime.no_item_is_its_own_ancestor
#print axioms Lime.parent_names_an_item

-- `after:`: the peel, sound and complete, and the check bites
#print axioms Lime.peelN_empty_or_fixed
#print axioms Lime.fixed_is_deadlocked
#print axioms Lime.afterAcyclic_sound
#print axioms Lime.afterAcyclic_complete
#print axioms Lime.self_dep_is_rejected
#print axioms Lime.no_deadlocked_set
#print axioms Lime.dep_names_an_item

-- `Normalized`: a site names one line
#print axioms Lime.site_names_one_line
#print axioms Lime.no_prose_line_shares_a_rank

-- §3.2's derived fields
#print axioms Lime.effectiveShape_as_written
#print axioms Lime.effectiveShape_prep
#print axioms Lime.effectiveShape_does_not_reach_the_grandparent
#print axioms Lime.effectiveCi_explicit
#print axioms Lime.effectiveCi_inherits
#print axioms Lime.effectiveCi_default
#print axioms Lime.rootPrio_of_a_root
#print axioms Lime.rootPrio_walks_past_the_child

-- §4.2's sections and §4.3's per-file-kind shapes
#print axioms Lime.a_day_file_holds_only_pinned_items
#print axioms Lime.calendar_lines_are_intervals
#print axioms Lime.a_routine_line_need_not_carry_the_open_flag
#print axioms Lime.routine_lines_have_a_window_or_after_done
#print axioms Lime.optional_items_declare_a_duration
#print axioms Lime.a_shapeless_calendar_line_is_rejected
#print axioms Lime.an_unpinned_day_item_is_rejected

-- ==========================================================================
-- APPENDED at the stage-one merge: the modules three concurrent branches
-- each added, which none of them could extend without conflicting.
-- ==========================================================================

-- Arith.lean
#print axioms Lime.Arith.denPos
#print axioms Lime.Arith.mkPos_num
#print axioms Lime.Arith.mkPos_den
#print axioms Lime.Arith.le_agrees_with_exact_division
#print axioms Lime.Arith.utilGe_eq_le
#print axioms Lime.Arith.utilGe_capacity_zero
#print axioms Lime.Arith.utilDefined_iff
#print axioms Lime.Arith.util_zero_over_zero_is_undefined
#print axioms Lime.Arith.util_zero_over_zero_is_hot
#print axioms Lime.Arith.utilScaledGe_cross
#print axioms Lime.Arith.utilScaledGe_eq_le
#print axioms Lime.Arith.isHot_iff
#print axioms Lime.Arith.impossible_imp_hot
#print axioms Lime.Arith.hot_and_possible_iff_exact
#print axioms Lime.Arith.binOf_ix
#print axioms Lime.Arith.binOf_eq_hot_iff
#print axioms Lime.Arith.binOf_eq_plus_iff
#print axioms Lime.Arith.rungs_le
#print axioms Lime.Arith.default_bin_le_three
#print axioms Lime.Arith.rungs_capacity_zero
#print axioms Lime.Arith.binOf_capacity_zero
#print axioms Lime.Arith.utilGe_mono
#print axioms Lime.Arith.rungs_antitone
#print axioms Lime.Arith.binOf_antitone
#print axioms Lime.Arith.rungs_mono_need
#print axioms Lime.Arith.rungs_anti_avail
#print axioms Lime.Arith.countP_tail_zero
#print axioms Lime.Arith.ladder_eq_rungs
#print axioms Lime.Arith.default_ladder_eq_rungs
#print axioms Lime.Arith.defaultBins_match_the_spec
#print axioms Lime.Arith.utilGe_edge_mono
#print axioms Lime.Arith.defaultBins_are_the_intervals
#print axioms Lime.Arith.log2_ladder_disagrees_at_eleven_percent
#print axioms Lime.Arith.floorQ_spec
#print axioms Lime.Arith.floorQ_le_self
#print axioms Lime.Arith.self_lt_floorQ_succ
#print axioms Lime.Arith.floorQ_withinOne
#print axioms Lime.Arith.floorQ_mono
#print axioms Lime.Arith.ceilQ_ge
#print axioms Lime.Arith.ceilQ_lt
#print axioms Lime.Arith.ceilQ_spec
#print axioms Lime.Arith.self_le_ceilQ
#print axioms Lime.Arith.ceilQ_withinOne
#print axioms Lime.Arith.ceilQ_mono
#print axioms Lime.Arith.floorQ_le_ceilQ
#print axioms Lime.Arith.halfUpQ_eq_floor
#print axioms Lime.Arith.halfUpQ_spec
#print axioms Lime.Arith.halfUpQ_withinOne
#print axioms Lime.Arith.halfUpQ_mono
#print axioms Lime.Arith.floorQ_le_halfUpQ
#print axioms Lime.Arith.halfUpQ_le_ceilQ
#print axioms Lime.Arith.rounding_agrees_when_exact
#print axioms Lime.Arith.scale_num
#print axioms Lime.Arith.scale_den
#print axioms Lime.Arith.needMin_covers
#print axioms Lime.Arith.needMin_ge_remaining
#print axioms Lime.Arith.needMin_safety_ge_remaining
#print axioms Lime.Arith.needMin_safety_examples
#print axioms Lime.Arith.rounding_the_need_changes_the_bin
#print axioms Lime.Arith.budget_eight_hours
#print axioms Lime.Arith.budget_mono_window
#print axioms Lime.Arith.overRatio_eq_lt
#print axioms Lime.Arith.overRatio_example
#print axioms Lime.Arith.plannedMin_mono
#print axioms Lime.Arith.plannedMin_withinOne
#print axioms Lime.Arith.plannedMin_example
#print axioms Lime.Arith.ramp_le_one
#print axioms Lime.Arith.ramp_full
#print axioms Lime.Arith.ramp_zero
#print axioms Lime.Arith.ramp_antitone
#print axioms Lime.Arith.defaultRamp_examples
#print axioms Lime.Arith.posterior_can_go_negative
#print axioms Lime.Arith.energyAfter_nonpos
#print axioms Lime.Arith.energyAfter_no_report
#print axioms Lime.Arith.energyAfter_examples

-- Boundary.lean
#print axioms Lime.grain_rejects_out_of_range
#print axioms Lime.grain_accepts_month
#print axioms Lime.dedupIds_cons
#print axioms Lime.mem_dedupIds
#print axioms Lime.orientPair_cases
#print axioms Lime.pairEntity_renders_back
#print axioms Lime.foldl_max_ge
#print axioms Lime.le_foldl_max
#print axioms Lime.live_line_mem
#print axioms Lime.demote_to_a_document_that_does_not_exist_is_rejected
#print axioms Lime.applyAll_closed

-- Cal.lean
#print axioms Lime.Cal.ys_zero
#print axioms Lime.Cal.ys_one
#print axioms Lime.Cal.ys_era_len
#print axioms Lime.Cal.ys_era
#print axioms Lime.Cal.q4
#print axioms Lime.Cal.q100
#print axioms Lime.Cal.q400
#print axioms Lime.Cal.isLeap_arith
#print axioms Lime.Cal.yearLen_as_if
#print axioms Lime.Cal.ys_step
#print axioms Lime.Cal.yearLen_bounds
#print axioms Lime.Cal.ys_succ_bounds
#print axioms Lime.Cal.ys_mono
#print axioms Lime.Cal.ys_le
#print axioms Lime.Cal.ys_ge
#print axioms Lime.Cal.yoe_bracket
#print axioms Lime.Cal.yearOfZ_bracket
#print axioms Lime.Cal.yearOfZ_unique
#print axioms Lime.Cal.yearOfZ_mono
#print axioms Lime.Cal.md_of_doy_common
#print axioms Lime.Cal.md_of_doy_leap
#print axioms Lime.Cal.doy_of_md_common
#print axioms Lime.Cal.doy_of_md_leap
#print axioms Lime.Cal.cumBefore_mono_common
#print axioms Lime.Cal.cumBefore_mono_leap
#print axioms Lime.Cal.monthLen_le_31_common
#print axioms Lime.Cal.monthLen_le_31_leap
#print axioms Lime.Cal.cumBefore_mono
#print axioms Lime.Cal.monthLen_le_31
#print axioms Lime.Cal.md_of_doy
#print axioms Lime.Cal.doy_of_md
#print axioms Lime.Cal.month_bracket
#print axioms Lime.Cal.monthOfDoy_mono
#print axioms Lime.Cal.valid_iff
#print axioms Lime.Cal.ofDay_year
#print axioms Lime.Cal.ofDay_month
#print axioms Lime.Cal.doy_in_range
#print axioms Lime.Cal.yearOfZ_ge_one
#print axioms Lime.Cal.ofDay_valid
#print axioms Lime.Cal.toDay_ofDay
#print axioms Lime.Cal.zOf_bracket
#print axioms Lime.Cal.originShift_le_zOf
#print axioms Lime.Cal.ofDay_toDay
#print axioms Lime.Cal.dayOf_dateOf
#print axioms Lime.Cal.dateOf_dayOf
#print axioms Lime.Cal.toDay_lt_of_year_lt
#print axioms Lime.Cal.leap_2000
#print axioms Lime.Cal.leap_1900
#print axioms Lime.Cal.leap_2024
#print axioms Lime.Cal.leap_2026
#print axioms Lime.Cal.feb_2024_has_29
#print axioms Lime.Cal.feb_1900_has_28
#print axioms Lime.Cal.feb_30_is_not_a_date
#print axioms Lime.Cal.feb_29_2024_is_a_date
#print axioms Lime.Cal.feb_29_2023_is_not_a_date
#print axioms Lime.Cal.month_13_is_not_a_date
#print axioms Lime.Cal.month_0_is_not_a_date
#print axioms Lime.Cal.year_0_is_not_a_date
#print axioms Lime.Cal.unixEpoch_eq
#print axioms Lime.Cal.after_feb28_2024
#print axioms Lime.Cal.after_feb28_2023
#print axioms Lime.Cal.year_2024_is_366
#print axioms Lime.Cal.year_1900_is_365
#print axioms Lime.Cal.year_2000_is_366
#print axioms Lime.Cal.weekday_origin
#print axioms Lime.Cal.weekday_1970_01_01
#print axioms Lime.Cal.weekday_2000_01_01
#print axioms Lime.Cal.weekday_2026_09_07
#print axioms Lime.Cal.weekdayOf_thursday_iff
#print axioms Lime.Cal.weekdayOf_wednesday_iff
#print axioms Lime.Cal.thursdayOf_is_thursday
#print axioms Lime.Cal.thursdayOf_in_week
#print axioms Lime.Cal.weekOrdinal_mono
#print axioms Lime.Cal.weekOrdinal_eq_iff
#print axioms Lime.Cal.jan1_shift
#print axioms Lime.Cal.jan1_step
#print axioms Lime.Cal.jan1_toDay
#print axioms Lime.Cal.isoOf_year
#print axioms Lime.Cal.isoOf_week
#print axioms Lime.Cal.isoOf_weekday
#print axioms Lime.Cal.isoOf_year_bracket
#print axioms Lime.Cal.isoOf_weekday_range
#print axioms Lime.Cal.isoOf_week_range
#print axioms Lime.Cal.isoWeeksIn_52_or_53
#print axioms Lime.Cal.isoWeeksIn_53_iff
#print axioms Lime.Cal.isoWeek1Monday_bracket
#print axioms Lime.Cal.dayOfIso_isoOf
#print axioms Lime.Cal.isoOf_dayOfIso
#print axioms Lime.Cal.iso_2026_09_07
#print axioms Lime.Cal.iso_2026_has_53_weeks
#print axioms Lime.Cal.iso_2027_01_01
#print axioms Lime.Cal.iso_2025_12_29
#print axioms Lime.Cal.iso_2020_has_53_weeks
#print axioms Lime.Cal.iso_2019_has_52_weeks
#print axioms Lime.Cal.iso_2021_01_01
#print axioms Lime.Cal.iso_year_can_differ_from_civil_year
#print axioms Lime.Cal.monthOrdinal_origin
#print axioms Lime.Cal.monthOrdinal_mono
#print axioms Lime.Cal.monthOrdinal_2026_09
#print axioms Lime.Cal.a_week_can_straddle_two_civil_months
#print axioms Lime.Cal.monthOfWeekByToday_is_not_stable
#print axioms Lime.Cal.monthOfIsoWeek_is_met
#print axioms Lime.Cal.monthOfIsoWeek_mono
#print axioms Lime.Cal.monthOfIsoWeek_W36
#print axioms Lime.Cal.monthOfIsoWeek_W35

-- Cmd.lean
#print axioms Lime.lift_roundtrips
#print axioms Lime.resolveDest_ix
#print axioms Lime.mapAt_get
#print axioms Lime.entityInRange_of_mem
#print axioms Lime.sitesInRange_set
#print axioms Lime.demotionsOriented_set
#print axioms Lime.settled_absorbing
#print axioms Lime.readopt_clears_archive
#print axioms Lime.readopt_keeps_stamps
#print axioms Lime.demote_stamps
#print axioms Lime.transform_state_none

-- Grain.lean
#print axioms Lime.coarsen_day
#print axioms Lime.coarsen_week
#print axioms Lime.coarsen_is_up
#print axioms Lime.index_day
#print axioms Lime.index_week
#print axioms Lime.index_month
#print axioms Lime.index_mono
#print axioms Lime.regionOf_is_open
#print axioms Lime.closed_is_stable_in_time
#print axioms Lime.epoch_day_6_is_a_sunday
#print axioms Lime.epoch_day_7_is_a_monday
#print axioms Lime.impl_rule_disagrees_iff
#print axioms Lime.containing_targets_a_closed_region_iff
#print axioms Lime.impl_day_rule_disagrees_2026
#print axioms Lime.containing_can_target_a_closed_region_2026
#print axioms Lime.day_refines_week
#print axioms Lime.week_does_not_refine_month
#print axioms Lime.monthOfWeek_is_met
#print axioms Lime.monthOfWeek_mono
#print axioms Lime.closeTo_week_is_not_monthOfWeek
#print axioms Lime.horizonPrecedes_iff
#print axioms Lime.horizonPrecedes_irrefl

-- Line.lean
#print axioms Lime.ofChar_char
#print axioms Lime.head_cons_tail
#print axioms Lime.rawFor_eq_raw
#print axioms Lime.unitValue_estWord
#print axioms Lime.isEstKey_estWord
#print axioms Lime.find_setEstIn
#print axioms Lime.find_insertBeforeId
#print axioms Lime.tok_wf_iff
#print axioms Lime.estWord_ne_nil
#print axioms Lime.estWord_no_space
#print axioms Lime.estWord_not_id
#print axioms Lime.est_tok_wf
#print axioms Lime.toksWf_head_sep
#print axioms Lime.insertBeforeId_head
#print axioms Lime.toksWf_insertBeforeId
#print axioms Lime.toksWf_setEstIn
#print axioms Lime.idWords_insertBeforeId
#print axioms Lime.estKey_not_id
#print axioms Lime.idWords_setEstIn
#print axioms Lime.canonical_iff

-- Plan.lean
#print axioms Lime.filter_flatMap
#print axioms Lime.render_filter_other
#print axioms Lime.render_filter_self
#print axioms Lime.flatMap_of_all_empty
#print axioms Lime.sum_over_nodup_one_key
#print axioms Lime.itemsWf_parts
#print axioms Lime.itemsWf_of_parts
#print axioms Lime.planWf_parts
#print axioms Lime.planWf_of_parts
#print axioms Lime.docsWf_store
#print axioms Lime.pathsDistinct_store
#print axioms Lime.render_site
#print axioms Lime.lines_mem
#print axioms Lime.weave_nil_right
#print axioms Lime.weave_item_first
#print axioms Lime.weave_prose_first
#print axioms Lime.splitDoc_prose_ge
#print axioms Lime.splitDoc_items_ge
#print axioms Lime.anc_zero
#print axioms Lime.anc_succ_none
#print axioms Lime.anc_succ_some
#print axioms Lime.anc_none_mono
#print axioms Lime.anc_none_add
#print axioms Lime.chainOf_succ_none
#print axioms Lime.chainOf_succ_some
#print axioms Lime.chainOf_length
#print axioms Lime.chainOf_mem_dom
#print axioms Lime.chainOf_mem_anc
#print axioms Lime.peelN_nil
#print axioms Lime.peel_eq_or_lt
#print axioms Lime.deadlocked_survives_peel
#print axioms Lime.deadlocked_survives_peelN
#print axioms Lime.nodup_map_inj
#print axioms Lime.WfPlan
#print axioms Lime.climb_succ_none
#print axioms Lime.climb_succ_some
#print axioms Lime.shapeWf_of_mem

-- State.lean
#print axioms Lime.clock_accepts_2330
#print axioms Lime.dedupTags_mem
#print axioms Lime.dedupTags_nodup
#print axioms Lime.wfPair_none
#print axioms Lime.wfPair_some
#print axioms Lime.wf_eq
#print axioms Lime.render_le_two
#print axioms Lime.render_all_same_id

-- Text.lean
#print axioms Lime.glyph_roundtrip
#print axioms Lime.digit_roundtrip
#print axioms Lime.digitsOf_ne_nil
#print axioms Lime.digitsOf_all_digits
#print axioms Lime.readNatAux_of_digits
#print axioms Lime.natStep_digitsOf
#print axioms Lime.toTok_raw
#print axioms Lime.chunk_flatten
#print axioms Lime.group_flatten
#print axioms Lime.takeWhile_append_all
#print axioms Lime.chunk_head
#print axioms Lime.chunk_merge
#print axioms Lime.group_head
#print axioms Lime.group_word
#print axioms Lime.group_sep
#print axioms Lime.toTok_of_wf
#print axioms Lime.group_tok

-- ==========================================================================
-- APPENDED after stage 2 and the field wiring.
-- ==========================================================================

-- Arith.lean

-- Boundary.lean
#print axioms Lime.sortByRank_nil
#print axioms Lime.sortByRank_cons
#print axioms Lime.insertByRank_mem
#print axioms Lime.sortByRank_mem
#print axioms Lime.insertByRank_sorted
#print axioms Lime.sortByRank_sorted
#print axioms Lime.insertByRank_distinct
#print axioms Lime.sortByRank_distinct
#print axioms Lime.sortByRank_id
#print axioms Lime.sortByRank_strict
#print axioms Lime.mem_placementsOfDoc
#print axioms Lime.mem_placementsOf
#print axioms Lime.buildEntities_fold
#print axioms Lime.buildEntities_spec
#print axioms Lime.loadStore_fold_not_mem
#print axioms Lime.loadStore_fold_mem
#print axioms Lime.loadStore_fold_some
#print axioms Lime.loadStore_get_of_mem
#print axioms Lime.loadStore_get_some
#print axioms Lime.mem_lines_of_render
#print axioms Lime.loneEntity_archive
#print axioms Lime.buildEntity_renders
#print axioms Lime.loadCore_docsWf
#print axioms Lime.loadCore_lines_mem
#print axioms Lime.placements_of_doc
#print axioms Lime.renderDocAt_loadCore
#print axioms Lime.loadPlan_spec
#print axioms Lime.loadPlan_docs
#print axioms Lime.the_kernel_reads_back_what_it_writes
#print axioms Lime.renderDocAt_untouched
#print axioms Lime.mapAt_ok_shape
#print axioms Lime.a_command_rewrites_only_the_files_it_touches
#print axioms Lime.foldl_max_ge_gen
#print axioms Lime.le_foldl_max_gen
#print axioms Lime.docProseMax_ge
#print axioms Lime.archive_line_mem
#print axioms Lime.live_line_site_mem
#print axioms Lime.normalized_of_fresh_or_old
#print axioms Lime.normalized_after_relocation
#print axioms Lime.normalized_after_edit
#print axioms Lime.move_at_freshRank_normalized
#print axioms Lime.moveTo_freshRank_normalized
#print axioms Lime.demote_at_freshRank_normalized
#print axioms Lime.readopt_at_freshRank_normalized
#print axioms Lime.drop_normalized
#print axioms Lime.setEst_normalized
#print axioms Lime.itemsWf_of_normalized
#print axioms Lime.applyCmd_move_succeeds
#print axioms Lime.runPlan_renders_the_input
#print axioms Lime.the_round_trip_is_not_vacuous
#print axioms Lime.the_round_trip_fires
#print axioms Lime.the_spec_demotion_pair_loads
#print axioms Lime.the_spec_pair_is_one_entity_with_a_tombstone
#print axioms Lime.the_spec_pair_puts_the_tombstone_in_the_month
#print axioms Lime.the_spec_demotion_pair_round_trips

-- Cmd.lean

-- Line.lean
#print axioms Lime.Field.isDigitC_cases
#print axioms Lime.Field.upper_not_lower
#print axioms Lime.Field.upper_not_digit
#print axioms Lime.Field.digit_not_lower
#print axioms Lime.Field.digit_not_upper
#print axioms Lime.Field.isName_all
#print axioms Lime.Field.isName_ne_nil
#print axioms Lime.Field.isNameC_ne
#print axioms Lime.Field.isName_avoids
#print axioms Lime.Field.isName_no_space
#print axioms Lime.Field.cap_is_an_alias_of_max
#print axioms Lime.Field.cap_writes_as_max
#print axioms Lime.Field.key_name_roundtrip
#print axioms Lime.Field.key_name_isKey
#print axioms Lime.Field.key_name_ne_nil
#print axioms Lime.Field.key_name_avoids
#print axioms Lime.Field.flag_name_roundtrip
#print axioms Lime.Field.flag_name_ne_nil
#print axioms Lime.Field.flag_name_no_space
#print axioms Lime.Field.flag_name_no_colon
#print axioms Lime.Field.digitsOf_isDigitC
#print axioms Lime.Field.hmOf_concat
#print axioms Lime.Field.parse_render_dur
#print axioms Lime.Field.parse_render_durND
#print axioms Lime.Field.renderDur_ne_nil
#print axioms Lime.Field.renderDur_chars
#print axioms Lime.Field.renderDur_head_digit
#print axioms Lime.Field.clock_rejects_2500
#print axioms Lime.Field.clock_rejects_minute_60
#print axioms Lime.Field.clock_rejects_unpadded
#print axioms Lime.Field.clock_reads_1130
#print axioms Lime.Field.padTo2_length
#print axioms Lime.Field.padTo_digits
#print axioms Lime.Field.padTo_no_colon
#print axioms Lime.Field.parse_render_clock
#print axioms Lime.Field.renderClock_length
#print axioms Lime.Field.renderClock_chars
#print axioms Lime.Field.renderClock_head_digit
#print axioms Lime.Field.ofDay_month_bounds
#print axioms Lime.Field.ofDay_day_bounds
#print axioms Lime.Field.padTo4_length
#print axioms Lime.Field.padTo_not_char
#print axioms Lime.Field.date_rejects_feb30
#print axioms Lime.Field.date_accepts_feb29_2024
#print axioms Lime.Field.date_rejects_unpadded
#print axioms Lime.Field.date_rejects_year_zero
#print axioms Lime.Field.parse_render_date
#print axioms Lime.Field.renderDate_chars
#print axioms Lime.Field.renderDate_avoid
#print axioms Lime.Field.renderDate_head_digit
#print axioms Lime.Field.renderDT_chars
#print axioms Lime.Field.renderDT_avoid
#print axioms Lime.Field.parse_render_DT
#print axioms Lime.Field.parseDT_clock_none
#print axioms Lime.Field.parse_render_moment
#print axioms Lime.Field.moment_date_form
#print axioms Lime.Field.moment_datetime_form
#print axioms Lime.Field.parse_render_interval
#print axioms Lime.Field.renderClock_no_slash
#print axioms Lime.Field.renderClock_no_dash
#print axioms Lime.Field.parse_render_window
#print axioms Lime.Field.overnight_window_roundtrips
#print axioms Lime.Field.pref_bare_wake
#print axioms Lime.Field.parse_render_pref
#print axioms Lime.Field.mapOpt_map
#print axioms Lime.Field.headSat_ne
#print axioms Lime.Field.headSat_cons
#print axioms Lime.Field.headSat_append
#print axioms Lime.Field.headSat_digitsOf
#print axioms Lime.Field.headSat_false_of
#print axioms Lime.Field.headSat_not
#print axioms Lime.Field.parse_render_weekday
#print axioms Lime.Field.renderWeekday_no_comma
#print axioms Lime.Field.headSat_renderWeekday
#print axioms Lime.Field.rule_day
#print axioms Lime.Field.rule_weekday
#print axioms Lime.Field.rule_mwf
#print axioms Lime.Field.rule_2w_sun
#print axioms Lime.Field.rule_3d
#print axioms Lime.Field.rule_month_15
#print axioms Lime.Field.rule_week
#print axioms Lime.Field.rule_month_0_rejected
#print axioms Lime.Field.rule_month_32_rejected
#print axioms Lime.Field.rule_0d_rejected
#print axioms Lime.Field.renderRule_not_literal
#print axioms Lime.Field.parse_render_rule
#print axioms Lime.Field.renderDur_no
#print axioms Lime.Field.parse_render_afterDone
#print axioms Lime.Field.parse_render_onEvent
#print axioms Lime.Field.parse_render_onMiss
#print axioms Lime.Field.parse_render_period
#print axioms Lime.Field.parse_render_rate
#print axioms Lime.Field.rate_6b_w
#print axioms Lime.Field.rate_4h_w
#print axioms Lime.Field.rate_2b_d
#print axioms Lime.Field.parse_render_dep
#print axioms Lime.Field.eventPrefix_no_comma
#print axioms Lime.Field.renderDep_no_comma
#print axioms Lime.Field.parse_render_deps
#print axioms Lime.Field.deps_mixed
#print axioms Lime.Field.parse_render_loc
#print axioms Lime.Field.parse_render_stamp
#print axioms Lime.Field.renderStamp_no_comma
#print axioms Lime.Field.parse_render_stamps
#print axioms Lime.Field.stamps_W36_W37
#print axioms Lime.Field.readNat_single
#print axioms Lime.Field.parse_render_ci
#print axioms Lime.Field.ci_rejects_6
#print axioms Lime.Field.ci_rejects_9
#print axioms Lime.Field.parse_render_prio
#print axioms Lime.Field.prio_rejects_5
#print axioms Lime.Field.prio_rejects_0
#print axioms Lime.Field.prio_reads_1
#print axioms Lime.Field.keyPrefix_head
#print axioms Lime.Field.sigilOf_head
#print axioms Lime.Field.sigil_not_key
#print axioms Lime.Field.sigil_not_digit
#print axioms Lime.Field.digit_not_key
#print axioms Lime.Field.keyPrefix_none_of
#print axioms Lime.Field.sigilOf_none_of
#print axioms Lime.Field.estSlot_head
#print axioms Lime.Field.ciSlot_head
#print axioms Lime.Field.startsToken_not_digit
#print axioms Lime.Field.estSlot_none_of_startsToken
#print axioms Lime.Field.ciSlot_none_of_startsToken
#print axioms Lime.Field.filterMap_cons_none'
#print axioms Lime.Field.filterMap_cons_some'
#print axioms Lime.Field.extract_phase3
#print axioms Lime.Field.extract_phase2
#print axioms Lime.Field.extract_phase1
#print axioms Lime.Field.extract_phase0
#print axioms Lime.Field.classifyPhase3_append
#print axioms Lime.Field.classifyPhase2_suffix
#print axioms Lime.Field.classifyPhase1_suffix
#print axioms Lime.Field.classifyPhase0_suffix
#print axioms Lime.Field.shape_at_wins
#print axioms Lime.Field.shape_win_needs_dur
#print axioms Lime.Field.shape_due_is_last
#print axioms Lime.Field.recur_every_wins
#print axioms Lime.Field.recur_afterDone_beats_onEvent
#print axioms Lime.Field.unparsed_sub_title
#print axioms Lime.Field.unclassified_token_stays_in_the_title
#print axioms Lime.Field.extra_sub_problems
#print axioms Lime.Field.unknown_key_is_reported
#print axioms Lime.Field.classifySigil_ne_extra
#print axioms Lime.Field.classifyPlain_ne_extra
#print axioms Lime.Field.kpOne_classifyBang
#print axioms Lime.Field.kpOne_classifySigil
#print axioms Lime.Field.kpOne_classifyPlain
#print axioms Lime.Field.keyValue_isSome
#print axioms Lime.Field.kpOne_classifyWord
#print axioms Lime.Field.extra_key_is_unknown
#print axioms Lime.Field.rawKeyPair_none_of_keyPrefix
#print axioms Lime.Field.rawKeyPair_none_of_digit
#print axioms Lime.Field.rawKeyPair_none_of_notStarts
#print axioms Lime.Field.keyPairs_raw
#print axioms Lime.Field.wordWf_iff
#print axioms Lime.Field.keyPrefix_keyWord
#print axioms Lime.Field.keyValue_keyWord
#print axioms Lime.Field.keyOf_keyWord
#print axioms Lime.Field.rawKeyPair_keyWord
#print axioms Lime.Field.keyWord_wordWf
#print axioms Lime.Field.keyWord_not_id
#print axioms Lime.Field.setKeyIn_cons_pos
#print axioms Lime.Field.setKeyIn_cons_neg
#print axioms Lime.Field.insertBeforeId_nil
#print axioms Lime.Field.insertBeforeId_id_nosep
#print axioms Lime.Field.insertBeforeId_id_sep
#print axioms Lime.Field.insertBeforeId_other
#print axioms Lime.Field.rawKeyPair_key
#print axioms Lime.Field.lookup_cons_ne
#print axioms Lime.Field.lookup_cons_self
#print axioms Lime.Field.lookup_cons_skip
#print axioms Lime.Field.lookup_setKeyIn
#print axioms Lime.Field.lookup_insertBeforeId
#print axioms Lime.Field.lookupKey_setKey
#print axioms Lime.Field.lookup_filter_none
#print axioms Lime.Field.lookupKey_unsetKey
#print axioms Lime.Field.view_set_due
#print axioms Lime.Field.view_set_at
#print axioms Lime.Field.view_set_win
#print axioms Lime.Field.view_set_dur
#print axioms Lime.Field.view_set_pref
#print axioms Lime.Field.view_set_every
#print axioms Lime.Field.view_set_afterDone
#print axioms Lime.Field.view_set_onEvent
#print axioms Lime.Field.view_set_onMiss
#print axioms Lime.Field.view_set_min
#print axioms Lime.Field.view_set_max
#print axioms Lime.Field.view_set_after
#print axioms Lime.Field.view_set_loc
#print axioms Lime.Field.view_set_estKey
#print axioms Lime.Field.view_set_demoted
#print axioms Lime.Field.view_set_waiting
#print axioms Lime.Field.view_set_buffer
#print axioms Lime.Field.view_set_ciKey
#print axioms Lime.Field.view_set_remaining
#print axioms Lime.Field.view_set_ci
#print axioms Lime.Field.est_key_beats_lead
#print axioms Lime.Field.ci_key_beats_positional
#print axioms Lime.Field.est_key_overrides_the_leading_estimate
#print axioms Lime.Field.unset_ci_key_leaves_the_positional_digit
#print axioms Lime.Field.set_max_writes_max
#print axioms Lime.Field.tok_wf_of_wordWf
#print axioms Lime.Field.toksWf_setKeyIn
#print axioms Lime.Field.toksWf_insertBeforeId_gen
#print axioms Lime.Field.idWords_setKeyIn
#print axioms Lime.Field.idWords_insertBeforeId_gen
#print axioms Lime.Field.setKey_canonical_box_ended
#print axioms Lime.Field.setKey_line_reparses
#print axioms Lime.Field.isIdWord_startsToken
#print axioms Lime.Field.classifyWord_flag
#print axioms Lime.Field.insertAfterId_shape
#print axioms Lime.Field.view_set_flag
#print axioms Lime.Field.insertAfterId_none
#print axioms Lime.Field.setFlag_needs_a_boundary
#print axioms Lime.Field.filterMap_map_none'
#print axioms Lime.Field.filterMap_map_id'
#print axioms Lime.Field.filterMap_opt_none
#print axioms Lime.Field.rawKeyPair_tokOf_sigil
#print axioms Lime.Field.sigilOf_cons
#print axioms Lime.Field.rawKeyPair_at
#print axioms Lime.Field.rawKeyPair_hash
#print axioms Lime.Field.rawKeyPair_caret
#print axioms Lime.Field.rawKeyPair_prio
#print axioms Lime.Field.renderCi_head
#print axioms Lime.Field.rawKeyPair_ci
#print axioms Lime.Field.renderDur_headSat
#print axioms Lime.Field.rawKeyPair_estWordD
#print axioms Lime.Field.keyPrefix_flag
#print axioms Lime.Field.rawKeyPair_flag
#print axioms Lime.Field.keyPrefix_extra
#print axioms Lime.Field.rawKeyPair_extra
#print axioms Lime.Field.filterMap_map_none_mem
#print axioms Lime.Field.classifyWord_unparsed_sigil
#print axioms Lime.Field.rawKeyPair_unparsed
#print axioms Lime.Field.keyPairs_render
#print axioms Lime.Field.lookup_pair_self
#print axioms Lime.Field.lookup_pair_ne
#print axioms Lime.Field.lookup_filterMap_notMem
#print axioms Lime.Field.lookup_filterMap_pairs
#print axioms Lime.Field.kvList_keys
#print axioms Lime.Field.kvList_nodup
#print axioms Lime.Field.lookupKey_render
#print axioms Lime.Field.bind_map_render
#print axioms Lime.Field.optWf_some
#print axioms Lime.Field.kv_due
#print axioms Lime.Field.kv_interval
#print axioms Lime.Field.kv_window
#print axioms Lime.Field.kv_dur
#print axioms Lime.Field.kv_pref
#print axioms Lime.Field.kv_every
#print axioms Lime.Field.kv_afterDone
#print axioms Lime.Field.kv_onEvent
#print axioms Lime.Field.kv_onMiss
#print axioms Lime.Field.kv_floor
#print axioms Lime.Field.kv_cap
#print axioms Lime.Field.kv_after
#print axioms Lime.Field.kv_loc
#print axioms Lime.Field.kv_est
#print axioms Lime.Field.kv_demoted
#print axioms Lime.Field.kv_waiting
#print axioms Lime.Field.kv_buffer
#print axioms Lime.Field.kv_ci
#print axioms Lime.Field.view_render_due
#print axioms Lime.Field.view_render_interval
#print axioms Lime.Field.view_render_window
#print axioms Lime.Field.view_render_dur
#print axioms Lime.Field.view_render_pref
#print axioms Lime.Field.view_render_every
#print axioms Lime.Field.view_render_afterDone
#print axioms Lime.Field.view_render_onEvent
#print axioms Lime.Field.view_render_onMiss
#print axioms Lime.Field.view_render_floor
#print axioms Lime.Field.view_render_cap
#print axioms Lime.Field.view_render_after
#print axioms Lime.Field.view_render_loc
#print axioms Lime.Field.view_render_est
#print axioms Lime.Field.view_render_demoted
#print axioms Lime.Field.view_render_waiting
#print axioms Lime.Field.view_render_buffer
#print axioms Lime.Field.view_render_ci
#print axioms Lime.Field.filterMapMapNone
#print axioms Lime.Field.filterMapMapSome
#print axioms Lime.Field.filterMapOptNone
#print axioms Lime.Field.filterMapOptSome
#print axioms Lime.Field.findSome_append
#print axioms Lime.Field.findSomeMapNone
#print axioms Lime.Field.findSomeOptNone
#print axioms Lime.Field.findSomeOptSome
#print axioms Lime.Field.classifyPhase3_map
#print axioms Lime.Field.classifyPhase2_title
#print axioms Lime.Field.classifyPhase1_of_noEst
#print axioms Lime.Field.classifyPhase0_of_noCi
#print axioms Lime.Field.ciSlot_renderCi
#print axioms Lime.Field.estSlot_renderDur
#print axioms Lime.Field.ciSlot_none_of_len
#print axioms Lime.Field.renderDur_length
#print axioms Lime.Field.ciSlot_renderDur
#print axioms Lime.Field.ciSlot_caret
#print axioms Lime.Field.estSlot_caret
#print axioms Lime.Field.startsToken_caret
#print axioms Lime.Field.key_not_sigil
#print axioms Lime.Field.sigilOf_keyed
#print axioms Lime.Field.classifyWord_id
#print axioms Lime.Field.classifyWord_parent
#print axioms Lime.Field.classifyWord_tag
#print axioms Lime.Field.classifyWord_prio
#print axioms Lime.Field.classifyWord_key
#print axioms Lime.Field.classifyWord_extra
#print axioms Lime.Field.map_map'
#print axioms Lime.Field.map_congr'
#print axioms Lime.Field.mapOpt_toList
#print axioms Lime.Field.optMap_congr
#print axioms Lime.Field.midToks_kinds
#print axioms Lime.Field.slotGuard_est
#print axioms Lime.Field.slotGuard_ci
#print axioms Lime.Field.head_title_mid
#print axioms Lime.Field.kinds_render
#print axioms Lime.Field.findSome_cons_none
#print axioms Lime.Field.orElse_none
#print axioms Lime.Field.view_render_title
#print axioms Lime.Field.view_render_unparsed
#print axioms Lime.Field.view_render_tags
#print axioms Lime.Field.view_render_flags
#print axioms Lime.Field.view_render_extra
#print axioms Lime.Field.view_render_parent
#print axioms Lime.Field.view_render_prio
#print axioms Lime.Field.view_render_ciSlot
#print axioms Lime.Field.view_render_estLead
#print axioms Lime.Field.view_render_id
#print axioms Lime.Field.field_round_trip
#print axioms Lime.Field.title_absorbs_the_unclassified
#print axioms Lime.spec_line_is_an_item
#print axioms Lime.Field.spec_line_ci
#print axioms Lime.Field.spec_line_leading_estimate
#print axioms Lime.Field.spec_line_remaining
#print axioms Lime.Field.spec_line_title
#print axioms Lime.Field.spec_line_parent
#print axioms Lime.Field.spec_line_tags
#print axioms Lime.Field.spec_line_due
#print axioms Lime.Field.spec_line_max
#print axioms Lime.Field.spec_line_id
#print axioms Lime.Field.spec_line_no_problems
#print axioms Lime.Field.spec_line_bytes
#print axioms Lime.Field.junk_extra_keys
#print axioms Lime.Field.junk_problems
#print axioms Lime.Field.junk_title
#print axioms Lime.Field.junk_bytes
#print axioms Lime.Field.flag_word_in_the_title_is_title_text
#print axioms Lime.Field.flag_word_after_the_id_is_a_flag
#print axioms Lime.Field.renderToks_words
#print axioms Lime.Field.toksWf_tokOf
#print axioms Lime.Field.wordWf_cons
#print axioms Lime.Field.wordWf_singleton
#print axioms Lime.Field.digitChar_not_space
#print axioms Lime.Field.wordWf_renderCi
#print axioms Lime.Field.wordWf_renderDur
#print axioms Lime.Field.wordWf_renderPrio
#print axioms Lime.Field.wordWf_flag
#print axioms Lime.Field.wordWf_isName
#print axioms Lime.Field.wordWf_caret
#print axioms Lime.Field.isIdWord_false_of_head
#print axioms Lime.Field.isIdWord_false_of_notStarts
#print axioms Lime.Field.isIdWord_false_cons
#print axioms Lime.Field.filter_map'
#print axioms Lime.Field.filterMapNoneList
#print axioms Lime.Field.filterOptNoneList
#print axioms Lime.Field.filter_map_gen
#print axioms Lime.Field.forall_mem_append'
#print axioms Lime.Field.forall_mem_cons'
#print axioms Lime.Field.forall_mem_map'
#print axioms Lime.Field.forall_mem_optToList'
#print axioms Lime.Field.filter_isIdWord_title
#print axioms Lime.Field.filter_isIdWord_words
#print axioms Lime.Field.headSat_keyWord
#print axioms Lime.Field.headSat_flag
#print axioms Lime.Field.renderWords_wordWf
#print axioms Lime.Field.filter_isIdWord_render
#print axioms Lime.Field.idToks_render
#print axioms Lime.Field.renderItem_canonical_box_ended
#print axioms Lime.Field.render_round_trip
#print axioms Lime.Field.demo_wf
#print axioms Lime.Field.demo_round_trips
#print axioms Lime.Field.demo_line_reparses
#print axioms Lime.Field.demo_line_bytes
#print axioms Lime.Field.row_due_date
#print axioms Lime.Field.row_due_datetime
#print axioms Lime.Field.row_at_same_day
#print axioms Lime.Field.row_at_cross_day
#print axioms Lime.Field.row_at_rolls_past_midnight
#print axioms Lime.Field.row_win_daily
#print axioms Lime.Field.row_win_absolute
#print axioms Lime.Field.row_dur_30m
#print axioms Lime.Field.row_dur_1h
#print axioms Lime.Field.row_dur_hours_minutes
#print axioms Lime.Field.row_pref_wake_plus
#print axioms Lime.Field.row_pref_clock
#print axioms Lime.Field.row_every_day
#print axioms Lime.Field.row_every_weekday
#print axioms Lime.Field.row_every_mwf
#print axioms Lime.Field.row_every_2w_sun
#print axioms Lime.Field.row_every_3d
#print axioms Lime.Field.row_every_month_15
#print axioms Lime.Field.row_every_week
#print axioms Lime.Field.row_after_done_offset
#print axioms Lime.Field.row_after_done_window
#print axioms Lime.Field.row_on_event_bare
#print axioms Lime.Field.row_on_event_timeout
#print axioms Lime.Field.row_on_miss_expire
#print axioms Lime.Field.row_on_miss_persist
#print axioms Lime.Field.row_on_miss_next
#print axioms Lime.Field.row_min_6b_w
#print axioms Lime.Field.row_max_2b_d
#print axioms Lime.Field.row_cap_4h_w
#print axioms Lime.Field.row_after_ids
#print axioms Lime.Field.row_after_event
#print axioms Lime.Field.row_loc_lounge
#print axioms Lime.Field.row_loc_named
#print axioms Lime.Field.row_est_1b
#print axioms Lime.Field.row_demoted_stamps
#print axioms Lime.Field.row_waiting_date
#print axioms Lime.Field.row_buffer_2h
#print axioms Lime.Field.row_ci_key
#print axioms Lime.Field.row_flags
#print axioms Lime.Field.intervalWf_is_satisfiable
#print axioms Lime.Field.the_two_est_setters_write_the_same_token
#print axioms Lime.Field.toksWf_head_wf
#print axioms Lime.Field.toksWf_tail
#print axioms Lime.Field.toksWf_seps
#print axioms Lime.Field.toksWf_filter
#print axioms Lime.Field.isKeyTok_false_of_isIdWord
#print axioms Lime.Field.idWords_filter_notKey
#print axioms Lime.Field.unsetKey_canonical_box_ended
#print axioms Lime.Field.unsetKey_line_reparses
#print axioms Lime.Field.setFlag_on_the_spec_line

-- Plan.lean
#print axioms Lime.splitDoc_nil
#print axioms Lime.splitDoc_cons_ok
#print axioms Lime.splitDoc_cons_error
#print axioms Lime.sorted_ext_by_key
#print axioms Lime.splitDoc_prose_sorted
#print axioms Lime.splitDoc_items_sorted
#print axioms Lime.pairwise_lt_of_le_ne
#print axioms Lime.pairwise_ne_of_nodup_keys
#print axioms Lime.flatMap_congr
#print axioms Lime.site_eq
#print axioms Lime.lines_set
#print axioms Lime.docRanks_eq
#print axioms Lime.ranksIn_append
#print axioms Lime.mem_ranksIn
#print axioms Lime.mem_proseRanks
#print axioms Lime.nodup_of_length_le_one
#print axioms Lime.render_filter_doc_len
#print axioms Lime.ranksIn_render_nodup
#print axioms Lime.nodup_swap_middle
#print axioms Lime.normalized_set

-- State.lean
#print axioms Lime.the_fields_are_the_line
#print axioms Lime.coreOfLine_fields
#print axioms Lime.coreOfLine_shape
#print axioms Lime.coreOfLine_recur
#print axioms Lime.coreOfLine_stamps
#print axioms Lime.the_spec_calendar_line_is_an_interval
#print axioms Lime.the_spec_calendar_line_has_a_loc
#print axioms Lime.the_spec_demoted_line_is_read_whole
#print axioms Lime.the_spec_item_line_is_read_whole
#print axioms Lime.core_fields_round_trip
#print axioms Lime.a_lone_demotion_renders_back

-- Text.lean
#print axioms Lime.digitsAux_fuel
#print axioms Lime.digitsOf_eq
#print axioms Lime.digitsOf_noSpace
#print axioms Lime.zeros_all_zero
#print axioms Lime.natStep_zeros
#print axioms Lime.zeros_are_digits
#print axioms Lime.readNat_padTo
#print axioms Lime.padTo_ne_nil
#print axioms Lime.padTo_no_space
#print axioms Lime.splitFirst_append
#print axioms Lime.splitFirst_sound
#print axioms Lime.splitOn_ne_nil
#print axioms Lime.splitOn_prepend
#print axioms Lime.splitOn_joinWith
#print axioms Lime.zeros_length
#print axioms Lime.digitsOf_length_le
#print axioms Lime.padTo_length
#print axioms Lime.splitFirst_none
#print axioms Lime.stripPre_append
#print axioms Lime.stripPre_head_ne

-- ==========================================================================
-- Dotted theorem names the earlier generator truncated (Q.le_refl became Q).
-- ==========================================================================
#print axioms Lime.Arith.Q.ok_defined
#print axioms Lime.Arith.Q.le_of
#print axioms Lime.Arith.Q.le_elim
#print axioms Lime.Arith.Q.lt_iff_not_le
#print axioms Lime.Arith.Q.le_refl
#print axioms Lime.Arith.Q.lt_irrefl
#print axioms Lime.Arith.Q.le_total
#print axioms Lime.Arith.Q.le_antisymm
#print axioms Lime.Arith.Q.le_trans
#print axioms Lime.Arith.Q.le_congr_left
#print axioms Lime.Arith.Q.le_congr_right
#print axioms Lime.Arith.Q.equiv_scale
#print axioms Lime.Arith.Q.le_scale_left
#print axioms Lime.Store.insert_get
#print axioms Lime.Store.get_set_self
#print axioms Lime.Store.get_set_other
#print axioms Lime.Store.dom_set
#print axioms Lime.WfPlan.items

-- the two `ofPair?` lemmas the earlier generator cut at the `?`
#print axioms Lime.Arith.ofPair?_zero
#print axioms Lime.Arith.ofPair?_some

-- added by the demotion-orientation revision
#print axioms Lime.demote_ok
#print axioms Lime.readopt_ok
#print axioms Lime.Core.archiveSite_none
#print axioms Lime.Core.archiveSite_some

-- APPENDED 2026-09-09 (stage-3 boundary session)
#print axioms Lime.the_char_edge_round_trips
-- APPENDED 2026-09-09 (stage-3 loader session: gap 16's loader pair)
#print axioms Lime.placement_doc_lt
#print axioms Lime.docRegion_loadCore_placement
#print axioms Lime.siteInRange_loadCore
#print axioms Lime.placement_bounds_pair
#print axioms Lime.entityInRange_loadEntity
#print axioms Lime.demotionOriented_loadEntity
#print axioms Lime.the_loader_builds_sites_in_range
#print axioms Lime.the_loader_builds_oriented_demotions

-- APPENDED 2026-09-09 (stage-3 loader session 2: the normalized third, gap 16 closed)
#print axioms Lime.render_nodup
#print axioms Lime.flatMap_nodup_store
#print axioms Lime.store_lines_nodup
#print axioms Lime.Store.insert_dom
#print axioms Lime.foldl_insert_dom_nodup
#print axioms Lime.slots_nodup_of_nodup
#print axioms Lime.placements_slot_nodup
#print axioms Lime.ranksIn_nodup_lines
#print axioms Lime.getElem?_eq_some_of_lt
#print axioms Lime.splitDoc_prose_nodup
#print axioms Lime.splitDoc_items_nodup
#print axioms Lime.splitDoc_slots_separated
#print axioms Lime.the_loader_builds_a_normalized_plan

-- APPENDED 2026-09-09 (stage-3 rank-verb session)
#print axioms Lime.lift_ok_of_wf
#print axioms Lime.wf_setRank
#print axioms Lime.setRankE_idem
#print axioms Lime.mapAt_at
#print axioms Lime.Store.set_same
#print axioms Lime.planCore_set_same
#print axioms Lime.rank_is_idempotent
#print axioms Lime.rank_preserves_the_order_of_the_others

-- APPENDED 2026-09-09 (stage-3 fresh-id session)
#print axioms Lime.digitsOf_injective
#print axioms Lime.candidates_nodup
#print axioms Lime.add_assigns_a_fresh_id

-- APPENDED 2026-09-10 (stage-3 gap-4 session: the est command path writes what Core.est reads)
#print axioms Lime.the_command_path_writes_what_the_field_path_reads

-- APPENDED 2026-09-10 (stage-3 add session: fresh id, insert, badItem)
#print axioms Lime.Store.get_insertFresh_self
#print axioms Lime.Store.get_insertFresh_other
#print axioms Lime.Store.dom_insertFresh
#print axioms Lime.WfPlan.insertFresh_get
#print axioms Lime.WfPlan.insertFresh_other
#print axioms Lime.WfPlan.insertFresh_rejects
#print axioms Lime.store_get_isNone_of_not_mem
#print axioms Lime.parseCmd_rejects_add_title_variants
#print axioms Lime.cmdAdd_inserts
#print axioms Lime.cmdAdd_rank
#print axioms Lime.cmdAdd_other_untouched

-- APPENDED 2026-09-12 (stage-3 continuation session)
#print axioms Lime.rank_onto_a_taken_rank_is_refused
#print axioms Lime.setRank_sitesFree
#print axioms Lime.cmdRank_succeeds
#print axioms Lime.applyCmd_rank_succeeds
#print axioms Lime.lines_insertFresh
#print axioms Lime.normalized_insertFresh_of_fresh
#print axioms Lime.add_at_freshRank_normalized
#print axioms Lime.sitesInRange_insertFresh
#print axioms Lime.demotionsOriented_insertFresh
#print axioms Lime.cmdAdd_succeeds
#print axioms Lime.the_undo_witness_loads
#print axioms Lime.move_has_no_inverse_command
#print axioms Lime.joinWith_splitOn
#print axioms Lime.a_file_splits_into_the_lines_it_was_joined_from_char
#print axioms Lime.joining_lines_is_not_injective_char

-- (same session, edit-widening block: the keyed edit, gap 32's guard, and
-- the est op routed through it)
#print axioms Lime.ndDur?_is_parseDurND
-- DELETED AT W-35 (track E): setVal_writes_the_token_the_loader_reads said every edit lands
-- its own key's token, which was the hole the owner's D56 closed (README gap 2572); REFUTED as
-- setVal_writes_the_token_the_loader_reads_is_refuted and restated on its subdomain as
-- setVal_writes_the_token_the_loader_reads_unless_it_rewrites_the_leading_estimate (audited below).
#print axioms Lime.editValOf_refuses_unwired_keys
#print axioms Lime.the_nine_wired_keys_accept_their_spec_values
#print axioms Lime.key_of_map
#print axioms Lime.editValOf_key
#print axioms Lime.the_edit_path_writes_what_the_field_path_reads
#print axioms Lime.unset_of_a_key_the_line_does_not_carry_is_refused
#print axioms Lime.unsetE_ok_of_present
#print axioms Lime.the_unset_path_removes_what_the_field_path_reads
#print axioms Lime.the_est_op_is_the_keyed_est_edit
#print axioms Lime.unset_of_an_absent_key_is_refused
#print axioms Lime.applyCmd_edit_succeeds
#print axioms Lime.applyCmd_est_succeeds
#print axioms Lime.applyCmd_unset_succeeds
#print axioms Lime.parseCmd_rejects_edit_variants
#print axioms Lime.parseCmd_reads_the_keyed_edit_forms

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 1: the JSON fragment's
-- foundations).  Every theorem of LimeKernel/Base/Json.lean, in declaration order.
-- Nothing here is on the wire yet -- Boundary.lean still builds Lean.Json --
-- so these audit the replacement, not the crossing.
-- ===========================================================================
#print axioms Lime.jbeq_sound
#print axioms Lime.jbeq_refl
#print axioms Lime.jbeq_iff
#print axioms Lime.jval_objects_keep_their_order
#print axioms Lime.demo_jval_is_decidable
#print axioms Lime.hexDigit_hexChar
#print axioms Lime.hexQuad_escOf
#print axioms Lime.junescape_escOf
#print axioms Lime.junescape_jescape
#print axioms Lime.demo_jescape_bytes
#print axioms Lime.demo_junescape_bytes
#print axioms Lime.the_escaping_is_not_vacuous
#print axioms Lime.the_emitted_escape_classes
#print axioms Lime.jescape_keeps_high_bytes_verbatim
#print axioms Lime.junescape_accepts_the_host_short_escapes
#print axioms Lime.the_accepted_escapes_exceed_the_emitted_ones
#print axioms Lime.junescape_refuses_a_truncated_escape
#print axioms Lime.junescape_refuses_a_truncated_hex_quad
#print axioms Lime.junescape_refuses_a_bad_hex_quad
#print axioms Lime.junescape_refuses_an_unknown_escape
#print axioms Lime.junescape_refuses_a_raw_quote
#print axioms Lime.junescape_refuses_a_raw_control
#print axioms Lime.junescape_refuses_a_lone_surrogate
#print axioms Lime.the_surrogate_guard_is_not_vacuous
#print axioms Lime.jrenderNat_is_digitsOf
#print axioms Lime.jdigits_append
#print axioms Lime.jparseNat_jrenderNat
#print axioms Lime.demo_jparseNat
#print axioms Lime.the_next_byte_guard_bites
#print axioms Lime.the_next_byte_guard_is_satisfiable
#print axioms Lime.jparseNat_refuses_a_non_numeral
#print axioms Lime.jparseNat_reads_a_bare_numeral

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 2: the emitter, the parser and
-- the round trip).  Every theorem LimeKernel/Base/Json.lean gained at J3-J4, in
-- declaration order: jemit, the fuel bound, the scanner, the parser's step
-- equations, jval_jemit / jparse_jemit, the fuel-sufficiency induction ending
-- in jparse_never_runs_out, and the witnesses.  Still not on the wire --
-- Boundary.lean builds Lean.Json until J5.
-- ===========================================================================
#print axioms Lime.one_le_jemitTail
#print axioms Lime.one_le_jemitOTail
#print axioms Lime.jemitTail_le_jemitArr
#print axioms Lime.jemitOTail_le_jemitObj
#print axioms Lime.jfuel_le_jemit
#print axioms Lime.skipWs_cons_of_not_ws
#print axioms Lime.jscan_cons_plain
#print axioms Lime.jscan_cons_esc
#print axioms Lime.hexChar_ne_quote_or_backslash
#print axioms Lime.jscan_escOf
#print axioms Lime.jscan_jescape
#print axioms Lime.jstring_jescape
#print axioms Lime.charDigit_cases
#print axioms Lime.charDigit_not_ws
#print axioms Lime.charDigit_ne_closers
#print axioms Lime.jemit_head
#print axioms Lime.notDigitStart_jemitTail
#print axioms Lime.notDigitStart_jemitOTail
#print axioms Lime.jval_null
#print axioms Lime.jval_true
#print axioms Lime.jval_false
#print axioms Lime.jval_string
#print axioms Lime.jval_lbracket
#print axioms Lime.jval_lbrace
#print axioms Lime.jval_digit
#print axioms Lime.jarr_empty
#print axioms Lime.jarr_value
#print axioms Lime.jarr_of_jemit
#print axioms Lime.jtail_end
#print axioms Lime.jtail_comma
#print axioms Lime.jobj_empty
#print axioms Lime.jobj_pair
#print axioms Lime.jobj_of_jemitPair
#print axioms Lime.jotail_end
#print axioms Lime.jotail_comma
#print axioms Lime.jpair_key
#print axioms Lime.jval_jemit
#print axioms Lime.jparse_jemit
#print axioms Lime.skipWs_length_le
#print axioms Lime.jscan_length
#print axioms Lime.jstring_length
#print axioms Lime.jstring_ne_outOfFuel
#print axioms Lime.jdigits_length
#print axioms Lime.jparseNat_length
#print axioms Lime.jdigits_fst_digits
#print axioms Lime.jparseNat_some_of_digit
#print axioms Lime.jval_consumes_step
#print axioms Lime.jarr_consumes_step
#print axioms Lime.jtail_consumes_step
#print axioms Lime.jobj_consumes_step
#print axioms Lime.jpair_consumes_step
#print axioms Lime.jotail_consumes_step
#print axioms Lime.jparser_consumes
#print axioms Lime.jval_fuel_step
#print axioms Lime.jarr_fuel_step
#print axioms Lime.jtail_fuel_step
#print axioms Lime.jobj_fuel_step
#print axioms Lime.jpair_fuel_step
#print axioms Lime.jotail_fuel_step
#print axioms Lime.jparser_fuel
#print axioms Lime.jparse_never_runs_out
#print axioms Lime.demo_jemit_bytes
#print axioms Lime.the_emitter_keeps_build_order
#print axioms Lime.the_emitter_is_compress_shaped
#print axioms Lime.the_json_round_trip_is_not_vacuous
#print axioms Lime.the_real_request_bytes_round_trip
#print axioms Lime.the_real_response_bytes_round_trip
#print axioms Lime.jparse_accepts_host_whitespace
#print axioms Lime.the_round_trip_survives_duplicate_keys
#print axioms Lime.jparse_refuses_a_leading_zero
#print axioms Lime.jparse_refuses_empty_input
#print axioms Lime.jparse_refuses_an_unterminated_string
#print axioms Lime.jparse_refuses_trailing_garbage
#print axioms Lime.jparse_refuses_a_bad_escape
#print axioms Lime.jparse_refuses_a_raw_control_byte
#print axioms Lime.jparse_refuses_a_trailing_comma
#print axioms Lime.jparse_refuses_an_unterminated_array
#print axioms Lime.jparse_refuses_a_missing_separator
#print axioms Lime.jparse_refuses_a_bare_key
#print axioms Lime.jparse_refuses_a_missing_colon
#print axioms Lime.jparse_refuses_an_unterminated_object
#print axioms Lime.jparse_reads_what_the_fragment_had_no_type_for
#print axioms Lime.jparseWith_refuses_when_the_fuel_runs_out
#print axioms Lime.the_jval_jemit_hypotheses_are_satisfiable
#print axioms Lime.the_jval_jemit_digit_guard_bites

-- ============================================================================
-- APPENDED 2026-09-12 (stage-3, J-route step 3: J5 -- the kernel's own JSON on
-- the wire).  Response side first: Boundary.lean builds every response as a
-- JVal and `call` emits it with `jemit` (key order is now build order).
-- `jescape_eq_jescapeTR` is the @[csimp] twin that keeps a long line off the
-- stack; the other two pin the new byte order at the builders the FFI calls.
-- ============================================================================
#print axioms Lime.jescape_eq_jescapeTR
#print axioms Lime.the_response_shapes_emit_in_build_order
#print axioms Lime.the_bad_line_diagnostic_keys_in_build_order
-- Request side (same banner, second commit): `call` reads with `jparse` and
-- every field through `jget`; no kernel module imports Lean.Data.Json.  The
-- @[csimp] twins keep a long string off the stack on the way in.
-- GOAL DISCHARGED: Goals.lean's `the_json_edge_round_trips` (stated over
-- Lean.Json, unprovable there) is renamed `the_response_call_emits_parses_back`
-- -- the round trip at the exported function -- and deleted from Goals.lean.
#print axioms Lime.junescapeTR_step
#print axioms Lime.junescapeTR_go
#print axioms Lime.junescape_eq_junescapeTR
#print axioms Lime.jscanTR_go
#print axioms Lime.jscan_eq_jscanTR
#print axioms Lime.jget_reads_the_one_pair
#print axioms Lime.jget_refuses_a_duplicate_key
#print axioms Lime.jget_ignores_a_duplicate_it_does_not_read
#print axioms Lime.parseCmd_refuses_a_duplicate_field
#print axioms Lime.run_refuses_cmds_that_are_not_an_array
#print axioms Lime.respond_names_a_parse_refusal
#print axioms Lime.the_response_call_emits_parses_back
#print axioms Lime.call_refuses_the_real_duplicate_id_request

-- ============================================================================
-- APPENDED 2026-09-12 (stage-3, step 4: a comment is prose).  An item line
-- inside <!-- --> is prose: splitDoc reads through commentAfter's state, the
-- scan skips commented lines and refuses an unterminated comment by name,
-- headings inside a comment are no sections, and placementSectionWf refuses a
-- placement inside a comment.  RENAMED (statements narrowed to lines outside a
-- comment; the unconditional forms are false of commented item lines), and
-- their old lines above removed: prose_is_never_an_item ->
-- prose_outside_a_comment_is_never_an_item; splitDoc_prose_not_item ->
-- splitDoc_prose_outside_a_comment_not_item; scanLines_prose ->
-- scanLines_prose_outside_a_comment.
-- ============================================================================
#print axioms Lime.item_lines_open_no_comment
#print axioms Lime.commentAfter_false_of_item
#print axioms Lime.ranksAscend_of_pairwise
#print axioms Lime.commentOpenFrom_cons_below
#print axioms Lime.commentOpenFrom_none_below
#print axioms Lime.prose_outside_a_comment_is_never_an_item
#print axioms Lime.prose_ranks_ascend
#print axioms Lime.splitDocC_cons
#print axioms Lime.splitDocC_prose_ge
#print axioms Lime.splitDocC_items_ge
#print axioms Lime.splitDocC_reads_comments
#print axioms Lime.splitDoc_prose_outside_a_comment_not_item
#print axioms Lime.splitDoc_items_outside_comments
#print axioms Lime.comment_free_prose_is_never_an_item
#print axioms Lime.renderSplit_splitDocC
#print axioms Lime.splitDocC_prose_strict
#print axioms Lime.splitDocC_items_strict
#print axioms Lime.splitDoc_prose_strict
#print axioms Lime.nodup_map_fst_of_strict
#print axioms Lime.splitDocC_slots_separated
#print axioms Lime.no_item_sits_in_a_comment
#print axioms Lime.an_item_in_a_comment_is_rejected
#print axioms Lime.scan_state_isSome
#print axioms Lime.scanLinesFrom_cons_ok
#print axioms Lime.scanLinesFrom_prose
#print axioms Lime.scanLines_prose_outside_a_comment
#print axioms Lime.scanLinesFrom_closes
#print axioms Lime.scanLines_accepts_only_closed_comments
#print axioms Lime.commentAt_loadCore_placement
#print axioms Lime.entityUncommented_loadEntity
#print axioms Lime.the_loader_places_no_item_in_a_comment
#print axioms Lime.a_commented_item_line_loads_as_prose
#print axioms Lime.the_commented_request_loads
#print axioms Lime.the_commented_request_round_trips
#print axioms Lime.a_commented_heading_is_no_section
#print axioms Lime.an_item_line_outside_a_comment_is_still_an_item
#print axioms Lime.an_unterminated_comment_is_refused

-- ============================================================================
-- APPENDED 2026-09-12 (stage-3, step 5: gap 40's bridges).  Line.lean's
-- parse => wf bridges (one shared readNat width bound under every date), the
-- edit table's guardWf and its no-second-grammar theorems for the eight keys
-- wired now (due at win every on-event loc waiting after), the year-9999
-- rollover where the at:/win: bridge is false, and after's plan-tier refusals
-- named danglingDep / depCycle with their success form.  Statements CHANGED in
-- place, names kept: the_edit_path_writes_what_the_field_path_reads (eight more
-- match arms), parseCmd_rejects_edit_variants (the keyNotWired witness is now
-- `demoted`), edit_of_a_tabbed_line_is_refused / applyCmd_edit_succeeds
-- (proofs only: applyCmd routes edits through nameEditFault).
-- ============================================================================
#print axioms Lime.Field.readNat_foldl_none
#print axioms Lime.Field.charDigit_lt
#print axioms Lime.Field.readNat_foldl_lt
#print axioms Lime.Field.readNat_lt_pow_length
#print axioms Lime.Field.mkDate?_some
#print axioms Lime.Field.parseDate_dayWf
#print axioms Lime.Field.parseRule_wf
#print axioms Lime.Field.parseOnEvent_wf
#print axioms Lime.Field.parseDep_wf
#print axioms Lime.Field.mapOpt_all
#print axioms Lime.Field.parseDeps_wf
#print axioms Lime.Field.parseLoc_wf
#print axioms Lime.guardWf_isSome
#print axioms Lime.guardWf_none_iff
#print axioms Lime.editValOf_every_refuses_only_what_parseRule_refuses
#print axioms Lime.editValOf_onEvent_refuses_only_what_parseOnEvent_refuses
#print axioms Lime.editValOf_after_refuses_only_what_parseDeps_refuses
#print axioms Lime.renderLoc_parseLoc
#print axioms Lime.editValOf_loc_refuses_only_a_bad_or_unworded_value
#print axioms Lime.the_eight_bridged_keys_accept_their_spec_values
#print axioms Lime.the_year_9999_rollover_parses_but_the_edit_refuses_it
#print axioms Lime.wordLoc_renders_a_word
#print axioms Lime.nameEditFault_ok
#print axioms Lime.nameEditFault_ok_of
#print axioms Lime.parseCmd_refuses_the_bridged_keys_bad_values
#print axioms Lime.parseCmd_reads_the_bridged_keys
#print axioms Lime.applyCmd_edit_names_the_plan_tier_fault
#print axioms Lime.editFault_of_get
#print axioms Lime.edit_of_a_dangling_after_is_refused_by_name
#print axioms Lime.edit_of_a_cyclic_after_is_refused_by_name
#print axioms Lime.applyCmd_after_succeeds
#print axioms Lime.the_after_refusals_are_named_on_a_loaded_plan

-- APPENDED 2026-09-12 (stage-3, verification repair).  Two theorems narrowed
-- in a4ccd9c (they gained `inComment d.prose q.1 = false`) kept their old names;
-- renamed so the name matches the statement (AGENTS §7.4 item 3).  Old lines above
-- removed; statements and proofs unchanged.
#print axioms Lime.a_demoted_section_outside_a_comment_is_a_month_section
#print axioms Lime.a_pinned_section_outside_a_comment_is_a_day_section

-- ===========================================================================
-- APPENDED 2026-09-12 (stage-4 session).  Stage 4 step 2: `close` is one fold at
-- three grains.  Close.lean (new module, imported by LimeKernel.lean and by
-- Boundary.lean): the ClosePolicy table and its bridges, the fold, its
-- denotation `close_spec`, the discharged goal `close_day_stamps_a_day_stamp`,
-- the narrowed forms beside three goals left for step 3, D1 and the wall carry
-- as theorems, and the named refusals.  Boundary.lean: `endRank_is_freshRank`
-- and the loaded-plan witnesses of both directions.
-- ===========================================================================
#print axioms Lime.closeStamp_names_the_closed_grain
#print axioms Lime.closeStamp_month
#print axioms Lime.close_never_takes_a_settled_line
#print axioms Lime.closePolicy_takes_the_demoted_record_only_at_month
#print axioms Lime.closePolicy_demoted_landing_is_in_a_month_file
#print axioms Lime.closePolicy_copies_only_below_month
#print axioms Lime.closePolicy_copy_stamps
#print axioms Lime.closePolicy_move_is_unstamped
#print axioms Lime.closePolicy_exemptions
#print axioms Lime.Core.skel_stamps
#print axioms Lime.Frame.refl
#print axioms Lime.Frame.trans
#print axioms Lime.Site.shiftIn_doc
#print axioms Lime.wf_shiftIn
#print axioms Lime.skel_shiftIn
#print axioms Lime.WfPlan.mapAt_spec
#print axioms Lime.WfPlan.shiftAt_val
#print axioms Lime.frame_of_docs
#print axioms Lime.frame_shiftIn
#print axioms Lime.landAt_spec
#print axioms Lime.moveTo_skel
#print axioms Lime.moveTo_live
#print axioms Lime.fileE_skel
#print axioms Lime.closedRegionOf_frame
#print axioms Lime.closeAct_frame
#print axioms Lime.findDocIx_frame
#print axioms Lime.stepSkel_frame
#print axioms Lime.findDocIx_spec
#print axioms Lime.closeAct_of_open
#print axioms Lime.closeOne_spec
#print axioms Lime.foldlM_closeOne_spec
#print axioms Lime.closeCands_nodup
#print axioms Lime.closeAct_of_not_mem_closeCands
#print axioms Lime.close_spec
#print axioms Lime.close_skel
#print axioms Lime.exemptAct_cases
#print axioms Lime.stepSkel_of_exempt
#print axioms Lime.skelAfter_doc
#print axioms Lime.close_leaves_no_line_it_would_take
#print axioms Lime.close_leaves_no_unfinished_line_in_a_closed_region
#print axioms Lime.stepSkel_day_stamps
#print axioms Lime.close_day_stamps_a_day_stamp
#print axioms Lime.close_never_demotes_a_wall_but_may_carry_it
#print axioms Lime.close_day_files_into_the_week_of_now
#print axioms Lime.close_carries_a_wall_that_is_still_ahead
#print axioms Lime.closeOne_refuses_a_missing_target
#print axioms Lime.closeOne_refuses_a_carry_with_no_live_week
#print axioms Lime.closeOne_refuses_a_missing_section
#print axioms Lime.closeOne_refuses_an_ill_formed_post_state
#print axioms Lime.close_refuses_what_its_first_step_refuses
#print axioms Lime.close_without_candidates_is_the_identity
#print axioms Lime.foldl_max_from
#print axioms Lime.endRank_is_freshRank
#print axioms Lime.the_week_close_copies_carries_and_leaves_the_rest
#print axioms Lime.the_day_close_files_into_the_week_of_now
#print axioms Lime.the_month_close_moves_each_line_into_its_section
-- Stage 4 step 3 (same session, same banner): L16 discharged as stated in
-- Close.lean, with the skeleton half of L17 that does commute; L17 and L27
-- refuted and renamed to their negations in Boundary.lean, on loaded plans.
#print axioms Lime.closeCands_eq_nil_of_stay
#print axioms Lime.close_is_idempotent
#print axioms Lime.stepSkel_of_stay
#print axioms Lime.closeAct_of_closedRegionOf_none
#print axioms Lime.closedRegionOf_spec
#print axioms Lime.closeAct_of_another_grain
#print axioms Lime.stepSkel_lands_outside_every_closed_region
#print axioms Lime.stepSkel_comm
#print axioms Lime.close_bind_close_skel
#print axioms Lime.two_closes_at_one_instant_commute_on_skeletons
#print axioms Lime.the_close_commute_witness_loads
#print axioms Lime.the_week_then_month_close_lands_the_week_record_first
#print axioms Lime.the_month_then_week_close_lands_the_month_record_first
#print axioms Lime.close_week_month_orders_both_succeed_and_differ
#print axioms Lime.close_week_and_close_month_do_not_commute
#print axioms Lime.demote_then_readopt_succeeds_and_the_reverse_is_refused
#print axioms Lime.lifecycle_commands_do_not_commute
-- Stage 4 step 4 (same session, same banner): `autoClose` in Close.lean — L19a
-- and L19b discharged as stated, L19c's narrowing and the one-stamp theorem;
-- L19c refuted and renamed on a loaded three-month-stale plan in Boundary.lean.
#print axioms Lime.autoCloseOrder_is_the_chain
#print axioms Lime.autoCloseOrder_names_each_grain_once
#print axioms Lime.autoCloseOrder_is_coarsest_last
#print axioms Lime.autoClose_is_each_grain_once
#print axioms Lime.autoClose_ok
#print axioms Lime.autoClose_refuses_what_a_grain_refuses
#print axioms Lime.autoClose_refuses_a_refused_day_close
#print axioms Lime.close_keeps_nothing_to_close
#print axioms Lime.autoClose_leaves_nothing_to_close
#print axioms Lime.autoClose_catches_up_in_one_step
#print axioms Lime.autoClose_strands_no_unfinished_line
#print axioms Lime.close_skel_after
#print axioms Lime.autoClose_skel
#print axioms Lime.stepSkel_three_is_one
#print axioms Lime.autoClose_takes_each_line_at_most_once
#print axioms Lime.the_stale_witness_loads
#print axioms Lime.mem_closedLiveIds
#print axioms Lime.the_stale_catch_up_observed
#print axioms Lime.staleCaughtUp_map
#print axioms Lime.the_stale_tree_catches_up_in_one_call
#print axioms Lime.the_stale_ledger_before_catch_up
#print axioms Lime.the_stale_ledger_after_catch_up
#print axioms Lime.the_stale_tree_catches_up_losing_nothing
#print axioms Lime.the_stale_catch_up_leaves_only_settled_and_recurring_lines
#print axioms Lime.autoClose_leaves_lines_in_periods_it_passes
#print axioms Lime.the_stale_catch_up_refusals_are_named
-- Stage 4 step 5 (same session, same banner): what a close reports — the new
-- module Report.lean (D3's named per-item list, `closeR`/`autoCloseR`, and the
-- kind lemmas that widen L22 to the close commands); `now` and `blockMin` on
-- the wire, the close ops, and the report under `ok` in Boundary.lean.
#print axioms Lime.BlockMin.ofNat?_zero
#print axioms Lime.BlockMin.ofNat?_pos
#print axioms Lime.CloseDid.ofName?_name
#print axioms Lime.CloseDid.ofName?_refuses
#print axioms Lime.closeR_plan
#print axioms Lime.foldlM_closeStepR_plan
#print axioms Lime.autoCloseR_plan
#print axioms Lime.filterMap_ids
#print axioms Lime.closeReport_ids
#print axioms Lime.mem_closeReport
#print axioms Lime.close_found_the_target
#print axioms Lime.closeReport_stamp_names_its_grain
#print axioms Lime.autoCloseR_ok
#print axioms Lime.mem_closeCands
#print axioms Lime.not_mem_closeCands_of_stay
#print axioms Lime.close_takes_a_line_out_of_every_close
#print axioms Lime.close_keeps_a_line_untaken
#print axioms Lime.autoCloseR_names_each_line_at_most_once
#print axioms Lime.closeAct_carry_is_a_wall
#print axioms Lime.closedRegionOf_of_closeAct
#print axioms Lime.stepSkel_doc_kinds
#print axioms Lime.except_map_pair_fst
#print axioms Lime.applyCmdR_plan
#print axioms Lime.applyAllR_plan
#print axioms Lime.the_clock_reads_now_and_blockMin
#print axioms Lime.the_clock_refuses_a_malformed_value_by_name
#print axioms Lime.parseCmdAt_reads_the_close_ops_and_refuses_without_the_clock
#print axioms Lime.parseCmdAt_is_parseCmd
#print axioms Lime.run_names_the_clock_refusals
#print axioms Lime.runPlan_refusal_carries_no_report
#print axioms Lime.the_week_close_reports_each_line
#print axioms Lime.the_day_close_reports_each_line
#print axioms Lime.the_month_close_reports_each_line
#print axioms Lime.a_close_entry_emits_in_build_order
-- Stage 4 step 6 (same session, same banner): the three goals stated stronger
-- than §6.3 — L18 at plan level, F4 and B1–B3 — refuted and renamed on the loaded
-- week witness in Boundary.lean; the estimate half of narrowed B1–B3 in
-- Close.lean, on `remainingOf_setDemoted` in Line.lean.
#print axioms Lime.hasEst_setEst
#print axioms Lime.Field.viewRemaining_words
#print axioms Lime.Field.readNat_none_of_mem
#print axioms Lime.Field.unitValue_none_of_mem
#print axioms Lime.Field.neutral_of_mem
#print axioms Lime.Field.neutral_keyWord_demoted
#print axioms Lime.Field.neutral_of_demoted_tok
#print axioms Lime.Field.neutral_of_id_word
#print axioms Lime.Field.leadWords_append_neutral
#print axioms Lime.Field.remainingWords_append_neutral
#print axioms Lime.Field.setKeyIn_split
#print axioms Lime.Field.insertBeforeId_split
#print axioms Lime.Field.remainingOf_setDemoted
#print axioms Lime.the_close_week_witness_loads
#print axioms Lime.the_week_close_leaves_r1_and_t1_in_the_closed_week
#print axioms Lime.the_week_close_carries_the_wall_x1_to_another_file
#print axioms Lime.the_week_close_stamps_m2_and_writes_no_estimate
#print axioms Lime.mem_closedLiveIdsOfGrain
#print axioms Lime.close_leaves_live_lines_in_a_closed_region
#print axioms Lime.close_does_not_leave_every_wall_as_it_was
#print axioms Lime.close_writes_a_line_demoteEst_does_not
-- ===================================================================
-- APPENDED 2026-09-13 (stage-4 session, rebuild-on-lean).  Step 8: gap 59 —
-- closeCands in source order, and close_keeps_source_order (Close.lean), with
-- its sightings on loaded plans (Boundary.lean).  Gap 20's demote verb: see README.
-- ===================================================================
#print axioms Lime.siteLe_iff
#print axioms Lime.siteLe_total
#print axioms Lime.siteLe_trans
#print axioms Lime.insertBySite_perm
#print axioms Lime.sortBySite_perm
#print axioms Lime.insertBySite_sorted
#print axioms Lime.sortBySite_sorted
#print axioms Lime.closeCands_perm
#print axioms Lime.closeCands_sorted
#print axioms Lime.mem_closeCands_iff
#print axioms Lime.shiftRank_lt_iff
#print axioms Lime.rankBump_lt_iff
#print axioms Lime.shiftRank_min
#print axioms Lime.Site.bump_doc
#print axioms Lime.Site.bump_rank_of_doc
#print axioms Lime.Site.bump_of_ne
#print axioms Lime.Site.bump_none
#print axioms Lime.Site.bump_lt
#print axioms Lime.inComment_shiftFrom
#print axioms Lime.liveHeading_shiftFrom
#print axioms Lime.firstHeadingAbove_eq
#print axioms Lime.loOk_shift
#print axioms Lime.foldl_fhaStep_shift
#print axioms Lime.firstHeadingAbove_bump
#print axioms Lime.landingSpot_bump
#print axioms Lime.landingSpot_src
#print axioms Lime.le_foldl_max_nat
#print axioms Lime.live_rank_lt_endRank
#print axioms Lime.docs_shiftIn_getElem?
#print axioms Lime.landAt_moves
#print axioms Lime.closeAct_closed
#print axioms Lime.closeOne_moves
#print axioms Lime.carryTarget_frame
#print axioms Lime.closeTarget_frame
#print axioms Lime.landingSpot_docs
#print axioms Lime.sectionAt_docs
#print axioms Lime.get_of_map_eq_some
#print axioms Lime.closeOne_keeps_untaken
#print axioms Lime.fold_keeps_order_both
#print axioms Lime.closeAct_skel_frame
#print axioms Lime.fold_keeps_order_after_first
#print axioms Lime.fold_keeps_order
#print axioms Lime.sublist_pair_or
#print axioms Lime.close_keeps_source_order
#print axioms Lime.close_keeps_source_order_iff
#print axioms Lime.the_week_close_keeps_source_order_in_demoted
#print axioms Lime.the_month_close_keeps_source_order_in_its_section
#print axioms Lime.the_day_close_keeps_source_order_at_the_end_of_the_week
#print axioms Lime.the_month_close_orders_lines_by_the_destination_sections
#print axioms Lime.the_week_close_reports_in_source_order
-- ===================================================================
-- APPENDED 2026-09-13 (stage-4 session, rebuild-on-lean).  Step 9: gap 20's
-- remainder — the `demote` verb files into `# Demoted` through the close's
-- landing (Boundary.lean).
-- ===================================================================
#print axioms Lime.demoteSpot_is_the_week_close_landing
#print axioms Lime.the_demote_verb_files_into_demoted_ahead_of_the_next_section
#print axioms Lime.the_demote_verb_lands_at_the_end_of_a_month_without_demoted
-- ===================================================================
-- APPENDED 2026-09-13 (stage-4 hardening).  Step 1: README gap 62 — the fast
-- checker behind the same interface.  Every `@[csimp]` equality below lets the
-- compiler run a twin in place of a definition the proofs are about; the
-- lemmas beside them are what the equalities rest on.  No relational law.
-- ===================================================================
-- Fast.lean: `planWf`'s hot conjuncts, the store's table, the response's buckets
#print axioms Lime.render_keys
#print axioms Lime.lines_keys
#print axioms Lime.proseKeys_at
#print axioms Lime.ranksIn_keys
#print axioms Lime.docRanks_keys
#print axioms Lime.docRanks_eq_docRanksFast
#print axioms Lime.nodup_pairs_iff
#print axioms Lime.normalized_iff_keys
#print axioms Lime.keyLe_trans
#print axioms Lime.keyLe_total
#print axioms Lime.keyLt_trans
#print axioms Lime.strictAsc_iff
#print axioms Lime.strictAsc_iff_nodup
#print axioms Lime.normalized_eq_normalizedFast
#print axioms Lime.IdMap.size_empty
#print axioms Lime.IdMap.size_insert
#print axioms Lime.IdMap.slot_insert
#print axioms Lime.IdMap.get_empty
#print axioms Lime.IdMap.get_insert
#print axioms Lime.Store.ext_of
#print axioms Lime.compactStep_fold
#print axioms Lime.Store.compact_eq
#print axioms Lime.Store.set_eq_setFast
#print axioms Lime.pathsFresh_iff
#print axioms Lime.pathsDistinct_eq_pathsDistinctFast
#print axioms Lime.parentsAcyclic_eq_parentsAcyclicFast
#print axioms Lime.sitesInRange_eq_sitesInRangeFast
#print axioms Lime.foldl_commentAfter_false
#print axioms Lime.inComment_of_clean
#print axioms Lime.docFacts_live
#print axioms Lime.docFacts_heads
#print axioms Lime.foldl_if_and_filter
#print axioms Lime.lastHeadingBefore_facts
#print axioms Lime.all_if_filter
#print axioms Lime.headingsWfF_docFacts
#print axioms Lime.docFacts_kind
#print axioms Lime.docFacts_doc
#print axioms Lime.facts_get
#print axioms Lime.kindAtF_eq
#print axioms Lime.placementSectionWfF_eq
#print axioms Lime.sectionsWf_eq_sectionsWfFast
#print axioms Lime.shapesWf_eq_shapesWfFast
#print axioms Lime.itemsWf_eq_itemsWfFast
#print axioms Lime.planWf_eq_planWfFast
#print axioms Lime.firstItemFault_eq_firstItemFaultFast
#print axioms Lime.bucketByDoc_get
#print axioms Lime.linesByDoc_get
-- Close.lean: a shifted store is compacted
#print axioms Lime.Store.mapEntities_eq_mapEntitiesFast
-- Boundary.lean: the loader's grouping, dedup and store; the response renders once
#print axioms Lime.dedupStep_eq
#print axioms Lime.dedupStep_fold
#print axioms Lime.dedupIds_eq_dedupIdsFast
#print axioms Lime.groupStep_fold
#print axioms Lime.foldlM_snoc_eq_mapM
#print axioms Lime.buildEntities_eq_buildEntitiesFast
#print axioms Lime.loadStep_eq
#print axioms Lime.loadStep_fold
#print axioms Lime.loadStore_eq_loadStoreFast
#print axioms Lime.renderDocAt_eq_renderDocFrom
#print axioms Lime.runPlan_eq_runPlanFast
-- Step 2 (2026-09-13): README gap 53 — a week close (and the `demote` verb)
-- merges a line into its item's standing `# Demoted` record instead of refusing
-- `alreadyDemoted`: fork-point `demote_one`'s merge, with L15's floor.  Eight
-- names above were retired with the statements they carried (the README's step-2
-- block lists each beside its replacement); their replacements are here.
-- Cmd.lean: the merge, the stamps, the estimate through `demoteEst`
#print axioms Lime.refile_roundtrips
#print axioms Lime.refile_of_no_record
#print axioms Lime.refile_twice_is_not_a_thing
#print axioms Lime.refile_refuses_only_a_record
#print axioms Lime.foldl_stampStep_mem
#print axioms Lime.foldl_stampStep_nodup
#print axioms Lime.foldl_stampStep_of_nodup
#print axioms Lime.mergeStamps_of_nodup
#print axioms Lime.mergeStamps_spec
#print axioms Lime.unitValue_isSome
#print axioms Lime.estKeyTok_of_hasEst
#print axioms Lime.remainingOf_of_not_ownsEstimate
#print axioms Lime.carryEst_reads_as_demoteEst
#print axioms Lime.refile_conserves
#print axioms Lime.refile_respects_user
-- Close.lean: the restated laws, the refusal gone, the merge
#print axioms Lime.mapAt_error
#print axioms Lime.landAt_error
#print axioms Lime.landingSpot_error
#print axioms Lime.fileE_alreadyDemoted
#print axioms Lime.autoClose_stamps_each_line_with_no_record_at_most_once
-- Report.lean: the named disposition `copyMerging`
#print axioms Lime.CloseDid.ofStep_ne_carry
#print axioms Lime.skelAfter_stamps_of_not_merging
#print axioms Lime.skelAfter_stamps_merging
-- Boundary.lean: the verb, the loaded-plan witnesses, three refutations
#print axioms Lime.WfPlan.mapAt_congr
#print axioms Lime.demote_verb_is_cmdDemote_at_freshRank_without_a_shift_or_a_record
#print axioms Lime.the_week_close_merges_each_standing_record
#print axioms Lime.the_week_close_reports_each_merge
#print axioms Lime.the_demote_verb_merges_into_a_standing_record
#print axioms Lime.the_close_merge_witness_loads
#print axioms Lime.the_week_close_floors_m5_at_its_record
#print axioms Lime.autoClose_merges_m2s_stamps
#print axioms Lime.a_merged_record_is_rewritten_beyond_its_stamp
#print axioms Lime.a_merged_record_changes_a_remaining_estimate
#print axioms Lime.autoClose_merges_a_line_beyond_one_appended_stamp
-- Step 3 (2026-09-13): repair of steps 1-2 after an independent verification.
-- A week close (and the `demote` verb) refuses, `alreadyDemoted`, an item whose
-- tombstone is not its `# Demoted` record instead of merging into it and deleting
-- a `[-]` line from a closed week; two names narrowed in place at step 2 and two
-- names that said more than their statements are retired and restated; the merge
-- laws' hypotheses are instantiated together.  Six names above were retired (the
-- README's step-3 block lists each beside its replacement); no relational law.
-- Close.lean: the guard, where a close answers `alreadyDemoted`, the renames
#print axioms Lime.guardStray_ok
#print axioms Lime.guardStray_error
#print axioms Lime.guardStray_of_error
#print axioms Lime.guardStray_false
#print axioms Lime.closeOne_refuses_alreadyDemoted_only_over_a_stray_tomb
#print axioms Lime.closeOne_never_refuses_alreadyDemoted_without_a_stray_tomb
#print axioms Lime.closeOne_never_merges_into_a_stray_tomb
#print axioms Lime.close_answers_alreadyDemoted_only_at_a_copying_row
#print axioms Lime.stepSkel_appends_at_most_one_stamp_or_merges
#print axioms Lime.autoClose_appends_at_most_one_stamp_or_merges_each_line
-- Report.lean: the report's agreement, under a name that matches its stamp clause
#print axioms Lime.closeReport_agrees_with_close_stamping_or_merging
-- Boundary.lean: the refusals by name, the stray tombstone at both entry points,
-- three refutations, the merge laws not vacuous
#print axioms Lime.the_pre_close_pair_closes_on_a_loaded_plan
#print axioms Lime.the_pre_close_pair_is_not_a_named_refusal
#print axioms Lime.the_stray_tomb_witness_loads
#print axioms Lime.a_stray_tomb_refuses_the_week_close
#print axioms Lime.a_stray_tomb_refuses_autoClose
#print axioms Lime.the_demote_verb_refuses_a_stray_tomb
#print axioms Lime.the_week_close_merges_m2s_stamps_and_reports_one
#print axioms Lime.mergeHypsAt_spec
#print axioms Lime.the_merge_hypotheses_hold_together
#print axioms Lime.refile_merge_laws_are_not_vacuous
#print axioms Lime.a_close_can_refuse_alreadyDemoted
#print axioms Lime.closeReport_agrees_with_close_is_refuted_by_a_merge
-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final).  Step 2: README gap 55 closed — the owner's
-- D7 (a past-due `persist` line at a week close moves to `backlog.md # Overdue`,
-- box, bytes and tombstone kept) and D8 (a `# Demoted` record may carry a date;
-- the month rule reads outcomes only).  Five names above were retired with the
-- statements they carried and restated here (README "Stage 4 final", step 2):
-- `month_items_are_outcomes` -> `month_items_outside_demoted_are_undated` (old
-- statement refuted: `a_dated_demoted_record_is_a_month_item_with_a_date`);
-- `closePolicy_owes` -> `closePolicy_owes_only_the_child_fold` beside
-- `closePolicy_routes_overdue_only_at_week`; `closeAct_of_exempt` ->
-- `closeAct_never_files_an_exempt_line`; `closeReport_names_the_region_of_now` ->
-- `closeReport_names_the_destination_of_now`;
-- `each_close_refusal_is_named_on_a_loaded_plan` ->
-- `the_close_refusals_left_after_d7_are_named_on_loaded_plans` (old statement
-- refuted: `a_dated_line_no_longer_refuses_the_week_close_as_badHorizon`).  The
-- two-run laws this breaks are re-proved in place under their own names (D5):
-- `close_is_idempotent`, `close_keeps_source_order`(`_iff`) through
-- `closeOne_moves`/`fold_keeps_order`(`_after_first`), the L19 `autoClose_*`
-- theorems, `closeReport_agrees_with_close_stamping_or_merging` and
-- `move_has_no_inverse_command`; their audit lines above stand.
-- Plan.lean / Fast.lean: D8's narrowing and its csimp twin
#print axioms Lime.shapeWf_or_record_of_mem
#print axioms Lime.month_items_outside_demoted_are_undated
#print axioms Lime.a_dated_month_outcome_is_rejected
#print axioms Lime.secKindAtF_eq
#print axioms Lime.demotedRecordPlacementF_eq
-- Close.lean: the table's new column, the fourth action, the laws
#print axioms Lime.closePolicy_routes_overdue_only_at_week
#print axioms Lime.Core.skel_onMiss
#print axioms Lime.Skel.overdue_of_wallAhead
#print axioms Lime.overdueTarget_frame
#print axioms Lime.overdueTarget_spec
#print axioms Lime.closeAct_of_regionless
#print axioms Lime.closeAct_never_files_an_exempt_line
#print axioms Lime.spot_bound_after_step
#print axioms Lime.rank_lt_landing
#print axioms Lime.landed_rank_lt_next_spot
#print axioms Lime.Field.lookup_filterMap_cons_congr
#print axioms Lime.Field.isKeyTok_of_keyOf_ne
#print axioms Lime.Field.lookup_setKeyIn_other
#print axioms Lime.Field.lookup_insertBeforeId_other
#print axioms Lime.Field.lookupKey_setKey_other
#print axioms Lime.Field.isEstKey_keyOf
#print axioms Lime.Field.viewShape_congr
#print axioms Lime.lookupKey_carryEst_other
#print axioms Lime.viewShape_refiledLine
#print axioms Lime.refiledLine_stamps_mem
#print axioms Lime.Core.skel_overdue_iff
#print axioms Lime.kindOfGrain_is_never_backlog
#print axioms Lime.pairwise_of_ranksAscend
#print axioms Lime.prose_eq_of_rank
#print axioms Lime.foldl_congr_mem
#print axioms Lime.lastHeadingBefore_shiftFrom
#print axioms Lime.lastHeadingBefore_eq_foldl
#print axioms Lime.foldl_lhbStep_some
#print axioms Lime.foldl_lhbStep_ne_none
#print axioms Lime.lastHeadingBefore_eq_of_max
#print axioms Lime.foldl_fhaStep_some
#print axioms Lime.foldl_fhaStep_none
#print axioms Lime.prose_rank_lt_endRank
#print axioms Lime.landingSpot_overdue_is_under_overdue
#print axioms Lime.closeOne_lands_an_overdue_line_under_overdue
#print axioms Lime.fold_keeps_an_overdue_line_under_overdue
#print axioms Lime.fold_lands_an_overdue_line_under_overdue
#print axioms Lime.close_lands_every_overdue_line_under_overdue
#print axioms Lime.close_moves_a_past_due_persist_line_to_the_backlog
#print axioms Lime.Skel.overdue_of_not_yet_due
#print axioms Lime.close_week_moves_a_past_due_persist_line_to_the_backlog
-- Report.lean: the sixth disposition
#print axioms Lime.CloseDid.ofStep_ne_moveOverdue
#print axioms Lime.CloseDid.ofName?_refuses_near_overdue
#print axioms Lime.closeAct_overdue_iff
-- Boundary.lean: the refusals left, the loaded witnesses, two refutations
#print axioms Lime.the_close_refusals_left_after_d7_are_named_on_loaded_plans
#print axioms Lime.a_dated_line_no_longer_refuses_the_week_close_as_badHorizon
#print axioms Lime.the_week_close_routes_dated_work_on_a_loaded_plan
#print axioms Lime.the_week_close_reports_the_overdue_route
#print axioms Lime.the_close_overdue_witness_loads
#print axioms Lime.the_dated_route_hypotheses_hold_on_a_loaded_plan
#print axioms Lime.a_dated_record_loads_and_a_dated_outcome_does_not
#print axioms Lime.a_dated_demoted_record_is_a_month_item_with_a_date
#print axioms Lime.the_example_week_closes_with_d1_in_the_backlog_overdue
-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final).  Step 3: README gap 22 closed — the owner's
-- D6.  `Core.parent` is a view of the line (`Field.parentRef`), not a stored slot;
-- a dangling `@parent` refuses the whole tree `itemCheck: danglingParent`, a cycle
-- `itemCheck: parentCycle`; §3.2's prep rule, `effectiveCi` inheritance and
-- `rootPrio` fire on loaded plans.  No name retired.  Kept names whose statements
-- changed, recorded (README "Stage 4 final", step 3): `the_fields_are_the_line`
-- (gains `c.parent = d.parent`), `wf_ignores_the_item_fields` (the `parent :=`
-- binder is gone with the slot), `the_kernel_can_read_the_pairs_it_writes` (its
-- `parent = none` hypothesis is gone — strictly stronger),
-- `the_pre_close_pair_closes_on_a_loaded_plan` (gains `loadsOk … = true`: without
-- it the statement held of a request that no longer loads), and
-- `closePolicy_owes_only_the_child_fold` (the column's constructor renamed
-- gap22Parent -> childFoldB3).  Four close witnesses gained the outcome their
-- lines name (`specMonthDoc`, `closePreClosePairWitness`, `closeStrayTombWitness`,
-- `closeMergeWitness`); every theorem over them is re-decided under its own name,
-- and their audit lines above stand.  No two-run theorem's statement or proof
-- changed: L16, source order, L19, the report agreement, `move_has_no_inverse_command`
-- and the commute refutations build unchanged against the derived field.
-- State.lean / Plan.lean: the view, and `parentsTotal` both ways
#print axioms Lime.coreOfLine_parent
#print axioms Lime.parentsTotal_iff
-- State.lean: `parentRef` skips a line with no `@` word (a new csimp twin, D6's cost)
#print axioms Lime.Field.kParent_classifyWord
#print axioms Lime.Field.findSome_kParent_phase3
#print axioms Lime.Field.findSome_kParent_phase2
#print axioms Lime.Field.findSome_kParent_phase1
#print axioms Lime.Field.parentRef_of_no_at
#print axioms Lime.Field.parentRef_eq_parentRefFast
-- Fast.lean: one parent table per check, shared by the two parent conjuncts
-- (`parentsAcyclic_eq_parentsAcyclicFast`, `itemsWf_eq_itemsWfFast` and
-- `firstItemFault_eq_firstItemFaultFast` keep their names and audit lines above;
-- their twins now read the table, so their proofs are no longer `rfl`)
#print axioms Lime.tableStep_fold
#print axioms Lime.parentStep_of_not_mem
#print axioms Lime.parentTable_get
#print axioms Lime.anc_eq_ancIn
#print axioms Lime.parentsAcyclicIn_eq
#print axioms Lime.parentsTotalIn_eq
-- Boundary.lean: the refusals by name, the loads, and the derived fields firing
#print axioms Lime.loadPlan_itemCheck
#print axioms Lime.loadPlan_refuses_a_dangling_parent
#print axioms Lime.loadPlan_refuses_a_parent_cycle
#print axioms Lime.the_parent_tree_loads
#print axioms Lime.the_example_tree_loads_with_its_parents
#print axioms Lime.the_typo_tree_fails_parentsTotal_only
#print axioms Lime.the_cycle_tree_fails_parentsAcyclic_only
#print axioms Lime.a_typod_parent_refuses_the_whole_tree_by_name
#print axioms Lime.a_parent_cycle_refuses_the_whole_tree_by_name
#print axioms Lime.the_prep_rule_fires_on_a_loaded_plan
#print axioms Lime.effectiveCi_inherits_on_a_loaded_plan
#print axioms Lime.rootPrio_reads_the_root_on_a_loaded_plan
-- ===========================================================================
-- APPENDED 2026-09-13 (stage-4 final).  Step 4: goal B3, the week row's child fold
-- — refuted and renamed, with §6.4's `max` law beside it; stage 4's goal count is
-- zero.  `close g now` gains the block length (`close g now bm`, `autoClose now
-- bm`); an unfinished child of a line the week close files from the same file is
-- dropped `[~]` in place and its own remaining floors that line's record (fork-point
-- `horizon::demote_est`'s `folded`).  Twelve names above were retired with the
-- statements they carried and restated here (README "Stage 4 final, step 4"), each
-- old statement refuted on the loaded fold witness where it is not a helper:
-- `closePolicy_owes_only_the_child_fold` -> `closePolicy_drops_children_only_at_week`
-- (+ `closePolicy_drops_children_only_at_a_copying_row`);
-- `stepSkel_line_is_stamped_or_merged` -> `stepSkel_line_is_stamped_merged_or_folded`;
-- `close_rewrites_a_line_only_by_stamping_or_merging_it` ->
-- `close_rewrites_a_line_only_by_stamping_merging_or_folding_it` (refuted:
-- `a_folded_record_is_rewritten_beyond_its_stamp`);
-- `close_rewrites_a_line_with_no_record_only_by_stamping_it` ->
-- `close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it` and
-- `close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it`
-- (refuted: `a_folded_line_with_no_record_is_rewritten_beyond_its_stamp`);
-- `close_reads_every_remaining_estimate_through_demoteEst` ->
-- `close_reads_every_remaining_estimate_through_demoteEst_and_the_fold` (refuted:
-- `a_folded_record_changes_a_remaining_estimate`);
-- `close_keeps_the_remaining_estimate_of_a_line_with_no_record` ->
-- `close_keeps_the_remaining_estimate_of_a_line_with_no_record_and_nothing_folded`
-- (refuted: `a_folded_line_with_no_record_changes_its_remaining_estimate`);
-- `close_files_a_taken_line_into_closeTo` ->
-- `close_files_a_taken_line_it_does_not_drop_into_closeTo` (refuted:
-- `a_dropped_child_is_not_filed_into_closeTo`);
-- `close_week_merges_a_standing_record` ->
-- `close_week_merges_a_standing_record_it_does_not_drop` (refuted:
-- `a_dropped_child_keeps_its_record_unmerged`), and its `_is_not_vacuous`;
-- `close_week_files_a_dated_line_keeping_its_date` ->
-- `close_week_files_a_dated_line_it_does_not_drop_keeping_its_date` (refuted:
-- `a_dropped_dated_child_is_not_filed_as_a_record`);
-- `close_week_demotes_a_not_yet_due_line_keeping_its_date` ->
-- `close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date`
-- (refuted: `a_not_yet_due_child_is_dropped_with_its_parent`);
-- `closeReport_names_the_destination_of_now` -> `closeReport_names_each_lines_destination`
-- (refuted: `a_dropped_child_is_reported_where_it_stays`).
-- The goal: `close_week_folds_a_dropped_child_into_its_parent` (Goals.lean, deleted)
-- -> `close_week_does_not_add_a_dropped_child_to_its_parent`.
-- The two-run laws this breaks are re-proved under their own names (D5), their
-- audit lines above standing: `close_is_idempotent` (L16; a `[~]` child is settled),
-- `close_keeps_source_order`(`_iff`) (the same action now includes the fold's drop:
-- `hfold`; the unextended form refuted as `a_dropped_child_and_its_filed_parent_part_ways`),
-- the L19 theorems (`autoClose_*`, through `stepSkel_leaves_nothing_a_close_takes` and
-- `close_keeps_foldFxOf_of_another_grain`), `closeReport_agrees_with_close_stamping_or_merging`
-- (three new dispositions), `two_closes_at_one_instant_commute_on_skeletons`,
-- `close_week_and_close_month_do_not_commute`, `move_has_no_inverse_command`, `close_spec`.
-- Cmd.lean: the fold's estimate, through `demoteEst`, and `refileX`
#print axioms Lime.find_setEstInTo
#print axioms Lime.foldEst_of_le
#print axioms Lime.foldEst_of_lt
#print axioms Lime.foldEst_reads_as_demoteEst
#print axioms Lime.foldEst_zero
#print axioms Lime.refiledLineX_none
#print axioms Lime.refiledLineX_of_apply
#print axioms Lime.refileX_none
#print axioms Lime.refileX_refuses_only_a_record
#print axioms Lime.refileX_roundtrips
#print axioms Lime.remainingOf_foldEst
#print axioms Lime.unitValue_digits_b
#print axioms Lime.unitValue_digits_h
#print axioms Lime.unitValue_digits_m
#print axioms Lime.unitValue_foldDur
#print axioms Lime.viewRemaining_setEstTo
-- Close.lean: the column, the fold, its laws, and the re-proofs' new lemmas
#print axioms Lime.children_of_not_copy
#print axioms Lime.closeAct_of_settled
#print axioms Lime.closeAct_of_takes_false
#print axioms Lime.close_dom
#print axioms Lime.close_files_a_taken_line_it_does_not_drop_into_closeTo
#print axioms Lime.close_keeps_foldFxOf_of_another_grain
#print axioms Lime.close_keeps_skel_of_another_grain
#print axioms Lime.close_keeps_the_remaining_estimate_of_a_line_with_no_record_and_nothing_folded
#print axioms Lime.closeOne_dom
#print axioms Lime.closePolicy_children_cases
#print axioms Lime.closePolicy_drops_children_only_at_a_copying_row
#print axioms Lime.closePolicy_drops_children_only_at_week
#print axioms Lime.close_reads_every_remaining_estimate_through_demoteEst_and_the_fold
#print axioms Lime.close_rewrites_a_line_only_by_stamping_merging_or_folding_it
#print axioms Lime.close_rewrites_a_line_with_no_record_and_nothing_folded_only_by_stamping_it
#print axioms Lime.close_rewrites_a_line_with_no_record_only_by_stamping_or_folding_it
#print axioms Lime.close_week_demotes_a_not_yet_due_line_it_does_not_drop_keeping_its_date
#print axioms Lime.close_week_drops_a_child_with_its_parent
#print axioms Lime.close_week_files_a_dated_line_it_does_not_drop_keeping_its_date
#print axioms Lime.close_week_folds_dropped_children_by_max
#print axioms Lime.close_week_keeps_a_dropped_childs_remaining_in_its_parents_record
#print axioms Lime.close_week_keeps_a_parent_that_covers_its_dropped_children
#print axioms Lime.close_week_lifts_a_parent_its_dropped_children_outweigh
#print axioms Lime.close_week_merges_a_standing_record_it_does_not_drop
#print axioms Lime.demoteEst_reads_zero
#print axioms Lime.dropE_skel
#print axioms Lime.dropsInto_congr
#print axioms Lime.dropsInto_of_asAnyLine
#print axioms Lime.dropsInto_spec
#print axioms Lime.filesLine_iff
#print axioms Lime.foldedMinutes_of_asAnyLine
#print axioms Lime.foldedMinutes_of_dropped
#print axioms Lime.foldFxOf_apply
#print axioms Lime.foldFxOf_congr
#print axioms Lime.foldFxOf_isDrop
#print axioms Lime.foldFxOf_of_asAnyLine
#print axioms Lime.fold_keeps_order_of_drop
#print axioms Lime.foldParent_congr
#print axioms Lime.foldParent_of_asAnyLine
#print axioms Lime.foldParent_spec
#print axioms Lime.foldTab_congr
#print axioms Lime.foldTab_of_asAnyLine
#print axioms Lime.foldTabSum_of_not_has
#print axioms Lime.foldParent_eq_foldParentFast
#print axioms Lime.foldTab_eq_foldTabFast
#print axioms Lime.foldTabSum_step
#print axioms Lime.foldUp_congr
#print axioms Lime.foldUp_spec
#print axioms Lime.landAt_dom
#print axioms Lime.le_foldTabSum
#print axioms Lime.lookupKey_apply_other
#print axioms Lime.Field.lookupKey_setEstTo_other
#print axioms Lime.Field.lookup_setEstInTo_other
#print axioms Lime.mem_foldTab
#print axioms Lime.ownMinutes_le_foldedMinutes
#print axioms Lime.refiledLineX_stamps_mem
#print axioms Lime.remainingOf_carriedLine
#print axioms Lime.skelAfter_week
#print axioms Lime.SkelKept.filesLine_eq
#print axioms Lime.SkelKept.get_none
#print axioms Lime.SkelKept.skel_of_files
#print axioms Lime.stepSkel_congr_fx
#print axioms Lime.stepSkel_leaves_nothing_a_close_takes
#print axioms Lime.stepSkel_line_is_stamped_merged_or_folded
#print axioms Lime.stepSkel_of_drop
#print axioms Lime.stepSkel_of_file
#print axioms Lime.viewShape_refiledLineX
#print axioms Lime.WfPlan.mapAt_dom
-- Report.lean: the three new dispositions, and where each line is
#print axioms Lime.CloseDid.ofName?_refuses_near_fold
#print axioms Lime.CloseDid.ofStep_folding_iff
#print axioms Lime.CloseDid.ofStep_merging_iff
#print axioms Lime.CloseDid.ofStep_ne_dropIntoParent
#print axioms Lime.closeReport_names_each_lines_destination
#print axioms Lime.foldFxOf_isLift_not_drop
#print axioms Lime.foldFxOf_isLift_week
-- Boundary.lean: the loaded fold witness, the refutations, non-vacuity
#print axioms Lime.a_dropped_child_and_its_filed_parent_part_ways
#print axioms Lime.a_dropped_child_is_not_filed_into_closeTo
#print axioms Lime.a_dropped_child_is_reported_where_it_stays
#print axioms Lime.a_dropped_child_keeps_its_record_unmerged
#print axioms Lime.a_dropped_dated_child_is_not_filed_as_a_record
#print axioms Lime.a_folded_line_with_no_record_changes_its_remaining_estimate
#print axioms Lime.a_folded_line_with_no_record_is_rewritten_beyond_its_stamp
#print axioms Lime.a_folded_record_changes_a_remaining_estimate
#print axioms Lime.a_folded_record_is_rewritten_beyond_its_stamp
#print axioms Lime.a_not_yet_due_child_is_dropped_with_its_parent
#print axioms Lime.archive_none_of_toNat
#print axioms Lime.beforeAfterFoldClose_some
#print axioms Lime.c5_dated_facts
#print axioms Lime.closeAct_file_facts
#print axioms Lime.close_week_does_not_add_a_dropped_child_to_its_parent
#print axioms Lime.close_week_drops_a_child_with_its_parent_is_not_vacuous
#print axioms Lime.close_week_folds_dropped_children_by_max_is_not_vacuous
#print axioms Lime.close_week_merges_a_standing_record_it_does_not_drop_is_not_vacuous
#print axioms Lime.fold_facts
#print axioms Lime.foldFacts_eq
#print axioms Lime.the_close_fold_witness_loads
#print axioms Lime.the_fold_facts_on_the_loaded_witness
#print axioms Lime.the_fold_on_the_loaded_witness
#print axioms Lime.the_fold_witness_links_and_dates
#print axioms Lime.the_merge_witness_drops_neither_record
#print axioms Lime.the_dated_witness_drops_nothing
#print axioms Lime.the_week_close_folds_dropped_children_on_a_loaded_plan
#print axioms Lime.the_week_close_reports_the_fold
#print axioms Lime.toNat_eq_one
#print axioms Lime.toNat_eq_zero

-- APPENDED 2026-09-13 (stage-4 final).  Repair: two defects of step 4 an independent
-- verification found (kernel/README.md "Stage 4 final, repair").  Defect 2: the mixed
-- pair — one line the fold drops, one it files, from one file by one action — gets the
-- order law `close_keeps_source_order` (whose `hfold` it falls outside) cannot state,
-- over the sites both leave in the source file; `close_keeps_source_order` and `_iff`
-- are unchanged.  Defect 3: the stage-one reader `unitValue` reads `NhMm`
-- (`hmValue`), so an `NhMm` child is folded at its minutes; `unitValue_estWord`,
-- `unitValue_isSome` and `Field.unitValue_none_of_mem` keep their statements, their
-- proofs re-run over the new branch.
#print axioms Lime.Entity.bumpIn_live
#print axioms Lime.Entity.bumpIn_archiveSite
#print axioms Lime.landAt_get
#print axioms Lime.closeOne_get_others
#print axioms Lime.fold_keeps_a_closed_site
#print axioms Lime.fold_keeps_a_dropped_line_in_place
#print axioms Lime.fold_leaves_a_copied_lines_tombstone_where_it_stood
#print axioms Lime.mem_closeCands_of_ne_stay
#print axioms Lime.files_of_isDrop
#print axioms Lime.close_leaves_a_dropped_line_where_it_stood
#print axioms Lime.close_leaves_a_copied_lines_tombstone_where_it_stood
#print axioms Lime.close_keeps_source_order_across_the_fold
#print axioms Lime.close_keeps_source_order_across_the_fold_is_not_vacuous
#print axioms Lime.the_mixed_pair_keeps_its_order_on_the_loaded_witness
#print axioms Lime.Field.hmValue_none_of_mem
#print axioms Lime.Field.unitValue_renderDur
#print axioms Lime.the_week_close_folds_an_hours_and_minutes_child

-- APPENDED 2026-09-14 (stage 5).  Step 1: §6.4's `remaining` and §5.4's series head
-- (kernel/README.md "Stage 5 step 1").  `Tree.lean` (new, imported after `Plan`):
-- `remainingMin` is fork-point `Tree::remaining` with structural fuel, proved to be
-- the one fixed point of its step on a well-formed plan; `seriesHead` is
-- `Tree::series_head` per document.  Goals discharged as stated:
-- `the_series_head_is_not_settled`, `the_series_head_ranks_first`.  Goals refuted as
-- written, the law that holds beside each: `remaining_is_the_est_key_when_set`,
-- `remaining_falls_back_to_the_leading_estimate`, `remaining_sums_the_children`
-- (`Boundary.lean`, on a loaded plan).  Gap 18 closed; gap 73 buildable, not rewired.
#print axioms Lime.viewFields_estLead
#print axioms Lime.ownRemaining_of_estKey
#print axioms Lime.ownRemaining_of_lead
#print axioms Lime.ownRemaining_of_dur
#print axioms Lime.ownRemaining_none
#print axioms Lime.parentStep_of_mem_childrenOf
#print axioms Lime.optAdd_getD
#print axioms Lime.remainingStep_congr
#print axioms Lime.remainingStep_missing
#print axioms Lime.remainingStep_settled
#print axioms Lime.remainingStep_own
#print axioms Lime.remainingStep_children
#print axioms Lime.anc_succ_bind
#print axioms Lime.anc_fuel_none
#print axioms Lime.WfPlan.acyclic
#print axioms Lime.anc_ne_of_child
#print axioms Lime.remainingAux_stable
#print axioms Lime.remainingAux_fuel_is_enough
#print axioms Lime.remainingOpt_step
#print axioms Lime.remainingOpt_is_the_unique_fixed_point
#print axioms Lime.foldl_optAdd_getD
#print axioms Lime.remaining_of_a_settled_item_is_zero
#print axioms Lime.remaining_of_a_missing_id_is_zero
#print axioms Lime.remaining_is_the_est_key_when_set_and_unsettled
#print axioms Lime.remaining_falls_back_to_the_leading_estimate_when_unsettled
#print axioms Lime.remaining_falls_back_to_dur_when_unsettled
#print axioms Lime.remaining_sums_the_children_when_unsettled_with_no_dur
#print axioms Lime.firstByRank_mem
#print axioms Lime.firstByRank_isSome_cons
#print axioms Lime.firstByRank_le
#print axioms Lime.firstByRank_eq_none
#print axioms Lime.mem_seriesOpen
#print axioms Lime.seriesHead_spec
#print axioms Lime.the_series_head_is_not_settled
#print axioms Lime.the_series_head_ranks_first
#print axioms Lime.seriesHead_isSome_of_an_unsettled_member
#print axioms Lime.seriesHead_none_when_every_member_is_settled
#print axioms Lime.the_tree_witness_loads
#print axioms Lime.remaining_reads_the_est_key_over_the_leading_estimate_on_a_loaded_plan
#print axioms Lime.remaining_reads_the_leading_estimate_on_a_loaded_plan
#print axioms Lime.remaining_sums_two_children_on_a_loaded_plan
#print axioms Lime.remaining_reads_dur_on_a_loaded_plan
#print axioms Lime.remaining_of_a_settled_line_is_zero_on_a_loaded_plan
#print axioms Lime.remaining_is_none_without_an_estimate_on_a_loaded_plan
#print axioms Lime.the_series_head_skips_a_settled_member_on_a_loaded_plan
#print axioms Lime.remaining_is_not_the_est_key_on_a_settled_line
#print axioms Lime.remaining_does_not_fall_back_to_the_leading_estimate_on_a_settled_line
#print axioms Lime.remaining_does_not_sum_the_children_over_a_dur

-- APPENDED 2026-09-14 (stage 5).  Step 2: §7.1's priority, §7.2's rule table and §7.4's
-- hysteresis (kernel/README.md "Stage 5 step 2").  `Priority.lean` (new, imported after
-- `Tree`): `prio` is `priority::clamp_p` over Arith's bin and `rootK` is
-- `Tree::root_priority`; the ladder takes a rational availability by
-- cross-multiplication (D10); `hysteresis` is `priority::apply_hysteresis`.  Goals
-- discharged as stated: `prio_of_hot_is_zero`, `prio_is_clamped`,
-- `prio_is_antitone_in_utilisation`, `hysteresis_improves_by_at_most_one_bin`,
-- `hysteresis_worsens_freely`, `hysteresis_never_delays_hot`.  Gap 27's loader check
-- has its smart constructor (`binsOf?`); the loader call waits for the config wiring.
#print axioms Lime.defaultPrioOf?_refuses_zero
#print axioms Lime.defaultPrioOf?_refuses_above_four
#print axioms Lime.defaultPrioOf?_accepts
#print axioms Lime.specDefaultPrio_is_three
#print axioms Lime.rootK_pos
#print axioms Lime.rootK_le_four
#print axioms Lime.rootK_of_a_root_with_k
#print axioms Lime.rootK_of_a_root_without_k
#print axioms Lime.prio_plus
#print axioms Lime.prio_of_hot_is_zero
#print axioms Lime.prio_is_clamped
#print axioms Lime.prio_mono_ix
#print axioms Lime.prio_is_antitone_in_utilisation
#print axioms Lime.prio_eq_zero_iff_hot
#print axioms Lime.prio_clamp_is_silent_on_the_default_ladder
#print axioms Lime.prio_clamp_fires_on_a_long_ladder
#print axioms Lime.utilQGe_cross
#print axioms Lime.utilQGe_eq_le
#print axioms Lime.utilQGe_is_division
#print axioms Lime.utilQGe_on_whole_minutes
#print axioms Lime.cross_transfer
#print axioms Lime.utilQGe_congr
#print axioms Lime.utilGe_scaled_pair_congr
#print axioms Lime.rungs_eq_of_utilGe_eq
#print axioms Lime.binOfQ_ix
#print axioms Lime.binOfScaledQ_ix
#print axioms Lime.binOfQ_on_whole_minutes
#print axioms Lime.utilScaledQGe_on_whole_minutes
#print axioms Lime.binOfScaledQ_on_whole_minutes
#print axioms Lime.utilScaledQGe_is_division
#print axioms Lime.binOfQ_congr
#print axioms Lime.binOfScaledQ_congr
#print axioms Lime.binOfQ_capacity_zero
#print axioms Lime.binOfScaledQ_capacity_zero
#print axioms Lime.zero_need_on_zero_capacity_is_hot
#print axioms Lime.binOfQ_anti_avail
#print axioms Lime.prio_is_antitone_in_rational_utilisation
#print axioms Lime.flooring_the_mixture_changes_the_bin
#print axioms Lime.Bins.ladder_eq_rungs
#print axioms Lime.binsOf?_isSome_iff
#print axioms Lime.binsOf?_val
#print axioms Lime.binsOf?_accepts_the_default
#print axioms Lime.binsOf?_refuses_unsorted_edges
#print axioms Lime.binsOf?_refuses_an_edge_above_hot
#print axioms Lime.binsOf?_refuses_an_infinite_edge
#print axioms Lime.binsOfPairs?_refuses_a_zero_denominator
#print axioms Lime.the_spec_decimals_are_the_default_ladder
#print axioms Lime.a_misconfigured_ladder_is_antitone_but_not_the_ladder
#print axioms Lime.safetyOf?_refuses_zero
#print axioms Lime.safetyOf?_refuses_a_zero_denominator
#print axioms Lime.safetyOf?_reads_the_spec
#print axioms Lime.hysteresis_cases
#print axioms Lime.hysteresis_improves_by_at_most_one_bin
#print axioms Lime.hysteresis_worsens_freely
#print axioms Lime.hysteresis_never_delays_hot
#print axioms Lime.hysteresis_never_raises_urgency
#print axioms Lime.hysteresis_holds_one_step_back
#print axioms Lime.hysteresis_le_max
#print axioms Lime.yesterdayOf?_refuses_eight
#print axioms Lime.yesterdayOf?_accepts
#print axioms Lime.applyHysteresis_without_yesterday
#print axioms Lime.applyHysteresis_disabled
#print axioms Lime.applyHysteresis_enabled
#print axioms Lime.applyHysteresis_zero
#print axioms Lime.applyHysteresis_cases
#print axioms Lime.hysteresisDays_closed_form
#print axioms Lime.hysteresis_settles_on_a_steady_priority
#print axioms Lime.hysteresis_holds_every_day_of_the_gap
#print axioms Lime.hysteresisDays_of_hot
#print axioms Lime.rawPrio_of_a_wall
#print axioms Lime.rawPrio_of_an_optional
#print axioms Lime.rawPrio_of_overdue
#print axioms Lime.rawPrio_of_a_mandatory_instance
#print axioms Lime.rawPrio_of_the_hot_flag
#print axioms Lime.rawPrio_of_a_pass
#print axioms Lime.rawPrio_of_pure_rank
#print axioms Lime.rawPrio_is_clamped
#print axioms Lime.rowOf_eq_wall_iff
#print axioms Lime.rawPrio_isNone_iff
#print axioms Lime.finalPrio_of_a_wall
#print axioms Lime.finalPrio_of_an_optional
#print axioms Lime.finalPrio_damps
#print axioms Lime.finalPrio_never_delays_zero
#print axioms Lime.finalPrio_is_clamped
#print axioms Lime.finalPrio_improves_by_at_most_one_step
#print axioms Lime.prio_reads_the_root_priority_on_a_loaded_plan
#print axioms Lime.a_root_without_k_takes_the_default_on_a_loaded_plan
#print axioms Lime.hot_is_zero_whatever_the_root_on_a_loaded_plan
#print axioms Lime.the_rule_table_ranks_a_loaded_plan

-- APPENDED 2026-09-14 (stage 5).  Step 3: §7.3's EDF reservation pass over given capacities
-- (kernel/README.md "Stage 5 step 3").  `Capacity.lean` (new, imported after `Priority`):
-- D10's exact minutes as numerators over one positive denominator; `reserveRest` is
-- `capacity::reserve` (earliest day first, highest matching level first, the ci filter),
-- `availUntil` is `capacity::available_until`, and `edf` / `edfGrants` are
-- `priority::compute`'s EDF loop over a stable due-ascending order.  Goals discharged, each
-- restated over rational minutes as D10 forces: `edf_keeps_the_days`,
-- `edf_only_spends_capacity`, `edf_reserves_only_before_the_deadline`.  Two-run laws proved
-- (D5): `edf_more_capacity_never_raises_a_shortfall`,
-- `edf_more_capacity_leaves_more_capacity`,
-- `edf_a_later_deadline_takes_nothing_from_an_earlier_one`.
#print axioms Lime.denOf?_refuses_zero
#print axioms Lime.denOf?_accepts
#print axioms Lime.levelOf?_refuses_six_and_above
#print axioms Lime.levelOf?_accepts
#print axioms Lime.minutesAt_le_iff
#print axioms Lime.minutesAt_eq_iff
#print axioms Lime.minutesAt_one
#print axioms Lime.stepLevel_val
#print axioms Lime.stepLevel_five_sub
#print axioms Lime.dayLeft_succ
#print axioms Lime.stepTake_le_left
#print axioms Lime.dayRest_eq_sub_take
#print axioms Lime.dayTake_eq_stepTake
#print axioms Lime.dayTake_le
#print axioms Lime.dayRest_le
#print axioms Lime.dayRest_below_ci
#print axioms Lime.dayLeft_eq_sub
#print axioms Lime.dayOut_eq
#print axioms Lime.dayOut_le
#print axioms Lime.topElig_mono_n
#print axioms Lime.topElig_mono_f
#print axioms Lime.eligAt_mono
#print axioms Lime.topElig_at
#print axioms Lime.topElig_at_le_eligAt
#print axioms Lime.topTake_add_dayLeft
#print axioms Lime.sum6_dayTake
#print axioms Lime.day_conserves
#print axioms Lime.day_gives_the_min
#print axioms Lime.dayRest_zero
#print axioms Lime.dayRest_drained
#print axioms Lime.dayRest_drained_of_dayOut_pos
#print axioms Lime.dayRest_drains_higher_levels
#print axioms Lime.dayRest_mono
#print axioms Lime.dayOut_mono
#print axioms Lime.reserveOut_eq
#print axioms Lime.reserveOut_le
#print axioms Lime.reserve_gives_the_min
#print axioms Lime.reserve_conserves
#print axioms Lime.reserveRest_zero
#print axioms Lime.reserving_the_clamped_request_is_the_same
#print axioms Lime.reserveRest_spent
#print axioms Lime.reserveRest_drains_earlier_days
#print axioms Lime.availUntil_mono
#print axioms Lime.reserveRest_mono
#print axioms Lime.reserveOut_anti
#print axioms Lime.perm_insertDue
#print axioms Lime.sortDue_perm
#print axioms Lime.mem_sortDue
#print axioms Lime.sorted_insertDue
#print axioms Lime.sortDue_sorted
#print axioms Lime.filter_due_insertDue
#print axioms Lime.sortDue_is_stable
#print axioms Lime.insertDue_append_last
#print axioms Lime.sortDue_append_last
#print axioms Lime.edfGrantsGo_deadlines
#print axioms Lime.edfGrants_deadlines
#print axioms Lime.edfGrants_length
#print axioms Lime.edf_serves_an_earlier_deadline_first
#print axioms Lime.edf_a_later_deadline_takes_nothing_from_an_earlier_one
#print axioms Lime.forall₂_refl
#print axioms Lime.forall₂_trans
#print axioms Lime.forall₂_length
#print axioms Lime.forall₂_getElem?
#print axioms Lime.edfCaps_spent
#print axioms Lime.edf_keeps_the_days
#print axioms Lime.edf_keeps_the_dates
#print axioms Lime.edf_only_spends_numerators
#print axioms Lime.edf_only_spends_capacity
#print axioms Lime.edf_reserves_only_before_the_deadline
#print axioms Lime.edf_spares_levels_below_every_ci
#print axioms Lime.edfCaps_conserves
#print axioms Lime.edf_spends_exactly_what_it_reserves
#print axioms Lime.Grant.hot_iff
#print axioms Lime.Grant.impossible_imp_hot
#print axioms Lime.grantOf_reserved
#print axioms Lime.edfGrantsGo_exact
#print axioms Lime.edf_reserves_the_min
#print axioms Lime.edf_reserves_no_more_than_the_need
#print axioms Lime.edf_reserves_no_more_than_was_available
#print axioms Lime.edf_reports_the_shortfall
#print axioms Lime.edf_shortfall_is_need_minus_avail
#print axioms Lime.edf_impossible_iff_shortfall
#print axioms Lime.edfCaps_mono
#print axioms Lime.edfGrantsGo_mono
#print axioms Lime.edf_more_capacity_leaves_more_capacity
#print axioms Lime.edf_more_capacity_never_raises_a_shortfall
#print axioms Lime.lookaheadOf?_refuses_a_zero_denominator
#print axioms Lime.lookaheadOf?_refuses_unsorted_days
#print axioms Lime.lookaheadOf?_accepts
#print axioms Lime.daysAscending_pairwise
#print axioms Lime.reserve_takes_the_best_levels_earliest
#print axioms Lime.edf_serves_the_earlier_deadline_first_on_a_witness
#print axioms Lime.edf_spends_before_the_deadline_and_not_after_on_a_witness
#print axioms Lime.flooring_the_capacity_changes_the_verdict
#print axioms Lime.the_ci_filter_on_a_witness
#print axioms Lime.sortDue_keeps_ties_in_input_order_on_a_witness
#print axioms Lime.lookaheadOf?_on_witnesses
#print axioms Lime.edf_five_deadlines_over_three_days
#print axioms Lime.edf_serves_a_loaded_plans_needs_earliest_deadline_first

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L1: D10's exact mixture
-- (kernel/README.md "Stage 5 D10 L1").  `Lookahead.lean` (new, imported after `Capacity`):
-- `capDen = 10^18` (D17), the weight decoder `mkWeight?` with its three named refusals,
-- `mix` (lounge and home weighed after each budget limit), `limitHist`, the threshold twin,
-- and the scaling laws that make `capDen` unobservable.  In-step (design §13.2); no goal
-- entered or left `Goals.lean`.  Two-run laws proved (D5): `edf_commutes_with_scaling`,
-- `edfGrants_commute_with_scaling`.
#print axioms Lime.Look.capDen_eq_pow
#print axioms Lime.Look.capDen_pos
#print axioms Lime.Look.mkWeight?_zero_den
#print axioms Lime.Look.mkWeight?_above_one
#print axioms Lime.Look.mkWeight?_precision
#print axioms Lime.Look.mkWeight?_refuses_more_than_18_places
#print axioms Lime.Look.mkWeight?_accepts
#print axioms Lime.Look.mkWeight?_ok_elim
#print axioms Lime.Look.mkWeight?_denotes
#print axioms Lime.Look.mkWeight?_accepted_width
#print axioms Lime.Look.mkWeight?_complement
#print axioms Lime.Look.mkWeight?_round2
#print axioms Lime.Look.mix_between_the_locations
#print axioms Lime.Look.mix_at_zero_is_home
#print axioms Lime.Look.mix_at_one_is_lounge
#print axioms Lime.Look.mixDay_at_a_certain_weight
#print axioms Lime.Look.mix_denotes_the_weighted_sum
#print axioms Lime.Look.mixDay_minutesAt_is_the_expectation
#print axioms Lime.Look.mix_width
#print axioms Lime.Look.topElig_lin
#print axioms Lime.Look.eligAt_mix
#print axioms Lime.Look.mix_atLeast_between_the_locations
#print axioms Lime.Look.limitHist_keeps_the_min
#print axioms Lime.Look.dayTake_scale
#print axioms Lime.Look.dayRest_scale
#print axioms Lime.Look.dayOut_scale
#print axioms Lime.Look.mixing_before_the_budget_agrees_at_a_certain_weight
#print axioms Lime.Look.mixing_before_the_budget_is_not_the_expectation
#print axioms Lime.Look.mixing_before_the_budget_on_the_witness
#print axioms Lime.Look.twin_is_the_forks_location
#print axioms Lime.Look.twin_is_the_forks_threshold
#print axioms Lime.Look.the_bin_does_not_see_capDen
#print axioms Lime.Look.availUntil_scale
#print axioms Lime.Look.reserveRest_scale
#print axioms Lime.Look.reserveOut_scale
#print axioms Lime.Look.edfCaps_scale
#print axioms Lime.Look.edfGrantsGo_scale
#print axioms Lime.Look.edf_commutes_with_scaling
#print axioms Lime.Look.edfGrants_commute_with_scaling
#print axioms Lime.Look.a_scaled_grant_keeps_its_verdicts
#print axioms Lime.Look.mkWeight?_on_witnesses
#print axioms Lime.Look.mix_on_a_witness

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step A1 (design §14.1): gap 44 closed.
-- The per-element recursions of the codec and splitDoc run as proved @[csimp]
-- accumulator twins (rule D9-21).  Json.lean: the emitter twin, then the parser twin;
-- Plan.lean: splitDoc's twin.  22 theorems.
#print axioms Lime.jemitRev_eq
#print axioms Lime.jemitTailAcc_go_eq
#print axioms Lime.jemitArrAcc_go_eq
#print axioms Lime.jemitOTailAcc_go_eq
#print axioms Lime.jemitPairAcc_go_eq
#print axioms Lime.jemitObjAcc_go_eq
#print axioms Lime.jemit_eq_jemitAcc
#print axioms Lime.jemitArr_eq_jemitArrAcc
#print axioms Lime.jemitTail_eq_jemitTailAcc
#print axioms Lime.jemitObj_eq_jemitObjAcc
#print axioms Lime.jemitPair_eq_jemitPairAcc
#print axioms Lime.jemitOTail_eq_jemitOTailAcc
#print axioms Lime.jparserAcc
#print axioms Lime.jval_eq_jvalAcc
#print axioms Lime.jarr_eq_jarrAcc
#print axioms Lime.jtail_eq_jtailAcc
#print axioms Lime.jobj_eq_jobjAcc
#print axioms Lime.jpair_eq_jpairAcc
#print axioms Lime.jotail_eq_jotailAcc
#print axioms Lime.splitDocCAcc_go
#print axioms Lime.splitDocC_eq_splitDocCAcc
#print axioms Lime.splitDoc_eq_splitDocAcc

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step A2 (design §14.1, §5.1): JSON gains an
-- exact decimal (`JVal.dec`), gaps 42 (surrogate pairs) and 43 (leading zeros) read as serde
-- reads, `jparse_jemit` re-proved unconditionally.  Json.lean, then Boundary.lean.  42 theorems;
-- two stage-3 lines above were renamed in place to their refutations
-- (`jparse_accepts_leading_zeros` -> `jparse_refuses_a_leading_zero`,
-- `jparse_refuses_what_the_fragment_has_no_type_for` -> `jparse_reads_what_the_fragment_had_no_type_for`).
#print axioms Lime.junescape_reads_a_surrogate_pair
#print axioms Lime.digitFin_finChar
#print axioms Lime.digitFin_of_not_digit
#print axioms Lime.finChar_is_digit
#print axioms Lime.jfinsTR_go
#print axioms Lime.jfins_eq_jfinsTR
#print axioms Lime.jdigitsTR_go
#print axioms Lime.jdigits_eq_jdigitsTR
#print axioms Lime.jfins_append
#print axioms Lime.notDigitStart_of_numEnd
#print axioms Lime.JDec.renderU_ne_nil
#print axioms Lime.digitsOf_zero_head
#print axioms Lime.jleadingZero_digitsOf
#print axioms Lime.numEnd_jemitTail
#print axioms Lime.numEnd_jemitOTail
#print axioms Lime.jval_minus
#print axioms Lime.notDigitStart_renderExp
#print axioms Lime.notDigitStart_renderFrac
#print axioms Lime.jexpAfter_digit
#print axioms Lime.jexp_renderExp
#print axioms Lime.jfrac_renderFrac
#print axioms Lime.jreadDec_renderU
#print axioms Lime.jval_render
#print axioms Lime.JVal.ofDec_plain
#print axioms Lime.JVal.ofDec_dec
#print axioms Lime.jemit_num_is_render
#print axioms Lime.jdigits_split
#print axioms Lime.jfins_length
#print axioms Lime.jparseNat_consumes
#print axioms Lime.jfrac_length
#print axioms Lime.jexpDigits_length
#print axioms Lime.jexp_length
#print axioms Lime.jreadDec_length
#print axioms Lime.jnumber_length
#print axioms Lime.jnumber_ne_outOfFuel
#print axioms Lime.jparse_reads_a_plain_numeral_as_num
#print axioms Lime.jparse_reads_a_signed_decimal_as_dec
#print axioms Lime.jparse_reads_an_exponent_as_written
#print axioms Lime.jparse_refuses_a_numeral_missing_a_digit
#print axioms Lime.the_jval_jemit_fraction_guard_bites
#print axioms Lime.a_request_number_that_is_not_a_nat_is_refused_by_its_reader
#print axioms Lime.respond_reads_a_decimal_and_a_surrogate_pair

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B1 (design §14.2, §5.2, §6.1 kernel side, §6.3):
-- instants, offsets and chrono's leap-second durations; the zone as a host-probed table
-- (`offsetAt`, `localDate`); `instantOf`, the fork's `local_dt`.  Cal.lean.  64 theorems,
-- including the two in-step goals of design §15 (`offsetAt_reads_the_last_transition`, restated
-- in chrono's order, and `instantOf_is_local_dt_on_an_unambiguous_time`).
#print axioms Lime.Cal.Instant.lt_iff
#print axioms Lime.Cal.Instant.le_iff
#print axioms Lime.Cal.Instant.lt_irrefl
#print axioms Lime.Cal.Instant.lt_trans
#print axioms Lime.Cal.Instant.not_lt
#print axioms Lime.Cal.Instant.le_total
#print axioms Lime.Cal.Instant.le_antisymm
#print axioms Lime.Cal.the_instant_order_is_not_the_nanos_order
#print axioms Lime.Cal.Instant.lt_iff_nanos_off_a_leap_second
#print axioms Lime.Cal.localSecAt_utcSecAt
#print axioms Lime.Cal.utcSecAt_localSecAt
#print axioms Lime.Cal.minutesBetween_is_num_minutes_max_zero
#print axioms Lime.Cal.subMinutes_zero
#print axioms Lime.Cal.subMinutes_nanos
#print axioms Lime.Cal.subMinutes_wf
#print axioms Lime.Cal.durationBetween_across_a_leap_second
#print axioms Lime.Cal.the_leap_second_counts_within_a_day_but_not_across_midnight
#print axioms Lime.Cal.minutesBetween_truncates
#print axioms Lime.Cal.secondsBetween_truncates_toward_zero
#print axioms Lime.Cal.durationBetween_total
#print axioms Lime.Cal.minutesBetween_zero_of_le
#print axioms Lime.Cal.mkInstant?_isSome_iff
#print axioms Lime.Cal.mkInstant?_refuses_a_bad_nanosecond
#print axioms Lime.Cal.mkOffset?_isSome_iff
#print axioms Lime.Cal.mkOffset?_refuses_a_whole_day
#print axioms Lime.Cal.the_written_clock_is_not_the_instant_order
#print axioms Lime.Cal.the_origin_second_is_not_unambiguous
#print axioms Lime.Cal.transFrom_mem
#print axioms Lime.Cal.transFrom_tail
#print axioms Lime.Cal.Tz.transFrom
#print axioms Lime.Cal.Tz.trans_ns
#print axioms Lime.Cal.tz_transitions_strictly_increase
#print axioms Lime.Cal.mkTz?_isSome_iff
#print axioms Lime.Cal.mkTz?_refuses_a_long_key
#print axioms Lime.Cal.mkTz?_refuses_too_many_transitions
#print axioms Lime.Cal.mkTz?_refuses_an_unsorted_table
#print axioms Lime.Cal.offsetFold_none
#print axioms Lime.Cal.offsetFold_last
#print axioms Lime.Cal.offsetAt_reads_the_last_transition
#print axioms Lime.Cal.offsetAt_before_every_transition
#print axioms Lime.Cal.offsetAt_at_a_transition
#print axioms Lime.Cal.offsetAt_does_not_read_the_last_transition_by_nanos
#print axioms Lime.Cal.offsetAt_wf
#print axioms Lime.Cal.localDate_near_the_utc_date
#print axioms Lime.Cal.foldl_offsetStep_congr
#print axioms Lime.Cal.offsetAt_is_constant_between_transitions
#print axioms Lime.Cal.localDate_mono_between_transitions
#print axioms Lime.Cal.pushHit_reverse
#print axioms Lime.Cal.hitFold
#print axioms Lime.Cal.localHits_eq
#print axioms Lime.Cal.spansFrom_lo
#print axioms Lime.Cal.offsetFold_span
#print axioms Lime.Cal.exists_span
#print axioms Lime.Cal.localSec_of_mem_localHits
#print axioms Lime.Cal.mem_localHits_of_localSec
#print axioms Lime.Cal.localSec_instantOf
#print axioms Lime.Cal.instantOf_is_local_dt_on_an_unambiguous_time
#print axioms Lime.Cal.chicago2026_wf
#print axioms Lime.Cal.the_witness_seconds_are_the_dates_they_name
#print axioms Lime.Cal.chicago_2026_offsets
#print axioms Lime.Cal.localDate_is_not_constant_between_transitions
#print axioms Lime.Cal.instantOf_in_the_spring_gap
#print axioms Lime.Cal.instantOf_in_the_fall_fold
#print axioms Lime.Cal.instantOf_on_an_unambiguous_noon

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L2 (design §13.3, §14.8 row L2): the day's
-- window, E7, in real seconds; the two STAGE 6 E7 goals discharged in Lookahead.lean
-- (restated to overlap semantics and refuted as written), and the plan's walls.
#print axioms Lime.Look.wallOverlap_eq_countIn
#print axioms Lime.Look.countIn_of_le
#print axioms Lime.Look.countIn_succ
#print axioms Lime.Look.countIn_congr
#print axioms Lime.Look.countIn_or
#print axioms Lime.Look.countIn_wall
#print axioms Lime.Look.countIn_zero
#print axioms Lime.Look.covered_cons
#print axioms Lime.Look.covered_eq_true
#print axioms Lime.Look.countIn_covered_nil
#print axioms Lime.Look.WallChain.tail
#print axioms Lime.Look.extend_ge
#print axioms Lime.Look.extendStep_pos
#print axioms Lime.Look.extendStep_neg
#print axioms Lime.Look.countIn_covered_cons
#print axioms Lime.Look.extend_least
#print axioms Lime.Look.extend_solves
#print axioms Lime.Look.mergeStep_spec
#print axioms Lime.Look.foldl_mergeStep_spec
#print axioms Lime.Look.covered_reverse
#print axioms Lime.Look.mergeSorted_spec
#print axioms Lime.Look.insertByStart_perm
#print axioms Lime.Look.insertByStart_sorted
#print axioms Lime.Look.sortByStart_perm
#print axioms Lime.Look.sortByStart_sorted
#print axioms Lime.Look.mergeSort_start_sorted
#print axioms Lime.Look.clipWalls_mem
#print axioms Lime.Look.covered_clipWalls
#print axioms Lime.Look.covered_perm
#print axioms Lime.Look.walk_is_the_least_solution
#print axioms Lime.Look.the_window_end_solves_the_equation
#print axioms Lime.Look.windowEnd_le_of_prefixpoint
#print axioms Lime.Look.the_window_end_is_the_least_solution
#print axioms Lime.Look.windowEnd_eq_windowEndFast
#print axioms Lime.Look.windowBase_le_windowEnd
#print axioms Lime.Look.arrival_le_windowEnd
#print axioms Lime.Look.windowEnd_without_walls
#print axioms Lime.Look.the_window_end_is_not_the_least_solution_over_walls_wholly_inside
#print axioms Lime.Look.the_window_end_is_not_the_least_solution_as_stage_6_wrote_it
#print axioms Lime.Look.the_window_base_is_clamped_to_the_arrival
#print axioms Lime.Look.a_wall_begun_before_the_arrival_extends_the_window
#print axioms Lime.Look.the_window_end_does_not_solve_the_equation_as_stage_6_wrote_it
#print axioms Lime.Look.overlapping_walls_count_once
#print axioms Lime.Look.budgetOf_denotes
#print axioms Lime.Look.window_and_budget_on_witnesses
#print axioms Lime.Look.instantOf_ns
#print axioms Lime.Look.windowOn_solves_E7
#print axioms Lime.Look.the_witness_days_are_the_dates_they_name
#print axioms Lime.Look.budget_of_an_eight_hour_window
#print axioms Lime.Look.walls_extend_the_window
#print axioms Lime.Look.the_cap_bounds_the_window
#print axioms Lime.Look.wall_extension_reaches_a_fixed_point
#print axioms Lime.Look.the_window_counts_real_hours_across_the_spring_transition
#print axioms Lime.Look.shiftBack_zero
#print axioms Lime.Look.mem_wallsOn
#print axioms Lime.Look.mem_wallIndex
#print axioms Lime.Look.wallOfEntity_settled
#print axioms Lime.Look.wallOfEntity_interval
#print axioms Lime.Look.the_buffer_is_taken_off_the_local_clock
#print axioms Lime.Look.a_multi_day_wall_puts_one_evening_in_two_windows

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L3 (design §13.3, §14.8 row L3): the slot cut,
-- fork `free_intervals` and `cut_slots_around`, in whole seconds, pulled from stage 6 under D12;
-- the four `cutSlots_*` laws of the step row in-step, and the fork's tests as witnesses.
#print axioms Lime.Look.insertByStart_append
#print axioms Lime.Look.sortByStart_eq_mergeSort
#print axioms Lime.Look.sortByStart_eq_sortByStartFast
#print axioms Lime.Look.clipTo_mem
#print axioms Lime.Look.covered_clipTo
#print axioms Lime.Look.freeChain_spec
#print axioms Lime.Look.freeFold_spec
#print axioms Lime.Look.mem_ite_cons
#print axioms Lime.Look.freeIntervals_spec
#print axioms Lime.Look.freeIntervals_inside_the_window
#print axioms Lime.Look.freeIntervals_are_in_order
#print axioms Lime.Look.freeIntervals_are_the_free_units
#print axioms Lime.Look.cutStretch_fuel
#print axioms Lime.Look.cutSlots_fuel_is_enough
#print axioms Lime.Look.cutStretch_rec
#print axioms Lime.Look.minLast_pos
#print axioms Lime.Look.AccInv.mono
#print axioms Lime.Look.AccInv.nil
#print axioms Lime.Look.cutStretch_spec
#print axioms Lime.Look.cutFold_spec
#print axioms Lime.Look.cutSlots_spec
#print axioms Lime.Look.cutSlots_without_a_block_length_is_empty
#print axioms Lime.Look.cutSlots_inside_the_window
#print axioms Lime.Look.cutSlots_breaks_inside_the_window
#print axioms Lime.Look.cutSlots_avoid_the_walls
#print axioms Lime.Look.cutSlots_breaks_avoid_the_walls
#print axioms Lime.Look.cutSlots_block_is_block_min
#print axioms Lime.Look.cutSlots_short_block_is_at_least_min_last
#print axioms Lime.Look.cutSlots_break_is_break_min
#print axioms Lime.Look.cutSlots_slots_are_in_order
#print axioms Lime.Look.cutSlots_breaks_are_in_order
#print axioms Lime.Look.cutSlots_no_slot_overlaps_a_break
#print axioms Lime.Look.every_break_is_followed_by_a_slot
#print axioms Lime.Look.cut_slots_on_the_spec_day
#print axioms Lime.Look.a_routine_passed_as_a_wall_does_not_pay_off_the_break
#print axioms Lime.Look.cut_slots_around_a_placed_routine
#print axioms Lime.Look.cut_slots_from_a_pending_break
#print axioms Lime.Look.a_cut_never_ends_on_a_break
#print axioms Lime.Look.a_long_wall_leaves_eight_hours_to_cut
#print axioms Lime.Look.a_late_arrival_cuts_nothing
#print axioms Lime.Look.free_intervals_merge_overlapping_walls
#print axioms Lime.Look.a_cut_counts_real_minutes_across_the_fall_transition

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L4 (design §13.3, §14.8 row L4): energy and the
-- budget limit, fork `hours_since_wake`/`bucket`/`StepFn::at`/`prior_energy`/`prior_level`/`predict`/
-- `cap_for_location`/`energize`/`limit_to_budget`, pulled from stage 6 under D12; site R11, the four
-- goals of the step row in-step (`limitSlots_is_limitHist` equal to L1's `limitHist`), and the fork's
-- tests as witnesses.
#print axioms Lime.Look.hsw100_is_round_half_away
#print axioms Lime.Look.hsw100_nearest
#print axioms Lime.Look.hsw100_mono
#print axioms Lime.Look.hsw100_withinOne
#print axioms Lime.Look.bucket_mono
#print axioms Lime.Look.futureEnergy_home_is_capped
#print axioms Lime.Look.futureEnergy_lounge_is_the_prediction
#print axioms Lime.Look.foldl_levelStep
#print axioms Lime.Look.histOf'_cons
#print axioms Lime.Look.histOf'_of_below
#print axioms Lime.Look.histOf'_perm
#print axioms Lime.Look.topElig_bump
#print axioms Lime.Look.topElig_of_zero_above
#print axioms Lime.Look.limitHist_eq
#print axioms Lime.Look.greedy_spec
#print axioms Lime.Look.limitSlots_is_limitHist
#print axioms Lime.Look.limitSlots_eq_limitSlotsFast
#print axioms Lime.Look.sum6_bump
#print axioms Lime.Look.foldl_add_minutes
#print axioms Lime.Look.sum6_histOf'
#print axioms Lime.Look.dayHist_eq
#print axioms Lime.Look.dayHist_keeps_the_min
#print axioms Lime.Look.dayHist_home_is_capped
#print axioms Lime.Look.hsw100_on_witnesses
#print axioms Lime.Look.the_bucket_reads_seconds
#print axioms Lime.Look.the_bucket_reads_seconds_on_the_spec_day
#print axioms Lime.Look.buckets_clamp
#print axioms Lime.Look.prior_energy_lookup
#print axioms Lime.Look.predict_matches_the_prior_tables_at_boundaries
#print axioms Lime.Look.predict_falls_back_to_the_prior
#print axioms Lime.Look.predict_uses_the_learned_curve
#print axioms Lime.Look.a_curve_falls_back_as_the_config_does
#print axioms Lime.Look.energize_follows_the_prior_curve
#print axioms Lime.Look.energize_applies_the_home_cap
#print axioms Lime.Look.a_future_tuesday_keeps_its_budget
#print axioms Lime.Look.the_learned_curve_moves_an_hour_on_sunday
#print axioms Lime.Look.hours_since_wake_count_real_hours_across_the_fall_transition

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B2 (design §14.2, §5.3): the log's timestamps,
-- chrono's RFC 3339 reader and its fallback (`parseStamp`), `fmt_timestamp` (`renderStamp`), the
-- `lime log` column (`displayStamp`) and chrono's stamp order (`stampBefore`).  Stamp.lean, namespace
-- `Lime.LogStamp`.  22 theorems, including the in-step `parseStamp_renderStamp` (restated with a
-- year bound; `parseStamp_renderStamp_fails_past_year_9999` refutes it as §15 writes it) and the
-- order witness `stamp_order_is_the_instant_order`.
#print axioms Lime.LogStamp.stampBefore_iff
#print axioms Lime.LogStamp.stampBefore_ignores_the_offset
#print axioms Lime.LogStamp.stampBefore_irrefl
#print axioms Lime.LogStamp.renderOffset_length
#print axioms Lime.LogStamp.rfcOffset_renderOffset
#print axioms Lime.LogStamp.year_of_a_day_before_the_end
#print axioms Lime.LogStamp.dateBase_renderDate
#print axioms Lime.LogStamp.renderDate_length
#print axioms Lime.LogStamp.localDateTod_spec
#print axioms Lime.LogStamp.fracOf_renderOffset
#print axioms Lime.LogStamp.rfc3339_renderStamp
#print axioms Lime.LogStamp.parseStamp_renderStamp_before_year_10000
#print axioms Lime.LogStamp.parseStamp_renderStamp_fails_past_year_9999
#print axioms Lime.LogStamp.renderStamp_is_fmt_timestamp
#print axioms Lime.LogStamp.renderStamp_writes_a_leap_second_as_60
#print axioms Lime.LogStamp.displayStamp_is_the_written_clock
#print axioms Lime.LogStamp.the_origin_west_of_utc_is_year_zero
#print axioms Lime.LogStamp.stamp_order_is_the_instant_order
#print axioms Lime.LogStamp.a_leap_second_stamp_is_before_the_next_second
#print axioms Lime.LogStamp.parseStamp_reads_the_rfc3339_spellings
#print axioms Lime.LogStamp.parseStamp_reads_the_fallback
#print axioms Lime.LogStamp.parseStamp_refuses_what_is_not_a_stamp

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B3 (design §14.2, §5.4–§5.6): the typed event grammar
-- of `.tm/log.jsonl` in Log.lean (new; namespace `Lime.Log`) — 26 known kinds and `unknown`, `readLine`,
-- `renderLine`, serde's `finiteF64`, the small grammars — and `digitsOf`'s runtime twin in Text.lean
-- (README gap 101, closed).  107 theorems: 2 in Text.lean, 105 in Log.lean, including the four goals
-- §15 names for B3 (`the_log_reads_what_it_renders`, `a_known_event_is_never_read_as_unknown`,
-- `an_unknown_tag_is_never_a_warning`, `lineTooLong_bounds_every_string`), added and discharged in
-- this step, so Goals.lean never held them.
#print axioms Lime.digitsOfTR_go
#print axioms Lime.digitsOf_eq_digitsOfTR
#print axioms Lime.Log.lastVal_go
#print axioms Lime.Log.lastVal_cons
#print axioms Lime.Log.lastVal_append
#print axioms Lime.Log.lastVal_nil
#print axioms Lime.Log.lastVal_of_not_mem
#print axioms Lime.Log.lastVal_mem
#print axioms Lime.Log.allStrs_map
#print axioms Lime.Log.readF_renderF
#print axioms Lime.Log.readArgs_of_agrees
#print axioms Lime.Log.renderArgs_keys
#print axioms Lime.Log.agrees_renderArgs
#print axioms Lime.Log.Kind.build_of_split
#print axioms Lime.Log.Event.tag_of_split
#print axioms Lime.Log.Event.fields_of_split
#print axioms Lime.Log.Event.strings_of_split
#print axioms Lime.Log.Event.canonical_of_split
#print axioms Lime.Log.Event.split_build
#print axioms Lime.Log.Event.split_of_not_unknown
#print axioms Lime.Log.kindOf_tag
#print axioms Lime.Log.Kind.keys_nodup
#print axioms Lime.Log.Kind.no_t_key
#print axioms Lime.Log.Kind.no_ev_key
#print axioms Lime.Log.finiteF64_of_nat
#print axioms Lime.Log.allFiniteL_map_str
#print axioms Lime.Log.allFiniteO_append
#print axioms Lime.Log.u32_le_u64Max
#print axioms Lime.Log.u8_le_u64Max
#print axioms Lime.Log.allFiniteO_renderArgs
#print axioms Lime.Log.jemitOTail_ends
#print axioms Lime.Log.jemit_obj_ends
#print axioms Lime.Log.trimCR_of_last
#print axioms Lime.Log.trimCR_jemit_obj
#print axioms Lime.Log.not_blank_jemit_obj
#print axioms Lime.Log.charsLt_irrefl
#print axioms Lime.Log.charsLe_of_lt
#print axioms Lime.Log.ne_of_charsLt
#print axioms Lime.Log.dedup_of_pairwise
#print axioms Lime.Log.restOf_canonical
#print axioms Lime.Log.countP_of_not_mem
#print axioms Lime.Log.stamp_hyps
#print axioms Lime.Log.readT_line
#print axioms Lime.Log.lastVal_ev_line
#print axioms Lime.Log.readLine_of_parse
#print axioms Lime.Log.keys_of_fields_known
#print axioms Lime.Log.keys_of_rest
#print axioms Lime.Log.the_log_reads_what_it_renders
#print axioms Lime.Log.a_known_event_is_never_read_as_unknown
#print axioms Lime.Log.trimCR_prefix
#print axioms Lime.Log.scan_peak_mono
#print axioms Lime.Log.depthOf_prefix
#print axioms Lime.Log.skipWs_suffix
#print axioms Lime.Log.jparse_not_blank
#print axioms Lime.Log.an_unknown_tag_is_never_a_warning
#print axioms Lime.Log.map_cons_ok
#print axioms Lime.Log.junescape_length
#print axioms Lime.Log.jscan_strlen
#print axioms Lime.Log.jstring_strlen
#print axioms Lime.Log.jstrs_ofDec
#print axioms Lime.Log.jstrsO_cons
#print axioms Lime.Log.jval_strs_step
#print axioms Lime.Log.jarr_strs_step
#print axioms Lime.Log.jtail_strs_step
#print axioms Lime.Log.jobj_strs_step
#print axioms Lime.Log.jpair_strs_step
#print axioms Lime.Log.jotail_strs_step
#print axioms Lime.Log.jparser_strs
#print axioms Lime.Log.jparse_strs
#print axioms Lime.Log.FR.pair_ok
#print axioms Lime.Log.mem_jstrsO_of_mem
#print axioms Lime.Log.jstrsO_sub
#print axioms Lime.Log.allStrs_mem
#print axioms Lime.Log.readF_strs
#print axioms Lime.Log.readArgs_strs
#print axioms Lime.Log.dedupStep_sub
#print axioms Lime.Log.restOf_sub
#print axioms Lime.Log.readLine_entry_inv
#print axioms Lime.Log.lineTooLong_bounds_every_string
#print axioms Lime.Log.digitsValue_ge
#print axioms Lime.Log.capExp_none
#print axioms Lime.Log.capExp_fold
#print axioms Lime.Log.finiteF64_reads_only_the_sign_past_an_i32_exponent
#print axioms Lime.Log.readF_refuses_a_u8_past_255
#print axioms Lime.Log.readF_refuses_a_u32_past_its_width
#print axioms Lime.Log.readF_refuses_a_decimal_at_an_integer_field
#print axioms Lime.Log.readF_reads_hsw_as_written
#print axioms Lime.Log.readLine_refuses_a_line_past_the_bound
#print axioms Lime.Log.readLine_refuses_a_line_nested_past_the_bound
#print axioms Lime.Log.readLine_refuses_a_line_that_is_not_utf8
#print axioms Lime.Log.malformed_line_1_is_a_wake
#print axioms Lime.Log.malformed_line_2_is_not_json
#print axioms Lime.Log.malformed_line_3_is_a_wake_without_slept_min
#print axioms Lime.Log.malformed_line_4_has_no_t
#print axioms Lime.Log.malformed_line_5_is_a_done_with_est_min_sixty
#print axioms Lime.Log.malformed_line_6_has_a_t_that_is_not_a_stamp
#print axioms Lime.Log.malformed_line_7_is_an_array
#print axioms Lime.Log.malformed_line_8_is_blank
#print axioms Lime.Log.malformed_line_9_is_an_unknown_mood
#print axioms Lime.Log.malformed_line_10_has_an_ev_that_is_not_a_string
#print axioms Lime.Log.malformed_line_11_is_a_note
#print axioms Lime.Log.the_malformed_corpus_reads_as_the_fork_point_did
#print axioms Lime.Log.an_out_of_range_numeral_warns_even_in_an_unknown_event
#print axioms Lime.Log.every_line_warning_is_reachable
#print axioms Lime.Log.finiteF64_is_serdes_band
#print axioms Lime.Log.the_small_grammars_read_as_the_fork_does

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step B4 (design §14.2 row B4, §6.1, §10): the `tz` and
-- `log` sections of the request in Boundary.lean — `readTz` (the zone table Rust probes, built only
-- by `Cal.mkTz?`), `readLogReq` and `mkLogReq?` (R10), `logAnswer` (lines, warnings, headers with tag
-- and id, render) and `runWithLog`, which `respond` now calls.  31 theorems, all in Boundary.lean;
-- `the_response_shapes_emit_in_build_order` is extended in place (already audited above).
#print axioms Lime.run_ok_shape
#print axioms Lime.runPlan_ok_shape
#print axioms Lime.runWithLog_without_a_log_is_run
#print axioms Lime.a_request_without_tz_or_log_is_read_as_before
#print axioms Lime.runWithLog_refuses_a_log_section_first
#print axioms Lime.runWithLog_puts_the_log_after_the_report
#print axioms Lime.readStep_fold
#print axioms Lime.logVerdicts_eq
#print axioms Lime.mkLogReq?_ok_iff
#print axioms Lime.mkLogReq?_keeps_the_request
#print axioms Lime.mkLogReq?_error_is_the_fault
#print axioms Lime.mkLogReq?_refuses_a_from_of_zero_or_past_2_40
#print axioms Lime.mkLogReq?_refuses_too_many_lines
#print axioms Lime.mkLogReq?_refuses_headersFrom_past_2_40
#print axioms Lime.mkLogReq?_refuses_too_many_render_lines
#print axioms Lime.LogReq.wf_bounds
#print axioms Lime.mkLogReq?_refuses_a_render_line_outside_the_tail
#print axioms Lime.readTz_refuses_a_long_key
#print axioms Lime.readTz_refuses_too_many_transitions
#print axioms Lime.readLogReq_refuses_more_lines_than_the_bound
#print axioms Lime.lineStep_error
#print axioms Lime.lineStep_fold
#print axioms Lime.readLogReq_reads_the_lines_as_sent
#print axioms Lime.LogReq.wf_render_in_tail
#print axioms Lime.logAnswer_renders_the_line_at_its_number
#print axioms Lime.readTzOffset_reads_the_table_spelling
#print axioms Lime.readTzInstant_reads_utc_whole_seconds
#print axioms Lime.readTz_reads_the_witness_table
#print axioms Lime.readTz_refuses_by_name
#print axioms Lime.the_log_op_reads_a_four_line_tail
#print axioms Lime.the_log_section_refuses_by_name

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L5 (design §13.4, §14.8 row L5): the lookahead, fork
-- `capacity::lookahead` with D10's mixture; `mkInput?` (R10, the model-then-config fallbacks of D10-4),
-- a future day's wake through `local_dt` at second resolution (`wakeInstantOf`), `pureDay`, `dayOf` held
-- once (`@[csimp] dayOf_eq_dayOfFast`), the §15 laws in-step, the twin, and the loaded-plan witness in
-- Boundary.lean through `wallIndex`.
#print axioms Lime.Look.WakeClock.ofClock_wf
#print axioms Lime.Look.wakeInstantOf_ofClock
#print axioms Lime.Look.wakeInstantOf_on_an_unambiguous_time
#print axioms Lime.Look.mkInput?_refuses_too_many_days
#print axioms Lime.Look.pureDay_is_dayHist
#print axioms Lime.Look.Six.get_of
#print axioms Lime.Look.locSix_get
#print axioms Lime.Look.dayOf_eq_dayOfFast
#print axioms Lime.Look.foldl_cons_map
#print axioms Lime.Look.lookahead_eq_map
#print axioms Lime.Look.dayOf_day
#print axioms Lime.Look.lookahead_keeps_the_days
#print axioms Lime.Look.lookahead_dates
#print axioms Lime.Look.lookahead_getElem?
#print axioms Lime.Look.daysAscending_range'
#print axioms Lime.Look.lookahead_is_a_lookahead
#print axioms Lime.Look.lookahead_entry
#print axioms Lime.Look.lookahead_day_zero_is_the_kernels
#print axioms Lime.Look.lookahead_future_day_is_the_mixture
#print axioms Lime.Look.lookahead_between_the_locations
#print axioms Lime.Look.lookahead_at_a_certain_weight_is_the_pure_location
#print axioms Lime.Look.the_twin_forces_the_forks_location
#print axioms Lime.Look.pureDay_le_budget
#print axioms Lime.Look.lookahead_future_day_width
#print axioms Lime.Look.weightsOf?_ok
#print axioms Lime.Look.weightsOf?_of_ok
#print axioms Lime.Look.mkInput?_ok_elim
#print axioms Lime.Look.mkInput?_weight_is_the_model_then_config
#print axioms Lime.Look.mkInput?_arrival_and_wake
#print axioms Lime.Look.mkInput?_days_le
#print axioms Lime.Look.mkInput?_refuses_a_bad_weight
#print axioms Lime.Look.mkInput?_refuses_a_bad_wake
#print axioms Lime.Look.mkInput?_refuses_a_now_that_disagrees
#print axioms Lime.Look.mkInput?_accepts
#print axioms Lime.Look.wakeOf_without_a_logged_wake_is_wf
#print axioms Lime.Look.lookahead_is_the_expected_minutes
#print axioms Lime.Look.wakeInstantOf_on_witnesses
#print axioms Lime.Look.a_future_day_reads_todays_wake_to_the_second
#print axioms Lime.Look.the_twin_follows_the_learned_arrival_and_location
#print axioms Lime.Look.the_expected_tuesday
#print axioms Lime.Look.mkInput?_on_witnesses
#print axioms Lime.Look.sunday_mixes_at_its_own_weight
#print axioms Lime.Look.a_wednesday_wall_moves_the_window_and_keeps_the_budget
#print axioms Lime.the_look_wall_witness_loads
#print axioms Lime.the_look_wall_calendar_indexes_one_wednesday_wall
#print axioms Lime.a_loaded_wednesday_wall_moves_the_window_and_keeps_the_budget

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L6 (design §13.6, §10.4, §14.8 row L6): capacity on
-- the wire.  Lookahead.lean: every §13.6 bound mkInput? does not check, with its smart constructor and
-- rejection theorems (mkDayCfg?, mkStep?, curveOk, priorOk, energyOk, homeMaxOk).  Boundary.lean: `run`
-- split at runLoad, the `capacity` and `tz` readers (CapWire), runCap / respondCap / callCap with the
-- export moved to them, the bridge to `run` and `call`, what an answered request satisfies, and the
-- decided witnesses.  Gap 77 closed.
#print axioms Lime.Look.mkDayCfg?_wf
#print axioms Lime.Look.mkDayCfg?_of_wf
#print axioms Lime.Look.mkDayCfg?_refuses_blockMin
#print axioms Lime.Look.mkDayCfg?_refuses_breakMin
#print axioms Lime.Look.mkDayCfg?_refuses_breakAfterBlocks
#print axioms Lime.Look.mkDayCfg?_refuses_minLastBlockMin
#print axioms Lime.Look.mkDayCfg?_refuses_windowHours
#print axioms Lime.Look.mkDayCfg?_refuses_budgetRatio
#print axioms Lime.Look.DayCfg.wf_window_le_a_day
#print axioms Lime.Look.mkStep?_ok_iff
#print axioms Lime.Look.mkStep?_refuses_a_zero_denominator
#print axioms Lime.Look.mkStep?_refuses_a_wide_denominator
#print axioms Lime.Look.mkStep?_refuses_past_48_hours
#print axioms Lime.Look.mkStep?_refuses_an_empty_range
#print axioms Lime.Look.mkStep?_refuses_a_level_above_five
#print axioms Lime.Look.curveOk_refuses_too_many_ranges
#print axioms Lime.Look.curveOk_refuses_a_bad_range
#print axioms Lime.Look.curveOk_refuses_an_unsorted_curve
#print axioms Lime.Look.priorOk_refuses_too_many_curves
#print axioms Lime.Look.priorOk_refuses_a_long_key
#print axioms Lime.Look.priorOk_refuses_a_key_twice
#print axioms Lime.Look.priorOk_refuses_a_bad_curve
#print axioms Lime.Look.energyOk_refuses_a_curve_not_of_12
#print axioms Lime.Look.energyOk_refuses_an_entry_past_a_byte
#print axioms Lime.Look.homeMaxOk_iff
#print axioms Lime.Look.priorOk_widths
#print axioms Lime.Look.priorOk_keys_in_the_exact_domain
#print axioms Lime.Look.the_shipped_bounds_hold
#print axioms Lime.run_is_runLoad_then_runPlan
#print axioms Lime.capBind_ok_elim
#print axioms Lime.runCap_without_capacity_is_run
#print axioms Lime.respondCap_without_capacity_is_respond
#print axioms Lime.callExport_without_capacity_is_call
#print axioms Lime.the_exported_call_emits_parses_back
#print axioms Lime.runCap_answers_with_the_lookahead
#print axioms Lime.runCap_refuses_what_the_section_refuses
#print axioms Lime.runPlan_ok_is_docs_then_report
#print axioms Lime.runCap_answers_docs_report_lookahead
#print axioms Lime.CapWire.unitsJson_reads_back
#print axioms Lime.CapWire.lookaheadJson_days
#print axioms Lime.CapWire.readWeight_ok
#print axioms Lime.CapWire.readWeekAll_ok
#print axioms Lime.CapWire.readWeekOpt_ok
#print axioms Lime.CapWire.orErr_ok
#print axioms Lime.CapWire.mapError_ok
#print axioms Lime.CapWire.readModelTable_ok
#print axioms Lime.CapWire.readTables_ok
#print axioms Lime.CapWire.readEnergyCurve_ok
#print axioms Lime.CapWire.readEnergy_ok
#print axioms Lime.CapWire.readCurve_ok
#print axioms Lime.CapWire.readPrior_ok
#print axioms Lime.CapWire.readHomeMax_ok
#print axioms Lime.CapWire.mkDayCfg?_blockMin
#print axioms Lime.CapWire.readDay_ok
#print axioms Lime.CapWire.readPriority_ok
#print axioms Lime.CapWire.readSection_ok
#print axioms Lime.CapWire.readCapacity_ok
#print axioms Lime.CapWire.the_zone_texts_read_on_witnesses
#print axioms Lime.CapWire.readTz_on_witnesses
#print axioms Lime.CapWire.readWeight_on_witnesses
#print axioms Lime.CapWire.readDay_on_witnesses
#print axioms Lime.CapWire.readPrior_on_witnesses
#print axioms Lime.CapWire.readEnergy_on_witnesses
#print axioms Lime.CapWire.readPriority_on_witnesses
#print axioms Lime.CapWire.the_capacity_section_reads_the_corpus_model
#print axioms Lime.CapWire.the_lookahead_response_emits_in_build_order
#print axioms Lime.CapWire.runCap_reads_the_corpus_request
#print axioms Lime.CapWire.jget_pairJ
#print axioms Lime.CapWire.natOfDigits_digitsOf
#print axioms Lime.CapWire.pairWith_digits
#print axioms Lime.CapWire.readWeight_reads_every_representable_weight
#print axioms Lime.CapWire.readWeight_refuses_more_than_18_places
#print axioms Lime.CapWire.readHomeMax_on_the_bound
#print axioms Lime.CapWire.readTz_refuses_too_many_transitions

-- APPENDED 2026-09-14 (merge of rebuild-on-lean's D9 B2-B4 into stage5-lookahead's D10 L5-L6).
-- `runCap` now composes B4's `log` section (`logInto`), so the bridge to the old entry point is
-- restated over `runWithLog`; the L6 name `runPlan_ok_shape` collided with B4's and was renamed
-- `runPlan_ok_is_docs_then_report` in place above.  L6's second `tz` reader is gone (gap 108):
-- `CapWire.readTz_on_witnesses`, `CapWire.the_zone_texts_read_on_witnesses` and
-- `CapWire.readTz_refuses_too_many_transitions` are re-proved over B4's `readTz` (audited above).
#print axioms Lime.runCap_without_capacity_is_runWithEmit
#print axioms Lime.runCap_refuses_a_log_section_first
#print axioms Lime.runCap_answers_docs_report_log_lookahead

-- APPENDED 2026-09-14 (stage 5, W-2 repair).  The audit's two minors: B2's narrowed stamp round
-- trip is renamed `Lime.LogStamp.parseStamp_renderStamp_before_year_10000` (its B2 line above is
-- edited in place, since the old name no longer exists; the refutation keeps its line), and B4's
-- 142-character `log` conjunct is split into three conjuncts of at most 52 characters, composed by
-- the new `withLog_jone`.  `malformedLine5` is spelled pair by pair (no new theorem).
#print axioms Lime.withLog_jone

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, kernel half (design §13.6, §13.8): the grants
-- on the wire (gaps 80, 107), EDF compiled linear (gap 106), one zone reading (gap 110), and capacity
-- refused beside commands (gap 109).  Three existing statements gained hypotheses for the new wire
-- (`runCap_answers_with_the_lookahead`, `runCap_answers_docs_report_lookahead`,
-- `runCap_answers_docs_report_log_lookahead`: no candidates, no commands); their audit lines stand above.
#print axioms Lime.NumSix.get_of
#print axioms Lime.availUntil_foldl
#print axioms Lime.availUntil_eq_availUntilFast
#print axioms Lime.reserveRestAcc_eq
#print axioms Lime.edfStepFast_foldl
#print axioms Lime.edfGrantsGo_eq_edfGrantsGoFast
#print axioms Lime.edfCaps_eq_edfCapsFast
#print axioms Lime.reserveRest_eq_reserveRestFast
#print axioms Lime.reserveOut_eq_reserveOutFast
#print axioms Lime.Look.enterOf_eq_some
#print axioms Lime.Look.mem_entering
#print axioms Lime.Look.insertDueIx_snd
#print axioms Lime.Look.sortDueIx_snd
#print axioms Lime.Look.perm_insertDueIx
#print axioms Lime.Look.sortDueIx_perm
#print axioms Lime.Look.edfGrantsGo_length
#print axioms Lime.Look.tagGrants_snd
#print axioms Lime.Look.servedGrants_are_the_pass
#print axioms Lime.Look.grantAt_servedGrants
#print axioms Lime.Look.grantAt_none_of_not_enters
#print axioms Lime.Look.grantAt_some_of_enters
#print axioms Lime.Look.priorities_length
#print axioms Lime.Look.priorities_getElem?
#print axioms Lime.Look.an_answer_carries_a_grant_iff_its_candidate_enters
#print axioms Lime.Look.an_answers_grant_reserves_the_min
#print axioms Lime.Look.an_answer_is_off_the_scale_iff_a_wall
#print axioms Lime.Look.finalPrio_of_pressure_hot
#print axioms Lime.Look.a_hot_answer_is_zero
#print axioms Lime.Look.priorities_on_a_witness
#print axioms Lime.readLogSection_is_zoneOf_then_logSectionWith
#print axioms Lime.zoneOf_ok_obj
#print axioms Lime.the_zone_is_read_once_and_feeds_both_sections
#print axioms Lime.runCap_with_capacity_reads_the_zone_once
#print axioms Lime.zoneOf_of_readLogSection
#print axioms Lime.runCap_answers_with_the_lookahead_and_grants
#print axioms Lime.runCap_refuses_what_the_candidates_refuse
#print axioms Lime.runCap_refuses_commands_beside_capacity
#print axioms Lime.an_answered_capacity_request_has_no_commands
#print axioms Lime.runCap_answers_docs_report_lookahead_grants
#print axioms Lime.CapWire.readCands_on_witnesses
#print axioms Lime.CapWire.runCap_refuses_a_command_beside_the_corpus_request
#print axioms Lime.CapWire.the_grant_response_emits_in_build_order

-- APPENDED 2026-09-14 (stage 5, D10 track).  Step L8, host half (design §13.8): the floor pass (gap
-- 79).  One existing statement gained a hypothesis for it (`runCap_answers_docs_report_lookahead_grants`:
-- no candidate carries a floor; its audit line stands above), and
-- `runCap_answers_docs_report_lookahead_floor_grants` states the general answer.
#print axioms Lime.Look.passLeft_is_edf
#print axioms Lime.Look.prioritiesWithFloors_length
#print axioms Lime.Look.prioritiesWithFloors_getElem?
#print axioms Lime.Look.lt_of_priorities_getElem?
#print axioms Lime.Look.prioritiesWithFloors_without_floors
#print axioms Lime.Look.a_floor_reserves_nothing
#print axioms Lime.Look.the_pass_wins_over_a_floor
#print axioms Lime.Look.an_ungranted_floor_is_answered_at_its_floor
#print axioms Lime.Look.a_floor_answer_reads_what_the_pass_left
#print axioms Lime.Look.a_hot_floor_answer_is_zero
#print axioms Lime.Look.prioritiesWithFloors_on_a_witness
#print axioms Lime.Look.prioritiesWithFloors_on_a_roomier_witness
#print axioms Lime.CapWire.grantJsonF_without_a_floor
#print axioms Lime.runCap_answers_docs_report_lookahead_floor_grants
#print axioms Lime.CapWire.readCands_reads_and_refuses_floors
#print axioms Lime.CapWire.the_floor_grant_response_emits_in_build_order

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step C1 (design §7.1, §14.4 row C1): the undo mask in
-- Replay.lean (new) and the `log` op's `facts.cancelled` in Boundary.lean.  The four goals §15 names for
-- C1 were added to Goals.lean and discharged in the step: `survivors_snoc_event`, `survivors_snoc_undo`,
-- `a_cancelled_event_is_never_revived` and `a_dangling_undo_dangles_in_every_extension` (the last
-- without §15's two unneeded hypotheses).  The fast twins are `survivors_eq_survivorsFast` and
-- `cancelledLines_eq_cancelledLinesFast`, both `@[csimp]`.
#print axioms Lime.Log.linesIncreasing_pairwise
#print axioms Lime.Replay.survivors_nil
#print axioms Lime.Replay.survivors_snoc_event
#print axioms Lime.Replay.survivors_snoc_undo
#print axioms Lime.Replay.mem_foldl_maskStep
#print axioms Lime.Replay.not_undo_of_mem_foldl_maskStep
#print axioms Lime.Replay.an_undo_never_survives
#print axioms Lime.Replay.mem_of_mem_survivors
#print axioms Lime.Replay.a_cancelled_event_is_never_revived
#print axioms Lime.Replay.danglingOf_fst_go
#print axioms Lime.Replay.danglingOf_fst
#print axioms Lime.Replay.danglingOf_snd_mono
#print axioms Lime.Replay.a_dangling_undo_dangles_in_every_extension
#print axioms Lime.Replay.an_entry_that_dangles_is_an_undo
#print axioms Lime.Replay.isUndo_of_tag_undo
#print axioms Lime.Replay.no_survivor_matches_an_undo_of_an_undo
#print axioms Lime.Replay.an_undo_of_an_undo_cancels_nothing_in_a_canonical_log
#print axioms Lime.Replay.dangleStep_of_no_match
#print axioms Lime.Replay.an_undo_of_an_undo_dangles_in_a_canonical_log
#print axioms Lime.Replay.maskStepI_map
#print axioms Lime.Replay.foldl_maskStepI_map
#print axioms Lime.Replay.zipIdx_map_fst
#print axioms Lime.Replay.stackI_map
#print axioms Lime.Replay.PosMap.size_set
#print axioms Lime.Replay.PosMap.get_empty
#print axioms Lime.Replay.find?_filter_ne
#print axioms Lime.Replay.PosMap.get_set
#print axioms Lime.Replay.pairKey_inj
#print axioms Lime.Replay.deadAt_set
#print axioms Lime.Replay.filter_dropWhile_cons
#print axioms Lime.Replay.filter_dropWhile_nil
#print axioms Lime.Replay.eraseP_eq_filter_pos
#print axioms Lime.Replay.eraseP_eq_self_of_filter_nil
#print axioms Lime.Replay.Inv.nodup
#print axioms Lime.Replay.filter_kill
#print axioms Lime.Replay.filter_kill1
#print axioms Lime.Replay.filter_pos_ne_comm
#print axioms Lime.Replay.foldl_snoc_maskStepI
#print axioms Lime.Replay.stack_positions_lt
#print axioms Lime.Replay.Inv.step_undo_none
#print axioms Lime.Replay.Inv.posLt_snoc
#print axioms Lime.Replay.Inv.incr_snoc
#print axioms Lime.Replay.Inv.step_undo_some
#print axioms Lime.Replay.maskFastStep_event
#print axioms Lime.Replay.maskStepI_event
#print axioms Lime.Replay.Inv.step_event
#print axioms Lime.Replay.Inv.step
#print axioms Lime.Replay.Inv.init
#print axioms Lime.Replay.maskFast_inv
#print axioms Lime.Replay.maskFast_stack
#print axioms Lime.Replay.cancelledAt_eq_deadAt
#print axioms Lime.Replay.survivors_are_the_uncancelled_entries
#print axioms Lime.Replay.survivors_eq_survivorsFast
#print axioms Lime.Replay.cancelledLines_eq_cancelledLinesFast
#print axioms Lime.Replay.cancelled_and_survivors_partition
#print axioms Lime.Replay.the_mask_ignores_isStateChange
#print axioms Lime.Replay.undo_mask_pairs_and_dangling_ported
#print axioms Lime.Replay.an_undo_of_an_undo_cancels_a_noncanonical_unknown_undo
#print axioms Lime.Replay.an_undo_with_an_id_passes_over_other_ids
#print axioms Lime.readLine_entry_line
#print axioms Lime.filterMap_entryOf_lines
#print axioms Lime.linesIncreasing_of_pairwise
#print axioms Lime.filterMap_entryOf_pairwise
#print axioms Lime.the_tail_entries_have_increasing_lines

-- APPENDED 2026-09-14 (stage 5, D9 track).  Step C2 (design §6.2, §14.4 row C2): the day index in
-- Replay.lean and the `log` op's `facts.days` in Boundary.lean (the request carries its zone,
-- `LogReq.tz`).  The three goals §15 names for C2 were added to Goals.lean restated in chrono's order
-- (carried note 1) and discharged in the step: `dayOf_is_the_wake_date_within_a_day`,
-- `a_wake_day_is_shorter_than_a_day` and `keptWakes_append_of_later`; §15's nanosecond statements are
-- refuted by the three `…_by_nanos_is_refuted`.  Quirk Q6(a): `the_kept_wake_is_not_the_first_logged_wake`
-- and `the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order`.  The fast twins are
-- `sortWakes_eq_sortWakesFast` and `entryDays_eq_entryDaysFast`, both `@[csimp]`.  Two existing
-- Boundary theorems gained the zone argument and keep their audit lines:
-- `readLogReq_refuses_more_lines_than_the_bound`, `readLogReq_reads_the_lines_as_sent`.
#print axioms Lime.Replay.instant_le_trans
#print axioms Lime.Replay.instant_le_refl
#print axioms Lime.Replay.instant_le_of_not_le
#print axioms Lime.Replay.instant_le_of_lt
#print axioms Lime.Replay.instant_not_le_of_lt
#print axioms Lime.Replay.insertWake_perm
#print axioms Lime.Replay.sortWakes_perm
#print axioms Lime.Replay.insertWake_sorted
#print axioms Lime.Replay.sortWakes_sorted
#print axioms Lime.Replay.eq_of_perm_of_sorted
#print axioms Lime.Replay.sortWakes_eq_sortWakesFast
#print axioms Lime.Replay.sortWakes_append_of_later
#print axioms Lime.Replay.foldl_keptStep_acc
#print axioms Lime.Replay.foldl_keptStep_head
#print axioms Lime.Replay.keptWakes_last
#print axioms Lime.Replay.keptWakes_append_of_later
#print axioms Lime.Replay.mem_foldl_keptStep
#print axioms Lime.Replay.mem_of_mem_keptFrom
#print axioms Lime.Replay.foldl_keptStep_sublist
#print axioms Lime.Replay.keptWakes_sorted
#print axioms Lime.Replay.foldl_lastWake_or
#print axioms Lime.Replay.lastWakeLe_cons
#print axioms Lime.Replay.lastWakeLe_le
#print axioms Lime.Replay.lastWakeLe_append_of_later
#print axioms Lime.Replay.dayOf_is_the_wake_date_within_a_day
#print axioms Lime.Replay.dayOf_without_a_recent_wake_is_the_local_date
#print axioms Lime.Replay.a_wake_day_is_shorter_than_a_day
#print axioms Lime.Replay.dayOf_agrees_below_a_later_wake
#print axioms Lime.Replay.an_instant_off_its_own_date_is_within_a_day_of_its_wake
#print axioms Lime.Replay.dedupFrom_append
#print axioms Lime.Replay.dedupFrom_last
#print axioms Lime.Replay.dedupFrom_single
#print axioms Lime.Replay.lastWakeLe_snoc
#print axioms Lime.Replay.lastWakeLe_of_all_le
#print axioms Lime.Replay.lastWakeLe_dedup_same_date
#print axioms Lime.Replay.a_wake_is_on_its_own_date
#print axioms Lime.Replay.find?_congr_mem
#print axioms Lime.Replay.find?_dedupFrom
#print axioms Lime.Replay.the_kept_wake_is_the_first_logged_wake_when_wakes_are_logged_in_order
#print axioms Lime.Replay.lePoint_spec
#print axioms Lime.Replay.lastWakeLe_of_point
#print axioms Lime.Replay.lastWakeLeArr_eq_lastWakeLe
#print axioms Lime.Replay.entryDays_eq_entryDaysFast
#print axioms Lime.Replay.day_index_wake_to_wake_ported
#print axioms Lime.Replay.the_kept_wake_is_not_the_first_logged_wake
#print axioms Lime.Replay.the_day_index_dedups_runs_not_dates
#print axioms Lime.Replay.dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted
#print axioms Lime.Replay.a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted
#print axioms Lime.Replay.keptWakes_append_of_later_by_nanos_is_refuted
#print axioms Lime.Replay.a_wake_day_is_shorter_than_a_day_is_not_vacuous
#print axioms Lime.Replay.an_undone_wake_indexes_nothing

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C3 (design §8.1–§8.2, §14.4 row C3): the machine's
-- state, effects and keys in Replay.lean, the block family's arms (`start`, `pause`, `unpause`,
-- `interrupt`, `resume`, `stop`, `done` with partials, `extend`) with `credit`, `uncredit_cut` and `cut`
-- ported by name, the maps' laws (`KMap`, and `HMap`, the bucketed map of items and item days), and the
-- `log` op's `facts.block` in Boundary.lean (`the_log_op_answers_the_block_facts`).  The three goals §15 names for C3
-- were added to Goals.lean as written and discharged in the step: `applyEffects_touches_only_named_keys`,
-- `every_known_event_has_an_arm` and `credit_conserves_the_day_minutes`.  Site R8 (quirk Q6c, gap 83):
-- `worked_minutes_floor_each_subsegment` and its twin `worked_minutes_is_not_the_floor_of_the_block`.  Site R9:
-- `load_is_exact_fifths`.
-- §8.2's `an_extend_changes_only_the_bookkeeping` is refuted under the owner's D14
-- (`an_extend_changes_more_than_the_bookkeeping`) and restated
-- (`an_extend_changes_only_the_bookkeeping_and_its_extended_minutes`).  The `@[csimp]` twins are
-- `replay_eq_replayFast`, `sortObs_eq_sortObsFast` and `sortSegs_eq_sortSegsFast`.
#print axioms Lime.Replay.insBy_append
#print axioms Lime.Replay.insSort_eq_mergeSort
#print axioms Lime.Replay.sortObs_eq_sortObsFast
#print axioms Lime.Replay.sortSegs_eq_sortSegsFast
#print axioms Lime.Replay.replay_eq_replayFast
#print axioms Lime.Replay.KMap.get_nil
#print axioms Lime.Replay.KMap.get_cons
#print axioms Lime.Replay.KMap.get_append
#print axioms Lime.Replay.KMap.get_eq_none_of_keys
#print axioms Lime.Replay.KMap.get_eq_none_iff_keys
#print axioms Lime.Replay.KMap.get_filter_key
#print axioms Lime.Replay.KMap.get_alterGo
#print axioms Lime.Replay.KMap.get_alter
#print axioms Lime.Replay.KMap.get_map_snd
#print axioms Lime.Replay.KMap.vsum_append
#print axioms Lime.Replay.KMap.vsum_cons
#print axioms Lime.Replay.KMap.vsum_reverse
#print axioms Lime.Replay.KMap.get_le_vsum
#print axioms Lime.Replay.KMap.mem_keys_of_get
#print axioms Lime.Replay.KMap.filter_key_of_not_mem
#print axioms Lime.Replay.KMap.vsum_alterGo
#print axioms Lime.Replay.KMap.vsum_alter
#print axioms Lime.Replay.HMap.get_alter
#print axioms Lime.Replay.HMap.get_mapVals
#print axioms Lime.Replay.HMap.get_empty
#print axioms Lime.Replay.valueAt_applyEffect
#print axioms Lime.Replay.applyEffects_touches_only_named_keys
#print axioms Lime.Replay.closePause_plain
#print axioms Lime.Replay.creditFx_plain
#print axioms Lime.Replay.obsFx_plain
#print axioms Lime.Replay.cut_plain
#print axioms Lime.Replay.not_header_of_plain
#print axioms Lime.Replay.uncreditFx_no_header
#print axioms Lime.Replay.doneClose_no_header
#print axioms Lime.Replay.doneFx_no_header
#print axioms Lime.Replay.arm_no_header
#print axioms Lime.Replay.every_known_event_has_an_arm
#print axioms Lime.Replay.Ci6.sum_add
#print axioms Lime.Replay.safe_of_plain
#print axioms Lime.Replay.DayAcc.bal_empty
#print axioms Lime.Replay.DayOp.bal_apply
#print axioms Lime.Replay.DayAcc.bal_uncredit
#print axioms Lime.Replay.applyEffects_append
#print axioms Lime.Replay.applyEffects_cons
#print axioms Lime.Replay.safe_apply
#print axioms Lime.Replay.safe_list
#print axioms Lime.Replay.machine_apply
#print axioms Lime.Replay.conserves_safe
#print axioms Lime.Replay.conserves_safe_then_machine
#print axioms Lime.Replay.closePause_lastCut
#print axioms Lime.Replay.all_safe_of_plain
#print axioms Lime.Replay.unk_credit_none
#print axioms Lime.Replay.conserves_cut
#print axioms Lime.Replay.bal_apply_uncredit
#print axioms Lime.Replay.conserves_arm
#print axioms Lime.Replay.conserves_init
#print axioms Lime.Replay.conserves_step
#print axioms Lime.Replay.conserves_foldl
#print axioms Lime.Replay.credit_conserves_the_day_minutes
#print axioms Lime.Replay.Ci6.fifths_add
#print axioms Lime.Replay.DayOp.fifths_apply
#print axioms Lime.Replay.DayOp.fifths_alterFn
#print axioms Lime.Replay.allFifths_apply
#print axioms Lime.Replay.allFifths_foldl
#print axioms Lime.Replay.load_is_exact_fifths
#print axioms Lime.Replay.worked_minutes_floor_each_subsegment
#print axioms Lime.Replay.an_extend_changes_only_the_bookkeeping_and_its_extended_minutes_is_refuted
#print axioms Lime.Replay.a_start_cuts_any_open_block_even_the_same_id
#print axioms Lime.Replay.a_block_cut_by_start_is_never_replaced_by_done
#print axioms Lime.Replay.a_stop_then_done_replaces_the_cut_credit
#print axioms Lime.Replay.a_stop_for_another_id_is_ignored
#print axioms Lime.Replay.a_matched_done_discards_the_clock_minutes
#print axioms Lime.Replay.close_pause_does_not_clear_paused
#print axioms Lime.Replay.a_partial_done_credits_but_does_not_complete
#print axioms Lime.Replay.a_partial_done_after_stop_replaces_the_cut
#print axioms Lime.Replay.a_block_started_during_an_interruption_runs_from_resume
#print axioms Lime.Replay.worked_minutes_is_not_the_floor_of_the_block
#print axioms Lime.Replay.an_extend_changes_more_than_the_bookkeeping

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C4 (design §8.2–§8.4, §14.4 row C4): the completion
-- family in Replay.lean (`completionArm`: `done`'s `mark_done`, `routine`, `skip`, `event`; the keys
-- `doneDate`, `instDate`, `instOther` and `named`; `arm_ofBlock`, which keeps the block family's arm off
-- the completion state), the `log` op's `facts.completion` and `facts.replayWarnings` in Boundary.lean
-- (`the_log_op_answers_the_completion_facts`), and Log.lean's repair of `parse_date`'s byte length
-- (`the_date_grammars_count_bytes_not_characters`).  The C4 goals §15 names were added to Goals.lean and
-- discharged in the step: `an_instance_is_its_last_record_in_file_order` (as written),
-- `last_done_is_the_latest_by_instant` (`doneInstants` without the zone it does not read) and
-- `instances_and_last_done_order_differently`.  Quirk Q6(b) (gap 118) beside them:
-- `last_done_is_the_first_of_the_latest`, `last_done_keeps_the_first_of_equal_instants`.  Carried note 3:
-- `a_since_filter_does_not_commute_with_the_latest_by_instant` refutes §8.4's claim, and
-- `named_keeps_the_latest_by_instant_and_the_latest_by_local_date` is fork `LatestNamed`.
-- `conserves_step`, `conserves_foldl`, `allFifths_foldl` and `arm_no_header` (audited under C3) are
-- re-proved over the zone and the completion arm.
#print axioms Lime.Log.the_date_grammars_count_bytes_not_characters
#print axioms Lime.Replay.ofBlock_of_plain
#print axioms Lime.Replay.header_of_ofBlock
#print axioms Lime.Replay.uncreditFx_ofBlock
#print axioms Lime.Replay.doneClose_ofBlock
#print axioms Lime.Replay.doneFx_ofBlock
#print axioms Lime.Replay.arm_ofBlock
#print axioms Lime.Replay.completionArm_no_header
#print axioms Lime.Replay.completionArm_safe
#print axioms Lime.Replay.foldl_lastMaxStep_some
#print axioms Lime.Replay.lastMax?_eq_none_iff
#print axioms Lime.Replay.maxSplit_step
#print axioms Lime.Replay.maxSplit_foldl
#print axioms Lime.Replay.lastMax?_spec
#print axioms Lime.Replay.filterMap_cons_toList
#print axioms Lime.Replay.applyEffect_lastDone
#print axioms Lime.Replay.lastDone_applyEffects
#print axioms Lime.Replay.markOf_of_ofBlock
#print axioms Lime.Replay.arm_markOf
#print axioms Lime.Replay.completionArm_markOf
#print axioms Lime.Replay.stepWith_lastDone
#print axioms Lime.Replay.foldl_stepWith_lastDone
#print axioms Lime.Replay.replay_state
#print axioms Lime.Replay.last_done_is_the_latest_by_instant
#print axioms Lime.Replay.instLt_trans
#print axioms Lime.Replay.instLt_skip
#print axioms Lime.Replay.last_done_is_the_first_of_the_latest
#print axioms Lime.Replay.last_done_isSome_iff
#print axioms Lime.Replay.applyEffect_instances
#print axioms Lime.Replay.instances_applyEffects
#print axioms Lime.Replay.instOf_of_ofBlock
#print axioms Lime.Replay.stepWith_instances
#print axioms Lime.Replay.foldl_stepWith_instances
#print axioms Lime.Replay.an_instance_is_its_last_record_in_file_order
#print axioms Lime.Replay.applyEffect_named
#print axioms Lime.Replay.named_applyEffects
#print axioms Lime.Replay.completionArm_namedOf
#print axioms Lime.Replay.stepWith_named
#print axioms Lime.Replay.foldl_stepWith_named
#print axioms Lime.Replay.foldl_pushStep_latest
#print axioms Lime.Replay.foldl_pushStep_dated
#print axioms Lime.Replay.named_keeps_the_latest_by_instant_and_the_latest_by_local_date
#print axioms Lime.Replay.applyEffect_ofBlock_keeps
#print axioms Lime.Replay.completionArm_rwarns
#print axioms Lime.Replay.stepWith_rwarns
#print axioms Lime.Replay.the_replay_warnings_are_the_unknown_statuses_in_file_order
#print axioms Lime.Replay.applyEffect_doneDates
#print axioms Lime.Replay.applyEffects_doneDates
#print axioms Lime.Replay.completionArm_doneDates
#print axioms Lime.Replay.stepWith_doneDates
#print axioms Lime.Replay.a_done_date_is_a_survivors_completion_date
#print axioms Lime.Replay.instances_and_last_done_order_differently
#print axioms Lime.Replay.a_retro_done_marks_done_and_credits_nothing
#print axioms Lime.Replay.a_later_pending_does_not_undo_a_done_date
#print axioms Lime.Replay.an_unknown_status_warns_and_is_pending
#print axioms Lime.Replay.last_done_keeps_the_first_of_equal_instants
#print axioms Lime.Replay.a_routine_done_is_dated_by_its_inst_only_when_it_is_a_date
#print axioms Lime.Replay.a_since_filter_does_not_commute_with_the_latest_by_instant

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C5 (design §8.2–§8.4, §14.4 row C5): the day header and
-- records family in Replay.lean (`dayArm`: `wake`, `arrive`, `loc`, `break`, `energy`, `idle`, `routine`'s day
-- half, `plan`, `demote`, `drop`, `close`, unknown events; `DayAcc` the whole of fork `DayReplay`; days
-- bucketed; fork `slept_by_day` built before the walk and compiled as `sleptMap`), the `log` op's `facts.day`
-- in Boundary.lean (`the_log_op_answers_the_day_facts`), and Log.lean's port of chrono's signed `%Y`
-- (`a_signed_year_is_a_date_to_chrono`).  The C5 goals were added to Goals.lean and discharged in the step:
-- `energy_obs_slept_is_the_days_first_logged_sleep` (as §15 writes it), `the_first_leak_maximum_wins`,
-- `a_demote_stamp_reads_the_week_or_date_key` and `idle_and_idle_since_read_different_orders`.  Quirks Q6(f)
-- and Q6(g) with their separating witnesses.  Audited under C3/C4 and re-proved over the new arm (their
-- names unchanged): `arm_ofBlock`, `arm_no_header`, `arm_markOf`, `uncreditFx_ofBlock`, `doneClose_ofBlock`,
-- `doneFx_ofBlock`, `conserves_arm`, `conserves_step`, `conserves_foldl`, `allFifths_foldl`,
-- `credit_conserves_the_day_minutes`, `load_is_exact_fifths`, `replay_state`, `replay_eq_replayFast` and the
-- C4 `stepWith_*` laws.
#print axioms Lime.Log.a_signed_year_is_a_date_to_chrono
#print axioms Lime.Replay.foldl_sleptStep_get
#print axioms Lime.Replay.blockOnly_of_plain
#print axioms Lime.Replay.ofBlock_of_blockOnly
#print axioms Lime.Replay.isRec_of_blockOnly
#print axioms Lime.Replay.uncreditFx_blockOnly
#print axioms Lime.Replay.doneClose_blockOnly
#print axioms Lime.Replay.doneFx_blockOnly
#print axioms Lime.Replay.dayArm_ofBlock
#print axioms Lime.Replay.arm_split
#print axioms Lime.Replay.arm_filterMap_rec
#print axioms Lime.Replay.dayArm_safe
#print axioms Lime.Replay.sleptInv_apply
#print axioms Lime.Replay.sleptInv_applyEffects
#print axioms Lime.Replay.closePause_pending
#print axioms Lime.Replay.closePause_sleptOk
#print axioms Lime.Replay.creditFx_sleptOk
#print axioms Lime.Replay.uncreditFx_sleptOk
#print axioms Lime.Replay.obsFx_sleptOk
#print axioms Lime.Replay.machine_sleptOk
#print axioms Lime.Replay.cut_sleptOk
#print axioms Lime.Replay.wentOn_fromStart
#print axioms Lime.Replay.doneClose_sleptOk
#print axioms Lime.Replay.doneFx_sleptOk
#print axioms Lime.Replay.dayArm_sleptOk
#print axioms Lime.Replay.completionArm_sleptOk
#print axioms Lime.Replay.resumeBlock_obs
#print axioms Lime.Replay.arm_sleptOk
#print axioms Lime.Replay.sleptInv_step
#print axioms Lime.Replay.sleptInv_foldl
#print axioms Lime.Replay.sleptInv_init
#print axioms Lime.Replay.insBy_perm
#print axioms Lime.Replay.insSort_perm
#print axioms Lime.Replay.isWake_eq_sleptOf
#print axioms Lime.Replay.sleptByDay_get
#print axioms Lime.Replay.energy_obs_slept_is_the_days_first_logged_sleep
#print axioms Lime.Replay.completionArm_noRec
#print axioms Lime.Replay.effectsWith_filterMap_rec
#print axioms Lime.Replay.applyEffects_longestLeak
#print axioms Lime.Replay.dayArm_leaks
#print axioms Lime.Replay.the_first_leak_maximum_wins
#print axioms Lime.Replay.leakLt_trans
#print axioms Lime.Replay.leakLt_skip
#print axioms Lime.Replay.the_longest_leak_is_the_first_of_the_longest
#print axioms Lime.Replay.applyEffects_records
#print axioms Lime.Replay.dayArm_records
#print axioms Lime.Replay.stepWith_records
#print axioms Lime.Replay.foldl_stepWith_records
#print axioms Lime.Replay.the_demotions_are_the_survivors_demotes_in_file_order
#print axioms Lime.Replay.the_closes_are_the_survivors_closes_in_file_order
#print axioms Lime.Replay.the_unknown_count_is_the_surviving_unknown_events
#print axioms Lime.Replay.a_demote_stamp_reads_the_week_or_date_key
#print axioms Lime.Replay.the_days_wake_is_its_first_logged_wake
#print axioms Lime.Replay.an_energy_line_before_its_wake_reads_the_wakes_sleep
#print axioms Lime.Replay.a_gap_is_on_the_day_it_began
#print axioms Lime.Replay.a_day_keeps_its_first_arrival_its_highest_replans_and_its_last_plan
#print axioms Lime.Replay.a_break_lasts_its_actual_minutes_else_its_planned
#print axioms Lime.Replay.the_first_of_equal_leaks_is_the_longest
#print axioms Lime.Replay.the_demote_stamps_of_a_week_a_date_and_a_month_key
#print axioms Lime.Replay.an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest
#print axioms Lime.Replay.the_calendar_today_is_not_the_replays_day_after_midnight
#print axioms Lime.Replay.idle_and_idle_since_read_different_orders

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C6 (design §8.2, §8.4, §11, §14.4 row C6): every line's header
-- (the survivors' `header` effects and the second pass over the cancelled lines, `entryHeaders` compiled as its
-- fast twin), the seams (`Effect.seam`, fork `DaySeam`), the observations in file order, `Effect.day?` and
-- `Key.date?`, and §8.4's view (`replayDoc`, `factsView`, `ask`, and the wire's grouping `dayOuts`, `winOuts`,
-- `itemOuts`) in Replay.lean; the `log` op's `facts` as the view and its headers with day, mask bit and display
-- in Boundary.lean (a header of a tail from any line but 1 refused by name).  The C6 goals were added to Goals.lean
-- and discharged in the step: `every_dated_output_names_its_day_key` (for every effect) and
-- `observations_are_in_file_order`, refuted as stated (`observations_are_not_in_file_order_when_a_line_repeats`)
-- and proved on increasing lines (`observations_are_in_file_order_on_increasing_lines`).  C5's owed equation:
-- `a_days_last_t_is_the_latest_stamp_of_its_survivors`.  Audited under C1–C5 and re-proved over the seam effect
-- and the new fields (names unchanged): `valueAt_applyEffect`, `every_known_event_has_an_arm`, `safe_apply`,
-- `conserves_step`, `an_extend_changes_only_the_bookkeeping_and_its_extended_minutes` (its key list gains the
-- seam's day), `stepWith_lastDone`, `stepWith_named`, `stepWith_doneDates`, the replay-warning step,
-- `sleptInv_step`, `effectsWith_filterMap_rec`, `the_log_op_reads_a_four_line_tail` (now from line 1),
-- `the_response_shapes_emit_in_build_order`, `logAnswer_facts` (restated over the view) and the five wire
-- witnesses `the_log_op_answers_*` (re-probed over the view).
#print axioms Lime.Replay.entryHeaders_eq_entryHeadersFast
#print axioms Lime.Replay.entryHeaders_length
#print axioms Lime.Replay.headerOf?_of_not_isHeader
#print axioms Lime.Replay.applyEffects_headers
#print axioms Lime.Replay.effectsWith_headers
#print axioms Lime.Replay.foldl_stepWith_headers
#print axioms Lime.Replay.the_survivors_headers_are_the_uncancelled_entry_headers
#print axioms Lime.Replay.the_two_header_passes_are_every_entrys_header
#print axioms Lime.Replay.seamOp_lastT
#print axioms Lime.Replay.applyEffects_seam_lastT
#print axioms Lime.Replay.dayArm_noSeam
#print axioms Lime.Replay.arm_noSeam
#print axioms Lime.Replay.completionArm_noSeam
#print axioms Lime.Replay.effectsWith_seams
#print axioms Lime.Replay.foldl_stepWith_seam_lastT
#print axioms Lime.Replay.a_days_last_t_is_the_latest_stamp_of_its_survivors
#print axioms Lime.Replay.every_dated_output_names_its_day_key
#print axioms Lime.Replay.every_leak_is_on_a_day_its_idle_record_names
#print axioms Lime.Replay.applyEffects_obs
#print axioms Lime.Replay.closePause_obs
#print axioms Lime.Replay.creditFx_obs
#print axioms Lime.Replay.uncreditFx_obs
#print axioms Lime.Replay.obsFx_obs
#print axioms Lime.Replay.cut_obs
#print axioms Lime.Replay.doneClose_obs
#print axioms Lime.Replay.doneFx_obs
#print axioms Lime.Replay.dayArm_obs
#print axioms Lime.Replay.arm_obs
#print axioms Lime.Replay.completionArm_obs
#print axioms Lime.Replay.stepWith_obs
#print axioms Lime.Replay.foldl_stepWith_obs
#print axioms Lime.Replay.sublist_nodup_of_pairwise_lt
#print axioms Lime.Replay.survivors_lines_pairwise
#print axioms Lime.Replay.observations_are_not_in_file_order_when_a_line_repeats
#print axioms Lime.Replay.observations_are_in_file_order_on_increasing_lines
#print axioms Lime.Replay.ask_reads_the_facts
#print axioms Lime.Replay.replayDoc_eq_replayDocFast
#print axioms Lime.Replay.a_days_seam_holds_its_break_its_marks_and_its_latest_stamp
#print axioms Lime.Replay.the_since_break_anchor_is_the_first_start_without_a_break
#print axioms Lime.Replay.every_line_has_a_header_and_a_cancelled_one_is_marked
#print axioms Lime.Replay.a_start_observation_is_in_its_starts_place
#print axioms Lime.Replay.the_view_reads_a_small_log

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step C7 (design §7.3, §14.4 row C7): the undo law in Replay.lean.
-- `undosFor` (what `lime undo` appends: one `undo{of: tag, id: primary id}` per event, most recent first) and
-- `untouchedBy`; the mask's half (`undoing_a_command_leaves_the_survivors_of_the_log_without_it`); the view reads only
-- the survivors, whatever its maps' bucket counts (`SameReadings`, `HMap.Keyed`, `HMap.perm_keys_pairs`,
-- `the_view_reads_only_the_survivors`).  The C7 goals were added to Goals.lean and discharged in the step:
-- `undoing_a_command_replays_the_log_without_it` (without §15's unused `hl`), `undo_of_a_silent_verb_cancels_an_older_event`
-- and `undo_after_housekeeping_cancels_the_housekeeping`, with the refutation twin in the law's conclusion
-- (`the_undo_law_fails_without_untouchedBy`) and quirk Q6(d)'s law and separation beside them.
#print axioms Lime.Replay.matches_its_own_undo
#print axioms Lime.Replay.foldl_maskStep_of_no_undo
#print axioms Lime.Replay.foldl_maskStep_undos
#print axioms Lime.Replay.undoing_a_command_leaves_the_survivors_of_the_log_without_it
#print axioms Lime.Replay.sameReadings_init
#print axioms Lime.Replay.SameReadings.apply
#print axioms Lime.Replay.SameReadings.applyEffects
#print axioms Lime.Replay.SameReadings.stepWith
#print axioms Lime.Replay.SameReadings.foldl
#print axioms Lime.Replay.KMap.mem_alterGo
#print axioms Lime.Replay.KMap.mem_alter
#print axioms Lime.Replay.KMap.nodup_alterGo
#print axioms Lime.Replay.KMap.nodup_alter
#print axioms Lime.Replay.HMap.keyed_empty
#print axioms Lime.Replay.HMap.keyed_alter
#print axioms Lime.Replay.HMap.keyed_mapVals
#print axioms Lime.Replay.HMap.mem_foldl_pairs
#print axioms Lime.Replay.HMap.nodup_foldl_pairs
#print axioms Lime.Replay.HMap.nodup_keys_pairs
#print axioms Lime.Replay.HMap.mem_keys_pairs_iff
#print axioms Lime.Replay.HMap.perm_keys_pairs
#print axioms Lime.Replay.HMap.keys_pairs_mapVals
#print axioms Lime.Replay.minDay?_perm
#print axioms Lime.Replay.maxDay?_perm
#print axioms Lime.Replay.pairsKeyed_init
#print axioms Lime.Replay.PairsKeyed.apply
#print axioms Lime.Replay.PairsKeyed.foldl
#print axioms Lime.Replay.doneKeys_filter
#print axioms Lime.Replay.doneCount_filter
#print axioms Lime.Replay.factsView_finish_of_sameReadings
#print axioms Lime.Replay.the_view_reads_only_the_survivors
#print axioms Lime.Replay.undoing_a_command_replays_the_log_without_it
#print axioms Lime.Replay.undoing_the_last_command_replays_the_log_without_it
#print axioms Lime.Replay.undoing_a_command_answers_every_fact_query_as_the_log_without_it
#print axioms Lime.Replay.a_silent_verb_undo_cancels_the_latest_event_of_its_name
#print axioms Lime.Replay.a_silent_verb_undo_cancels_nothing_iff_no_survivor_has_its_name
#print axioms Lime.Replay.move_toList
#print axioms Lime.Replay.undo_of_a_silent_verb_cancels_an_older_event
#print axioms Lime.Replay.undo_after_housekeeping_cancels_the_housekeeping
#print axioms Lime.Replay.the_undo_law_fails_without_untouchedBy
#print axioms Lime.Replay.a_done_undone_over_an_automatic_close_is_untouched

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W1 (design §9.2, §10.4, §14.5 row W1, §15 W block): the new module
-- Seal.lean.  The codec library (a round trip per combinator, for every value), the record codecs, the checkpoint's
-- keyed codec and law 10 (`readCkpt_emitCkpt`, `readDayRecord_emitDayRecord`, `readWindowRecord_emitWindowRecord`, each
-- with its smart-decoder converse and iff), R10 (`Ckpt.wf_bounds`, the missing-field refusal, `mkPolicy?`), the horizon
-- (`the_horizon_is_at_most_thirty_days_back`), carried note 1 (`the_answer_reads_the_replays_longest_leak`) and the
-- specification's ties to the replay (`replay_eq_finish_foldedState`, `entryHeaders_eq_foldedHeaders`,
-- `the_answer_reads_the_replays_scalar_facts`), and nine decided witnesses.  The sixteen W goals entered Goals.lean and
-- stay there until W2 (the burn-down rises 13 -> 29); nothing here depends on them.
#print axioms Lime.Seal.cNat_nonnull
#print axioms Lime.Seal.cStr_nonnull
#print axioms Lime.Seal.foldl_listStep_map
#print axioms Lime.Seal.cList_nonnull
#print axioms Lime.Seal.cTuple_nonnull
#print axioms Lime.Seal.cIso_nonnull
#print axioms Lime.Seal.cBool_nonnull
#print axioms Lime.Seal.cFin_nonnull
#print axioms Lime.Seal.cPair_nonnull
#print axioms Lime.Seal.cInstant_nonnull
#print axioms Lime.Seal.cAt_nonnull
#print axioms Lime.Seal.cVInstant_nonnull
#print axioms Lime.Seal.cVOffset_nonnull
#print axioms Lime.Seal.cNum_nonnull
#print axioms Lime.Seal.cEnergyObs_nonnull
#print axioms Lime.Seal.cLeakRec_nonnull
#print axioms Lime.Seal.cStamp_nonnull
#print axioms Lime.Seal.cDayAcc_nonnull
#print axioms Lime.Seal.cItemAcc_nonnull
#print axioms Lime.Seal.cBlock_nonnull
#print axioms Lime.Seal.cCut_nonnull
#print axioms Lime.Seal.cOpenInt_nonnull
#print axioms Lime.Seal.cSeamAcc_nonnull
#print axioms Lime.Seal.pos_enc
#print axioms Lime.Seal.key_enc
#print axioms Lime.Seal.ok_bind
#print axioms Lime.Seal.err_bind
#print axioms Lime.Seal.key_ne
#print axioms Lime.Seal.readDayFields_emit
#print axioms Lime.Seal.readDayRecord_emitDayRecord
#print axioms Lime.Seal.readDayRecord_wf
#print axioms Lime.Seal.readDayRecord_emitDayRecord_iff
#print axioms Lime.Seal.readWindowFields_emit
#print axioms Lime.Seal.readWindowRecord_emitWindowRecord
#print axioms Lime.Seal.readWindowRecord_wf
#print axioms Lime.Seal.readWindowRecord_emitWindowRecord_iff
#print axioms Lime.Seal.readCkptFields_emit
#print axioms Lime.Seal.readCkpt_emitCkpt
#print axioms Lime.Seal.readCkpt_wf
#print axioms Lime.Seal.readCkpt_emitCkpt_iff
#print axioms Lime.Seal.readCkpt_refuses_a_checkpoint_without_its_ledgerDay
#print axioms Lime.Seal.mkPolicy?_refuses_keepDays_past_31
#print axioms Lime.Seal.mkPolicy?_refuses_maxLine_past_2_40
#print axioms Lime.Seal.horizonOf_le
#print axioms Lime.Seal.the_horizon_is_at_most_thirty_days_back
#print axioms Lime.Seal.replay_eq_finish_foldedState
#print axioms Lime.Seal.entryHeaders_eq_foldedHeaders
#print axioms Lime.Seal.the_answer_reads_the_replays_longest_leak
#print axioms Lime.Seal.the_answer_reads_the_replays_scalar_facts
#print axioms Lime.Seal.orElse_eq_none
#print axioms Lime.Seal.check_eq_none
#print axioms Lime.Seal.Ckpt.wf_bounds
#print axioms Lime.Seal.the_checkpoint_of_nothing_is_the_empty_checkpoint
#print axioms Lime.Seal.the_empty_checkpoint_is_wf
#print axioms Lime.Seal.a_log_sealed_anywhere_answers_as_its_replay
#print axioms Lime.Seal.the_last_done_outlives_the_seal_of_its_days
#print axioms Lime.Seal.a_checkpoint_carries_the_last_cut
#print axioms Lime.Seal.the_horizon_of_2026_09_14
#print axioms Lime.Seal.an_undo_is_settled_when_its_target_is_folded_or_absent
#print axioms Lime.Seal.an_unfolded_undo_of_a_sealed_day_is_not_sealable
#print axioms Lime.Seal.a_future_dated_line_sets_the_future_floor
#print axioms Lime.Seal.sealed_and_live_observations_on_a_start_across_the_seal
#print axioms Lime.Seal.the_round_trips_are_not_vacuous

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 1 (design §9.5 laws 1 and 11, §14.5 row W2, §15 W block):
-- the new module SealLaw.lean.  Law 1's four goals and law 11 discharged under their names, with their companions
-- (law 1 needs neither `contiguousFrom` nor `sealable`; law 11 needs `contiguousFrom`), and the canonical-list,
-- keyed-map, stable-sort and observation-line lemmas beneath them.
#print axioms Lime.Seal.StrictTotal.eq_of_not
#print axioms Lime.Seal.StrictTotal.asymm
#print axioms Lime.Seal.mem_insUniq
#print axioms Lime.Seal.sorted_insUniq
#print axioms Lime.Seal.mem_foldl_insUniq
#print axioms Lime.Seal.sorted_foldl_insUniq
#print axioms Lime.Seal.mem_canon
#print axioms Lime.Seal.sorted_canon
#print axioms Lime.Seal.nodup_of_sorted
#print axioms Lime.Seal.nodup_canon
#print axioms Lime.Seal.eq_of_sorted_of_mem_iff
#print axioms Lime.Seal.canon_eq_of_mem_iff
#print axioms Lime.Seal.natLt_strictTotal
#print axioms Lime.Seal.charsLt_trans
#print axioms Lime.Seal.charsLt_total
#print axioms Lime.Seal.idLt_strictTotal
#print axioms Lime.Seal.lexLt_strictTotal
#print axioms Lime.Seal.optLt_strictTotal
#print axioms Lime.Seal.instKeyLt_strictTotal
#print axioms Lime.Seal.namedKeyLt_strictTotal
#print axioms Lime.Seal.find?_filterMap_of_nodup
#print axioms Lime.Seal.find?_map_filter_of_nodup
#print axioms Lime.Seal.allKeyed_init
#print axioms Lime.Seal.AllKeyed.apply
#print axioms Lime.Seal.AllKeyed.applyEffects
#print axioms Lime.Seal.AllKeyed.foldl
#print axioms Lime.Seal.allKeyed_foldedState
#print axioms Lime.Seal.get_eq_none_of_not_mem_keys
#print axioms Lime.Seal.mem_keys_of_get
#print axioms Lime.Seal.insBy_nil'
#print axioms Lime.Seal.insBy_cons'
#print axioms Lime.Seal.insSort_cons'
#print axioms Lime.Seal.insBy_of_all
#print axioms Lime.Seal.insBy_filter
#print axioms Lime.Seal.insBy_sorted
#print axioms Lime.Seal.insSort_sorted
#print axioms Lime.Seal.insSort_filter
#print axioms Lime.Seal.obsLe_trans
#print axioms Lime.Seal.obsLe_total
#print axioms Lime.Seal.sortObs_filter
#print axioms Lime.Seal.filter_day_eq_nil
#print axioms Lime.Seal.not_mem_dayKeys
#print axioms Lime.Seal.pendingOn_eq
#print axioms Lime.Seal.dayRead_state
#print axioms Lime.Seal.findDay_days
#print axioms Lime.Seal.get_filterMap_find
#print axioms Lime.Seal.not_mem_winKeys
#print axioms Lime.Seal.pair_not_mem_keys
#print axioms Lime.Seal.winRead_state
#print axioms Lime.Seal.findWin_windows
#print axioms Lime.Seal.find?_map_of_nodup
#print axioms Lime.Seal.not_mem_itemIds
#print axioms Lime.Seal.findItem_items
#print axioms Lime.Seal.doneDays_nil_of_not_mem
#print axioms Lime.Seal.items_read_state
#print axioms Lime.Seal.others_read_state
#print axioms Lime.Seal.scalars_read_state
#print axioms Lime.Seal.ckptOf_eq
#print axioms Lime.Seal.answer_ledgerDay
#print axioms Lime.Seal.answer_horizon
#print axioms Lime.Seal.answer_days
#print axioms Lime.Seal.answer_window
#print axioms Lime.Seal.answer_items
#print axioms Lime.Seal.answer_instOther
#print axioms Lime.Seal.answer_named
#print axioms Lime.Seal.answer_openBlock
#print axioms Lime.Seal.answer_openInterrupt
#print axioms Lime.Seal.answer_lastDay
#print axioms Lime.Seal.answer_lastEffective
#print axioms Lime.Seal.answer_entryCount
#print axioms Lime.Seal.answer_unknown
#print axioms Lime.Seal.answer_longestLeak
#print axioms Lime.Seal.answer_rwarns
#print axioms Lime.Seal.answer_reads_state
#print axioms Lime.Seal.day_records_read_state
#print axioms Lime.Seal.window_records_read_state
#print axioms Lime.Seal.replayLines_eq
#print axioms Lime.Seal.ckptOf_nil
#print axioms Lime.Seal.answer_reads_the_replay
#print axioms Lime.Seal.day_record_is_the_replays_day
#print axioms Lime.Seal.window_record_is_the_replays_window
#print axioms Lime.Seal.partition_is_the_replay
#print axioms Lime.Seal.Line.entry_line
#print axioms Lime.Seal.lineEntries_pairwise
#print axioms Lime.Seal.arm_durations_nil
#print axioms Lime.Seal.arm_obs_one
#print axioms Lime.Seal.stepWith_obs_one
#print axioms Lime.Seal.foldl_stepWith_obs_one
#print axioms Lime.Seal.foldedSurvivors_sublist
#print axioms Lime.Seal.foldedState_obs_nodup
#print axioms Lime.Seal.perm_flatMap_pointwise
#print axioms Lime.Seal.flatMap_append_perm
#print axioms Lime.Seal.flatMap_map_eq
#print axioms Lime.Seal.map_flatMap_eq
#print axioms Lime.Seal.sum_ite_mem
#print axioms Lime.Seal.perm_flatMap_filter
#print axioms Lime.Seal.eq_of_perm_of_pairwise_lt
#print axioms Lime.Seal.sortByLine_sorted
#print axioms Lime.Seal.sortByLine_eq_of_perm
#print axioms Lime.Seal.mem_dayKeys_energy
#print axioms Lime.Seal.mem_dayKeys_durations
#print axioms Lime.Seal.mem_dayKeys_pending
#print axioms Lime.Seal.obs_perm_state
#print axioms Lime.Seal.observations_read_state
#print axioms Lime.Seal.observations_read_lines
#print axioms Lime.Seal.the_answer_reads_the_replay
#print axioms Lime.Seal.a_day_record_is_the_replays_day
#print axioms Lime.Seal.a_window_record_is_the_replays_window
#print axioms Lime.Seal.seal_partition_is_the_replay
#print axioms Lime.Seal.sealed_and_live_observations_are_the_replays

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 2 (design §9.3 the guards, §9.5 laws 2, 3 and 8 and the
-- `now` anchor, §14.5 row W2, §15 W block): the new modules SealResume.lean (resume, G0–G4, the restored state and
-- the resumed answer; definitions only) through SealLaw2F.lean.  Law 2 (`resume_is_replay`, through the codec round
-- trips as rewrites), law 3, the `now` anchor, law 8 and its pair discharged under their names, with the route
-- beneath them: the mask splits under G1 (SealMask), the index agrees at folded instants and at or after the head
-- second (SealIndex), a step reads the index only at its queries (SealStep), late binding commutes with the fold
-- (SealRebind), a common effect keeps two states agreeing above the horizons (SealAgree), the restored state agrees
-- with the folded one (SealRestore), and the grouped answer is the whole log's (SealGroup, SealAgg, SealAgg2,
-- SealHeaders, SealLaw2A–2D).
#print axioms Lime.Seal.closePause_congr
#print axioms Lime.Seal.cut_congr
#print axioms Lime.Seal.doneClose_congr
#print axioms Lime.Seal.arm_congr
#print axioms Lime.Seal.effectsWith_congr
#print axioms Lime.Seal.foldl_stepWith_congr
#print axioms Lime.Seal.stepQueries_sub
#print axioms Lime.Seal.cut_mi
#print axioms Lime.Seal.doneFx_machines
#print axioms Lime.Seal.arm_mi
#print axioms Lime.Seal.stepWith_mi
#print axioms Lime.Seal.foldQueries_sub
#print axioms Lime.Seal.foldl_mi
#print axioms Lime.Seal.applyEffect_rebind
#print axioms Lime.Seal.applyEffects_rebind
#print axioms Lime.Seal.rebind_of_sleptOk
#print axioms Lime.Seal.map_rebind_of_all
#print axioms Lime.Seal.arm_sl
#print axioms Lime.Seal.effectsWith_machine
#print axioms Lime.Seal.effectsWith_rebind
#print axioms Lime.Seal.pendingStart_step
#print axioms Lime.Seal.stepWith_rebind
#print axioms Lime.Seal.foldl_rebind
#print axioms Lime.Seal.pendingStart_foldl
#print axioms Lime.Seal.rebind_rebind
#print axioms Lime.Seal.localDate_ne_of_far
#print axioms Lime.Seal.duration_of_far
#print axioms Lime.Seal.ns_lt_of_wf
#print axioms Lime.Seal.dayOf_of_far
#print axioms Lime.Seal.localDate_lt_of_head
#print axioms Lime.Seal.dayOf_lt_of_head
#print axioms Lime.Seal.sortWakes_eq_of_perm
#print axioms Lime.Seal.sortWakes_of_sorted
#print axioms Lime.Seal.sortWakes_three
#print axioms Lime.Seal.dedupFrom_cons
#print axioms Lime.Seal.dedupFrom_nil
#print axioms Lime.Seal.dedupFrom_of_noRuns
#print axioms Lime.Seal.lastKept_cons
#print axioms Lime.Seal.noRuns_dedupFrom
#print axioms Lime.Seal.dedupFrom_dedupFrom
#print axioms Lime.Seal.noRuns_drop
#print axioms Lime.Seal.dedupFrom_far
#print axioms Lime.Seal.sec_le_of_le
#print axioms Lime.Seal.filter_sec_split
#print axioms Lime.Seal.storedWakes_suffix
#print axioms Lime.Seal.lastWakeLe_isSome
#print axioms Lime.Seal.lastWakeLe_append
#print axioms Lime.Seal.lastWakeLe_append_of_mem
#print axioms Lime.Seal.keptWakes_eq
#print axioms Lime.Seal.lastKept_append
#print axioms Lime.Seal.dedupFrom_append'
#print axioms Lime.Seal.lastKept_mem
#print axioms Lime.Seal.mem_of_mem_dedupFrom
#print axioms Lime.Seal.mem_sortWakes
#print axioms Lime.Seal.mem_keptWakes
#print axioms Lime.Seal.lt_of_lt_of_le'
#print axioms Lime.Seal.lt_of_far
#print axioms Lime.Seal.far_of_lt_of_far
#print axioms Lime.Seal.dayOf_folded_agrees
#print axioms Lime.Seal.storedWakes_append_of_ge
#print axioms Lime.Seal.noRuns_of_far_start
#print axioms Lime.Seal.dedupFrom_sorted
#print axioms Lime.Seal.storedWakes_nil
#print axioms Lime.Seal.storedWakes_ne_nil
#print axioms Lime.Seal.noRuns_storedWakes
#print axioms Lime.Seal.sorted_storedWakes
#print axioms Lime.Seal.lastKept_none_eq
#print axioms Lime.Seal.noRuns_nil_dedup
#print axioms Lime.Seal.dayOf_tail_agrees
#print axioms Lime.Seal.eraseP_filter_of_first
#print axioms Lime.Seal.eraseP_filter_of_first_not
#print axioms Lime.Seal.tag_kept_or_overflow
#print axioms Lime.Seal.stackOf_append
#print axioms Lime.Seal.settledStep_fst
#print axioms Lime.Seal.Split.push
#print axioms Lime.Seal.Split.eraseP
#print axioms Lime.Seal.Split.foldl
#print axioms Lime.Seal.Split.eq
#print axioms Lime.Seal.eraseP_eq_self_of_find?_none
#print axioms Lime.Seal.part1
#print axioms Lime.Seal.part2
#print axioms Lime.Seal.mem_foldl_maskStep'
#print axioms Lime.Seal.unsettled_append
#print axioms Lime.Seal.unsettled_reverse
#print axioms Lime.Seal.unsettled_of_lines
#print axioms Lime.Seal.settled_lines_sub
#print axioms Lime.Seal.survivors_append_split
#print axioms Lime.Seal.mem_zipIdx_fst
#print axioms Lime.Seal.survivors_append_of_g1
#print axioms Lime.Seal.filter_cons_day
#print axioms Lime.Seal.AgreeAbove.apply
#print axioms Lime.Seal.AgreeAbove.applyEffects
#print axioms Lime.Seal.AgreeAbove.stepWith
#print axioms Lime.Seal.AgreeAbove.foldl
#print axioms Lime.Seal.AgreeAbove.trans
#print axioms Lime.Seal.AgreeAbove.symm
#print axioms Lime.Seal.AgreeAbove.of_sameReadings
#print axioms Lime.Seal.AgreeAbove.rebind
#print axioms Lime.Seal.get_foldl_step
#print axioms Lime.Seal.get_writeOpt
#print axioms Lime.Seal.get_foldl_pairs
#print axioms Lime.Seal.find?_pairs_of_mem
#print axioms Lime.Seal.find?_pairs_none
#print axioms Lime.Seal.get_writeAll_empty
#print axioms Lime.Seal.find?_openDays
#print axioms Lime.Seal.openDays_days_nodup
#print axioms Lime.Seal.restore_days
#print axioms Lime.Seal.restore_seams
#print axioms Lime.Seal.items_ids_nodup
#print axioms Lime.Seal.find?_items
#print axioms Lime.Seal.restore_items
#print axioms Lime.Seal.restore_lastDone
#print axioms Lime.Seal.restore_dropped
#print axioms Lime.Seal.filterMap_pair_fst_sublist
#print axioms Lime.Seal.mem_filterMap_pair
#print axioms Lime.Seal.restore_named
#print axioms Lime.Seal.mem_windowsFrom
#print axioms Lime.Seal.mem_itemMin
#print axioms Lime.Seal.mem_winKeys_of_itemDay
#print axioms Lime.Seal.nodup_flatMap_keyed
#print axioms Lime.Seal.windows_days_nodup
#print axioms Lime.Seal.itemMin_ids_nodup
#print axioms Lime.Seal.restore_itemDays
#print axioms Lime.Seal.mem_doneIds
#print axioms Lime.Seal.mem_winKeys_of_doneDate
#print axioms Lime.Seal.restore_doneDates
#print axioms Lime.Seal.mem_windowInst
#print axioms Lime.Seal.mem_instOther
#print axioms Lime.Seal.mem_winKeys_of_inst
#print axioms Lime.Seal.restore_instances
#print axioms Lime.Seal.filter_flatMap_days
#print axioms Lime.Seal.dayKeys_filter_nodup
#print axioms Lime.Seal.mem_dayKeys_filter
#print axioms Lime.Seal.restore_list
#print axioms Lime.Seal.map_pair_of_fst
#print axioms Lime.Seal.ckpt_openDays
#print axioms Lime.Seal.ckpt_items
#print axioms Lime.Seal.ckpt_window
#print axioms Lime.Seal.ckpt_instOther
#print axioms Lime.Seal.ckpt_named
#print axioms Lime.Seal.ckpt_machine
#print axioms Lime.Seal.ckpt_lastEff
#print axioms Lime.Seal.ckpt_rwarns
#print axioms Lime.Seal.ckpt_longestLeak
#print axioms Lime.Seal.ckpt_unknown
#print axioms Lime.Seal.ckpt_ledgerDay
#print axioms Lime.Seal.openDays_flatMap
#print axioms Lime.Seal.restore_agrees
#print axioms Lime.Seal.tailFold_fst
#print axioms Lime.Seal.tailFold_snd
#print axioms Lime.Seal.orElse_none
#print axioms Lime.Seal.stepCheck_none
#print axioms Lime.Seal.headerCheck_none
#print axioms Lime.Seal.resumeRun_ok
#print axioms Lime.Seal.idx_eq_of_pairwise_lt
#print axioms Lime.Seal.getElem?_of_mem_zipIdx
#print axioms Lime.Seal.mem_survivors_iff_uncancelled
#print axioms Lime.Seal.kmap_get_eq
#print axioms Lime.Seal.get_storedSlept
#print axioms Lime.Seal.sleptByDay_append
#print axioms Lime.Seal.filterMap_congr'
#print axioms Lime.Seal.sleptByDay_congr
#print axioms Lime.Seal.foldedState_nil
#print axioms Lime.Seal.applyEffect_keeps_keys
#print axioms Lime.Seal.foldl_keeps_keys
#print axioms Lime.Seal.applyEffects_below
#print axioms Lime.Seal.foldl_below
#print axioms Lime.Seal.instant_lt_or_le
#print axioms Lime.Seal.foldl_max_spec
#print axioms Lime.Seal.maxInstant?_spec
#print axioms Lime.Seal.maxInstant?_none
#print axioms Lime.Seal.foldl_min_spec
#print axioms Lime.Seal.minInstant?_spec
#print axioms Lime.Seal.minInstant?_none
#print axioms Lime.Seal.sep_of_bounds
#print axioms Lime.Seal.canon_filter
#print axioms Lime.Seal.mem_keys_map_iff
#print axioms Lime.Seal.mem_map_iff_filter_ne_nil
#print axioms Lime.Seal.mem_ids_of_day
#print axioms Lime.Seal.mem_keys_filter_iff
#print axioms Lime.Seal.winKeys_filter_eq
#print axioms Lime.Seal.windowOf_eq
#print axioms Lime.Seal.windowsFrom_eq
#print axioms Lime.Seal.instOtherOf_eq
#print axioms Lime.Seal.namedOf_eq
#print axioms Lime.Seal.dayKeys_filter_eq
#print axioms Lime.Seal.openDayOf_eq
#print axioms Lime.Seal.daysFrom_eq
#print axioms Lime.Seal.minDay?_nil
#print axioms Lime.Seal.minDay?_cons
#print axioms Lime.Seal.minOpt_assoc
#print axioms Lime.Seal.minDay?_append
#print axioms Lime.Seal.minDay?_spec
#print axioms Lime.Seal.minDay?_none_iff
#print axioms Lime.Seal.minDay?_eq_of_mem_iff
#print axioms Lime.Seal.maxDay?_cons
#print axioms Lime.Seal.maxOpt_assoc
#print axioms Lime.Seal.maxDay?_append
#print axioms Lime.Seal.maxDay?_spec
#print axioms Lime.Seal.maxDay?_none_iff
#print axioms Lime.Seal.maxDay?_eq_of_mem_iff
#print axioms Lime.Seal.storedHeaders_filter
#print axioms Lime.Seal.unsettled_cons
#print axioms Lime.Seal.tailHeaders_foldl
#print axioms Lime.Seal.tailHeaders_eq_spec
#print axioms Lime.Seal.mem_unsettled_sub
#print axioms Lime.Seal.tailHeadersSpec_eq
#print axioms Lime.Seal.mem_datesOf
#print axioms Lime.Seal.datesOf_nodup
#print axioms Lime.Seal.length_eq_of_mem_iff
#print axioms Lime.Seal.length_filter_split
#print axioms Lime.Seal.dates_union
#print axioms Lime.Seal.doneFirst_union
#print axioms Lime.Seal.doneCount_union
#print axioms Lime.Seal.lastDay_union
#print axioms Lime.Seal.mem_itemIds_iff
#print axioms Lime.Seal.ckpt_tagLast
#print axioms Lime.Seal.ckpt_tagOverflow
#print axioms Lime.Seal.ckpt_settled
#print axioms Lime.Seal.ckpt_maxT
#print axioms Lime.Seal.ckpt_futureFloor
#print axioms Lime.Seal.ckpt_wakes
#print axioms Lime.Seal.ckpt_sleptByDay
#print axioms Lime.Seal.ckpt_ledgerDay'
#print axioms Lime.Seal.wakeInstants_append
#print axioms Lime.Seal.mem_wakeInstants
#print axioms Lime.Seal.mem_foldQueries
#print axioms Lime.Seal.entryInstants_ns
#print axioms Lime.Seal.resume_survivors
#print axioms Lime.Seal.resume_sep
#print axioms Lime.Seal.resume_fold_congr
#print axioms Lime.Seal.rebindState_init
#print axioms Lime.Seal.Effect.key_rebind
#print axioms Lime.Seal.effectsWith_keys
#print axioms Lime.Seal.pendingStart_init
#print axioms Lime.Seal.keyed_foldl_step
#print axioms Lime.Seal.keyed_writeOpt
#print axioms Lime.Seal.keyed_writeAll
#print axioms Lime.Seal.get_foldl_alter_of_not_mem
#print axioms Lime.Seal.get_foldl_writeOpt_of_not_mem
#print axioms Lime.Seal.allKeyed_restore
#print axioms Lime.Seal.AllKeyed.rebind
#print axioms Lime.Seal.openDayOf_day
#print axioms Lime.Seal.windowOf_day
#print axioms Lime.Seal.restore_below
#print axioms Lime.Seal.AgreeAbove.refl
#print axioms Lime.Seal.kmap_get_append
#print axioms Lime.Seal.foldedState_eq
#print axioms Lime.Seal.pendingStart_restore
#print axioms Lime.Seal.foldedSurvivors_nil
#print axioms Lime.Seal.foldedIndex_nil
#print axioms Lime.Seal.mem_foldedSurvivors_iff
#print axioms Lime.Seal.map_zipIdx_eq
#print axioms Lime.Seal.valueAt_day_get
#print axioms Lime.Seal.valueAt_doneDate_get
#print axioms Lime.Seal.resume_index
#print axioms Lime.Seal.resume_state_agrees
#print axioms Lime.Seal.ckpt_lastDay
#print axioms Lime.Seal.ckpt_entryCount
#print axioms Lime.Seal.ckpt_warnings
#print axioms Lime.Seal.ckpt_warnOverflow
#print axioms Lime.Seal.answer_ckptOfEntries
#print axioms Lime.Seal.take_take_append
#print axioms Lime.Seal.lineEntries_nil
#print axioms Lime.Seal.window_done_count
#print axioms Lime.Seal.aggMerged_eq
#print axioms Lime.Seal.itemAggOf_eq
#print axioms Lime.Seal.items_merged_eq
#print axioms Lime.Seal.resume_headers
#print axioms Lime.Seal.resume_answer_eq
#print axioms Lime.Seal.resume_ok_run
#print axioms Lime.Seal.resume_answer_ignores_the_policy
#print axioms Lime.Seal.ys_mono
#print axioms Lime.Seal.monthStart_eq
#print axioms Lime.Seal.cumBefore_le_335
#print axioms Lime.Seal.monthStart_mono
#print axioms Lime.Seal.isoMonday_mono
#print axioms Lime.Seal.an_accepted_resume_covers_now
#print axioms Lime.Seal.horizonOf_zero
#print axioms Lime.Seal.keyAtOrAbove_zero
#print axioms Lime.Seal.g1_empty
#print axioms Lime.Seal.stepCheck_empty
#print axioms Lime.Seal.headerCheck_empty
#print axioms Lime.Seal.tailFold_empty
#print axioms Lime.Seal.resume_from_empty_never_refuses_by_guard
#print axioms Lime.Seal.resume_ok_answer
#print axioms Lime.Seal.readCkpt_emitCkpt_eq
#print axioms Lime.Seal.resume_is_replay
#print axioms Lime.Seal.resume_from_empty_is_replay
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 3 (design §9.5 laws 4 and 5, §15 W block): the new modules
-- SealReach.lean (law 5's spec side: reachFree on the whole list, tagsClear as G1 on the specification's tags),
-- SealLaw5A.lean and SealLaw5B.lean (acceptance both ways; the resume's steps against the whole log's, from either
-- side's head checks), SealPending.lean (a fold's pending start observation) and SealLaw4.lean (the whole log reads as
-- the folded lines below the horizons).  Laws 4 and 5 discharged under their names.
#print axioms Lime.Seal.foldAll_iff
#print axioms Lime.Seal.foldAll_eq_true
#print axioms Lime.Seal.tagsClear_iff
#print axioms Lime.Seal.contiguousFrom_append
#print axioms Lime.Seal.head_of_contiguousFrom
#print axioms Lime.Seal.stepCheck_eq_none
#print axioms Lime.Seal.tailFold_none_of
#print axioms Lime.Seal.headerCheck_none_of
#print axioms Lime.Seal.resumeRun_isOk_of
#print axioms Lime.Seal.index_facts
#print axioms Lime.Seal.folded_part_agrees
#print axioms Lime.Seal.steps_agree
#print axioms Lime.Seal.congr_of_spec
#print axioms Lime.Seal.maxInstant?_mem
#print axioms Lime.Seal.minInstant?_mem
#print axioms Lime.Seal.resume_isOk_eq
#print axioms Lime.Seal.isOk_iff_exists
#print axioms Lime.Seal.foldAll_append_vacuous
#print axioms Lime.Seal.reachFree_iff
#print axioms Lime.Seal.reachFree_of_accepted
#print axioms Lime.Seal.accepted_of_reachFree
#print axioms Lime.Seal.resume_ok_iff
#print axioms Lime.Seal.pending_none_of_pendLines
#print axioms Lime.Seal.arm_pending
#print axioms Lime.Seal.stepWith_pending
#print axioms Lime.Seal.foldl_pending
#print axioms Lime.Seal.AgreeBelow.symm
#print axioms Lime.Seal.pendingOn_below
#print axioms Lime.Seal.not_mem_pending_below
#print axioms Lime.Seal.winKeys_filter_below
#print axioms Lime.Seal.windowOf_below
#print axioms Lime.Seal.windowsIn_below
#print axioms Lime.Seal.dayKeys_filter_below
#print axioms Lime.Seal.openDayOf_below
#print axioms Lime.Seal.daysIn_below
#print axioms Lime.Seal.valueAt_day_view
#print axioms Lime.Seal.valueAt_itemDay_get
#print axioms Lime.Seal.valueAt_instDate_get
#print axioms Lime.Seal.filter_fst_eq_of_snd
#print axioms Lime.Seal.foldl_frame
#print axioms Lime.Seal.filter_rebind_below
#print axioms Lime.Seal.resume_below
#print axioms Lime.Seal.resume_keeps_the_sealed_records
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, in-step theorems (§14.5's W2 row): SealInStep.lean.  The stored
-- wakes' two edge cases, the fence's day-index law at three days with the two-day margin refuted on a two-transition
-- zone, a spurious G1 refusal, and a resume without the guards that is not the replay.
#print axioms Lime.Seal.an_instant_before_the_stored_wakes_is_sealed
#print axioms Lime.Seal.keptWakes_eq_nil
#print axioms Lime.Seal.dayOf_with_no_folded_wake_reads_the_tail
#print axioms Lime.Seal.dayOf_agrees_three_days_before
#print axioms Lime.Seal.a_spurious_tag_refusal_exists
#print axioms Lime.Seal.resume_without_the_guards_is_not_replay
#print axioms Lime.Seal.the_window_at_the_horizon_reads_the_replay
#print axioms Lime.Seal.dayOf_agrees_two_days_before_is_false
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 4b (design §9.4 the reseal, §9.5 law 6's pair, §14.5 row
-- W2's in-step theorems): SealFoldPoint.lean (the fold point is the greatest valid cut; an unterminated line is never
-- folded), SealLaw6Pair.lean (a reseal never seals past now), and the reseal's route at the cut: SealCutBounds.lean
-- (maxT, futureFloor), SealCutMask.lean (lines, folded survivors, undo targets), SealCutStep.lean (an undo past the cut
-- never reaches the folded lines; the folded lines' own mask; the settled undos), SealCutTags.lean (tag lines merge),
-- SealCutWakes.lean (stored wakes).
#print axioms Lime.Seal.foldl_last_valid
#print axioms Lime.Seal.getLast?_ge_of_sorted
#print axioms Lime.Seal.greatestValid_spec
#print axioms Lime.Seal.foldPoint_eq
#print axioms Lime.Seal.sealDay_eq
#print axioms Lime.Seal.foldPoint_valid
#print axioms Lime.Seal.foldPoint_greatest
#print axioms Lime.Seal.resealOf_some
#print axioms Lime.Seal.resume_some_reseal
#print axioms Lime.Seal.cutOk_parts
#print axioms Lime.Seal.the_unterminated_segment_is_never_folded
#print axioms Lime.Seal.foldl_min_le
#print axioms Lime.Seal.floorOf_le
#print axioms Lime.Seal.max_foldl_min_bound
#print axioms Lime.Seal.sealDayOf_bound
#print axioms Lime.Seal.le_sealDayOf
#print axioms Lime.Seal.a_reseal_never_seals_past_now
#print axioms Lime.Seal.instant_antisymm
#print axioms Lime.Seal.maxInstant?_some_of_ne_nil
#print axioms Lime.Seal.minInstant?_some_of_ne_nil
#print axioms Lime.Seal.maxInstant?_append
#print axioms Lime.Seal.minInstant?_append
#print axioms Lime.Seal.isFuture_migrates
#print axioms Lime.Seal.resealed_maxT
#print axioms Lime.Seal.resealed_futureFloor
#print axioms Lime.Seal.lineEntries_ge
#print axioms Lime.Seal.lineEntries_take
#print axioms Lime.Seal.lineEntries_drop
#print axioms Lime.Seal.foldedSurvivors_eq_filter
#print axioms Lime.Seal.foldedSurvivors_at_cut
#print axioms Lime.Seal.dangling_misses_the_folded
#print axioms Lime.Seal.undoTargets_eq
#print axioms Lime.Seal.undoStep_fst
#print axioms Lime.Seal.undoStep_snd_mono
#print axioms Lime.Seal.mem_undoTargets
#print axioms Lime.Seal.split_stackOf
#print axioms Lime.Seal.find?_split
#print axioms Lime.Seal.settled_lines_mono
#print axioms Lime.Seal.settled_prefix_lines
#print axioms Lime.Seal.foldl_maskStep_filter
#print axioms Lime.Seal.g1_prefix
#print axioms Lime.Seal.dangles_of_no_match
#print axioms Lime.Seal.unsettled_split_at
#print axioms Lime.Seal.cut_step_past
#print axioms Lime.Seal.cut_step_within
#print axioms Lime.Seal.cut_step
#print axioms Lime.Seal.survivors_at_cut
#print axioms Lime.Seal.dangleStep_fst
#print axioms Lime.Seal.settledStep_fst_one
#print axioms Lime.Seal.mem_of_mem_dangling
#print axioms Lime.Seal.cut_find_past
#print axioms Lime.Seal.cut_find_within
#print axioms Lime.Seal.cut_find_eq
#print axioms Lime.Seal.stackOf_snoc
#print axioms Lime.Seal.settled_at_cut
#print axioms Lime.Seal.tagLines_eq
#print axioms Lime.Seal.foldl_line_of_ne_nil
#print axioms Lime.Seal.lastLineOf_append
#print axioms Lime.Seal.find?_eq_of_mem_nodup
#print axioms Lime.Seal.find?_map_key
#print axioms Lime.Seal.tagLines_find
#print axioms Lime.Seal.tagLines_fst
#print axioms Lime.Seal.tagLines_append
#print axioms Lime.Seal.take_filter_of_prefix
#print axioms Lime.Seal.mem_take_iff_count
#print axioms Lime.Seal.headSec_mono
#print axioms Lime.Seal.storedWakes_prefix_absorb
#print axioms Lime.Seal.storedWakes_storedWakes
#print axioms Lime.Seal.lastKept_eq_getLast
#print axioms Lime.Seal.dedupFrom_far_noRuns
#print axioms Lime.Seal.getLast?_storedWakes
#print axioms Lime.Seal.storedWakes_at_cut
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 4c (design §9.4 the reseal, §9.5 laws 6 and 7):
-- SealLaw6.lean (a reseal is a seal; a resealed checkpoint accepts its own suffix), through SealRsDefs.lean (the
-- reseal's parts, named), SealLaw6Ctx.lean (an accepted resume and a valid cut as entries), SealLaw6Ckpt.lean (the
-- checkpoint and records at the cut), SealLaw6Seal.lean (sealable, and the reach condition, at the new ledger day), and
-- the route: SealCutState.lean (the state at the cut), SealCutHeaders.lean (headers; the unfolded lines cancel nothing
-- folded), SealCutSlept.lean (the stored slept_by_day), SealCutTags2.lean (the truncated tags merge), SealCutMachine.lean
-- (a fold's machine days), SealCutLows.lean (what bounds the new ledger day; a warning's line), SealCutGroup.lean (groups
-- at a later ledger day), SealCutSteps.lean (the unfolded steps), SealTagsSelf.lean (a checkpoint's own suffix leaves no
-- undo dangling).
#print axioms Lime.Seal.kmap_get_isSome_of_mem
#print axioms Lime.Seal.mem_storedSlept_keys
#print axioms Lime.Seal.storedSlept_congr
#print axioms Lime.Seal.mem_keys_iff_get
#print axioms Lime.Seal.storedSlept_congr_get
#print axioms Lime.Seal.cut_index_agrees
#print axioms Lime.Seal.restore_fold_mi
#print axioms Lime.Seal.cut_state_agrees
#print axioms Lime.Seal.closePause_keeps
#print axioms Lime.Seal.cut_keeps
#print axioms Lime.Seal.arm_lastCut
#print axioms Lime.Seal.arm_interrupt
#print axioms Lime.Seal.stepWith_machine_eq
#print axioms Lime.Seal.stepWith_machineDays
#print axioms Lime.Seal.foldl_machineDays
#print axioms Lime.Seal.keepTags_eq
#print axioms Lime.Seal.keptTags_eq_keepTags
#print axioms Lime.Seal.shortUnknown_key
#print axioms Lime.Seal.tagSorted_map
#print axioms Lime.Seal.tagSorted_tagLines
#print axioms Lime.Seal.tagSorted_merge
#print axioms Lime.Seal.find?_key_of_mem
#print axioms Lime.Seal.mem_tagLines_fst
#print axioms Lime.Seal.mem_merge_fst
#print axioms Lime.Seal.merge_filter_old
#print axioms Lime.Seal.keptBy_iff
#print axioms Lime.Seal.count_below_mono
#print axioms Lime.Seal.keptBy_filter
#print axioms Lime.Seal.keepTags_filter
#print axioms Lime.Seal.tag_line_exists
#print axioms Lime.Seal.merge_first_kept
#print axioms Lime.Seal.merge_kept_in
#print axioms Lime.Seal.keptTags_append
#print axioms Lime.Seal.length_keepTags_lt_iff
#print axioms Lime.Seal.tagOverflow_append
#print axioms Lime.Seal.foldedIndex_congr_er
#print axioms Lime.Seal.foldedState_congr_er
#print axioms Lime.Seal.cancelledAt_congr_er
#print axioms Lime.Seal.foldedHeaders_congr_er
#print axioms Lime.Seal.length_foldedHeaders
#print axioms Lime.Seal.foldedHeaders_at_cut
#print axioms Lime.Seal.stepLows_eq
#print axioms Lime.Seal.lowsStep_mono
#print axioms Lime.Seal.mem_lows
#print axioms Lime.Seal.foldl_min_le_of_mem
#print axioms Lime.Seal.sealDayOf_le_max
#print axioms Lime.Seal.filter_line_split
#print axioms Lime.Seal.survivors_sublist
#print axioms Lime.Seal.unsettled_sublist
#print axioms Lime.Seal.readObject_warn
#print axioms Lime.Seal.readValue_warn
#print axioms Lime.Seal.readLine_warn
#print axioms Lime.Seal.Line.warning_line
#print axioms Lime.Seal.lineWarnings_ge
#print axioms Lime.Seal.lineWarnings_take
#print axioms Lime.Seal.AgreeAbove.mono
#print axioms Lime.Seal.horizonOf_mono
#print axioms Lime.Seal.daysFrom_eq_raw
#print axioms Lime.Seal.daysIn_eq_filter
#print axioms Lime.Seal.windowsIn_eq_filter
#print axioms Lime.Seal.items_merged_eq_raw
#print axioms Lime.Seal.settledStep_snd
#print axioms Lime.Seal.mem_settledOf_iff
#print axioms Lime.Seal.isUndo_iff
#print axioms Lime.Seal.maskStep_push
#print axioms Lime.Seal.dangleStep_push
#print axioms Lime.Seal.stackOf_filter_nil
#print axioms Lime.Seal.tail_dangle_inv
#print axioms Lime.Seal.dangling_unsettled_self
#print axioms Lime.Seal.tagsClear_self
#print axioms Lime.Seal.resume_steps
#print axioms Lime.Seal.keyAtOrAbove_later
#print axioms Lime.Seal.headSec_later
#print axioms Lime.Seal.unfoldedEffects_eq
#print axioms Lime.Seal.mem_collect
#print axioms Lime.Seal.survivors_split
#print axioms Lime.Seal.resealOf_eq
#print axioms Lime.Seal.resealOf_parts
#print axioms Lime.Seal.rs_context
#print axioms Lime.Seal.rs_state_parts
#print axioms Lime.Seal.rs_sealable_reachFree
#print axioms Lime.Seal.reseal_is_seal
#print axioms Lime.Seal.a_resealed_checkpoint_accepts_its_own_suffix
-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W2, part 4d (design §9.7 genesis, §9.5 law 9): SealGenesis.lean
-- (the chunked rebuild with exact pops; definitions only), SealLaw9A.lean (a call's lines, the records' splits and
-- restrictions, records above an answer's horizons, the empty log sealable, the stack's pops, the chunks' ends),
-- SealLaw9B.lean (law 9's invariant; one accepted call through laws 2, 4, 6 and 7), SealLaw9.lean (genesis' loop keeps
-- the invariant; law 9).
#print axioms Lime.Seal.contiguousFrom_take
#print axioms Lime.Seal.genLines_append
#print axioms Lime.Seal.genLines_take
#print axioms Lime.Seal.genLines_drop
#print axioms Lime.Seal.length_genLines
#print axioms Lime.Seal.filter_range_split
#print axioms Lime.Seal.finish_day
#print axioms Lime.Seal.daysIn_split
#print axioms Lime.Seal.windowsIn_split
#print axioms Lime.Seal.dayRecordsBetween_split
#print axioms Lime.Seal.windowRecordsBetween_split
#print axioms Lime.Seal.daysIn_restrict
#print axioms Lime.Seal.windowsIn_restrict
#print axioms Lime.Seal.dayRecordsBetween_restrict
#print axioms Lime.Seal.windowRecordsBetween_restrict
#print axioms Lime.Seal.mem_daysIn_finish
#print axioms Lime.Seal.mem_windowsIn
#print axioms Lime.Seal.mem_dayRecordsBetween
#print axioms Lime.Seal.mem_windowRecordsBetween
#print axioms Lime.Seal.askMerged_extra
#print axioms Lime.Seal.sealable_empty
#print axioms Lime.Seal.popTo_sub
#print axioms Lime.Seal.popTo_ne_nil
#print axioms Lime.Seal.endsFrom_spec
#print axioms Lime.Seal.genOk_empty
#print axioms Lime.Seal.genesis_call
#print axioms Lime.Seal.genLoop_ok
#print axioms Lime.Seal.genEnds_spec
#print axioms Lime.Seal.chunked_genesis_is_one_replay

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W3 (design §9.6–§9.8, §10, §14.5 row W3): the window crosses the wire.
-- SealWire.lean (new): the downward fold-point scan and the compiled twins of `cutOk`, `resumeRun` and `resealOf`
-- (`@[csimp]`), the reseal's emitters and their read-back, the sealed input and its merge (`askMerged`), law 13's
-- numeral check.  Boundary.lean, section W3: the op's R10 rows, G0 at the op, the op as the resume, law 13, laws 8 and
-- 2 at the wire, three witnesses.  RETIRED with C6's string-tagged facts (their lines removed above, recorded in the
-- README's W3 block): logAnswer_facts, logAnswer_headers, LogReq.wf_facts_from_line_one,
-- mkLogReq?_refuses_facts_of_a_tail_without_a_checkpoint, LogReq.wf_headers_from_line_one,
-- mkLogReq?_refuses_headers_of_a_tail_without_a_checkpoint, logSectionWith_passes_its_zone,
-- the_log_op_answers_the_cancelled_lines, the_log_op_answers_every_entrys_day, the_log_op_answers_the_block_facts,
-- the_log_op_answers_the_completion_facts, the_log_op_answers_the_day_facts.
#print axioms Lime.Seal.greatestValid_succ
#print axioms Lime.Seal.greatestValid_eq_down
#print axioms Lime.Seal.cutOk_eq_cutOkFast
#print axioms Lime.Seal.resumeRun_eq_resumeRunFast
#print axioms Lime.Seal.resealOf_eq_resealOfFast
#print axioms Lime.Seal.cOpenBlock_nonnull
#print axioms Lime.Seal.cInterruption_nonnull
#print axioms Lime.Seal.findSome?_eq_none_all
#print axioms Lime.Seal.emitResealed_reads_back
#print axioms Lime.Seal.findDay_filter_append
#print axioms Lime.Seal.findWin_filter_append
#print axioms Lime.Seal.the_merged_days_read_as_askMerged
#print axioms Lime.Seal.the_merged_window_reads_as_askMerged
#print axioms Lime.Seal.answer_ckptOf_days_ge
#print axioms Lime.Seal.numeralBound_eq
#print axioms Lime.Seal.jnumsBelow_obj
#print axioms Lime.Seal.jnumsBelow_arr
#print axioms Lime.logLineStep_fold
#print axioms Lime.logLines_eq
#print axioms Lime.contiguousFrom_zipIdx
#print axioms Lime.logLines_contiguous
#print axioms Lime.LogReq.fault_of_b4_bounds
#print axioms Lime.mkLogReq?_refuses_keepDays_past_31
#print axioms Lime.mkLogReq?_refuses_maxLine_past_2_40
#print axioms Lime.policyOk_any
#print axioms Lime.mkLogReq?_refuses_a_sealed_input_out_of_bounds
#print axioms Lime.mkLogReq?_refuses_a_checkpoint_out_of_bounds
#print axioms Lime.mkLogReq?_refuses_a_resume_without_now
#print axioms Lime.LogReq.wf_resume_bounds
#print axioms Lime.readCkptField_refuses_what_readCkpt_refuses
#print axioms Lime.readLogReq_refuses_a_checkpoint_its_reader_refuses
#print axioms Lime.readSealedField_refuses_more_than_62_records
#print axioms Lime.logOp_refuses_a_checkpoint_of_another_zone
#print axioms Lime.logOp_refuses_a_tail_not_at_its_checkpoints_cut
#print axioms Lime.logOp_refuses_what_the_resume_refuses
#print axioms Lime.logOp_answers_through_the_resume
#print axioms Lime.logOp_reads_without_a_replay
#print axioms Lime.within53_ok
#print axioms Lime.within53_refuses_by_name
#print axioms Lime.the_log_op_emits_only_numerals_below_2_53
#print axioms Lime.the_log_op_checks_every_numeral
#print axioms Lime.the_log_op_emits_only_what_its_readers_read_back
#print axioms Lime.the_log_op_facts_from_genesis_are_the_replays
#print axioms Lime.the_log_op_facts_from_a_stored_checkpoint_are_the_replays
#print axioms Lime.the_log_op_names_its_resume_refusals
#print axioms Lime.the_log_op_refuses_a_count_past_2_53_by_its_key
#print axioms Lime.the_log_op_merges_a_sealed_day_below_its_ledger_day

-- APPENDED 2026-09-15 (stage 5, D9 track).  Step W4 (design §14.5 row W4, §19 K1/K23; W5's gate failed): the replay's
-- compiled twins where the profile put the time.  SealTwin.lean (new): `canonDesc` and the csimp twins of the grouping
-- functions over the checkpoint's four orders, the window facts grouped by date, the item tables, `mergedItems` and
-- `resumedAnswer`, and the day index by bisection (`bisect`, `offsetAtArr`, `dayOfZ`, `dayFn`).  SealWire.lean: the resume
-- over caller-read entries and warnings (`resumeRunV`) and building only what its request wants (`resumeRunW`), the cut
-- check with its fixed parts given (`cutCheckAt`), the state at the cut and the unfolded lows in one fold (`foldCut`), the
-- reseal over caller-read warnings (`resealOfV`).  Boundary.lean: the `log` op reading each line once (`logOpFast`).
#print axioms Lime.Seal.canon_eq_canonDesc
#print axioms Lime.Seal.itemIds_eq_itemIdsFast
#print axioms Lime.Seal.dayKeys_eq_dayKeysFast
#print axioms Lime.Seal.winKeys_eq_winKeysFast
#print axioms Lime.Seal.windowOf_eq_windowOfFast
#print axioms Lime.Seal.instOtherOf_eq_instOtherOfFast
#print axioms Lime.Seal.namedOf_eq_namedOfFast
#print axioms Lime.Seal.storedSlept_eq_storedSleptFast
#print axioms Lime.Seal.mergeTagLines_eq_mergeTagLinesFast
#print axioms Lime.Seal.daysIn_eq_daysInT
#print axioms Lime.Seal.daysFrom_eq_daysFromT
#print axioms Lime.Seal.mem_foldl_groupStep
#print axioms Lime.Seal.windowOfG_eq
#print axioms Lime.Seal.windowsIn_eq_windowsInG
#print axioms Lime.Seal.windowsFrom_eq_windowsFromG
#print axioms Lime.Seal.foldl_firstStep_get
#print axioms Lime.Seal.foldl_doneStep
#print axioms Lime.Seal.foldl_doneIdStep_get
#print axioms Lime.Seal.foldl_incr_get
#print axioms Lime.Seal.foldl_winStep_get
#print axioms Lime.Seal.aggMergedT_eq
#print axioms Lime.Seal.mergedItems_eq_mergedItemsFast
#print axioms Lime.Seal.resumedAnswer_eq_resumedAnswerFast
#print axioms Lime.Seal.bisect_spec
#print axioms Lime.Seal.foldl_last_of_point
#print axioms Lime.Seal.offsetAtArr_eq
#print axioms Lime.Seal.localDateArr_eq
#print axioms Lime.Seal.dayOfZ_eq
#print axioms Lime.Seal.instAscending_pairwise
#print axioms Lime.Seal.dayFn_eq
#print axioms Lime.Seal.resumeRunV_eq
#print axioms Lime.Seal.resumeRunW_eq
#print axioms Lime.Seal.foldl_badStep_all
#print axioms Lime.Seal.firstBadLine_all
#print axioms Lime.Seal.and8_perm
#print axioms Lime.Seal.cutCheckAt_eq
#print axioms Lime.Seal.foldl_lowsStep_of_not
#print axioms Lime.Seal.filter_split_of_pairwise
#print axioms Lime.Seal.foldCut_eq_foldCutFast
#print axioms Lime.Seal.resealOfWith_spec
#print axioms Lime.Seal.resealOfV_eq
#print axioms Lime.foldl_logLineStep_map_verdict
#print axioms Lime.logLines_map_verdict
#print axioms Lime.lineEntries_eq_verdicts
#print axioms Lime.lineWarnings_eq_verdicts
#print axioms Lime.logOpZ_core
#print axioms Lime.logOpCore_map
#print axioms Lime.logOpZFast_core
#print axioms Lime.logOpZ_eq_logOpZFast

-- APPENDED 2026-09-16 (stage 5, W-12).  Step S2 (owner decision D16; design §22.1's "a new step
-- after S", §14.7 F5): the kernel writes the log lines it reads.  `Log.emitEvent`/`Log.emitLine`
-- reuse the reader (`readArgs`) and the writer (`renderLine`) rather than adding a third
-- definition of the format; the `emit` section puts them on the wire.  11 theorems, in Log.lean
-- and Boundary.lean.
#print axioms Lime.Log.renderLine_ignores_the_line
#print axioms Lime.Log.restOf_cons_t_ev
#print axioms Lime.Log.restOf_of_canonical
#print axioms Lime.Log.emitEvent_of_fields
#print axioms Lime.Log.the_log_emits_what_it_reads
#print axioms Lime.Log.the_log_reads_what_it_emits
#print axioms Lime.Log.emitEvent_refuses_what_a_line_could_not_carry
#print axioms Lime.Log.the_kernel_decides_what_is_left_out
#print axioms Lime.runWithEmit_without_an_emit_is_runWithLog
#print axioms Lime.a_request_without_an_emit_is_read_as_before
#print axioms Lime.runWithEmit_refuses_an_emit_section_first

-- APPENDED 2026-09-16 (stage 5, W-12).  Quirk **Q6(f)** (gap 86; owner answer Q6's last column,
-- "fix, after the switch"): a `close` carries `period:key` as its primary id, so `lime undo` of one
-- cancels *that* close and not whichever close is latest.  The quirk's own theorem is renamed in
-- place above, beside the rule it replaces
-- (`an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest`), and the
-- undo law's counterexample is re-witnessed rather than weakened.
#print axioms Lime.Replay.an_automatic_close_of_another_period_is_untouched

-- APPENDED 2026-09-16 (stage 6, W-13, track B).  **D24, gap 210: the seam is opened inside the
-- kernel.**  The `log` op now answers a `LogAnswer` — the bytes it always answered, and the
-- `Seal.Answer` those bytes were rendered from — and `runCapZ` hands that replay to the capacity
-- section, which could not previously reach it (`readCapacityZ` had no argument it could arrive
-- through).  `logOp` is kept as the bytes half, a *view* of `logOpZ`, so every law stated about it
-- before D24 keeps its exact text and its audit line above: the three W4 twin rows are the only
-- renames, and they are renamed in place (`logOpZ_core`, `logOpZFast_core`,
-- `logOpZ_eq_logOpZFast`), the `@[csimp]` now carrying the seam's fourth argument.
--
-- Re-proved over their current shapes, NOT weakened (D5), and audited by their standing lines
-- above: `readLogSection_is_zoneOf_then_logSectionWith` (3180) and
-- `runCap_without_capacity_is_runWithEmit` (3133) are **unchanged, word for word**;
-- `the_zone_is_read_once_and_feeds_both_sections` (3182) is **strengthened** — its capacity
-- conjunct now quantifies over the replay as well (`∀ plan clock rep cap`), so the old statement
-- is its `rep = none` instance and it says strictly more.
--
-- The seam's own laws follow.  `a_capacity_answer_can_depend_on_a_log_fact` is the one that makes
-- the parameter load-bearing rather than decorative (AGENTS §5.2, §5.6): its two `decide`
-- witnesses were probed under `MemoryMax=8G`, `timeout 120`.
#print axioms Lime.within53A_wire
#print axioms Lime.logAnswerOf_carries_the_op
#print axioms Lime.the_capacity_section_reads_the_log_sections_own_replay
#print axioms Lime.runCap_reads_the_capacity_section_against_its_own_log_answer
#print axioms Lime.Look.mkInput?_ok_wake_wf
#print axioms Lime.CapWire.wakeClockOf_sec_lt
#print axioms Lime.CapWire.wakeClockOf_wf
#print axioms Lime.CapWire.resolve_fromLog_without_a_replay
#print axioms Lime.CapWire.resolve_fromLog_without_a_day
#print axioms Lime.CapWire.readCapacityZ_refuses_a_logged_wake_without_a_replay
#print axioms Lime.CapWire.the_capacity_input_is_the_replays_wake
#print axioms Lime.CapWire.a_capacity_answer_can_depend_on_a_log_fact

-- ===========================================================================
-- APPENDED 2026-09-16 (stage 6, run W-13, step **L9** — day 0 is the kernel's
-- own; design §13.5, gap 93).  `Look.Input.day0` and the `badDay0` refusal are
-- **gone**: the kernel derives today from its own replay through D24's seam.
--
-- Two rows above were RENAMED with their theorems, not deleted:
-- `lookahead_day_zero_is_the_hosts` -> `lookahead_day_zero_is_the_kernels`
-- (restated: day 0 is `ofHist I.today (day0Hist I)`), and
-- `mkInput?_refuses_a_bad_day0` -> `mkInput?_refuses_a_now_that_disagrees`
-- (the refusal `badDay0` existed to raise is gone; `nowDisagrees` takes its
-- place in the same position of the constructor's order).
--
-- Site R10 lands here **with its caller** (`Look.todayEnergy`), which is why
-- W-6 and W-12 both refused to land it alone (AGENTS §5.6, §7.4 items 5, 11).
#print axioms Lime.Arith.roundAway_withinOne
#print axioms Lime.Arith.roundAway_mono
#print axioms Lime.Arith.roundAway_examples
#print axioms Lime.Look.predictAt_val
#print axioms Lime.Look.latestBefore_sound
#print axioms Lime.Look.latestBefore_none_of_all_after
#print axioms Lime.Look.weightAt_full
#print axioms Lime.Look.weightAt_zero
#print axioms Lime.Look.correctAt_without_a_report
#print axioms Lime.Look.the_posterior_rounds_a_half_the_way_the_fork_does
#print axioms Lime.Look.day0_slots_are_inside_the_window
#print axioms Lime.Look.day0_slots_avoid_the_walls
#print axioms Lime.Look.day0_after_the_window_is_empty
#print axioms Lime.Look.day0Six_get
#print axioms Lime.Look.the_day_zero_histogram_is_not_limited_to_the_budget
#print axioms Lime.Look.day_zero_is_the_spec_day_energised
#print axioms Lime.Look.day_zero_is_cut_from_now
#print axioms Lime.Look.day_zero_reads_the_stored_window
#print axioms Lime.Look.todays_posterior_moves_todays_levels
#print axioms Lime.Look.a_short_night_shifts_every_level
#print axioms Lime.Look.day_zero_reads_todays_location
#print axioms Lime.Look.weightAt_antitone
#print axioms Lime.CapWire.boundedPos_zero_den
#print axioms Lime.CapWire.boundedPos_wide_den
#print axioms Lime.CapWire.boundedPos_large_num
#print axioms Lime.CapWire.boundedPos_ok

-- ===========================================================================
-- APPENDED 2026-09-16 (stage 6, run **W-13 repair**, defect 1 — the nine
-- theorems step L9 declared and did not audit).
--
-- AGENTS §6.3 gives two ways to end a step: append the audit lines, **or**
-- record the omission by name in the README block.  `5ab24bf` did neither, and
-- its block said the opposite twice ("New theorems: **26**, every one with an
-- audit line").  The three §6.3 counts read 3984 / 3984 / **3993** at that
-- commit; they reconciled exactly at `0585e72`, `f9ee3d0` and `455ac8d`.
--
-- The nine are helper lemmas — nothing imports `Goals.lean` and check 3 finds
-- no `sorryAx`, so this was never a soundness hole; the audit was simply nine
-- short while the printed count said healthy.  That is gap 260's shape exactly
-- (the audit has a count, not a roster), and check 3 now carries the §6.3
-- reconciliation so a declared theorem can no longer go unaudited in silence.
#print axioms Lime.Arith.Signed.den_pos
#print axioms Lime.Arith.halfUpQ_of_zero_num
#print axioms Lime.Arith.roundAway_withinOne_aux
#print axioms Lime.Arith.roundAway_mono_aux

-- W-27's repair step: four `private theorem`s and one INDENTED theorem were
-- declared in the library and audited by nobody, because `check.sh`'s check-3
-- roster grep anchored `theorem` at column zero with at most one attribute in
-- front of it.  The enumeration hole had moved from the WALK (W-21), to the
-- LIBRARY ROOT (W-23), to the DECLARATION SHAPE.  The grep is a shape now, and
-- `private` is off these four so that this file can name them: a lemma nothing
-- else may cite is still a lemma the audit must see.
#print axioms Lime.Arith.cancelR
#print axioms Lime.Look.keepsIt_le
#print axioms Lime.Look.latestBefore_nil
#print axioms Lime.Look.latestBefore_go
#print axioms Lime.Look.SleepCfg.shiftOf_without_sleep
#print axioms Lime.Look.day0Cut_eq

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-14**, track P step **P0** — the
-- planner's vocabulary: `Planner.lean`, `Seg` on absolute seconds, `PlanReq`
-- without a second window).
--
-- Fifty-six theorems: R10's smart constructors and their rejections, R11's
-- `view ∘ set = id` pairs, the two `Look.Today` budget laws L9's `storedWindow`
-- needed beside it, and `dayPlan`'s shape.
--
-- Two of them were TRIPWIRES and were meant to stop compiling.  Step P1 took
-- the first one (`the_day_has_no_segments_until_the_first_step_lands`, deleted
-- with `dayPlan_diagnostics` and `dayPlan_assigns_nothing_yet`, which P1's body
-- made false); `the_plan_hash_is_a_placeholder_until_the_emitter_lands` still
-- stands and is P8's.  P1's own tripwire, in the block below, is
-- `the_day_assigns_nothing_after_now_until_the_assign_step_lands`.
-- ===========================================================================
#print axioms Lime.Look.Today.storedBudget_on_another_day
#print axioms Lime.Look.Today.storedBudget_today
#print axioms Lime.Look.Today.storedWindow_brings_a_budget
#print axioms Lime.Planner.Capped.ofList?_refuses_past_the_cap
#print axioms Lime.Planner.Capped.ofList?_accepts
#print axioms Lime.Planner.Capped.cons?_refuses_past_the_cap
#print axioms Lime.Planner.Capped.val_cons?
#print axioms Lime.Planner.mkBatch?_refuses_too_many_members
#print axioms Lime.Planner.mkBatch?_accepts
#print axioms Lime.Planner.mkSeg?_refuses_an_inverted_segment
#print axioms Lime.Planner.mkSeg?_refuses_past_the_horizon
#print axioms Lime.Planner.mkSeg?_accepts
#print axioms Lime.Planner.Seg.energy_withEnergy
#print axioms Lime.Planner.Seg.withEnergy_touches_only_the_energy
#print axioms Lime.Planner.Seg.wf_withEnergy
#print axioms Lime.Planner.Seg.note_withNote
#print axioms Lime.Planner.Seg.withNote_touches_only_the_note
#print axioms Lime.Planner.Seg.wf_withNote
#print axioms Lime.Planner.Diagnostics.notes_withNote
#print axioms Lime.Planner.Diagnostics.withNote_touches_only_the_notes
#print axioms Lime.Planner.Diagnostics.droppedTail_withDropped
#print axioms Lime.Planner.Diagnostics.withDropped_touches_only_the_dropped_tail
#print axioms Lime.Planner.mkBudget?_refuses_an_impossible_budget
#print axioms Lime.Planner.mkBudget?_accepts
#print axioms Lime.Planner.mkActive?_accepts
#print axioms Lime.Planner.RuntimeIn.activeId_empty
#print axioms Lime.Planner.PlanOverrides.isEmpty_empty
#print axioms Lime.Planner.assignedOf_empty
#print axioms Lime.Planner.blockSeconds_empty
#print axioms Lime.Planner.PlanReq.window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_unless_a_windowless_day_has_only_a_logged_arrival_or_a_wall_passes_its_bounds
#print axioms Lime.Planner.PlanReq.budget_is_the_stored_one_when_there_is_one
#print axioms Lime.Planner.PlanReq.budget_is_the_formula_without_a_budget_on_its_day
#print axioms Lime.Planner.dayPlan_day
#print axioms Lime.Planner.dayPlan_window
#print axioms Lime.Planner.dayPlan_blockMin
#print axioms Lime.Planner.dayPlan_budgetBlocks

-- ===========================================================================
-- STAGE 6, W-14 TRACK P, STEP P1 (2026-09-17): the walls
--
-- Appended for step P1 (design 14.2's P1 row): 8.2 step 1 in `Planner.lean`,
-- on the wall set stage 5 already indexes.  `Look.WallIx` is WIDENED, not
-- forked (AGENTS 5.3): it carries the item id it always had in scope and the
-- event's own start that `buffer:` used to fold away, and `Look.wallIxOn` is
-- `wallsOn`'s own selection with the projection left off, so the day's window,
-- the day's cut and the day's rows read ONE rule about which walls are today's.
--
-- Forty-one theorems.  Two are RUN rather than argued -- AGENTS 5.2's non-vacuity
-- check -- and two are findings named as such:
--
--   * `the_spec_days_walls_are_placed_where_they_are_written` and
--     `the_spec_days_clash_is_named_once` -- 8.2 step 1 evaluated on the 4.3
--     Monday with a `buffer:1h` meeting and a second one that clashes with it:
--     three rows at the six seconds the index wrote, and the pair named once.
--
--   * `plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted` -- the goal's
--     form is FALSE against the fork (a `buffer:` puts a second Wall row in
--     front of the event; a wall past midnight is clipped to the day), refuted
--     and restated with `plan_never_moves_a_wall` and
--     `a_wall_row_comes_from_the_index` beside it (AGENTS 3.1 item 3, D5).
--   * `the_day_assigns_nothing_after_now_until_the_assign_step_lands` -- the
--     TRIPWIRE P5 must delete.  Step 1 places no Block of its own, so
--     `plan_places_no_block_over_a_wall` is NOT discharged here: it is vacuous
--     over this body and design 6.4's row that gives it to P1 is wrong
--     (README gap 347).
--     [BANNER, W-17 track G: two names in this bullet have moved and the
--     sentence is left standing as the record of what was true when it was
--     written.  The tripwire is `Planner.the_day_assigns_nothing_after_now
--     _but_the_running_block` since step P3 (choice 5b's reservation made the
--     empty-list form false).  And `plan_places_no_block_over_a_wall` is
--     DISCHARGED as of W-17 -- still not by this body, which is what the
--     sentence says, but as `PlanCheck.plan_places_no_block_over_a_wall`, over
--     the Block rows that start at or after `now`, with its refutation in
--     `PlannerWit`.  See this file's last banner.]
-- ===========================================================================
#print axioms Lime.Look.mem_wallIxOn
#print axioms Lime.Look.wallsOn_eq_map_wallIxOn
#print axioms Lime.Look.wallOfEntity_lo_is_evLo_without_a_buffer
#print axioms Lime.Look.wallOfEntity_keeps_the_id
#print axioms Lime.Look.wallOfEntity_evLo_is_the_written_start
#print axioms Lime.Planner.Capped.ofListTake_keeps_everything_below_the_cap
#print axioms Lime.Planner.Capped.ofListTake_is_a_prefix
#print axioms Lime.Planner.mem_assignedOf
#print axioms Lime.Planner.a_wall_is_not_work
#print axioms Lime.Planner.instant_wf_of_sec
#print axioms Lime.Planner.the_horizon_is_cal_instants_own_bound
#print axioms Lime.Planner.Seg.wf_of
#print axioms Lime.Planner.clampSec_lt
#print axioms Lime.Planner.clampSec_id
#print axioms Lime.Planner.segOf_is_the_row_inside_the_calendar
#print axioms Lime.Planner.segOf_kind
#print axioms Lime.Planner.segOf_item
#print axioms Lime.Planner.wallsToday_is_wallsOfDay
#print axioms Lime.Planner.mem_wallsToday
#print axioms Lime.Planner.clipWall_id
#print axioms Lime.Planner.clipWall_within
#print axioms Lime.Planner.clipWall_id_inside
#print axioms Lime.Planner.the_spec_days_clash_is_named_once
#print axioms Lime.Planner.wallConflicts_nil
#print axioms Lime.Planner.mem_wallConflicts
#print axioms Lime.Planner.a_travel_day_has_no_budget
#print axioms Lime.Planner.remainingBudget_le_budget
#print axioms Lime.Planner.wallRows_are_walls_of_the_item
#print axioms Lime.Planner.the_event_row_is_the_event
#print axioms Lime.Planner.wallRows_without_a_buffer
#print axioms Lime.Planner.the_spec_days_walls_are_placed_where_they_are_written
#print axioms Lime.Planner.interruptRows_are_open_lost_time
#print axioms Lime.Planner.interruptRows_are_not_walls
#print axioms Lime.Planner.pastRows_end_at_now
#print axioms Lime.Planner.pastRows_are_not_walls
#print axioms Lime.Planner.sortRows_eq_sortRowsFast
#print axioms Lime.Planner.mem_sortRows
#print axioms Lime.Planner.mem_dayRows
#print axioms Lime.Planner.dayPlan_segments
#print axioms Lime.Planner.dayPlan_remaining_budget_is_the_forks_local
#print axioms Lime.Planner.plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted
#print axioms Lime.Planner.plan_never_moves_a_wall
#print axioms Lime.Planner.a_wall_row_comes_from_the_index

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-14**, track G — L26's eleven single-run
-- laws as one checker battery: `PlanCheck.lean`, design §6).
--
-- Fifty-nine theorems: the eleven reflection lemmas and their per-element
-- helpers, `checks_all` and the eleven one-line bridges a P step's discharge
-- will be, the fold induction's base case, the eleven non-vacuity witnesses
-- (AGENTS §5.2 — a battery that cannot refuse means nothing), and the list
-- arithmetic D29's refutation will apply.
--
-- ONE of them was a TRIPWIRE and IT FIRED.  `dayPlan_ok_core_given_the_budget` is §6.1's lift
-- over the seven eligibility-free checks; track G proved it in one line over
-- P0's empty day, from
-- `Planner.the_day_has_no_segments_until_the_first_step_lands`.  P1 deleted that
-- theorem, and the LAND step (W-14, gaps 385-389) re-proved the lift over the
-- day P1 produces.  It could not be re-proved unchanged: the form track G wrote
-- is FALSE of the filled day, twice over -- the replayed past holds Blocks the
-- planner did not place, and `wallsUnmoved` is the form P1 refuted (`buffer:`,
-- the midnight clip).  NO CHECKER WAS WEAKENED; the two findings are carried as
-- named hypotheses (`hnopast`, `hagree`/`hplain`), exactly as P1 carried them on
-- `plan_never_moves_a_wall`.  Gap 385 is the record, and two theorems were added
-- beside the lift (`dayPlan_block_rows_come_from_the_log`, unconditional, and
-- `dayPlan_has_no_block_row_when_nothing_runs_or_is_assigned`).
--
-- `dayPlan_ok_at_every_eligibility_while_the_day_is_empty` is GONE, and its name
-- is why: it was stated about a day with no segments and P1's day has some.  It
-- loses nothing -- `planOk_of_no_segments` is the general lemma and stays.
--
-- **No goal was discharged here** — see `Goals.lean`'s stage-6 header and
-- `PlanCheck.lean`'s own.
-- ===========================================================================
#print axioms Lime.PlanCheck.withoutActive_segments
#print axioms Lime.PlanCheck.noOverbook_iff
#print axioms Lime.PlanCheck.oneBlockAtATime_iff
#print axioms Lime.PlanCheck.energyOk_iff
#print axioms Lime.PlanCheck.energyFilterOk_iff
#print axioms Lime.PlanCheck.noBlockOverAWall_iff
#print axioms Lime.PlanCheck.noBlockOverABreak_iff
#print axioms Lime.PlanCheck.windDownOk_iff
#print axioms Lime.PlanCheck.noDemandingAfterWindDown_iff
#print axioms Lime.PlanCheck.wallUnmoved_iff
#print axioms Lime.PlanCheck.wallsUnmoved_iff
#print axioms Lime.PlanCheck.rankPairOk_iff
#print axioms Lime.PlanCheck.hotPairOk_iff
#print axioms Lime.PlanCheck.impossibleKept_iff
#print axioms Lime.PlanCheck.batchPairOk_iff
#print axioms Lime.PlanCheck.checksOf_length
#print axioms Lime.PlanCheck.checksCore_length
#print axioms Lime.PlanCheck.checks_all
#print axioms Lime.PlanCheck.checksCore_all
#print axioms Lime.PlanCheck.planOk_imp_core
#print axioms Lime.PlanCheck.overbook_from_the_battery
#print axioms Lime.PlanCheck.one_block_from_the_battery
#print axioms Lime.PlanCheck.energy_filter_from_the_battery
#print axioms Lime.PlanCheck.no_block_over_a_wall_from_the_battery
#print axioms Lime.PlanCheck.no_block_over_a_break_from_the_battery
#print axioms Lime.PlanCheck.wind_down_from_the_battery
#print axioms Lime.PlanCheck.walls_unmoved_from_the_battery
#print axioms Lime.PlanCheck.monotone_in_rank_from_the_battery
#print axioms Lime.PlanCheck.hot_before_queue_from_the_battery
#print axioms Lime.PlanCheck.impossible_kept_from_the_battery
#print axioms Lime.PlanCheck.mem_dom_of_get
#print axioms Lime.PlanCheck.assignedOf_of_no_segments
#print axioms Lime.PlanCheck.eligibleSomewhere_of_no_segments
#print axioms Lime.PlanCheck.planOkCore_of_no_segments
#print axioms Lime.PlanCheck.a_replayed_row_is_a_row_of_the_day
#print axioms Lime.PlanCheck.a_replayed_block_is_assigned
#print axioms Lime.PlanCheck.dayPlan_has_no_block_row_when_nothing_runs_or_is_assigned
#print axioms Lime.PlanCheck.dayPlan_ok_core_given_the_budget
#print axioms Lime.PlanCheck.all_eq_false_of_mem
#print axioms Lime.PlanCheck.wSeg_wf
#print axioms Lime.PlanCheck.horizonOk
#print axioms Lime.PlanCheck.wDay_segments
#print axioms Lime.PlanCheck.effectiveCi_of_an_absent_id
#print axioms Lime.PlanCheck.aBlockOfAnHour_is_not_the_reservation
#print axioms Lime.PlanCheck.noOverbook_can_fail
#print axioms Lime.PlanCheck.oneBlockAtATime_can_fail
#print axioms Lime.PlanCheck.energyFilterOk_can_fail
#print axioms Lime.PlanCheck.noBlockOverAWall_can_fail
#print axioms Lime.PlanCheck.noBlockOverABreak_can_fail
#print axioms Lime.PlanCheck.noDemandingAfterWindDown_can_fail
#print axioms Lime.PlanCheck.wallsUnmoved_can_fail
#print axioms Lime.PlanCheck.assignedOf_theOnlyJIsAssignedDay
#print axioms Lime.PlanCheck.eligibleSomewhere_permissive
#print axioms Lime.PlanCheck.monotoneInRank_can_fail
#print axioms Lime.PlanCheck.hotBeforeQueue_can_fail
#print axioms Lime.PlanCheck.assignedOf_theBatchDay
#print axioms Lime.PlanCheck.batchDoesNotReachPast_can_fail
#print axioms Lime.PlanCheck.impossibleKept_can_fail
#print axioms Lime.PlanCheck.planOkCore_can_fail
#print axioms Lime.PlanCheck.planOk_can_fail
#print axioms Lime.PlanCheck.a_kept_reservation_defeats_the_prefix_but_not_the_erasure

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-15**, track P, step P2 — §8.2 step 2:
-- the routines, the evening, and gap 285's named refusal).
--
-- Thirty-two theorems.  Three are `Lookahead.lean`'s: `[day]` was WIDENED with
-- §16's `wind_down` and `bed` rather than forked into `Planner.lean`, and the
-- three `the_evening_keys_do_not_move_…` lines are the projections that say
-- every reader `DayCfg` had before P2 sees the record it had before P2
-- (AGENTS §5.3).  The rest are the step's own: the placement engine on L3's
-- `freeIntervals`, `mkRoutine?`'s five named refusals (the second of which IS
-- README gap 285), the fold invariant that a placed routine is inside its
-- window, and the four "no row step 2 places is a Wall / a Block / work"
-- lemmas that let P1's laws keep their proofs over a day with a fourth source
-- of rows.
--
-- One line above was EDITED rather than appended: `Lime.Planner.mem_stepOneRows`
-- is `Lime.Planner.mem_dayRows`, because the day's rows are no longer step one's
-- alone.  §6.3 forbids editing this file in *parallel*; a rename leaves check 3
-- naming an unknown constant, so it is fixed here and named in the README block.
-- ===========================================================================

#print axioms Lime.Look.the_evening_keys_do_not_move_the_window
#print axioms Lime.Look.the_evening_keys_do_not_move_the_cut
#print axioms Lime.Look.the_evening_keys_do_not_move_the_budget
#print axioms Lime.Planner.the_night_is_in_order
#print axioms Lime.Planner.earliestFree_inside
#print axioms Lime.Planner.earliestFree_is_free
#print axioms Lime.Planner.overlapsAny_false_covers_nothing
#print axioms Lime.Planner.overlapsAny_true_of_covered
#print axioms Lime.Planner.mkRoutine?_refuses_an_unknown_item
#print axioms Lime.Planner.mkRoutine?_refuses_a_window_the_item_does_not_declare
#print axioms Lime.Planner.mkRoutine?_refuses_an_empty_window
#print axioms Lime.Planner.mkRoutine?_refuses_past_the_horizon
#print axioms Lime.Planner.mkRoutine?_refuses_an_instance_with_no_minutes
#print axioms Lime.Planner.mkRoutine?_accepts
#print axioms Lime.Planner.mkRoutine?_ok_is_wf
#print axioms Lime.Planner.mkRoutines?_refuses_too_many
#print axioms Lime.Planner.mkRoutines?_refuses_when_one_is_refused
#print axioms Lime.Planner.isSleepId_accepts_the_written_spellings
#print axioms Lime.Planner.splitSleep_keeps_the_rest
#print axioms Lime.Planner.mem_sortRoutines
#print axioms Lime.Planner.placeStep_keeps_PlacedOk
#print axioms Lime.Planner.foldl_placeStep_keeps_PlacedOk
#print axioms Lime.Planner.a_placed_routine_is_inside_its_window
#print axioms Lime.Planner.stepTwoSegs_kinds
#print axioms Lime.Planner.stepTwoSegs_are_not_walls
#print axioms Lime.Planner.stepTwoSegs_are_not_blocks
#print axioms Lime.Planner.stepTwoSegs_are_not_work
#print axioms Lime.Planner.a_routine_row_is_where_the_placement_put_it
#print axioms Lime.Planner.the_wind_down_row_runs_to_bed
#print axioms Lime.Planner.the_earliest_free_position_is_run
#print axioms Lime.Planner.the_evening_is_closed_to_a_routine
#print axioms Lime.Planner.a_deferred_routine_has_no_row
-- W-15 track K, K3a (D31, gap 301): the item grammar widened — the state box
-- is optional and an id-less line is keyed by its title (`Field.titleKey`).
-- `Lime.parseLine` is the store's reading; `Lime.parseItem` stays the file's.
#print axioms Lime.an_unflagged_optional_is_open
#print axioms Lime.an_unflagged_routine_is_open
#print axioms Lime.bareOk_any
#print axioms Lime.boxAt_eq_some
#print axioms Lime.boxAt_none_of_head
#print axioms Lime.canonicalKeyed_of_canonical_box_ended
#print axioms Lime.Field.findSome_kParent_phase0
#print axioms Lime.Field.kinds_bare
#print axioms Lime.Field.kinds_boxed
#print axioms Lime.parseBody_bare
#print axioms Lime.parseLine_ok
#print axioms Lime.parseToks_ok
#print axioms Lime.serialize_parse_id
#print axioms Lime.serialize_parseLine
#print axioms Lime.the_flag_is_still_read_off_a_week_line
#print axioms Lime.the_spec_routine_line_is_a_title_keyed_item
#print axioms Lime.the_spec_routine_line_round_trips
#print axioms Lime.Field.titleKey_congr
#print axioms Lime.a_boxless_line_cannot_carry_a_state
#print axioms Lime.a_boxless_todo_line_is_well_formed
#print axioms Lime.boxesWf_set
#print axioms Lime.boxWf_of_mem
#print axioms Lime.Field.setKey_boxed
#print axioms Lime.setVal_boxed
#print axioms Lime.a_routine_line_is_an_item
#print axioms Lime.an_optional_line_is_keyed_by_its_whole_title
#print axioms Lime.a_bare_line_has_no_positional_slots
#print axioms Lime.an_empty_bullet_is_prose
#print axioms Lime.a_front_matter_rule_is_prose
#print axioms Lime.a_bare_line_may_carry_its_id
#print axioms Lime.the_three_refusals_are_unchanged
#print axioms Lime.effectiveScope
#print axioms Lime.a_routine_line_loads_as_an_entity
#print axioms Lime.two_titles_in_one_file_are_a_dupId
#print axioms Lime.a_title_colliding_with_an_id_is_refused
#print axioms Lime.parseLine_serializeItem
/-! ############################################################################
## Stage 6, track W (run W-15): the `PlanReq` builder and its witnesses
`LimeKernel/Laws/PlannerWit.lean` — README gap 348, and the three gaps it blocked (366's
refutation half, 393's witness half, 396).  Nothing imports this module; it is the
end-to-end witness `Planner.lean` and `PlanCheck.lean` could not write.
############################################################################ -/
#print axioms Lime.PlannerWit.mkPlanReq?_refuses_a_plan_the_loader_refuses
#print axioms Lime.PlannerWit.mkPlanReq?_refuses_an_input_the_decoder_refuses
#print axioms Lime.PlannerWit.mkPlanReq?_refuses_a_wall_index_that_is_not_the_plans
#print axioms Lime.PlannerWit.mkPlanReq?_refuses_a_run_the_guards_refuse
#print axioms Lime.PlannerWit.mkPlanReq?_ok_wallsAgree
#print axioms Lime.PlannerWit.mkPlanReq?_ok_parts
#print axioms Lime.PlannerWit.witInput_decodes_ok
#print axioms Lime.PlannerWit.witInput_decodes
#print axioms Lime.PlannerWit.witInput_fields
#print axioms Lime.PlannerWit.lookWallPlan_loads
#print axioms Lime.PlannerWit.witRun_resumes_ok
#print axioms Lime.PlannerWit.witRun_resumes
#print axioms Lime.PlannerWit.witBuilds
#print axioms Lime.PlannerWit.theRequest_wallsAgree
#print axioms Lime.PlannerWit.the_witness_day_is_two_replayed_blocks_the_written_wall_and_the_evening
#print axioms Lime.PlannerWit.the_witness_day_is_planned_from_the_logged_arrival
#print axioms Lime.PlannerWit.the_witness_assigns_the_two_replayed_blocks
#print axioms Lime.PlannerWit.the_witness_assigns_nothing_after_now
#print axioms Lime.PlannerWit.the_battery_passes_at_the_witness
#print axioms Lime.PlannerWit.the_witness_replays_a_block
#print axioms Lime.PlannerWit.the_witness_defeats_the_lifts_hypothesis
#print axioms Lime.PlannerWit.the_battery_bites_at_the_witness
#print axioms Lime.PlannerWit.witRun0_resumes_ok
#print axioms Lime.PlannerWit.witRun0_resumes
#print axioms Lime.PlannerWit.witBuilds0
#print axioms Lime.PlannerWit.the_quiet_day_assigns_nothing
#print axioms Lime.PlannerWit.the_budget_moves_the_assigned_set_at_the_busy_request

#print axioms Lime.PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin
#print axioms Lime.PlannerWit.erasing_the_active_item_does_not_repair_a_law_whose_run_is_free

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-15**, the LAND step — the two
-- theorems the merge of tracks K, P and W had to add, plus one rename).
--
-- The rename is `Lime.PlannerWit.the_witness_day_is_two_replayed_blocks_and_the
-- _written_wall`, whose line above was EDITED rather than appended: P2 put
-- §16's `wind_down` and `bed` in the day track W wrote that equation against,
-- so the three-row form is FALSE and the equation is re-proved over five rows
-- under the name it now deserves (D5, AGENTS §5.2).  Every prose citation was
-- grepped and moved with it.
-- ===========================================================================
#print axioms Lime.Planner.mkRoutines?_of_none
#print axioms Lime.Planner.splitSleep_congr
#print axioms Lime.PlannerWit.the_witness_carries_no_routine
#print axioms Lime.PlannerWit.mkPlanReq?_refuses_a_routine_the_rule_refuses

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-16**, track A — **D32 item 1**, gap
-- 475: `LErr.dupId`, `.notADemotion` and `.ambiguousDemotion` widened to carry
-- BOTH colliding lines' `path` and `line`.
--
-- The order the two lines are named in is a total order on `Spot` (`charsLe`
-- on the path, then the line), because `pairedEntity_order_independent` — the
-- theorem that refutes AGENTS §5.6's defect — has to hold of what the refusal
-- *says* and not only of which constructor it uses.  `spotPair_comm` is that,
-- and `buildEntity_collision_is_a_projection` is §5.3's obligation: the two
-- new fields are `Placement.spot` of placements the loader already held, and
-- `.map Placement.id` over them gives back the one `Id` the error used to be.
--
-- MOVED at W-16's repair step: this block declared `Lime.charsLe_antisymm` and
-- `Lime.charsLe_total` over a SECOND `charsLe` written in `Boundary.lean`.  The
-- fork is deleted and both laws are proved on `Lime.Log.charsLe`, the one
-- lexicographic order this package has (AGENTS §5.3); the two lines moved to
-- the repair step's own banner at the end of this file, and `spotLe` now calls
-- `Log.charsLe`.
-- ===========================================================================
#print axioms Lime.spotLe_antisymm
#print axioms Lime.spotLe_total
#print axioms Lime.spotPair_comm
#print axioms Lime.placementSpots_comm
#print axioms Lime.spotPair_cases
#print axioms Lime.pairedEntity_error_spots
#print axioms Lime.buildEntity_collision_is_a_projection
#print axioms Lime.buildEntity_is_never_asked_about_an_absent_id
-- APPENDED 2026-09-17 (stage 6, run **W-16**, track K step **K3b** — §5's
-- recurrence family inside the kernel: `Recur.lean` (new, with its import line
-- in `LimeKernel.lean`), the `doneDatesIn` widening in `Replay.lean` and
-- `SealAgg2.lean`, and the four end-to-end witnesses in `PlannerWit.lean`.
--
-- No goal is discharged and none is added: the burn-down is 12 before and 12
-- after.  Nothing in the shipped binary calls `Recur.lean`.
-- ===========================================================================
#print axioms Lime.Replay.mem_instancesOf

#print axioms Lime.Recur.dateOfT_atClock
#print axioms Lime.Recur.dateOfT_endOfDay
#print axioms Lime.Recur.a_close_at_or_after_now_needs_the_seconds
#print axioms Lime.Recur.parseInstKey_renderInstKey_nth
#print axioms Lime.Recur.eachDayGo_length_le
#print axioms Lime.Recur.eachDay_length_le
#print axioms Lime.Recur.eachDayGo_mem
#print axioms Lime.Recur.eachDay_mem
#print axioms Lime.Recur.phaseEpoch_is_1970_01_01
#print axioms Lime.Recur.the_two_epochs_are_the_dates_the_fork_names
#print axioms Lime.Recur.mondayOf_is_a_monday
#print axioms Lime.Recur.dayHere_length_le
#print axioms Lime.Recur.monthHere_length_le
#print axioms Lime.Recur.monthsGo_length_le
#print axioms Lime.Recur.weekHere_length_le
#print axioms Lime.Recur.mondaysGo_length_le
#print axioms Lime.Recur.placeMinutesOf_is_declaredDur_off_an_interval
#print axioms Lime.Recur.placeMinutesOf_and_declaredDur_differ_on_an_interval
#print axioms Lime.Recur.todayInstances_length_le
#print axioms Lime.Recur.todayInstances_singleton
#print axioms Lime.Recur.every_day_is_every_day
#print axioms Lime.Recur.every_weekday_and_every_thursday_pick_their_days
#print axioms Lime.Recur.every_three_days_counts_from_the_anchor_and_not_from_the_range
#print axioms Lime.Recur.every_two_weeks_skips_a_week
#print axioms Lime.Recur.every_week_is_monday_to_sunday
#print axioms Lime.Recur.every_month_31_clamps_in_february
#print axioms Lime.Recur.a_daily_window_closes_on_its_own_date_unless_it_runs_overnight
#print axioms Lime.Recur.an_instance_key_reads_back_both_ways
#print axioms Lime.Recur.a_future_anchor_does_not_collapse_the_phase

#print axioms Lime.PlannerWit.the_recur_witness_loads
#print axioms Lime.PlannerWit.recurDay_is_the_witness_wednesday
#print axioms Lime.PlannerWit.the_lunch_routine_is_todays_mandatory_window_at_noon
#print axioms Lime.PlannerWit.the_lunch_routine_is_gone_by_two_in_the_afternoon
#print axioms Lime.PlannerWit.the_persist_witness_loads
#print axioms Lime.PlannerWit.a_persist_routine_is_one_carried_obligation_not_sixty_one
-- APPENDED 2026-09-17: stage 6 (the planner), run W-16, track P, step P3 —
-- §8.2 step 3 (the slot cut, on L3's own `Look.cutSlots`, and the slot energies
-- on L4's own `Look.energizeToday`) and §8.2 choice 5b (the running block
-- reserved before the routines and before the cut).
--
-- THREE AUDIT LINES WERE DELETED BY THIS STEP, and each is a theorem the
-- reservation made FALSE, restated in the same commit (AGENTS §3.1 item 3, D5):
--   Lime.Planner.a_block_row_is_a_replayed_row
--       -> Lime.Planner.a_block_row_is_replayed_reserved_or_assigned
--   Lime.Planner.the_day_assigns_nothing_after_now_until_the_assign_step_lands
--       -> Lime.Planner.the_day_assigns_after_now_the_running_block_and_what_step_five_chose
--   Lime.PlanCheck.dayPlan_block_rows_come_from_the_log
--       -> Lime.PlanCheck.dayPlan_block_rows_are_replayed_reserved_or_assigned
-- All three were grepped repo-wide, prose included, before the rename.
--
-- ONE GOAL LEFT Goals.lean: plan_reserves_one_block_at_a_time, restated over
-- the Block rows that start at or after `now` and proved in Planner.lean, with
-- PlannerWit.plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted
-- beside it.  Burn-down 12 -> 11.
-- ===========================================================================
#print axioms Lime.Look.day0Slots_is_energizeToday
#print axioms Lime.Planner.segOf_units
#print axioms Lime.Planner.PlanReq.activeAgrees_of_none
#print axioms Lime.Planner.PlanReq.activeAgrees_of_mkActive?
#print axioms Lime.Planner.PlanReq.blockMin_pos
#print axioms Lime.Planner.the_block_boundary_is_run
#print axioms Lime.Planner.PlanReq.currentBlockEnd_within_a_block
#print axioms Lime.Planner.PlanReq.activeRun_spec
#print axioms Lime.Planner.PlanReq.the_reservation_is_at_most_one_block
#print axioms Lime.Planner.PlanReq.the_reservation_is_free_of_every_wall
#print axioms Lime.Planner.PlanReq.the_reservation_stops_at_the_limit
#print axioms Lime.Planner.PlanReq.mem_activeRow
#print axioms Lime.Planner.PlanReq.activeRow_is_an_energyless_block
#print axioms Lime.Planner.placeStep_grows_the_blocked
#print axioms Lime.Planner.placeStep_keeps_PlacedOffThe
#print axioms Lime.Planner.foldl_placeStep_grows_the_blocked
#print axioms Lime.Planner.foldl_placeStep_keeps_PlacedOffThe
#print axioms Lime.Planner.a_routine_is_never_placed_over_the_running_block
#print axioms Lime.Planner.PlanReq.todayCut_is_the_lookaheads
#print axioms Lime.Planner.PlanReq.energisedSlots_are_the_lookaheads
#print axioms Lime.Planner.PlanReq.a_slots_level_is_todays_energy
#print axioms Lime.Planner.PlanReq.a_slot_is_inside_the_window
#print axioms Lime.Planner.PlanReq.a_slot_touches_nothing_blocked
#print axioms Lime.Planner.PlanReq.no_slot_touches_the_running_block
#print axioms Lime.Planner.PlanReq.no_slot_reaches_the_evening
#print axioms Lime.Planner.PlanReq.the_reservation_never_runs_under_a_wind_down_row
#print axioms Lime.Planner.PlanReq.no_slot_overlaps_a_break
#print axioms Lime.Planner.PlanReq.a_slot_is_at_most_one_block
#print axioms Lime.Planner.pastRows_are_not_wind_down
#print axioms Lime.Planner.a_wind_down_row_is_the_evenings
#print axioms Lime.Planner.reservationSegs_are_blocks
#print axioms Lime.Planner.reservationSegs_are_not_walls
#print axioms Lime.Planner.the_reservation_row_names_the_running_item
#print axioms Lime.Planner.the_reservation_row_is_exact
#print axioms Lime.Planner.mem_dayRows_of_mem
#print axioms Lime.Planner.mem_assignedFrom
#print axioms Lime.Planner.the_day_assigns_after_now_the_running_block_and_what_step_five_chose
#print axioms Lime.Planner.a_wall_row_sits_in_a_blocked_span
#print axioms Lime.Planner.a_wind_down_row_of_the_day
#print axioms Lime.Planner.a_block_row_is_replayed_reserved_or_assigned
#print axioms Lime.Planner.plan_reserves_one_block_at_a_time
#print axioms Lime.PlanCheck.dayPlan_block_rows_are_replayed_reserved_or_assigned
#print axioms Lime.PlanCheck.dayPlan_block_rows_are_the_reservation_on_an_unassigned_day
#print axioms Lime.PlannerWit.witBuildsRun
#print axioms Lime.PlannerWit.the_running_request_agrees
#print axioms Lime.PlannerWit.the_reservation_is_clipped_to_the_block_it_is_in
#print axioms Lime.PlannerWit.the_reserved_day_is_the_witness_day_and_the_running_block
#print axioms Lime.PlannerWit.the_reservation_row_carries_no_energy
#print axioms Lime.PlannerWit.the_reserved_day_assigns_the_running_block
#print axioms Lime.PlannerWit.the_battery_passes_at_the_reserved_day
#print axioms Lime.PlannerWit.the_battery_bites_on_the_reservation
#print axioms Lime.PlannerWit.the_short_block_day_holds_a_block_longer_than_a_block
#print axioms Lime.PlannerWit.plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted

-- ===========================================================================
-- APPENDED 2026-09-17 (stage 6, run **W-16**, the REPAIR step — the two
-- auditors' findings.
--
-- `Log.charsLe`'s three order laws.  W-16 shipped THREE definitions of one
-- lexicographic order — `Log.charsLe` (stage 4), `Boundary.charsLe` (track A,
-- `9fa58fc`) and `Recur.charsLe` (track K, `648a160`) — with the two new ones
-- covered by an explicit "re-implemented nothing" claim.  Both forks are
-- deleted and their call sites (`spotLe`, `keyedLe`) consume `Log.charsLe`;
-- the two laws track A proved on its fork are proved here on the real one, and
-- transitivity is added beside them.
--
-- That closes **gap 394** as well, which had stayed open for exactly these
-- lemmas: `Replay.insSort_eq_mergeSort` wants the order transitive and total,
-- so `Planner.wallsOfDay`'s and `sortRoutines`' specification sorts could not
-- have compiled twins.  Both have one now.
-- ===========================================================================
#print axioms Lime.Log.char_val_ne
#print axioms Lime.Log.char_lt_toNat
#print axioms Lime.Log.charsLe_antisymm
#print axioms Lime.Log.charsLe_total
#print axioms Lime.Log.charsLe_trans
#print axioms Lime.Planner.wallLe_trans
#print axioms Lime.Planner.wallLe_total
#print axioms Lime.Planner.sortWalls_eq_sortWallsFast
#print axioms Lime.Planner.mem_sortWalls
#print axioms Lime.Planner.routineLe_trans
#print axioms Lime.Planner.routine_span_total
#print axioms Lime.Planner.routineLe_total
#print axioms Lime.Planner.sortRoutines_eq_sortRoutinesFast

-- ===========================================================================
-- APPENDED 2026-09-18 (stage 6, run **W-17**, track P, step **P4** — §8.2
-- step 4, PRIORITY.
--
-- The pass itself is stage 5's and is CALLED, not copied: `PlanReq.candAnswers`
-- is `Look.prioritiesWithFloors` at step 4's arguments, and
-- `candAnswers_is_the_capacity_ops_own_grants` is the equation that says it is
-- the same expression `Boundary.grantsOf` answers `lookahead.grants` with.
-- What is new here is §7.4's key (`CandKey`, `natsLe`, `sortRanked`) and the
-- wiring: `edfNumbers` stopped being a `sorry` in `Goals.lean` and
-- `DayPlan.priorities` stopped being empty.
--
-- THREE AUDIT LINES WERE DELETED, each naming a theorem this step deleted with
-- its subject, and each replaced:
--   * `Lime.PlannerWit.mkPlanReq?_refuses_a_zero_denominator` — the EDF lookahead
--     stopped being a FIELD of `PlanReq` and became a view of
--     `Look.lookahead r.look` (`Planner.PlanReq.caps`), because a carried one
--     is a second answer to a question `Look.Input` settles.  A view cannot be
--     handed a zero denominator, so the refusal became unreachable;
--     `mkPlanReq?_refuses_too_many_candidates` is the R10 refusal that took its
--     place in the builder.
--   * `Lime.PlannerWit.witCaps_ok` and `Lime.PlannerWit.witCaps_eq` — the witness
--     lookahead the field needed, gone with the field.  (Both were `decide` at
--     `maxRecDepth 40000`; the step is cheaper for their going.)
-- `Planner.PlanReq.caps_days` and `caps_den` are what replaced what they said.
-- ===========================================================================
#print axioms Lime.rawPrio_is_on_the_scale
#print axioms Lime.applyHysteresis_is_on_the_scale
#print axioms Lime.finalPrio_is_on_the_scale
#print axioms Lime.Look.candOut_p_is_on_the_scale
#print axioms Lime.Look.priorities_p_is_on_the_scale
#print axioms Lime.Look.withFloor_p_is_on_the_scale
#print axioms Lime.Look.prioritiesWithFloors_p_is_on_the_scale
#print axioms Lime.Planner.Capped.ofList?_nil
#print axioms Lime.Planner.PlanReq.edfDays_is_the_lookaheads
#print axioms Lime.Planner.lookaheadOf?_is_what_it_was_given
#print axioms Lime.Planner.PlanReq.caps_days
#print axioms Lime.Planner.PlanReq.caps_den
#print axioms Lime.Planner.PlanReq.candAnswers_is_the_lookaheads
#print axioms Lime.Planner.PlanReq.candAnswers_is_the_capacity_ops_own_grants
#print axioms Lime.Planner.PlanReq.candAnswers_length
#print axioms Lime.Planner.PlanReq.candAnswers_capped
#print axioms Lime.Planner.edfNumbers_is_the_grants_own_impossibility
#print axioms Lime.Planner.edfNumbers_without_a_grant
#print axioms Lime.Planner.edfNumbers_is_the_grant
#print axioms Lime.Planner.natsLe_trans
#print axioms Lime.Planner.natsLe_cons
#print axioms Lime.Planner.natsLe_total
#print axioms Lime.Planner.natsLe_cons_le
#print axioms Lime.Planner.candKeyLe_trans
#print axioms Lime.Planner.candKeyLe_total
#print axioms Lime.Planner.candKeyLe_notWall
#print axioms Lime.Planner.candKeyLe_p
#print axioms Lime.Planner.rankedLe_trans
#print axioms Lime.Planner.rankedLe_total
#print axioms Lime.Planner.sortRanked_eq_sortRankedFast
#print axioms Lime.Planner.mem_sortRanked
#print axioms Lime.Planner.sortRanked_length
#print axioms Lime.Planner.sortRanked_sorted
#print axioms Lime.Planner.PlanReq.rankedCands_length
#print axioms Lime.Planner.PlanReq.mem_rankedCands
#print axioms Lime.Planner.PlanReq.a_ranked_entry_is_an_answer
#print axioms Lime.Planner.PlanReq.a_ranked_entry_carries_its_answers_facts
#print axioms Lime.Planner.PlanReq.rankedCands_sorted
#print axioms Lime.Planner.PlanReq.a_wall_ranks_before_a_task
#print axioms Lime.Planner.PlanReq.a_lower_p_ranks_first
#print axioms Lime.Planner.dayPriorities_val
#print axioms Lime.Planner.a_wall_has_no_priority_row
#print axioms Lime.Planner.an_answer_with_a_p_gets_a_row
#print axioms Lime.Planner.a_row_is_lost_only_off_the_scale
#print axioms Lime.Planner.a_priority_row_carries_the_answers_p
#print axioms Lime.Planner.dayPlan_priorities
#print axioms Lime.PlannerWit.mkPlanReq?_refuses_too_many_candidates
#print axioms Lime.PlannerWit.witBuildsCands
#print axioms Lime.PlannerWit.the_ranking_requests_answers_are_stage_fives
#print axioms Lime.PlannerWit.the_ranking_request_is_ordered
#print axioms Lime.PlannerWit.the_ranking_requests_day_carries_its_priorities
#print axioms Lime.PlannerWit.the_ranking_request_reads_the_plans_line_order
#print axioms Lime.PlannerWit.clearing_overdue_moves_the_candidate
#print axioms Lime.PlannerWit.clearing_mandatory_moves_the_candidate
#print axioms Lime.PlannerWit.clearing_wall_moves_it_off_the_front
#print axioms Lime.PlannerWit.taking_the_written_k_away_moves_the_candidate
#print axioms Lime.PlannerWit.yesterdays_priority_holds_the_candidate_back
#print axioms Lime.PlannerWit.the_request_order_breaks_a_tie

-- ===========================================================================
-- APPENDED 2026-09-18: stage 6, run **W-17**, track **G** -- the lift loses a
-- hypothesis, and §8.3's wall law leaves `Goals.lean`.
--
-- Three groups.
--
-- 1. **`PlanCheck.plan_places_no_block_over_a_wall` -- a goal DISCHARGED**
--    (AGENTS 3.2's burn-down protocol: proved in a shipped module, audited
--    here, then deleted from `Goals.lean`; burn-down 11 -> 10).  It is a
--    §3.1-item-3 discharge, not a plain one: the goal as `Goals.lean` wrote it
--    is FALSE, and
--    `PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted`
--    is the compiled refutation, over the day a request whose calendar acquired
--    a meeting on an already-worked hour produces.  The restatement is over the
--    Block rows that start at or after `now` -- the fork's own
--    `assigned_set(day, w.now)` and step P3's own restriction for E1.
--
--    **The banner at `plan_never_moves_a_wall`'s block above is corrected in
--    place**: it says `plan_places_no_block_over_a_wall` "is NOT discharged
--    here", which was and remains true of step P1's body, and is no longer the
--    whole story.
--
-- 2. **`PlanCheck.dayPlan_ok_core_from_now_given_the_budget` -- §6.1's lift without `hnopast`.**
--    `dayPlan_ok_core_given_the_budget` carries "the log holds no Block for today", which is
--    false of every real day after breakfast and is not a fact about the
--    planner.  `withoutPast` names the restriction §8.3 is about instead of
--    assuming it away, and the same conjunction over the same seven checkers
--    goes through with five hypotheses, all R10 or decoder obligations.  Both
--    lifts are kept: they are incomparable, so nothing is weakened (D5).
--
-- 3. **README gap 396's other eight.**  `PlannerWit.the_battery_census_over_a
--    _produced_day` computes what each of the eleven ranges over on a day the
--    planner really produced -- six have a subject, five do not and each names
--    the step that ends that -- and `the_battery_bites_over_a_produced_day`
--    plus `the_whole_battery_refuses_each_mutation` take the battery from
--    three of eleven refusing something to **eleven of eleven**.
-- ===========================================================================
#print axioms Lime.PlanCheck.withoutPast_segments
#print axioms Lime.PlanCheck.mem_withoutPast
#print axioms Lime.PlanCheck.a_block_row_from_now_is_reserved_or_assigned
#print axioms Lime.PlanCheck.plan_places_no_block_over_a_wall
#print axioms Lime.PlanCheck.dayPlan_ok_core_from_now_given_the_budget
#print axioms Lime.PlannerWit.the_morning_wall_day_lays_a_block_across_a_wall
#print axioms Lime.PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_stored_witness_loads
#print axioms Lime.PlannerWit.the_stored_witness_holds_two_ranked_siblings
#print axioms Lime.PlannerWit.the_stored_day_passes_the_whole_battery
#print axioms Lime.PlannerWit.the_battery_census_over_a_produced_day
#print axioms Lime.PlannerWit.the_battery_bites_over_a_produced_day
#print axioms Lime.PlannerWit.the_whole_battery_refuses_each_mutation

-- ===========================================================================
-- APPENDED 2026-09-18: stage 6, run **W-17**, track **G**, second commit --
-- the new lift's five hypotheses, discharged at a request.
--
-- AGENTS 7.4 item 2: *"Is every hypothesis satisfiable?  Exhibit a witness if
-- it is not obvious.  A precondition nothing satisfies makes the conclusion
-- vacuous, and it stayed invisible for a whole stage once."*
-- `dayPlan_ok_core_from_now_given_the_budget` keeps five hypotheses after dropping `hnopast`, so
-- all five are supplied here at `theRunningRequest` and the lift is APPLIED.
-- `the_running_request_is_plain` is the one that needed an argument rather than
-- a `decide` -- it quantifies over every `Id`, and `PlanCheck.mem_dom_of_get`
-- is what bounds it to the one id this store holds.
-- `the_restricted_day_keeps_the_reservation_and_the_wall` computes what
-- `withoutPast` removes: the two replayed Blocks, and nothing else.
-- ===========================================================================
#print axioms Lime.PlannerWit.the_only_dated_item
#print axioms Lime.PlannerWit.the_running_request_is_plain
#print axioms Lime.PlannerWit.the_running_request_is_inside_the_calendar
#print axioms Lime.PlannerWit.theRunningRequest_wallsAgree
#print axioms Lime.PlannerWit.the_restricted_day_keeps_the_reservation_and_the_wall
#print axioms Lime.PlannerWit.the_lift_applies_at_the_running_request

-- ===========================================================================
-- APPENDED 2026-09-18: stage 6, run **W-17**, the REPAIR step --
-- the root walk the key really does, and the census at the reserved day.
--
-- README gap 677: inverting `Planner.CandKey.nums`' `siteNums k.root ++
-- siteNums k.own` to `siteNums k.own ++ siteNums k.root` left check.sh 7/7 and
-- `cargo test --workspace` 1,337/0/9 green (both re-measured under the
-- inversion), because every candidate of every witness in the tree had a root
-- site EQUAL to its own site.  `theRootedRequest` is the first plan in which
-- the two disagree -- two week tasks whose month parents are crossed -- and
-- `the_root_order_decides_before_the_items_own` is the `decide` the inversion
-- fails.  `exchanging_the_parents_exchanges_the_order` is its perturbation
-- half: a wrong VALUE fails, not only a missing name (gap 577's rule).
--
-- README gap 678: `PlanCheck.lean`'s two lift paragraphs quoted populations
-- nothing computed -- one of them citing
-- `the_battery_census_at_the_reserved_day` for a whole run before the theorem
-- existed.  It exists now, and it counts what `checksCore`'s seven range over
-- at `theRunningRequest`: FOUR of seven over the whole day, THREE of seven
-- over the `PlanCheck.withoutPast` day the new lift is about.
-- ===========================================================================
#print axioms Lime.PlannerWit.the_rooted_witness_loads
#print axioms Lime.PlannerWit.the_rooted_witness_separates_the_root_from_the_item
#print axioms Lime.PlannerWit.the_rooted_requests_answers_tie_on_p
#print axioms Lime.PlannerWit.the_root_order_decides_before_the_items_own
#print axioms Lime.PlannerWit.the_swapped_rooted_witness_loads
#print axioms Lime.PlannerWit.exchanging_the_parents_exchanges_the_order
#print axioms Lime.PlannerWit.the_battery_census_at_the_reserved_day

-- ===========================================================================
-- APPENDED 2026-09-18, stage 6 run W-18, track P, step P5a: the wire carries
-- what the fold reads (AGENTS 6.3).
--
-- README gap 606, measured at W-17: the assignment fold reads NINE candidate
-- facts the wire did not carry -- `planned_min`, `multiplier`, `loc`,
-- `splittable`, `cap` and `cap_done_min` off each `priority::Candidate`, and
-- `state`, `blocked_by` and `wall_today` from `sorted_candidates`' own filter.
-- P5a puts them on it, HOST-COLLECTED exactly as the present twelve are: every
-- one is derivable inside the kernel from `PlanCore` and the D24 run, and
-- deriving one here would be doing D27 early, which D34 forbids.
--
-- `waiting` is not a tenth fact.  Fork `priority.rs:718` sets it to `state ==
-- State::Waiting`, so `Look.PlanFacts.waiting` derives it from `state` and
-- `the_waiting_flag_is_the_state_and_not_a_tenth_fact` says so; README gap 602
-- lists it beside `state` as though it were independent, and gap 700 records
-- the correction.
--
-- The widening is safe because SEVEN'S PASS DOES NOT READ THE NINE, and that
-- is a theorem and not a claim: `prioritiesWithFloors_ignores_the_plan_facts`
-- runs the whole of section 7, floor pass included, over the candidates with
-- their nine facts erased and gets the same answers.  That is AGENTS 5.3's
-- "widen it and prove the old view is a projection", discharged.
--
-- R10: `Look.PlanFacts.wf` is the predicate, `mkPlanFacts?` the constructor,
-- and `Cand.plan`'s TYPE is the `Subtype` -- so `Cand.plan_is_bounded` holds
-- of every candidate there is, on the wire or off it, with no convention to
-- forget.  Three of the nine are bounded by their type and say so:
-- `splittable`/`wallToday` are `Bool`, `state` is `Status` through
-- `Glyph.ofChar?`, and `multiplier` is `Arith.Pos` whose property is
-- `0 < den`, with its SIZE bound at the wire beside the safety's
-- (`multiplierOfWire`), where every configured decimal's size bound lives.
--
-- The witnesses are gap 677's lesson taken literally: `loudFacts` and
-- `loudFactsInverted` differ in ALL NINE
-- (`the_two_loud_records_differ_in_every_one_of_the_nine`), so a decoder that
-- returned a constant, read two fields off one key, or swapped `splittable`
-- for `wallToday` fails `readCand_reads_the_nine` or its perturbation half.
-- ===========================================================================
#print axioms Lime.Look.MaxCap.reached_iff_nothing_left
#print axioms Lime.Look.the_waiting_flag_is_the_state_and_not_a_tenth_fact
#print axioms Lime.Look.the_open_states_are_the_two_live_ones
#print axioms Lime.Look.PlanFacts.capOk_iff
#print axioms Lime.Look.PlanFacts.capOk_of_a_cap
#print axioms Lime.Look.PlanFacts.eligible_iff
#print axioms Lime.Look.mkPlanFacts?_accepts
#print axioms Lime.Look.mkPlanFacts?_ok
#print axioms Lime.Look.mkPlanFacts?_of_not_wf
#print axioms Lime.Look.mkPlanFacts?_refuses_planned_minutes_past_the_wires_u32
#print axioms Lime.Look.mkPlanFacts?_refuses_a_cap_past_the_wires_u32
#print axioms Lime.Look.mkPlanFacts?_refuses_a_spend_past_the_wires_u32
#print axioms Lime.Look.mkPlanFacts?_refuses_a_second_name_for_a_known_location
#print axioms Lime.Look.mkPlanFacts?_refuses_too_many_dependencies
#print axioms Lime.Look.mkPlanFacts?_refuses_a_dependency_that_is_not_a_name
#print axioms Lime.Look.mkPlanFacts?_refuses_a_dependency_token_past_the_id_bound
#print axioms Lime.Look.the_unconstrained_facts_are_wf
#print axioms Lime.Look.the_unconstrained_candidate_is_eligible
#print axioms Lime.Look.Cand.plan_withPlan
#print axioms Lime.Look.Cand.plan_is_bounded
#print axioms Lime.Look.Cand.withPlan_touches_only_the_plan
#print axioms Lime.Look.Cand.erasePlan_wall
#print axioms Lime.Look.Cand.erasePlan_ci
#print axioms Lime.Look.Cand.erasePlan_rule
#print axioms Lime.Look.Cand.erasePlan_yesterday
#print axioms Lime.Look.zipIdx_map_fst
#print axioms Lime.Look.entering_erasePlan
#print axioms Lime.Look.servedOrder_erasePlan
#print axioms Lime.Look.servedGrants_erasePlan
#print axioms Lime.Look.passLeft_erasePlan
#print axioms Lime.Look.priorities_erasePlan
#print axioms Lime.Look.withFloor_erasePlan
#print axioms Lime.Look.prioritiesWithFloors_ignores_the_plan_facts
#print axioms Lime.CapWire.multiplierOfWire_refuses_a_zero_denominator
#print axioms Lime.CapWire.multiplierOfWire_refuses_a_wide_denominator
#print axioms Lime.CapWire.multiplierOfWire_refuses_a_multiplier_past_a_thousand
#print axioms Lime.CapWire.parseLoc_never_makes_a_second_name
#print axioms Lime.CapWire.statusOfWire_refuses_a_character_that_is_not_a_box
#print axioms Lime.CapWire.statusOfWire_refuses_a_word
#print axioms Lime.CapWire.statusOfWire_reads_the_six
#print axioms Lime.CapWire.readPlanFacts_is_bounded
#print axioms Lime.CapWire.the_two_loud_records_differ_in_every_one_of_the_nine
#print axioms Lime.CapWire.readCand_reads_the_nine
#print axioms Lime.CapWire.readCand_reads_the_nine_the_other_way
#print axioms Lime.CapWire.readCand_refuses_each_of_the_nine_by_name
#print axioms Lime.CapWire.readCand_refuses_too_many_dependencies

-- ===========================================================================
-- APPENDED 2026-09-18, stage 6 run W-18, track P, step P5b-i: the assignment
-- order's own filter (AGENTS 6.3).
--
-- README gap 602 said fork `priority::sorted_candidates` drops `!c.eligible()`
-- and an Interval that is not today's, and that NONE of those facts was on the
-- wire. P5a put them there, so the filter lands: `Planner.entersTheOrder` is
-- the fork's two clauses and `PlanReq.rankedCands` applies it BEFORE the sort,
-- as the fork does. Filtering a sorted list changes no pair's order, so every
-- sortedness law above is untouched -- `the_filter_keeps_the_survivors_in_order`
-- computes that at two of the perturbations rather than asserting it.
--
-- `rankedCands_length` is now a BOUND and not an equality, which is the visible
-- consequence of the step and is why it is restated rather than kept.
--
-- The witnesses are one cause at a time: `[?]`, a closed state, an unsatisfied
-- `after:` and an exhausted `max:` each drop `^r1` with nothing else about it
-- changed, and `a_cap_with_minutes_left_keeps_the_candidate` is the line that
-- stops `capReachedFacts` being satisfied by a filter that dropped every capped
-- item. `wall_today` gets both halves too: clearing it on the calendar's `^g1`
-- removes it, and setting it on `^r1`, which is not a wall, changes nothing --
-- so the pair is about the fork's conjunction and not about the flag alone.
--
-- What is NOT here: Planner.eligibleAt, the SLOT half of section 8.2 step 5's
-- filter (ci against the slot's energy, `loc_ok`, the wind-down rule, the
-- atomic run). That is the fold's and README gap 365 still stands.
-- ===========================================================================
#print axioms Lime.Planner.PlanReq.a_ranked_entry_enters_the_order
#print axioms Lime.Planner.PlanReq.an_ineligible_candidate_is_not_ranked
#print axioms Lime.Planner.PlanReq.another_days_wall_is_not_ranked
#print axioms Lime.PlannerWit.each_cause_of_ineligibility_drops_the_candidate
#print axioms Lime.PlannerWit.a_cap_with_minutes_left_keeps_the_candidate
#print axioms Lime.PlannerWit.a_wall_that_is_not_todays_is_dropped
#print axioms Lime.PlannerWit.wall_today_is_read_only_of_a_wall
#print axioms Lime.PlannerWit.the_filter_keeps_the_survivors_in_order

-- ===========================================================================
-- APPENDED 2026-09-18: stage 6, run **W-18**, **track G** --
-- the vacuity proved rather than counted, the break law refuted and restated,
-- and one request with one ratio.
--
-- README gap 650 left four checkers "ranging over nothing on any day the
-- planner can produce today", measured at two requests.  A population computed
-- at a request is evidence about that request, not the claim.  The first four
-- theorems below are the claim, about EVERY `PlanReq`: no Block row of the day
-- carries a slot energy, no Block row reaches the wind-down, no row is a Batch
-- row, and `Diagnostics.impossible` is empty.  The next four are the same four
-- in the battery's own terms -- each checker returns `true` BECAUSE its subject
-- is empty -- and each is a build-time wall P5 and P8 must delete.  (P8's came
-- down at W-33: the impossible pair was refuted when the field was written --
-- W-33 repair, gap 2565.)
--
-- Two of gap 650's four were not of that kind, and this step says which:
-- `wallsUnmoved` wanted a store that holds the wall the day places, and
-- `noBlockOverABreak` wanted a LOG WITH A BREAK IN IT.  Both are request
-- questions.  `theCensusRequest` supplies both and
-- `the_battery_census_at_the_census_request` computes the ratio: SEVEN of the
-- eleven have a subject there, four do not, and the four are the proved ones.
--
-- `Goals.plan_places_no_block_over_a_break` is FALSE as stage 6 wrote it --
-- a `break` logged while a block is running puts a Break row INSIDE a Block
-- row, neither of them the planner's doing (README gap 385, for the third
-- time).  It leaves `Goals.lean` here as
-- `PlanCheck.plan_places_no_block_over_a_break`, over the Block rows that start
-- at or after `now`, with `..._as_stage_6_wrote_it_is_refuted` beside it and
-- `the_break_law_applies_at_the_census_request` showing it is not vacuous.
-- Burn-down 10 -> 9.
--
-- `dayPlan_ok_from_now_except_the_two_comparisons_on_an_unassigned_day_given_no_eligible_impossible_item` is how far design §6.1's
-- lift has come: NINE of the eleven at every eligibility, two of those nine
-- true only because they are empty, and the missing two are `monotoneInRank`
-- and `hotBeforeQueue`, which wait on Planner.eligibleAt (gap 365).
-- ===========================================================================
#print axioms Lime.PlanCheck.the_day_has_no_batch_row_on_an_unassigned_day
#print axioms Lime.PlanCheck.no_block_row_of_the_day_carries_a_slot_energy_on_an_unassigned_day
#print axioms Lime.PlanCheck.no_block_row_of_the_day_reaches_the_wind_down_on_an_unassigned_day
-- DELETED AT W-33 (track P): the_day_names_no_impossible_item, `:= rfl`, described the
-- hole P8's first half closed; REFUTED as PlannerWit.the_day_names_no_impossible_item_is_refuted
-- and replaced by Planner.dayPlan_impossible / Planner.PlanReq.mem_dayImpossible (audited below).
#print axioms Lime.PlanCheck.batchDoesNotReachPast_of_no_batch_row
#print axioms Lime.PlanCheck.impossibleKept_of_no_impossible
#print axioms Lime.PlanCheck.energyFilterOk_is_true_because_its_subject_is_empty_on_an_unassigned_day
#print axioms Lime.PlanCheck.noDemandingAfterWindDown_is_true_because_its_subject_is_empty_on_an_unassigned_day
#print axioms Lime.PlanCheck.batchDoesNotReachPast_is_true_because_its_subject_is_empty_on_an_unassigned_day
-- DELETED AT W-33 (track P): impossibleKept_is_true_because_its_subject_is_empty -- REFUTED as
-- PlannerWit.impossibleKept_is_true_because_its_subject_is_empty_is_refuted; the law it stood in
-- front of is PlanCheck.impossibleKept_of_nothing_assigned_iff (audited below).
#print axioms Lime.PlanCheck.plan_places_no_block_over_a_break
-- RENAMED WITH ITS THEOREM AT W-33 (not deleted): the lift takes `hnoimp`, and its name says so.
#print axioms Lime.PlannerWit.censusRun_resumes_ok
#print axioms Lime.PlannerWit.censusRun_resumes
#print axioms Lime.PlannerWit.the_census_witness_loads
#print axioms Lime.PlannerWit.censusPlan_loads
#print axioms Lime.PlannerWit.the_census_witness_indexes_the_calendars_one_wall
#print axioms Lime.PlannerWit.the_census_witness_holds_the_wall_and_two_ranked_siblings
#print axioms Lime.PlannerWit.witBuildsCensus
#print axioms Lime.PlannerWit.theCensusRequest_wallsAgree
#print axioms Lime.PlannerWit.the_census_request_agrees
#print axioms Lime.PlannerWit.the_census_request_is_inside_the_calendar
#print axioms Lime.PlannerWit.the_census_day_carries_the_mornings_break
#print axioms Lime.PlannerWit.the_battery_passes_at_the_census_request
#print axioms Lime.PlannerWit.the_battery_census_at_the_census_request
#print axioms Lime.PlannerWit.the_census_request_is_plain
#print axioms Lime.PlannerWit.the_lift_applies_at_the_census_request
#print axioms Lime.PlannerWit.midBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_break_law_applies_at_the_census_request

-- ===========================================================================
-- APPENDED 2026-09-18 (stage 6, run **W-18**, the REPAIR step).
--
-- Ten new theorems, from two repairs.
--
-- (1) AGENTS 5.3, W-18's reuse critic: `boundedPos`, `safetyOfWire` and (from
--     P5a) `multiplierOfWire` were three copies of one bounded-rational wire
--     reader in one namespace, with three parallel refusal batteries.  The
--     concept is now ONE definition, `CapWire.boundedPair`, and each of the
--     three old views is PROVED to be a projection of it -- the widen-and-
--     project pattern, so no statement changed and no law narrowed (D5).  All
--     SEVEN old theorems -- boundedPos's four and multiplierOfWire's three --
--     keep their exact statements and are re-proved from the generic ones.
--     `multiplierOfWire_ok` is new and is where the
--     multiplier's SIZE bound is stated, because `Look.PlanFacts.wf` does not
--     carry it (README gap 777).
--
-- (2) AGENTS 9.2, "a check no input can fail": `Look.PlanFacts.eligible`'s
--     first conjunct `!waiting` is implied by its second, `isOpen` -- Holder's
--     three constructors are disjoint -- so NO `PlanFacts` can distinguish it
--     and no witness could pin it (W-17 lesson 2's shape, from the other
--     side).  The conjunct is kept because the fork writes it; the theorem is
--     the record that it decides nothing.  README gap 775.  The INVERSION --
--     delete the conjunct and run everything -- broke exactly ONE thing in the
--     tree, `eligible_iff`'s own proof, whose residual goal is literally the
--     defect: an iff restating `waiting = false` beside three real conditions.
--     So `eligible_iff_without_the_free_component` is added, stating the three
--     obligations a caller has.  `eligible_iff` itself is untouched (D5).
-- ===========================================================================
#print axioms Lime.CapWire.boundedPair_zero_den
#print axioms Lime.CapWire.boundedPair_wide_den
#print axioms Lime.CapWire.boundedPair_large_num
#print axioms Lime.CapWire.boundedPair_ok
#print axioms Lime.CapWire.boundedPos_is_the_pair_at_the_energy_bounds
#print axioms Lime.CapWire.safetyOfWire_is_the_pair_reader_past_one_more_refusal
#print axioms Lime.CapWire.multiplierOfWire_is_the_pair_at_the_multiplier_bounds
#print axioms Lime.CapWire.multiplierOfWire_ok
#print axioms Lime.Look.PlanFacts.the_waiting_conjunct_is_implied_by_the_open_states
#print axioms Lime.Look.PlanFacts.eligible_iff_without_the_free_component
#print axioms Lime.Look.scaled_le
#print axioms Lime.Look.convex_between
#print axioms Lime.Look.dayLeft_scale

-- ===========================================================================
-- APPENDED 2026-09-18 (stage 6, run **W-19**, track P, step **P5b** -- the
-- assign fold's first half: the GROUPS the cursor walks).
--
-- Fork `Planner::build_groups` (planner.rs:1406) over fork `priority::batches`
-- (priority.rs:1214) and fork `split_by_filters` (planner.rs:2354).  This is
-- NOT an EDF pass (README gap 701): fork `build_groups`/`pick` is a greedy
-- cursor in 7.4's key order with no deadline anywhere, and 7.3's pass reaches
-- step 5 only as the `p` inside `CandKey`.
--
-- 59 theorems in `Planner.lean` and 8 `decide` witnesses in `PlannerWit.lean`.
-- The four laws a later step reads are `PlanReq.a_group_member_is_ranked`
-- (nothing invented), `PlanReq.a_ranked_candidate_has_a_group` (nothing
-- dropped), `gatherBatch_fst_is_a_prefix_of_its_ci` (E2: the gather cannot
-- reach past an equal-`ci` candidate it left behind) and
-- `groupOf_commit_le_cap` (6.2's `max:` binds the commitment).
--
-- No goal is discharged and none is added: the burn-down does not move.  The
-- CURSOR -- `contiguous_fits`, `pick`, the slot walk and the Block/Batch rows
-- -- is NOT written; `dayPlan` is unchanged and no group reaches a segment.
-- README gaps 800-806 say so by name.
-- ===========================================================================
#print axioms Lime.Planner.batches_ci
#print axioms Lime.Planner.batches_cover
#print axioms Lime.Planner.batches_flatten_perm
#print axioms Lime.Planner.batches_length
#print axioms Lime.Planner.batches_ne_nil
#print axioms Lime.Planner.batchLoop_ci
#print axioms Lime.Planner.batchLoop_flatten_perm
#print axioms Lime.Planner.batchLoop_length
#print axioms Lime.Planner.batchLoop_ne_nil
#print axioms Lime.Planner.capFold_le_member
#print axioms Lime.Planner.capFold_some
#print axioms Lime.Planner.capLeftOf_le_member
#print axioms Lime.Planner.commitOf_le_cap
#print axioms Lime.Planner.commitOf_le_planned
#print axioms Lime.Planner.gatherBatch_fst_ci
#print axioms Lime.Planner.gatherBatch_fst_is_a_prefix_of_its_ci
#print axioms Lime.Planner.gatherBatch_fst_length
#print axioms Lime.Planner.gatherBatch_perm
#print axioms Lime.Planner.gatherBatch_snd_length
#print axioms Lime.Planner.groupKeyLe_total
#print axioms Lime.Planner.groupKeyLe_trans
#print axioms Lime.Planner.groupLe_total
#print axioms Lime.Planner.groupLe_trans
#print axioms Lime.Planner.Group.live_iff
#print axioms Lime.Planner.groupOf_commit_le_cap
#print axioms Lime.Planner.groupOf_commit_le_planned
#print axioms Lime.Planner.groupOf_members
#print axioms Lime.Planner.mem_batchMembers
#print axioms Lime.Planner.mem_batchMembers_of
#print axioms Lime.Planner.mem_of_mem_batches
#print axioms Lime.Planner.mem_of_mem_splitGroups
#print axioms Lime.Planner.mem_sortGroups
#print axioms Lime.Planner.minGroupKey_le_mem
#print axioms Lime.Planner.minGroupKey_le_seed
#print axioms Lime.Planner.PlanReq.a_group_is_a_bounded_batch
#print axioms Lime.Planner.PlanReq.a_group_key_is_its_minimum
#print axioms Lime.Planner.PlanReq.a_group_member_carries_the_groups_ci
#print axioms Lime.Planner.PlanReq.a_group_member_carries_the_groups_filters
#print axioms Lime.Planner.PlanReq.a_group_member_is_ranked
#print axioms Lime.Planner.PlanReq.a_ranked_candidate_has_a_group
#print axioms Lime.Planner.PlanReq.a_started_group_is_a_built_group
#print axioms Lime.Planner.PlanReq.buildGroups_sorted
#print axioms Lime.Planner.PlanReq.mem_buildGroups
#print axioms Lime.Planner.PlanReq.mem_rawGroups
#print axioms Lime.Planner.sortGroups_eq_sortGroupsFast
#print axioms Lime.Planner.sortGroups_sorted
#print axioms Lime.Planner.spendActive_keys
#print axioms Lime.Planner.spendActive_length
#print axioms Lime.Planner.splitFold_flatten
#print axioms Lime.Planner.splitFold_SplitNe
#print axioms Lime.Planner.splitFold_SplitOk
#print axioms Lime.Planner.splitGroups_cover
#print axioms Lime.Planner.splitGroups_flatten
#print axioms Lime.Planner.splitGroups_keys
#print axioms Lime.Planner.splitGroups_length
#print axioms Lime.Planner.splitGroups_ne_nil
#print axioms Lime.Planner.splitPush_flatten
#print axioms Lime.Planner.splitPush_keeps_SplitNe
#print axioms Lime.Planner.splitPush_keeps_SplitOk
#print axioms Lime.PlannerWit.the_batch_request_is_ordered
#print axioms Lime.PlannerWit.the_commitment_is_capped_by_a_members_max
#print axioms Lime.PlannerWit.the_gather_passes_over_another_ci_and_stops_at_its_own
#print axioms Lime.PlannerWit.the_gather_stops_at_the_batch_bound
#print axioms Lime.PlannerWit.the_running_block_starts_its_group_with_its_minutes_spent
#print axioms Lime.PlannerWit.the_split_cuts_a_batch_on_atomic
#print axioms Lime.PlannerWit.the_split_cuts_a_batch_on_its_location
#print axioms Lime.PlannerWit.the_split_cuts_out_the_running_block

-- ===========================================================================
-- APPENDED 2026-09-18 (stage 6, run **W-19**, track P, step **P5b** -- the
-- assign fold's second half: the CURSOR).
--
-- Fork `plan()`'s assign loop (planner.rs:1017-1026) over fork `Planner::pick`
-- (planner.rs:1582) and fork `contiguous_fits` (planner.rs:2303).  This is
-- eligibleAt's SLOT half (README gap 365); the item half is
-- `entersTheOrder`'s and ran before the sort at P5b-i.
--
-- 15 theorems in `Planner.lean` and 11 `decide` witnesses in `PlannerWit.lean`.
-- `PlanReq.assignFold_ok` is the one a later step reads: every slot the cursor
-- filled went to a group whose `ci` the slot's energy covers, whose `loc:` fits
-- where the day is lived, and which is not demanding work after the wind-down.
-- Those three are about fields the walk never moves, which is why they survive
-- it; the other two clauses of `pick` (`g.live` and the atomic run) are about
-- values the walk does move and are pinned by witnesses instead.
--
-- NOTHING HERE REACHES `dayPlan`.  No row is emitted, `dayRows` is unchanged,
-- `PlanCheck`'s four emptiness theorems still hold, no goal is discharged and
-- none is added.  README gaps 803-806 say what is owed.
-- ===========================================================================
#print axioms Lime.Planner.lt_of_getElem?_some
#print axioms Lime.Planner.PlanReq.an_assigned_slot_names_a_group
#print axioms Lime.Planner.PlanReq.a_spent_budget_assigns_nothing
#print axioms Lime.Planner.PlanReq.assignFold_ok
#print axioms Lime.Planner.PlanReq.assignFold_used
#print axioms Lime.Planner.PlanReq.assignStart_ok
#print axioms Lime.Planner.PlanReq.assignStep_cases
#print axioms Lime.Planner.PlanReq.assignStep_keeps_the_group
#print axioms Lime.Planner.PlanReq.assignStep_lengths
#print axioms Lime.Planner.PlanReq.assignStep_ok
#print axioms Lime.Planner.PlanReq.assignStep_used
#print axioms Lime.Planner.PlanReq.energisedSlots_length
#print axioms Lime.Planner.PlanReq.foldl_assignStep_ok
#print axioms Lime.Planner.PlanReq.foldl_assignStep_used
#print axioms Lime.PlannerWit.an_assigned_slot_breaks_an_atomic_run
#print axioms Lime.PlannerWit.an_atomic_group_needs_its_whole_run
#print axioms Lime.PlannerWit.an_atomic_group_that_fits_is_placed
#print axioms Lime.PlannerWit.a_planned_break_does_not_break_an_atomic_run
#print axioms Lime.PlannerWit.the_budget_stops_the_cursor
#print axioms Lime.PlannerWit.the_cursor_fills_the_day_in_key_order
#print axioms Lime.PlannerWit.the_cursor_refuses_a_slot_in_the_wrong_place
#print axioms Lime.PlannerWit.the_cursor_refuses_a_slot_that_is_not_good_enough
#print axioms Lime.PlannerWit.the_cursor_request_batches_nothing
#print axioms Lime.PlannerWit.the_cursor_requests_day_is_four_slots
#print axioms Lime.PlannerWit.two_groups_fit_the_first_slot_and_the_order_decides
-- ===========================================================================
-- APPENDED 2026-09-18 (stage 6, run **W-19**, track G).
--
-- Seventeen theorems, and what they settle is a question the two numbers this
-- module already prints could not answer between them.  Section 14 of
-- `PlannerWit.lean` measures SEVEN of the eleven checkers with a subject at
-- `theCensusRequest`; `PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons_on_an_unassigned_day_given_no_eligible_impossible_item`
-- proves NINE of the eleven at every eligibility.  Neither says whether the
-- other two are unproved or FALSE.
--
-- They are false.  `PlannerWit.theQueuedRequest` is the census request with
-- `m1`'s two log lines removed and `m2` running instead -- so the hot sibling
-- that ranks FIRST reaches no row of the day -- and on the day it produces,
-- with no mutation at all, `monotoneInRank` and `hotBeforeQueue` both answer
-- `false` at the permissive eligibility, on the whole day and on
-- `withoutPast`'s day alike, while the other nine keep answering `true`.
--
-- Consequences, each a theorem here:
--   * the `∀ el` form of design 6.1's lift is refuted, BOTH over the whole day
--     and over the restricted day (`PlanCheck.lean` asserted the first in prose
--     from W-14 and never stated the second);
--   * `Goals.plan_is_monotone_in_rank` and `Goals.plan_puts_hot_before_the_queue`
--     are refuted AS WRITTEN -- design 6.3 rows 4 and 5, predicted from the
--     fork's proptest header and until now never computed;
--   * NEITHER goal leaves `Goals.lean`, because the restatements need
--     Planner.eligibleAt, which is P5's (gap 365), and a restatement without
--     its refutation is a weakening -- `Goals.plan_tail_drop`'s situation
--     exactly.  The burn-down is 9, unchanged.  README gap 851.
--
-- `dayPlan_ok_from_now_given_the_two_comparisons_and_no_eligible_impossible_item_on_an_unassigned_day` assembles design 6.1's own
-- `planOk` from the nine plus the two, so that "nine of eleven" is the
-- compiler's arithmetic and not a reader's (README gap 684's class).
-- ===========================================================================
-- RENAMED WITH ITS THEOREM AT W-33 (not deleted): `hnoimp` added.
#print axioms Lime.PlannerWit.queuedRun_resumes_ok
#print axioms Lime.PlannerWit.queuedRun_resumes
#print axioms Lime.PlannerWit.witBuildsQueued
#print axioms Lime.PlannerWit.theQueuedRequest_wallsAgree
#print axioms Lime.PlannerWit.the_queued_request_agrees
#print axioms Lime.PlannerWit.the_queued_request_is_inside_the_calendar
#print axioms Lime.PlannerWit.the_queued_request_is_plain
#print axioms Lime.PlannerWit.the_queued_day_is_the_second_sibling_twice
#print axioms Lime.PlannerWit.the_queued_day_assigns_the_second_sibling_only
#print axioms Lime.PlannerWit.the_other_nine_hold_where_the_two_fail
#print axioms Lime.PlannerWit.the_lift_applies_at_the_queued_request
#print axioms Lime.PlannerWit.dayPlan_ok_at_every_eligibility_is_refuted
#print axioms Lime.PlannerWit.dayPlan_ok_from_now_at_every_eligibility_is_refuted
#print axioms Lime.PlannerWit.plan_is_monotone_in_rank_as_stage_6_wrote_it_is_refuted
#print axioms Lime.PlannerWit.plan_puts_hot_before_the_queue_as_stage_6_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_one_id_store_gives_neither_comparison_a_subject

-- APPENDED 2026-09-19 (stage 6, run **W-19**, the REPAIR step -- the reuse
-- repairs).  `pickedGroup_is_the_first_that_fits` replaces the deleted
-- pickFrom_sound: the cursor calls `List.findIdx?` rather than a third copy of
-- it, and the new statement carries the "first" the old one did not.  README
-- gap 877.
#print axioms Lime.Planner.pickedGroup_is_the_first_that_fits

-- APPENDED 2026-09-19 (stage 6, run **W-19**, the REPAIR step -- the witnesses).
--   `the_gather_predicate_refuses_on_each_clause` and
--   `the_gather_reads_each_of_its_five_clauses` are the subjects
--   `Planner.Ranked.gatherable` never had: `:= true` was green across the whole
--   build before them, and so was the removal of any one of its clauses.
--   README gap 875.
--   `the_two_comparisons_hold_at_the_reserved_day` and
--   `the_two_comparison_lift_applies_at_the_reserved_day` give
--   `PlanCheck.dayPlan_ok_from_now_given_the_two_comparisons_and_no_eligible_impossible_item_on_an_unassigned_day` the computed
--   instance it shipped without.  README gap 879.
#print axioms Lime.PlannerWit.the_gather_predicate_refuses_on_each_clause
#print axioms Lime.PlannerWit.the_gather_reads_each_of_its_five_clauses
#print axioms Lime.PlannerWit.the_two_comparisons_hold_at_the_reserved_day
#print axioms Lime.PlannerWit.the_two_comparison_lift_applies_at_the_reserved_day

-- ===========================================================================
-- APPENDED 2026-09-19 (stage 6, run **W-20**, track P, step **P6** -- §8.2
-- step 6, the routines that missed their window).
--
-- `freeStretch_gives_a_position` and `earliestFree_from_a_stretch` are a
-- REFACTOR, not new content: step 2's `earliestFree_inside` and
-- `earliestFree_is_free` (audited above, statements unchanged) and step 6's
-- `PlanReq.lowestFree_inside` are now one lemma at two choices of stretch.
--
-- `leastBy` is `Replay.lastMax?` with its replacing relation turned round, so
-- `leastBy_spec` is `Replay.lastMax?_spec` at `flip_trans`/`flip_skip`; the two
-- orders it is taken in are `Seal.lexLt Seal.natLt _`, with `Seal.natLt` and
-- `Seal.lexLt_strictTotal` doing the work.  Nothing here is a second fold,
-- a second free-interval walk, a second energy reader or a second picker:
-- `PlanReq.rePlaceWalk` calls `PlanReq.assignStep`, step 5's own body.
--
-- `PlanReq.deferOne_cases` is the section's one case split (the shape
-- `PlanReq.assignStep_cases` set at P5b): nothing else unfolds the loop body.
--
-- `a_deferred_routine_is_inside_its_window` is step 2's own law restated over
-- step 6's output, and `PlanReq.deferOne_places_nothing_in_a_closed_window` is
-- README gap 285's family -- an occurrence whose span has closed is passed
-- over, never squeezed in.
-- ===========================================================================
#print axioms Lime.Planner.freeStretch_gives_a_position
#print axioms Lime.Planner.earliestFree_from_a_stretch
#print axioms Lime.Planner.flip_trans
#print axioms Lime.Planner.flip_skip
#print axioms Lime.Planner.leastBy_spec
#print axioms Lime.Planner.posLt_strictTotal
#print axioms Lime.Planner.victimLt_strictTotal
#print axioms Lime.Planner.PlanReq.lowestFree_from_a_stretch
#print axioms Lime.Planner.PlanReq.lowestFree_inside
#print axioms Lime.Planner.unspend_keeps_the_group
#print axioms Lime.Planner.unspend_length
#print axioms Lime.Planner.PlanReq.victimSlot_spec
#print axioms Lime.Planner.PlanReq.energised_slot_is_a_slot
#print axioms Lime.Planner.PlanReq.deferOne_cases
#print axioms Lime.Planner.PlanReq.deferOne_keeps_a_placed_routine
#print axioms Lime.Planner.PlanReq.deferOne_places_nothing_in_a_closed_window
#print axioms Lime.Planner.placeAt_PlacedOk
#print axioms Lime.Planner.PlanReq.deferOne_keeps_PlacedOk
#print axioms Lime.Planner.PlanReq.a_light_deferred_instance_stays_out_of_the_evening
#print axioms Lime.Planner.PlanReq.rePlaceWalk_lengths
#print axioms Lime.Planner.PlanReq.rePlaceWalk_used
#print axioms Lime.Planner.PlanReq.displaceInto_lengths
#print axioms Lime.Planner.PlanReq.displaceInto_used
#print axioms Lime.Planner.PlanReq.deferOne_lengths
#print axioms Lime.Planner.PlanReq.deferOne_used
#print axioms Lime.Planner.PlanReq.deferWalk_keeps_PlacedOk
#print axioms Lime.Planner.PlanReq.deferWalk_lengths
#print axioms Lime.Planner.PlanReq.deferWalk_used
#print axioms Lime.Planner.a_deferred_routine_is_inside_its_window
#print axioms Lime.Planner.the_deferred_pass_keeps_the_assignments_shape
#print axioms Lime.Planner.the_deferred_pass_stays_inside_the_budget

-- APPENDED 2026-09-19 (stage 6, run **W-20**, track P, step **P6** -- the
-- witnesses).  `theRoutineRequest` is the FIRST request in this repository
-- that carries a window instance, so these are also the first computed subject
-- §8.2 step 2's placement fold has ever had.  The displacement's three
-- (`victimSlot`, `unspend`, `rePlaceWalk`) are computed at their own arguments
-- because no request reaches them -- README gap 903.
#print axioms Lime.PlannerWit.the_routine_witness_loads
#print axioms Lime.PlannerWit.the_routine_witness_holds_three_routines_and_the_wall
#print axioms Lime.PlannerWit.the_routine_instances_are_accepted
#print axioms Lime.PlannerWit.the_mandatory_routine_is_placed_and_the_other_is_deferred
#print axioms Lime.PlannerWit.the_deferred_windows_two_stretches_are_at_different_energies
#print axioms Lime.PlannerWit.the_lowest_energy_rule_and_the_earliest_rule_disagree_here
#print axioms Lime.PlannerWit.a_tie_on_energy_goes_to_the_earlier_position
#print axioms Lime.PlannerWit.the_deferred_routine_takes_the_lowest_energy_position
#print axioms Lime.PlannerWit.the_crowded_instances_are_accepted
#print axioms Lime.PlannerWit.an_instance_with_no_room_is_named_in_the_notes
#print axioms Lime.PlannerWit.the_lapsed_instances_are_accepted
#print axioms Lime.PlannerWit.an_instance_whose_window_has_closed_is_passed_over_and_not_reported
#print axioms Lime.PlannerWit.the_victim_is_the_lowest_energy_slot_and_the_latest_of_those
#print axioms Lime.PlannerWit.the_restore_lowers_one_groups_spent_and_touches_no_other
#print axioms Lime.PlannerWit.the_re_placement_fills_one_slot_where_the_cursor_fills_four
#print axioms Lime.PlannerWit.the_busy_instances_are_accepted
#print axioms Lime.PlannerWit.a_day_the_cursor_filled_leaves_the_routine_nowhere_to_go
#print axioms Lime.PlannerWit.the_kept_break_and_the_filled_slots_are_each_what_leaves_no_room
#print axioms Lime.PlannerWit.the_displacement_frees_one_slot_and_gives_its_minutes_back

-- APPENDED 2026-09-19 (stage 6, run **W-20**, track P, step **P6** -- the
-- wire).  `dayRows` reads the routines as STEP 6 left them, which is where
-- fork `emit_segments` reads its own (`planner.rs:1032`, then 1063), and
-- `dayDiagnostics` carries `Note.noPosition`.  The day-assembly block moved
-- below §8.2 steps 4, 5 and 6 in `Planner.lean` so that it can: nothing else
-- about it changed and its 26 declarations keep their names.
--
-- `routineRows` is `stepTwoSegs` widened to the routine list it renders
-- (AGENTS 5.3's widen-and-project): one renderer, two arguments -- step 2's
-- list and the day's.  The four `stepTwoSegs_*` laws keep their names and
-- statements and are now specialisations, and `a_wind_down_row_is_the_evenings`
-- is generalised the same way (D5: re-proved over the new shape, never
-- weakened).
--
-- `assignedOf_dayPlan_is_step_one_the_reservation_and_step_five` is what makes the move safe:
-- `assignedOf` keeps only `SegKind.isWork` rows, and `sortRows_filter` --
-- `Seal.insSort_filter` at `rowLe` -- lets the filter run before the sort, so
-- neither step 2's rows nor step 6's can enter the assigned set OR reorder it.
-- `the_budget_does_not_move_the_assigned_set_at_the_busy_request` is
-- re-proved through it: the budget now reaches `assignFold` and therefore
-- reaches which routine rows exist, and that theorem's `rfl` proof was true
-- only while it did not.
#print axioms Lime.Planner.rowLe_trans
#print axioms Lime.Planner.rowLe_total
#print axioms Lime.Planner.sortRows_filter
#print axioms Lime.Planner.routineRows_kinds
#print axioms Lime.Planner.routineRows_are_not_walls
#print axioms Lime.Planner.routineRows_are_not_blocks
#print axioms Lime.Planner.routineRows_are_not_work
#print axioms Lime.Planner.assignedOf_dayPlan_is_step_one_the_reservation_and_step_five
#print axioms Lime.PlannerWit.the_day_carries_the_deferred_routines_row
#print axioms Lime.PlannerWit.the_day_with_no_room_carries_the_note_instead
#print axioms Lime.PlannerWit.the_battery_passes_where_step_six_filled_and_fails_where_step_five_did

-- APPENDED 2026-09-19 (stage 6, run **W-20**, track G -- the quiet day, README
-- gap 960, and the two clauses README gap 806 left unpinned).
--
--   `dayPlan_ok_on_a_quiet_unassigned_day_except_hot_given_no_eligible_impossible_item` is **TEN of §6.1's eleven**, over the
--   WHOLE day and at every eligibility, for the class of requests whose log
--   holds no Block and whose runtime holds no reservation.  W-19's ceiling was
--   nine, over `withoutPast`'s day.  `monotoneInRank` is the tenth and
--   `dayPlan_assigns_nothing_on_a_quiet_unassigned_day` is why.
--   `hotBeforeQueue_is_false_on_a_quiet_day` and
--   `a_quiet_day_does_not_pass_the_whole_battery` are the matching ceiling:
--   the eleventh fails on a day with no Block row at all, so neither the fold
--   nor an eligibleAt at the reservation row reaches it (README gap 850).
--
--   `the_cursor_refuses_a_group_that_owes_nothing` and
--   `the_cursor_refuses_an_atomic_group_whose_run_is_broken` are README gap
--   806's two clauses, as ∀-theorems over every accumulator rather than as
--   witnesses.  `the_cursor_skips_no_group_that_fits` is README gap 877's
--   consumer for `pickedGroup_is_the_first_that_fits`' second conjunct.
--   `assignFold_owes` is the same first clause lifted over the whole walk.
#print axioms Lime.PlanCheck.dayPlan_assigns_nothing_on_a_quiet_unassigned_day
#print axioms Lime.PlanCheck.monotoneInRank_of_nothing_assigned
-- BOTH RENAMED WITH THEIR THEOREMS AT W-33 (not deleted): `hnoimp` added to each.
#print axioms Lime.PlanCheck.the_cursor_refuses_a_group_that_owes_nothing
#print axioms Lime.PlanCheck.the_cursor_refuses_an_atomic_group_whose_run_is_broken
#print axioms Lime.PlanCheck.the_cursor_skips_no_group_that_fits
#print axioms Lime.PlanCheck.assignStart_owes
#print axioms Lime.PlanCheck.assignStep_owes
#print axioms Lime.PlanCheck.foldl_assignStep_owes
#print axioms Lime.PlanCheck.assignFold_owes
#print axioms Lime.PlannerWit.witBuildsQuietCensus
#print axioms Lime.PlannerWit.the_quiet_census_request_is_quiet
#print axioms Lime.PlannerWit.the_quiet_census_day_is_a_wall_and_an_evening
#print axioms Lime.PlannerWit.hotBeforeQueue_is_false_on_a_quiet_day
#print axioms Lime.PlannerWit.the_ten_hold_where_the_eleventh_fails
#print axioms Lime.PlannerWit.a_quiet_day_does_not_pass_the_whole_battery
#print axioms Lime.PlannerWit.the_quiet_request_agrees
#print axioms Lime.PlannerWit.theQuietRequest_wallsAgree
#print axioms Lime.PlannerWit.the_quiet_lift_applies_at_the_quiet_request
#print axioms Lime.PlannerWit.the_quiet_battery_passes_at_the_quiet_request
#print axioms Lime.PlannerWit.the_first_group_is_spent_after_one_slot
#print axioms Lime.PlannerWit.the_owes_invariant_has_a_subject
#print axioms Lime.PlanCheck.the_cursor_gives_no_slot_to_a_group_that_owes_nothing
#print axioms Lime.PlannerWit.the_quiet_census_request_agrees
#print axioms Lime.PlannerWit.theQuietCensusRequest_wallsAgree
#print axioms Lime.PlannerWit.the_quiet_lift_applies_at_the_quiet_census_request
#print axioms Lime.PlannerWit.the_tenth_is_vacuous_where_the_eleventh_bites
#print axioms Lime.Planner.PlanReq.emitKeptBreaks_is_a_kept_break
#print axioms Lime.Planner.PlanReq.an_emitted_break_is_clear_of_the_routines
#print axioms Lime.Planner.optionalWant_without_a_cap
#print axioms Lime.Planner.optionalWant_is_within_the_cap
#print axioms Lime.Planner.optionalWant_le_remaining
#print axioms Lime.Planner.PlanReq.an_optional_candidate_is_optional_and_eligible
#print axioms Lime.Planner.placeOptional_spec
#print axioms Lime.Planner.freeIntervals_FreeOk
#print axioms Lime.Planner.placeOptional_FreeOk
#print axioms Lime.Planner.optionalFold_ok
#print axioms Lime.Planner.an_optional_is_placed_in_the_free_day_before_the_wind_down
#print axioms Lime.Planner.PlanReq.optionalRows_kinds
#print axioms Lime.Planner.PlanReq.restRows_kinds
#print axioms Lime.Planner.a_rest_row_is_a_piece_of_an_unfilled_slot
#print axioms Lime.Planner.a_rest_row_comes_from_a_slot_no_group_took
#print axioms Lime.Planner.PlanReq.aCapacityLost_needs_rest
#print axioms Lime.Planner.PlanReq.aCapacityLost_is_the_rest_minutes
#print axioms Lime.Planner.PlanReq.no_budget_note_while_the_budget_lasts
#print axioms Lime.Planner.PlanReq.no_budget_note_without_a_block
#print axioms Lime.PlannerWit.an_optional_asks_for_what_its_cap_leaves
#print axioms Lime.PlannerWit.the_optionals_fill_the_day_in_request_order
#print axioms Lime.PlannerWit.the_rest_rows_are_the_slots_no_group_took
#print axioms Lime.PlannerWit.an_optional_takes_its_minutes_out_of_rest
#print axioms Lime.PlannerWit.a_routine_step_six_placed_is_taken_out_of_rest
#print axioms Lime.PlannerWit.the_break_the_day_keeps_is_not_free_for_an_optional
#print axioms Lime.PlannerWit.the_a_capacity_lost_is_the_high_rest_a_ci_5_item_could_not_have
#print axioms Lime.PlannerWit.a_spent_budget_is_named_and_a_live_one_is_not
#print axioms Lime.Planner.PlanReq.optionalRows_are_not_work
#print axioms Lime.Planner.PlanReq.optionalRows_are_not_blocks
#print axioms Lime.Planner.PlanReq.optionalRows_are_not_walls
#print axioms Lime.Planner.PlanReq.optionalRows_are_not_breaks
#print axioms Lime.Planner.PlanReq.optionalRows_are_not_wind_down
#print axioms Lime.Planner.PlanReq.restRows_are_not_work
#print axioms Lime.Planner.PlanReq.restRows_are_not_blocks
#print axioms Lime.Planner.PlanReq.restRows_are_not_walls
#print axioms Lime.Planner.PlanReq.restRows_are_not_breaks
#print axioms Lime.Planner.PlanReq.restRows_are_not_wind_down
#print axioms Lime.PlannerWit.the_day_with_two_optionals_on_it
#print axioms Lime.PlannerWit.the_battery_is_unmoved_by_the_rest_rows
#print axioms Lime.PlannerWit.the_day_reports_its_lost_capacity_and_its_spent_budget
#print axioms Lime.Planner.assignedOf_dayPlan_is_dayAssigned

-- APPENDED 2026-09-19 (stage 6, run **W-21**, track G -- eleven of eleven on the
-- quiet class, and the subject census as a function).
--
--   `planOk_antitone` is the structural half: all four eligibility-dependent
--   checkers read `el` in their ANTECEDENT, so narrowing `el` can only make the
--   battery easier, and `planOk_at_every_eligibility` collapses the whole
--   "at every eligibility" axis to one computation at `PlannerWit.permissive`.
--   W-19's "nine is a ceiling" was that argument in prose.
--
--   `WorkAnchored` is the other half: an `el` that admits a candidate only at a
--   row §8.2 step 5 could assign into.  `dayPlan_ok_on_a_quiet_unassigned_day` is design
--   §6.1's dayPlan_ok at **ELEVEN of eleven** for every quiet request and
--   every such `el` -- the class W-20 left at ten with the eleventh refuted
--   (README gap 960).  `the_whole_battery_passes_on_the_quiet_census_day` is it
--   fired at the very request where `hotBeforeQueue` is `false` at `permissive`.
--
--   `subjectOf` / `subjectCount` are the SUBJECT census, keyed on each check's
--   own `CheckName` and filtered over `checksOf`'s own list, so the ratio is the
--   compiler's arithmetic and not a reader's over a table.
--   `a_check_with_no_subject_is_a_free_pass` is what makes it a measurement;
--   `planOk_of_no_subject` says what an empty census is worth.
--   `the_census_ceiling_is_seven_on_an_unassigned_day_given_no_eligible_impossible_item` proves SEVEN is a ceiling over every request,
--   and `PlannerWit.the_census_ratio` reaches it at `theCensusRequest`.
--   `PlannerWit.the_quiet_eleven_is_one_checker_biting` is the honest price of
--   the eleven: one checker has a subject there.
#print axioms Lime.PlanCheck.eligibleSomewhere_mono
#print axioms Lime.PlanCheck.monotoneInRank_antitone
#print axioms Lime.PlanCheck.hotBeforeQueue_antitone
#print axioms Lime.PlanCheck.batchDoesNotReachPast_antitone
#print axioms Lime.PlanCheck.planOk_antitone
#print axioms Lime.PlanCheck.planOk_at_every_eligibility
#print axioms Lime.PlanCheck.dayPlan_has_no_work_row_on_an_unassigned_day
#print axioms Lime.PlanCheck.eligibleSomewhere_of_no_work_row
#print axioms Lime.PlanCheck.monotoneInRank_of_nothing_eligible
#print axioms Lime.PlanCheck.hotBeforeQueue_of_nothing_eligible
#print axioms Lime.PlanCheck.dayPlan_ok_on_a_quiet_unassigned_day
#print axioms Lime.PlanCheck.false_of_any_eq_false
#print axioms Lime.PlanCheck.blockSeconds_of_no_block
#print axioms Lime.PlanCheck.noOverbook_of_no_subject
#print axioms Lime.PlanCheck.oneBlockAtATime_of_no_subject
#print axioms Lime.PlanCheck.energyFilterOk_of_no_subject
#print axioms Lime.PlanCheck.noBlockOverAWall_of_no_subject
#print axioms Lime.PlanCheck.noBlockOverABreak_of_no_subject
#print axioms Lime.PlanCheck.noDemandingAfterWindDown_of_no_subject
#print axioms Lime.PlanCheck.wallsUnmoved_of_no_subject
#print axioms Lime.PlanCheck.mem_rankSubjects
#print axioms Lime.PlanCheck.mem_hotSubjects
#print axioms Lime.PlanCheck.monotoneInRank_of_no_subject
#print axioms Lime.PlanCheck.hotBeforeQueue_of_no_subject
#print axioms Lime.PlanCheck.impossibleKept_of_no_subject
#print axioms Lime.PlanCheck.batchDoesNotReachPast_of_no_subject
#print axioms Lime.PlanCheck.a_check_with_no_subject_is_a_free_pass
#print axioms Lime.PlanCheck.planOk_of_no_subject
#print axioms Lime.PlanCheck.subjectCount_le_eleven
#print axioms Lime.PlanCheck.energyFilter_has_no_subject_on_an_unassigned_day
#print axioms Lime.PlanCheck.windDown_has_no_subject_on_an_unassigned_day
#print axioms Lime.PlanCheck.batch_has_no_subject_on_an_unassigned_day
-- DELETED AT W-33 (track P): impossible_has_no_subject -- REFUTED as
-- PlannerWit.impossible_has_no_subject_is_refuted; PlanCheck.impossible_has_no_subject_of_nothing_eligible
-- and impossible_has_a_subject_iff_an_impossible_answer_is_eligible replace it (audited below).
-- RENAMED WITH ITS THEOREM AT W-33 (not deleted): seven holds GIVEN no eligible impossible item;
-- the unconditional ceiling is EIGHT now (the_census_ceiling_is_eight_on_an_unassigned_day, below).
#print axioms Lime.PlannerWit.onlyOnWorkRows_is_work_anchored
#print axioms Lime.PlannerWit.the_whole_battery_passes_on_the_quiet_census_day
#print axioms Lime.PlannerWit.the_whole_battery_passes_on_the_quiet_day
#print axioms Lime.PlannerWit.the_quiet_eleven_is_one_checker_biting
#print axioms Lime.PlannerWit.the_census_ratio
#print axioms Lime.PlannerWit.the_census_ratio_at_a_work_anchored_eligibility
#print axioms Lime.PlannerWit.step_six_gave_no_checker_a_subject
#print axioms Lime.PlannerWit.the_census_counts_a_checker_that_fails

-- the day section as cells (stage 6 step P8, Emit.lean and PlannerWit §20)
#print axioms Lime.Emit.cells_are_the_nine_in_order
#print axioms Lime.Emit.cells_length
#print axioms Lime.Emit.timeCell_length
#print axioms Lime.Emit.markCell_length
#print axioms Lime.Emit.markChar_mem
#print axioms Lime.Emit.glyphOf_mem
#print axioms Lime.Emit.the_glyphs_stay_out_of_the_mark_column
#print axioms Lime.Emit.ciCell_is_the_glyph_off_the_scale
#print axioms Lime.Emit.pCell_is_empty_off_the_scale
#print axioms Lime.Emit.actualCell_of_not_done
#print axioms Lime.Emit.actualCell_of_rest
#print axioms Lime.Emit.the_three_quiet_kinds_are_off_the_scale
#print axioms Lime.Emit.rowsOf_length
#print axioms Lime.Emit.rowsOf_eq
#print axioms Lime.Emit.digitChar_no_newline
#print axioms Lime.Emit.digitsOf_no_newline
#print axioms Lime.Emit.timeCell_no_newline
#print axioms Lime.Emit.markCell_no_newline
#print axioms Lime.Emit.glyphOf_no_newline
#print axioms Lime.Emit.ciCell_no_newline
#print axioms Lime.Emit.actualCell_no_newline
#print axioms Lime.PlannerWit.the_day_section_of_the_routine_day_is_these_cells
#print axioms Lime.PlannerWit.the_emit_witness_rows_are_these_cells
#print axioms Lime.PlannerWit.the_eleven_notes_are_these_sentences
#print axioms Lime.PlannerWit.the_emit_predicates_at_the_witness_rows
#print axioms Lime.PlannerWit.the_emit_numerals
#print axioms Lime.PlannerWit.the_time_cell_is_local
/-! ############################################################################
## Stage 6, W-22, track G: §6.1's lift off the quiet class, and the census on the
## rows §8.3 is about
##
## `PlanCheck.dayPlan_ok_from_now_on_an_unassigned_day` is design §6.1's `planOk` at ELEVEN of eleven over
## `PlanCheck.withoutPast`'s day, for EVERY request and every `PlanCheck.SlotAnchored`
## eligibility — W-19 left that day at nine with the two comparisons refuted, and W-20/W-21
## reached eleven only on the quiet class.  `PlanCheck.the_census_ceiling_from_now_is_four_on_an_unassigned_day`
## is what it is worth: at most four of the eleven can have a subject there, at any request.
############################################################################ -/

#print axioms Lime.PlanCheck.withoutPast_work_rows_are_the_reservation_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_work_rows_are_the_reservation_on_an_unassigned_day
#print axioms Lime.PlanCheck.eligibleSomewhere_of_only_the_reservation
#print axioms Lime.PlanCheck.dayPlan_ok_from_now_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_on_a_day_with_no_replayed_block_on_an_unassigned_day
#print axioms Lime.PlanCheck.any_filter_of_any_eq_false
#print axioms Lime.PlanCheck.overbook_has_no_subject_from_now_on_an_unassigned_day
#print axioms Lime.PlanCheck.energyFilter_has_no_subject_from_now_on_an_unassigned_day
#print axioms Lime.PlanCheck.windDown_has_no_subject_from_now_on_an_unassigned_day
#print axioms Lime.PlanCheck.batch_has_no_subject_from_now_on_an_unassigned_day
-- DELETED AT W-33 (track P): impossible_has_no_subject_from_now -- REFUTED as
-- PlannerWit.impossible_has_no_subject_from_now_is_refuted; the four-check ceiling takes
-- impossible_has_no_subject_of_nothing_eligible at its own `hnone`.
#print axioms Lime.PlanCheck.rankSubjects_of_nothing_eligible
#print axioms Lime.PlanCheck.hotSubjects_of_nothing_eligible
#print axioms Lime.PlanCheck.rank_has_no_subject_of_nothing_eligible
#print axioms Lime.PlanCheck.hot_has_no_subject_of_nothing_eligible
#print axioms Lime.PlanCheck.the_census_ceiling_from_now_is_four_on_an_unassigned_day
#print axioms Lime.PlannerWit.onlyOnFreeWorkRows_is_slot_anchored
#print axioms Lime.PlannerWit.the_whole_battery_passes_from_now_at_the_census_request
#print axioms Lime.PlannerWit.the_whole_battery_passes_from_now_at_the_queued_request
#print axioms Lime.PlannerWit.the_whole_battery_passes_from_now_at_the_running_request
#print axioms Lime.PlannerWit.the_eleven_from_now_is_four_checkers_biting
#print axioms Lime.PlannerWit.the_census_requests_are_not_quiet
#print axioms Lime.PlannerWit.step_seven_gave_no_checker_a_subject
#print axioms Lime.PlannerWit.four_is_the_ceiling_and_it_is_reached_on_an_unassigned_day
#print axioms Lime.PlannerWit.the_slot_anchoring_is_the_whole_residue
/-! ############################################################################
## Stage 6, W-23, track G: the eligibility axis closes on the WHOLE day, and the
## day that proves one clause of it cannot be dropped
##
## `PlanCheck.dayPlan_ok_is_the_core_seven_on_an_unassigned_day` says §6.1's eleven over the whole day IS §6.1's
## seven, at every request and every `PlanCheck.FromNowAnchored` eligibility — a `Bool`
## equality, nothing assumed about the log.  `PlannerWit.dayPlan_ok_at_every_slot_anchored_
## eligibility_on_the_whole_day_is_refuted` is why the third clause is a hypothesis and not a
## decoration, and `PlannerWit.the_core_seven_is_false_on_three_whole_days` is the residue it
## leaves: the replayed past, on three days this kernel already builds.
############################################################################ -/

#print axioms Lime.PlanCheck.eligibleSomewhere_of_nothing_from_now_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_is_the_core_seven_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_of_the_core_seven_on_an_unassigned_day
#print axioms Lime.PlanCheck.the_census_ceiling_on_the_whole_day_is_five_on_an_unassigned_day
#print axioms Lime.PlannerWit.fromNowWorkRows_is_from_now_anchored
#print axioms Lime.PlannerWit.the_from_now_eligibility_reads_all_three_of_its_clauses
#print axioms Lime.PlannerWit.onlyOnFreeWorkRows_is_not_from_now_anchored
#print axioms Lime.PlannerWit.witBuildsIdleQueued
#print axioms Lime.PlannerWit.theIdleQueuedRequest_wallsAgree
#print axioms Lime.PlannerWit.the_idle_queued_request_agrees
#print axioms Lime.PlannerWit.the_idle_queued_request_is_inside_the_calendar
#print axioms Lime.PlannerWit.the_idle_queued_request_is_plain
#print axioms Lime.PlannerWit.the_idle_queued_day_is_the_second_sibling_and_an_evening
#print axioms Lime.PlannerWit.dayPlan_ok_on_the_whole_day_at_a_slot_anchored_eligibility_is_refuted
#print axioms Lime.PlannerWit.dayPlan_ok_at_every_slot_anchored_eligibility_on_the_whole_day_is_refuted
#print axioms Lime.PlannerWit.the_from_now_lift_holds_where_the_slot_anchored_one_is_refuted
#print axioms Lime.PlannerWit.the_whole_day_census_at_the_from_now_eligibility_is_five
#print axioms Lime.PlannerWit.five_is_the_ceiling_and_it_is_reached_on_an_unassigned_day
#print axioms Lime.PlannerWit.the_core_seven_is_false_on_three_whole_days

-- APPENDED 2026-09-22 (stage 6, W-24, track P): the `plan` section of the wire — an `Emit.Row`
-- reaches the FFI entry at last (README gaps 1105/1318).  `EmitWire.lean` is the new module;
-- `Emit.batchTitle_is_the_frame_over_batchNames` is the one theorem added to `Emit.lean`, where
-- the batch members were split out of the joined title so the Rust fitter can reach them.
#print axioms Lime.Emit.batchTitle_is_the_frame_over_batchNames
#print axioms Lime.EmitWire.asPlan_keeps_the_value
#print axioms Lime.EmitWire.asPlan_renames_a_refusal
#print axioms Lime.EmitWire.runRows_without_a_plan_section_is_runCap
#print axioms Lime.EmitWire.callRows_without_a_plan_section_is_callCap
#print axioms Lime.EmitWire.callExport_is_callRows
#print axioms Lime.EmitWire.runRows_refuses_a_plan_section_with_commands
#print axioms Lime.EmitWire.rowJson_is_the_nine_cells_in_order
#print axioms Lime.EmitWire.rowsJson_length
#print axioms Lime.EmitWire.rowsOfReq_eq
#print axioms Lime.EmitWire.readPrios_refuses_past_the_cap
#print axioms Lime.EmitWire.readSegs_of_nil
#print axioms Lime.EmitWire.readPrios_of_nil
#print axioms Lime.EmitWire.readPrio_refuses_a_priority_past_seven
#print axioms Lime.EmitWire.readPrio_refuses_eight
#print axioms Lime.EmitWire.readPrio_accepts_seven
#print axioms Lime.EmitWire.readNote_refuses_a_long_text
#print axioms Lime.EmitWire.readNote_accepts_a_short_text
#print axioms Lime.EmitWire.readKind_refuses_an_unknown_kind
#print axioms Lime.EmitWire.readKind_refuses_a_batch_past_the_cap
#print axioms Lime.EmitWire.readKind_accepts_a_batch_at_the_cap
#print axioms Lime.EmitWire.readSeg_refuses_an_energy_past_five
#print axioms Lime.EmitWire.readSeg_refuses_an_inverted_segment
#print axioms Lime.EmitWire.readSeg_refuses_past_the_horizon
#print axioms Lime.EmitWire.readSeg_refuses_a_planned_past_the_bound
#print axioms Lime.EmitWire.readSeg_refuses_a_zero_denominator
#print axioms Lime.EmitWire.readSeg_accepts_a_block
#print axioms Lime.EmitWire.readRowSection_refuses_a_bad_bed
#print axioms Lime.EmitWire.readRowSection_accepts_an_empty_day
#print axioms Lime.EmitWire.rowKey_names_are_the_wire_keys
#print axioms Lime.EmitWire.segErrName_names_the_two
#print axioms Lime.EmitWire.the_refusals_spell_themselves
#print axioms Lime.EmitWire.rowRefusalJson_is_the_err_plan_shape
#print axioms Lime.EmitWire.readOptNote_of_an_absent_note
#print axioms Lime.EmitWire.readOptNote_of_a_present_note
#print axioms Lime.EmitWire.batchNamesOf_of_a_batch
#print axioms Lime.EmitWire.batchNamesOf_of_a_block
#print axioms Lime.EmitWire.withPlan_appends_the_plan_key
/-! ############################################################################
## Stage 6, W-24, track G: the LOG axis, one named clause at a time
##
## `PlanCheck.PastPays` is the four clauses the replayed past owes §6.1's seven — three of the
## seven owe it nothing at all — and `PlanCheck.dayPlan_ok_core_of_a_paying_past_on_an_unassigned_day` is the
## whole-day lift with `hnopast` gone.  `PlanCheck.PastPays_of_no_past_block_on_an_unassigned_day` makes
## `PlanCheck.dayPlan_ok_core_given_the_budget` a corollary of it, and
## `PlannerWit.the_paying_past_holds_where_hnopast_does_not` is the request where the new one
## fires and the old one cannot.  `PlannerWit.the_paying_past_fails_on_four_whole_days` is the
## other bound: one refuting day per clause, no clause implied by the other three.
############################################################################ -/

#print axioms Lime.PlanCheck.pastHalf_segments
#print axioms Lime.PlanCheck.segOf_replayed
#print axioms Lime.PlanCheck.a_block_row_that_is_not_the_reservation_has_started_on_an_unassigned_day
#print axioms Lime.PlanCheck.foldl_add_filter_le
#print axioms Lime.PlanCheck.blockSeconds_withoutActive_le_pastHalf_on_an_unassigned_day
#print axioms Lime.PlanCheck.PastPays_of_no_past_block_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_core_of_a_paying_past_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_on_the_whole_day_on_an_unassigned_day
#print axioms Lime.PlannerWit.the_over_budget_request_is_over_budget
#print axioms Lime.PlannerWit.the_log_at_the_census_request_holds_a_block
#print axioms Lime.PlannerWit.the_paying_past_at_the_census_request
#print axioms Lime.PlannerWit.the_paying_past_holds_where_hnopast_does_not
#print axioms Lime.PlannerWit.the_core_seven_hold_on_the_whole_day_of_a_worked_morning
#print axioms Lime.PlannerWit.the_eleven_hold_on_the_whole_day_of_a_worked_morning
#print axioms Lime.PlannerWit.the_paying_past_fails_on_four_whole_days
#print axioms Lime.PlannerWit.the_core_seven_is_false_on_the_over_budget_day
#print axioms Lime.PlannerWit.the_log_axis_moves_no_census_number
#print axioms Lime.PlannerWit.plan_does_not_overbook_as_stage_6_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_designs_restatement_of_the_overbooking_law_is_refuted_too
#print axioms Lime.PlannerWit.the_replayed_half_is_a_strict_part_of_the_day
#print axioms Lime.PlannerWit.every_refuted_day_refutes_its_own_clause
#print axioms Lime.PlannerWit.the_census_at_every_request_the_prose_quotes

-- APPENDED 2026-09-22: stage 6 W-24, the REPAIR step (AGENTS §6.3).  README gap
-- 1415's eight: `EmitWire.idWithin` is the smart constructor the section's five
-- `Id`s now go through, and these are its bound's rejection theorems and their
-- acceptances.  Three of the five were named by the audit (`item`, a priority
-- record's `id`, a batch member) and two were not (`Note.noPosition`'s and
-- `Note.bufferBefore`'s, both read by `readNote`).
#print axioms Lime.EmitWire.idWithin_refuses_a_long_id
#print axioms Lime.EmitWire.idWithin_accepts_at_the_bound
#print axioms Lime.EmitWire.idWithin_refuses_1025_and_accepts_1024
#print axioms Lime.EmitWire.readSeg_refuses_a_long_item
#print axioms Lime.EmitWire.readPrio_refuses_a_long_id
#print axioms Lime.EmitWire.readKind_refuses_a_long_batch_member
#print axioms Lime.EmitWire.readNote_refuses_a_long_no_position_id
#print axioms Lime.EmitWire.readNote_refuses_a_long_buffer_before_id

-- APPENDED 2026-09-22: stage 6 W-25, track A (AGENTS §6.3).  README gap 1415's
-- OTHER HALF: the seven bare `Nat`s `EmitWire.readNote` read with no stated
-- width.  `u32Within` and `secWithin` are the two constructors and NEITHER
-- declares a bound: the five counts take `CapWire.maxRemaining`
-- (`Look.maxPlanMinutes`, whose own header says *fork `u32`*) and the two
-- absolute seconds take `Cal.Instant.wf` through `Cal.mkInstant?`, which is the
-- clause `Planner.Seg.wf` already puts on a segment's `stop`.  The two
-- `_is_the_` theorems are AGENTS §5.3's "not a second bound" as a theorem
-- rather than as a sentence.
#print axioms Lime.EmitWire.u32Within_refuses_past_the_width
#print axioms Lime.EmitWire.u32Within_accepts_at_the_width
#print axioms Lime.EmitWire.u32Within_refuses_the_width_plus_one
#print axioms Lime.EmitWire.u32Within_is_the_logs_u32_width
#print axioms Lime.EmitWire.secWithin_refuses_past_the_calendar
#print axioms Lime.EmitWire.secWithin_accepts_a_representable_second
#print axioms Lime.EmitWire.secWithin_refuses_the_first_second_past_the_years
#print axioms Lime.EmitWire.secWithin_is_the_clause_Seg_wf_puts_on_a_stop
#print axioms Lime.EmitWire.readNote_refuses_a_long_duration
#print axioms Lime.EmitWire.readNote_refuses_a_low_past_the_calendar
#print axioms Lime.EmitWire.readNote_refuses_a_high_past_the_calendar
#print axioms Lime.EmitWire.readNote_refuses_a_blocks_done_past_the_width
#print axioms Lime.EmitWire.readNote_refuses_a_planned_past_the_width
#print axioms Lime.EmitWire.readNote_refuses_a_total_past_the_width
#print axioms Lime.EmitWire.readNote_refuses_a_left_min_past_the_width
#print axioms Lime.EmitWire.readNote_accepts_the_seven_inside_their_bounds
-- ===================================================================
-- APPENDED 2026-09-22: stage 6, W-25, track G (AGENTS §6.3).  Two things.
--
-- (1) THE WALL AXIS, the third and last `∀` over the request in §6.1's
--     whole-day lift.  W-23 named the eligibility bound (`FromNowAnchored`)
--     and W-24 the log bound (`PastPays`); the one left was an unnamed
--     store-wide plainness hypothesis that is FALSE of a calendar holding a
--     meeting tomorrow.  `PlanCheck.PlainStore` names it, `WallsArePlain`
--     restricts it to the entities a Wall row of the produced day actually
--     names, and `PlannerWit.theOffDayRequest` is the census Wednesday with
--     one Thursday line added: the blanket is false there, the restriction
--     holds, and §6.1's eleven hold on the whole day through the new lift.
--
-- (2) G3.  `Goals.plan_is_stable_across_a_replan` is refuted, and NOT for
--     design §6.3 row 3's reason: the hypotheses leave `run` free, exactly as
--     `plan_tail_drop`'s do, and the design's own restatement (`not open`) is
--     refuted by the same pair.  It cannot bite because `Planner.SegFlags.
--     isOpen` is set at ONE construction site in this kernel — the running
--     interruption — and §8.2 choice 5b's reservation, the row that grows,
--     is not it.  No goal is discharged: the burn-down stays 9.
-- ===================================================================
#print axioms Lime.PlanCheck.WallsArePlain_of_a_plain_store
#print axioms Lime.PlanCheck.dayPlan_ok_core_of_plain_walls_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_on_the_whole_day_of_plain_walls_on_an_unassigned_day
#print axioms Lime.PlannerWit.the_two_wall_witness_loads
#print axioms Lime.PlannerWit.the_off_day_request_agrees
#print axioms Lime.PlannerWit.the_off_day_request_is_inside_the_calendar
#print axioms Lime.PlannerWit.tomorrows_meeting_is_not_one_of_todays_walls
#print axioms Lime.PlannerWit.the_off_day_walls_name_the_meeting
#print axioms Lime.PlannerWit.the_off_day_request_has_plain_walls
#print axioms Lime.PlannerWit.the_blanket_plainness_is_false_at_the_off_day_request
#print axioms Lime.PlannerWit.the_off_day_past_pays
#print axioms Lime.PlannerWit.the_core_seven_hold_where_the_blanket_fails
#print axioms Lime.PlannerWit.the_eleven_hold_where_the_blanket_fails
#print axioms Lime.PlannerWit.the_census_request_has_a_plain_store
#print axioms Lime.PlannerWit.the_relabelled_day_holds_tomorrows_meeting
#print axioms Lime.PlannerWit.the_wall_axis_can_fail
#print axioms Lime.PlannerWit.the_witness_day_holds_a_settled_block_no_replan_may_drop
#print axioms Lime.PlannerWit.plan_is_stable_across_a_replan_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin
#print axioms Lime.PlannerWit.the_designs_restatement_of_the_stability_law_is_refuted_too
#print axioms Lime.PlannerWit.the_reservation_row_is_not_marked_open
#print axioms Lime.PlannerWit.no_row_of_the_days_this_tree_builds_is_open
#print axioms Lime.PlannerWit.an_hour_later_changes_one_field_and_keeps_the_window_the_log_anchors
#print axioms Lime.PlannerWit.an_hour_later_keeps_every_row_that_had_settled
#print axioms Lime.PlannerWit.three_rows_had_settled_when_the_witness_planned
#print axioms Lime.PlannerWit.the_wall_axis_moves_no_census_number
#print axioms Lime.PlannerWit.the_wall_axis_definitions_are_not_constants
#print axioms Lime.PlannerWit.the_open_sweep_and_the_replan_both_had_a_subject

-- ===================================================================
-- W-26 (track G).  The fourth and last axis of §6.1's lift is named —
--     `PlanCheck.DecoderPays`, the request decoder's four clauses — and
--     the builder is shown to pay exactly one of them, at EVERY request
--     it accepts, because it never reads `Planner.RuntimeIn` at all.
--     And §8.3's missing invariant is stated: `PlanCheck.holeFree`, the
--     segment-free hole of README gap 1529, computed FALSE on the day
--     where the subject census is seven.  It is NOT one of the eleven.
--     No goal is discharged: the burn-down stays 9.
-- ===================================================================
#print axioms Lime.PlanCheck.futureHalf_segments
#print axioms Lime.PlanCheck.mem_futureHalf
#print axioms Lime.PlanCheck.holeFree_iff
#print axioms Lime.PlanCheck.the_last_row_is_never_a_holes_subject
#print axioms Lime.PlanCheck.an_uncovered_instant_between_two_rows_is_a_hole
#print axioms Lime.PlanCheck.dayPlan_ok_on_the_whole_day_of_a_paying_decoder_on_an_unassigned_day
#print axioms Lime.PlannerWit.mkPlanReq?_ignores_state
#print axioms Lime.PlannerWit.the_builder_accepts_a_running_block_it_never_checked
#print axioms Lime.PlannerWit.the_census_days_future_half_has_a_hole
#print axioms Lime.PlannerWit.the_tail_remainder_day_has_no_hole
#print axioms Lime.PlannerWit.the_tail_remainder_day_really_has_a_tail
#print axioms Lime.PlannerWit.the_hole_property_is_not_a_constant
#print axioms Lime.PlannerWit.the_hole_property_is_not_one_of_the_eleven
#print axioms Lime.PlanCheck.a_zero_length_row_cannot_cover_an_instant
#print axioms Lime.PlanCheck.holeFree_of_no_rows
#print axioms Lime.PlannerWit.the_census_request_pays_the_decoder
#print axioms Lime.PlannerWit.the_census_request_pays_the_fifth_clause
#print axioms Lime.PlannerWit.the_future_half_is_not_the_whole_day
#print axioms Lime.PlannerWit.the_hole_property_is_blind_to_a_leading_remainder

-- ===================================================================
-- Stage 6 W-27, track P (step R2, D48): the PLANNER's inputs cross the
-- wire.  `PlanWire.lean` -- the four values `Planner.PlanReq` needed and
-- no section carried: `state` (SS9's RuntimeIn), `routines`, `overrides`
-- and `prio.batchMaxMin` (SS16's [priority] batch_max_min, README gap 801).
-- Every bound is one this wire already had: CapWire.maxCandId,
-- CapWire.maxRemaining (the fork u32), Cal.Instant.wf, Look.maxDayMin and
-- Planner.maxCands, each through the constructor that already owns it.
-- No goal is discharged: the burn-down stays 9.
-- ===================================================================
#print axioms Lime.PlanWire.instantWithin_is_secWithin_at_the_zero_nanosecond
#print axioms Lime.PlanWire.instantWithin_refuses_past_the_calendar
#print axioms Lime.PlanWire.instantWithin_accepts_a_representable_second
#print axioms Lime.PlanWire.instantWithin_refuses_the_first_second_past_the_years
#print axioms Lime.PlanWire.planKey_names_are_the_wire_keys
#print axioms Lime.PlanWire.planKey_record_names_are_the_wire_keys
#print axioms Lime.PlanWire.the_refusals_spell_themselves
#print axioms Lime.PlanWire.plannerRefusalJson_is_the_err_planner_shape
#print axioms Lime.PlanWire.the_two_refusal_families_do_not_share_a_key
#print axioms Lime.PlanWire.readActive_refuses_a_long_id
#print axioms Lime.PlanWire.readActive_refuses_a_start_past_the_calendar
#print axioms Lime.PlanWire.readActive_accepts_a_running_block
#print axioms Lime.PlanWire.the_four_break_places_read
#print axioms Lime.PlanWire.readInterrupt_refuses_a_long_id
#print axioms Lime.PlanWire.readInterrupt_accepts_an_open_interruption
#print axioms Lime.PlanWire.readState_of_an_empty_object
#print axioms Lime.PlanWire.readState_accepts_a_running_day
#print axioms Lime.PlanWire.readRoutine_refuses_a_long_id
#print axioms Lime.PlanWire.readRoutine_refuses_a_window_past_the_calendar
#print axioms Lime.PlanWire.readRoutine_refuses_a_duration_past_the_width
#print axioms Lime.PlanWire.readRoutine_accepts_an_instance
#print axioms Lime.PlanWire.readRoutine_mandatory_is_absent_is_false
#print axioms Lime.PlanWire.readRoutines_of_nil
#print axioms Lime.PlanWire.readRoutines_accepts_two_instances
#print axioms Lime.PlanWire.readBatchMaxMin_refuses_past_the_width
#print axioms Lime.PlanWire.readBatchMaxMin_refuses_an_absent_priority
#print axioms Lime.PlanWire.readBatchMaxMin_accepts_the_shipped_default
#print axioms Lime.PlanWire.readBatchMaxMin_is_the_forks_u32_width
#print axioms Lime.PlanWire.readPlannerSection_of_an_empty_object
#print axioms Lime.PlanWire.readPlannerSection_refuses_a_routines_that_is_not_an_array
#print axioms Lime.PlanWire.runPlanner_without_a_planner_section_is_runRows
#print axioms Lime.PlanWire.callPlanner_without_a_planner_section_is_callRows
-- W-28 (D48's RESPONSE half, README gap 1667): the two theorems W-27 proved so that the step
-- which builds the response would be the step which deletes them are GONE --
-- runPlanner_with_a_readable_section_answers_as_runRows (the call answers the day now, so the
-- statement is false of this definition) and
-- runPlanner_keeps_the_capacity_sections_name_for_an_unreadable_at (gap 1672's unreachable
-- branch: `Boundary.CapParts` hands the decoded instant out and the second `readAt` is gone).
#print axioms Lime.PlanWire.runPlanner_passes_a_rows_refusal_through
#print axioms Lime.PlanWire.runPlanner_answers_the_day
#print axioms Lime.PlanWire.runPlanner_refuses_a_section_the_decoder_refuses
#print axioms Lime.PlanWire.runPlanner_refuses_a_planner_section_without_a_capacity
#print axioms Lime.PlanWire.runPlanner_refuses_a_batch_max_min_the_decoder_refuses
#print axioms Lime.PlanWire.runPlanner_refuses_a_request_the_assembler_refuses
#print axioms Lime.PlanWire.segJson_writes_every_field_of_a_segment
#print axioms Lime.PlanWire.segJson_writes_null_for_every_absent_field
#print axioms Lime.PlanWire.noteJson_names_the_eleven
#print axioms Lime.PlanWire.diagJson_of_an_untroubled_day
#print axioms Lime.PlanWire.diagJson_carries_its_lists
#print axioms Lime.PlanWire.priosJson_is_the_id_and_the_priority
#print axioms Lime.PlanWire.the_routine_errors_spell_themselves
-- W-28 repair: the emitters pinned as FUNCTIONS and not at two points (README gap 1881).
#print axioms Lime.PlanWire.segJson_is_its_eleven_keys
#print axioms Lime.PlanWire.flagsJson_is_its_seven_marks
#print axioms Lime.PlanWire.kindJson_is_the_name_and_the_batch
#print axioms Lime.PlanWire.idsJson_is_the_list
#print axioms Lime.PlanWire.optStr_is_null_or_the_id
#print axioms Lime.PlanWire.priosJson_is_the_id_and_the_priority_of_every_pair
#print axioms Lime.PlanWire.diagJson_is_its_twelve_fields
#print axioms Lime.PlanWire.noteJson_writes_every_field
#print axioms Lime.PlanWire.routineErrName_spells_every_id
#print axioms Lime.PlanWire.planJson_writes_the_seven_keys
#print axioms Lime.PlanWire.the_plan_objects_keys_are_disjoint
#print axioms Lime.PlanWire.planJson_of_a_planned_day_is_the_requests_own_views
#print axioms Lime.PlanWire.planJson_segments_length
#print axioms Lime.PlanWire.intoPlan_skips_another_key
#print axioms Lime.PlanWire.intoPlan_into_the_plan_object
#print axioms Lime.PlanWire.intoPlan_makes_a_plan_object
#print axioms Lime.PlanWire.withPlanner_shares_the_plan_object
#print axioms Lime.PlanWire.withPlanner_makes_the_plan_object
#print axioms Lime.PlanWire.the_seam_carries_its_run_exactly_when_it_carries_its_facts
#print axioms Lime.PlanWire.the_two_candidate_caps_are_one_number
#print axioms Lime.PlanWire.hashHex_length
#print axioms Lime.PlanWire.readKind_reads_back_every_kind_it_writes
#print axioms Lime.PlanWire.callExport_is_callPlanner

-- W-28: the seam carries the RUN, not only the merged answer (README gap 1669), and the
-- capacity request hands out what it decoded (gaps 1671 and 1672).
#print axioms Lime.Seal.trimRun_of_wanted_facts
#print axioms Lime.runCapP_bytes
#print axioms Lime.runCapZ_is_runCapZP_bytes
#print axioms Lime.EmitWire.runRowsP_bytes

-- W-28 (track G): the leading half of README gap 1620, and the decoder axis's second payer.
#print axioms Lime.PlanCheck.coveredAt_iff
#print axioms Lime.PlanCheck.coveredAt_of_no_rows
#print axioms Lime.PlanCheck.holeFreeFrom_iff
#print axioms Lime.PlanCheck.holeFreeFrom_implies_holeFree
#print axioms Lime.PlanCheck.holeFreeFrom_of_no_rows
#print axioms Lime.PlannerWit.readActive_answers_only_a_block_mkActive_built
#print axioms Lime.PlannerWit.readOptActive_answers_only_a_block_mkActive_built
#print axioms Lime.PlannerWit.readState_reads_active
#print axioms Lime.PlannerWit.readState_answers_only_a_block_mkActive_built
#print axioms Lime.PlannerWit.a_request_whose_state_the_wire_read_pays_the_active_clause
#print axioms Lime.PlannerWit.an_at_the_wire_accepted_is_inside_the_calendar
#print axioms Lime.PlannerWit.the_instant_bound_is_one_second_wider_than_the_now_clause
#print axioms Lime.PlannerWit.the_eleven_hold_with_every_axis_named
#print axioms Lime.PlannerWit.the_leading_guard_catches_the_leading_remainder
#print axioms Lime.PlannerWit.the_leading_guard_keeps_the_tail_carve_out
#print axioms Lime.PlannerWit.the_leading_guard_is_not_a_constant
#print axioms Lime.PlannerWit.the_leading_guard_is_not_one_of_the_eleven

-- W-29 (P9): §8.2 step 5's rows reach the day.  `Planner.PlanReq.assignedRows` is in
-- `Planner.dayRows`, so the composition D50 named is done; `assignedSeg`'s ten field laws are
-- what pin the BYTES a row writes rather than its shape (W-28's ten survivors), and the four
-- "is not" corollaries are one class lemma (`a_work_row_is_not`) at four kinds.
--
-- DELETED HERE, each restated with its refutation beside it: Planner.a_block_row_is_replayed
-- _or_reserved; Planner.assignedOf_dayPlan_drops_the_routine_rows; Planner.the_day_assigns
-- _nothing_after_now_but_the_running_block; PlanCheck.dayPlan_block_rows_are_replayed_or
-- _reserved and the nineteen lifts that carried `hblk`, each renamed to name the subdomain it
-- is now proved on (AGENTS §3.1 item 4); PlannerWit.the_budget_does_not_reach_the_assigned
-- _set_until_the_assign_fold_lands and the_battery_passes_on_the_day_step_six_filled.
#print axioms Lime.Planner.batchIdsOf_of_bounded
#print axioms Lime.Planner.batchIdsOf_is_a_prefix
#print axioms Lime.Planner.WfSeg.stop_lt_yearEnd
#print axioms Lime.Planner.WfSeg.start_le_stop
#print axioms Lime.Planner.segOf_items
#print axioms Lime.Planner.PlanReq.a_slot_is_not_empty
#print axioms Lime.Planner.PlanReq.no_slot_touches_a_wall
#print axioms Lime.Planner.assignedSeg_start
#print axioms Lime.Planner.assignedSeg_stop
#print axioms Lime.Planner.assignedSeg_energy
#print axioms Lime.Planner.assignedSeg_planned
#print axioms Lime.Planner.assignedSeg_mult
#print axioms Lime.Planner.assignedSeg_inst
#print axioms Lime.Planner.assignedSeg_underused
#print axioms Lime.Planner.assignedSeg_hot
#print axioms Lime.Planner.assignedSeg_note
#print axioms Lime.Planner.assignedSeg_is_work
#print axioms Lime.Planner.shortListIsItsHead
#print axioms Lime.Planner.assignedSeg_items_when_the_group_fits_the_batch_bound
#print axioms Lime.Planner.PlanReq.mem_assignedRows
#print axioms Lime.Planner.PlanReq.assignedRows_are_work
#print axioms Lime.Planner.PlanReq.a_work_row_is_not
#print axioms Lime.Planner.PlanReq.assignedRows_are_not_walls
#print axioms Lime.Planner.PlanReq.assignedRows_are_not_breaks
#print axioms Lime.Planner.PlanReq.assignedRows_are_not_wind_down
#print axioms Lime.Planner.PlanReq.assignedRows_are_not_rest
#print axioms Lime.Planner.PlanReq.an_assigned_row_is_a_slot_of_the_day
#print axioms Lime.Planner.PlanReq.an_assigned_row_carries_its_group
#print axioms Lime.PlannerWit.the_assigned_set_is_not_the_reservations_alone
#print axioms Lime.PlannerWit.the_assigned_day_has_a_block_row_that_is_not_the_reservation
-- W-29 (track G): what STEP 6 keeps (`finalAssign_ok`, the invariant a composed Block row
-- reads), the group provenance that carries it to a group's members, and the FIFTH clause the
-- request decoder owes -- the wire's `ci` against the plan's `effectiveCi`, README gap 1984.
#print axioms Lime.PlanCheck.KeepsTheFilterFields_refl
#print axioms Lime.PlanCheck.KeepsTheFilterFields_unspend
#print axioms Lime.PlanCheck.AssignOk_of_freed
#print axioms Lime.PlanCheck.rePlaceWalk_keeps_AssignOk
#print axioms Lime.PlanCheck.displaceInto_keeps_AssignOk
#print axioms Lime.PlanCheck.deferOne_keeps_AssignOk
#print axioms Lime.PlanCheck.deferWalk_keeps_AssignOk
#print axioms Lime.PlanCheck.finalAssign_ok
#print axioms Lime.PlanCheck.an_assigned_slot_is_under_its_slots_energy
#print axioms Lime.PlanCheck.KeepsTheFilterFields_trans
#print axioms Lime.PlanCheck.KeepsTheFilterFields_assignStep
#print axioms Lime.PlanCheck.KeepsTheFilterFields_rePlaceWalk
#print axioms Lime.PlanCheck.KeepsTheFilterFields_displaceInto
#print axioms Lime.PlanCheck.KeepsTheFilterFields_deferOne
#print axioms Lime.PlanCheck.KeepsTheFilterFields_deferWalk
#print axioms Lime.PlanCheck.KeepsTheFilterFields_foldl_assignStep
#print axioms Lime.PlanCheck.CarriesBuiltGroups_of_keeps
#print axioms Lime.PlanCheck.CarriesBuiltGroups_startGroups
#print axioms Lime.PlanCheck.CarriesBuiltGroups_finalAssign
#print axioms Lime.PlanCheck.a_member_of_an_assigned_group_carries_its_ci
#print axioms Lime.PlanCheck.candsAgree_iff
#print axioms Lime.PlanCheck.candsAgree_of_no_cands
#print axioms Lime.PlanCheck.a_candidates_ci_is_its_items_ci
#print axioms Lime.PlanCheck.a_candidate_whose_two_readings_differ_breaks_the_clause
#print axioms Lime.PlanCheck.an_assigned_member_is_under_its_slots_energy
#print axioms Lime.PlanCheck.an_assigned_member_after_the_wind_down_is_not_demanding
-- and the three definitions the clause is stated over, audited the way `Lime.WfPlan` is (6.3).
#print axioms Lime.PlanCheck.candPlanView
#print axioms Lime.PlanCheck.candWireView
#print axioms Lime.PlanCheck.candsAgree
-- W-29 (track G): the seam computed at a request this tree already builds, and the settling
-- answer to "does the composition step make README gap 1529 enableable" -- it does not.
#print axioms Lime.PlannerWit.the_wire_ci_and_the_plan_ci_disagree_at_the_busy_request
#print axioms Lime.PlannerWit.the_busy_request_does_not_pay_the_fifth_decoder_clause
#print axioms Lime.PlannerWit.the_lifts_own_request_pays_the_fifth_clause_for_nothing
#print axioms Lime.PlannerWit.the_filter_passed_a_slot_the_battery_reads_differently
#print axioms Lime.PlannerWit.the_hole_survives_where_the_composition_adds_no_row

-- ############################################################################
-- W-30 (track G): THE LIFT'S DOMAIN, RESTORED.  P9 composed 8.2 step 5's rows into
-- `Planner.dayRows` and the two `planOkCore` lifts kept their proofs by taking
-- `r.assignedRows = []` -- a precondition that excludes exactly the days step 5 is about,
-- which is AGENTS 5.2's failure mode and the shape D29 declined for `plan_tail_drop`.  Six
-- of the seven core checks are proved over a day that assigns here; the seventh
-- (`noOverbook`) is a COUNT this tree does not have and is named as a hypothesis rather
-- than assumed silently (README gap 2020).
--
-- ONE AUDIT LINE WAS RENAMED WITH ITS THEOREM, not deleted: PlanCheck.dayPlan_ok_core
-- _on_an_unassigned_day -> `PlanCheck.dayPlan_ok_core_given_the_budget`.  It is a strict
-- generalisation: `PlanCheck.an_unassigned_day_pays_the_lift` turns the old hypothesis into the
-- two new arguments in one line, so every instance of the old statement is an instance of the
-- new one (D5, AGENTS 5.2).  `PlanCheck.dayPlan_ok_core_from_now_given_the_budget` is the same
-- generalisation of the `withoutPast` lift, and there
-- `PlanCheck.dayPlan_ok_core_from_now_on_an_unassigned_day` is KEPT as a corollary of it, for
-- the callers that really are about a day the fold left alone.
--
-- ONE AUDIT LINE IS NEW BECAUSE A GOAL LEFT `Goals.lean`:
-- `PlanCheck.plan_respects_the_energy_filter`, with
-- `PlannerWit.plan_respects_the_energy_filter_as_stage_6_wrote_it_is_refuted` beside it
-- (AGENTS 3.1 item 3).  Burn-down 9 -> 8.

-- The row-level facts a Block row the FOLD placed brings to the battery.
#print axioms Lime.Planner.PlanReq.an_assigned_row_starts_at_or_after_now
#print axioms Lime.PlanCheck.dayPlan_block_rows_are_reserved_or_assigned
#print axioms Lime.PlanCheck.a_block_row_of_a_logless_day_starts_at_or_after_now
#print axioms Lime.PlanCheck.an_assigned_block_row_is_at_most_one_block
#print axioms Lime.PlanCheck.an_assigned_block_row_clears_a_wall_row
#print axioms Lime.PlanCheck.a_block_row_from_now_clears_a_break_row
#print axioms Lime.PlanCheck.the_reservation_row_clears_a_wall_row
-- The six block-side checks, each with the hypotheses it needs and no others.
#print axioms Lime.PlanCheck.oneBlockAtATime_of_a_logless_day
#print axioms Lime.PlanCheck.noBlockOverAWall_of_a_logless_day
#print axioms Lime.PlanCheck.noBlockOverABreak_of_a_logless_day
#print axioms Lime.PlanCheck.energyFilterOk_of_a_day_that_pays
#print axioms Lime.PlanCheck.plan_respects_the_energy_filter
#print axioms Lime.PlanCheck.noDemandingAfterWindDown_of_a_day_that_pays
#print axioms Lime.PlanCheck.noOverbook_when_only_the_reservation_is_a_block
#print axioms Lime.PlanCheck.a_reserved_block_row_is_active
#print axioms Lime.PlanCheck.an_unassigned_day_pays_the_lift
#print axioms Lime.PlanCheck.withoutPast_block_rows_are_reserved_or_assigned
#print axioms Lime.PlanCheck.dayPlan_ok_core_from_now_on_an_unassigned_day
-- The chain that carries the FIFTH decoder clause from an assignment to a ROW.
#print axioms Lime.PlanCheck.mem_assignedRows_at_a_slot
#print axioms Lime.PlanCheck.an_assigned_row_names_a_member
#print axioms Lime.PlanCheck.an_answer_of_the_pass_names_its_candidate
#print axioms Lime.PlanCheck.a_ranked_candidate_is_a_candidate
#print axioms Lime.PlanCheck.a_member_of_an_assigned_group_is_a_candidate
#print axioms Lime.PlanCheck.an_assigned_members_ci_is_under_its_slots_energy
#print axioms Lime.PlanCheck.an_assigned_members_ci_after_the_wind_down
#print axioms Lime.PlanCheck.AssignedRowsPay_of_a_paying_decoder
-- W-30 repair (gap 2133): the fourth axis carries the fifth clause, and these two
-- lifts discharge `hpay` from it over a day that ASSIGNS.
#print axioms Lime.PlanCheck.dayPlan_ok_core_of_a_paying_decoder
#print axioms Lime.PlanCheck.dayPlan_ok_core_from_now_of_a_paying_decoder
-- and the property the hypothesis was replaced by, audited the way `Lime.WfPlan` is (6.3).
#print axioms Lime.PlanCheck.AssignedRowsPay
-- W-30 (track G): the witness the lift needed and nine runs did not have -- a request that
-- ASSIGNS and whose decoder PAYS, and the refutation of the goal that left `Goals.lean`.
#print axioms Lime.PlannerWit.the_paying_witness_loads
#print axioms Lime.PlannerWit.the_paying_witness_holds_the_wall_and_two_tasks
#print axioms Lime.PlannerWit.the_paying_witness_indexes_the_calendars_one_wall
#print axioms Lime.PlannerWit.the_paying_request_assigns_and_the_battery_passes
#print axioms Lime.PlannerWit.the_paying_request_agrees
#print axioms Lime.PlannerWit.thePayingRequest_wallsAgree
#print axioms Lime.PlannerWit.the_paying_request_is_quiet
#print axioms Lime.PlannerWit.the_paying_request_is_plain
#print axioms Lime.PlannerWit.the_paying_request_pays_the_decoder
#print axioms Lime.PlannerWit.the_lift_applies_at_the_paying_request
#print axioms Lime.PlannerWit.plan_respects_the_energy_filter_as_stage_6_wrote_it_is_refuted
-- W-30 (track G): and the correction of W-29's own count -- "theBusyRequest is the only
-- request whose cursor fills a slot" is FALSE; 19 of this module's 43 requests assign, and
-- exactly one of the nineteen pays the fifth decoder clause (README gap 2025).
#print axioms Lime.PlannerWit.the_cursor_family_assigns_and_none_of_it_pays

-- ############################################################################
-- W-31 (track G): §6.1's ELEVEN off `hnoassign` -- the eleven-check lifts, the
-- `Goals.lean` entry that left by refute-and-rename, and the widened paying set.
-- ############################################################################
--
-- THE HYPOTHESIS THE ELEVEN-CHECK LIFTS CARRIED WAS ONE PROPERTY OF THE
-- ELIGIBILITY SPELLED AS A DOMAIN.  This line said SIX, the run brief said six and
-- the land block said seven; the population is TWELVE and nine of them still carry
-- the hypothesis (W-31 repair, README gap 2251, which stays OPEN because the number
-- is prose and no gate counts a CONCLUSION SHAPE).  MEASURED over comment-stripped
-- source, by the declarations whose conclusion is `planOk _ _ = true` and whose name
-- is `dayPlan_ok_*`, plus the bridge: nine carrying `r.assignedRows = []`, two free
-- (`dayPlan_ok_of_the_core_seven`, `dayPlan_ok_on_the_whole_day_of_a_paying_decoder`)
-- and `the_unassigned_eleven_is_an_instance_of_the_paying_eleven`, which carries it by
-- design.  An independent auditor's count and this one agree exactly.  `r.assignedRows = []` was being spent on
-- `batchDoesNotReachPast` (no Batch row exists) and on the two comparisons (every
-- work row is the reservation), and on nothing else -- `impossibleKept` never
-- needed it.  `FoldRowsAdmitNothing` is what those three actually want, and it is
-- W-27's shape: TWO facts establish it and they have nothing in common.
#print axioms Lime.PlanCheck.a_batch_row_of_the_day_is_the_folds
#print axioms Lime.PlanCheck.a_work_row_from_now_is_reserved_or_assigned
#print axioms Lime.PlanCheck.FoldRowsAdmitNothing_of_nothing_assigned
#print axioms Lime.PlanCheck.FoldRowsAdmitNothing_of_an_unfilled_anchor
#print axioms Lime.PlanCheck.batchDoesNotReachPast_of_a_fold_that_admits_nothing
#print axioms Lime.PlanCheck.eligibleSomewhere_of_nothing_from_now
-- The lifts themselves: the equality, the discharge, and §6.1's eleven on the whole
-- day of a request whose decoder pays -- with no `r.assignedRows = []` in any of them.
-- and the generality claim as a THEOREM rather than a doc comment (D5, 3.1 item 4).
#print axioms Lime.PlanCheck.the_unassigned_eleven_is_an_instance_of_the_paying_eleven
-- the two properties, audited the way `Lime.WfPlan` and `AssignedRowsPay` are (6.3).
#print axioms Lime.PlanCheck.FoldRowsAdmitNothing
#print axioms Lime.PlanCheck.UnfilledAnchored
-- Goals.plan_does_not_overbook LEFT `Goals.lean`: refuted at W-24, restated here.
-- The reason it could not leave then was that the restatement had no subject; P9's
-- rows are the subject (`the_overbooking_sum_has_a_subject_where_the_fold_filled_slots`).
#print axioms Lime.PlanCheck.plan_does_not_overbook_where_nothing_runs
#print axioms Lime.PlanCheck.plan_does_not_overbook_from_now_where_nothing_runs
-- W-31 (track G), the witness side: the fourth clause P5's eligibility owes the lift,
-- the ELEVEN fired at a day that ASSIGNS, and the census that prices it.
#print axioms Lime.PlannerWit.freeSlotRows_is_from_now_anchored
#print axioms Lime.PlannerWit.freeSlotRows_is_unfilled
#print axioms Lime.PlannerWit.the_free_slot_eligibility_reads_its_fourth_clause
#print axioms Lime.PlannerWit.the_eleven_applies_at_the_paying_request
#print axioms Lime.PlannerWit.the_eleven_at_the_paying_day_is_five_biting
-- The paying set, widened from ONE to THREE (W-30's own count was one of nineteen).
#print axioms Lime.PlannerWit.the_mirror_witness_loads
#print axioms Lime.PlannerWit.the_two_witness_loads
#print axioms Lime.PlannerWit.three_requests_now_assign_and_pay
#print axioms Lime.PlannerWit.the_mirrored_day_assigns_the_hot_item
#print axioms Lime.PlannerWit.the_new_paying_days_are_quiet_and_inside_the_budget
-- The overbooking law: the subject P9 gave it, and the two firings of the restatement.
#print axioms Lime.PlannerWit.the_overbooking_sum_has_a_subject_where_the_fold_filled_slots
#print axioms Lime.PlannerWit.the_over_budget_request_fails_the_checker_too
#print axioms Lime.PlannerWit.the_overbook_restatement_fires_on_a_worked_morning
#print axioms Lime.PlannerWit.the_overbook_restatement_fires_where_the_fold_filled_slots
-- AND THE MEASUREMENT THAT SAYS WHY THE WIND-DOWN GOAL DID NOT MOVE: this module
-- plans ONE INSTANT, so no day in it holds a WindDown row with a Block at or after
-- it, and the refutation that goal needs cannot be computed here (gap 2199).
#print axioms Lime.PlannerWit.the_witness_module_plans_one_instant
-- W-32 (track G): the burn-down of seven is ONE blocker counted seven times.
-- Goals.plan_never_drops_an_impossible_item LEFT `Goals.lean`: refuted here, at the
-- first request in this tree whose hypothesis is satisfiable at all.  Every candidate
-- of all 45 requests carried `due = none` before this one, so `Arith.isImpossible`
-- had never answered `true` about a request and the goal's hypothesis was empty.
#print axioms Lime.PlannerWit.the_first_impossible_candidate_this_tree_has_had
#print axioms Lime.PlannerWit.plan_never_drops_an_impossible_item_as_stage_6_wrote_it_is_refuted
-- Its restatement's subject WAS empty at every request and every eligibility, and that
-- theorem was ALREADY here -- PlanCheck.impossible_has_no_subject, audited above until W-33
-- refuted it.  A second copy of it was written and deleted in this run (AGENTS 5.3).
-- Filling the list `PlanCheck.impossibleKept` reads was P8's step (gap 2321); W-33 did it
-- (`Planner.PlanReq.dayImpossible`), and the list has a subject now.  (Rewritten in the W-33
-- repair, gap 2565: the merge patched one parenthesis and left the present tense.)
-- Goals.plan_puts_hot_before_the_queue, refuted a THIRD time -- this time at a day the
-- fold FILLED, at a request that PAYS, with W-20's own repair (`sj` is a work row)
-- already in the statement.  The two earlier refutations both blamed the unwritten
-- fold; P9 wrote it and the law is still false.
#print axioms Lime.PlannerWit.the_paying_day_carries_the_queue_and_never_the_hot_item
#print axioms Lime.PlannerWit.plan_puts_hot_before_the_queue_is_refuted_at_a_day_that_assigns_and_pays
-- GAP 365 PRICED: §6.1's `hot` check is false where it has a subject and empty where it
-- is proved, and which of the two is decided by the eligibility alone.
#print axioms Lime.PlannerWit.the_hot_check_is_false_where_it_has_a_subject_and_empty_where_it_is_proved
-- The paying set, widened from THREE to FOUR, along the axis `Planner.edfNumbers` is
-- about; and the four checks the remaining single-run goals restate, measured empty on
-- every one of the four days that assign and pay.
#print axioms Lime.PlannerWit.four_requests_now_assign_and_pay
#print axioms Lime.PlannerWit.the_three_empty_checks_are_empty_at_every_day_that_assigns_and_pays
#print axioms Lime.PlannerWit.the_batch_rows_this_tree_builds_belong_to_no_store
-- Gap 2199's route to the wind-down refutation does not exist: no row §8.2 step 5
-- places starts inside the evening, so `PlanCheck.AssignedRowsPay`'s second clause has
-- an unsatisfiable antecedent on any day inside the horizon.  `no_slot_reaches_the_evening`
-- has said the slot half since P3; this is the step onto the ROWS that nobody had taken.
#print axioms Lime.PlannerWit.an_assigned_row_starts_outside_the_evening
#print axioms Lime.PlannerWit.an_assigned_row_inside_the_horizon_is_before_the_wind_down
-- W-32 (track G) §29: the BATCH check's FIRST SUBJECT, and design §6.3's own `loc:` skip
-- refuting two goals at one day that assigns and pays.  Gap 2194 asked for a paying
-- request whose group has two members; the reason none existed was the STORE, not the
-- fold -- `the_batch_rows_this_tree_builds_belong_to_no_store` above is that measured.
#print axioms Lime.PlannerWit.the_batch_store_witness_loads
#print axioms Lime.PlannerWit.the_batch_store_holds_three_siblings_at_one_ci
#print axioms Lime.PlannerWit.the_two_batch_requests_assign_and_pay
#print axioms Lime.PlannerWit.the_skipped_day_batches_past_the_sibling_that_ranks_ahead
#print axioms Lime.PlannerWit.plan_never_batches_past_an_equal_ci_candidate_is_refuted_at_a_paying_day
-- and the same day refutes the rank law, which W-19 could only refute by pointing at a
-- fold that did not exist yet.  P9 wrote it and the law is still false.
#print axioms Lime.PlannerWit.plan_is_monotone_in_rank_is_refuted_at_a_paying_day
-- the paying set: FOUR at §28, SIX here.
#print axioms Lime.PlannerWit.the_paying_set_is_six_and_the_batch_check_has_a_subject

-- ===================================================================
-- APPENDED 2026-09-25: stage 6, W-33, track P (AGENTS §6.3).
-- `Diagnostics.impossible` IS WRITTEN -- P8's first half (README gaps 2321,
-- 2419; gap 2403 moves from three of twelve fields to TEN).
-- `Planner.PlanReq.dayImpossible` names every ANSWER whose own reported
-- shortfall is positive (`Look.FloorOut.shortfall`), floored to minutes:
-- exactly the shipped binary's `Prio::is_impossible` as `prio_of` reads the
-- capacity op's grant (D53) -- a HOT floor that falls short included, a grant
-- that is impossible only through R1's ceiling while its bin is not HOT
-- excluded.  D34: the day reports its own section-7 answer; nothing derived.
-- `hot`, `waiting`, `blocked`, `droppedTail`, `underused`, `planHonesty` are
-- filled the same way; `deferred` and `restDebtMin` stay empty (gap 2511).
--
-- FOUR THEOREMS DESCRIBED THE HOLE AND ARE DELETED ABOVE, each refuted by
-- computation in PlannerWit section 30.  FIVE lifts are RENAMED WITH THEIR
-- THEOREMS above: four at every eligibility carry `hnoimp`, and the census
-- ceiling of seven carries it too; the unconditional ceiling is EIGHT.
--
-- THE FINDING: at `slotFitRows` -- step 5's own energy clause at the rows it
-- filled -- `impossibleKept` is FALSE at a day that PAYS with the other ten
-- true: two impossible items contend for one day and the second, which fits
-- every slot, gets none.  Gap 2510 is the owner question.  No goal is
-- discharged; the burn-down stays 6.
-- ===================================================================
#print axioms Lime.Planner.PlanReq.dayImpossible_capped
#print axioms Lime.Planner.PlanReq.mem_dayImpossible
#print axioms Lime.Planner.PlanReq.a_granted_answer
#print axioms Lime.Planner.PlanReq.a_named_grant_is_impossible_at_a_hot_bin
#print axioms Lime.Planner.PlanReq.an_impossible_grant_at_a_hot_bin_is_short
#print axioms Lime.Planner.PlanReq.a_named_answer_without_a_grant_is_a_short_floor
#print axioms Lime.Planner.PlanReq.answerFor_of_mem
#print axioms Lime.Planner.the_day_names_every_item_whose_numbers_say_impossible_at_a_hot_bin
#print axioms Lime.Planner.an_item_the_day_names_with_a_grant_has_impossible_numbers
#print axioms Lime.Planner.eraseDups_length_le
#print axioms Lime.Planner.PlanReq.dayHot_capped
#print axioms Lime.Planner.PlanReq.dayWaiting_capped
#print axioms Lime.Planner.PlanReq.dayBlocked_capped
#print axioms Lime.Planner.PlanReq.mem_dayHot
#print axioms Lime.Planner.PlanReq.mem_dayWaiting
#print axioms Lime.Planner.PlanReq.mem_dayBlocked
#print axioms Lime.Planner.dayDiagnostics_impossible
#print axioms Lime.Planner.dayDiagnostics_hot
#print axioms Lime.Planner.dayDiagnostics_waiting
#print axioms Lime.Planner.dayDiagnostics_blocked
#print axioms Lime.Planner.dayDiagnostics_droppedTail
#print axioms Lime.Planner.dayDiagnostics_underused
#print axioms Lime.Planner.dayDiagnostics_planHonesty
#print axioms Lime.Planner.dayPlan_impossible
#print axioms Lime.Planner.dayPlan_hot
#print axioms Lime.PlanCheck.impossibleKept_of_no_eligible_impossible_item
#print axioms Lime.PlanCheck.impossibleKept_of_nothing_assigned_iff
#print axioms Lime.PlanCheck.impossible_subject_iff
#print axioms Lime.PlanCheck.impossible_has_a_subject_iff_an_owed_impossible_answer_is_eligible_with_budget_left
#print axioms Lime.PlanCheck.the_census_ceiling_is_eight_on_an_unassigned_day
#print axioms Lime.PlannerWit.the_day_names_its_first_impossible_item
#print axioms Lime.PlannerWit.the_day_names_no_impossible_item_is_refuted
#print axioms Lime.PlannerWit.the_impossible_check_passes_where_the_grant_holds_nothing_and_is_empty_where_it_is_proved
#print axioms Lime.PlannerWit.impossible_has_no_subject_is_refuted
#print axioms Lime.PlannerWit.impossible_has_no_subject_from_now_is_refuted
#print axioms Lime.PlannerWit.theUnassignedImpossibleRequest_wallsAgree
#print axioms Lime.PlannerWit.the_unassigned_impossible_request_agrees
#print axioms Lime.PlannerWit.dayPlan_ok_on_a_quiet_unassigned_day_except_hot_as_W_20_wrote_it_is_refuted
#print axioms Lime.PlannerWit.theQuietImpossibleRequest_wallsAgree
#print axioms Lime.PlannerWit.dayPlan_ok_on_a_quiet_unassigned_day_given_hot_as_W_20_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_overlap_witness_loads
#print axioms Lime.PlannerWit.the_day_names_its_overlapping_walls
#print axioms Lime.PlannerWit.the_impossible_check_over_the_paying_set
#print axioms Lime.PlannerWit.the_planner_drops_an_impossible_item_its_own_energy_clause_admits
#print axioms Lime.PlannerWit.the_day_names_an_impossible_floor
#print axioms Lime.PlannerWit.the_impossible_request_fills_five_diagnostic_fields
#print axioms Lime.PlannerWit.the_day_names_its_waiting_and_blocked_candidates
#print axioms Lime.PlannerWit.eraseDups_keeps_the_first_where_dedupIds_keeps_the_last
#print axioms Lime.PlannerWit.the_energy_clause_separates_the_energy_drop_from_the_contention_drop

-- ===========================================================================
-- APPENDED 2026-09-25: stage 6 (the planner), run W-34, track H — P8's
-- emitter, the plan hash (README "Stage 6 — W-34, track H").
--
-- `Planner.planDigest` is fork `DayPlan::hash` ported byte for byte, and
-- `Planner.dayPlan` carries it.  The tripwire P0 left for this step,
-- the_plan_hash_is_a_placeholder_until_the_emitter_lands, is DELETED from
-- `Planner.lean` and from this file: it is refuted by
-- `PlannerWit.the_plan_hash_is_a_placeholder_until_the_emitter_lands_is_refuted`
-- and renamed to what the day carries, `Planner.dayPlan_planHash` (AGENTS
-- §3.2).  PlanWire.hashHex_reads_back was the round trip at every digest (`PlanWire.hashHex_digits_read_back` since
-- the W-47 repair).
-- ===========================================================================
#print axioms Lime.Planner.fnvFold_lt
#print axioms Lime.Planner.fnv1a_lt
#print axioms Lime.Planner.fnv1a_test_vectors
#print axioms Lime.Planner.dayPlan_planHash
#print axioms Lime.Planner.dayPlan_planHash_is_a_function_of_the_rows
#print axioms Lime.Planner.placementText_ignores_the_marks_and_the_note
#print axioms Lime.Planner.instantText_is_renderStamp_off_utc
#print axioms Lime.Planner.instantText_spells_chrono
#print axioms Lime.Planner.multText_is_zmijs
#print axioms Lime.Planner.the_placement_bytes_are_the_forks
#print axioms Lime.PlanWire.hexFold_digits
#print axioms Lime.PlannerWit.the_witness_days_hash_is_the_forks
#print axioms Lime.PlannerWit.the_plan_hash_is_a_placeholder_until_the_emitter_lands_is_refuted

-- ===========================================================================
-- APPENDED 2026-09-26: stage 6, run W-34, track H — step 8's last two fields,
-- the one reading of `ineligible_reason`, and the two caps (README gaps 2511,
-- 555, 2573, 2576; README "Stage 6 — W-34, track H").
--
-- `Planner.dayDiagnostics` writes all twelve fields: `deferred` over
-- `PlanReq.rawSlots` (the flat posterior, gap 555) and `restDebtMin` over the
-- day record's breaks.  W-33's tripwire
-- the_day_leaves_two_diagnostic_fields_empty is DELETED from `Planner.lean`
-- and from this file: refuted by
-- `PlannerWit.the_day_leaves_two_diagnostic_fields_empty_is_refuted` and
-- renamed `Planner.dayDiagnostics_deferred` / `…_restDebtMin`.
-- `Look.PlanFacts.eligible` is `ineligibleReason`'s `none` case and
-- `PlanReq.dayBlocked` its `blocked` case (gap 2573; `mem_dayBlocked` and
-- `eligible_iff` re-proved with their statements unchanged, D5).
-- ===========================================================================
#print axioms Lime.Look.PlanFacts.ineligibleReason_blocked_iff
#print axioms Lime.Look.PlanFacts.eligible_is_the_four_conjuncts
#print axioms Lime.Planner.PlanReq.dayDeferred_capped
#print axioms Lime.Planner.dayDiagnostics_deferred
#print axioms Lime.Planner.dayDiagnostics_restDebtMin
#print axioms Lime.Planner.PlanReq.the_raw_and_energised_slots_are_the_same_slots
#print axioms Lime.Planner.PlanReq.mem_dayDeferred
#print axioms Lime.Planner.PlanReq.dayRestDebtMin_is_the_sum_of_the_shortfalls
#print axioms Lime.Planner.nodup_eraseDups
#print axioms Lime.Planner.PlanReq.dayDroppedTail_capped
#print axioms Lime.Planner.dayDiagnostics_droppedTail_whole
#print axioms Lime.Planner.length_flatMap_le_mul
#print axioms Lime.Planner.segItems_length_le
#print axioms Lime.Planner.PlanReq.dayUnderused_length_le
#print axioms Lime.Planner.dayDiagnostics_underused_whole_below_the_cap
#print axioms Lime.PlannerWit.restRun_resumes_ok
#print axioms Lime.PlannerWit.the_day_owes_the_rest_its_log_cut_short
#print axioms Lime.PlannerWit.the_day_names_what_the_posterior_cost_a_slot
#print axioms Lime.PlannerWit.the_day_leaves_two_diagnostic_fields_empty_is_refuted
#print axioms Lime.PlannerWit.the_underused_list_names_an_item_once_per_slot
#print axioms Lime.PlannerWit.the_underused_list_holds_each_candidate_once_is_refuted

-- APPENDED 2026-09-26 (stage 6, run W-34, track D; README gaps 2680-2719): fork
-- `open_block_segment` composed into `Planner.dayRows` through `replayedRows` (gaps 554, 2519),
-- the laws W-34 restated over the log's whole replayed past, the refutation of each old form at
-- the open requests, fork `planner::diff` and `overtime_drops` (`PlanDiff.lean`, a new module,
-- imported in `LimeKernel.lean` in the same commit), and the `planner` section's `overtime` key.
-- Restated in place and already audited under their own names: `Planner.a_block_row_is_replayed
-- _reserved_or_assigned`, `PlanWire.runPlanner_answers_the_day` and every `PlanCheck` lift whose
-- `hnopast`/`PastPays` now ranges over `Planner.replayedRows`.
#print axioms Lime.Planner.openClip_le
#print axioms Lime.Planner.openClip_le_start
#print axioms Lime.Planner.PlanReq.openStop_le
#print axioms Lime.Planner.mem_openBlockRows
#print axioms Lime.Planner.openBlockRows_end_at_now
#print axioms Lime.Planner.openBlockRows_are_energyless_blocks
#print axioms Lime.Planner.the_open_row_is_current_exactly_when_nothing_is_reserved_or_interrupted
#print axioms Lime.Planner.the_open_row_stops_where_a_later_interruption_starts
#print axioms Lime.Planner.the_open_row_is_the_logs_open_block
#print axioms Lime.Planner.openBlockRows_length_le_one
#print axioms Lime.Planner.openBlockRows_of_an_open_block
#print axioms Lime.Planner.mem_replayedRows
#print axioms Lime.Planner.replayedRows_end_at_now
#print axioms Lime.Planner.replayedRows_are_not_walls
#print axioms Lime.Planner.replayedRows_are_not_wind_down
#print axioms Lime.Planner.pastRows_carry_no_energy
#print axioms Lime.Planner.pastRows_are_not_batches
#print axioms Lime.Planner.replayedRows_carry_no_energy
#print axioms Lime.Planner.replayedRows_are_not_batches
#print axioms Lime.Planner.the_open_row_is_a_row_of_the_day
#print axioms Lime.Planner.the_open_rows_item_is_assigned
#print axioms Lime.PlanCheck.dayPlan_block_rows_are_open_reserved_or_assigned
#print axioms Lime.Planner.mem_diffIds
#print axioms Lime.Planner.diffIds_sorted
#print axioms Lime.Planner.firstStart_eq_none_iff
#print axioms Lime.Planner.firstStart_spec
#print axioms Lime.Planner.mem_diff_removed
#print axioms Lime.Planner.mem_diff_added
#print axioms Lime.Planner.mem_diff_moved
#print axioms Lime.Planner.an_item_that_keeps_its_first_start_is_not_moved
#print axioms Lime.Planner.diff_removed_and_added_are_disjoint
#print axioms Lime.Planner.a_moved_item_is_neither_removed_nor_added
#print axioms Lime.Planner.diff_removed_sorted
#print axioms Lime.Planner.diff_added_sorted
#print axioms Lime.Planner.diff_driftMin_is_the_moved_minutes
#print axioms Lime.Planner.diff_self
#print axioms Lime.Planner.the_extension_moves_only_the_running_estimate_and_the_overrides
#print axioms Lime.Planner.the_extension_grows_the_running_estimate
#print axioms Lime.Planner.the_extension_leaves_another_items_block
#print axioms Lime.Planner.the_extension_is_one_extra_override
#print axioms Lime.Planner.mem_overtime_drops
#print axioms Lime.Planner.overtime_drops_ascend_in_id_order
#print axioms Lime.Planner.overtimeDiff_of_an_unchanged_day
#print axioms Lime.PlanWire.runPlanner_answers_the_day_without_an_overtime
#print axioms Lime.PlanWire.runPlanner_refuses_an_overtime_the_decoder_refuses
#print axioms Lime.PlanWire.readOvertime_of_an_absent_key
#print axioms Lime.PlanWire.readOvertime_accepts_an_extension
#print axioms Lime.PlanWire.readOvertime_refuses_blocks_past_the_width
#print axioms Lime.PlanWire.readOvertime_refuses_a_missing_id
#print axioms Lime.PlanWire.readOvertime_refuses_a_long_id
#print axioms Lime.PlanWire.the_overtime_refusal_spells_itself
#print axioms Lime.PlanWire.overtimeJson_of_none
#print axioms Lime.PlanWire.overtimeJson_answers_the_what_if
#print axioms Lime.PlanWire.diffJson_writes_every_field
#print axioms Lime.PlanWire.the_overtime_keys_removed_is_overtime_drops
#print axioms Lime.PlanWire.noteJson_writes_so_far
#print axioms Lime.PlannerWit.openRun_resumes_ok
#print axioms Lime.PlannerWit.openBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_open_day_is_the_worked_stretch_the_wall_and_the_reservation
#print axioms Lime.PlannerWit.the_open_row_carries_the_forks_marks
#print axioms Lime.PlannerWit.the_open_row_stops_at_the_interruption
#print axioms Lime.PlannerWit.the_open_requests_agree
#print axioms Lime.PlannerWit.the_battery_bites_on_the_open_row
#print axioms Lime.PlannerWit.theOpenRow_is_the_open_row
#print axioms Lime.PlannerWit.a_block_row_is_replayed_reserved_or_assigned_over_the_closed_rows_is_refuted
#print axioms Lime.PlannerWit.dayPlan_ok_core_given_the_budget_over_the_closed_rows_is_refuted
#print axioms Lime.PlannerWit.the_paying_past_lift_over_the_closed_rows_is_refuted
#print axioms Lime.PlannerWit.noBlockOverABreak_of_a_logless_day_over_the_closed_rows_is_refuted
#print axioms Lime.PlannerWit.the_quiet_day_laws_over_the_closed_rows_are_refuted
#print axioms Lime.PlannerWit.the_whole_day_lifts_over_the_closed_rows_are_refuted
#print axioms Lime.PlannerWit.the_diff_of_two_written_days
#print axioms Lime.PlannerWit.the_overtime_what_if_moves_the_tail
#print axioms Lime.Planner.openWorkedMin_is_the_banked_minutes_and_the_running_stretch
#print axioms Lime.Planner.diffRow_reads_every_kind_but_rest_and_break
#print axioms Lime.PlannerWit.the_block_row_laws_over_the_closed_rows_are_refuted
#print axioms Lime.PlannerWit.the_logless_day_checks_over_the_closed_rows_are_refuted
#print axioms Lime.PlannerWit.the_remaining_lifts_over_the_closed_rows_are_refuted
#print axioms Lime.PlannerWit.openEarlyRun_resumes_ok
#print axioms Lime.PlannerWit.PastPays_of_no_past_block_over_the_closed_rows_is_refuted
#print axioms Lime.PlannerWit.the_paying_past_lifts_over_the_closed_rows_are_refuted

-- APPENDED 2026-09-26 (stage 6, run W-34, land step; README gaps 2720-2729): the witness
-- check 9's second pass asked for when the merge moved `Planner.serdeInstance`'s pin site.
#print axioms Lime.PlannerWit.the_instance_key_is_spelled_as_serde_tags_it

-- APPENDED 2026-09-26 (stage 6, run W-34, repair step; README gaps 2730-2769): the what-if's
-- domain, both directions (gap 2737), and the refutation of `planJson`'s pre-W-34 form (gap 2739).
#print axioms Lime.PlannerWit.planJson_of_a_planned_day_emits_the_zero_hash_is_refuted

-- APPENDED 2026-09-26 (stage 6, run W-35, track K; README gaps 2800-2839): D55 -- an impossible
-- item is owed what ITS OWN GRANT holds.  Three audit lines above were RENAMED in place with the
-- theorems they audit; the renamed-from forms are refuted in `PlannerWit.lean`'s W-35 block.
#print axioms Lime.PlanCheck.owedByItsGrant_eq_false_iff
#print axioms Lime.PlannerWit.an_unassigned_day_that_drops_an_item_its_grant_holds_nothing_for_passes
#print axioms Lime.PlannerWit.an_eligible_impossible_item_fails_the_check_where_nothing_is_assigned_is_refuted
#print axioms Lime.PlannerWit.impossible_has_a_subject_iff_an_impossible_answer_is_eligible_is_refuted
#print axioms Lime.PlannerWit.the_restated_check_bites_on_a_planted_drop_of_an_owed_item
#print axioms Lime.PlannerWit.the_reversed_day_serves_the_earlier_due_impossible_item_first

/- ================================================================================
   APPENDED 2026-09-26: W-35 track K, D57 -- the running break (P45), overtime (P46) and
   a wall on `now` (P47).  Planner.a_break_row_is_a_replayed_row is refuted and renamed
   in place above; PlanCheck.a_block_row_from_now_clears_a_break_row is restated under
   its own name, its audit line unchanged.
   ================================================================================ -/
#print axioms Lime.Planner.breakRows_are_running_breaks
#print axioms Lime.Planner.a_running_break_is_blocked
#print axioms Lime.Planner.a_running_break_pauses_the_block
#print axioms Lime.Planner.breakRows_are_not_work
#print axioms Lime.Planner.PlanReq.the_reservation_clears_a_blocked_span
#print axioms Lime.Planner.PlanReq.a_slot_clears_a_blocked_span
#print axioms Lime.Planner.a_block_row_clears_the_running_break
#print axioms Lime.Planner.a_block_row_from_now_clears_the_running_break
#print axioms Lime.Planner.the_open_row_stops_where_the_running_break_starts
#print axioms Lime.Planner.PlanReq.activeStop_in_overtime
#print axioms Lime.Planner.PlanReq.activeStop_before_overtime
#print axioms Lime.Planner.a_wall_on_now_pauses_the_block
#print axioms Lime.Planner.the_open_row_stops_where_a_wall_on_now_starts
#print axioms Lime.Planner.the_open_row_is_not_current_under_a_wall_on_now
#print axioms Lime.PlanWire.placeOf_reads_the_word
#print axioms Lime.PlannerWit.the_running_break_is_drawn_and_nothing_is_scheduled_over_it
#print axioms Lime.PlannerWit.an_overrun_break_is_open_and_the_next_block_starts_now
#print axioms Lime.PlannerWit.in_overtime_the_running_block_stays_current
#print axioms Lime.PlannerWit.a_wall_on_now_pauses_the_running_block
#print axioms Lime.PlannerWit.a_break_row_is_a_replayed_row_is_refuted
#print axioms Lime.PlannerWit.a_block_row_from_now_clears_a_break_row_as_W_30_wrote_it_is_refuted

-- APPENDED 2026-09-26 (stage 6, run W-35, track E; README gaps 2840-2869): D56's slot-reading
-- est setter and its laws (gap 2572), the est op's value-as-written form, and the fork's three
-- whole diagnostic tuples with their projection laws (gaps 2640, 2743).
#print axioms Lime.Field.kEst_classifyWord
#print axioms Lime.Field.findSome_kEst_phase3
#print axioms Lime.Field.findSome_kEst_phase2
#print axioms Lime.Field.estLeadOf_bare
#print axioms Lime.Field.boxed_of_estLeadOf
#print axioms Lime.Field.estLeadOf_setLead
#print axioms Lime.Field.setLeadToks_seps
#print axioms Lime.Field.mem_setLeadToks
#print axioms Lime.Field.renderDur_head
#print axioms Lime.Field.keyOf_renderDur
#print axioms Lime.Field.isIdWord_of_digit_head
#print axioms Lime.Field.isIdWord_renderDur
#print axioms Lime.Field.isIdWord_of_estSlot
#print axioms Lime.Field.lookupKey_none_of_no_keyTok
#print axioms Lime.Field.hasKeyTok_setLead
#print axioms Lime.Field.view_set_remaining_slot
#print axioms Lime.Field.setRemaining_writes_no_key_over_a_leading_estimate
#print axioms Lime.Field.setRemaining_boxed
#print axioms Lime.Field.toksWf_head_word
#print axioms Lime.Field.toksWf_setLeadToks
#print axioms Lime.Field.idWords_setLeadToks
#print axioms Lime.Field.setLead_canonical_box_ended
#print axioms Lime.Field.setRemaining_canonical
#print axioms Lime.Field.setRemaining_line_reparses
#print axioms Lime.Field.the_leading_estimate_is_rewritten_in_place
#print axioms Lime.Field.a_line_without_a_leading_estimate_gets_the_key
#print axioms Lime.setEstE_rewrites_the_leading_estimate
#print axioms Lime.setVal_writes_the_token_the_loader_reads_is_refuted
#print axioms Lime.setVal_writes_the_token_the_loader_reads_unless_it_rewrites_the_leading_estimate
#print axioms Lime.setVal_est_rewrites_the_leading_estimate
#print axioms Lime.the_edit_path_writes_the_minutes_it_was_given
#print axioms Lime.parseCmd_reads_the_est_value_as_written
#print axioms Lime.parseCmd_refuses_est_value_variants
#print axioms Lime.Planner.PlanReq.a_short_answer_has_an_until
#print axioms Lime.Planner.PlanReq.dayImpossible_is_the_projection
#print axioms Lime.Planner.PlanReq.dayImpossibleUntil_capped
#print axioms Lime.Planner.PlanReq.dayUnderused_is_the_projection
#print axioms Lime.Planner.PlanReq.dayBlocked_is_the_projection
#print axioms Lime.Planner.PlanReq.dayBlockedDeps_capped
#print axioms Lime.Planner.dayDiagnostics_impossibleUntil
#print axioms Lime.Planner.dayDiagnostics_impossible_is_the_projection
#print axioms Lime.Planner.dayDiagnostics_blockedDeps
#print axioms Lime.Planner.dayDiagnostics_blocked_is_the_projection
#print axioms Lime.Planner.dayDiagnostics_underused_is_the_projection
#print axioms Lime.PlannerWit.the_day_names_its_first_impossible_item_with_its_date
#print axioms Lime.PlannerWit.the_day_names_its_underused_slot_with_its_levels
#print axioms Lime.PlannerWit.the_day_names_its_blocked_candidate_with_its_deps
#print axioms Lime.PlanWire.the_seam_carries_the_run_it_was_given_exactly_when_asked
#print axioms Lime.runCapP_without_a_capacity_section_hands_out_no_parts
#print axioms Lime.PlanWire.batchOf_is_the_batchs_ids
#print axioms Lime.PlanWire.respondPlanner_answers_an_empty_request
#print axioms Lime.PlanWire.callPlanner_is_the_emitted_answer
#print axioms Lime.EditVal.rendered_is_the_tokens_bytes
-- APPENDED 2026-09-27 (stage 6, run W-36, track K; README gaps 3000-3039): D60 -- IMPOSSIBLE
-- ties at p = 0 by due date (parity P51) -- and D59 -- never dropped while the day's budget can
-- still be spent.  Three lines above were RENAMED in place with the theorems they audit (W-36):
-- PlanCheck's failure law and subject law gained the budget clause (their W-35 forms are refuted
-- in PlannerWit's W-36 block), and PlannerWit's reversed-day witness states the D60 day.
#print axioms Lime.Planner.rankedLe_notWall
#print axioms Lime.Planner.rankedLe_p
#print axioms Lime.Planner.natsLe_append_same
#print axioms Lime.Planner.natsLe_of_append
#print axioms Lime.Planner.Ranked.imp_eq_some_iff
#print axioms Lime.Planner.Ranked.imp_isSome
#print axioms Lime.Planner.impNums_le_some
#print axioms Lime.Planner.rankedLe_impossible_by_until
#print axioms Lime.Planner.rankedLe_is_the_forks_off_the_impossible
#print axioms Lime.Planner.PlanReq.an_earlier_due_impossible_item_ranks_first
#print axioms Lime.Planner.minGroupKey_mem
#print axioms Lime.Planner.PlanReq.a_group_key_is_a_members
#print axioms Lime.Planner.PlanReq.an_earlier_due_impossible_group_is_walked_first
#print axioms Lime.PlannerWit.the_reversed_day_drops_the_impossible_item_its_grant_owes_is_refuted
#print axioms Lime.PlannerWit.a_spent_day_passes_the_impossible_check
#print axioms Lime.PlannerWit.an_eligible_impossible_item_its_grant_owes_fails_the_check_where_nothing_is_assigned_is_refuted
#print axioms Lime.PlannerWit.impossible_has_a_subject_iff_an_owed_impossible_answer_is_eligible_is_refuted
#print axioms Lime.PlannerWit.impossibleKept_can_fail_as_W_35_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_atomic_day_drops_the_impossible_item_its_grant_owes_today
-- W-36 track K, gap 2873 (D58's kernel half): the what-if reads the host's grown facts.
#print axioms Lime.Planner.mkGrown?_refuses_a_remaining_past_the_width
#print axioms Lime.Planner.mkGrown?_refuses_planned_minutes_past_the_width
#print axioms Lime.Planner.mkGrown?_accepts
#print axioms Lime.Planner.planFacts_wf_with_plannedMin
#print axioms Lime.Planner.growCand_remaining
#print axioms Lime.Planner.growCand_plannedMin
#print axioms Lime.Planner.growCand_keeps
#print axioms Lime.Planner.PlanReq.growing_none
#print axioms Lime.Planner.PlanReq.growing_touches_only_the_candidates
#print axioms Lime.Planner.PlanReq.mem_growing
#print axioms Lime.PlanWire.readGrown_of_an_absent_key
#print axioms Lime.PlanWire.readGrown_accepts_the_hosts_facts
#print axioms Lime.PlanWire.readGrown_refuses_a_remaining_past_the_width
#print axioms Lime.PlanWire.readGrown_refuses_planned_minutes_past_the_width
#print axioms Lime.PlanWire.readGrown_refuses_a_grown_that_is_not_an_object
#print axioms Lime.PlanWire.readOvertime_carries_the_grown_facts
#print axioms Lime.PlanWire.the_grown_refusals_spell_themselves
#print axioms Lime.PlanWire.readGrown_refuses_a_grown_carried_twice
#print axioms Lime.PlanWire.mkGrown?_accepts_what_the_width_reads_pass
#print axioms Lime.PlannerWit.the_hosts_grown_facts_reach_the_what_if
-- W-36 track K, D40 (README gap 3008): the group walk's sort, which nothing pinned until this step.
#print axioms Lime.PlannerWit.the_group_walk_is_sorted_where_a_split_bucket_ranks_late

-- =====================================================================
-- APPENDED 2026-09-27: stage 6 W-36 TRACK T (worktree `w36-t`) -- README gap 2929: an
-- estimate's value has ONE reader on the wire, bounded by `Look.maxPlanMinutes`.
-- =====================================================================
#print axioms Lime.parseCmd_refuses_an_estimate_past_the_hosts_width
#print axioms Lime.parseCmd_reads_an_estimate_at_the_hosts_width
#print axioms Lime.the_keyed_est_edit_reads_as_the_est_op

-- =====================================================================
-- APPENDED 2026-09-27: stage 6 W-36 TRACK T (worktree `w36-t`) -- README gap 2920 (the planner
-- READS the host's worked minutes, `RuntimeIn.worked`, parity P55) and the owner's D61 (a logged
-- wall pause is no worked time, parity P53).
-- =====================================================================
#print axioms Lime.Planner.a_worked_reading_within_a_day_is_read
#print axioms Lime.Planner.PlanReq.activeWorked_is_the_hosts
#print axioms Lime.Planner.PlanReq.activeWorked_without_the_hosts
#print axioms Lime.Planner.the_open_row_reads_the_running_blocks_worked_minutes
#print axioms Lime.Planner.the_open_row_reads_the_hosts_worked_minutes
#print axioms Lime.Planner.a_logged_wall_pause_is_no_worked_time
#print axioms Lime.Planner.an_unlogged_wall_is_worked_time
#print axioms Lime.PlanWire.readState_reads_the_hosts_worked_minutes
#print axioms Lime.PlanWire.planKey_workedMin_is_the_wire_key
#print axioms Lime.PlannerWit.openWallRun_resumes_ok
#print axioms Lime.PlannerWit.a_logged_wall_pause_keeps_the_open_row_off_the_meeting
#print axioms Lime.PlannerWit.the_host_reading_is_the_one_reading
#print axioms Lime.PlannerWit.the_open_row_carries_the_logs_worked_minutes_is_refuted

-- APPENDED 2026-09-28: stage 6 W-36 REPAIR -- README gap 3130: `PlanCheck.budgetLeft` counts
-- only the rows a dropped impossible item could not have displaced, so a budget spent on work it
-- outranks no longer excuses its drop; gap 3137: the capacity answer's `until` is
-- `Planner.answerUntil`'s.
#print axioms Lime.PlannerWit.the_budget_spent_on_work_an_owed_impossible_item_outranks_does_not_excuse_its_drop
#print axioms Lime.PlannerWit.a_budget_spent_where_the_item_could_not_go_excuses_its_drop
#print axioms Lime.PlanWire.the_wire_until_is_answerUntil

-- =====================================================================
-- APPENDED 2026-09-28: stage 6 W-37 TRACK T (worktree `w37-t`) -- the owner's D65 (parity P56,
-- README gaps 3044, 3141, 3142): a meeting that paused the running block is drawn as the WALL
-- ALONE -- the part of a paused row a wall of the day covers is cut out of the replayed past.
-- =====================================================================
#print axioms Lime.Planner.mem_pastRows
#print axioms Lime.Planner.cutOne_sub
#print axioms Lime.Planner.cutOne_nonempty
#print axioms Lime.Planner.cutOne_apart
#print axioms Lime.Planner.cutOne_untouched
#print axioms Lime.Planner.cutAll_sub
#print axioms Lime.Planner.cutAll_nonempty
#print axioms Lime.Planner.cutAll_apart
#print axioms Lime.Planner.cutAll_untouched
#print axioms Lime.Planner.clipCut_within
#print axioms Lime.Planner.clipCut_apart
#print axioms Lime.Planner.clipCut_nil
#print axioms Lime.Planner.clipCut_untouched
#print axioms Lime.Planner.the_cut_is_run
#print axioms Lime.Planner.pastSpans_of_not_a_pause
#print axioms Lime.Planner.a_paused_row_lies_under_no_wall
#print axioms Lime.Planner.a_pause_no_wall_touches_is_drawn_whole
#print axioms Lime.PlannerWit.openStraddleRun_resumes_ok
#print axioms Lime.PlannerWit.the_meeting_is_drawn_as_a_paused_lost_row_is_refuted
#print axioms Lime.PlannerWit.the_meeting_is_drawn_as_the_wall_alone
#print axioms Lime.PlannerWit.a_pause_that_straddles_a_wall_keeps_its_minutes_outside_it

-- =====================================================================
-- APPENDED 2026-09-28: stage 6 W-37 TRACK T (worktree `w37-t`) -- README gap 3139: D61 decided
-- by the kernel (`WallTimer.lean`, the `emit` section's walls form) and the campaign's D66 call on
-- gap 3048 (`WallTimer.pausedFor`, the meeting `lime pause` names when it resumes).
-- =====================================================================
#print axioms Lime.WallTimer.inst_le
#print axioms Lime.WallTimer.inst_lt
#print axioms Lime.WallTimer.hasUnpause_none_of_untouched
#print axioms Lime.WallTimer.lastIsPauseAt_append
#print axioms Lime.WallTimer.step_of_running
#print axioms Lime.WallTimer.a_wall_that_starts_while_a_block_runs_stops_its_timer
#print axioms Lime.WallTimer.a_wall_that_has_not_begun_writes_nothing
#print axioms Lime.WallTimer.a_timer_already_stopped_at_the_wall_is_left_alone
#print axioms Lime.WallTimer.a_timer_mark_after_the_walls_start_stands
#print axioms Lime.WallTimer.the_walls_end_restarts_the_timer_it_stopped
#print axioms Lime.WallTimer.a_user_who_resumed_during_the_meeting_keeps_their_timer
#print axioms Lime.WallTimer.step_written
#print axioms Lime.WallTimer.mem_writes
#print axioms Lime.WallTimer.after_one_wall_a_second_verb_writes_nothing_more
#print axioms Lime.WallTimer.pausedFor_is_a_meeting_the_timer_is_paused_for
#print axioms Lime.WallTimer.answer_without_an_open_block
#print axioms Lime.WallTimer.answer_refuses_commands
#print axioms Lime.WallTimer.answer_refuses_without_the_replay
#print axioms Lime.WallTimer.answer_congr_ix
#print axioms Lime.WallTimer.the_walls_refusals_spell_themselves
#print axioms Lime.WallTimer.the_rule_is_run
#print axioms Lime.WallTimer.pausedFor_is_run
#print axioms Lime.WallTimer.spansOf_is_run
#print axioms Lime.WallTimer.readReq_is_run
#print axioms Lime.WallTimer.the_walls_refusal_is_the_err_emit_shape
#print axioms Lime.readEmitSection_of_the_walls_form
#print axioms Lime.wallsEmit_refuses_without_the_replay
#print axioms Lime.PlannerWit.the_pause_is_rendered_as_the_log_writes_it
#print axioms Lime.PlannerWit.the_open_wednesdays_wall_is_answered_on_its_index
#print axioms Lime.PlannerWit.the_open_wednesdays_wall_is_answered_by_the_kernel
#print axioms Lime.PlannerWit.the_logged_wall_writes_nothing_more
#print axioms Lime.the_walls_form_is_answered_through_the_emit_section
#print axioms Lime.WallTimer.the_day_befores_marks_are_read
#print axioms Lime.WallTimer.a_break_inside_the_meeting_leaves_the_pause_the_last_word

-- =====================================================================
-- APPENDED 2026-09-28: stage 6 W-37 TRACK K (worktree `w37-k`; README gaps 3160-3199): D66 --
-- `PlanCheck.impossibleKept` reads section 8.2 step 5's own filter before the walk, and the five
-- lifts are proved without hnoimp -- and D63 -- `PlanCheck.monotoneInRank` reads the planner's
-- own order.  PlanFold is new (gap 903 is a theorem).  24 audit lines REMOVED above, each a name
-- W-37 renamed, deleted or refuted-and-renamed (README gaps 3161, 3162); the four re-proved
-- refutations kept their lines.
-- =====================================================================
#print axioms Lime.PlanFold.a_deferred_mandatory_instance_found_no_position
#print axioms Lime.PlanFold.assignStep_fills_a_free_slot_a_group_fits
#print axioms Lime.PlanFold.deferOne_keeps_the_assignment
#print axioms Lime.PlanFold.deferWalk_keeps_the_assignment
#print axioms Lime.PlanFold.earliestFree_isSome_of_a_free_run
#print axioms Lime.PlanFold.finalAssign_is_assignFold
#print axioms Lime.PlanFold.foldl_assignStep_idle
#print axioms Lime.PlanFold.foldl_placeStep_keeps_the_record
#print axioms Lime.PlanFold.freeIntervals_holds_a_free_run
#print axioms Lime.PlanFold.freeIntervals_next_unit
#print axioms Lime.PlanFold.nothing_fits_before_on_an_unassigned_day
#print axioms Lime.PlanFold.nothing_fits_before_where_the_fold_fills_nothing
#print axioms Lime.PlanFold.pairwise_mem_or
#print axioms Lime.PlanFold.placeStep_keeps_the_record
#print axioms Lime.PlanFold.the_fold_fills_nothing_on_an_unassigned_day
#print axioms Lime.PlanFold.the_reservation_row_is_a_work_row_of_the_day
#print axioms Lime.PlanCheck.a_waiting_item_is_never_eligible_before
#print axioms Lime.PlanCheck.an_item_eligible_before_is_ranked
#print axioms Lime.PlanCheck.an_unassigned_day_admits_nothing_under_its_budget
#print axioms Lime.PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_from_now_given_the_two_comparisons_on_an_unassigned_day
#print axioms Lime.PlanCheck.dayPlan_ok_is_the_core_seven_and_the_impossible_check
#print axioms Lime.PlanCheck.dayPlan_ok_on_a_quiet_unassigned_day_except_hot
#print axioms Lime.PlanCheck.dayPlan_ok_on_a_quiet_unassigned_day_given_hot
#print axioms Lime.PlanCheck.dayPlan_ok_on_the_whole_day_of_a_paying_decoder_is_the_impossible_check
#print axioms Lime.PlanCheck.eligibleBefore_iff
#print axioms Lime.PlanCheck.impossibleKept_of_nothing_eligible_before
#print axioms Lime.PlanCheck.impossibleKept_on_an_unassigned_day
#print axioms Lime.PlanCheck.impossible_has_no_subject_on_an_unassigned_day
#print axioms Lime.PlanCheck.planOk_of_no_segments_is_the_impossible_check
#print axioms Lime.PlanCheck.rankedBefore_iff
#print axioms Lime.PlanCheck.the_census_ceiling_is_seven_on_an_unassigned_day
#print axioms Lime.PlanCheck.the_reservation_is_a_budget_row_from_now
#print axioms Lime.PlanCheck.the_reservation_is_a_budget_row_of_the_day
#print axioms Lime.PlannerWit.a_planted_drop_of_an_item_step_five_admits_fails_the_check
#print axioms Lime.PlannerWit.a_quiet_hot_day_drops_its_waiting_impossible_item_and_passes
#print axioms Lime.PlannerWit.an_unassigned_day_drops_its_waiting_impossible_item_and_passes
#print axioms Lime.PlannerWit.monotone_rank_over_step_fives_filter_before_the_walk_is_refuted
#print axioms Lime.PlannerWit.planOk_of_no_segments_as_W_14_wrote_it_is_refuted
#print axioms Lime.PlannerWit.step_five_drops_an_owed_impossible_item_its_filter_admitted_before_the_walk
#print axioms Lime.PlannerWit.the_census_is_six_where_the_impossible_item_waits
#print axioms Lime.PlannerWit.the_census_ratio_is_six_since_D63
#print axioms Lime.PlannerWit.the_contiguity_finding_request_is_plain
#print axioms Lime.PlannerWit.the_contiguity_finding_request_is_quiet_and_in_budget
#print axioms Lime.PlannerWit.the_contiguity_finding_request_pays_the_decoder
#print axioms Lime.PlannerWit.the_contiguity_finding_witness_loads
#print axioms Lime.PlannerWit.the_given_lifts_fire_at_the_quiet_impossible_request
#print axioms Lime.PlannerWit.the_hot_comparison_has_subjects_where_it_bites
#print axioms Lime.PlannerWit.the_hot_comparison_is_false_at_the_queued_request
#print axioms Lime.PlannerWit.the_monotone_rank_check_passes_where_D60_orders_by_date
#print axioms Lime.PlannerWit.the_open_item_is_admitted_at_the_first_slot
#print axioms Lime.PlannerWit.the_rank_check_refuses_a_planted_violation_of_the_planners_order
#print axioms Lime.PlannerWit.the_rank_finding_day_places_the_later_sibling
#print axioms Lime.PlannerWit.the_rank_finding_witness_loads
#print axioms Lime.PlannerWit.the_waiting_law_fires_at_both_waiting_requests

-- =====================================================================
-- APPENDED 2026-09-28: stage 6 W-37 TRACK R (worktree `w37-r`) -- README gaps 551 (the cut's
-- kept breaks are drawn), 550 (the reservation row carries the running candidate's multiplier)
-- and 2870/435 (a scheduled window task's Routine row carries its `⚠` at `p = 0`).
-- DELETED above, by this banner: the audit line of Planner.a_break_row_is_replayed_or_the_running_break,
-- which W-37 refutes (`PlannerWit.a_break_row_is_replayed_or_the_running_break_is_refuted`) and
-- restates as `Planner.a_break_row_is_replayed_running_or_kept` (audited below).
-- =====================================================================
#print axioms Lime.Planner.PlanReq.mem_keptBreakRows
#print axioms Lime.Planner.PlanReq.keptBreakRows_kinds
#print axioms Lime.Planner.PlanReq.keptBreakRows_are_not_work
#print axioms Lime.Planner.PlanReq.keptBreakRows_are_not_blocks
#print axioms Lime.Planner.PlanReq.keptBreakRows_are_not_walls
#print axioms Lime.Planner.PlanReq.keptBreakRows_are_not_wind_down
#print axioms Lime.Planner.PlanReq.a_kept_break_is_a_break_of_the_cut
#print axioms Lime.Planner.PlanReq.a_kept_break_is_after_now
#print axioms Lime.Planner.PlanReq.a_kept_break_touches_nothing_blocked
#print axioms Lime.Planner.PlanReq.a_kept_break_clears_the_reservation
#print axioms Lime.Planner.PlanReq.a_slot_clears_a_kept_break
#print axioms Lime.Planner.a_block_row_clears_a_kept_break
#print axioms Lime.Planner.a_break_row_is_replayed_running_or_kept
#print axioms Lime.PlannerWit.the_busy_day_draws_the_break_its_work_touches
#print axioms Lime.PlannerWit.a_break_no_work_touches_is_not_drawn
#print axioms Lime.PlannerWit.a_break_row_is_replayed_or_the_running_break_is_refuted
#print axioms Lime.PlannerWit.the_reservation_row_carries_the_running_candidates_multiplier
#print axioms Lime.PlannerWit.the_hot_routine_witness_loads
#print axioms Lime.PlannerWit.the_hot_routine_instances_are_accepted
#print axioms Lime.PlannerWit.a_scheduled_window_tasks_routine_row_is_hot_at_p_zero
#print axioms Lime.PlannerWit.the_reservation_reads_the_first_candidate_of_its_id

-- ============================================================================
-- APPENDED 2026-09-29: stage 6 W-37 REPAIR -- D61's walls read the day before (README gap 3334),
-- and `touchedAfter`/`pausedFor` written by recursion so the export reaches them (gap 3333),
-- each with its old definition proved as an equation.  The WallTimer witnesses and the walls
-- form's witness request moved to `PlannerWit.lean` with their names kept, so their lines above
-- stand as they were.
-- ============================================================================
#print axioms Lime.WallTimer.the_evening_befores_walls_are_read
#print axioms Lime.WallTimer.touchedAfter_eq_any
#print axioms Lime.WallTimer.pausedFor_eq_find

-- ============================================================================
-- APPENDED 2026-09-29: stage 6 W-37 REPAIR, second commit -- §8.1's window as the fork's planner
-- reads it (README gaps 320 and 3341): a stored window crossing midnight ends on the next day.
-- The view law window_is_the_lookaheads was renamed in place above to the subdomain it holds on.
-- ============================================================================
#print axioms Lime.Planner.PlanReq.window_crosses_midnight_as_the_forks_planner_reads_it

-- ============================================================================
-- APPENDED 2026-09-29: stage 6 W-38 TRACK K -- the owner's D67 (README gap 3160, parity P58): the day NAMES
-- why an owed impossible item step 5 admitted has no row (`Planner.PlanReq.dayUnplaced`), the impossible check
-- reads placed-or-named-with-a-true-reason, and it holds on every produced day (`PlanCheck.impossibleKept_on_every_day`,
-- from `PlanFold`'s W-38 walk lemmas), so the W-31 paying lifts are theorems again.  Removed above with their
-- subjects: the W-37 refutations D67 makes false (replaced in place by the statements they refuted, fired) and
-- the two laws renamed to `…_or_named` / `an_unnamed_…` (their old forms refuted in PlannerWit's W-38 block).
-- ============================================================================
#print axioms Lime.PlanCheck.an_unnamed_owed_eligible_impossible_item_fails_the_check_with_budget_left_where_nothing_is_assigned
#print axioms Lime.PlanCheck.dayPlan_ok_is_the_core_seven
#print axioms Lime.PlanCheck.dayPlan_ok_of_the_core_seven
#print axioms Lime.PlanCheck.dayPlan_ok_on_the_whole_day_of_a_paying_decoder
#print axioms Lime.PlanCheck.impossibleKept_iff_the_owed_items_are_assigned_or_named
#print axioms Lime.PlanCheck.impossibleKept_on_every_day
#print axioms Lime.PlanCheck.whyHolds_of_a_name_the_day_carries
#print axioms Lime.PlanFold.a_budget_spent_name_is_true_of_the_day
#print axioms Lime.PlanFold.a_filled_slot_assigns_its_groups_members
#print axioms Lime.PlanFold.assignedRows_length
#print axioms Lime.PlanFold.assignFold_used_counts
#print axioms Lime.PlanFold.assignStep_counts
#print axioms Lime.PlanFold.assignStep_groups_of_not_picked
#print axioms Lime.PlanFold.assignStep_slotOf_ne
#print axioms Lime.PlanFold.assignStep_used_le
#print axioms Lime.PlanFold.a_taken_name_holds_every_slot_it_fits
#print axioms Lime.PlanFold.clampSec_mono
#print axioms Lime.PlanFold.countP_snd_zip
#print axioms Lime.PlanFold.drop_zip
#print axioms Lime.PlanFold.foldl_assignStep_counts
#print axioms Lime.PlanFold.foldl_assignStep_groups_of_never_picked
#print axioms Lime.PlanFold.foldl_assignStep_keeps_the_members
#print axioms Lime.PlanFold.foldl_assignStep_lengths
#print axioms Lime.PlanFold.foldl_assignStep_slotOf_ne
#print axioms Lime.PlanFold.foldl_assignStep_used_le
#print axioms Lime.PlanFold.groupFitsSlot_of_drop
#print axioms Lime.PlanFold.the_day_holds_every_block_the_walk_spent
#print axioms Lime.PlanFold.the_walk_passes_a_slot_a_group_fits_before_it_only_for_the_budget
#print axioms Lime.PlanFold.zipIdx_index
#print axioms Lime.PlanFold.zipIdx_split
#print axioms Lime.Planner.dayDiagnostics_unplaced
#print axioms Lime.Planner.PlanReq.dayUnplaced_capped
#print axioms Lime.Planner.PlanReq.mem_dayUnplaced
#print axioms Lime.PlannerWit.a_named_reason_the_day_does_not_bear_out_fails_the_check
#print axioms Lime.PlannerWit.dayPlan_ok_is_the_core_seven_at_the_contiguity_finding
#print axioms Lime.PlannerWit.dayPlan_ok_of_the_core_seven_at_the_contiguity_finding
#print axioms Lime.PlannerWit.dayPlan_ok_on_the_whole_day_of_a_paying_decoder_fires_at_the_contiguity_finding
#print axioms Lime.PlannerWit.impossible_kept_from_the_battery_as_W_37_wrote_it_is_refuted
#print axioms Lime.PlannerWit.impossibleKept_holds_on_a_paying_day
#print axioms Lime.PlannerWit.impossibleKept_iff_the_owed_items_are_assigned_as_W_37_wrote_it_is_refuted
#print axioms Lime.PlannerWit.impossibleKept_is_true_but_not_because_its_subject_is_empty
#print axioms Lime.PlannerWit.impossibleKept_of_nothing_assigned_iff_as_W_37_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_budget_spent_name_holds_at_the_one_block_day
#print axioms Lime.PlannerWit.the_day_names_each_reason_the_walk_can_give
#print axioms Lime.PlannerWit.the_day_without_its_name_fails_the_check
#print axioms Lime.PlannerWit.the_no_run_left_name_holds_at_the_contiguity_finding
-- W-38 TRACK K, continued -- the campaign's D69 on README gap 3323 (`Lime.DocKind.ciDefault`, the file kind's
-- `ci` default at the top of `effectiveCiAux`'s walk; `Lime.effectiveCi_default` restated in place, its old form refuted in
-- PlannerWit) and README gap 3322 (the seven from `now` are implied by the seven on the whole day, and where they differ
-- the difference is a row the log replayed).
#print axioms Lime.effectiveCi_default_is_three_outside_the_furniture_files
#print axioms Lime.PlanCheck.a_core_failure_on_a_paying_day_is_a_logged_row
#print axioms Lime.PlanCheck.a_whole_day_core_failure_is_a_logged_row
#print axioms Lime.PlanCheck.planOkCore_from_now_of_the_whole_day
#print axioms Lime.PlannerWit.effectiveCi_default_as_W_37_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_furniture_files_read_their_own_ci_default
#print axioms Lime.PlannerWit.the_log_overbooks_the_whole_day_and_not_the_day_from_now
#print axioms Lime.PlannerWit.the_over_budget_failure_is_a_logged_row
-- W-38 TRACK K, continued -- README gap 2020's from-now half: overbooking from `now` cannot happen on a produced day,
-- so the seven from `now` follow from the decoder and a plain store alone.
#print axioms Lime.PlanCheck.dayPlan_ok_core_from_now_of_a_decoder
#print axioms Lime.PlanCheck.foldl_add_is_sum
#print axioms Lime.PlanCheck.noOverbook_from_now
#print axioms Lime.PlanCheck.sum_le_length_mul
#print axioms Lime.PlannerWit.the_fold_s_blocks_fit_the_budget_from_now

#print axioms Lime.Planner.dayPlan_window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_unless_a_windowless_day_has_only_a_logged_arrival_or_a_wall_passes_its_bounds

-- ============================================================================
-- APPENDED 2026-09-29: stage 6 W-38 TRACK R -- the running interruption walked among the walls in
-- fork `collect_walls`' order (README gap 3281), the stored window and budget read as the fork's
-- planner reads them (gap 320's two remaining inputs), step 5's served order on the day (gap 3343),
-- the step-8 pair and id keys as their tuples' projections on the wire (gap 3282), and the busy
-- day's budget witness answered the other way (gap 3391).  Four audit lines above were renamed in
-- place with their theorems: the two window view laws and the budget formula law (restated on the
-- subdomain they hold on) and the busy day's budget witness (restated, its P9 form refuted below).
-- ============================================================================
#print axioms Lime.Look.Today.forToday_of_date
#print axioms Lime.Look.Today.forToday_of_no_date
#print axioms Lime.Look.Today.not_forToday_of_another_day
#print axioms Lime.Look.Today.storedWindow_is_a_planWindow
#print axioms Lime.Look.Today.storedBudget_is_a_planBudget
#print axioms Lime.Look.Today.planArrivalSec_on_a_dated_state
#print axioms Lime.Look.the_planner_reads_a_window_with_no_date_or_no_budget
#print axioms Lime.Look.the_planner_reads_an_arrival_with_no_date
#print axioms Lime.Look.adhoc_walk_perm
#print axioms Lime.Look.adhoc_walk_map_filter
#print axioms Lime.Planner.PlanReq.window_is_the_stored_one_on_its_day
#print axioms Lime.Planner.PlanReq.window_is_the_formula_without_a_window_on_its_day
#print axioms Lime.Planner.insBy_append_cons_of_le
#print axioms Lime.Planner.insBy_append_of_after
#print axioms Lime.Planner.insSort_snoc
#print axioms Lime.Planner.sortWalls_snoc
#print axioms Lime.Planner.stepOneOrder_without_an_interruption
#print axioms Lime.Planner.PlanReq.the_interruption_is_walked_where_collect_walls_sorts_it
#print axioms Lime.Planner.stepOneOrder_perm
#print axioms Lime.Planner.PlanReq.dayServed_capped
#print axioms Lime.Planner.dayDiagnostics_served
#print axioms Lime.Planner.dayPlan_serves_in_the_walks_order
#print axioms Lime.Planner.PlanReq.mem_dayServed
#print axioms Lime.PlanWire.the_impossible_key_is_the_impossibleUntil_key_projected
#print axioms Lime.PlanWire.the_underused_key_is_the_underusedLevels_key_projected
#print axioms Lime.PlanWire.the_blocked_key_is_the_blockedDeps_key_projected
#print axioms Lime.PlanWire.the_served_key_is_the_walks_order
#print axioms Lime.PlannerWit.the_interruption_and_the_meeting_are_drawn_in_the_forks_order
#print axioms Lime.PlannerWit.the_order_laws_have_subjects
#print axioms Lime.PlannerWit.gap_320s_two_inputs_are_read_as_the_forks_planner_reads_them
#print axioms Lime.PlannerWit.the_dated_window_request_is_in_the_view_laws_domain
#print axioms Lime.PlannerWit.the_planners_window_is_the_lookaheads_unless_it_crosses_midnight_is_refuted
#print axioms Lime.PlannerWit.the_budget_is_the_formula_without_a_stored_one_is_refuted
#print axioms Lime.PlannerWit.the_budget_does_not_move_the_assigned_set_at_the_busy_request_is_refuted
#print axioms Lime.PlannerWit.the_day_carries_the_order_step_five_serves


-- ============================================================================
-- APPENDED 2026-09-29: stage 6 W-38 TRACK T (worktree `w38-t`) -- the owner's D68 (a typed
-- pause is drawn as a pause, not lost time: `Emit.pausedRow` and its laws, the witness day in
-- `PlannerWit.lean`; parity P59) and the campaign's D69 call on README gap 3345 (a duration past
-- the host's width refuses the tree by name: the new module `Width.lean`, and `runLoad`'s witness
-- at the end of `Boundary.lean`; parity P61).  Gaps 3244 and 3283 are host-only.
-- ============================================================================
#print axioms Lime.Emit.pausedRow_iff
#print axioms Lime.Emit.titleCell_of_pausedRow
#print axioms Lime.Emit.noteCell_of_pausedRow
#print axioms Lime.Emit.titleCell_of_a_lost_row_that_is_not_a_pause
#print axioms Lime.Emit.noteCell_of_a_row_that_is_not_a_pause
#print axioms Lime.Emit.pausedRow_pastRowOf
#print axioms Lime.Emit.a_replayed_pause_is_drawn_as_a_pause
#print axioms Lime.Emit.a_lost_row_that_is_not_a_pause_is_drawn_lost
#print axioms Lime.PlannerWit.typedPauseRun_resumes_ok
#print axioms Lime.PlannerWit.a_typed_pause_is_drawn_paused_and_an_interruption_lost
#print axioms Lime.PlannerWit.the_minutes_drawn_lost_are_the_minutes_the_review_counts_lost
#print axioms Lime.Width.pastWidth_eq_none_iff
#print axioms Lime.Width.pastWidth_eq_some
#print axioms Lime.Width.firstPastWidth_eq_none_iff
#print axioms Lime.Width.firstPastWidth_eq_some
#print axioms Lime.Width.fits_of_fits_at_a_longer_block
#print axioms Lime.Width.fits_at_one_of_fits
#print axioms Lime.Width.the_leading_estimate_past_the_width_is_refused
#print axioms Lime.Width.the_three_keys_past_the_width_are_refused
#print axioms Lime.Width.a_block_estimate_is_read_at_the_block_length
#print axioms Lime.Width.a_commented_line_past_the_width_is_prose
#print axioms Lime.Width.the_slots_spell_themselves
#print axioms Lime.Width.refusalJson_is_the_err_shape
#print axioms Lime.runLoad_refuses_a_duration_past_the_width
-- ============================================================================
-- APPENDED 2026-09-29: stage 6 W-38 REPAIR -- D69 on the WRITERS (README gap 3520): a command
-- that would write a duration past the host's width into one of `Width.Slot`'s places is
-- refused `badValue <key>` by `runLoad`'s `widthGate`, at the end of `Boundary.lean`.
-- ============================================================================
#print axioms Lime.widthGate_eq_ok_iff
#print axioms Lime.widthGate_refuses_only_past_the_width
#print axioms Lime.widthGate_ok_is_the_command
#print axioms Lime.editValDurs_reads_the_width_keys
#print axioms Lime.runLoad_refuses_a_command_writing_past_the_width
-- W-38 REPAIR, continued -- D67 as a CLASS (README gap 3523): an item the day lists impossible and
-- does not place is NAMED, `noSlotAdmits` when step 5's filter admits it nowhere
-- (`Planner.PlanReq.dayUnplaced`, `PlanCheck.every_listed_impossible_item_is_placed_or_named`).
#print axioms Lime.Planner.PlanReq.an_item_the_filter_admits_nowhere_is_named
#print axioms Lime.Planner.PlanReq.every_unassigned_listed_item_is_named
#print axioms Lime.PlanCheck.every_listed_impossible_item_is_placed_or_named
#print axioms Lime.PlanCheck.whyHolds_noSlotAdmits_iff
#print axioms Lime.PlannerWit.an_impossible_item_no_slot_admits_is_named_so
-- ============================================================================
-- APPENDED 2026-09-30: stage 6 W-39 TRACK K (worktree `w39-k`) -- the burn-down, 6 -> 0.  All six
-- goals leave `Goals.lean`, each refuted as stage 6 wrote it and restated over what §8.2 does:
-- `PlanCheck.plan_places_no_demanding_block_after_wind_down` (the decoder's fifth clause, the
-- wind-down inside the calendar, the whole day), `PlanFold.plan_is_monotone_in_rank_in_the_served_group_order`
-- and `PlanFold.plan_puts_hot_before_the_queue_in_the_served_group_order` (README gap 3526; renamed at W-40),
-- `PlanCheck.a_batch_row_holds_members_of_one_run_of_its_ci` (renamed at W-40; every batch a run of equal-`ci`
-- entries), L24 `PlanFold.plan_tail_drop` (the budget only stops the walk early; D29's form is
-- `PlanFold.plan_tail_drop_with_the_active_item_erased`) and L25
-- `PlanFold.plan_is_stable_across_a_replan` (what ended before `now` and is closed stays).  The
-- lemmas: gap 3526 (served order), gap 3354 (the partition), gap 2326 (REFUTED).
-- ============================================================================
#print axioms Lime.PlanFold.assignStep_fills_with_the_first_that_fits
#print axioms Lime.PlanFold.spendActive_sorted
#print axioms Lime.PlanFold.startGroups_sorted
#print axioms Lime.PlanFold.a_group_served_earlier_is_no_later_in_the_key
#print axioms Lime.PlanFold.a_slot_a_group_fits_before_the_walk_went_to_a_group_served_no_later
#print axioms Lime.PlanFold.a_slot_a_group_fits_before_the_walk_went_to_a_group_served_before_it
#print axioms Lime.PlanFold.a_taken_name_went_to_groups_served_before_the_items
#print axioms Lime.PlanFold.natsLe_refl
#print axioms Lime.PlanFold.served_earlier_of_the_key
#print axioms Lime.PlanFold.an_earlier_group_that_fits_a_taken_slot_was_placed_before_it
#print axioms Lime.PlanFold.a_filled_slot_draws_a_work_row_of_its_groups_members
#print axioms Lime.PlanFold.an_earlier_slot_starts_earlier
#print axioms Lime.PlanFold.plan_is_monotone_in_rank_in_the_served_group_order
#print axioms Lime.PlanFold.plan_puts_hot_before_the_queue_in_the_served_group_order
#print axioms Lime.PlanFold.eq_of_mem_of_nodup_map
#print axioms Lime.PlanFold.nodup_of_nodup_map
#print axioms Lime.PlanFold.flatMap_nodup_at_two_positions
#print axioms Lime.PlanFold.flatMap_sublist
#print axioms Lime.PlanFold.rankedCands_ix_nodup
#print axioms Lime.PlanFold.rankedCands_nodup
#print axioms Lime.PlanFold.filterMap_groupOf_members
#print axioms Lime.PlanFold.rawGroups_members_perm
#print axioms Lime.PlanFold.rawGroups_members_nodup
#print axioms Lime.PlanFold.spendActive_members
#print axioms Lime.PlanFold.startGroups_members_nodup
#print axioms Lime.PlanFold.a_ranked_entry_is_in_one_start_group_at_most
#print axioms Lime.PlanFold.gatherBatch_snd_filter_other
#print axioms Lime.PlanFold.gatherBatch_snd_filter_own
#print axioms Lime.PlanFold.batchLoop_is_a_run_of_its_ci
#print axioms Lime.PlanFold.a_batch_is_a_run_of_equal_ci_entries_of_the_order
#print axioms Lime.PlanFold.assignStep_of_spent
#print axioms Lime.PlanFold.assignStep_below
#print axioms Lime.PlanFold.foldl_assignStep_of_spent
#print axioms Lime.PlanFold.foldl_assignStep_truncates
#print axioms Lime.PlanFold.assignStep_group_is_the_group_with_its_spent
#print axioms Lime.PlanFold.foldl_assignStep_group_is_the_group_with_its_spent
#print axioms Lime.PlanFold.assignedSeg_ignores_spent
#print axioms Lime.PlanFold.filterMap_prefix_of_agreeing_head
#print axioms Lime.PlanFold.insBy_append_after
#print axioms Lime.PlanFold.insSort_append_after
#print axioms Lime.PlanFold.todaySlots_of_energisedSlots
#print axioms Lime.PlanFold.activeSeed_is_the_reservation
#print axioms Lime.PlanFold.energised_start_lt
#print axioms Lime.PlanFold.rowLe_of_start_lt
#print axioms Lime.PlanFold.filter_work_of_no_work
#print axioms Lime.PlanFold.stepOneOrder_work
#print axioms Lime.PlanFold.work_rows_of_the_day
#print axioms Lime.PlanFold.assignedRows_of_assignFold
#print axioms Lime.PlanFold.rows_ignore_spent
#print axioms Lime.PlanFold.groupFitsSlot_congr
#print axioms Lime.PlanFold.assignedSeg_congr
#print axioms Lime.PlanFold.findIdx?_of_values
#print axioms Lime.PlanFold.assignStep_on_views
#print axioms Lime.PlanFold.foldl_assignStep_on_views
#print axioms Lime.PlanFold.rows_of_views
#print axioms Lime.PlanFold.views_of_three_parts
#print axioms Lime.PlanFold.snd_mem_of_mem_zip
#print axioms Lime.PlanFold.plan_tail_drop
#print axioms Lime.PlanFold.take_erase_is_a_prefix_of_erase
#print axioms Lime.PlanFold.plan_tail_drop_with_the_active_item_erased
#print axioms Lime.PlanFold.a_longer_clip_keeps_its_pieces_through_a_cut
#print axioms Lime.PlanFold.a_longer_clip_keeps_its_pieces_through_the_cuts
#print axioms Lime.PlanFold.clipCut_keeps_an_early_piece
#print axioms Lime.PlanFold.a_past_row_ended_before_now_is_a_past_row_later
#print axioms Lime.PlanFold.a_slot_starts_at_or_after_now
#print axioms Lime.PlanFold.a_planned_row_starts_at_or_after_now
#print axioms Lime.PlanFold.plan_is_stable_across_a_replan
-- W-39 TRACK K, continued -- beside the checker (`PlanCheck.lean`).
#print axioms Lime.PlanCheck.candAnswers_ids
#print axioms Lime.PlanCheck.rankedCands_ids_nodup
#print axioms Lime.PlanCheck.an_item_is_in_one_start_group_at_most
#print axioms Lime.PlanCheck.plan_places_no_demanding_block_after_wind_down
#print axioms Lime.PlanCheck.a_batch_row_holds_members_of_one_run_of_its_ci
-- W-39 TRACK K, continued -- the refutations, the firings and the findings (`PlannerWit.lean`).
#print axioms Lime.PlannerWit.the_conference_window_runs_past_the_night_is_refuted
#print axioms Lime.PlannerWit.the_conference_window_ends_inside_the_night
#print axioms Lime.PlannerWit.day_zeros_window_is_not_bounded_by_the_night
#print axioms Lime.PlannerWit.the_conference_day_places_a_block_after_the_wind_down_is_refuted
#print axioms Lime.PlannerWit.the_wind_down_goal_holds_at_the_conference_wednesday
#print axioms Lime.PlannerWit.the_wind_down_law_has_a_subject_where_the_wire_agrees_is_refuted
#print axioms Lime.PlannerWit.the_agreeing_conferences_item_is_not_demanding
#print axioms Lime.PlannerWit.the_split_day_serves_the_later_sibling_first_is_refuted
#print axioms Lime.PlannerWit.the_rank_goal_holds_at_the_split_day
#print axioms Lime.PlannerWit.monotone_rank_in_the_candidate_order_at_the_taken_slot_is_refuted
#print axioms Lime.PlannerWit.the_batch_goal_holds_at_the_split_day
#print axioms Lime.PlannerWit.the_rank_and_batch_checks_fail_at_the_split_day_is_refuted
#print axioms Lime.PlannerWit.the_served_order_rank_law_has_a_subject
#print axioms Lime.PlannerWit.the_served_order_rank_law_fires_at_the_paying_batch_day
#print axioms Lime.PlannerWit.the_served_order_hot_law_has_a_subject
#print axioms Lime.PlannerWit.the_served_order_hot_law_fires
#print axioms Lime.PlannerWit.the_no_run_left_slots_went_to_a_group_served_before_it
#print axioms Lime.PlannerWit.an_id_sent_twice_sits_in_two_start_groups
#print axioms Lime.PlannerWit.one_start_group_per_item_needs_each_id_sent_once
#print axioms Lime.PlannerWit.the_batches_are_runs_of_their_ci_at_the_batch_request
#print axioms Lime.PlannerWit.the_tail_drop_law_has_a_subject_with_a_block_running
#print axioms Lime.PlannerWit.the_tail_drop_law_fires_with_a_block_running
#print axioms Lime.PlannerWit.the_stability_law_fires_an_hour_later
#print axioms Lime.PlannerWit.the_stability_law_needs_the_row_to_have_ended_before_now
#print axioms Lime.PlannerWit.the_stability_law_needs_the_row_to_be_closed
-- ============================================================================
-- APPENDED 2026-09-30: stage 6 W-39 TRACK A -- the planner's arrival is fork `Planner::new`'s:
-- the state's, else the day's first logged `arrive`, else `now` (README gap 3390); `planBudget`
-- reads `forToday` (gap 3535) and the stored window's two readings are one on every state the
-- binary writes; the file-kind `ci` default read alike by the plan and the wire (gap 3531).  Four
-- renames are in place above (the two view laws, the witness day's window, the hour-later pair).
-- ============================================================================
#print axioms Lime.Look.Today.planArrivalSec_reads_the_stored_arrival_first
#print axioms Lime.Look.Today.planArrivalSec_reads_the_logged_arrival
#print axioms Lime.Look.Today.planArrivalSec_without_a_logged_arrival
#print axioms Lime.Look.Today.planArrivalSec_is_arrivalSec_unless_only_the_log_holds_it
#print axioms Lime.Look.the_two_arrivals_part_at_a_logged_arrival
#print axioms Lime.Look.Today.planArrivalSec_on_a_dated_state_whatever_the_log_holds_is_refuted
#print axioms Lime.Look.Today.storedWindow_today
#print axioms Lime.Look.Today.storedWindow_is_planWindow_on_a_written_state
#print axioms Lime.Look.the_binary_writes_a_window_only_with_its_day_and_budget
#print axioms Lime.PlannerWit.the_witness_day_is_planned_from_two_in_the_afternoon_is_refuted
#print axioms Lime.PlannerWit.the_woken_day_is_planned_from_the_logged_arrival
#print axioms Lime.PlannerWit.the_planners_window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_is_refuted
#print axioms Lime.PlannerWit.the_days_window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_is_refuted
#print axioms Lime.PlannerWit.the_rebuilt_request_is_in_the_restated_view_laws_domain
#print axioms Lime.PlannerWit.the_rebuilt_state_plans_the_woken_day
#print axioms Lime.PlannerWit.the_stored_arrival_is_read_before_the_logged_one
#print axioms Lime.PlannerWit.an_hour_later_changes_one_field_and_moves_the_window_is_refuted
#print axioms Lime.PlannerWit.an_hour_later_moves_the_window_of_a_day_with_no_arrival
#print axioms Lime.PlannerWit.the_furniture_witness_loads
#print axioms Lime.PlannerWit.the_plan_and_the_wire_read_the_file_kinds_ci_alike
-- ============================================================================
-- APPENDED 2026-09-30: stage 6 W-39 TRACK T -- the week grid cuts a pause with the planner's cut
-- (README gaps 3432 and 3528; `GridCut.lean`): `GridCut.segSpans` is `Planner.pastSpans` at the day
-- it plans, the grid's partition of a clip, and the `emit` walls form's `week`.
-- ============================================================================
#print axioms Lime.GridCut.pastSpans_is_segSpans
#print axioms Lime.GridCut.in_cutOne_iff
#print axioms Lime.GridCut.in_cutAll_iff
#print axioms Lime.GridCut.in_clipCut_iff
#print axioms Lime.GridCut.the_grid_draws_every_second_of_the_clip_once
#print axioms Lime.GridCut.a_second_is_covered_iff_a_wall_of_the_day_covers_it
#print axioms Lime.GridCut.nothing_but_a_pause_is_covered
#print axioms Lime.GridCut.answer_without_a_week
#print axioms Lime.GridCut.walls_answer_had_its_inputs
#print axioms Lime.GridCut.a_week_asked_is_answered
#print axioms Lime.GridCut.a_bad_week_is_refused_by_name
#print axioms Lime.GridCut.answer_refuses_without_the_replay
#print axioms Lime.GridCut.the_week_refusal_is_the_err_emit_shape
#print axioms Lime.GridCut.the_cut_is_run
#print axioms Lime.GridCut.readWeek_is_run
#print axioms Lime.GridCut.the_weeks_cut_is_answered

/- =====================================================================
   APPENDED 2026-09-30: stage 6, run W-39, REPAIR STEP (README gaps 3556, 3712, 3713).
   The planner's window reads the day's walls clipped to it; the conference witnesses
   refuted and renamed; the wind-down goal back in Goals.lean.
   ===================================================================== -/
#print axioms Lime.Look.wallsClippedOn_eq_wallsOn
#print axioms Lime.Look.wallsClippedOn_ends_by
#print axioms Lime.Planner.PlanReq.the_windows_walls_are_the_walls_step_one_places
#print axioms Lime.Planner.PlanReq.the_windows_walls_end_by_the_days_end
#print axioms Lime.PlannerWit.the_planners_window_formula_over_the_days_whole_walls_is_refuted
#print axioms Lime.PlannerWit.the_view_law_without_the_days_walls_inside_it_is_refuted
#print axioms Lime.PlannerWit.the_view_laws_subjects_have_their_walls_inside_their_day
#print axioms Lime.PlannerWit.the_conference_is_clipped_to_the_day_for_the_window_and_the_walls

/- =====================================================================
   APPENDED 2026-09-30: stage 6, run W-40, TRACK K (the owner's D74, parity P64; D77;
   README gaps 3546, 3714, 3548, 3541).  §7.5's batches split into RUNS; step 5 serves each
   `ci` in the candidate order; the rank, HOT and batch laws restated over what a user can
   observe.  Renamed in place above: the W-39 group-order laws (`..._in_the_served_group_order`),
   the W-39 batch-run law (`a_batch_row_holds_members_of_one_run_of_its_ci`), and the split
   day's W-39 witnesses (refuted and renamed, or retired with the hole and replaced).
   ===================================================================== -/
#print axioms Lime.Planner.mem_splitPush
#print axioms Lime.PlanFold.splitPush_flatten_eq
#print axioms Lime.PlanFold.splitFold_flatten_eq
#print axioms Lime.PlanFold.splitGroups_flatten_eq
#print axioms Lime.PlanFold.splitPush_head
#print axioms Lime.PlanFold.splitPush_keeps_closing
#print axioms Lime.PlanFold.splitFold_closes
#print axioms Lime.PlanFold.splitGroups_closes
#print axioms Lime.PlanFold.batchLoop_filter_flatten
#print axioms Lime.PlanFold.groupsOfBatch_members
#print axioms Lime.PlanFold.flatMap_members_filter_ci
#print axioms Lime.PlanFold.rawGroups_members
#print axioms Lime.PlanFold.rawGroups_filter_ci_members
#print axioms Lime.PlanFold.natsLe_of_append
#print axioms Lime.PlanFold.groupKeyLe_of_rankedLe
#print axioms Lime.PlanFold.a_group_member_is_not_a_wall
#print axioms Lime.PlanFold.rawGroups_filter_ci_sorted
#print axioms Lime.PlanFold.buildGroups_filter_ci
#print axioms Lime.PlanFold.the_walk_serves_each_ci_in_the_candidate_order
#print axioms Lime.PlanFold.a_same_ci_entry_ahead_is_served_no_later
#print axioms Lime.PlanCheck.a_work_row_with_an_energy_is_the_folds
#print axioms Lime.PlanCheck.a_placed_row_at_a_slots_start_is_that_slots
#print axioms Lime.PlanCheck.a_started_member_is_ranked
#print axioms Lime.PlanCheck.plan_is_monotone_in_rank
#print axioms Lime.PlanCheck.plan_puts_hot_before_the_queue
#print axioms Lime.PlanCheck.a_batch_row_carries_a_slots_energy
#print axioms Lime.PlanCheck.a_batch_rows_items_are_a_run_of_its_ci
#print axioms Lime.PlanCheck.plan_never_batches_past_an_equal_ci_candidate
#print axioms Lime.PlannerWit.the_split_day_serves_the_siblings_in_the_candidate_order
#print axioms Lime.PlannerWit.the_two_block_split_day_places_the_siblings_in_the_candidate_order
#print axioms Lime.PlannerWit.the_batch_store_writes_no_item_before_line_one
#print axioms Lime.PlannerWit.the_split_day_has_no_batch_row
#print axioms Lime.PlannerWit.the_rank_and_batch_checks_hold_at_the_split_day_and_fail_on_its_planted_inversion
#print axioms Lime.PlannerWit.the_riding_witness_loads
#print axioms Lime.PlannerWit.the_riding_day_batches_across_a_ci
#print axioms Lime.PlannerWit.the_riding_day_refutes_both_weakenings
#print axioms Lime.PlannerWit.monotone_rank_in_the_candidate_order_needs_one_ci
#print axioms Lime.PlannerWit.plan_puts_hot_before_the_queue_needs_a_row_of_queue_items
#print axioms Lime.PlannerWit.the_candidate_order_rank_law_has_a_subject_at_the_two_block_split_day
#print axioms Lime.PlannerWit.the_candidate_order_rank_law_fires_at_the_two_block_split_day
#print axioms Lime.PlannerWit.the_candidate_order_hot_law_has_a_subject
#print axioms Lime.PlannerWit.the_candidate_order_hot_law_fires
#print axioms Lime.PlannerWit.the_candidate_order_batch_law_has_a_subject
#print axioms Lime.PlannerWit.the_candidate_order_batch_law_fires

/- =====================================================================
   APPENDED 2026-09-30: stage 6, run W-40, TRACK P (README gaps 3480, 3666, 2326, 3544,
   3713, 3714, 3780-3790; parity P67).  `PlanStable.lean` — a running break read once
   (D77), the planner's window inside the night and the wind-down law without E8's seam,
   and L25 over a replan after a logged verb — and `PlannerWit`'s W-40 block.
   `Lime.Planner.PlanReq.window_crosses_midnight_as_the_forks_planner_reads_it` keeps its
   audit line above: RESTATED, same name (README gap 3782).
   ===================================================================== -/
#print axioms Lime.PlanStable.clipTo_drops_walls_ending_by
#print axioms Lime.PlanStable.freeIntervals_drop_walls_ending_by
#print axioms Lime.PlanStable.overlapsAny_drops_walls_ending_by
#print axioms Lime.PlanStable.earliestFree_drops_walls_ending_by
#print axioms Lime.PlanStable.cutSlots_drop_walls_ending_by
#print axioms Lime.PlanStable.sinceBreak_is_the_starts_after_the_last_break
#print axioms Lime.PlanStable.the_running_break_and_its_logged_twin_count_alike
#print axioms Lime.PlanStable.an_overrun_break_ends_at_now
#print axioms Lime.PlanStable.nothing_is_reserved_while_the_block_is_paused
#print axioms Lime.PlanStable.placeStep_drops_walls_ending_by_now
#print axioms Lime.PlanStable.foldl_placeStep_drops_walls_ending_by_now
#print axioms Lime.PlanStable.the_cut_does_not_change_when_an_overrun_break_is_logged
#print axioms Lime.PlanStable.countIn_le_below
#print axioms Lime.PlanStable.windowEnd_le_of_walls_end_by
#print axioms Lime.PlanStable.the_window_ends_by_the_night_without_a_stored_window
#print axioms Lime.PlanStable.the_stored_window_ends_by_the_night
#print axioms Lime.PlanStable.the_window_ends_by_the_night
#print axioms Lime.PlanStable.no_block_row_starts_at_or_after_a_wind_down_row_when_the_window_ends_by_the_night
#print axioms Lime.PlanStable.plan_places_no_demanding_block_after_wind_down_when_the_window_ends_by_the_night
#print axioms Lime.PlannerWit.plan_places_no_demanding_block_after_wind_down_where_the_wire_agrees_or_the_window_ends_by_the_night
#print axioms Lime.PlanStable.plan_places_no_demanding_block_after_wind_down_on_a_planned_window
#print axioms Lime.PlanStable.plan_places_no_demanding_block_after_wind_down_inside_the_day
#print axioms Lime.PlanStable.a_past_row_is_replayed_from_an_extending_record
#print axioms Lime.PlanStable.pastRowOf_reads_the_record_only_for_done
#print axioms Lime.PlanStable.a_closed_row_ended_before_now_is_kept
#print axioms Lime.PlanStable.plan_is_stable_across_a_replan_after_a_logged_verb
#print axioms Lime.PlanStable.plan_is_stable_across_a_replan_after_a_verb_that_closes_nothing
#print axioms Lime.PlanStable.plan_is_stable_across_a_replan_of_the_same_record
#print axioms Lime.PlanStable.lowestFree_drops_walls_ending_by
#print axioms Lime.PlanStable.the_logged_twins_inputs
#print axioms Lime.PlanStable.the_logged_twins_folds
#print axioms Lime.PlanStable.replayedRows_from_now
#print axioms Lime.PlanStable.breakRows_from_now
#print axioms Lime.PlanStable.the_day_from_now_of_the_twins_inputs
#print axioms Lime.PlanStable.stepOneOrder_from_now_of_the_logged_twin
#print axioms Lime.PlanStable.the_day_from_now_does_not_change_when_an_overrun_break_is_logged
#print axioms Lime.PlannerWit.shortBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_short_break_running_and_logged_plan_one_day_from_now
#print axioms Lime.PlannerWit.the_rest_reading_cut_a_break_the_logged_twin_does_not
#print axioms Lime.PlannerWit.the_counter_reads_the_sit_as_a_break_running_or_logged
#print axioms Lime.PlannerWit.the_cut_law_fires_at_the_short_break
#print axioms Lime.PlannerWit.the_wind_down_law_needs_the_wind_down_inside_the_calendar
#print axioms Lime.PlannerWit.the_wind_down_goal_fails_where_the_kernels_clock_merges_the_last_evening
#print axioms Lime.PlannerWit.the_window_crossing_midnight_ends_on_the_next_days_clock_is_refuted
#print axioms Lime.PlannerWit.the_fall_back_window_ends_inside_the_night_as_the_forks_does
#print axioms Lime.PlannerWit.the_planned_window_bound_fires_at_the_witness_wednesday
#print axioms Lime.PlannerWit.eveRun_resumes_ok
#print axioms Lime.PlannerWit.the_eves_window_runs_past_the_night
#print axioms Lime.PlannerWit.the_eve_places_a_block_after_the_wind_down
#print axioms Lime.PlannerWit.the_wind_down_law_has_a_subject_on_the_eve
#print axioms Lime.PlannerWit.the_window_bound_needs_the_arrival_inside_the_day
#print axioms Lime.PlannerWit.no_block_after_the_wind_down_needs_the_window_inside_the_night
#print axioms Lime.PlannerWit.recordExtends_spec
#print axioms Lime.PlannerWit.morningRun_resumes_ok
#print axioms Lime.PlannerWit.the_morning_is_extended_by_lime_done
#print axioms Lime.PlannerWit.flipEarlyRun_resumes_ok
#print axioms Lime.PlannerWit.flipLateRun_resumes_ok
#print axioms Lime.PlannerWit.lime_done_after_now_raises_an_earlier_blocks_done_flag
#print axioms Lime.PlannerWit.plan_is_stable_across_a_replan_over_an_extending_record_exactly_is_refuted
#print axioms Lime.PlannerWit.the_l25_law_fires_after_lime_done_with_the_flag_raised
#print axioms Lime.PlannerWit.undoEarlyRun_resumes_ok
#print axioms Lime.PlannerWit.undoLateRun_resumes_ok
#print axioms Lime.PlannerWit.an_undo_after_now_is_not_an_extension
#print axioms Lime.PlannerWit.the_day_law_fires_at_the_short_break

/- =====================================================================
   APPENDED 2026-09-30: stage 6, run W-40, TRACK T (README gap 3620; the campaign's D77 call,
   parity P63 restated).  A Pause past local midnight is cut by EACH calendar day's own walls:
   `GridCut.daySpans`/`dayCovered`, the partition laws over the days and the `Cal` lemma that a
   zone's midnights rise (`MidnightCut.lean`).
   ===================================================================== -/
#print axioms Lime.GridCut.the_call_past_midnight_is_its_days_wall
#print axioms Lime.Cal.spansFrom_off_mem
#print axioms Lime.Cal.Span.hit_sec
#print axioms Lime.Cal.localHits_sec
#print axioms Lime.Cal.gapHit_some
#print axioms Lime.Cal.instantOf_sec
#print axioms Lime.Cal.instantOf_midnights_rise
#print axioms Lime.Cal.chicago_midnights_rise
#print axioms Lime.Cal.a_date_line_table_is_not_near
#print axioms Lime.GridCut.mem_daySpans_iff
#print axioms Lime.GridCut.mem_dayCovered_iff
#print axioms Lime.GridCut.one_le_clipDays
#print axioms Lime.GridCut.last_at_or_below
#print axioms Lime.GridCut.a_second_of_the_clip_is_in_a_days_part
#print axioms Lime.GridCut.midnights_rise_over
#print axioms Lime.GridCut.a_second_is_in_one_days_part
#print axioms Lime.GridCut.a_days_part_is_inside_the_clip
#print axioms Lime.GridCut.the_grid_draws_every_second_of_the_clip_once_day_by_day
#print axioms Lime.GridCut.a_second_is_covered_iff_a_wall_of_its_own_day_covers_it
#print axioms Lime.GridCut.the_grid_cuts_every_second_once_in_a_zone_near_utc
#print axioms Lime.GridCut.the_cut_inside_its_day_is_unchanged
#print axioms Lime.GridCut.the_call_past_midnight_is_its_days_wall_in_chicago
#print axioms Lime.GridCut.the_day_by_day_cut_is_run
-- =====================================================================
-- APPENDED W-41 TRACK K (stage 6): D78 (a running record's start after `now` is planned from
-- `now`, as fork 4748911 plans it), D80 (the planner request refuses by name a day whose
-- evening runs past the calendar and a candidate whose wire `ci` is not the plan's, P71/P72)
-- and D81 gap 3902 (the running estimate, break and worked minutes widen to the host's width).
-- Fourteen audit lines LEFT with the names they audited, each refuted, renamed or deleted:
--   Planner.mkActive?_refuses_a_start_after_now      -> mkActive?_refuses_a_start_after_now_is_refuted
--   Planner.mkActive?_refuses_an_estimate_past_the_day -> mkActive?_reads_an_estimate_past_the_day
--                                                        (+ mkActive?_refuses_an_estimate_past_the_width)
--   Planner.mkBreak?_refuses_a_break_longer_than_a_day -> mkBreak?_reads_a_break_past_the_day
--                                                        (+ mkBreak?_refuses_a_break_past_the_width)
--   Planner.mkInterrupt?_refuses_a_start_after_now, Planner.mkInterrupt?_accepts -> DELETED with
--     the constructor (D78 left it no bound); PlanWire.readInterrupt_accepts_a_start_after_now
--   PlanWire.readActive_refuses_a_start_after_now   -> PlanWire.readActive_accepts_a_start_after_now
--   PlanWire.readActive_refuses_an_estimate_past_the_day -> readActive_reads_an_estimate_past_the_day
--                                                        (+ readActive_refuses_an_estimate_past_the_width)
--   PlanWire.readBreak_refuses_a_break_longer_than_a_day -> readBreak_refuses_a_break_past_the_width
--   PlanWire.readInterrupt_refuses_a_start_after_now -> PlanWire.readInterrupt_accepts_a_start_after_now
--   Planner.the_extension_agrees_when_the_estimate_fits_a_day -> ..._fits_the_width (implies it)
--   Planner.the_extension_disagrees_past_a_day      -> ..._past_the_width (refuted at the day)
--   Planner.a_worked_reading_past_a_day_is_refused  -> a_worked_reading_past_the_width_is_refused
--   Planner.the_worked_minutes_bound_is_run         -> the_worked_minutes_bound_is_run_at_the_width
--   PlanWire.readOptWorked_refuses_a_reading_past_the_day -> ..._past_the_width
-- And Goals.plan_places_no_demanding_block_after_wind_down LEFT Goals.lean: discharged as
-- written over every request PlanWire.planReqOf accepts (PlannerWit's W-41 block), on
-- PlanCheck.plan_places_no_demanding_block_after_wind_down restated over D80 (b)'s clause.
-- =====================================================================
#print axioms Lime.Planner.mkActive?_refuses_an_estimate_past_the_width
#print axioms Lime.Planner.mkActive?_reads_an_estimate_past_the_day
#print axioms Lime.Planner.mkActive?_refuses_a_start_after_now_is_refuted
#print axioms Lime.Planner.a_worked_reading_past_the_width_is_refused
#print axioms Lime.Planner.the_worked_minutes_bound_is_run_at_the_width
#print axioms Lime.Planner.PlanReq.the_reservation_reaches_at_most_one_block_past_its_start
#print axioms Lime.Planner.plan_reserves_one_block_at_a_time_when_the_block_started_by_now
#print axioms Lime.Planner.PlanReq.no_lead_without_a_running_block
#print axioms Lime.Planner.PlanReq.no_lead_for_a_start_by_now
#print axioms Lime.Planner.a_worked_reading_within_the_width_is_read
#print axioms Lime.Planner.PlanReq.windDown_inside_the_calendar
#print axioms Lime.Planner.PlanReq.dayEnd_and_window_inside_the_calendar
#print axioms Lime.Planner.PlanReq.the_wind_down_row_is_not_clamped
#print axioms Lime.Planner.PlanReq.an_evening_past_the_calendar_fails_the_clause
#print axioms Lime.Planner.PlanReq.ciDisagreement_eq_none_iff
#print axioms Lime.Planner.PlanReq.a_candidates_ci_is_its_items_where_the_wire_agrees
#print axioms Lime.Planner.PlanReq.a_ci_disagreement_names_a_candidate
#print axioms Lime.Planner.the_extension_agrees_when_the_estimate_fits_the_width
#print axioms Lime.Planner.the_extension_disagrees_past_the_width
#print axioms Lime.PlanWire.readActive_accepts_a_start_after_now
#print axioms Lime.PlanWire.readActive_refuses_an_estimate_past_the_width
#print axioms Lime.PlanWire.readActive_reads_an_estimate_past_the_day
#print axioms Lime.PlanWire.readInterrupt_accepts_a_start_after_now
#print axioms Lime.PlanWire.readOptWorked_refuses_a_reading_past_the_width
#print axioms Lime.PlanWire.planReqRefusal_names_an_evening_past_the_calendar
#print axioms Lime.PlanWire.planReqRefusal_names_a_candidate_whose_ci_disagrees
#print axioms Lime.PlanWire.planReqRefusal_of_a_request_paying_both
#print axioms Lime.PlanWire.planReqRefusal_eq_none_pays_both
#print axioms Lime.PlanWire.planReqOf_pays_the_evening_and_the_ci
#print axioms Lime.PlanWire.the_d80_refusals_spell_themselves
#print axioms Lime.PlanWire.readOptInterrupt_reads_the_interruption
#print axioms Lime.PlanCheck.candPlanView_ci_is_planCi
#print axioms Lime.PlanCheck.ciDisagreement_eq_none_of_candsAgree
#print axioms Lime.PlanCheck.plan_places_no_demanding_block_after_wind_down_on_a_request_paying_d80
#print axioms Lime.PlannerWit.startAfterNowRun_resumes_ok
#print axioms Lime.PlannerWit.a_start_after_now_is_planned_from_now_as_the_fork_plans_it
#print axioms Lime.PlannerWit.plan_reserves_one_block_at_a_time_without_the_lead_is_refuted_by_d78
#print axioms Lime.PlannerWit.an_interruption_after_now_is_drawn_as_the_fork_draws_it
#print axioms Lime.PlannerWit.the_last_evening_is_refused_by_name
#print axioms Lime.PlannerWit.the_conference_wire_is_refused_by_name
#print axioms Lime.PlannerWit.the_eve_pays_both_of_d80s_clauses
#print axioms Lime.PlannerWit.plan_places_no_demanding_block_after_wind_down_on_every_request_the_decoder_accepts
#print axioms Lime.PlannerWit.an_extension_past_the_day_agrees
#print axioms Lime.PlannerWit.aBlockPastTheWidth_is_past_the_width
#print axioms Lime.PlannerWit.the_start_after_now_log_holds_the_open_block

/- ===================================================================
   APPENDED 2026-10-01: stage 6 (the planner), run W-41, REPAIR STEP —
   E1's lead on the running row alone (README gap 4136), and the
   what-if's request paying D80's two clauses (gap 4147).
   =================================================================== -/
#print axioms Lime.Planner.plan_reserves_one_block_at_a_time_off_the_running_row
#print axioms Lime.Planner.PlanReq.the_whatif_keeps_the_evening
#print axioms Lime.Planner.PlanReq.growing_keeps_the_ci_agreement
#print axioms Lime.Planner.PlanReq.the_whatif_request_pays_d80

-- ===========================================================================
-- APPENDED 2026-10-02 (stage 6, run W-42, track G — owner D83, README gap 32 closed: the
-- kernel reads as a separator exactly what the host reads).  Thirty-eight new theorems (among the
-- last five, the D40 witnesses `setLeadWord`'s touched body, the new `Field.afterSlots` and the
-- touched `kerrName` needed -- the last two in PlannerWit.lean -- and P80's positive witness), and
-- sixteen RETIRED names whose lines are deleted above, each refuted where it stood or restated
-- under a new name (README "W-42 track G", the retirement table): a_line_with_a_bracket_is_not_a_bare_item,
-- bareOk_all, bareOk_mk, boxAt_box, editE_ok_of_tabless, editE_refuses_a_tabbed_line,
-- edit_of_a_tabbed_line_is_refused, est_of_a_tabbed_line_is_refused, parseBody_bare_head,
-- parseBody_bare_of_noBox, parseBody_boxed, the_tab_guard_is_not_vacuous, tokBare_head,
-- tokBare_sep, unsetE_refuses_a_tabbed_line, unset_of_a_tabbed_line_is_refused.
-- ===========================================================================
#print axioms Lime.isSp_eq_whiteSpace
#print axioms Lime.isSp_of_isIndent
#print axioms Lime.isSp_of_digit
#print axioms Lime.the_separator_is_white_space
#print axioms Lime.isSp_of_isBoxEnd
#print axioms Lime.isBoxEnd_space
#print axioms Lime.boxAt_box_of_end
#print axioms Lime.a_box_needs_its_end
#print axioms Lime.bareOk_iff
#print axioms Lime.parseBody_cons
#print axioms Lime.parseBody_boxed_of_end
#print axioms Lime.parseBody_bare_of_no_box_after_seps
#print axioms Lime.endsBox_of_head_sep
#print axioms Lime.round_trip_B_without_the_box_end_is_refuted
#print axioms Lime.setEstIn_head_sep
#print axioms Lime.insertBeforeId_endsBox
#print axioms Lime.Field.isSp_of_printable
#print axioms Lime.Field.isSp_of_isNameC
#print axioms Lime.Field.isSp_of_isKeyC
#print axioms Lime.Field.setKeyIn_head_sep
#print axioms Lime.Field.the_title_key_is_the_hosts_span
#print axioms Lime.Field.endBox_words
#print axioms Lime.Field.endBox_filterMap_word
#print axioms Lime.Field.toksWf_endBox
#print axioms Lime.Field.endBox_endsBox
#print axioms Lime.Field.idWords_endBox
#print axioms Lime.a_line_spaced_from_its_box_is_boxed
#print axioms Lime.a_bracket_in_a_bare_line_is_title_text
#print axioms Lime.a_tab_separates_the_id
#print axioms Lime.editE_ok
#print axioms Lime.Field.setLeadToks_head_sep
#print axioms Lime.a_tabbed_line_is_edited_as_the_host_edits_it
#print axioms Lime.setLeadWord_writes_the_leading_word
#print axioms Lime.the_title_key_of_a_boxed_line_skips_its_slots
#print axioms Lime.an_unset_keeps_the_box_ended
#print axioms Lime.PlannerWit.kerrName_names_each_refusal
#print axioms Lime.PlannerWit.kerrName_injective
/- ===================================================================
   APPENDED 2026-10-02: stage 6 (the planner), run W-42, TRACK S —
   the owner's D82 (README gaps 4150 and 4152): §8.2's day with every
   view it reads more than once computed once (`PlanOnce.lean`), and
   the `@[csimp]` lemma that makes `PlanWire.runPlanner` run it.
   =================================================================== -/
#print axioms Lime.Planner.walkRePlace_nil
#print axioms Lime.Planner.walkRePlace_cons
#print axioms Lime.Planner.walkRePlace_eq
#print axioms Lime.Planner.walkDefer_nil
#print axioms Lime.Planner.walkDefer_cons
#print axioms Lime.Planner.walkDefer_eq
#print axioms Lime.Planner.groupFitsAt_eq
#print axioms Lime.Planner.assignStepAt_eq
#print axioms Lime.Planner.Memo.of_eq
#print axioms Lime.Planner.walkRePlace_at
#print axioms Lime.Planner.deferOneAt_eq
#print axioms Lime.Planner.deferOneAt_takes_the_lowest_free
#print axioms Lime.Planner.dayPlanFrom_spec
#print axioms Lime.Planner.dayPlanOnce_eq
#print axioms Lime.Planner.dayPlan_eq_dayPlanOnce
/- ===================================================================
   APPENDED 2026-10-02: stage 6, run W-42, TRACK R — the owner's D87, a
   break taken inside a block is not block time (README gap 4137, parity
   P81).  `Replay.brkFx` and its laws, C5's `arm_split` and W2's
   `arm_mi`/`stepWith_mi` restated with their old statements refuted by
   name, the replay's break witnesses, and PlannerWit's section 31.
   =================================================================== -/
#print axioms Lime.Replay.arm_split_of_not_brk
#print axioms Lime.Replay.brkFx_blockOnly
#print axioms Lime.Replay.brkFx_machine
#print axioms Lime.Replay.brkFx_obs
#print axioms Lime.Replay.a_break_inside_a_stopped_block_is_not_block_time
#print axioms Lime.Replay.a_done_after_a_break_credits_its_minutes_and_splits_its_block
#print axioms Lime.Replay.the_open_block_restarts_at_the_breaks_end
#print axioms Lime.Replay.a_break_with_no_actual_nets_its_planned_minutes
#print axioms Lime.Replay.a_break_while_the_block_is_paused_changes_nothing
#print axioms Lime.Replay.arm_split_as_c5_stated_it_is_refuted
#print axioms Lime.Seal.brkFx_mi
#print axioms Lime.Seal.arm_mi_of_not_brk
#print axioms Lime.Seal.arm_mi_as_w2_stated_it_is_refuted
#print axioms Lime.Seal.stepWith_mi_as_w2_stated_it_is_refuted
#print axioms Lime.PlannerWit.insideBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_inside_break_day_splits_the_block_at_the_break
#print axioms Lime.PlannerWit.insideOpenBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_open_row_starts_at_the_breaks_end

/-
   APPENDED 2026-10-03: stage 6, run W-42, the REPAIR step — a signed `ci:` and
   `every:month:` value read as the host's `u8::from_str` reads it (README gaps
   4162 and 4330), `add`'s title guards over every separator (gaps 4164 and 4337),
   and the separator's second definition deleted (gaps 4161, 4324 and 4336:
   Lime.LogStamp.isRustSpace_eq_isSp and Lime.Log.isRustSpace_digit are retired,
   their lines removed above; `isSp_of_digit` is the latter's statement over `isSp`).
-/
#print axioms Lime.readRustNat_of_head
#print axioms Lime.readRustNat_digitsOf
#print axioms Lime.readRustNat_reads_one_plus
#print axioms Lime.Field.ci_reads_a_signed_value
#print axioms Lime.Field.rule_month_signed
#print axioms Lime.parseCmd_refuses_every_separator_at_a_titles_edge

/-
   APPENDED 2026-10-03: stage 6, run W-43, TRACK K — the owner's D92 (README gap 4241,
   parity P85): a break that runs INTO a block's start is not block time.  Two lines
   removed above: Lime.PlannerWit.plan_places_no_block_over_a_break_as_stage_6_wrote_it_is_refuted
   (deleted; its goal is back in Goals.lean, gap 4362) and
   Lime.Replay.a_break_logged_before_its_blocks_start_is_not_netted (refuted and renamed:
   `…_is_not_netted_is_refuted` and `…_is_netted` below).
-/
#print axioms Lime.Replay.brkFx_brk
#print axioms Lime.Replay.closePause_brk
#print axioms Lime.Replay.cut_brk
#print axioms Lime.Replay.a_break_logged_before_its_blocks_start_is_not_netted_is_refuted
#print axioms Lime.Replay.a_break_logged_before_its_blocks_start_is_netted
#print axioms Lime.Replay.an_open_block_begun_inside_a_break_runs_from_its_end
#print axioms Lime.Replay.a_done_begun_inside_a_break_credits_its_minutes_and_is_drawn_after_it
#print axioms Lime.Replay.an_unpause_inside_a_break_restarts_the_clock_at_its_end
#print axioms Lime.Replay.a_resume_inside_a_break_restarts_the_clock_at_its_end
#print axioms Lime.Replay.a_break_the_start_ended_nets_nothing
#print axioms Lime.Seal.a_machine_holds_its_last_breaks_end
#print axioms Lime.PlannerWit.intoBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_into_break_day_keeps_its_block_off_the_break
#print axioms Lime.PlannerWit.openIntoBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_open_row_begun_inside_a_break_starts_at_its_end

/-
   APPENDED 2026-10-03: stage 6, run W-43, TRACK G — an item line reads a date through
   chrono's readers (README gap 4346): `Log.instDate?`, `Field.parseDT` (`parse_datetime`) and
   `Field.parseTime` (`parse_time`), with chrono's item readers MOVED to Line.lean.  Ten
   stage-3 bridge and edit laws that held because the line refused a signed year are refuted
   by one and restated beside it; their lines are removed above.  And gap 4344: seven laws
   over W-42's narrower CanonicalItem carry the suffix _box_ended (their lines renamed above).
-/
#print axioms Lime.LogStamp.trimWs_cons
#print axioms Lime.LogStamp.lit_cons
#print axioms Lime.LogStamp.numIn_digits
#print axioms Lime.LogStamp.numIn_ok_range
#print axioms Lime.Log.utf8Len_of_ascii
#print axioms Lime.Log.utf8Size_of_digit
#print axioms Lime.Log.isLeap_cycle
#print axioms Lime.Log.chronoDateValid_of_valid
#print axioms Lime.Log.valid_of_chronoDateValid
#print axioms Lime.Log.dayOfParts?_some
#print axioms Lime.Log.chronoYear_le_unless_plus
#print axioms Lime.Log.chronoYmd_year
#print axioms Lime.Log.dayOfParts?_of_valid
#print axioms Lime.Field.renderClock_utf8Len
#print axioms Lime.Field.parse_render_time
#print axioms Lime.Field.renderDate_utf8Len
#print axioms Lime.Field.the_line_reads_back_the_date_it_writes
#print axioms Lime.Field.parseDT_render
#print axioms Lime.Field.dayWf_of_le
#print axioms Lime.Field.instDate?_dayWf_unless_signed
#print axioms Lime.Field.parseDT_wf_unless_signed
#print axioms Lime.Field.parseMoment_wf_unless_signed
#print axioms Lime.Field.parseDT_wf_is_refuted
#print axioms Lime.Field.parseMoment_wf_is_refuted
#print axioms Lime.Field.parseEnd_orders_its_ends
#print axioms Lime.Field.parseEnd_spec_is_refuted
#print axioms Lime.Field.parseInterval_orders_its_ends
#print axioms Lime.Field.parseInterval_wf_unless_its_end_is_past_9999
#print axioms Lime.Field.parseInterval_spec_is_refuted
#print axioms Lime.Field.parseInterval_wf_unless_rollover_is_refuted
#print axioms Lime.Field.parseWindow_wf_unless_its_end_is_past_9999
#print axioms Lime.Field.parseWindow_wf_unless_rollover_is_refuted
#print axioms Lime.Field.the_line_reads_a_signed_year_as_chrono_does
#print axioms Lime.Field.a_date_before_year_one_is_no_date_on_the_line
#print axioms Lime.Field.the_line_refuses_a_date_chrono_refuses
#print axioms Lime.Field.parseTime_is_chronos_not_rfc3339s
#print axioms Lime.editValOf_due_refuses_only_a_bad_value_or_a_signed_year
#print axioms Lime.editValOf_due_refuses_only_what_parseMoment_refuses_is_refuted
#print axioms Lime.editValOf_waiting_refuses_only_a_bad_value_or_a_signed_year
#print axioms Lime.editValOf_waiting_refuses_only_what_parseDate_refuses_is_refuted
#print axioms Lime.editValOf_interval_refuses_only_a_bad_value_or_an_end_past_9999
#print axioms Lime.editValOf_interval_refuses_only_a_bad_value_or_the_rollover_is_refuted
#print axioms Lime.editValOf_window_refuses_only_a_bad_value_or_an_end_past_9999
#print axioms Lime.editValOf_window_refuses_only_a_bad_value_or_the_rollover_is_refuted
#print axioms Lime.a_signed_year_is_edited_as_the_host_reads_it
#print axioms Lime.Field.readNat_foldl_digits
#print axioms Lime.Field.readNat_all_digits
#print axioms Lime.Log.chronoYmd_digits
#print axioms Lime.Log.chronoHM_digits
#print axioms Lime.Log.utf8Len_of_dateish
#print axioms Lime.Field.parseDate_shape
#print axioms Lime.Field.parseClock_shape
#print axioms Lime.Field.chronoYmd_of_parseDate
#print axioms Lime.Field.instDate?_is_chronos_parse_date
#print axioms Lime.Field.parseDT_is_chronos_parse_datetime
#print axioms Lime.Field.parseTime_is_chronos_parse_time
#print axioms Lime.LogStamp.trimWs_eq_dropWhile

-- =====================================================================
-- APPENDED 2026-10-03: stage 6 (the planner), run W-44, TRACK K — the owner's D94 (README gaps 4361, 4506 and
-- 4362; parity P92): every break on a block's ledger days is netted (`Replay.Machine.brks`, Replay.restartAt,
-- Replay.closeSub, `Replay.openOf`; the middle two deleted at W-47 for `Replay.settle`), D94's bound (`Replay.pruneBrks`), and the last goal refuted on a world with one
-- reading.  One line removed: Replay.a_break_logged_before_a_start_but_begun_after_it_is_not_netted, refuted and
-- renamed `…_is_not_netted_is_refuted` (D5).
-- =====================================================================
#print axioms Lime.PlannerWit.aheadBreakRun_resumes_ok
#print axioms Lime.PlannerWit.the_ahead_break_day_keeps_its_block_off_the_break
#print axioms Lime.PlannerWit.the_open_row_is_read_past_a_break_held_ahead_of_its_clock
#print axioms Lime.Replay.a_break_logged_before_a_start_but_begun_after_it_is_netted
#print axioms Lime.Replay.a_break_logged_before_a_start_but_begun_after_it_is_not_netted_is_refuted
#print axioms Lime.Replay.a_break_on_the_ledger_day_before_a_running_block_stops_no_clock
#print axioms Lime.Replay.a_break_on_the_ledger_day_before_the_blocks_is_not_netted
#print axioms Lime.Replay.an_unpause_inside_an_earlier_break_nets_every_break_held
#print axioms Lime.Replay.a_resume_inside_an_earlier_break_nets_every_break_held
#print axioms Lime.Replay.a_start_inside_an_earlier_break_nets_every_break_held
#print axioms Lime.Replay.a_start_inside_overlapping_breaks_runs_from_their_union_end
#print axioms Lime.Replay.countP_lt_of_witness
#print axioms Lime.Replay.liftGo_cases
#print axioms Lime.Replay.liftGo_uncovered
#print axioms Lime.Replay.lift_uncovered
#print axioms Lime.Replay.mem_pruneBrks
#print axioms Lime.Replay.mem_spansFor
#print axioms Lime.Replay.nextStart_covers
#print axioms Lime.Replay.nextStart_spec
#print axioms Lime.Replay.piecesGo_avoids
#print axioms Lime.Replay.piecesGo_starts
#print axioms Lime.Replay.pruneBrks_drops_a_break_past_the_bound
#print axioms Lime.Replay.spansFor_end
#print axioms Lime.Replay.the_open_block_is_read_past_a_break_held_ahead_of_its_clock
#print axioms Lime.Replay.worked_minutes_floor_each_subsegment_as_c3_stated_it_is_refuted
#print axioms Lime.Replay.worked_minutes_floor_each_subsegment_with_no_break_held
#print axioms Lime.Seal.a_machine_holds_the_end_of_every_break_it_holds
#print axioms Lime.Seal.a_replay_holds_breaks_within_maxKeepDays_of_the_newest
#print axioms Lime.Seal.arm_brks
#print axioms Lime.Seal.foldl_brks_within
#print axioms Lime.Seal.foldl_maxDay_le
#print axioms Lime.Seal.le_foldl_maxDay
#print axioms Lime.Seal.pruneBrks_within
#print axioms Lime.Seal.stepWith_brks_within
#print axioms Lime.Seal.pruneBrks_is_bounded_by_maxKeepDays
#print axioms Lime.Seal.the_compiled_resume_reads_its_open_block_through_openOf

/-
   APPENDED 2026-10-04: stage 6, run W-44, THE REPAIR — one line removed above:
   Lime.PlannerWit.plan_places_no_block_over_a_break_as_stage_6_wrote_it_is_refuted (deleted;
   the world it stood on reads the break's span two ways, gap 4520's closed half, and the goal
   is back in Goals.lean, README gap 4611).  Added: the wall rule's two new witnesses (README
   gaps 4550 and 4610) and the seam's since-break anchor read through `brkEnd` (gap 4550, P97).
-/
#print axioms Lime.Replay.seam_since_break_is_brkEnd
#print axioms Lime.Replay.a_planned_only_break_anchors_since_break_at_its_planned_end
#print axioms Lime.WallTimer.a_resume_ends_the_interruption_and_not_the_users_pause
#print axioms Lime.WallTimer.a_break_across_the_walls_start_does_not_stand_for_the_users_stop

/-
   APPENDED 2026-10-04: stage 6, run W-45, TRACK D — the day's rows in fork `emit_segments`'
   push order where two rows tie (README gap 4623): the reservation before the routines and
   the evening last (`Planner.dayRows`), the list a permutation of the one it was, and the
   witness a block running past bed to midnight holds.
-/
#print axioms Lime.Planner.dayRows_list_perm
#print axioms Lime.Planner.the_reservation_precedes_the_evening_in_the_list
#print axioms Lime.PlannerWit.the_running_block_precedes_the_sleep_it_ties_with

/-
   APPENDED 2026-10-04: stage 6, run W-45, TRACK Q — README gap 3583's property as a law over the
   planner's own reading (`TodayWhole.lean`, a module of theorems only): the planner's day record is
   the run answer's reading of today, and on a resumed run it is the whole log's replay's.
-/
#print axioms Lime.Planner.PlanReq.todayRecord_is_the_answers_reading
#print axioms Lime.Planner.PlanReq.todayRecord_on_a_resumed_run_is_the_whole_logs

/-
   APPENDED 2026-10-05: stage 6, run W-46, TRACK K — the owner's D105 (README "Stage 6 — W-46 track K",
   gaps 1034, 1085, 4740; parity P100): `lime break` logs a `break_start`, the machine holds the running break
   (`Replay.Machine.brkOpen`) until a `break` line ends it, the facts and the checkpoint carry it, and its day
   holds the ledger day.
-/
#print axioms Lime.Replay.closePause_brkOpen
#print axioms Lime.Replay.cut_brkOpen
#print axioms Lime.Replay.doneClose_brkOpen
#print axioms Lime.Replay.brkFx_brkOpen
#print axioms Lime.Replay.the_break_start_arm_opens_the_running_break
#print axioms Lime.Replay.the_break_start_has_no_completion_arm
#print axioms Lime.Replay.a_break_start_is_the_running_break
#print axioms Lime.Replay.a_break_line_ends_the_running_break
#print axioms Lime.Replay.a_break_line_ends_the_running_break_whatever_its_stamp_as_d105_stated_it_is_refuted
#print axioms Lime.Replay.an_undone_break_start_leaves_no_break_running
#print axioms Lime.Replay.an_undone_break_line_leaves_the_break_running
#print axioms Lime.Replay.a_second_break_start_replaces_the_first
#print axioms Lime.Replay.a_break_start_is_not_an_unknown_event
#print axioms Lime.Replay.a_running_break_moves_no_clock
#print axioms Lime.Seal.a_running_break_holds_the_ledger_day
#print axioms Lime.Seal.openBreak_reads_state
#print axioms Lime.Seal.answer_openBreak
#print axioms Lime.Seal.arm_brkOpen

/-
   APPENDED 2026-10-05: stage 6, run W-46, TRACK H — README gap 4751: three refusals of the planner
   section no request reaches (`PlanWire.lean`, the section "Three refusals no request reaches"),
   and the lemmas they stand on.
-/
#print axioms Lime.PlanWire.except_mapM_length
#print axioms Lime.PlanWire.readCands_within_the_cap
#print axioms Lime.PlanWire.runCapZP_parts
#print axioms Lime.PlanWire.runRowsP_parts
#print axioms Lime.PlanWire.mkInput?_keeps_the_zone_the_day_and_the_walls
#print axioms Lime.PlanWire.readCapacityZ_walls
#print axioms Lime.PlanWire.readCapacityZ_needs_a_replay
#print axioms Lime.PlanWire.within53A_ok
#print axioms Lime.PlanWire.logOpZ_run_iff_facts
#print axioms Lime.PlanWire.logSectionWith_run_iff_facts
#print axioms Lime.PlanWire.planReqRefusal_names
#print axioms Lime.PlanWire.planReqOf_never_refuses_what_the_capacity_section_excludes

/-
   APPENDED 2026-10-05: stage 6, run W-46, TRACK H, resumed after a cut-off — README gaps 4795 and
   4793: the assembler asks D80 before it reads the routines (`planReqOf`), so a routine word the two
   readers key apart is P72's refusal by P72's name; `routineRefused pastTheHorizon` answered to no
   section the reader accepts; `routineRefused unknownItem` to no request whose routines each name a
   candidate it carries; and the lemmas they stand on.
-/
#print axioms Lime.PlanWire.planReqRefusal_ignores_the_routines
#print axioms Lime.PlanWire.planReqOf_refuses_only_by_d80_or_a_routine
#print axioms Lime.PlanWire.except_mapM_mem
#print axioms Lime.PlanWire.except_mapM_error
#print axioms Lime.PlanWire.secWithin_ok
#print axioms Lime.PlanWire.readRoutine_closes_inside_the_calendar
#print axioms Lime.PlanWire.readPlannerSection_routines_close_inside_the_calendar
#print axioms Lime.PlanWire.mkRoutines?_past_the_horizon
#print axioms Lime.PlanWire.mkRoutines?_unknown_item
#print axioms Lime.PlanWire.planReqOf_never_refuses_past_the_horizon
#print axioms Lime.PlanWire.planReqOf_never_refuses_an_item_a_candidate_names

/-
   APPENDED 2026-10-05: stage 6, run W-46, THE REPAIR — README gap 4793 (the W-46 switch's gap 4843, an R3
   BLOCKER): a planner-section refusal yields to D80 (a), asked of the capacity section's parts (`eveningFirst`), so
   a day whose evening runs past the calendar reaches the host by P71's name.
-/
#print axioms Lime.PlanWire.eveningFirst_names_only_the_evening
#print axioms Lime.PlanWire.eveningFirst_probe_passes
#print axioms Lime.PlanWire.eveningFirst_probe_of_a_request_passes
#print axioms Lime.PlanWire.eveningFirst_passes_what_planReqOf_builds
#print axioms Lime.PlanWire.an_evening_eveningFirst_refuses_is_never_planned
#print axioms Lime.PlanWire.runPlanner_names_an_evening_past_the_calendar_over_a_section_refusal

/-
   APPENDED 2026-10-05: stage 6, run W-46, THE AUDIT'S REPAIR — README gap 4905: the narrowed law's old
   statement (`runPlanner_refuses_a_section_the_decoder_refuses` before the W-46 repair) refuted wherever the
   order fires, so the narrowing is a pair of theorems and not an FFI test alone (D5).
-/
#print axioms Lime.PlanWire.runPlanner_refuses_a_section_the_decoder_refuses_as_written_fails_where_the_order_fires

/-
   APPENDED 2026-10-06: stage 6, run W-47, TRACK K — the owner's D99 (README "Stage 6 — W-47 track K", gap 4520a;
   parity P104): the open block holds its own idle spans and the pieces it drew, and `Replay.settle` re-draws it at
   every mark that moves what its clock nets (`Replay.redraw`, `DayOp.unsegment`), so a `break`, `pause` or
   `interrupt` logged out of its stamp's order is netted where it lies; a cut credits the pieces it is left with
   (`Replay.cutPieces`).  The window machinery reads the index at the new pieces' starts (`Seal.settleReads`,
   `Seal.cutReads`).  Twenty-six lines removed, each theorem's subject deleted with D99 (closeSub, restartAt,
   lastEndAfter, the old resumeBlock) and its successor appended here — the table is the README block's §3;
   brkFx_of_stopped is refuted and renamed with its narrowing beside it (D5).
-/
#print axioms Lime.Replay.a_break_logged_behind_a_closed_stretch_is_netted
#print axioms Lime.Replay.an_interruption_logged_behind_a_closed_stretch_is_netted
#print axioms Lime.Replay.an_unpause_stamped_before_its_pause_idles_nothing
#print axioms Lime.Replay.a_pause_logged_behind_a_closed_stretch_is_netted
#print axioms Lime.Replay.a_pause_stamped_before_the_start_is_not_the_blocks
#print axioms Lime.Replay.a_stop_stamped_before_a_logged_pause_credits_to_the_stop
#print axioms Lime.Replay.atEq_iff
#print axioms Lime.Replay.closePauseM_keeps
#print axioms Lime.Replay.closePauseM_pending
#print axioms Lime.Replay.cut_avoids_every_span_it_nets
#print axioms Lime.Replay.redraw_draws_its_spans
#print axioms Lime.Replay.redraw_obs
#print axioms Lime.Replay.redraw_plain
#print axioms Lime.Replay.redraw_sleptOk
#print axioms Lime.Replay.runFrom_step_ge
#print axioms Lime.Replay.runFrom_uncovered
#print axioms Lime.Replay.settle_avoids_every_span_it_nets
#print axioms Lime.Replay.settle_block_isSome
#print axioms Lime.Replay.settle_duration
#print axioms Lime.Replay.settle_energy
#print axioms Lime.Replay.settle_fx_obs
#print axioms Lime.Replay.settle_keeps
#print axioms Lime.Replay.settle_machines
#print axioms Lime.Replay.settle_obs
#print axioms Lime.Replay.settle_pendLines
#print axioms Lime.Replay.settle_plain
#print axioms Lime.Replay.settle_runs_outside_every_span_it_nets
#print axioms Lime.Replay.settle_sleptOk
#print axioms Lime.Replay.settle_then_machine_obs
#print axioms Lime.Replay.the_open_blocks_banked_piece_is_drawn
#print axioms Lime.Replay.a_paused_stretch_is_drawn_between_the_blocks_pieces
#print axioms Lime.Replay.an_open_block_a_pause_or_an_interruption_stopped_is_not_running
#print axioms Lime.Replay.redraw_of_its_own_pieces_writes_nothing
#print axioms Lime.Replay.redraw_of_its_own_pieces_writes_nothing_run
#print axioms Lime.Replay.atEq_run
#print axioms Lime.Seal.stepLows_run
#print axioms Lime.Replay.two_breaks_logged_out_of_order_are_each_netted
#print axioms Lime.Replay.worked_minutes_of_the_open_block_floor_each_piece
#print axioms Lime.Seal.arm_settled_brkOpen
#print axioms Lime.Seal.arm_settled_interrupt
#print axioms Lime.Seal.arm_settled_lastCut
#print axioms Lime.Seal.blockPaused_mi
#print axioms Lime.Seal.closePauseM_brks
#print axioms Lime.Seal.closePauseM_interrupt
#print axioms Lime.Seal.closePauseM_mi
#print axioms Lime.Seal.cutReads_mi
#print axioms Lime.Seal.heldBrk_mi
#print axioms Lime.Seal.interruptMachine_mi
#print axioms Lime.Seal.mem_machineInstants
#print axioms Lime.Seal.mi_of_block
#print axioms Lime.Seal.piece_start_mi
#print axioms Lime.Seal.redraw_congr
#print axioms Lime.Seal.redrawReads_mi
#print axioms Lime.Seal.resumed_mi
#print axioms Lime.Seal.runFrom_cases
#print axioms Lime.Seal.settle_congr
#print axioms Lime.Seal.settle_mi
#print axioms Lime.Seal.settleReads_mi
#print axioms Lime.Seal.startedMachine_mi
#print axioms Lime.Seal.stepQueries_congr
#print axioms Lime.Seal.unpaused_mi
#print axioms Lime.Replay.brkFx_with_no_block_open
#print axioms Lime.Replay.brkFx_of_stopped_as_d92_stated_it_is_refuted

/-
   APPENDED 2026-10-06: stage 6, run W-47, TRACK K — the owner's D100 (README "Stage 6 — W-47 track K" §11, gap 4520b;
   parity P105): the machine holds the blocks it closed (`Replay.Closed`, `Replay.pruneClosed`), and a `break` logged
   after one closed, stamped inside it, nets it (`Replay.netClosed`): its pieces re-drawn around the break, and what the
   break took off its credit, its item's minutes and its `done`'s duration observation (`DayOp.net`, `Replay.netDur`).
   The conservation invariant carries the held blocks (`Replay.Conserves`, `Replay.HeadOk`); the window
   reads the index where a late break re-draws a held block (`Seal.closedReads`) and the checkpoint codec carries the
   held blocks and the duration nets (`Seal.cMachine`, `Seal.cDayAcc`).  Two lines removed: Replay.conserves_doneClose,
   restated over the held blocks as `Replay.conserves_doneClosed`, and
   PlannerWit.the_mid_break_day_lays_a_block_across_a_break, false since D100 at the decoder's own day and restated
   as `PlannerWit.the_mid_break_day_cuts_its_block_around_the_break`, its old statement kept at a run the decoder no
   longer builds (`PlannerWit.the_mid_break_day_as_drawn_before_d100_lays_a_block_across_a_break`).
-/
#print axioms Lime.PlannerWit.the_core_seven_hold_on_the_mid_break_day_by_the_lift
#print axioms Lime.PlannerWit.the_mid_break_day_as_drawn_before_d100_lays_a_block_across_a_break
#print axioms Lime.PlannerWit.the_mid_break_day_cuts_its_block_around_the_break
#print axioms Lime.PlannerWit.the_paying_past_at_the_mid_break_request
#print axioms Lime.Replay.bal_apply_net
#print axioms Lime.Replay.brkFx_with_no_block_open_as_d99_stated_it_is_refuted
#print axioms Lime.Replay.brkFx_with_nothing_open_or_held
#print axioms Lime.Replay.Ci6.fifths_ge
#print axioms Lime.Replay.Ci6.fifths_sub
#print axioms Lime.Replay.Ci6.get_le_sum
#print axioms Lime.Replay.Ci6.sum_sub
#print axioms Lime.Replay.closePauseM_closed
#print axioms Lime.Replay.conserves_after
#print axioms Lime.Replay.conserves_doneClosed
#print axioms Lime.Replay.conserves_machine_kept
#print axioms Lime.Replay.conserves_netClosed
#print axioms Lime.Replay.conserves_safe_then_kept
#print axioms Lime.Replay.cut_headOk
#print axioms Lime.Replay.cutOut_starts
#print axioms Lime.Replay.DayAcc.bal_net
#print axioms Lime.Replay.filter_map_netDur
#print axioms Lime.Replay.heldOf_cons
#print axioms Lime.Replay.heldOf_filter_le
#print axioms Lime.Replay.interruptMachine_closed
#print axioms Lime.Replay.lastCut_le_unk
#print axioms Lime.Replay.map_line_netDur
#print axioms Lime.Replay.mem_pruneClosed
#print axioms Lime.Replay.netAll_conserves
#print axioms Lime.Replay.netClosed_blockOnly
#print axioms Lime.Replay.netClosed_keeps
#print axioms Lime.Replay.netClosed_mem
#print axioms Lime.Replay.netClosed_obs
#print axioms Lime.Replay.netClosed_pendLines
#print axioms Lime.Replay.netClosed_sleptOk
#print axioms Lime.Replay.netDur_day
#print axioms Lime.Replay.netOne_conserves
#print axioms Lime.Replay.netOne_keeps
#print axioms Lime.Replay.netOne_mem
#print axioms Lime.Replay.pruneClosed_cons
#print axioms Lime.Replay.pruneClosed_held
#print axioms Lime.Replay.redraw_fst_starts
#print axioms Lime.Replay.settle_closed
#print axioms Lime.Replay.unk_credit_none_eq
#print axioms Lime.Replay.unk_net
#print axioms Lime.Replay.unk_uncredit_eq
#print axioms Lime.Seal.closedReads_mi
#print axioms Lime.Seal.cut_interrupt
#print axioms Lime.Seal.cutPieces_mi
#print axioms Lime.Seal.doneClosed_congr
#print axioms Lime.Seal.doneClosed_mi
#print axioms Lime.Seal.doneClose_keeps
#print axioms Lime.Seal.netClosed_congr
#print axioms Lime.Seal.netClosed_mi
#print axioms Lime.Seal.netOne_congr
#print axioms Lime.Seal.settleReads_startedMachine
#print axioms Lime.Replay.a_break_logged_after_a_done_is_netted_from_the_block
#print axioms Lime.Replay.a_break_logged_after_a_stop_is_netted_from_the_block
#print axioms Lime.Replay.a_late_break_nets_the_block_it_crosses_and_not_the_next
#print axioms Lime.Replay.a_late_break_nets_a_done_that_replaced_a_stop
#print axioms Lime.Replay.a_late_break_past_the_blocks_end_takes_what_it_covers
#print axioms Lime.Replay.a_late_break_takes_no_more_than_the_blocks_credit
#print axioms Lime.Replay.a_late_break_nets_a_block_held_and_not_one_pruned
#print axioms Lime.Replay.a_late_break_filed_the_day_before_nets_nothing
#print axioms Lime.Replay.two_late_breaks_net_their_union_once
#print axioms Lime.Replay.a_break_netted_while_open_is_not_netted_again_after_the_done
#print axioms Lime.Replay.a_done_after_a_stop_and_a_late_break_credits_its_own_minutes
#print axioms Lime.Replay.redraw_fst_spans
#print axioms Lime.Replay.cutOut_avoids
#print axioms Lime.Replay.netOne_avoids_the_break
#print axioms Lime.Replay.netOne_leaves_no_piece_across_the_break
#print axioms Lime.Replay.netClosed_avoids_the_break
#print axioms Lime.Replay.netClosed_leaves_no_piece_across_the_break
#print axioms Lime.Replay.the_unsafe_effects_are_the_machine_an_uncredit_and_a_net
#print axioms Lime.Replay.the_held_credit_counts_a_cut_and_not_a_done
-- ===========================================================================
-- APPENDED 2026-10-06: stage 6, run W-47, TRACK K, second commit -- the owner's
-- D110 (README gap 4748: a block started inside a wall is paused from its
-- start until the wall ends) and D99's wall-rule days (gaps 4616 and 4619).
-- Every theorem the step declares.  One line removed above: the renamed
-- a_block_started_inside_a_wall_is_not_paused_by_it, refuted under its new
-- name (with _as_d61_wrote_it_is_refuted), which is audited here.
-- ===========================================================================
#print axioms Lime.WallTimer.a_block_open_since_an_earlier_day_reads_its_own_pause
#print axioms Lime.WallTimer.a_block_started_inside_a_wall_is_not_paused_by_it_as_d61_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_block_started_inside_a_wall_is_paused_from_its_start
#print axioms Lime.WallTimer.an_interruption_open_since_before_the_block_holds_it_at_a_wall
#print axioms Lime.WallTimer.a_span_whose_pause_second_has_come_is_paused
#print axioms Lime.WallTimer.a_timer_already_stopped_at_the_wall_is_left_alone_as_d61_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_timer_mark_after_the_walls_start_stands_as_d61_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_user_who_resumed_during_the_meeting_keeps_their_timer_as_d61_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_wall_that_ended_before_the_block_began_writes_nothing
#print axioms Lime.WallTimer.mem_writes_as_d61_wrote_it_is_refuted
#print axioms Lime.WallTimer.pauseSec_ge
#print axioms Lime.WallTimer.pauseSec_of_lt

/-
   APPENDED 2026-10-06: stage 6, run W-47, TRACK L — the owner's D111 (README gap 4904; parity P108): a
   logged `break_start`'s place is read through the ONE table of places in the log grammar, any other word
   makes the line malformed, and the planner's reader and the host read the same table (a request's `places`
   key, answered by `PlanWire.respondPlanner` through `EmitWire.withPlaces`).  The export is still
   `PlanWire.callPlanner`; `PlanWire.callPlanner_without_a_planner_section_is_callRows` gained a `places`
   hypothesis and its W-27 form is refuted one level down.
-/
#print axioms Lime.Log.readF_renderF_at_every_value_is_refuted
#print axioms Lime.Log.placeWords_are_places_and_distinct
#print axioms Lime.Log.isPlace_reads_the_four_and_refuses_any_other_word
#print axioms Lime.Log.readF_place
#print axioms Lime.Log.a_break_start_is_emitted_only_with_a_place
#print axioms Lime.Log.a_break_start_line_reads_its_place_and_is_malformed_with_any_other_word
#print axioms Lime.Log.a_break_line_keeps_any_place
#print axioms Lime.Log.fieldFinite_of_a_place
#print axioms Lime.Log.every_place_has_its_own_key
#print axioms Lime.Log.readF_readable
#print axioms Lime.Log.readArgs_readable
#print axioms Lime.Log.a_break_start_read_off_the_disk_is_at_a_place
#print axioms Lime.PlanWire.placeOf_reads_exactly_the_table
#print axioms Lime.PlanWire.respondPlanner_without_places
#print axioms Lime.PlanWire.respondPlanner_with_places
#print axioms Lime.PlanWire.respondPlanner_answers_the_table
#print axioms Lime.PlanWire.respondPlanner_is_respondRows_without_a_planner_section_is_refuted
#print axioms Lime.EmitWire.withPlaces_without_places
#print axioms Lime.EmitWire.withPlaces_appends_the_table
#print axioms Lime.EmitWire.withPlaces_refuses_what_jget_refuses
#print axioms Lime.EmitWire.the_table_on_the_wire_is_placeWords

/-
   APPENDED 2026-10-06: stage 6, run W-47, TRACK L — the owner's D112 (README gap 4897; parity P109): the
   binary's plan rows are the kernel's `Emit.Row` cells, asked through the `plan` section and padded by one
   Rust function.  README gaps 1101 (the estimate AS WRITTEN) and 1102 (a HOT row's deadline,
   `EmitDue.lean`) are closed at their cause.
-/
#print axioms Lime.Emit.dueWords_at_every_branch
#print axioms Lime.Emit.renderWeekday_is_chronos
#print axioms Lime.Emit.hotCell_of_no_deadline
#print axioms Lime.Emit.hotCell_of_a_deadline
#print axioms Lime.Emit.dueDayOf_of_a_point
#print axioms Lime.Emit.dueDayOf_of_an_interval
#print axioms Lime.Emit.dueDayOf_of_an_absolute_window
#print axioms Lime.Emit.dueDayOf_of_a_daily_window
#print axioms Lime.Emit.dueDayOf_of_no_shape
#print axioms Lime.Emit.dueWords_ne_nil
#print axioms Lime.Emit.hotCell_ne_nil_of_a_deadline
#print axioms Lime.Emit.itemEstOf_is_the_written_estimate
#print axioms Lime.Emit.itemEstOf_prefers_the_leading_estimate
#print axioms Lime.Emit.itemEstOf_falls_back_to_the_est_key
#print axioms Lime.Emit.noteCell_of_a_hot_row
#print axioms Lime.Emit.noteCell_of_a_row_neither_underused_nor_hot
#print axioms Lime.Emit.noteCell_of_an_underused_row_it_can_name
#print axioms Lime.Emit.rowsOf_tells_the_planned_day
#print axioms Lime.EmitWire.rowsOfReq_tells_the_requests_day
#print axioms Lime.EmitWire.rowsJson_length_on_a_day
#print axioms Lime.EmitWire.readNote_reads_soFar
#print axioms Lime.EmitWire.readNote_reads_the_planners_key_and_refuses_the_other

/-! APPENDED 2026-10-06 (stage 6, run W-47, THE REPAIR): the open row under a running break (README gap 5020) and
D112's decoder exits (gap 5021).  The theorems the exits deleted (the `lastHash` and `overrides` readers' laws, and
mkHash?'s and mkOverrides?'s) left this file with them. -/
#print axioms Lime.Planner.openClipStep_le
#print axioms Lime.Planner.openClip_le_cover
#print axioms Lime.Planner.the_open_row_lies_under_no_running_break
#print axioms Lime.PlanWire.hashHex_digits_read_back
#print axioms Lime.PlanWire.hashHex_injective
#print axioms Lime.PlanWire.readPlannerSection_leaves_overrides_unread

/-! APPENDED 2026-10-11 (stage 6, run W-48, TRACK K, second commit): the owner's D114 (a break still running when a
wall ends holds the block — `WallTimer.breakHolds`; README gap 5014, parity P115) and D117 (a block resumed inside a
wall is paused from its resume until the wall ends — `WallTimer.pauseSec` over `WallTimer.intSpans`; README gaps 5036
and 3042, parity P116), each law they break refuted as written and restated beside it. -/
#print axioms Lime.WallTimer.a_block_resumed_inside_a_wall_is_paused_from_its_resume
#print axioms Lime.WallTimer.a_block_resumed_inside_a_wall_is_paused_from_its_resume_run
#print axioms Lime.WallTimer.a_block_started_inside_a_wall_is_paused_from_its_start_as_d110_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_break_running_past_the_walls_end_holds_the_block
#print axioms Lime.WallTimer.a_running_break_holds_the_walls_unpause_until_it_ends
#print axioms Lime.WallTimer.a_span_whose_pause_second_has_come_is_paused_as_d110_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_timer_already_stopped_at_the_wall_is_left_alone_as_d110_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_timer_mark_after_the_walls_start_stands_as_d110_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_user_who_resumed_during_the_meeting_keeps_their_timer_as_d110_wrote_it_is_refuted
#print axioms Lime.WallTimer.a_wall_that_starts_while_a_block_runs_stops_its_timer_as_d61_wrote_it_is_refuted
#print axioms Lime.WallTimer.ceilSec_le_of_le
#print axioms Lime.WallTimer.instant_le_ceilSec
#print axioms Lime.WallTimer.intSpans_append_marksOf
#print axioms Lime.WallTimer.intSpans_fold
#print axioms Lime.WallTimer.intSpans_sub
#print axioms Lime.WallTimer.intStep_markOf
#print axioms Lime.WallTimer.lt_ceilSec_of_lt
#print axioms Lime.WallTimer.not_covered_of_not_stopped
#print axioms Lime.WallTimer.pauseSec_cases
#print axioms Lime.WallTimer.pauseSec_of_lt_as_d110_wrote_it_is_refuted
#print axioms Lime.WallTimer.pauseSec_of_uncovered
#print axioms Lime.WallTimer.startSec_le_pauseSec
#print axioms Lime.WallTimer.the_walls_end_restarts_the_timer_it_stopped_as_d61_wrote_it_is_refuted

/-! APPENDED 2026-10-11 (stage 6, run W-48, track R): the `window ends` divider is a kernel row (README gaps 5031 and
1301) — `Emit.divider` over the rows the `plan` section is sent, answered beside them from the budget and window's end
the binary sends back. -/
#print axioms Lime.Emit.dividerGlyph_is_three_rules
#print axioms Lime.Emit.dividerRow_cells
#print axioms Lime.Emit.budgetStep_of_a_row_that_is_not_work
#print axioms Lime.Emit.budgetStep_keeps_the_instant
#print axioms Lime.Emit.dividerAt_where_the_budget_ran_out
#print axioms Lime.Emit.dividerAt_unspent
#print axioms Lime.Emit.dividerAt_is_the_window_end_or_the_spent_instant
#print axioms Lime.Emit.divider_eq
#print axioms Lime.Emit.dividerBefore_le_length
#print axioms Lime.Emit.the_budget_runs_out_at_the_second_blocks_end
#print axioms Lime.Emit.an_unspent_budget_divides_at_the_window_end
#print axioms Lime.Emit.nothing_past_the_window_and_nothing_spent_is_no_divider
#print axioms Lime.Emit.a_budget_spent_past_the_window_divides_at_its_end
#print axioms Lime.Emit.a_zero_budget_runs_out_nowhere
#print axioms Lime.EmitWire.rowKey_names_the_divider_keys
#print axioms Lime.EmitWire.readRowSection_reads_the_budget_and_the_window_end
#print axioms Lime.EmitWire.readRowSection_without_them_reads_no_divider
#print axioms Lime.EmitWire.readRowSection_refuses_one_without_the_other
#print axioms Lime.EmitWire.readRowSection_refuses_a_budget_past_the_width_and_an_end_past_the_calendar
#print axioms Lime.EmitWire.dividerJson_is_its_position_then_the_nine_cells
#print axioms Lime.EmitWire.dividerPairs_without_the_inputs
#print axioms Lime.EmitWire.dividerPairs_with_the_inputs
#print axioms Lime.EmitWire.withPlan_of_no_extra
#print axioms Lime.EmitWire.dividerPairs_on_the_wire

-- ===========================================================================
-- APPENDED 2026-10-11: stage 6, run W-48, TRACK A — the owner's D108 (README
-- gaps 4893 and 4876, parity P119): the day's first `plan` carries §7.4's
-- hysteresis input (`Log`, `Replay.DayAcc.yesterday`) and the replay holds the
-- open block's own extends (`Replay.Block.ext`).  D14's `extend` law is
-- refuted as written and restated beside it; its audit line above (line 3413)
-- names the refutation now, the restatement and its subdomain form are here.
-- ===========================================================================
#print axioms Lime.Log.allPrios_map
#print axioms Lime.Log.allPrios_mem
#print axioms Lime.Log.a_plan_line_carries_its_hysteresis_input
#print axioms Lime.Log.a_plan_line_without_it_carries_none
#print axioms Lime.Log.an_empty_hysteresis_input_is_not_written
#print axioms Lime.Log.a_malformed_hysteresis_input_is_refused
#print axioms Lime.Log.every_hysteresis_input_is_read_back
#print axioms Lime.Replay.extendFx_keys
#print axioms Lime.Replay.applyEffects_extendFx
#print axioms Lime.Replay.an_extend_changes_only_the_bookkeeping_its_extended_minutes_and_its_blocks
#print axioms Lime.Replay.an_extend_changes_only_the_bookkeeping_and_its_extended_minutes_with_no_block_of_it_open
#print axioms Lime.Replay.extendFx_obs
#print axioms Lime.Replay.extendFx_machines
#print axioms Lime.Replay.an_open_blocks_extends_are_its_own
#print axioms Lime.Replay.a_start_begins_the_extends_again
#print axioms Lime.Log.a_wake_is_a_state_change_and_a_plan_is_not

-- ===========================================================================
-- APPENDED 2026-10-11: stage 6, run W-48, TRACK A, second commit — README gap
-- 5027: D99's re-draw made linear per mark by `@[csimp]` twins proved equal to
-- the definitions every theorem reads (`pieces`, `redraw`, `Seal.redrawReads`).
-- `countP_lt_of_witness` moved up the file (its audit line stands above).
-- ===========================================================================
#print axioms Lime.Replay.apart_spec
#print axioms Lime.Replay.liftGo_of_uncovered
#print axioms Lime.Replay.liftGo_succ
#print axioms Lime.Replay.lift_of_cover
#print axioms Lime.Replay.nextStart_none_of
#print axioms Lime.Replay.nextStart_of_least
#print axioms Lime.Replay.piecesGo_congr
#print axioms Lime.Replay.piecesGo_of_uncovered
#print axioms Lime.Replay.piecesGo_eq_sweep
#print axioms Lime.Replay.pieces_eq_piecesFast
#print axioms Lime.Replay.samePiece_start
#print axioms Lime.Replay.startsUp_cons
#print axioms Lime.Replay.redrawWalkGo_spec
#print axioms Lime.Replay.redraw_eq_redrawFast
#print axioms Lime.Replay.the_one_pass_answers_as_pieces
#print axioms Lime.Replay.the_pass_is_guarded
#print axioms Lime.Replay.the_merge_is_guarded
#print axioms Lime.Replay.piecesFast_answers_through_the_pass
#print axioms Lime.Replay.the_merge_keeps_unmoved_pieces_and_redraws_moved_ones
#print axioms Lime.Replay.redrawFast_answers_through_the_merge_and_else_through_redraw
#print axioms Lime.Seal.redrawReads_eq_redrawReadsFast
#print axioms Lime.Seal.redrawReadsFast_reads_through_the_merge_and_else_through_redrawReads
/-! APPENDED 2026-10-11 (stage 6, run W-48, track G; README "Stage 6 — W-48 track G"): `Goals.plan_places_no_block_over_a_break` reduced to three
facts about the replay's answer and the running break (`PlanCheck.plan_places_no_block_over_a_break_on_an_apart_replay`),
the replay's half of the open-row clause and the closed side's step half of the record clause, and the witnesses — the law applied whole at the mid-break day, the record
clause biting at the pre-D100 run, and a day the decoder builds that fails the running-break clause (README gap 5180).
The goal stays in `Goals.lean`. -/
#print axioms Lime.PlanCheck.segOf_apart
#print axioms Lime.PlanCheck.a_past_row_lies_inside_its_segment
#print axioms Lime.PlanCheck.the_running_break_row_starts_where_it_started
#print axioms Lime.PlanCheck.plan_places_no_block_over_a_break_on_an_apart_replay
#print axioms Lime.PlanCheck.settle_runs_after_every_span_it_nets
#print axioms Lime.PlannerWit.the_apart_replay_holds_at_the_mid_break_request
#print axioms Lime.PlannerWit.the_break_law_holds_whole_at_the_mid_break_request
#print axioms Lime.PlannerWit.the_apart_replay_fails_at_the_pre_d100_request
#print axioms Lime.PlannerWit.closeUnderBreakRun_resumes_ok
#print axioms Lime.PlanCheck.netOne_draws_beside_the_break

/-! APPENDED 2026-10-11 (stage 6, run W-48, TRACK K, third commit): the owner's D115 (a late `start` stamped inside a
block a later `done` closed cuts it — `Replay.netStart`; README gap 5034, parity P120), D119 (a late interruption is
netted from the block it crosses — `Replay.netClosed` in the `resume` arm — and a late mark past the 31-day bound is
named, `RWarn.pastBound`; README gaps 4913, 4917 and 5029, parity P121) and D116 (a break is read at its `break_start`'s
place, another word on its end line named, `Replay.placed`, `RWarn.breakPlace`; README gap 5035, parity P122), with the
seal laws re-proved over the instants they read. -/
#print axioms Lime.Replay.a_break_is_read_at_its_starts_place
#print axioms Lime.Replay.a_late_interruption_nets_the_block_it_crosses
#print axioms Lime.Replay.a_late_mark_past_the_bound_is_named
#print axioms Lime.Replay.a_late_start_cuts_the_block_it_is_stamped_inside
#print axioms Lime.Replay.applyEffects_lateWarns_rwarns
#print axioms Lime.Replay.a_start_cuts_no_block_it_is_not_stamped_inside
#print axioms Lime.Replay.completionArm_instOf
#print axioms Lime.Replay.completionCore_doneDates
#print axioms Lime.Replay.completionCore_markOf
#print axioms Lime.Replay.completionCore_namedOf
#print axioms Lime.Replay.completionCore_no_header
#print axioms Lime.Replay.completionCore_noRec
#print axioms Lime.Replay.completionCore_noSeam
#print axioms Lime.Replay.completionCore_obs
#print axioms Lime.Replay.completionCore_rwarns
#print axioms Lime.Replay.completionCore_safe
#print axioms Lime.Replay.completionCore_sleptOk
#print axioms Lime.Replay.conserves_cut_of
#print axioms Lime.Replay.cutOut_lt
#print axioms Lime.Replay.cutOut_startEnd_starts
#print axioms Lime.Replay.dayArm_placed_rec
#print axioms Lime.Replay.foldl_end_ge
#print axioms Lime.Replay.lateWarnList_not_status
#print axioms Lime.Replay.lateWarns_all
#print axioms Lime.Replay.lateWarns_any
#print axioms Lime.Replay.lateWarns_filterMap
#print axioms Lime.Replay.lateWarns_rwarn
#print axioms Lime.Replay.netClosed_conserves
#print axioms Lime.Replay.netEachAll_conserves
#print axioms Lime.Replay.netStart_blockOnly
#print axioms Lime.Replay.netStart_conserves
#print axioms Lime.Replay.netStart_keeps
#print axioms Lime.Replay.netStart_mem
#print axioms Lime.Replay.netStart_obs
#print axioms Lime.Replay.netStart_pendLines
#print axioms Lime.Replay.netStart_sleptOk
#print axioms Lime.Replay.piecesGo_lt
#print axioms Lime.Replay.placed_ev_of_brk
#print axioms Lime.Replay.placed_line
#print axioms Lime.Replay.placed_of_not_brk
#print axioms Lime.Replay.startEnd_ge
#print axioms Lime.Replay.startEnd_guard
#print axioms Lime.Replay.the_replay_warnings_are_the_unknown_statuses_in_file_order_as_c4_stated_it_is_refuted
#print axioms Lime.Seal.cutReads_netStart
#print axioms Lime.Seal.netClosed_lastCut_day
#print axioms Lime.Seal.netStart_congr
#print axioms Lime.Seal.netStart_mi
#print axioms Lime.Seal.startReads_mi
#print axioms Lime.Replay.arm_split_as_d87_stated_it_is_refuted

-- ===========================================================================
-- APPENDED 2026-10-11: stage 6, run W-48, THE REPAIR — D108 read by the plan lines' own stamps (README gaps 5210 and
-- 5211: `Replay.DayAcc.planAt`, `lateAt`, `late`; `a_plan_sets_the_hysteresis_input_iff_it_is_the_days_first` is
-- restated with the stamp's binder and keeps its audit line above), and the last goal's reduction given a subject for
-- each of its replay hypotheses (README gap 5219).
-- ===========================================================================
#print axioms Lime.Replay.a_plan_records_its_stamp
#print axioms Lime.Replay.a_plan_with_an_input_is_the_latest_and_one_without_keeps_it
#print axioms Lime.Replay.the_latest_input_and_the_last_plan_are_read_at_their_stamps
#print axioms Lime.PlannerWit.openAfterBreakRun_resumes_ok
#print axioms Lime.PlannerWit.breakAfterDoneRun_resumes_ok
#print axioms Lime.PlannerWit.the_apart_replay_holds_with_a_block_open_after_a_break
#print axioms Lime.PlannerWit.the_break_law_holds_whole_with_a_block_open_after_a_break
#print axioms Lime.PlannerWit.the_apart_replay_holds_with_a_break_running_after_a_done
#print axioms Lime.PlannerWit.the_break_law_holds_whole_with_a_break_running_after_a_done

/- ===========================================================================
   APPENDED 2026-10-13: stage 6, run W-49, TRACK P — the planner's rows in one
   call, at every length (the owner's D123 and D124; README gaps 5212 and 5130).
   EmitWire.readSegs_refuses_past_the_cap is DELETED (D123 widened the reader
   to the planner's day) and its negation is audited below.
   =========================================================================== -/
#print axioms Lime.EmitWire.readSegs_reads_every_list_whose_segments_read
#print axioms Lime.EmitWire.readSeg_reads_a_rest_at_every_position
#print axioms Lime.EmitWire.readSegs_refuses_past_the_cap_is_refuted
#print axioms Lime.EmitWire.readSegs_reads_a_rest_and_refuses_a_record_without_a_start
#print axioms Lime.EmitWire.answersRows_of_an_answer_without_rows
#print axioms Lime.EmitWire.RowReq.ofDay_is_the_days_own
#print axioms Lime.EmitWire.the_planned_days_rows_are_rowsOf
#print axioms Lime.EmitWire.dayRowsPairs_is_the_rows_then_the_days_divider
#print axioms Lime.EmitWire.dayRowsPairs_rows_length
#print axioms Lime.EmitWire.the_door_writes_the_one_calls_pairs
#print axioms Lime.EmitWire.answersRows_withPlan
#print axioms Lime.EmitWire.answersRows_without_a_plan_key
#print axioms Lime.PlanWire.runPlanner_answers_the_days_rows
#print axioms Lime.PlanWire.runPlanner_refuses_a_plan_section_beside_it
#print axioms Lime.PlanWire.planWithPlanner_spells_itself
-- ===========================================================================
-- APPENDED 2026-10-13: stage 6, run W-49, TRACK W — the remainder after a wall that holds the running block (README
-- gap 5217, parity P123; the owner's D110, D117 and D114).  `activeRun_spec`, `mem_activeRow`,
-- `activeRow_is_an_energyless_block`, `the_reservation_row_is_exact`, `a_running_break_pauses_the_block`, the D77
-- overrun-break laws and the other restated theorems keep their audit lines above, under their names.
-- ===========================================================================
#print axioms Lime.WallTimer.heldFor_without_a_break
#print axioms Lime.WallTimer.heldFor_spec
#print axioms Lime.WallTimer.heldFor_started_le
#print axioms Lime.WallTimer.holdOf_spec
#print axioms Lime.Planner.PlanReq.held_started
#print axioms Lime.WallTimer.before_the_first_free_stretch_is_blocked
#print axioms Lime.Planner.PlanReq.a_held_reservation_reaches_at_most_one_block
#print axioms Lime.Planner.PlanReq.no_slot_before_the_reservation
#print axioms Lime.Planner.PlanReq.the_reservation_starts_before_the_wind_down
#print axioms Lime.Planner.the_reservation_row_is_at_most_one_block
#print axioms Lime.PlannerWit.heldRun_resumes_ok
#print axioms Lime.PlannerWit.the_held_block_is_reserved_from_the_walls_end
#print axioms Lime.PlannerWit.nothing_drifts_when_the_wall_lets_the_block_go
#print axioms Lime.PlannerWit.the_break_that_holds_the_block_releases_it_at_its_end
#print axioms Lime.PlannerWit.the_reservation_starts_at_now_is_refuted
#print axioms Lime.PlannerWit.the_reservation_row_starts_at_now_is_refuted
#print axioms Lime.PlannerWit.a_running_break_pauses_the_block_as_w35_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_held_reservation_bound_fires
#print axioms Lime.PlannerWit.loggedAcrossRun_resumes_ok
#print axioms Lime.PlannerWit.a_twin_without_the_meetings_pause_loses_the_hold
#print axioms Lime.PlannerWit.the_cut_does_not_change_when_an_overrun_break_is_logged_as_d77_wrote_it_is_refuted
#print axioms Lime.PlannerWit.the_day_from_now_does_not_change_when_an_overrun_break_is_logged_as_d77_wrote_it_is_refuted
#print axioms Lime.PlannerWit.an_overrun_break_that_holds_the_block_reserves_nothing
#print axioms Lime.PlannerWit.the_reservation_start_guard_fires
-- ===========================================================================
-- APPENDED 2026-10-13: stage 6, run W-49, TRACK L — the replay reads a block closed, stopped or paused while a logged
-- break runs as it will once the break's line arrives (README gap 5180: `Replay.runNet`, `Replay.runSpan`; the seal's
-- queries read the netting at `Seal.runReads`).  the_close_under_a_running_break_lays_its_block_across_the_break is
-- deleted with its audit line (its statement decided the defect this closes); its successor is
-- `the_close_under_a_running_break_is_netted_from_its_block`.  `the_break_start_arm_opens_the_running_break` is restated
-- and keeps its audit line above.
-- ===========================================================================
#print axioms Lime.PlannerWit.the_break_law_holds_whole_at_the_close_under_a_running_break
#print axioms Lime.PlannerWit.the_close_under_a_running_break_is_netted_from_its_block
#print axioms Lime.Replay.a_break_start_logged_after_a_done_nets_it
#print axioms Lime.Replay.a_done_under_a_running_break_is_netted_by_it
#print axioms Lime.Replay.a_pause_under_a_running_break_draws_up_to_its_start
#print axioms Lime.Replay.applyEffect_machine_comm
#print axioms Lime.Replay.applyEffects_machine_comm
#print axioms Lime.Replay.a_running_break_after_a_done_nets_nothing
#print axioms Lime.Replay.a_start_under_a_running_break_cuts_the_open_block_at_the_break
#print axioms Lime.Replay.a_stop_under_a_running_break_is_netted_by_it
#print axioms Lime.Replay.conserves_doneFx
#print axioms Lime.Replay.conserves_runNet
#print axioms Lime.Replay.cutOut_runTo_starts
#print axioms Lime.Replay.doneClose_noMachine
#print axioms Lime.Replay.netClosed_headOk
#print axioms Lime.Replay.noMachine_of_plain
#print axioms Lime.Replay.noMachine_of_safe
#print axioms Lime.Replay.runNet_blockOnly
#print axioms Lime.Replay.runNet_cases
#print axioms Lime.Replay.runNet_conserves
#print axioms Lime.Replay.runNet_duration
#print axioms Lime.Replay.runNet_energy
#print axioms Lime.Replay.runNet_headOk
#print axioms Lime.Replay.runNet_keeps
#print axioms Lime.Replay.runNet_machines
#print axioms Lime.Replay.runNet_mem
#print axioms Lime.Replay.runNet_noMachine
#print axioms Lime.Replay.runNet_obs
#print axioms Lime.Replay.runNet_pendLines
#print axioms Lime.Replay.runNet_sleptOk
#print axioms Lime.Replay.runTo_ge
#print axioms Lime.Replay.settle_avoids_the_running_break
#print axioms Lime.Replay.the_break_start_arm_as_d105_stated_it_is_refuted
#print axioms Lime.Replay.the_break_start_arm_writes_only_the_running_break_with_nothing_open_or_drawn_after_it
#print axioms Lime.Replay.the_running_breaks_line_moves_nothing_it_netted
#print axioms Lime.Seal.closedReads_shp
#print axioms Lime.Seal.cut_shp
#print axioms Lime.Seal.doneClosed_shp
#print axioms Lime.Seal.netOne_shp
#print axioms Lime.Seal.netStart_shp
#print axioms Lime.Seal.piece_start_run_mi
#print axioms Lime.Seal.pruneClosed_shp
#print axioms Lime.Seal.redraw_fst_map
#print axioms Lime.Seal.runNet_congr
#print axioms Lime.Seal.runNet_lastCut_cases
#print axioms Lime.Seal.runNet_lastCut_day
#print axioms Lime.Seal.runNet_mi
#print axioms Lime.Seal.runReads_mi
#print axioms Lime.Seal.runReads_settle
#print axioms Lime.Seal.runReads_shp
#print axioms Lime.Seal.runReads_starts
#print axioms Lime.Seal.runTo_spans

-- ===========================================================================
-- APPENDED 2026-10-13: stage 6, run W-49, TRACK L — D108's one answer (README gap 5300; the owner's D125): the day
-- keeps the latest calendar date's last `plan` and last input, with their lines (`Replay.DayAcc.planHash`, `planLine`,
-- `lateLine`; `Replay.notBefore`).  a_day_keeps_its_first_plans_hysteresis_input and
-- a_plan_sets_the_hysteresis_input_iff_it_is_the_days_first are deleted with their audit lines: they were the
-- first-of-the-ledger-day answer, now gone.  `a_plan_records_its_stamp`,
-- `a_plan_with_an_input_is_the_latest_and_one_without_keeps_it` and
-- `the_latest_input_and_the_last_plan_are_read_at_their_stamps` are restated and keep their audit lines above.
-- ===========================================================================
#print axioms Lime.Replay.a_clock_behind_the_log_moves_no_later_dates_answer
#print axioms Lime.Replay.a_day_keeps_its_latest_plans_hysteresis_input
#print axioms Lime.Replay.a_plan_of_an_earlier_date_keeps_the_slot
#print axioms Lime.Replay.a_plan_with_an_input_is_the_latest_as_the_w48_repair_stated_it_is_refuted
#print axioms Lime.Replay.a_plan_records_its_stamp_as_the_w48_repair_stated_it_is_refuted

-- APPENDED W-49 TRACK Y (README "Stage 6 — W-49 track Y", gap 5161): `planner.state.yesterday`
-- left the decoder with `Planner.RuntimeIn`'s field; six laws went with their subjects (named in the
-- block) and one is new.
#print axioms Lime.PlanWire.readState_leaves_yesterday_unread

-- ===========================================================================
-- APPENDED 2026-10-14 by stage 6 W-49 track Q (README "Stage 6 — W-49 track Q", gap 5181): the
-- replay's two fold invariants behind the last goal's `hopen` (`BreakFold.lean`: `OpenAfter`, `BrkHeld`, carried
-- through every step and every resume from a state holding them), `hopen` discharged at the planner's request
-- (`PlanCheck.hopen_on_a_resumed_run`) and the reduction with it (`PlanCheck.plan_places_no_block_over_a_break_on_a_resumed_run`),
-- and `PlannerWit`'s witnesses: the fold's `hopen` at a day with a subject, and the two worlds on which the goal as
-- written fails at a request the decoder builds (README gaps 5340 and 5341).
-- ===========================================================================
#print axioms Lime.BreakFold.applyEffect_days
#print axioms Lime.BreakFold.applyEffects_seg_src
#print axioms Lime.BreakFold.arm_noBrkSeg
#print axioms Lime.BreakFold.arm_openAfter
#print axioms Lime.BreakFold.brkFx_noBrkSeg
#print axioms Lime.BreakFold.closePause_noBrkSeg
#print axioms Lime.BreakFold.completionArm_noBrkSeg
#print axioms Lime.BreakFold.creditFx_noBrkSeg
#print axioms Lime.BreakFold.cut_block
#print axioms Lime.BreakFold.cut_noBrkSeg
#print axioms Lime.BreakFold.dayArm_noBrkSeg
#print axioms Lime.BreakFold.DayOp.alterFn_segments
#print axioms Lime.BreakFold.DayOp.apply_segments
#print axioms Lime.BreakFold.doneClose_keeps
#print axioms Lime.BreakFold.doneClose_noBrkSeg
#print axioms Lime.BreakFold.doneFx_noBrkSeg
#print axioms Lime.BreakFold.extendFx_noBrkSeg
#print axioms Lime.BreakFold.finish_segments
#print axioms Lime.BreakFold.flatten_noBrkSeg
#print axioms Lime.BreakFold.fm_attain
#print axioms Lime.BreakFold.fm_ge_init
#print axioms Lime.BreakFold.fm_ge_mem
#print axioms Lime.BreakFold.fm_le
#print axioms Lime.BreakFold.fm_mono
#print axioms Lime.BreakFold.foldl_brkHeld
#print axioms Lime.BreakFold.foldl_openAfter
#print axioms Lime.BreakFold.hi_grows
#print axioms Lime.BreakFold.hi_pruneBrks
#print axioms Lime.BreakFold.netClosed_noBrkSeg
#print axioms Lime.BreakFold.netOne_noBrkSeg
#print axioms Lime.BreakFold.netStart_noBrkSeg
#print axioms Lime.BreakFold.noBrkSeg_append
#print axioms Lime.BreakFold.noBrkSeg_nil
#print axioms Lime.BreakFold.noBrkSeg_of_no_segment
#print axioms Lime.BreakFold.obsFx_noBrkSeg
#print axioms Lime.BreakFold.openAfter_congr
#print axioms Lime.BreakFold.openAfter_of_no_block
#print axioms Lime.BreakFold.prune_keeps
#print axioms Lime.BreakFold.redraw_noBrkSeg
#print axioms Lime.BreakFold.restore_empty_holds
#print axioms Lime.BreakFold.resumedAnswer_day_src
#print axioms Lime.BreakFold.resumeRun_holds
#print axioms Lime.BreakFold.runNet_noBrkSeg
#print axioms Lime.BreakFold.settle_noBrkSeg
#print axioms Lime.BreakFold.settle_openAfter
#print axioms Lime.BreakFold.stepWith_brkHeld
#print axioms Lime.BreakFold.stepWith_brks
#print axioms Lime.BreakFold.stepWith_brks_of_brk
#print axioms Lime.BreakFold.stepWith_openAfter
#print axioms Lime.BreakFold.the_genesis_restore_holds
#print axioms Lime.BreakFold.the_resumed_open_block_runs_after_every_break
#print axioms Lime.BreakFold.uncreditFx_noBrkSeg
#print axioms Lime.PlanCheck.hopen_on_a_resumed_run
#print axioms Lime.PlanCheck.plan_places_no_block_over_a_break_on_a_resumed_run
#print axioms Lime.PlannerWit.openAfterBreakRun_resumes
#print axioms Lime.PlannerWit.planReqOf_keeps_the_hosts_runtime
#print axioms Lime.PlannerWit.the_break_law_holds_whole_at_the_open_after_break_request_by_the_fold
#print axioms Lime.PlannerWit.the_fold_discharges_the_open_block_clause_at_the_open_after_break_request
#print axioms Lime.PlannerWit.ydBreakRun_resumes_ok

-- APPENDED 2026-10-17 by stage 6 W-49 repair (README "Stage 6 — W-49 repair", gap 5411): the two
-- `hrun`-false worlds are whole requests the decoder builds, and the planner wire refuses neither.
#print axioms Lime.PlannerWit.breakAfterDoneRun_resumes
#print axioms Lime.PlannerWit.ydBreakRun_resumes
#print axioms Lime.PlannerWit.witBuildsHostBreak
#print axioms Lime.PlannerWit.witBuildsYdBreak
#print axioms Lime.PlannerWit.the_host_and_yd_break_requests_are_not_refused

-- APPENDED 2026-10-28 by stage 6 W-50 track K (README "Stage 6 — W-50 track K", gaps 5430-5433, parity P127): the
-- owner's D129 — a `start` ends a running break at its instant, read in stamp order.  The arm's start, `break_start`
-- and `break` cases, each law over them re-proved (D5), three restated and refuted by name, and the witnesses.
#print axioms Lime.Replay.firstStep_mem
#print axioms Lime.Replay.foldl_firstStep_mem
#print axioms Lime.Replay.firstStart_mem
#print axioms Lime.Replay.endBrkFx_blockOnly
#print axioms Lime.Replay.endRecs_blockOnly
#print axioms Lime.Replay.startArm_blockOnly
#print axioms Lime.Replay.brkStartArm_blockOnly
#print axioms Lime.Replay.endRecs_safe
#print axioms Lime.Replay.conserves_brkFx
#print axioms Lime.Replay.conserves_endBrkFx
#print axioms Lime.Replay.conserves_startArm
#print axioms Lime.Replay.conserves_brkStartArm
#print axioms Lime.Replay.brkFx_sleptOk
#print axioms Lime.Replay.endRecs_sleptOk
#print axioms Lime.Replay.endBrkFx_sleptOk
#print axioms Lime.Replay.startArm_sleptOk
#print axioms Lime.Replay.brkStartArm_sleptOk
#print axioms Lime.Replay.endRecs_obs
#print axioms Lime.Replay.endBrkFx_obs
#print axioms Lime.Replay.startArm_machines
#print axioms Lime.Replay.startArm_obs
#print axioms Lime.Replay.startEnds_mem
#print axioms Lime.Replay.endBrkFx_mem
#print axioms Lime.Replay.a_start_ends_the_running_break
#print axioms Lime.Replay.a_late_break_start_ends_at_the_first_start_after_it
#print axioms Lime.Replay.a_break_from_the_day_before_ends_at_the_next_start
#print axioms Lime.Replay.a_breaks_own_line_after_a_start_ended_it_is_not_a_second_break
#print axioms Lime.Replay.a_start_at_the_breaks_instant_ends_it_there
#print axioms Lime.Replay.a_start_stamped_before_the_break_ends_nothing
#print axioms Lime.Replay.a_late_break_inside_a_block_with_no_start_after_it_still_runs
#print axioms Lime.Replay.the_break_start_arm_as_w49_stated_it_is_refuted
#print axioms Lime.Replay.the_break_start_arm_with_nothing_open_or_drawn_after_it_as_w49_stated_it_is_refuted
#print axioms Lime.Replay.arm_split_as_d116_stated_it_is_refuted
#print axioms Lime.Seal.startQueries_congr
#print axioms Lime.Seal.startArm_congr
#print axioms Lime.Seal.brkFx_congr
#print axioms Lime.Seal.startQueries_sub
#print axioms Lime.Seal.endMachine_mi
#print axioms Lime.Seal.firstStart_mi
#print axioms Lime.Seal.brkFxReads_sub
#print axioms Lime.Seal.startArm_mi
#print axioms Lime.BreakFold.startArm_noBrkSeg
#print axioms Lime.BreakFold.brkStartArm_noBrkSeg
#print axioms Lime.BreakFold.endRecs_seg
#print axioms Lime.BreakFold.held_of_prune
#print axioms Lime.BreakFold.stepWith_brks_of_start
#print axioms Lime.BreakFold.stepWith_brks_of_brkStart
#print axioms Lime.BreakFold.arm_noBrkSeg_as_w49_stated_it_is_refuted
#print axioms Lime.BreakFold.stepWith_brks_of_brk_as_w49_stated_it_is_refuted
#print axioms Lime.PlannerWit.a_break_running_since_the_day_before_lays_todays_block_across_it_as_w49_stated_it_is_refuted
#print axioms Lime.Replay.a_late_break_past_the_bound_is_not_ended_by_a_start

-- APPENDED W-50 REPAIR TRACK R (README "Stage 6 — W-50 repair, track R", gaps 5500-5502): D129's stamp-order edges.
#print axioms Lime.Replay.a_start_tying_the_break_logged_before_it_ends_nothing
#print axioms Lime.Replay.a_drawn_piece_is_not_a_start
#print axioms Lime.Replay.the_earliest_start_ends_a_late_break
#print axioms Lime.Replay.the_earliest_start_ends_a_late_break_logged_in_either_order

-- ===========================================================================
-- APPENDED 2026-10-28 (stage 6, W-50 repair, track B — the owner's D133, README gaps 5520-5539, parity P130).
-- The running break leaves the planner wire: `Planner.PlanReq.runningBreak` reads it off the request's own replay.
-- Removed above with their definitions (README gap 5524): Planner's four mkBreak? laws, PlanWire's four readBreak
-- laws and readOptBreak_reads_the_break; PlannerWit's two host-copy witnesses, each refuted below under its old name.
-- ===========================================================================
#print axioms Lime.PlanWire.readState_leaves_the_break_unread
#print axioms Lime.PlannerWit.the_running_break_is_the_replays
#print axioms Lime.PlannerWit.the_hosts_running_break_lays_a_block_across_it_is_refuted
#print axioms Lime.PlannerWit.a_break_running_since_the_day_before_lays_todays_block_across_it_is_refuted
#print axioms Lime.PlannerWit.hrun_holds_on_the_host_and_yd_break_logs

-- ===========================================================================
-- APPENDED 2026-10-30 (stage 6, W-51, track K — the owner's D137, README gaps 5580-5599, parity P134).
-- A running break's `break` line gives back what its running took outside its own span (`Replay.giveBack`).
-- ===========================================================================
#print axioms Lime.Replay.runOne_netOne
#print axioms Lime.Replay.netOne_ran
#print axioms Lime.Replay.heldOf_map_congr
#print axioms Lime.Replay.giveOne_mem
#print axioms Lime.Replay.giveBack_mem
#print axioms Lime.Replay.giveBack_plain
#print axioms Lime.Replay.giveBack_keeps
#print axioms Lime.Replay.giveOne_keeps
#print axioms Lime.Replay.endMachine_held
#print axioms Lime.Replay.giveOne_conserves
#print axioms Lime.Replay.giveAll_conserves
#print axioms Lime.Replay.giveBack_conserves
#print axioms Lime.Replay.giveBack_headOk
#print axioms Lime.Replay.conserves_brkFx_of
#print axioms Lime.Replay.giveBack_sleptOk
#print axioms Lime.Replay.giveBack_obs
#print axioms Lime.Replay.giveBack_brkFx_machine
#print axioms Lime.Replay.giveOne_of_no_run
#print axioms Lime.Replay.a_late_breaks_line_gives_back_what_lies_after_it
#print axioms Lime.Replay.a_running_breaks_line_gives_back_the_close_it_did_not_reach
#print axioms Lime.Replay.a_late_breaks_line_gives_back_a_stopped_block
#print axioms Lime.Seal.giveBack_shp
#print axioms Lime.Seal.brkFxReads_giveBack
#print axioms Lime.Seal.netOne_congr_mem
#print axioms Lime.Seal.giveBack_congr
#print axioms Lime.Seal.restored_starts
#print axioms Lime.Seal.giveReads_mi
#print axioms Lime.Seal.giveBack_mi
#print axioms Lime.BreakFold.giveBack_noBrkSeg
#print axioms Lime.Replay.runOne_remembers_only_the_pieces_it_met
-- APPENDED W-51 repair track K (w51r-k): a give-back keeps every later netting (README gap 5630)
#print axioms Lime.Replay.startEnd_ge_run
#print axioms Lime.Replay.startEnd_guard_as_w51_stated_it_is_refuted
#print axioms Lime.Replay.reNet_fst
#print axioms Lime.Replay.netOne_ran_as_w51_stated_it_is_refuted
#print axioms Lime.Replay.netOne_ran_of_no_run
#print axioms Lime.Replay.cutOut_startEnd_starts_of
#print axioms Lime.Replay.cutRan_spans
#print axioms Lime.Replay.reNet_starts
#print axioms Lime.Replay.reNet_startEnd_starts
#print axioms Lime.Replay.netOne_min_add
#print axioms Lime.Replay.netOne_took_of_no_meet
#print axioms Lime.Replay.giveOne_runOne_min
#print axioms Lime.Replay.netOne_nets_the_give_back
#print axioms Lime.Replay.giveOne_after_a_later_netting_min
#print axioms Lime.Replay.the_k_log_reads_as_its_break_had_no_start
#print axioms Lime.Replay.the_k_log_without_its_break_start
#print axioms Lime.Replay.the_c_log_reads_as_its_break_had_no_start
#print axioms Lime.Replay.the_c_log_without_its_break_start
#print axioms Lime.Replay.netOne_nets_the_give_back_is_not_vacuous

/- ======================================================================
   APPENDED 2026-10-31: stage 6 W-52 track K (w52-k) — gap 5631 (a give-back's gate) and the owner's D142
   (overlapping logged breaks read as their union, parity P136).
   ====================================================================== -/
#print axioms Lime.Replay.brkRecsC_cases
#print axioms Lime.Replay.brkDay_cases
#print axioms Lime.Replay.brkDay_obs3
#print axioms Lime.Replay.giveOne_of_no_run_as_w51_stated_it_is_refuted
#print axioms Lime.Replay.netOne_ran_of_no_run_as_w51r_stated_it_is_refuted
#print axioms Lime.Replay.a_give_back_with_no_piece_left_still_gives_its_minutes
#print axioms Lime.Replay.the_j_log_draws_and_records_its_breaks_once
#print axioms Lime.Replay.a_break_an_earlier_covers_in_part_is_drawn_from_its_end
#print axioms Lime.Replay.a_break_no_earlier_covers_is_drawn_as_logged
#print axioms Lime.Replay.coverFrom_reads_only_earlier_breaks

/- ======================================================================
   APPENDED 2026-10-31: stage 6 W-52b track K2 (w52-k2) — the owner's D141, its replay half (README gaps 5633 and
   5660, parity P137): a `break` line ending a break D129 already ended, where it says.
   ====================================================================== -/
#print axioms Lime.Replay.forget_held
#print axioms Lime.Replay.forget_headOk
#print axioms Lime.Replay.forgetIdle_held
#print axioms Lime.Replay.forgetIdle_headOk
#print axioms Lime.Replay.forgetIdle_keeps
#print axioms Lime.Replay.conserves_netTake
#print axioms Lime.Replay.brkFx_block
#print axioms Lime.Replay.a_break_line_before_its_d129_end_ends_the_break_there
#print axioms Lime.Replay.a_break_line_at_or_after_its_d129_end_is_the_breaks_own
#print axioms Lime.Replay.a_break_line_ending_at_its_d129_end_is_the_breaks_own
#print axioms Lime.Replay.a_break_line_ending_a_covered_break_leaves_two_records
#print axioms Lime.Replay.a_break_line_for_an_older_ended_break_a_newer_one_overlaps_is_its_own
#print axioms Lime.Replay.forgetIdle_clears_a_take_only_with_no_break_running
#print axioms Lime.Seal.mi_of_sub
#print axioms Lime.Seal.forget_mi
#print axioms Lime.Seal.forgetIdle_mi
#print axioms Lime.Seal.tail_mi
#print axioms Lime.BreakFold.undo141_seg
#print axioms Lime.BreakFold.stepWith_brkHeld_d141
#print axioms Lime.Replay.a_d129_ending_covered_in_part_is_recorded_by_its_drawn_minutes

/- ============================================================================================
   APPENDED — stage 6 W-52 repair track R (kernel half): D141 for every break D129 ended — the
   endings held as a list keyed by the line that made them (`Replay.Ending`, `Machine.ended`), each
   ending's take kept under its key (`Closed.held`), its record by its key (`BreakRec.src`), and
   the fact the host reads (`Replay.endable`, `open.ended`).  README gaps 5711-5714, 5730, 5740-5749.
   ============================================================================================ -/
#print axioms Lime.Replay.stash_keeps
#print axioms Lime.Replay.dropTake_keeps
#print axioms Lime.Replay.unstash_keeps
#print axioms Lime.Replay.held_map_keeps
#print axioms Lime.Replay.headOk_map_keeps
#print axioms Lime.Replay.reNet_startEnd_starts_of
#print axioms Lime.Replay.startEnd_past_all
#print axioms Lime.Replay.reNetTake_startEnd_starts
#print axioms Lime.Replay.reNetTake_starts
#print axioms Lime.Replay.netOne_held
#print axioms Lime.Replay.d141_reads_iff_endable
#print axioms Lime.Replay.arm_brk_of_endable
#print axioms Lime.Replay.giveOne_minutes
#print axioms Lime.Replay.the_d141_give_back_credits_exactly_its_endings_take
#print axioms Lime.Replay.the_d141_give_back_restores_the_endings_minutes
#print axioms Lime.Replay.no_give_back_twice
#print axioms Lime.Replay.d141Machine_ended
#print axioms Lime.Replay.scenario_c_holds_two_endable_breaks
#print axioms Lime.Replay.scenario_c_older_line_first_ends_both_breaks
#print axioms Lime.Replay.scenario_c_newer_line_first_ends_both_breaks
#print axioms Lime.Replay.j2_an_ordinary_break_after_the_ending_leaves_it_endable
#print axioms Lime.Replay.b2_two_breaks_at_one_stamp_end_by_identity
#print axioms Lime.Replay.a_running_break_a_start_ended_gives_back_on_its_line
#print axioms Lime.Replay.an_ending_a_later_break_overlaps_is_not_reached
#print axioms Lime.Replay.a_checkpoint_holding_two_endings_round_trips
#print axioms Lime.Seal.netOne_held_starts
#print axioms Lime.Seal.netOne_held_startEnd
#print axioms Lime.Seal.pcs_stash
#print axioms Lime.Seal.pcs_dropTake
#print axioms Lime.Seal.pcs_unstash
#print axioms Lime.Seal.d141Machine_mi
#print axioms Lime.Seal.letGo_mi
#print axioms Lime.Seal.openEnded_reads_state
#print axioms Lime.Seal.answer_openEnded
#print axioms Lime.BreakFold.fm_erase_le

/- ============================================================================================
   APPENDED — stage 6 W-53 track K (`w53-k`): D142 in any logging order (README gap 5661) — a
   break held on top of the others re-draws every held break it reaches back to (`Replay.reachFx`,
   `DayOp.redraw`, `DayAcc.redrawBrk`), the ending a D141 line lets go re-draws the breaks it
   covered (`Replay.growFx`), and where a re-drawing comes from (`Replay.NoRedraw`), which
   `BreakFold.BrkHeld` reads.  README gaps 5790-5809.
   ============================================================================================ -/
#print axioms Lime.Replay.reachGo_redraw
#print axioms Lime.Replay.startsGo_mem
#print axioms Lime.Replay.growFx_redraw
#print axioms Lime.Replay.redrawOnly_filterMap
#print axioms Lime.Replay.redrawOnly_all
#print axioms Lime.Replay.endRecs_cases
#print axioms Lime.Replay.brkArm_mem
#print axioms Lime.Replay.reachFx_filterMap
#print axioms Lime.Replay.growFx_filterMap
#print axioms Lime.Replay.reachFx_redraw
#print axioms Lime.Replay.noRedraw_nil
#print axioms Lime.Replay.noRedraw_append
#print axioms Lime.Replay.noRedraw_flatten
#print axioms Lime.Replay.redraw_noRedraw
#print axioms Lime.Replay.settle_noRedraw
#print axioms Lime.Replay.closePause_noRedraw
#print axioms Lime.Replay.creditFx_noRedraw
#print axioms Lime.Replay.uncreditFx_noRedraw
#print axioms Lime.Replay.obsFx_noRedraw
#print axioms Lime.Replay.cut_noRedraw
#print axioms Lime.Replay.netOne_noRedraw
#print axioms Lime.Replay.netClosed_noRedraw
#print axioms Lime.Replay.giveBack_noRedraw
#print axioms Lime.Replay.netStart_noRedraw
#print axioms Lime.Replay.runNet_noRedraw
#print axioms Lime.Replay.doneClose_noRedraw
#print axioms Lime.Replay.machineList_noRedraw
#print axioms Lime.Replay.brkFx_noRedraw
#print axioms Lime.Replay.doneFx_noRedraw
#print axioms Lime.Replay.extendFx_noRedraw
#print axioms Lime.Replay.dayArm_noRedraw
#print axioms Lime.Replay.completionArm_noRedraw
#print axioms Lime.Replay.startArm_noRedraw
#print axioms Lime.Replay.brkStartArm_noRedraw
#print axioms Lime.Replay.arm_noRedraw
#print axioms Lime.Replay.brkDay_noRedraw
#print axioms Lime.Replay.drawSeg_mem
#print axioms Lime.Replay.three_overlapping_breaks_logged_a_b_c_are_one_day
#print axioms Lime.Replay.three_overlapping_breaks_logged_a_c_b_are_one_day
#print axioms Lime.Replay.three_overlapping_breaks_logged_b_a_c_are_one_day
#print axioms Lime.Replay.three_overlapping_breaks_logged_b_c_a_are_one_day
#print axioms Lime.Replay.three_overlapping_breaks_logged_c_a_b_are_one_day
#print axioms Lime.Replay.three_overlapping_breaks_logged_c_b_a_are_one_day
#print axioms Lime.Replay.a_break_a_later_logged_ending_covers_is_drawn_from_its_end
#print axioms Lime.Replay.a_break_a_later_logged_ending_covers_is_recorded_zero
#print axioms Lime.Replay.a_block_two_overlapping_late_breaks_cover_is_netted_by_their_union
#print axioms Lime.Replay.a_block_is_netted_by_the_union_once_the_line_lets_the_ending_go
#print axioms Lime.Replay.a_break_an_ending_covered_is_drawn_again_when_its_line_lets_it_go
#print axioms Lime.Replay.a_break_an_ending_covered_is_recorded_again_when_its_line_lets_it_go
#print axioms Lime.Replay.reachFx_reaches_a_later_stamped_break
#print axioms Lime.Replay.growFx_re_draws_the_break_the_ending_covered
#print axioms Lime.Replay.a_held_breaks_drawing_moves_on_data

/- ======================================================================
   APPENDED — stage 6 W-53 repair track K (`w53r-k`): a held break's identity (README gap 5791) and the breaks
   with their own `break` line on the wire (D147's fact, `open.finished`).
   ====================================================================== -/
#print axioms Lime.Replay.col3_is_one_day_in_either_logging_order
#print axioms Lime.Replay.col2_draws_each_minute_once
#print axioms Lime.Seal.openFinished_reads_state
#print axioms Lime.Seal.answer_openFinished
#print axioms Lime.Replay.arm_brk_eq
#print axioms Lime.Replay.arm_brk_of_endable_as_w52r_stated_it_is_refuted
#print axioms Lime.Replay.brkLine_machines
#print axioms Lime.Replay.brkLine_mem
#print axioms Lime.Replay.brkOwn_machines
#print axioms Lime.Replay.brkOwn_mem
#print axioms Lime.Replay.netTake_pendLines
#print axioms Lime.Replay.netTake_snd
#print axioms Lime.Replay.a_later_longer_line_reads_as_the_union
#print axioms Lime.Replay.a_later_shorter_line_at_a_finished_breaks_stamp_re_times_it
#print axioms Lime.PlanCheck.brkCover_ge
#print axioms Lime.PlannerWit.a_running_break_is_drawn_from_where_the_logged_breaks_stop
#print axioms Lime.PlannerWit.the_running_break_row_starts_where_it_started_as_w35_stated_it_is_refuted
#print axioms Lime.Replay.two_finished_breaks_at_one_stamp_stay_two

/-! APPENDED 2026-11-03, stage 6 W-54 track K (README gaps 5870-5889): the re-time's give-back from an open block
    (`openTakes`), the later nettings kept, the exact un-draw, the P127 take kept, the finished-break fact's contract,
    twins as one, the widest end, and the refutations of the W-53 repair's unrefuted old forms and of this step's
    restated `arm_brk_of_endable`. -/
#print axioms Lime.Replay.brkArmK_mem
#print axioms Lime.Replay.finished_mem
#print axioms Lime.Replay.finished_of_running
#print axioms Lime.Replay.a_finished_break_is_re_timed_by_its_line
#print axioms Lime.Replay.pruneBrks_pair_ne
#print axioms Lime.Replay.arm_brk_of_endable_as_w54_stated_it_is_refuted
#print axioms Lime.Replay.the_fact_holds_no_break_on_the_col3_log
#print axioms Lime.Replay.the_finished_breaks_are_the_held_breaks_with_their_own_line_as_w53r_stated_it_is_refuted
#print axioms Lime.Seal.openTakes_mi
#print axioms Lime.Seal.arm_brks_as_w53_stated_it_is_refuted
#print axioms Lime.BreakFold.stepWith_brks_as_w53_stated_it_is_refuted
#print axioms Lime.BreakFold.stepWith_brks_of_brk_as_w53_stated_it_is_refuted
#print axioms Lime.Replay.a_retime_gives_back_what_the_break_took_from_an_open_block
#print axioms Lime.Replay.a_retime_keeps_a_later_breaks_take
#print axioms Lime.Replay.col3_with_a_retime_is_one_day_in_every_logging_order
#print axioms Lime.Replay.a_retime_of_a_p127_break_gives_back_its_take
#print axioms Lime.Replay.the_fact_omits_a_break_a_newer_one_overlaps
#print axioms Lime.Replay.twin_finished_breaks_are_re_timed_as_one
#print axioms Lime.Replay.a_finished_break_keeps_its_widest_end
#print axioms Lime.Replay.a_longer_line_raises_the_widest_end
#print axioms Lime.Replay.a_retime_gives_back_only_what_a_paused_block_worked
#print axioms Lime.Replay.a_p127_line_lets_its_ending_go
#print axioms Lime.Replay.a_retime_raises_the_duration_observation

/-! APPENDED 2026-11-03, stage 6 W-54 repair track K (README gaps 5920-5939): the owner's D145 (a finished break's line
    ends only its own break: the parked reading, its laws through the window and the fold), D151 (the widest end is the
    break's own lines'), the finished-break fact's overlap filter, and D152's replay witness.  Three audit lines above were
    renamed with their theorems (a D105 witness refuted by D145, a W-53r refutation withdrawn by D151 and replaced by W-54's,
    the W-54 fact witness restated). -/
#print axioms Lime.BreakFold.arm_of_parked
#print axioms Lime.BreakFold.brkPark_of_none
#print axioms Lime.BreakFold.stepWith_brks_of_brk_as_w54_stated_it_is_refuted
#print axioms Lime.BreakFold.stepWith_brks_of_park
#print axioms Lime.Replay.a_break_line_in_the_running_breaks_minute_ends_it
#print axioms Lime.Replay.a_finished_break_whose_drawn_piece_another_meets_is_omitted
#print axioms Lime.Replay.a_finished_break_inside_the_running_block_nets_it_and_leaves_it_running
#print axioms Lime.Replay.a_finished_line_ends_only_its_own_break
#print axioms Lime.Replay.all_machine
#print axioms Lime.Replay.an_omitted_finished_break_draws_no_piece_of_its_own
#print axioms Lime.Replay.a_parked_line_is_read_at_its_own_place
#print axioms Lime.Replay.a_parked_line_leaves_the_running_break_running
#print axioms Lime.Replay.a_parked_line_reads_as_if_logged_before_the_running_break
#print axioms Lime.Replay.applyEffects_lastMach
#print axioms Lime.Replay.arm_brk_eq_as_w53r_stated_it_is_refuted
#print axioms Lime.Replay.arm_brk_of_endable_third_as_w54_stated_it_is_refuted
#print axioms Lime.Replay.arm_brk_parked_keeps_the_running_break
#print axioms Lime.Replay.brkPark_machines
#print axioms Lime.Replay.brkPark_mem
#print axioms Lime.Replay.lastMach_cases
#print axioms Lime.Replay.lastMach_eq
#print axioms Lime.Replay.givesUp_of_ownDrawn
#print axioms Lime.Replay.the_finished_breaks_are_the_ones_a_line_re_times_as_w54_stated_it_is_refuted
#print axioms Lime.Replay.the_widest_end_is_the_breaks_own_lines
#print axioms Lime.Seal.arm_brk_machine_keeps
#print axioms Lime.Seal.brkArmK_congr_mi
#print axioms Lime.Seal.brkArmK_mi
#print axioms Lime.Seal.brkLine_congr
#print axioms Lime.Seal.brkLine_mi
#print axioms Lime.Seal.brkPark_congr
#print axioms Lime.Seal.brkPark_machine_cases
#print axioms Lime.Seal.brkPark_machine_keeps
#print axioms Lime.Seal.brkPark_mi
#print axioms Lime.Seal.d141OrArm_congr
#print axioms Lime.Seal.d141OrArm_keeps
#print axioms Lime.Seal.d141OrArm_mi
#print axioms Lime.Seal.mi_upd
#print axioms Lime.Seal.reopen_keeps
#print axioms Lime.Seal.reopen_mi

/-! APPENDED 2026-11-04, stage 6 W-54 second repair track K (README gaps 5970-5989): the finished-break fact lists a break
   whose drawn piece is its own (`Replay.ownDrawn`, replacing otherMeets), and a re-time of a finished break is read where
   it gives up nothing another held break covers (`Replay.givesUp`, `Replay.retimeBlocked`, replacing `newerMeets` for a
   finished break in `d141Ok`).  Three entries above were renamed in place, one per theorem restated under a new name:
   `an_omitted_finished_break_draws_no_piece_of_its_own`, `givesUp_of_ownDrawn` and
   `a_finished_break_whose_drawn_piece_another_meets_is_omitted`. -/
#print axioms Lime.Replay.retimeBlocked_of_ended
#print axioms Lime.Replay.retimeBlocked_of_finished
#print axioms Lime.Replay.a_frozen_break_is_not_re_timed
#print axioms Lime.Replay.ownDrawn_eq_false_iff
#print axioms Lime.Replay.a_head_clipped_break_is_re_timed_in_its_own_piece
#print axioms Lime.Replay.a_line_ending_inside_another_breaks_stretch_re_times_it
#print axioms Lime.Replay.a_retime_of_a_covering_break_off_a_later_ones_head_is_read
#print axioms Lime.Replay.a_retime_of_an_outer_break_past_a_nested_one_is_read
#print axioms Lime.Replay.a_retime_giving_up_nothing_another_break_covers_is_read_over_a_newer_one
#print axioms Lime.Replay.a_break_re_timed_out_over_a_nested_one_is_read
#print axioms Lime.Replay.a_retime_over_an_overlapped_break_leaves_the_running_block_net_of_the_union
#print axioms Lime.Replay.an_identical_line_re_times_a_break_a_newer_one_overlaps
#print axioms Lime.Replay.a_finished_break_is_re_timed_by_its_line_as_w54_stated_it_is_refuted
#print axioms Lime.Replay.a_finished_break_another_overlaps_is_omitted_as_w54r_stated_it_is_refuted
#print axioms Lime.Replay.the_fact_omits_a_break_a_newer_one_overlaps_as_w54r_stated_it_is_refuted

/-! APPENDED 2026-11-05, stage 6 W-54 third repair track K (README gaps 6020-6039): a take put back whole, a shared stretch let
go read and the break it leaves short frozen, one fact per held break, the log's typed-time lines (the owner's D154). -/
#print axioms Lime.Replay.endOf_hb
#print axioms Lime.Replay.heldFact_retimeFrom
#print axioms Lime.Replay.heldFact_outTo
#print axioms Lime.Replay.a_held_break_is_re_timed_in_its_range
#print axioms Lime.Replay.a_held_break_is_re_timed_only_in_its_range
#print axioms Lime.Replay.a_piece_wider_than_a_take_is_put_back_whole
#print axioms Lime.Replay.a_retime_out_over_a_later_break_keeps_the_takes_with_the_union
#print axioms Lime.Replay.the_fact_holds_every_held_break_unclipped
#print axioms Lime.Replay.a_retime_letting_go_of_a_shared_stretch_freezes_the_other
#print axioms Lime.Replay.a_frozen_break_is_not_re_timed_on_the_log
#print axioms Lime.Replay.the_outer_break_is_re_timed_past_a_nested_one_and_freezes_it
#print axioms Lime.Replay.c2_and_d3_are_in_range
#print axioms Lime.Replay.gap_5973s_day_freezes_the_older_break
#print axioms Lime.Replay.the_fact_is_empty_of_ranges_while_a_break_runs
#print axioms Lime.Replay.a_retime_that_gives_up_another_breaks_stretch_is_not_read_as_w54r2_stated_it_is_refuted
#print axioms Lime.Replay.a_finished_break_is_re_timed_by_its_line_as_w54r2_stated_it_is_refuted
#print axioms Lime.Seal.maxTyped_is_the_latest_typed_stamp
#print axioms Lime.Seal.heldJson_shape
#print axioms Lime.Seal.openHeld_reads_state
#print axioms Lime.Seal.answer_openHeld
#print axioms Lime.Seal.ckpt_maxTyped
#print axioms Lime.Seal.resealed_maxTyped
#print axioms Lime.Seal.typedOf_append
#print axioms Lime.Seal.typedOf_sub
#print axioms Lime.Seal.latestTyped_is_the_whole_logs
#print axioms Lime.Seal.latestTyped_skips_a_far_future_line_and_counts_an_undone_one
#print axioms Lime.typedOf_without_a_fence
#print axioms Lime.typedOf_with_a_fence
#print axioms Lime.readFenceField_reads_and_refuses
#print axioms Lime.CapWire.corpus_request_day_one
#print axioms Lime.CapWire.corpus_request_too_long
#print axioms Lime.CapWire.corpus_request_without_a_zone
#print axioms Lime.the_fence_is_named_on_the_wire
#print axioms Lime.Seal.kMaxTyped_is_its_key
#print axioms Lime.Seal.maxTyped_is_named_on_the_wire
#print axioms Lime.a_bad_fence_is_refused_by_its_name
#print axioms Lime.typedOf_with_a_fence_keys_it
#print axioms Lime.readFenceField_of_a_string
#print axioms Lime.logBodyV_is_logBody
#print axioms Lime.resumedV_is_resumed
#print axioms Lime.Seal.resealOfWith_answers_a_valid_cut
