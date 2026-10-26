import NLA.Proofs.TR04.MachineTTFirstSelectionFamily
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine
open NLA.Proofs.TR04.TensorFormat.TTStrict
namespace FirstSelectionExactConsumer
theorem literal_every_legal_reply_family {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 167) (hs : s.status = .running)
    (hp : s.natural 105 = min (s.natural 81) (s.natural 82))
    (hr : 1 ≤ s.natural 80) (hzero : s.natural 127 = 0)
    (hcap : s.natural 106 = min (s.natural 80) (min (s.natural 81) (s.natural 82)))
    (hd : OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74)) :
    ∃ U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ,
    ∃ sigma : Fin (min (s.natural 81) (s.natural 82)) → ℝ,
    ∃ V : Matrix (Fin (s.natural 82)) (Fin (s.natural 82)) ℝ,
    ∃ hvalid : ValidSVD (readMatrix s.memory (s.natural 81) (s.natural 82) (s.natural 92)) U sigma V,
    ∃ n : ℕ,
      n ≤ 9 * min (s.natural 81) (s.natural 82) + 24 ∧
      (trace.state (offset + n)).label = 189 ∧ (trace.state (offset + n)).status = .running ∧
      TTFirstSelected (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
        (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr) (trace.state (offset + n)) ∧
      (∀ inputBase outputBase, TTFirstChoiceRealizes U
        (ttFirstChoice sigma hvalid.2.2.2.1 (s.natural 80)
          (min (s.natural 80) (min (s.natural 81) (s.natural 82))) hr)
        (explicitFirstFrames hvalid (s.natural 80)) inputBase outputBase) ∧
      (trace.state (offset + n)).memory =
        writeSVD s.memory (s.natural 72) (s.natural 73) (s.natural 74) U sigma V ∧
      (∀ j : Fin 128, TTFirstProtected j → (trace.state (offset + n)).natural j = s.natural j) ∧
      CostThrough ttProgram trace (offset + n) ≤ CostThrough ttProgram trace offset +
        (s.natural 81 + s.natural 82 + 1)^3 + (9 * min (s.natural 81) (s.natural 82) + 23) := by
  exact ttFirstSelection_svd_family ht offset s he hl hs hp hr hzero hcap hd
#assert_trust kernel literal_every_legal_reply_family
#print axioms literal_every_legal_reply_family

theorem literal_actual_readonly_counts {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 168) (hs : s.status = .running)
    (hr : ¬s.natural 105 < s.natural 80)
    (hz : (s.natural 127 : ℝ) < s.memory (s.natural 73 + (s.natural 80 - 1))) :
    let P : ThresholdScanParameters := ⟨s.natural 105, s.natural 80, s.natural 73⟩
    let tau := s.memory (s.natural 73 + (s.natural 80 - 1))
    let n := offset + (9 * P.count + 23)
    (trace.state n).label = 189 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural 77 = thresholdAboveCount s.memory P tau P.count ∧
      (trace.state n).natural 78 = thresholdTiedCount s.memory P tau P.count ∧
      (trace.state n).natural 79 = thresholdTakeCount s.memory P tau P.count ∧
      (trace.state n).natural 75 = thresholdTiedCount s.memory P tau P.count ∧
      TTFirstPreserves s (trace.state n) ∧
      CostThrough ttProgram trace n ≤ CostThrough ttProgram trace offset + (9 * P.count + 23) := by
  exact ttFirstSelection_positive_run ht offset s he hl hs hr hz
#assert_trust kernel literal_actual_readonly_counts
#print axioms literal_actual_readonly_counts

theorem literal_prefix_full_width (m : ℕ) : (prefixGatherParameters m m 0 0).Valid :=
  prefixGatherParameters_valid m m 0 0 le_rfl
#assert_trust kernel literal_prefix_full_width
#print axioms literal_prefix_full_width

theorem literal_prefix_empty : (prefixGatherParameters 0 0 0 0).Valid :=
  prefixGatherParameters_valid 0 0 0 0 le_rfl
#assert_trust kernel literal_prefix_empty
#print axioms literal_prefix_empty

theorem literal_corrected_prefix_code : ttProgram.code 185 = .natural 78 1 186 := rfl
#assert_trust kernel literal_corrected_prefix_code
#print axioms literal_corrected_prefix_code
end FirstSelectionExactConsumer

#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_nonzero_reals
#print axioms NLA.Proofs.TR04.ttFirstSelection_nonzero_reals
#assert_trust kernel NLA.Proofs.TR04.ttFirstPrefixResult
#print axioms NLA.Proofs.TR04.ttFirstPrefixResult
#assert_trust kernel NLA.Proofs.TR04.ttFirstThresholdRead
#print axioms NLA.Proofs.TR04.ttFirstThresholdRead
#assert_trust kernel NLA.Proofs.TR04.ttFirstThresholdEntry
#print axioms NLA.Proofs.TR04.ttFirstThresholdEntry
#assert_trust kernel NLA.Proofs.TR04.ttFirstCountResult
#print axioms NLA.Proofs.TR04.ttFirstCountResult
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_prefix_five
#print axioms NLA.Proofs.TR04.ttFirstSelection_prefix_five
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_large_six
#print axioms NLA.Proofs.TR04.ttFirstSelection_large_six
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_read_seven
#print axioms NLA.Proofs.TR04.ttFirstSelection_read_seven
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_nonpositive_twelve
#print axioms NLA.Proofs.TR04.ttFirstSelection_nonpositive_twelve
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_setup_four
#print axioms NLA.Proofs.TR04.ttFirstSelection_setup_four
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_return_six
#print axioms NLA.Proofs.TR04.ttFirstSelection_return_six
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_not_svd
#print axioms NLA.Proofs.TR04.ttFirstSelection_not_svd
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_prefix_safe
#print axioms NLA.Proofs.TR04.ttFirstSelection_prefix_safe
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_large_safe
#print axioms NLA.Proofs.TR04.ttFirstSelection_large_safe
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_read_safe
#print axioms NLA.Proofs.TR04.ttFirstSelection_read_safe
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_nonpositive_safe
#print axioms NLA.Proofs.TR04.ttFirstSelection_nonpositive_safe
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_setup_safe
#print axioms NLA.Proofs.TR04.ttFirstSelection_setup_safe
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_return_safe
#print axioms NLA.Proofs.TR04.ttFirstSelection_return_safe
#assert_trust kernel NLA.Proofs.TR04.TTFirstProtected
#print axioms NLA.Proofs.TR04.TTFirstProtected
#assert_trust kernel NLA.Proofs.TR04.TTFirstPreserves
#print axioms NLA.Proofs.TR04.TTFirstPreserves
#assert_trust kernel NLA.Proofs.TR04.ttFirstPreserves_trans
#print axioms NLA.Proofs.TR04.ttFirstPreserves_trans
#assert_trust kernel NLA.Proofs.TR04.ttFirstPrefix_preserves
#print axioms NLA.Proofs.TR04.ttFirstPrefix_preserves
#assert_trust kernel NLA.Proofs.TR04.ttFirstRead_preserves
#print axioms NLA.Proofs.TR04.ttFirstRead_preserves
#assert_trust kernel NLA.Proofs.TR04.ttFirstEntry_preserves
#print axioms NLA.Proofs.TR04.ttFirstEntry_preserves
#assert_trust kernel NLA.Proofs.TR04.ttFirstCount_preserves
#print axioms NLA.Proofs.TR04.ttFirstCount_preserves
#assert_trust kernel NLA.Proofs.TR04.ttFirstThresholdAux
#print axioms NLA.Proofs.TR04.ttFirstThresholdAux
#assert_trust kernel NLA.Proofs.TR04.ttFirstThreshold_relates
#print axioms NLA.Proofs.TR04.ttFirstThreshold_relates
#assert_trust kernel NLA.Proofs.TR04.ttFirstThreshold_outside
#print axioms NLA.Proofs.TR04.ttFirstThreshold_outside
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_large_run
#print axioms NLA.Proofs.TR04.ttFirstSelection_large_run
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_nonpositive_run
#print axioms NLA.Proofs.TR04.ttFirstSelection_nonpositive_run
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_positive_run
#print axioms NLA.Proofs.TR04.ttFirstSelection_positive_run
#assert_trust kernel NLA.Proofs.TR04.TTFirstChoice
#print axioms NLA.Proofs.TR04.TTFirstChoice
#assert_trust kernel NLA.Proofs.TR04.ttFirstPrefixChoice
#print axioms NLA.Proofs.TR04.ttFirstPrefixChoice
#assert_trust kernel NLA.Proofs.TR04.ttFirstChoice
#print axioms NLA.Proofs.TR04.ttFirstChoice
#assert_trust kernel NLA.Proofs.TR04.TTFirstSelected
#print axioms NLA.Proofs.TR04.TTFirstSelected
#assert_trust kernel NLA.Proofs.TR04.ttFirstChoice_count_pos
#print axioms NLA.Proofs.TR04.ttFirstChoice_count_pos
#assert_trust kernel NLA.Proofs.TR04.ttFirstChoice_width
#print axioms NLA.Proofs.TR04.ttFirstChoice_width
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_run
#print axioms NLA.Proofs.TR04.ttFirstSelection_run
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_svd_run
#print axioms NLA.Proofs.TR04.ttFirstSelection_svd_run
#assert_trust kernel NLA.Proofs.TR04.ttFirstGatherParameters
#print axioms NLA.Proofs.TR04.ttFirstGatherParameters
#assert_trust kernel NLA.Proofs.TR04.TTFirstChoiceRealizes
#print axioms NLA.Proofs.TR04.TTFirstChoiceRealizes
#assert_trust kernel NLA.Proofs.TR04.ttFirstPrefix_realizes
#print axioms NLA.Proofs.TR04.ttFirstPrefix_realizes
#assert_trust kernel NLA.Proofs.TR04.ttFirstChoice_realizes_explicit
#print axioms NLA.Proofs.TR04.ttFirstChoice_realizes_explicit
#assert_trust kernel NLA.Proofs.TR04.ttFirstSelection_svd_family
#print axioms NLA.Proofs.TR04.ttFirstSelection_svd_family
