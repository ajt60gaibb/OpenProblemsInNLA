import NLA.Proofs.TR04.MachineThresholdScanSVD
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine
namespace ThresholdScanExactConsumer

theorem literal_standalone (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (aux : Fin 5 → ℕ) (trace : Trace thresholdScanProgram)
    (ht : LegalTrace thresholdScanProgram (thresholdScanStart memory P tau scratch aux) trace) :
    (trace.state (9 * P.count + 7)).status = .halted P.base ∧
      (trace.state (9 * P.count + 7)).natural 5 = ((Finset.range P.count).filter (fun i => tau < memory (P.base + i))).card ∧
      (trace.state (9 * P.count + 7)).natural 6 = ((Finset.range P.count).filter (fun i => memory (P.base + i) = tau)).card ∧
      (trace.state (9 * P.count + 7)).natural 7 = ((Finset.range P.count).filter (fun i => i < P.rank ∧ memory (P.base + i) = tau)).card ∧
      (trace.state (9 * P.count + 7)).real 0 = tau ∧
      (trace.state (9 * P.count + 7)).memory = memory ∧
      CostThrough thresholdScanProgram trace (9 * P.count + 7) ≤ 9 * P.count + 7 := by
  simpa only [thresholdAboveCount, thresholdTiedCount, thresholdTakeCount] using
    thresholdScanProgram_trace_result memory P tau scratch aux trace ht
#assert_trust kernel literal_standalone

theorem literal_caller {Q : Program} (E : RoutineEmbedding thresholdScanProgram Q)
    (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau scratch : ℝ) (aux : Fin 5 → ℕ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (thresholdScanStart memory P tau scratch aux) (trace.state offset))
    (ht : LegalTrace Q start trace) :
    let n := offset + (9 * P.count + 6)
    (trace.state n).label = E.labels 22 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural (E.naturals 5) = ((Finset.range P.count).filter (fun i => tau < memory (P.base + i))).card ∧
      (trace.state n).natural (E.naturals 6) = ((Finset.range P.count).filter (fun i => memory (P.base + i) = tau)).card ∧
      (trace.state n).natural (E.naturals 7) = ((Finset.range P.count).filter (fun i => i < P.rank ∧ memory (P.base + i) = tau)).card ∧
      (trace.state n).real (E.reals 0) = tau ∧ (trace.state n).memory = memory ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (9 * P.count + 6) := by
  simpa only [thresholdAboveCount, thresholdTiedCount, thresholdTakeCount] using
    E.thresholdScan_run_values memory P tau scratch aux offset hs ht
#assert_trust kernel literal_caller

theorem literal_validSVD_caller {Q : Program}
    (E : RoutineEmbedding thresholdScanProgram Q) {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (hValid : ValidSVD B U sigma V) (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ (min m l))
    (memory : ℕ → ℝ) (base : ℕ) (hmem : ∀ k : Fin (min m l), memory (base + k.val) = sigma k)
    (scratch : ℝ) (aux : Fin 5 → ℕ) {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (thresholdScanStart memory ⟨(min m l), r, base⟩
      (sigma ⟨r - 1, by omega⟩) scratch aux) (trace.state offset)) (ht : LegalTrace Q start trace) :
    let a : Fin (min m l) := ⟨r - 1, by omega⟩
    let T := SVD.countedTieStructure sigma hValid.2.2.2.1 a
    let n := offset + (9 * (min m l) + 6)
    (trace.state n).label = E.labels 22 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural (E.naturals 5) = T.above ∧
      (trace.state n).natural (E.naturals 6) = T.tied ∧
      (trace.state n).natural (E.naturals 7) = T.take ∧
      (trace.state n).natural (E.naturals 5) + (trace.state n).natural (E.naturals 7) = r ∧
      (trace.state n).real (E.reals 0) = sigma a ∧ (trace.state n).memory = memory ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (9 * (min m l) + 6) :=
  E.thresholdScan_run_counted sigma hValid.2.2.2.1 r hr hrp memory base hmem scratch aux offset hs ht
#assert_trust kernel literal_validSVD_caller
end ThresholdScanExactConsumer
#assert_trust kernel NLA.Proofs.TR04.ThresholdScanParameters
#print axioms NLA.Proofs.TR04.ThresholdScanParameters
#assert_trust kernel NLA.Proofs.TR04.thresholdAboveCount
#print axioms NLA.Proofs.TR04.thresholdAboveCount
#assert_trust kernel NLA.Proofs.TR04.thresholdTiedCount
#print axioms NLA.Proofs.TR04.thresholdTiedCount
#assert_trust kernel NLA.Proofs.TR04.thresholdTakeCount
#print axioms NLA.Proofs.TR04.thresholdTakeCount
#assert_trust kernel NLA.Proofs.TR04.thresholdAboveCount_zero
#print axioms NLA.Proofs.TR04.thresholdAboveCount_zero
#assert_trust kernel NLA.Proofs.TR04.thresholdTiedCount_zero
#print axioms NLA.Proofs.TR04.thresholdTiedCount_zero
#assert_trust kernel NLA.Proofs.TR04.thresholdTakeCount_zero
#print axioms NLA.Proofs.TR04.thresholdTakeCount_zero
#assert_trust kernel NLA.Proofs.TR04.thresholdAboveCount_succ
#print axioms NLA.Proofs.TR04.thresholdAboveCount_succ
#assert_trust kernel NLA.Proofs.TR04.thresholdTiedCount_succ
#print axioms NLA.Proofs.TR04.thresholdTiedCount_succ
#assert_trust kernel NLA.Proofs.TR04.thresholdTakeCount_succ
#print axioms NLA.Proofs.TR04.thresholdTakeCount_succ
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram
#print axioms NLA.Proofs.TR04.thresholdScanProgram
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals
#print axioms NLA.Proofs.TR04.thresholdScanProgram_nonzero_reals
#assert_trust kernel NLA.Proofs.TR04.thresholdScanLoopState
#print axioms NLA.Proofs.TR04.thresholdScanLoopState
#assert_trust kernel NLA.Proofs.TR04.thresholdScanStart
#print axioms NLA.Proofs.TR04.thresholdScanStart
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_scalar
#print axioms NLA.Proofs.TR04.thresholdScanProgram_scalar
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_initialize
#print axioms NLA.Proofs.TR04.thresholdScanProgram_initialize
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_nine_steps
#print axioms NLA.Proofs.TR04.thresholdScanProgram_nine_steps
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_iterations
#print axioms NLA.Proofs.TR04.thresholdScanProgram_iterations
#assert_trust kernel NLA.Proofs.TR04.thresholdScanReturnState
#print axioms NLA.Proofs.TR04.thresholdScanReturnState
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_return
#print axioms NLA.Proofs.TR04.thresholdScanProgram_return
#assert_trust kernel NLA.Proofs.TR04.thresholdScanProgram_trace_result
#print axioms NLA.Proofs.TR04.thresholdScanProgram_trace_result
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_values
#print axioms NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_values
#assert_trust kernel NLA.Proofs.TR04.thresholdCard_filter_range_fin
#print axioms NLA.Proofs.TR04.thresholdCard_filter_range_fin
#assert_trust kernel NLA.Proofs.TR04.thresholdCard_filter_fin_interval
#print axioms NLA.Proofs.TR04.thresholdCard_filter_fin_interval
#assert_trust kernel NLA.Proofs.TR04.thresholdCounts_countedTieStructure
#print axioms NLA.Proofs.TR04.thresholdCounts_countedTieStructure
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_counted
#print axioms NLA.Proofs.TR04.RoutineEmbedding.thresholdScan_run_counted
