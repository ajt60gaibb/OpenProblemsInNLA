import NLA.Proofs.TR04.MachineThresholdScanTrace
import NLA.Proofs.TR04.SVDExplicitTie

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem thresholdCard_filter_range_fin (p : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range p).filter P).card = ((Finset.univ : Finset (Fin p)).filter (fun i => P i.val)).card := by
  apply Finset.card_bij (fun k hk => (⟨k, Finset.mem_range.mp (Finset.mem_filter.mp hk).1⟩ : Fin p))
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩
  · intro i hi j hj he
    exact congrArg (fun k : Fin p => k.val) he
  · intro j hj
    refine ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, (Finset.mem_filter.mp hj).2⟩, ?_⟩
    exact Fin.ext rfl

theorem thresholdCard_filter_fin_interval {p : ℕ} (h s : ℕ) (hs : h + s ≤ p) :
    ((Finset.univ : Finset (Fin p)).filter (fun k => h ≤ k.val ∧ k.val < h + s)).card = s := by
  classical
  have hc : ((Finset.univ : Finset (Fin p)).filter
      (fun k => h ≤ k.val ∧ k.val < h + s)).card = (Finset.univ : Finset (Fin s)).card := by
    apply Finset.card_bij (fun k hk => (⟨k.val - h, by
      have hc := (Finset.mem_filter.mp hk).2
      omega⟩ : Fin s))
    · intro k hk
      exact Finset.mem_univ _
    · intro i hi j hj he
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      have hv := congrArg (fun k : Fin s => k.val) he
      apply Fin.ext
      dsimp at hv
      omega
    · intro j _
      refine ⟨⟨h + j.val, by omega⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by dsimp; omega⟩
      · apply Fin.ext
        dsimp
        omega
  exact hc.trans (by simp)

/-- The actual three finite-array scan counts are exactly the deterministic
complete threshold-block parameters. No sign assumption is needed for counting. -/
theorem thresholdCounts_countedTieStructure {p : ℕ} (sigma : Fin p → ℝ) (hord : Antitone sigma)
    (a : Fin p) (memory : ℕ → ℝ) (base : ℕ)
    (hmem : ∀ k : Fin p, memory (base + k.val) = sigma k) :
    let P : ThresholdScanParameters := ⟨p, a.val + 1, base⟩
    let T := SVD.countedTieStructure sigma hord a
    thresholdAboveCount memory P (sigma a) p = T.above ∧
      thresholdTiedCount memory P (sigma a) p = T.tied ∧
      thresholdTakeCount memory P (sigma a) p = T.take := by
  classical
  let T := SVD.countedTieStructure sigma hord a
  refine ⟨?_, ?_, ?_⟩
  · change ((Finset.range p).filter (fun i => sigma a < memory (base + i))).card = T.above
    rw [thresholdCard_filter_range_fin]
    simp_rw [hmem]
    exact (SVD.countedTieStructure_above sigma hord a).symm
  · change ((Finset.range p).filter (fun i => memory (base + i) = sigma a)).card = T.tied
    rw [thresholdCard_filter_range_fin]
    simp_rw [hmem, T.equal_iff]
    exact thresholdCard_filter_fin_interval T.above T.tied T.fits
  · change ((Finset.range p).filter (fun i => i < a.val + 1 ∧ memory (base + i) = sigma a)).card = T.take
    rw [thresholdCard_filter_range_fin]
    simp_rw [hmem, T.equal_iff]
    have he (k : Fin p) : (k.val < a.val + 1 ∧ T.above ≤ k.val ∧ k.val < T.above + T.tied) ↔
        (T.above ≤ k.val ∧ k.val < T.above + T.take) := by
      have hr := T.rank_eq
      have ht := T.take_le
      omega
    simp_rw [he]
    exact thresholdCard_filter_fin_interval T.above T.take (by rw [T.rank_eq]; omega)

/-- The actual caller registers contain the exact counted complete block for
every supplied ordered singular-value array at its retained rank threshold. -/
theorem RoutineEmbedding.thresholdScan_run_counted {Q : Program}
    (E : RoutineEmbedding thresholdScanProgram Q) {p : ℕ} (sigma : Fin p → ℝ)
    (hord : Antitone sigma) (r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p)
    (memory : ℕ → ℝ) (base : ℕ) (hmem : ∀ k : Fin p, memory (base + k.val) = sigma k)
    (scratch : ℝ) (aux : Fin 5 → ℕ) {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (thresholdScanStart memory ⟨p, r, base⟩
      (sigma ⟨r - 1, by omega⟩) scratch aux) (trace.state offset)) (ht : LegalTrace Q start trace) :
    let a : Fin p := ⟨r - 1, by omega⟩
    let T := SVD.countedTieStructure sigma hord a
    let n := offset + (9 * p + 6)
    (trace.state n).label = E.labels 22 ∧ (trace.state n).status = .running ∧
      (trace.state n).natural (E.naturals 5) = T.above ∧
      (trace.state n).natural (E.naturals 6) = T.tied ∧
      (trace.state n).natural (E.naturals 7) = T.take ∧
      (trace.state n).natural (E.naturals 5) + (trace.state n).natural (E.naturals 7) = r ∧
      (trace.state n).real (E.reals 0) = sigma a ∧ (trace.state n).memory = memory ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (9 * p + 6) := by
  let a : Fin p := ⟨r - 1, by omega⟩
  let T := SVD.countedTieStructure sigma hord a
  let P : ThresholdScanParameters := ⟨p, r, base⟩
  have har : a.val + 1 = r := by dsimp [a]; omega
  have hcounts : thresholdAboveCount memory P (sigma a) p = T.above ∧
      thresholdTiedCount memory P (sigma a) p = T.tied ∧
      thresholdTakeCount memory P (sigma a) p = T.take := by
    simpa only [har] using thresholdCounts_countedTieStructure sigma hord a memory base hmem
  obtain ⟨hl, hstatus, hA, hT, hS, hreal, hmemory, hcost⟩ :=
    E.thresholdScan_run_values memory P (sigma a) scratch aux offset hs ht
  have hA' := hA.trans hcounts.1
  have hT' := hT.trans hcounts.2.1
  have hS' := hS.trans hcounts.2.2
  refine ⟨hl, hstatus, hA', hT', hS', ?_, hreal, hmemory, hcost⟩
  rw [hA', hS', T.rank_eq, har]

#assert_trust kernel thresholdCard_filter_range_fin
#assert_trust kernel thresholdCard_filter_fin_interval
#assert_trust kernel thresholdCounts_countedTieStructure
#assert_trust kernel RoutineEmbedding.thresholdScan_run_counted
#print axioms thresholdCounts_countedTieStructure
end NLA.Proofs.TR04
