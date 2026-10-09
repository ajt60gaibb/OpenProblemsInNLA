import NLA.IE06.PivotFiltration
import NLA.IE06.GaussianLinear
import NLA.IE06.GrowthEvents

/-! Exact transfer from canonical elimination row norms to all-Schur Gaussian
exceedance probabilities. Preimplementation review is recorded separately. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace NLA.IE06.GaussianEliminationTail
open PivotFiltration GaussianLinear GaussianQuadratic

def RowCap {n : ℕ} (E : Mat n) (L : ℝ) : Prop :=
  ∀ i, squareNorm (E i) ≤ L

def linearBadEvent (n : ℕ) (L x : ℝ) : Set (Mat n × (Fin n → ℝ)) :=
  {p | RowCap p.1 L ∧ ∃ i, Real.sqrt (2*x*L) < |dot (p.1 i) p.2|}

theorem linearBadEvent_measurable (n : ℕ) (L x : ℝ) :
    MeasurableSet (linearBadEvent n L x) := by
  simp only [linearBadEvent, RowCap, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    unfold squareNorm
    fun_prop
  · apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    unfold dot
    fun_prop

private theorem linearBadEvent_fiber_le {n : ℕ} (E : Mat n) (L x : ℝ)
    (hL : 0 ≤ L) (hx : 0 < x) :
    gaussianVector n (Prod.mk E ⁻¹' linearBadEvent n L x) ≤
      (2*(n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) := by
  by_cases hE : RowCap E L
  · have hs : Prod.mk E ⁻¹' linearBadEvent n L x =
        {z | ∃ i, Real.sqrt (2*x*L) < |dot (E i) z|} := by
      ext z
      simp only [Set.mem_preimage, linearBadEvent, Set.mem_ofPred_eq, hE, true_and]
    rw [hs]
    exact rows_tail E L x hL hE hx
  · have hs : Prod.mk E ⁻¹' linearBadEvent n L x = ∅ := by
      ext z
      simp only [Set.mem_preimage, linearBadEvent, Set.mem_ofPred_eq, hE, false_and,
        Set.mem_empty_iff_false]
    rw [hs, measure_empty]
    exact zero_le

/-- The cap is checked at this stage only, before integrating the fresh column.
No global-good-event conditioning occurs. -/
theorem stage_column_tail {n : ℕ} (k : ℕ) (j : Fin n) (hj : k ≤ j.val)
    (L x : ℝ) (hL : 0 ≤ L) (hx : 0 < x) :
    gaussianMatrix n {A : Mat n | RowCap (selectedRows A k) L ∧
      ∃ i, Real.sqrt (2*x*L) < |dot (selectedRows A k i) (column j A)|} ≤
      (2*(n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) := by
  let μ := (gaussianMatrix n).map (fun A : Mat n => selectedRows A k)
  have hm := measurable_selectedRows (n := n) k
  let : IsProbabilityMeasure (gaussianMatrix n) := gaussianMatrix_probability_proved n
  have hmass : μ Set.univ = 1 := by
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp
  have hp : μ.prod (gaussianVector n) (linearBadEvent n L x) ≤
      (2*(n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) := by
    rw [Measure.prod_apply (linearBadEvent_measurable n L x)]
    calc
      _ ≤ ∫⁻ _ : Mat n, (2*(n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) ∂μ :=
        lintegral_mono (fun E => linearBadEvent_fiber_le E L x hL hx)
      _ = _ := by rw [lintegral_const, hmass, mul_one]
  have hlaw := selectedRows_column_joint_law k j hj
  change (gaussianMatrix n).map (fun A : Mat n => (selectedRows A k, column j A)) =
    μ.prod (gaussianVector n) at hlaw
  rw [← hlaw, Measure.map_apply (hm.prodMk (measurable_column j))
    (linearBadEvent_measurable n L x)] at hp
  exact hp

/-- A pointwise finite-maximum bound; only the active entries are tested. -/
theorem rawSchurMax_le {n : ℕ} (A : Mat n) (path : PivotPath n) (t : ℝ)
    (ht : 0 ≤ t)
    (h : ∀ k : Fin n, ∀ i j : Fin n, k.val ≤ i.val → k.val ≤ j.val →
      |trajectory A path k.val i j| ≤ t) : rawSchurMax A path ≤ t := by
  unfold rawSchurMax
  rw [← Real.coe_toNNReal t ht, NNReal.coe_le_coe]
  apply Finset.sup_le_iff.mpr
  intro k _
  unfold activeMaxNN
  apply Finset.sup_le_iff.mpr
  intro ij _
  split_ifs with hij
  · apply NNReal.coe_le_coe.mp
    simpa only [coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal t ht] using
      h k ij.1 ij.2 hij.1 hij.2
  · exact zero_le

def AllRowsCap {n : ℕ} (A : Mat n) (L : ℝ) : Prop :=
  ∀ k : Fin n, RowCap (selectedRows A k.val) L

def stagePairEvent (n : ℕ) (L x : ℝ) (p : Fin n × Fin n) : Set (Mat n) :=
  {A | p.1.val ≤ p.2.val ∧ RowCap (selectedRows A p.1.val) L ∧
    ∃ i, Real.sqrt (2*x*L) < |dot (selectedRows A p.1.val i) (column p.2 A)|}

private theorem stagePairEvent_le {n : ℕ} (L x : ℝ) (hL : 0 ≤ L) (hx : 0 < x)
    (p : Fin n × Fin n) : gaussianMatrix n (stagePairEvent n L x p) ≤
      (2*(n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) := by
  by_cases hj : p.1.val ≤ p.2.val
  · simpa only [stagePairEvent, hj, true_and] using stage_column_tail p.1.val p.2 hj L x hL hx
  · simp only [stagePairEvent, hj, false_and, Set.ofPred_false, measure_empty]
    exact zero_le

theorem guarded_raw_subset (n : ℕ) (L x : ℝ) (_hL : 0 ≤ L) (_hx : 0 < x) :
    {A : Mat n | AllRowsCap A L ∧ Real.sqrt (2*x*L) < rawSchurMax A (firstPath A)} ⊆
      ⋃ p : Fin n × Fin n, stagePairEvent n L x p := by
  classical
  intro A hA
  change AllRowsCap A L ∧ Real.sqrt (2*x*L) < rawSchurMax A (firstPath A) at hA
  by_contra hnot
  have hentries (k : Fin n) (i j : Fin n) (_hi : k.val ≤ i.val) (hj : k.val ≤ j.val) :
      |trajectory A (firstPath A) k.val i j| ≤ Real.sqrt (2*x*L) := by
    by_contra hgt
    have he : dot (selectedRows A k.val i) (column j A) =
        trajectory A (firstPath A) k.val i j := by
      have he := eliminationRows_mul A (firstPath A) k.val i j hj
      rw [Matrix.mul_apply] at he
      dsimp [Matrix.of] at he
      exact he
    apply hnot
    apply Set.mem_iUnion.mpr
    refine ⟨(k,j), hj, hA.1 k, i, ?_⟩
    rw [he]
    exact lt_of_not_ge hgt
  exact (not_lt_of_ge (rawSchurMax_le A (firstPath A) _ (Real.sqrt_nonneg _) hentries)) hA.2

/-- Exact all-stage transfer using fresh-column product laws and a finite union.
The global row guard is only used for set containment. -/
theorem guarded_raw_tail (n : ℕ) (L x : ℝ) (hL : 0 ≤ L) (hx : 0 < x) :
    gaussianMatrix n {A : Mat n | AllRowsCap A L ∧
      Real.sqrt (2*x*L) < rawSchurMax A (firstPath A)} ≤
      (2*(n : ℝ≥0∞)^3) * ENNReal.ofReal (Real.exp (-x)) := by
  calc
    _ ≤ gaussianMatrix n (⋃ p : Fin n × Fin n, stagePairEvent n L x p) :=
      measure_mono (guarded_raw_subset n L x hL hx)
    _ ≤ ∑ p : Fin n × Fin n, gaussianMatrix n (stagePairEvent n L x p) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ : Fin n × Fin n, (2*(n : ℝ≥0∞)) * ENNReal.ofReal (Real.exp (-x)) :=
      Finset.sum_le_sum (fun p _ => stagePairEvent_le L x hL hx p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

def badRowsEvent (n : ℕ) (L : ℝ) : Set (Mat n) :=
  {A | ∃ k : Fin n, ∃ i : Fin n, L < squareNorm (selectedRows A k.val i)}

theorem canonicalRaw_measure_le_badRows_add (n : ℕ) (L x : ℝ) (hL : 0 ≤ L) (hx : 0 < x) :
    gaussianMatrix n (canonicalRawEvent n (Real.sqrt (2*x*L))) ≤
      gaussianMatrix n (badRowsEvent n L) +
      (2*(n : ℝ≥0∞)^3) * ENNReal.ofReal (Real.exp (-x)) := by
  classical
  have hs : canonicalRawEvent n (Real.sqrt (2*x*L)) ⊆ badRowsEvent n L ∪
      {A : Mat n | AllRowsCap A L ∧ Real.sqrt (2*x*L) < rawSchurMax A (firstPath A)} := by
    intro A hA
    by_cases hcap : AllRowsCap A L
    · exact Or.inr ⟨hcap, hA⟩
    · left
      simp only [AllRowsCap, RowCap, not_forall, not_le] at hcap
      exact hcap
  exact (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (guarded_raw_tail n L x hL hx)))

theorem normalized_tail_transfer (n : ℕ) (L x : ℝ) (hL : 0 ≤ L) (hx : 0 < x) :
    gaussianMatrix n (exceedanceEvent n (Real.sqrt (2*x*L))) ≤
      gaussianMatrix n (badRowsEvent n L) +
      (2*(n : ℝ≥0∞)^3) * ENNReal.ofReal (Real.exp (-x)) +
      ENNReal.ofReal (gaussianUnitIntervalMass^(n^2)) :=
  (exceedanceEvent_measure_le_raw_add_exact_normalization n _).trans
    (add_le_add (canonicalRaw_measure_le_badRows_add n L x hL hx) le_rfl)

#assert_trust kernel rawSchurMax_le
#assert_trust kernel guarded_raw_subset
#assert_trust kernel guarded_raw_tail
#assert_trust kernel canonicalRaw_measure_le_badRows_add
#assert_trust kernel normalized_tail_transfer
#print axioms guarded_raw_tail
#print axioms normalized_tail_transfer
#assert_trust kernel linearBadEvent_measurable
#assert_trust kernel stage_column_tail
#print axioms stage_column_tail
end NLA.IE06.GaussianEliminationTail
