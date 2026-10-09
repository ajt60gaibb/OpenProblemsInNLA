import NLA.IE06.GaussianStageSmoothing
import NLA.IE06.GaussianEliminationTail

/-! Finite union of the actual stage bounds, with the reviewed early-stage
deterministic branch and no conditioning on a simultaneous success event. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianAllRows
open GaussianStageSmoothing GaussianSpectralBase TruncatedInverse EliminationSmoothing
open PivotFiltration GaussianEliminationTail

def rowBound (r : ℕ) (τ x : ℝ) : ℝ :=
  (2:ℝ)^(5*r)*Real.sqrt (1+(2+4*x)*τ)*
    (1+Real.sqrt (8*r+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r))

theorem rowNorm_le_rowL1 {n : ℕ} (E : Mat n) (i : Fin n) :
    rowNorm (Matrix.of E) i ≤ rowL1 E i := by
  apply (sq_le_sq₀ (rowNorm_nonneg _ _) (by unfold rowL1; positivity)).mp
  rw [rowNorm_sq]
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun j _ => abs_nonneg (E i j))
  simpa only [sq_abs,Matrix.of_apply,rowL1] using h

theorem rowBound_nonneg (r : ℕ) (τ x : ℝ) : 0 ≤ rowBound r τ x := by
  unfold rowBound
  positivity

theorem early_threshold_le (r : ℕ) {τ x : ℝ} (hτ : 0 ≤ τ) (hx : 0 ≤ x) :
    (2:ℝ)^(5*r) ≤ rowBound r τ x := by
  have hz : 1 ≤ Real.sqrt (1+(2+4*x)*τ) := by
    apply Real.one_le_sqrt.mpr
    have : 0 ≤ (2+4*x)*τ := by positivity
    linarith
  have hf : 1 ≤ 1+Real.sqrt (8*r+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r) :=
    le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ = (2:ℝ)^(5*r)*1*1 := by ring
    _ ≤ _ := by unfold rowBound; gcongr

theorem stage_threshold_le (r : ℕ) (τ x : ℝ) :
    GaussianFutureSmoothing.threshold (4*r) r (Real.sqrt (1+(2+4*x)*τ)) x ≤ rowBound r τ x := by
  have he : 2*((4*r:ℕ):ℝ)+4*x = 8*r+4*x := by push_cast; ring
  simp only [GaussianFutureSmoothing.threshold,rowBound,he]
  gcongr <;> norm_num

def inverseBad (n r : ℕ) (τ : ℝ) : Set (Mat n) :=
  {A | ∃ t, ∃ ht : t ≤ n, τ < sigmaInvSum (block ht A) r}

def lateStageEvent (n r : ℕ) (τ x : ℝ) (k : Fin n) : Set (Mat n) :=
  if h : 5*r < k.val then stageEvent (by omega : k.val-4*r ≤ n) r τ x else ∅

theorem lateStageEvent_tail {n r : ℕ} (hr : 1 ≤ r) {τ x : ℝ}
    (hτ : 0 ≤ τ) (hx : 0 < x) (k : Fin n) :
    gaussianMatrix n (lateStageEvent n r τ x k) ≤
      (2*(n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
  unfold lateStageEvent
  split_ifs with hk
  · exact stage_tail (by omega : k.val-4*r+4*r ≤ n) hr (by omega) hτ hx
  · rw [measure_empty]
    exact zero_le

theorem badRows_subset_ae {n r : ℕ} (hr : 1 ≤ r) {τ x : ℝ}
    (hτ : 0 ≤ τ) (hx : 0 < x) :
    badRowsEvent n ((rowBound r τ x)^2) ≤ᵐ[gaussianMatrix n]
      (fun A => A ∈ inverseBad n r τ ∪ ⋃ k : Fin n, lateStageEvent n r τ x k) := by
  have hnon : ∀ᵐ A : Mat n ∂gaussianMatrix n, A.det ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using gaussianMatrix_singular_null_proved n
  filter_upwards [hnon] with A hA
  rintro ⟨k,i,hki⟩
  by_cases hbad : A ∈ inverseBad n r τ
  · exact Or.inl hbad
  have hnorm : rowBound r τ x < rowNorm (Matrix.of (selectedRows A k.val)) i := by
    apply (sq_lt_sq₀ (rowBound_nonneg _ _ _) (rowNorm_nonneg _ _)).mp
    rw [rowNorm_sq]
    exact hki
  have hk : 5*r < k.val := by
    by_contra! hk
    have hrow := (rowNorm_le_rowL1 (selectedRows A k.val) i).trans
      (eliminationRows_rowL1_le A (firstPath A) (firstPath_admissible_proved A hA) k.val i)
    have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk
    exact (not_lt_of_ge (hrow.trans (hpow.trans (early_threshold_le r hτ hx.le)))) hnorm
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨k,?_⟩
  rw [lateStageEvent,dif_pos hk]
  have ht : k.val-4*r ≤ n := by omega
  refine ⟨?_,hA,?_⟩
  · exact le_of_not_gt (fun hs => hbad ⟨k.val-4*r,ht,hs⟩)
  · refine ⟨i,?_⟩
    have he : k.val-4*r+4*r=k.val := by omega
    rw [he]
    exact (stage_threshold_le r τ x).trans_lt hnorm

/-- Simultaneous row control pays at most n actual smoothing events. -/
theorem badRows_tail {n r : ℕ} (hr : 1 ≤ r) {τ x : ℝ} (hτ : 0 ≤ τ) (hx : 0 < x) :
    gaussianMatrix n (badRowsEvent n ((rowBound r τ x)^2)) ≤
      gaussianMatrix n (inverseBad n r τ)+
        (2*(n:ℝ≥0∞)^2+n)*ENNReal.ofReal (Real.exp (-x)) := by
  have hu : gaussianMatrix n (⋃ k : Fin n, lateStageEvent n r τ x k) ≤
      (2*(n:ℝ≥0∞)^2+n)*ENNReal.ofReal (Real.exp (-x)) := by
    calc
      _ ≤ ∑ k : Fin n, gaussianMatrix n (lateStageEvent n r τ x k) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Fin n, (2*(n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) :=
        Finset.sum_le_sum (fun k _ => lateStageEvent_tail hr hτ hx k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
  exact (measure_mono_ae (badRows_subset_ae hr hτ hx)).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hu))

/-- The complete growth transfer, retaining only the simultaneous spectral
inverse-tail probability that the separate B5 theorem supplies. -/
theorem growth_tail {n r : ℕ} (hr : 1 ≤ r) {τ x : ℝ} (hτ : 0 ≤ τ) (hx : 0 < x) :
    gaussianMatrix n (exceedanceEvent n (Real.sqrt (2*x*(rowBound r τ x)^2))) ≤
      gaussianMatrix n (inverseBad n r τ)+
        (2*(n:ℝ≥0∞)^2+n+2*(n:ℝ≥0∞)^3)*ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal (gaussianUnitIntervalMass^(n^2)) := by
  apply (normalized_tail_transfer n ((rowBound r τ x)^2) x (sq_nonneg _) hx).trans
  calc
    _ ≤ (gaussianMatrix n (inverseBad n r τ)+
        (2*(n:ℝ≥0∞)^2+n)*ENNReal.ofReal (Real.exp (-x)))+
        (2*(n:ℝ≥0∞)^3)*ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal (gaussianUnitIntervalMass^(n^2)) :=
      add_le_add (add_le_add (badRows_tail hr hτ hx) le_rfl) le_rfl
    _ = _ := by ring

#assert_trust kernel rowBound
#assert_trust kernel rowNorm_le_rowL1
#assert_trust kernel rowBound_nonneg
#assert_trust kernel early_threshold_le
#assert_trust kernel stage_threshold_le
#assert_trust kernel inverseBad
#assert_trust kernel lateStageEvent
#assert_trust kernel lateStageEvent_tail
#assert_trust kernel badRows_subset_ae
#assert_trust kernel badRows_tail
#assert_trust kernel growth_tail
#print axioms growth_tail
end NLA.IE06.GaussianAllRows
