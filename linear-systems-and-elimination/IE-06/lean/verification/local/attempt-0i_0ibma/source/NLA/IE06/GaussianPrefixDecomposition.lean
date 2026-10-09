/- Fixed-T inverse truncation on the actual Gaussian pivot-order fiber.
The exact stage contract and this interface were approved before implementation.
-/
import NLA.IE06.GaussianCoordinates
import NLA.IE06.GaussianTruncatedRows
import NLA.IE06.SelectedBlockTruncation
import NLA.IE06.TruncatedInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ENNReal
namespace NLA.IE06.GaussianPrefixDecomposition
open GaussianPivotConditioning GaussianCoordinates SelectedBlockElimination
open SelectedBlockTruncation EliminationSmoothing TruncatedInverse

/-- Literal product law of the remaining original rows on a fixed T fiber. -/
def fiberLaw {n t : ℕ} (π : Fin t ↪ Fin n) (T : Mat t) :
    Measure (RemainingRows π → Fin t → ℝ) :=
  Measure.pi (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T))

/-- Restore the prefix, using zero for every unexposed future column. -/
def prefixInput {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (Z : RemainingRows π → Fin t → ℝ) : Mat n := restore ht π ((T,Z),0)

theorem restricted_strict_ae {t : ℕ} (T : Mat t) :
    ∀ᵐ z ∂GaussianRestriction.restrictedGaussian (truncationBody T), z ∈ strictTruncationBody T := by
  rw [ae_iff]
  change GaussianRestriction.restrictedGaussian (truncationBody T) (strictTruncationBody T)ᶜ = 0
  rw [GaussianRestriction.restrictedGaussian,Measure.smul_apply,
    Measure.restrict_apply (strictTruncationBody_open T).measurableSet.compl]
  have he : (strictTruncationBody T)ᶜ ∩ truncationBody T =
      truncationBody T \ strictTruncationBody T := by ext z; simp; tauto
  rw [he,truncationBody_boundary_null]
  simp

theorem product_strict_ae {n t : ℕ} (π : Fin t ↪ Fin n) (T : Mat t) :
    ∀ᵐ Z ∂fiberLaw π T, ∀ i : RemainingRows π, Z i ∈ strictTruncationBody T := by
  classical
  let _ := GaussianRestriction.restrictedGaussian_probability
    (ne_of_gt (truncationBody_mass_pos T))
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : RemainingRows π =>
    GaussianRestriction.restrictedGaussian (truncationBody T)) i).quasiMeasurePreserving.ae
      (restricted_strict_ae T)

/-- The actual canonical pivot order in this fixed fiber, with no later-pivot premise. -/
theorem prefix_order_ae {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (hg : Good T) : ∀ᵐ Z ∂fiberLaw π T, pivotOrder ht (prefixInput ht π T Z) = π := by
  filter_upwards [product_strict_ae π T] with Z hZ
  apply strict_fiber_implies_order ht π
  · simpa only [prefixInput,selectedBlock_restore] using hg
  · simpa only [prefixInput,selectedBlock_restore,remainingBlock_restore] using hZ

theorem prefix_data_ae {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (hg : Good T) : ∀ᵐ Z ∂fiberLaw π T,
      pivotOrder ht (prefixInput ht π T Z) = π ∧
      selectedBlock ht (pivotOrder ht (prefixInput ht π T Z)) (prefixInput ht π T Z) = T ∧
      PrefixNonzero ht (prefixInput ht π T Z) := by
  filter_upwards [prefix_order_ae ht π T hg] with Z hZ
  have hT : selectedBlock ht (pivotOrder ht (prefixInput ht π T Z)) (prefixInput ht π T Z) = T := by
    rw [hZ]
    exact selectedBlock_restore ht π ((T,Z),0)
  exact ⟨hZ,hT,prefixNonzero_of_good ht _ (by rw [hT]; exact hg)⟩

/-- The fixed-coordinate reconstruction is measurable in the remaining rows. -/
theorem prefixInput_measurable {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t) :
    Measurable (prefixInput ht π T) :=
  (restore_measurable ht π).comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)

/-- The actual canonical retained operator with any fixed R is measurable. -/
theorem retainedRows_measurable {n t : ℕ} (ht : t ≤ n) (R : Matrix (Fin t) (Fin t) ℝ) :
    Measurable (fun A : Mat n => retainedRows ht A R) := by
  classical
  let F : Mat n × PivotPath n → Mat n := fun z i j => if t ≤ i.val then
    (if j = rowLabels z.2 t i then 1 else 0) -
      ∑ a : Fin t, (∑ b : Fin t, z.1 (rowLabels z.2 t i) (Fin.castLE ht b) * R b a) *
        (if j = rowLabels z.2 t (Fin.castLE ht a) then 1 else 0) else 0
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro p
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    dsimp only [F]
    by_cases hi : t ≤ i.val
    · simp only [if_pos hi]
      have hm (a : Fin t) : Measurable (fun A : Mat n =>
          ∑ b : Fin t, A (rowLabels p t i) (Fin.castLE ht b) * R b a) := by fun_prop
      have hsum := Finset.measurable_sum Finset.univ (fun a _ =>
        (hm a).mul_const (if j = rowLabels p t (Fin.castLE ht a) then (1:ℝ) else 0))
      exact (show Measurable (fun _ : Mat n =>
        if j = rowLabels p t i then (1:ℝ) else 0) from measurable_const).sub hsum
    · simp only [if_neg hi]
      exact measurable_const
  have hm := hF.comp (measurable_id.prodMk (PivotFiltration.measurable_firstPath n))
  convert hm using 1
  funext A i j
  rw [retainedRows_apply]
  rfl

theorem retained_rowNorm_measurable {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (R : Matrix (Fin t) (Fin t) ℝ) (i : Fin n) :
    Measurable (fun Z => rowNorm (retainedRows ht (prefixInput ht π T Z) R) i) := by
  have hm := (retainedRows_measurable ht R).comp (prefixInput_measurable ht π T)
  have hs : Measurable (fun Z => ∑ j : Fin n, (retainedRows ht (prefixInput ht π T Z) R i j)^2) := by
    apply Finset.measurable_sum
    intro j _
    exact ((hm.eval).eval).pow_const 2
  have he (Z : RemainingRows π → Fin t → ℝ) :
      rowNorm (retainedRows ht (prefixInput ht π T Z) R) i =
        Real.sqrt (∑ j : Fin n, (retainedRows ht (prefixInput ht π T Z) R i j)^2) := by
    rw [← EliminationSmoothing.rowNorm_sq,Real.sqrt_sq (rowNorm_nonneg _ _)]
  simpa only [← he] using hs.sqrt

theorem measurableSet_bad_retainedRows {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (R : Matrix (Fin t) (Fin t) ℝ) (cap : ℝ) :
    MeasurableSet {Z | ∃ i : Fin n, cap < rowNorm (retainedRows ht (prefixInput ht π T Z) R) i} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const
    (retained_rowNorm_measurable ht π T R i))

/-- A fixed retained matrix's row bound, before any T-dependent spectral choice. -/
theorem retained_rows_tail {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (hg : Good T) (R : Matrix (Fin t) (Fin t) ℝ) {x τ : ℝ}
    (hx : 0 ≤ x) (hτ : KyFan.frobeniusNorm R^2 ≤ τ) :
    (fiberLaw π T) {Z | ∃ i : Fin n,
      Real.sqrt (1+(2+4*x)*τ) < rowNorm (retainedRows ht (prefixInput ht π T Z) R) i} ≤
      (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-x)) := by
  classical
  have hτ0 : 0 ≤ τ := (sq_nonneg (KyFan.frobeniusNorm R)).trans hτ
  have harg : 0 ≤ 1+(2+4*x)*τ := by positivity
  have hsub : {Z | ∃ i : Fin n,
      Real.sqrt (1+(2+4*x)*τ) < rowNorm (retainedRows ht (prefixInput ht π T Z) R) i} ≤ᵐ[fiberLaw π T]
      {Z | ∃ a : RemainingRows π, (2+4*x)*τ < GaussianTruncatedRows.rowEnergy R (Z a)} := by
    filter_upwards [prefix_order_ae ht π T hg] with Z horder
    rintro ⟨i,hi⟩
    have hactive : t ≤ i.val := by
      by_contra! hi0
      have hz := retainedRows_inactive ht (prefixInput ht π T Z) R i hi0
      have hnorm : rowNorm (retainedRows ht (prefixInput ht π T Z) R) i = 0 := by
        simp only [rowNorm,hz]
        simp
      rw [hnorm] at hi
      exact (not_lt_of_ge (Real.sqrt_nonneg _)) hi
    have hlabel : rowLabels (firstPath (prefixInput ht π T Z)) t i ∉ Set.range π := by
      have h := active_label_not_selected ht (prefixInput ht π T Z) i hactive
      simpa only [horder] using h
    let a : RemainingRows π := ⟨rowLabels (firstPath (prefixInput ht π T Z)) t i,hlabel⟩
    have hz : prefixRows ht (prefixInput ht π T Z)
        (rowLabels (firstPath (prefixInput ht π T Z)) t i) = Z a := by
      exact congrFun (remainingBlock_restore ht π ((T,Z),0)) a
    have he := retainedRows_rowNorm_sq ht (prefixInput ht π T Z) R i hactive
    rw [hz,EuclideanSpace.real_norm_sq_eq] at he
    have hs : (Real.sqrt (1+(2+4*x)*τ))^2 <
        rowNorm (retainedRows ht (prefixInput ht π T Z) R) i ^ 2 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg _) (rowNorm_nonneg _ _)).mpr hi
    rw [Real.sq_sqrt harg,he] at hs
    exact ⟨a,by change (2+4*x)*τ < ∑ j, ((Z a) ᵥ* R) j ^ 2; linarith⟩
  calc
    _ ≤ (fiberLaw π T) {Z | ∃ a : RemainingRows π,
        (2+4*x)*τ < GaussianTruncatedRows.rowEnergy R (Z a)} := measure_mono_ae hsub
    _ ≤ (Fintype.card (RemainingRows π) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-x)) :=
      GaussianTruncatedRows.rows_tail T R hx hτ
    _ ≤ _ := by
      gcongr
      exact_mod_cast (remainingRows_card π).trans_le (Nat.sub_le n t)

/-- Fixed-T spectral choice and its actual prefix-fiber identities and probability bound. -/
theorem exists_prefix_decomposition {n t r : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (T : Mat t)
    (hg : Good T) (_hr1 : 1 ≤ r) (hr : r < t) {x τ : ℝ} (hx : 0 < x)
    (hτ : sigmaInvSum T r ≤ τ) :
    ∃ R : Matrix (Fin t) (Fin t) ℝ, ∃ H V : Matrix (Fin t) (Fin r) ℝ,
      Vᴴ * V = 1 ∧ T⁻¹ = R + H * Vᴴ ∧ KyFan.frobeniusNorm R^2 = sigmaInvSum T r ∧
      (coordinateEmbedding π * V)ᴴ * (coordinateEmbedding π * V) = 1 ∧
      (∀ᵐ Z ∂fiberLaw π T,
        pivotOrder ht (prefixInput ht π T Z) = π ∧ PrefixNonzero ht (prefixInput ht π T Z) ∧
        Matrix.of (eliminationRows (prefixInput ht π T Z) (firstPath (prefixInput ht π T Z)) t) =
          retainedRows ht (prefixInput ht π T Z) R +
          discardedRows ht (prefixInput ht π T Z) H * (coordinateEmbedding π * V)ᴴ) ∧
      (fiberLaw π T) {Z | ∃ i : Fin n,
        Real.sqrt (1+(2+4*x)*τ) < rowNorm (retainedRows ht (prefixInput ht π T Z) R) i} ≤
          (n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-x)) := by
  obtain ⟨R,H,V,hV,_,hT,hF,_⟩ := exists_inverse_decomposition T (det_ne_zero_of_pivots T hg.1) hr
  refine ⟨R,H,V,hV,hT,hF,discardedFrame_orthonormal π V hV,?_,?_⟩
  · filter_upwards [prefix_data_ae ht π T hg] with Z hZ
    refine ⟨hZ.1,hZ.2.2,?_⟩
    have h := eliminationRows_decomposition ht (prefixInput ht π T Z) hZ.2.2 R H V
      (by rw [hZ.2.1]; exact hT)
    simpa only [discardedFrame,hZ.1] using h
  · exact retained_rows_tail ht π T hg R hx.le (hF.trans_le hτ)

#assert_trust kernel fiberLaw
#print axioms fiberLaw
#assert_trust kernel prefixInput
#print axioms prefixInput
#assert_trust kernel restricted_strict_ae
#print axioms restricted_strict_ae
#assert_trust kernel product_strict_ae
#print axioms product_strict_ae
#assert_trust kernel prefix_order_ae
#print axioms prefix_order_ae
#assert_trust kernel prefix_data_ae
#print axioms prefix_data_ae
#assert_trust kernel prefixInput_measurable
#print axioms prefixInput_measurable
#assert_trust kernel retainedRows_measurable
#print axioms retainedRows_measurable
#assert_trust kernel retained_rowNorm_measurable
#print axioms retained_rowNorm_measurable
#assert_trust kernel measurableSet_bad_retainedRows
#print axioms measurableSet_bad_retainedRows
#assert_trust kernel retained_rows_tail
#print axioms retained_rows_tail
#assert_trust kernel exists_prefix_decomposition
#print axioms exists_prefix_decomposition
end NLA.IE06.GaussianPrefixDecomposition
