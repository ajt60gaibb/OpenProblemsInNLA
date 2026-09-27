import NLA.FR05.Gaussian.GaussianConditionalDensity
import NLA.FR05.Likelihood.KernelLocalEstimates

/-!
# Overlap Cholesky coordinates and the Gaussian coupling

The sections develop `OverlapCholesky`, `CanonicalOverlapLaw`, `GaussianOverlapBridge`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section OverlapCholesky

open MeasureTheory Complex Real Matrix
open scoped ENNReal BigOperators

def overlapCholeskyFirst (K : SourceOverlapMatrix) : ℝ := 1 - overlapColumnEnergy K 0

def overlapCholeskySecond (K : SourceOverlapMatrix) : ℝ :=
  overlapDeterminant K / overlapCholeskyFirst K

def overlapCholeskySlope (K : SourceOverlapMatrix) : ℂ :=
  -star (overlapColumnCross K) / (overlapCholeskyFirst K : ℂ)

def overlapCholesky (K : SourceOverlapMatrix) : SourceOverlapMatrix :=
  !![(Real.sqrt (overlapCholeskyFirst K) : ℂ), 0;
    overlapCholeskySlope K * (Real.sqrt (overlapCholeskyFirst K) : ℂ),
    (Real.sqrt (overlapCholeskySecond K) : ℂ)]

theorem overlapCholeskyFirst_pos {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    0 < overlapCholeskyFirst K := by
  have hρ := overlapOperatorNorm_nonneg K
  have h := overlapColumnEnergy_le K 0
  unfold overlapCholeskyFirst
  nlinarith

theorem overlapCholeskySecond_pos {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    0 < overlapCholeskySecond K :=
  div_pos (overlapDeterminant_pos hK) (overlapCholeskyFirst_pos hK)

theorem overlapResidual_complete_square {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (u : Signal 2) :
    (coneInner u ((overlapResidualMatrix K)⁻¹ *ᵥ u)).re =
      Complex.normSq (u 0) / overlapCholeskyFirst K +
        Complex.normSq (u 1 - overlapCholeskySlope K * u 0) / overlapCholeskySecond K := by
  have ha := (overlapCholeskyFirst_pos hK).ne'
  have hΔ := (overlapDeterminant_pos hK).ne'
  unfold overlapCholeskySlope overlapCholeskySecond
  have hc := complex_complete_square (a := overlapCholeskyFirst K)
    (b := 1 - overlapColumnEnergy K 1) (d := overlapDeterminant K)
    ha hΔ (-overlapColumnCross K) (u 0) (u 1)
    (by rw [overlapDeterminant_columns]; simp [overlapCholeskyFirst])
  simp only [star_neg, neg_div] at hc ⊢
  rw [hc, overlapResidualMatrix_inverse, ← Complex.ofReal_inv]
  simp only [coneInner, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.add_re, Complex.add_im, Complex.normSq_apply,
    Complex.neg_re, Complex.neg_im]
  unfold overlapCholeskyFirst
  field_simp
  ring

theorem overlapGaussianRatio_conditional_density {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (z w : Signal 2) :
    scalarComplexDensity (w 0) * scalarComplexDensity (w 1) * overlapGaussianRatio K z w =
      triangularGaussianDensity (overlapCholeskyFirst K) (overlapCholeskySecond K)
        (overlapCholeskySlope K) (Kᴴ *ᵥ z) w := by
  have ha := (overlapCholeskyFirst_pos hK).ne'
  have hΔ := (overlapDeterminant_pos hK).ne'
  have he : (w 1 - (Kᴴ *ᵥ z) 1) - overlapCholeskySlope K * (w 0 - (Kᴴ *ᵥ z) 0) =
      w 1 - ((Kᴴ *ᵥ z) 1 + overlapCholeskySlope K * (w 0 - (Kᴴ *ᵥ z) 0)) := by ring
  have hquad := overlapResidual_complete_square hK (w - Kᴴ *ᵥ z)
  simp only [Pi.sub_apply, he] at hquad
  unfold scalarComplexDensity overlapGaussianRatio triangularGaussianDensity scalarGaussianDensity
  rw [hquad]
  unfold sourceRadiusSq
  calc
    _ = (Real.pi⁻¹ * Real.pi⁻¹ * (overlapDeterminant K)⁻¹) *
        Real.exp (-Complex.normSq (w 0 - (Kᴴ *ᵥ z) 0) / overlapCholeskyFirst K -
          Complex.normSq (w 1 - ((Kᴴ *ᵥ z) 1 +
            overlapCholeskySlope K * (w 0 - (Kᴴ *ᵥ z) 0))) / overlapCholeskySecond K) := by
      simp only [Real.exp_sub, Real.exp_add, neg_div, Real.exp_neg]
      field_simp
    _ = _ := by
      simp only [sub_eq_add_neg, Real.exp_add, neg_div]
      unfold overlapCholeskySecond
      field_simp [ha, hΔ, Real.pi_ne_zero]

theorem overlapCholesky_mul_conjTranspose {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) :
    overlapCholesky K * (overlapCholesky K)ᴴ = overlapResidualMatrix K := by
  have ha := (overlapCholeskyFirst_pos hK).ne'
  have hs1 := Real.sq_sqrt (overlapCholeskyFirst_pos hK).le
  have hs2 := Real.sq_sqrt (overlapCholeskySecond_pos hK).le
  rw [overlapResidualMatrix_eq]
  have ha' : 1 - overlapColumnEnergy K 0 ≠ 0 := ha
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals
    simp [overlapCholesky, overlapCholeskySlope, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im] <;>
    field_simp <;>
    simp only [hs1, hs2] <;>
    simp only [overlapCholeskySecond, overlapCholeskyFirst,
      overlapDeterminant_columns, Complex.normSq_apply] <;>
    field_simp [ha'] <;>
    ring

end OverlapCholesky

section CanonicalOverlapLaw

set_option maxHeartbeats 800000
open MeasureTheory Complex Real Matrix
open scoped ENNReal


theorem triangularGaussian_eq_overlap {K : SourceOverlapMatrix} (z ξ : Signal 2) :
    triangularGaussian (overlapCholeskyFirst K) (overlapCholeskySecond K)
      (overlapCholeskySlope K) (Kᴴ *ᵥ z) ξ =
      Kᴴ *ᵥ z + overlapCholesky K *ᵥ ξ := by
  ext i
  fin_cases i <;>
    simp [triangularGaussian, overlapCholesky, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Complex.real_smul] <;> ring

theorem lintegral_overlapGaussianRatio {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (z : Signal 2)
    (f : Signal 2 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, ENNReal.ofReal (overlapGaussianRatio K z w) * f w ∂standardComplexGaussianTail 2) =
      ∫⁻ ξ, f (Kᴴ *ᵥ z + overlapCholesky K *ᵥ ξ) ∂standardComplexGaussianTail 2 := by
  rw [lintegral_standardComplexGaussianTail_two _
    (by unfold overlapGaussianRatio coneInner sourceRadiusSq; fun_prop)]
  have he (x y : ℂ) :
      ENNReal.ofReal (scalarComplexDensity x) * ENNReal.ofReal (scalarComplexDensity y) *
        (ENNReal.ofReal (overlapGaussianRatio K z ![x, y]) * f ![x, y]) =
      ENNReal.ofReal (triangularGaussianDensity (overlapCholeskyFirst K)
        (overlapCholeskySecond K) (overlapCholeskySlope K) (Kᴴ *ᵥ z) ![x, y]) * f ![x, y] := by
    have h := overlapGaussianRatio_conditional_density hK z ![x, y]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
    rw [← mul_assoc, ← ENNReal.ofReal_mul (scalarComplexDensity_nonneg x),
      ← ENNReal.ofReal_mul (mul_nonneg (scalarComplexDensity_nonneg x) (scalarComplexDensity_nonneg y)), h]
  simp_rw [he]
  rw [lintegral_triangularGaussian (overlapCholeskyFirst_pos hK) (overlapCholeskySecond_pos hK)]
  simp_rw [triangularGaussian_eq_overlap]
  exact hf

def canonicalOverlapMap (K : SourceOverlapMatrix) (p : Signal 2 × Signal 2) : Signal 2 × Signal 2 :=
  (p.1, Kᴴ *ᵥ p.1 + overlapCholesky K *ᵥ p.2)

@[fun_prop]
theorem continuous_canonicalOverlapMap (K : SourceOverlapMatrix) : Continuous (canonicalOverlapMap K) := by
  unfold canonicalOverlapMap
  fun_prop

def canonicalOverlapLaw (K : SourceOverlapMatrix) : Measure (Signal 2 × Signal 2) :=
  ((standardComplexGaussianTail 2).prod (standardComplexGaussianTail 2)).map (canonicalOverlapMap K)

instance (K : SourceOverlapMatrix) : IsProbabilityMeasure (canonicalOverlapLaw K) :=
  Measure.isProbabilityMeasure_map (continuous_canonicalOverlapMap K).measurable.aemeasurable

theorem canonicalOverlapLaw_eq_withDensity {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) :
    canonicalOverlapLaw K =
      ((standardComplexGaussianTail 2).prod (standardComplexGaussianTail 2)).withDensity
        (fun p ↦ ENNReal.ofReal (overlapGaussianRatio K p.1 p.2)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [canonicalOverlapLaw, lintegral_map hf (continuous_canonicalOverlapMap K).measurable,
    lintegral_withDensity_eq_lintegral_mul _
      (continuous_overlapGaussianRatio K).measurable.ennreal_ofReal hf,
    lintegral_prod _ (by apply Measurable.aemeasurable; fun_prop),
    lintegral_prod _ (by apply Measurable.aemeasurable; fun_prop)]
  apply lintegral_congr
  intro z
  exact (lintegral_overlapGaussianRatio hK z (fun w ↦ f (z, w)) (by fun_prop)).symm

theorem sourceDensityCorrelation_eq_integral_canonical {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (a b : SourceDensityKind) (M : ℕ) :
    sourceDensityCorrelation a b M K =
      ∫ p, sourceDensity a M p.1 * sourceDensity b M p.2 ∂canonicalOverlapLaw K := by
  have hm : Measurable (fun p : Signal 2 × Signal 2 ↦
      ENNReal.ofReal (sourceDensity a M p.1) * ENNReal.ofReal (sourceDensity b M p.2)) :=
    (((measurable_sourceDensity a M).comp measurable_fst).ennreal_ofReal.mul
      ((measurable_sourceDensity b M).comp measurable_snd).ennreal_ofReal)
  rw [sourceDensityCorrelation, canonicalOverlapLaw_eq_withDensity hK,
    sourceDensityLaw, sourceDensityLaw,
    prod_withDensity (measurable_sourceDensity a M).ennreal_ofReal
      (measurable_sourceDensity b M).ennreal_ofReal,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul
      (continuous_overlapGaussianRatio K).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with p
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sourceDensity_nonneg a M _),
    ENNReal.toReal_ofReal (sourceDensity_nonneg b M _),
    ENNReal.toReal_ofReal (overlapGaussianRatio_nonneg hK _ _), smul_eq_mul]
  ring

end CanonicalOverlapLaw

section GaussianOverlapBridge

open MeasureTheory Complex Real Matrix WithLp


/-- The two independent Gaussian pairs in the canonical overlap construction. -/
def splitGaussianFour : Signal 4 → Signal 2 × Signal 2 := splitGaussianSum 2 2

@[fun_prop]
theorem continuous_splitGaussianFour : Continuous splitGaussianFour := by
  exact continuous_splitGaussianSum 2 2

theorem standardComplexGaussianTail_map_split :
    (standardComplexGaussianTail 4).map splitGaussianFour =
      (standardComplexGaussianTail 2).prod (standardComplexGaussianTail 2) := by
  exact standardComplexGaussianTail_map_splitSum 2 2

def canonicalOverlapColumns (K : SourceOverlapMatrix) : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) ℂ :=
  (Matrix.fromBlocks (1 : SourceOverlapMatrix) K 0 (overlapCholesky K)ᴴ).submatrix
    (finSumFinEquiv (m := 2) (n := 2)).symm id

theorem canonicalOverlapColumns_gram {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) :
    (canonicalOverlapColumns K)ᴴ * canonicalOverlapColumns K =
      Matrix.fromBlocks 1 K Kᴴ 1 := by
  rw [canonicalOverlapColumns, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
    overlapCholesky_mul_conjTranspose hK, overlapResidualMatrix, add_sub_cancel]

theorem canonicalOverlapProjection (K : SourceOverlapMatrix) (x : Signal 4) :
    unpackSourceProjections (gaussianMatrixProjection (canonicalOverlapColumns K) x) =
      canonicalOverlapMap K (splitGaussianFour (star x)) := by
  unfold gaussianMatrixProjection canonicalOverlapColumns
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mulVec_equiv]
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_one,
    Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose,
    Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero,
    Function.comp_id]
  rfl

theorem canonicalOverlapLaw_eq_projection (K : SourceOverlapMatrix) :
    canonicalOverlapLaw K =
      ((standardComplexGaussianTail 4).map
        (gaussianMatrixProjection (canonicalOverlapColumns K))).map unpackSourceProjections := by
  rw [Measure.map_map continuous_unpackSourceProjections.measurable
    (continuous_gaussianMatrixProjection _).measurable]
  have he : unpackSourceProjections ∘ gaussianMatrixProjection (canonicalOverlapColumns K) =
      canonicalOverlapMap K ∘ splitGaussianFour ∘ star := by
    funext x
    exact canonicalOverlapProjection K x
  rw [he, ← Measure.map_map (continuous_canonicalOverlapMap K).measurable
      (continuous_splitGaussianFour.measurable.comp (by fun_prop)),
    ← Measure.map_map continuous_splitGaussianFour.measurable (by fun_prop),
    standardComplexGaussianTail_map_star, standardComplexGaussianTail_map_split]
  rfl

theorem sourceJointProjectionLaw_eq_canonical {M : ℕ} (hM : 2 ≤ M)
    (U V : SourceUnitary M) (hK : overlapOperatorNorm (sourceOverlap hM U V) < 1) :
    sourceJointProjectionLaw hM U V = canonicalOverlapLaw (sourceOverlap hM U V) := by
  rw [sourceJointProjectionLaw_eq_map, canonicalOverlapLaw_eq_projection]
  congr 1
  apply gaussianMatrixProjection_law_eq_of_gram
  rw [sourcePairColumns_gram, canonicalOverlapColumns_gram hK]

theorem sourcePairKernel_eq_densityCorrelation {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (U V : SourceUnitary M)
    (hK : overlapOperatorNorm (sourceOverlap hM U V) < 1) :
    sourcePairKernel hM a b U V =
      sourceDensityCorrelation a b M (sourceOverlap hM U V) := by
  rw [sourcePairKernel_eq_integral_jointLaw, sourceJointProjectionLaw_eq_canonical hM U V hK,
    sourceDensityCorrelation_eq_integral_canonical hK]

theorem sourcePairKernel_local_expansion {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (U V : SourceUnitary M)
    (hK : overlapOperatorNorm (sourceOverlap hM U V) ≤ 1 / 128) :
    |sourcePairKernel hM a b U V -
        (1 + (1 - sourceVariance M)^2 * overlapFrobeniusSq (sourceOverlap hM U V))| ≤
      (11000 * kernelMomentConstant 4) * overlapFrobeniusSq (sourceOverlap hM U V)^2 := by
  rw [sourcePairKernel_eq_densityCorrelation hM a b U V (by linarith)]
  exact sourceDensityCorrelation_local_expansion hM a b hK

end GaussianOverlapBridge

end NLA.FR05
