import NLA.FR05.Overlap.OverlapCholesky
import NLA.FR05.Overlap.Spectrum

/-!
# Exact reference kernels and determinant bounds

The sections develop `ReferenceDeterminant`, `ReferenceKernelExact`, `ReferenceGlobalBound`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ReferenceDeterminant

open Complex Matrix

def referenceOverlapBlock (K : SourceOverlapMatrix) (v : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  fromBlocks 1 (((1 - v : ℝ) : ℂ) • K) (((1 - v : ℝ) : ℂ) • Kᴴ) 1

theorem referenceOverlapBlock_det (K : SourceOverlapMatrix) (v : ℝ) :
    (referenceOverlapBlock K v).det =
      (1 - (((1 - v : ℝ) : ℂ) • K) * (((1 - v : ℝ) : ℂ) • K)ᴴ).det := by
  rw [referenceOverlapBlock, det_fromBlocks_one₁₁, det_one_sub_mul_comm]
  simp [conjTranspose_smul]

theorem referenceOverlapBlock_scale {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {v : ℝ} (hv : v ≠ 0) :
    (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) +
      (((v⁻¹ - 1 : ℝ) : ℂ) • (canonicalOverlapColumns K)ᴴ) *
        canonicalOverlapColumns K =
      ((v⁻¹ : ℝ) : ℂ) • referenceOverlapBlock K v := by
  rw [smul_mul, canonicalOverlapColumns_gram hK]
  ext i j
  cases i <;> cases j <;>
    simp [referenceOverlapBlock, Matrix.one_apply, Matrix.fromBlocks, smul_eq_mul]
  all_goals try {split_ifs <;> simp_all}
  all_goals field_simp [Complex.ofReal_ne_zero.mpr hv]

theorem canonical_reference_determinant {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {v : ℝ} (hv : v ≠ 0) :
    (1 + (canonicalOverlapColumns K) *
      (((v⁻¹ - 1 : ℝ) : ℂ) • (canonicalOverlapColumns K)ᴴ)).det =
      ((v⁻¹ : ℝ) : ℂ)^4 *
        (1 - (((1 - v : ℝ) : ℂ) • K) * (((1 - v : ℝ) : ℂ) • K)ᴴ).det := by
  rw [det_one_add_mul_comm, referenceOverlapBlock_scale hK hv, det_smul,
    referenceOverlapBlock_det]
  simp

theorem canonical_reference_determinant_re {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {v : ℝ} (hv : v ≠ 0) :
    (1 + (canonicalOverlapColumns K) *
      (((v⁻¹ - 1 : ℝ) : ℂ) • (canonicalOverlapColumns K)ᴴ)).det.re =
      v⁻¹ ^ 4 * overlapDeterminant (((1 - v : ℝ) : ℂ) • K) := by
  rw [canonical_reference_determinant hK hv, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rfl

end ReferenceDeterminant

section ReferenceKernelExact

open MeasureTheory Complex Real Matrix WithLp
open scoped ComplexOrder

theorem gaussianQuadratic_smul {n : ℕ} (a : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Signal n) :
    gaussianQuadratic ((a : ℂ) • A) z = a * gaussianQuadratic A z := by
  simp [gaussianQuadratic, smul_mulVec, dotProduct_smul]

theorem gaussianQuadratic_gram {n : ℕ} {ι : Type*} [Fintype ι]
    (C : Matrix (Fin n) ι ℂ) (z : Signal n) :
    gaussianQuadratic (C * Cᴴ) z = ∑ j, Complex.normSq ((Cᴴ *ᵥ z) j) := by
  unfold gaussianQuadratic
  rw [← mulVec_mulVec, dotProduct_mulVec]
  have he : star z ᵥ* C = star (Cᴴ *ᵥ z) := by
    simpa using vecMul_conjTranspose Cᴴ (star z)
  rw [he]
  simp [dotProduct, Complex.conj_mul', Complex.re_sum, ← Complex.ofReal_pow, Complex.sq_norm]

theorem canonical_projection_energy (K : SourceOverlapMatrix) (x : Signal 4) :
    sourceRadiusSq (unpackSourceProjections (gaussianMatrixProjection (canonicalOverlapColumns K) x)).1 +
      sourceRadiusSq (unpackSourceProjections (gaussianMatrixProjection (canonicalOverlapColumns K) x)).2 =
      gaussianQuadratic (canonicalOverlapColumns K * (canonicalOverlapColumns K)ᴴ) (star x) := by
  rw [gaussianQuadratic_gram]
  simp [gaussianMatrixProjection, unpackSourceProjections, sourceRadiusSq,
    Fintype.sum_sum_type, Fin.sum_univ_two]

theorem reference_projection_product (M : ℕ) (K : SourceOverlapMatrix) (x : Signal 4) :
    sourceDensity .reference M
        (unpackSourceProjections (gaussianMatrixProjection (canonicalOverlapColumns K) x)).1 *
      sourceDensity .reference M
        (unpackSourceProjections (gaussianMatrixProjection (canonicalOverlapColumns K) x)).2 =
      (sourceVariance M)⁻¹ ^ 4 *
        Real.exp (-gaussianQuadratic
          (((sourceVariance M)⁻¹ - 1 : ℝ) •
            (canonicalOverlapColumns K * (canonicalOverlapColumns K)ᴴ)) (star x)) := by
  change sourceReferenceDensity M _ * sourceReferenceDensity M _ = _
  unfold sourceReferenceDensity
  rw [show ∀ a b c : ℝ, (a * b) * (a * c) = a^2 * (b * c) by intros; ring,
    ← Real.exp_add, ← mul_add, canonical_projection_energy]
  have he : (((sourceVariance M)⁻¹ - 1 : ℝ) •
      (canonicalOverlapColumns K * (canonicalOverlapColumns K)ᴴ)) =
      (((sourceVariance M)⁻¹ - 1 : ℝ) : ℂ) •
        (canonicalOverlapColumns K * (canonicalOverlapColumns K)ᴴ) := by
    ext i j
    simp [Algebra.smul_def]
  rw [he, gaussianQuadratic_smul]
  congr 1
  · ring
  · congr 1; ring

theorem sourceDensityCorrelation_reference_exact {M : ℕ} (hM : 2 ≤ M)
    {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation .reference .reference M K =
      (overlapDeterminant (((1 - sourceVariance M : ℝ) : ℂ) • K))⁻¹ := by
  have hv := sourceVariance_pos M
  have ha : 0 ≤ (sourceVariance M)⁻¹ - 1 :=
    sub_nonneg.mpr ((one_le_inv₀ hv).mpr (sourceVariance_le_one hM))
  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    ((sourceVariance M)⁻¹ - 1 : ℝ) •
      (canonicalOverlapColumns K * (canonicalOverlapColumns K)ᴴ)
  have hA : A.PosSemidef := (posSemidef_self_mul_conjTranspose _).smul ha
  rw [sourceDensityCorrelation_eq_integral_canonical hK, canonicalOverlapLaw_eq_projection,
    integral_map continuous_unpackSourceProjections.measurable.aemeasurable
      (by apply Measurable.aestronglyMeasurable; unfold sourceDensity sourceReferenceDensity sourceRadiusSq; fun_prop),
    integral_map (continuous_gaussianMatrixProjection _).measurable.aemeasurable
      (by apply Measurable.aestronglyMeasurable; unfold sourceDensity sourceReferenceDensity sourceRadiusSq; fun_prop)]
  simp_rw [reference_projection_product]
  rw [integral_const_mul]
  have hstar :
      (∫ x, Real.exp (-gaussianQuadratic A (star x)) ∂standardComplexGaussianTail 4) =
        ∫ x, Real.exp (-gaussianQuadratic A x) ∂standardComplexGaussianTail 4 := by
    rw [← integral_map (φ := star) (f := fun x ↦ Real.exp (-gaussianQuadratic A x))
      (by fun_prop) (by fun_prop), standardComplexGaussianTail_map_star]
  rw [hstar, integral_gaussianQuadratic_exp_det hA]
  have he : A = canonicalOverlapColumns K *
      ((((sourceVariance M)⁻¹ - 1 : ℝ) : ℂ) • (canonicalOverlapColumns K)ᴴ) := by
    simp only [Matrix.mul_smul, A]
    ext i j
    simp [Algebra.smul_def]
  rw [he, canonical_reference_determinant_re hK hv.ne', _root_.mul_inv_rev]
  field_simp [hv.ne']

end ReferenceKernelExact

section ReferenceGlobalBound

open Real Complex Matrix

theorem reference_scalar_log_bound {q x : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 4 - 1 / 2000) (hx : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - q * x) ≤ -x / 2000 - Real.log (1 - x) / 4 := by
  have hq' : q ≤ 1 := by linarith
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 - x ∈ Set.Ioi 0 by exact sub_pos.mpr hx1)
    (show 0 ≤ 1 - q by linarith) hq (show 1 - q + q = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hc
  rw [show (1 - q) * 1 + q * (1 - x) = 1 - q * x by ring] at hc
  have hl := Real.log_le_sub_one_of_pos (sub_pos.mpr hx1)
  have hn := mul_nonneg (show 0 ≤ 1 / 4 - q by linarith)
    (show 0 ≤ -Real.log (1 - x) - x by linarith)
  have hgap := mul_nonneg (show 0 ≤ 1 / 4 - 1 / 2000 - q by linarith) hx
  nlinarith

theorem reference_scalar_bound {q x : ℝ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1 / 4 - 1 / 2000) (hx : 0 ≤ x) (hx1 : x < 1) :
    (1 - q * x)⁻¹ ≤ Real.exp (-x / 2000) * (1 - x)^(-(1 / 4 : ℝ)) := by
  have hp : 0 < 1 - q * x := by nlinarith [mul_nonneg hq hx, mul_nonneg hq (sub_pos.mpr hx1).le]
  rw [Real.rpow_def_of_pos (sub_pos.mpr hx1), ← Real.exp_add,
    ← Real.exp_log (inv_pos.mpr hp), Real.log_inv]
  apply Real.exp_le_exp.mpr
  convert reference_scalar_log_bound hq hq1 hx hx1 using 1
  ring

theorem sourceReference_bias_sq_bound {M : ℕ} (hM : 2 ≤ M) :
    (1 - sourceVariance M)^2 ≤ 1 / 4 - 1 / 2000 := by
  have hlo := sourceVariance_lower M
  have hhi := sourceVariance_le_one hM
  norm_num [sourceEta] at hlo
  have h1 : 0 ≤ 1 - sourceVariance M := by linarith
  have h2 : 1 - sourceVariance M ≤ 99 / 200 := by linarith
  nlinarith [mul_nonneg h1 (show 0 ≤ 99 / 200 - (1 - sourceVariance M) by linarith)]

theorem overlapSquaredSingularValues_lt_one {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (i : Fin 2) :
    overlapSquaredSingularValues K i < 1 := by
  have hn := overlapOperatorNorm_nonneg K
  have h := overlapSquaredSingularValues_le K i
  nlinarith

theorem sourceDensityCorrelation_reference_global_bound {M : ℕ} (hM : 2 ≤ M)
    {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    sourceDensityCorrelation .reference .reference M K ≤
      Real.exp (-overlapOperatorNorm K ^ 2 / 2000) *
        overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
  let l := overlapSquaredSingularValues K
  have hl (i : Fin 2) : 0 ≤ l i := overlapSquaredSingularValues_nonneg K i
  have hl1 (i : Fin 2) : l i < 1 := overlapSquaredSingularValues_lt_one hK i
  rw [sourceDensityCorrelation_reference_exact hM hK,
    overlapDeterminant_smul_singularValues, ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ i : Fin 2, Real.exp (-l i / 2000) * (1 - l i)^(-(1 / 4 : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i hi
        apply inv_nonneg.mpr
        have hq := sourceReference_bias_sq_bound hM
        have hq0 := sq_nonneg (1 - sourceVariance M)
        have hx := hl i
        have hx1 := hl1 i
        change 0 ≤ 1 - (1 - sourceVariance M)^2 * l i
        nlinarith [mul_nonneg hq0 (show 0 ≤ 1 - l i by linarith)]
      · intro i hi
        exact reference_scalar_bound (sq_nonneg _) (sourceReference_bias_sq_bound hM)
          (hl i) (hl1 i)
    _ = Real.exp (-overlapFrobeniusSq K / 2000) *
        overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
      rw [Fin.prod_univ_two, overlapDeterminant_singularValues, Fin.prod_univ_two,
        Real.mul_rpow (sub_pos.mpr (hl1 0)).le (sub_pos.mpr (hl1 1)).le]
      have hs := overlapSquaredSingularValues_sum K
      rw [Fin.sum_univ_two] at hs
      dsimp [l]
      rw [show -overlapFrobeniusSq K / 2000 =
        -overlapSquaredSingularValues K 0 / 2000 +
          -overlapSquaredSingularValues K 1 / 2000 by linarith, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (overlapDeterminant_pos hK).le _)
      apply Real.exp_le_exp.mpr
      have h := overlapOperatorNorm_sq_le_frobenius K
      linarith

end ReferenceGlobalBound

end NLA.FR05
