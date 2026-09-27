import NLA.FR05.Cone.ConeGeometry

/-!
# Cone image coordinates and integral estimates

The sections develop `ConeImageEstimates`, `ConeCoordinates`, `ConeBaseBound`,
`ConeExponentialBound`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ConeImageEstimates

open MeasureTheory Complex Real Matrix
open scoped BigOperators ENNReal

def coneImage (K : SourceOverlapMatrix) (s : ℝ) (θ : ConePhase) : Fin 2 → ℂ :=
  K *ᵥ coneNormal s (conePhasePoint θ)

@[fun_prop]
theorem continuous_coneImage (K : SourceOverlapMatrix) (s : ℝ) :
    Continuous (coneImage K s) := by
  unfold coneImage
  fun_prop

theorem coneImage_energy_bound {s : ℝ} (hs : |s| ≤ 1) (K : SourceOverlapMatrix)
    (θ : ConePhase) : sourceRadiusSq (coneImage K s θ) ≤ overlapOperatorNorm K ^ 2 := by
  simpa [coneImage, coneNormal_energy hs (norm_conePhasePoint θ)] using
    sourceRadiusSq_mulVec_le K (coneNormal s (conePhasePoint θ))

theorem coneImage_energy_lt_one {s : ℝ} (hs : |s| ≤ 1) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) (θ : ConePhase) :
    sourceRadiusSq (coneImage K s θ) < 1 := by
  have h := coneImage_energy_bound hs K θ
  have hρ := overlapOperatorNorm_nonneg K
  nlinarith

theorem continuous_conePhaseJ_image {t s : ℝ} (ht : |t| < 1) (hs : |s| ≤ 1)
    {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    Continuous (fun θ ↦ conePhaseJ t (coneImage K s θ)) := by
  apply Continuous.inv₀
  · unfold conePhaseR conePhaseU conePhaseB
    fun_prop
  · intro θ
    exact (conePhaseR_pos ht (coneImage_energy_lt_one hs hK θ)).ne'

def coneImageA (K : SourceOverlapMatrix) (s : ℝ) : ℝ :=
  (1 - s) / 2 * (1 - overlapColumnEnergy K 0) +
    (1 + s) / 2 * (1 - overlapColumnEnergy K 1)

def coneImageB (K : SourceOverlapMatrix) (s : ℝ) : ℂ :=
  -2 * ((Real.sqrt ((1 + s) / 2) * Real.sqrt ((1 - s) / 2) : ℝ) : ℂ) *
    overlapColumnCross K

theorem coneImage_denominator {s : ℝ} (hs : |s| ≤ 1) (K : SourceOverlapMatrix)
    (θ : ConePhase) :
    1 - sourceRadiusSq (coneImage K s θ) =
      coneImageA K s - (coneImageB K s * conePhasePoint θ).re := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq hs
  have hz2 : Complex.normSq (conePhasePoint θ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_conePhasePoint]; norm_num
  simp only [coneImage, coneNormal, sourceRadiusSq, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_ofReal, hz2, one_mul, ← pow_two, hp, hm]
  simp [coneImageA, coneImageB, overlapColumnEnergy, overlapColumnCross,
    Complex.mul_re, Complex.mul_im]
  ring

theorem coneImage_discriminant {s : ℝ} (hs : |s| ≤ 1) (K : SourceOverlapMatrix) :
    coneImageA K s ^ 2 - Complex.normSq (coneImageB K s) =
      (1 - s ^ 2) * overlapDeterminant K +
        ((1 - s) / 2 * (1 - overlapColumnEnergy K 0) -
          (1 + s) / 2 * (1 - overlapColumnEnergy K 1)) ^ 2 := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq hs
  have hb : Complex.normSq (coneImageB K s) =
      (1 - s ^ 2) * Complex.normSq (overlapColumnCross K) := by
    calc
      _ = 4 * Real.sqrt ((1 + s) / 2) ^ 2 * Real.sqrt ((1 - s) / 2) ^ 2 *
          Complex.normSq (overlapColumnCross K) := by
        simp only [coneImageB, Complex.normSq_mul, Complex.normSq_neg,
          Complex.normSq_ofReal, Complex.normSq_ofNat]
        ring
      _ = _ := by rw [hp, hm]; ring
  rw [hb, overlapDeterminant_columns]
  unfold coneImageA
  ring

theorem coneImageB_norm_lt {s : ℝ} (hs : |s| < 1) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) : ‖coneImageB K s‖ < coneImageA K s := by
  have hρ := overlapOperatorNorm_nonneg K
  have hA0 : 0 < 1 - overlapColumnEnergy K 0 := by
    have h := overlapColumnEnergy_le K 0
    nlinarith
  have hA1 : 0 < 1 - overlapColumnEnergy K 1 := by
    have h := overlapColumnEnergy_le K 1
    nlinarith
  obtain ⟨hs0, hs1⟩ := abs_lt.mp hs
  have hA : 0 < coneImageA K s := by
    unfold coneImageA
    exact add_pos (mul_pos (by linarith) hA0) (mul_pos (by linarith) hA1)
  have hd := coneImage_discriminant hs.le K
  have hpos : 0 < (1 - s ^ 2) * overlapDeterminant K := by
    exact mul_pos (by nlinarith [abs_nonneg s, sq_abs s]) (overlapDeterminant_pos hK)
  rw [Complex.normSq_eq_norm_sq] at hd
  nlinarith [sq_nonneg ((1 - s) / 2 * (1 - overlapColumnEnergy K 0) -
    (1 + s) / 2 * (1 - overlapColumnEnergy K 1)), norm_nonneg (coneImageB K s)]

theorem integral_coneImage_energy (K : SourceOverlapMatrix) {s : ℝ} (hs : |s| ≤ 1) :
    (∫ θ, sourceRadiusSq (coneImage K s θ) ∂AddCircle.haarAddCircle) =
      (1 - s) / 2 * overlapColumnEnergy K 0 +
        (1 + s) / 2 * overlapColumnEnergy K 1 := by
  have he (θ : ConePhase) :
      sourceRadiusSq (coneImage K s θ) =
        (1 - coneImageA K s) + (coneImageB K s * conePhasePoint θ).re := by
    have h := coneImage_denominator hs K θ
    linarith
  simp_rw [he]
  rw [integral_add (integrable_const _) (by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _), integral_const,
      integral_conePhasePoint_re_mul]
  simp [coneImageA]
  ring

theorem integral_coneImage_energy_lower {s : ℝ} (hs : |s| ≤ 1 / 4)
    (K : SourceOverlapMatrix) :
    3 / 8 * overlapOperatorNorm K ^ 2 ≤
      ∫ θ, sourceRadiusSq (coneImage K s θ) ∂AddCircle.haarAddCircle := by
  have hs' : |s| ≤ 1 := le_trans hs (by norm_num)
  rw [integral_coneImage_energy K hs']
  have hf := overlapOperatorNorm_sq_le_frobenius K
  have he : overlapFrobeniusSq K = overlapColumnEnergy K 0 + overlapColumnEnergy K 1 := by
    simp [overlapFrobeniusSq, overlapColumnEnergy, Fin.sum_univ_two]; ring
  rw [he] at hf
  have h0 : 0 ≤ overlapColumnEnergy K 0 := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have h1 : 0 ≤ overlapColumnEnergy K 1 := add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  obtain ⟨hs0, hs1⟩ := abs_le.mp hs
  nlinarith

theorem integral_coneImage_inv_bound {s : ℝ} (hs : |s| < 1) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) :
    (∫ θ, (1 - sourceRadiusSq (coneImage K s θ))⁻¹ ∂AddCircle.haarAddCircle) ≤
      (Real.sqrt ((1 - s ^ 2) * overlapDeterminant K))⁻¹ := by
  have h := (circleAverage_inv_affine (coneImageA K s) (coneImageB K s)
    (coneImageB_norm_lt hs hK)).1
  simp_rw [coneImage_denominator hs.le]
  rw [integral_conePhasePoint (fun z ↦ (coneImageA K s - (coneImageB K s * z).re)⁻¹), h]
  have hp : 0 < (1 - s ^ 2) * overlapDeterminant K :=
    mul_pos (by nlinarith [abs_nonneg s, sq_abs s]) (overlapDeterminant_pos hK)
  apply (inv_le_inv₀ (Real.sqrt_pos.mpr _) (Real.sqrt_pos.mpr hp)).mpr
  · apply Real.sqrt_le_sqrt
    rw [coneImage_discriminant hs.le]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · rw [coneImage_discriminant hs.le]
    positivity

end ConeImageEstimates

section ConeCoordinates

open MeasureTheory Complex Real Matrix WithLp
open scoped BigOperators

def coneBasis (t : ℝ) (z : ℂ) : SourceOverlapMatrix :=
  !![(Real.sqrt ((1 + t) / 2) : ℂ), Real.sqrt ((1 - t) / 2);
     z * Real.sqrt ((1 - t) / 2), -z * Real.sqrt ((1 + t) / 2)]

theorem coneBasis_col_zero (t : ℝ) (z : ℂ) :
    (fun i ↦ coneBasis t z i 0) = coneDirection t z := by
  funext i; fin_cases i <;> rfl

theorem coneBasis_col_one (t : ℝ) (z : ℂ) :
    (fun i ↦ coneBasis t z i 1) = coneNormal t z := by
  funext i; fin_cases i <;> rfl

theorem coneBasis_adjoint_apply (t : ℝ) (z : ℂ) (v : Fin 2 → ℂ) :
    (coneBasis t z)ᴴ *ᵥ v =
      ![coneInner (coneDirection t z) v, coneInner (coneNormal t z) v] := by
  ext i; fin_cases i <;>
    simp [coneBasis, coneDirection, coneNormal, coneInner, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.conjTranspose_apply]

theorem coneBasis_adjoint_energy {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1)
    (v : Fin 2 → ℂ) : sourceRadiusSq ((coneBasis t z)ᴴ *ᵥ v) = sourceRadiusSq v := by
  rw [coneBasis_adjoint_apply]
  exact cone_parseval ht hz v

theorem coneBasis_energy {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1)
    (v : Fin 2 → ℂ) : sourceRadiusSq (coneBasis t z *ᵥ v) = sourceRadiusSq v := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  have hz2 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have he : coneBasis t z *ᵥ v =
      ![(Real.sqrt ((1 + t) / 2) : ℂ) * v 0 + Real.sqrt ((1 - t) / 2) * v 1,
        z * ((Real.sqrt ((1 - t) / 2) : ℂ) * v 0 - Real.sqrt ((1 + t) / 2) * v 1)] := by
    ext i
    fin_cases i <;> simp [coneBasis, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [he]
  simp only [sourceRadiusSq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.normSq_mul, hz2, one_mul]
  rw [Complex.normSq_add, Complex.normSq_sub]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two, hp, hm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    map_mul, Complex.conj_re, Complex.conj_im, Complex.conj_ofReal]
  ring

def coneRotatedOverlap (K : SourceOverlapMatrix) (t s : ℝ) (φ ψ : ConePhase) :
    SourceOverlapMatrix :=
  (coneBasis t (conePhasePoint φ))ᴴ * K * coneBasis s (conePhasePoint ψ)

theorem overlapOperatorNorm_le_of_energy (K : SourceOverlapMatrix) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ v : Fin 2 → ℂ, sourceRadiusSq (K *ᵥ v) ≤ ρ ^ 2 * sourceRadiusSq v) :
    overlapOperatorNorm K ≤ ρ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hρ
  intro v
  have hh := h (ofLp v)
  rw [sourceRadiusSq_eq_norm_sq, sourceRadiusSq_eq_norm_sq] at hh
  simp only [toLp_ofLp] at hh
  change ‖toLp 2 (K *ᵥ ofLp v)‖ ≤ ρ * ‖v‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ (norm_nonneg v))).mp
  simpa only [mul_pow] using hh

theorem coneRotatedOverlap_norm_le {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1)
    (K : SourceOverlapMatrix) (φ ψ : ConePhase) :
    overlapOperatorNorm (coneRotatedOverlap K t s φ ψ) ≤ overlapOperatorNorm K := by
  apply overlapOperatorNorm_le_of_energy _ (overlapOperatorNorm_nonneg K)
  intro v
  unfold coneRotatedOverlap
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    coneBasis_adjoint_energy ht (norm_conePhasePoint φ)]
  have h := sourceRadiusSq_mulVec_le K (coneBasis s (conePhasePoint ψ) *ᵥ v)
  rwa [coneBasis_energy hs (norm_conePhasePoint ψ)] at h

theorem coneRotatedOverlap_apply (K : SourceOverlapMatrix) (t s : ℝ) (φ ψ : ConePhase) :
    coneRotatedOverlap K t s φ ψ =
      !![coneInner (coneDirection t (conePhasePoint φ)) (K *ᵥ coneDirection s (conePhasePoint ψ)),
         coneInner (coneDirection t (conePhasePoint φ)) (coneImage K s ψ);
         coneInner (coneNormal t (conePhasePoint φ)) (K *ᵥ coneDirection s (conePhasePoint ψ)),
         coneInner (coneNormal t (conePhasePoint φ)) (coneImage K s ψ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneRotatedOverlap, coneBasis, coneInner, coneDirection, coneNormal,
      coneImage, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring

@[fun_prop]
theorem continuous_coneRotatedOverlap (K : SourceOverlapMatrix) (t s : ℝ) :
    Continuous (fun p : ConePhase × ConePhase ↦ coneRotatedOverlap K t s p.1 p.2) := by
  unfold coneRotatedOverlap coneBasis
  fun_prop

theorem coneRotatedOverlap_adjoint (K : SourceOverlapMatrix) (t s : ℝ) (φ ψ : ConePhase) :
    (coneRotatedOverlap K t s φ ψ)ᴴ = coneRotatedOverlap Kᴴ s t ψ φ := by
  simp [coneRotatedOverlap, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end ConeCoordinates

section ConeBaseBound

open MeasureTheory Complex Real
open scoped ENNReal

def coneBaseIntegral (K : SourceOverlapMatrix) (t s : ℝ) : ℝ :=
  ∫ ψ, conePhaseJ t (coneImage K s ψ) ∂AddCircle.haarAddCircle

theorem coneBaseIntegral_ge_one {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| < 1) (hs : |s| ≤ 1) : 1 ≤ coneBaseIntegral K t s := by
  calc
    1 = ∫ _ : ConePhase, (1 : ℝ) ∂AddCircle.haarAddCircle := by simp
    _ ≤ _ := integral_mono (integrable_const _)
      ((continuous_conePhaseJ_image ht hs hK).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (fun ψ ↦ conePhaseJ_ge_one ht (coneImage_energy_lt_one hs hK ψ))

theorem cone_integral_sq_le (f : ConePhase → ℝ) (hf : Continuous f) :
    (∫ θ, f θ ∂AddCircle.haarAddCircle) ^ 2 ≤
      ∫ θ, f θ ^ 2 ∂AddCircle.haarAddCircle := by
  have h := ProbabilityTheory.variance_nonneg f AddCircle.haarAddCircle
  rw [ProbabilityTheory.variance_eq_sub
    (hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at h
  exact sub_nonneg.mp h

theorem continuous_coneImage_sqrt_inv {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {s : ℝ} (hs : |s| ≤ 1) :
    Continuous (fun ψ ↦ (Real.sqrt (1 - sourceRadiusSq (coneImage K s ψ)))⁻¹) := by
  apply Continuous.inv₀
  · unfold sourceRadiusSq
    fun_prop
  · intro ψ
    exact (Real.sqrt_pos.mpr (sub_pos.mpr (coneImage_energy_lt_one hs hK ψ))).ne'

theorem coneBaseIntegral_bound {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| < 1) (hs : |s| < 1) :
    coneBaseIntegral K t s ≤
      (Real.sqrt (1 - t ^ 2))⁻¹ * (Real.sqrt (Real.sqrt (1 - s ^ 2)))⁻¹ *
        (Real.sqrt (Real.sqrt (overlapDeterminant K)))⁻¹ := by
  let f : ConePhase → ℝ := fun ψ ↦ (Real.sqrt (1 - sourceRadiusSq (coneImage K s ψ)))⁻¹
  have hf : Continuous f := continuous_coneImage_sqrt_inv hK hs.le
  have hi : Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsq := cone_integral_sq_le f hf
  have he (ψ : ConePhase) : f ψ ^ 2 = (1 - sourceRadiusSq (coneImage K s ψ))⁻¹ := by
    dsimp [f]
    rw [inv_pow, Real.sq_sqrt (sub_nonneg.mpr (coneImage_energy_lt_one hs.le hK ψ).le)]
  simp_rw [he] at hsq
  have hsq' := le_trans hsq (integral_coneImage_inv_bound hs hK)
  have hs2 : 0 < 1 - s ^ 2 := by nlinarith [abs_nonneg s, sq_abs s]
  have hprod : 0 < (1 - s ^ 2) * overlapDeterminant K :=
    mul_pos hs2 (overlapDeterminant_pos hK)
  have hbound : (∫ ψ, f ψ ∂AddCircle.haarAddCircle) ≤
      (Real.sqrt (Real.sqrt ((1 - s ^ 2) * overlapDeterminant K)))⁻¹ := by
    have hn := Real.sqrt_nonneg (Real.sqrt ((1 - s ^ 2) * overlapDeterminant K))
    have heq : ((Real.sqrt (Real.sqrt ((1 - s ^ 2) * overlapDeterminant K)))⁻¹) ^ 2 =
        (Real.sqrt ((1 - s ^ 2) * overlapDeterminant K))⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
    nlinarith [inv_nonneg.mpr hn]
  have hJ := (continuous_conePhaseJ_image ht hs.le hK).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hI : coneBaseIntegral K t s ≤
      (Real.sqrt (1 - t ^ 2))⁻¹ * ∫ ψ, f ψ ∂AddCircle.haarAddCircle := by
    rw [← integral_const_mul]
    exact integral_mono hJ (hi.const_mul _) (fun ψ ↦
      conePhaseR_inv_bound ht (coneImage_energy_lt_one hs.le hK ψ))
  apply le_trans hI
  have hm := mul_le_mul_of_nonneg_left hbound
    (inv_nonneg.mpr (Real.sqrt_nonneg (1 - t ^ 2)))
  simpa only [Real.sqrt_mul hs2.le, Real.sqrt_mul (Real.sqrt_nonneg (1 - s ^ 2)),
    mul_inv, mul_assoc] using hm

theorem coneBaseIntegral_weighted_lower {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {t s : ℝ}
    (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    overlapOperatorNorm K ^ 2 / 8 * coneBaseIntegral K t s ≤
      ∫ ψ, sourceRadiusSq (coneImage K s ψ) * conePhaseJ t (coneImage K s ψ)
        ∂AddCircle.haarAddCircle := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hs' : |s| ≤ 1 := le_trans hs (by norm_num)
  have hJ := continuous_conePhaseJ_image ht' hs' hK
  have hx : Continuous (fun ψ ↦ sourceRadiusSq (coneImage K s ψ)) := by
    unfold sourceRadiusSq
    fun_prop
  apply conePhaseJ_weighted_lower ht
    (by nlinarith [overlapOperatorNorm_nonneg K]) (coneImage K s)
    (coneImage_energy_lt_one hs' hK)
  · exact hJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (hx.mul hJ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact integral_coneImage_energy_lower hs K

end ConeBaseBound

section ConeExponentialBound

open Real

theorem cone_log_bound {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1 / 16) :
    -Real.log (1 - y) ≤ 16 / 15 * y := by
  have hp : 0 < 1 - y := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at h
  apply le_trans h
  have hh : (1 - y)⁻¹ ≤ 1 + 16 / 15 * y := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith

theorem cone_inverse_sqrt_bound {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1 / 16) :
    (Real.sqrt (1 - y))⁻¹ ≤ Real.exp (8 / 15 * y) := by
  have hp : 0 < 1 - y := by linarith
  rw [← Real.exp_log (inv_pos.mpr (Real.sqrt_pos.mpr hp)), Real.log_inv,
    Real.log_sqrt hp.le]
  apply Real.exp_le_exp.mpr
  have h := cone_log_bound hy hy1
  linarith

theorem cone_inverse_fourth_root_bound {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1 / 16) :
    (Real.sqrt (Real.sqrt (1 - y)))⁻¹ ≤ Real.exp (4 / 15 * y) := by
  have hp : 0 < 1 - y := by linarith
  rw [← Real.exp_log (inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hp))),
    Real.log_inv, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hp.le]
  apply Real.exp_le_exp.mpr
  have h := cone_log_bound hy hy1
  linarith

theorem coneBaseIntegral_exp_bound {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {t s : ℝ}
    (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    coneBaseIntegral K t s ≤ Real.exp (8 / 15 * t ^ 2 + 4 / 15 * s ^ 2) *
      (Real.sqrt (Real.sqrt (overlapDeterminant K)))⁻¹ := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hs' : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  apply le_trans (coneBaseIntegral_bound hK ht' hs')
  rw [Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply mul_le_mul
    (cone_inverse_sqrt_bound (sq_nonneg t) (by nlinarith [abs_nonneg t, sq_abs t]))
    (cone_inverse_fourth_root_bound (sq_nonneg s) (by nlinarith [abs_nonneg s, sq_abs s]))
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) (Real.exp_nonneg _)

theorem cone_radial_final_arithmetic {I D Q ρ t s : ℝ}
    (hI : 0 ≤ I)
    (hD : (3 / 32 * ρ ^ 2 - 2 * (t ^ 2 + s ^ 2)) * I ≤ D)
    (hQ : Q - I ≤ 4 * ρ ^ 2 * I) :
    I - sourceEta * (1 - sourceEta) * D + sourceEta ^ 2 * (Q - I) ≤
      I * Real.exp (-ρ ^ 2 / 2000 + 2 * sourceEta * (1 - sourceEta) * (t ^ 2 + s ^ 2)) := by
  have hpoly : I - sourceEta * (1 - sourceEta) * D + sourceEta ^ 2 * (Q - I) ≤
      I * (1 + (-ρ ^ 2 / 2000 + 2 * sourceEta * (1 - sourceEta) * (t ^ 2 + s ^ 2))) := by
    norm_num [sourceEta] at *
    nlinarith [mul_nonneg (sq_nonneg ρ) hI]
  exact le_trans hpoly (mul_le_mul_of_nonneg_left (by
    have h := Real.add_one_le_exp
      (-ρ ^ 2 / 2000 + 2 * sourceEta * (1 - sourceEta) * (t ^ 2 + s ^ 2))
    linarith only [h]) hI)

theorem cone_radial_exponential_arithmetic {I q ρ t s Δ : ℝ}
    (hI : I ≤ Real.exp (8 / 15 * t ^ 2 + 4 / 15 * s ^ 2) *
      (Real.sqrt (Real.sqrt Δ))⁻¹)
    (hq : q ≤ I * Real.exp (-ρ ^ 2 / 2000 + 2 * sourceEta * (1 - sourceEta) * (t ^ 2 + s ^ 2))) :
    q ≤ Real.exp (t ^ 2 + s ^ 2 - ρ ^ 2 / 2000) * (Real.sqrt (Real.sqrt Δ))⁻¹ := by
  apply le_trans hq
  apply le_trans (mul_le_mul_of_nonneg_right hI (Real.exp_nonneg _))
  rw [mul_right_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  norm_num [sourceEta]
  nlinarith [sq_nonneg t, sq_nonneg s]

end ConeExponentialBound

end NLA.FR05
