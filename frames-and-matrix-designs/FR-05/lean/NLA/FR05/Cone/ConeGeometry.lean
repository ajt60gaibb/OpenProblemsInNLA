import NLA.FR05.Cone.Phase
import NLA.FR05.Overlap.Overlap

/-!
# Cone geometry, radial corrections, and matrix bounds

The sections develop `ConeGeometry`, `ConeRadialCorrection`, `ConeMatrixBounds`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ConeGeometry

open MeasureTheory Complex Metric Real
open scoped BigOperators

def coneDirection (t : ℝ) (z : ℂ) : (Fin 2 → ℂ) :=
  ![(Real.sqrt ((1 + t) / 2) : ℂ), z * Real.sqrt ((1 - t) / 2)]

def coneNormal (t : ℝ) (z : ℂ) : (Fin 2 → ℂ) :=
  ![(Real.sqrt ((1 - t) / 2) : ℂ), -z * Real.sqrt ((1 + t) / 2)]

def coneInner (v w : (Fin 2 → ℂ)) : ℂ := star (v 0) * w 0 + star (v 1) * w 1

def conePhaseU (t : ℝ) (v : (Fin 2 → ℂ)) : ℝ :=
  1 - (1 - t) / 2 * Complex.normSq (v 0) - (1 + t) / 2 * Complex.normSq (v 1)

def conePhaseB (t : ℝ) (v : (Fin 2 → ℂ)) : ℂ :=
  -2 * ((Real.sqrt ((1 + t) / 2) * Real.sqrt ((1 - t) / 2) : ℝ) : ℂ) *
    (v 0 * star (v 1))

def conePhaseR (t : ℝ) (v : (Fin 2 → ℂ)) : ℝ :=
  Real.sqrt (conePhaseU t v ^ 2 - Complex.normSq (conePhaseB t v))

theorem cone_sqrt_sq {t : ℝ} (ht : |t| ≤ 1) :
    Real.sqrt ((1 + t) / 2) ^ 2 = (1 + t) / 2 ∧
    Real.sqrt ((1 - t) / 2) ^ 2 = (1 - t) / 2 := by
  obtain ⟨ht0, ht1⟩ := abs_le.mp ht
  constructor <;> apply Real.sq_sqrt <;> linarith

theorem coneDirection_energy {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    sourceRadiusSq (coneDirection t z) = 1 := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  simp only [sourceRadiusSq, coneDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [Complex.normSq_eq_norm_sq z, hz]
  nlinarith

theorem coneNormal_energy {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    sourceRadiusSq (coneNormal t z) = 1 := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  simp only [sourceRadiusSq, coneNormal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal]
  rw [Complex.normSq_eq_norm_sq z, hz]
  nlinarith

theorem coneNormal_inner_identity {t : ℝ} (ht : |t| ≤ 1) {z : ℂ}
    (hz : ‖z‖ = 1) (v : (Fin 2 → ℂ)) :
    1 - Complex.normSq (coneInner (coneNormal t z) v) =
      conePhaseU t v - (conePhaseB t v * z).re := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  have hz2 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  simp only [coneInner, coneNormal, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  simp only [Complex.star_def, map_mul, map_neg, Complex.conj_ofReal]
  rw [Complex.normSq_add]
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_conj,
    Complex.normSq_ofReal, hz2, one_mul, ← pow_two, hp, hm]
  simp [conePhaseU, conePhaseB, Complex.mul_re, Complex.mul_im]
  ring

theorem conePhaseB_normSq {t : ℝ} (ht : |t| ≤ 1) (v : (Fin 2 → ℂ)) :
    Complex.normSq (conePhaseB t v) =
      (1 - t ^ 2) * Complex.normSq (v 0) * Complex.normSq (v 1) := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  calc
    _ = 4 * Real.sqrt ((1 + t) / 2) ^ 2 * Real.sqrt ((1 - t) / 2) ^ 2 *
        Complex.normSq (v 0) * Complex.normSq (v 1) := by
      simp only [conePhaseB, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
        Complex.normSq_neg, Complex.normSq_ofReal, Complex.normSq_ofNat]
      ring
    _ = _ := by rw [hp, hm]; ring

theorem conePhase_discriminant {t : ℝ} (ht : |t| ≤ 1) (v : (Fin 2 → ℂ)) :
    conePhaseU t v ^ 2 - Complex.normSq (conePhaseB t v) =
      (1 - t ^ 2) * (1 - sourceRadiusSq v) +
        ((Complex.normSq (v 0) - Complex.normSq (v 1)) / 2 +
          t * (1 - sourceRadiusSq v / 2)) ^ 2 := by
  rw [conePhaseB_normSq ht]
  unfold conePhaseU sourceRadiusSq
  ring

theorem conePhaseU_lower {t : ℝ} (ht : |t| ≤ 1) (v : (Fin 2 → ℂ)) :
    1 - sourceRadiusSq v ≤ conePhaseU t v := by
  have h0 := Complex.normSq_nonneg (v 0)
  have h1 := Complex.normSq_nonneg (v 1)
  obtain ⟨ht0, ht1⟩ := abs_le.mp ht
  unfold conePhaseU sourceRadiusSq
  nlinarith

theorem conePhaseB_norm_lt {t : ℝ} (ht : |t| < 1) {v : (Fin 2 → ℂ)}
    (hv : sourceRadiusSq v < 1) : ‖conePhaseB t v‖ < conePhaseU t v := by
  have hu := conePhaseU_lower ht.le v
  have hpos : 0 < (1 - t ^ 2) * (1 - sourceRadiusSq v) := by
    apply mul_pos _ (sub_pos.mpr hv)
    nlinarith [abs_nonneg t, sq_abs t]
  have hd := conePhase_discriminant ht.le v
  rw [Complex.normSq_eq_norm_sq] at hd
  nlinarith [sq_nonneg ((Complex.normSq (v 0) - Complex.normSq (v 1)) / 2 +
    t * (1 - sourceRadiusSq v / 2)), norm_nonneg (conePhaseB t v)]

theorem conePhaseR_pos {t : ℝ} (ht : |t| < 1) {v : (Fin 2 → ℂ)}
    (hv : sourceRadiusSq v < 1) : 0 < conePhaseR t v := by
  unfold conePhaseR
  apply Real.sqrt_pos.mpr
  have hb := conePhaseB_norm_lt ht hv
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (conePhaseB t v)]

theorem conePhase_integrals {t : ℝ} (ht : |t| < 1) {v : (Fin 2 → ℂ)}
    (hv : sourceRadiusSq v < 1) :
    circleAverage (fun z ↦ (1 - Complex.normSq (coneInner (coneNormal t z) v))⁻¹) 0 1 =
      (conePhaseR t v)⁻¹ ∧
    circleAverage (fun z ↦ (1 - Complex.normSq (coneInner (coneNormal t z) v))⁻¹ ^ 2) 0 1 =
      conePhaseU t v / conePhaseR t v ^ 3 := by
  have h := circleAverage_inv_affine (conePhaseU t v) (conePhaseB t v)
    (conePhaseB_norm_lt ht hv)
  have he (z : ℂ) (hz : z ∈ sphere (0 : ℂ) |(1 : ℝ)|) :=
    coneNormal_inner_identity ht.le (show ‖z‖ = 1 by simpa using hz) v
  constructor
  · exact (circleAverage_congr_sphere (fun z hz ↦ congrArg Inv.inv (he z hz))).trans h.1
  · exact (circleAverage_congr_sphere
      (fun z hz ↦ congrArg (fun x : ℝ ↦ x⁻¹ ^ 2) (he z hz))).trans h.2

@[fun_prop]
theorem continuous_coneDirection (t : ℝ) : Continuous (coneDirection t) := by
  unfold coneDirection
  fun_prop

@[fun_prop]
theorem continuous_coneNormal (t : ℝ) : Continuous (coneNormal t) := by
  unfold coneNormal
  fun_prop

@[fun_prop]
theorem continuous_coneInner : Continuous (fun p : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
    coneInner p.1 p.2) := by
  unfold coneInner
  fun_prop

theorem cone_parseval {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1)
    (v : Fin 2 → ℂ) :
    Complex.normSq (coneInner (coneDirection t z) v) +
      Complex.normSq (coneInner (coneNormal t z) v) = sourceRadiusSq v := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  have hz2 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  simp only [coneInner, coneNormal, coneDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Complex.star_def, map_mul, map_neg, Complex.conj_ofReal,
    Complex.normSq_add, Complex.normSq_neg, Complex.normSq_conj,
    Complex.normSq_ofReal, hz2, one_mul, ← pow_two, hp, hm]
  simp [sourceRadiusSq, Complex.mul_re, Complex.mul_im]
  ring

theorem coneNormal_inner_normSq_le {t : ℝ} (ht : |t| ≤ 1) {z : ℂ}
    (hz : ‖z‖ = 1) (v : Fin 2 → ℂ) :
    Complex.normSq (coneInner (coneNormal t z) v) ≤ sourceRadiusSq v := by
  have h := cone_parseval ht hz v
  linarith [Complex.normSq_nonneg (coneInner (coneDirection t z) v)]

theorem conePhaseR_sq {t : ℝ} (ht : |t| < 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) :
    conePhaseR t v ^ 2 =
      (1 - t ^ 2) * (1 - sourceRadiusSq v) +
        ((Complex.normSq (v 0) - Complex.normSq (v 1)) / 2 +
          t * (1 - sourceRadiusSq v / 2)) ^ 2 := by
  rw [conePhaseR, Real.sq_sqrt, conePhase_discriminant ht.le]
  have h := conePhaseB_norm_lt ht hv
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg (conePhaseB t v)]

theorem conePhaseR_inv_bound {t : ℝ} (ht : |t| < 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) :
    (conePhaseR t v)⁻¹ ≤
      (Real.sqrt (1 - t ^ 2))⁻¹ * (Real.sqrt (1 - sourceRadiusSq v))⁻¹ := by
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
  have hs : 0 < Real.sqrt ((1 - t ^ 2) * (1 - sourceRadiusSq v)) :=
    Real.sqrt_pos.mpr (mul_pos ht2 (sub_pos.mpr hv))
  calc
    _ ≤ (Real.sqrt ((1 - t ^ 2) * (1 - sourceRadiusSq v)))⁻¹ := by
      apply (inv_le_inv₀ (conePhaseR_pos ht hv) hs).mpr
      rw [Real.sqrt_le_iff]
      exact ⟨(conePhaseR_pos ht hv).le, by rw [conePhaseR_sq ht hv]; exact le_add_of_nonneg_right (sq_nonneg _)⟩
    _ = _ := by rw [Real.sqrt_mul ht2.le, mul_inv]

theorem conePhaseU_upper_quarter {t : ℝ} (ht : |t| ≤ 1 / 4) (v : Fin 2 → ℂ) :
    conePhaseU t v ≤ 1 - 3 / 8 * sourceRadiusSq v := by
  obtain ⟨ht0, ht1⟩ := abs_le.mp ht
  have h0 := Complex.normSq_nonneg (v 0)
  have h1 := Complex.normSq_nonneg (v 1)
  unfold conePhaseU sourceRadiusSq
  nlinarith

theorem cone_radial_correction_pointwise {t : ℝ} (ht : |t| ≤ 1 / 4)
    {v : Fin 2 → ℂ} (hv : sourceRadiusSq v < 1) :
    3 / 8 * sourceRadiusSq v - 2 * t ^ 2 ≤
      1 - (1 - sourceRadiusSq v) * conePhaseU t v / conePhaseR t v ^ 2 := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith [abs_nonneg t, sq_abs t]
  have hx := sourceRadiusSq_nonneg v
  have hu := conePhaseU_upper_quarter ht v
  have hr := conePhaseR_pos ht' hv
  have hd := conePhaseR_sq ht' hv
  have hcoef : 0 ≤ 1 - 3 / 8 * sourceRadiusSq v + 2 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hp : conePhaseU t v ≤
      (1 - 3 / 8 * sourceRadiusSq v + 2 * t ^ 2) * (1 - t ^ 2) := by
    nlinarith [sq_nonneg t, mul_nonneg hx (sq_nonneg t)]
  have hmul := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hv.le)
  have hmul' := mul_le_mul_of_nonneg_left
    (show (1 - t ^ 2) * (1 - sourceRadiusSq v) ≤ conePhaseR t v ^ 2 by
      rw [hd]; exact le_add_of_nonneg_right (sq_nonneg _)) hcoef
  have hdiv : (1 - sourceRadiusSq v) * conePhaseU t v / conePhaseR t v ^ 2 ≤
      1 - 3 / 8 * sourceRadiusSq v + 2 * t ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by nlinarith only [hmul, hmul'])
  linarith

end ConeGeometry

section ConeRadialCorrection

open MeasureTheory Complex Real
open scoped ENNReal

def conePhaseJ (t : ℝ) (v : Fin 2 → ℂ) : ℝ := (conePhaseR t v)⁻¹

theorem coneNormal_denominator_pos {t : ℝ} (ht : |t| ≤ 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) (θ : ConePhase) :
    0 < 1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v) := by
  have h := coneNormal_inner_normSq_le ht (norm_conePhasePoint θ) v
  linarith

theorem continuous_coneNormal_inv {t : ℝ} (ht : |t| ≤ 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) :
    Continuous (fun θ : ConePhase ↦
      (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v))⁻¹) := by
  unfold coneInner
  apply Continuous.inv₀ (by fun_prop)
  intro θ
  exact (coneNormal_denominator_pos ht hv θ).ne'

theorem integral_coneNormal_inv {t : ℝ} (ht : |t| < 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) :
    (∫ θ : ConePhase,
      (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v))⁻¹
        ∂AddCircle.haarAddCircle) = conePhaseJ t v := by
  rw [integral_conePhasePoint
    (fun z ↦ (1 - Complex.normSq (coneInner (coneNormal t z) v))⁻¹)]
  exact (conePhase_integrals ht hv).1

theorem integral_coneNormal_inv_sq {t : ℝ} (ht : |t| < 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) :
    (∫ θ : ConePhase,
      (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v))⁻¹ ^ 2
        ∂AddCircle.haarAddCircle) = conePhaseU t v / conePhaseR t v ^ 3 := by
  rw [integral_conePhasePoint
    (fun z ↦ (1 - Complex.normSq (coneInner (coneNormal t z) v))⁻¹ ^ 2)]
  exact (conePhase_integrals ht hv).2

theorem conePhaseJ_ge_one {t : ℝ} (ht : |t| < 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) : 1 ≤ conePhaseJ t v := by
  rw [← integral_coneNormal_inv ht hv]
  have hi := (continuous_coneNormal_inv ht.le hv).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  calc
    1 = ∫ _ : ConePhase, (1 : ℝ) ∂AddCircle.haarAddCircle := by simp
    _ ≤ _ := integral_mono (integrable_const 1) hi (fun θ ↦ by
      have hp := coneNormal_denominator_pos ht.le hv θ
      rw [← one_div]
      apply (le_div_iff₀ hp).mpr
      linarith [Complex.normSq_nonneg (coneInner (coneNormal t (conePhasePoint θ)) v)])

theorem integral_cone_radial_correction {t : ℝ} (ht : |t| < 1) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v < 1) :
    (∫ θ : ConePhase,
      Complex.normSq (coneInner (coneDirection t (conePhasePoint θ)) v) /
        (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v)) ^ 2
          ∂AddCircle.haarAddCircle) =
      conePhaseJ t v *
        (1 - (1 - sourceRadiusSq v) * conePhaseU t v / conePhaseR t v ^ 2) := by
  have hi := (continuous_coneNormal_inv ht.le hv).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun θ : ConePhase ↦
      (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v))⁻¹ ^ 2)
        AddCircle.haarAddCircle :=
    ((continuous_coneNormal_inv ht.le hv).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (θ : ConePhase) :
      Complex.normSq (coneInner (coneDirection t (conePhasePoint θ)) v) /
        (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v)) ^ 2 =
      (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v))⁻¹ -
        (1 - sourceRadiusSq v) *
          (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v))⁻¹ ^ 2 := by
    have h := cone_parseval ht.le (norm_conePhasePoint θ) v
    have hp := coneNormal_denominator_pos ht.le hv θ
    field_simp
    linarith
  simp_rw [he]
  rw [integral_sub hi (hi2.const_mul _), integral_const_mul,
    integral_coneNormal_inv ht hv, integral_coneNormal_inv_sq ht hv]
  unfold conePhaseJ
  field_simp [(conePhaseR_pos ht hv).ne']

theorem integral_cone_radial_correction_lower {t : ℝ} (ht : |t| ≤ 1 / 4)
    {v : Fin 2 → ℂ} (hv : sourceRadiusSq v < 1) :
    (3 / 8 * sourceRadiusSq v - 2 * t ^ 2) * conePhaseJ t v ≤
      ∫ θ : ConePhase,
        Complex.normSq (coneInner (coneDirection t (conePhasePoint θ)) v) /
          (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint θ)) v)) ^ 2
            ∂AddCircle.haarAddCircle := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  rw [integral_cone_radial_correction ht' hv, mul_comm (conePhaseJ t v)]
  exact mul_le_mul_of_nonneg_right (cone_radial_correction_pointwise ht hv)
    (le_trans zero_le_one (conePhaseJ_ge_one ht' hv))

theorem conePhaseJ_small {t : ℝ} (ht : |t| ≤ 1 / 4) {v : Fin 2 → ℂ}
    (hv : sourceRadiusSq v ≤ 1 / 4) : conePhaseJ t v ≤ 4 / 3 := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hv' : sourceRadiusSq v < 1 := lt_of_le_of_lt hv (by norm_num)
  have hr := conePhaseR_pos ht' hv'
  have hd := conePhaseR_sq ht' hv'
  have ht2 : t ^ 2 ≤ 1 / 16 := by nlinarith [abs_nonneg t, sq_abs t]
  have hx := sourceRadiusSq_nonneg v
  have hR : 3 / 4 ≤ conePhaseR t v := by
    nlinarith [sq_nonneg ((Complex.normSq (v 0) - Complex.normSq (v 1)) / 2 +
      t * (1 - sourceRadiusSq v / 2)), mul_nonneg hx (sq_nonneg t)]
  simpa only [conePhaseJ, one_div] using
    (div_le_iff₀ hr).mpr (show 1 ≤ (4 / 3) * conePhaseR t v by linarith)

theorem conePhaseJ_weight_pointwise {t ρ : ℝ} (ht : |t| ≤ 1 / 4)
    (hρ : ρ ^ 2 ≤ 1) {v : Fin 2 → ℂ} (hv : sourceRadiusSq v < 1) :
    ρ ^ 2 / 4 * (conePhaseJ t v - 4 / 3) ≤ sourceRadiusSq v * conePhaseJ t v := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hJ := conePhaseJ_ge_one ht' hv
  by_cases hx : sourceRadiusSq v ≤ ρ ^ 2 / 4
  · have hsmall := conePhaseJ_small ht (le_trans hx (by linarith))
    have hnonneg := mul_nonneg (sourceRadiusSq_nonneg v) (le_trans zero_le_one hJ)
    nlinarith [sq_nonneg ρ]
  · have hx' : ρ ^ 2 / 4 ≤ sourceRadiusSq v := le_of_lt (lt_of_not_ge hx)
    nlinarith [mul_le_mul_of_nonneg_right hx' (le_trans zero_le_one hJ),
      sq_nonneg ρ]

theorem conePhaseJ_weighted_lower {t ρ : ℝ} (ht : |t| ≤ 1 / 4) (hρ : ρ ^ 2 ≤ 1)
    (v : ConePhase → Fin 2 → ℂ) (hv : ∀ θ, sourceRadiusSq (v θ) < 1)
    (hi : Integrable (fun θ ↦ conePhaseJ t (v θ)) AddCircle.haarAddCircle)
    (hx : Integrable (fun θ ↦ sourceRadiusSq (v θ)) AddCircle.haarAddCircle)
    (hxJ : Integrable (fun θ ↦ sourceRadiusSq (v θ) * conePhaseJ t (v θ))
      AddCircle.haarAddCircle)
    (hmean : 3 / 8 * ρ ^ 2 ≤ ∫ θ, sourceRadiusSq (v θ) ∂AddCircle.haarAddCircle) :
    ρ ^ 2 / 8 * (∫ θ, conePhaseJ t (v θ) ∂AddCircle.haarAddCircle) ≤
      ∫ θ, sourceRadiusSq (v θ) * conePhaseJ t (v θ) ∂AddCircle.haarAddCircle := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have h1 : 3 / 8 * ρ ^ 2 ≤
      ∫ θ, sourceRadiusSq (v θ) * conePhaseJ t (v θ) ∂AddCircle.haarAddCircle := by
    apply le_trans hmean (integral_mono hx hxJ _)
    intro θ
    exact le_mul_of_one_le_right (sourceRadiusSq_nonneg _) (conePhaseJ_ge_one ht' (hv θ))
  have h2 := integral_mono ((hi.sub (integrable_const (4 / 3))).const_mul (ρ ^ 2 / 4))
    hxJ (fun θ ↦ conePhaseJ_weight_pointwise ht hρ (hv θ))
  simp only [Pi.sub_apply] at h2
  rw [integral_const_mul, integral_sub hi (integrable_const (4 / 3)), integral_const] at h2
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h2
  by_cases hI : (∫ θ, conePhaseJ t (v θ) ∂AddCircle.haarAddCircle) ≤ 3
  · nlinarith [mul_le_mul_of_nonneg_left hI (sq_nonneg ρ)]
  · have hI' : 3 ≤ ∫ θ, conePhaseJ t (v θ) ∂AddCircle.haarAddCircle := le_of_lt (lt_of_not_ge hI)
    nlinarith [mul_le_mul_of_nonneg_left hI' (sq_nonneg ρ)]

end ConeRadialCorrection

section ConeMatrixBounds

open MeasureTheory Complex Real Matrix WithLp
open scoped BigOperators

def overlapOperatorNorm (K : SourceOverlapMatrix) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) K‖

theorem overlapOperatorNorm_nonneg (K : SourceOverlapMatrix) :
    0 ≤ overlapOperatorNorm K := norm_nonneg _

theorem overlapOperatorNorm_conjTranspose (K : SourceOverlapMatrix) :
    overlapOperatorNorm Kᴴ = overlapOperatorNorm K := by
  unfold overlapOperatorNorm
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) (star K)‖ = _
  rw [map_star]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem sourceRadiusSq_eq_norm_sq (v : Fin 2 → ℂ) :
    sourceRadiusSq v = ‖toLp 2 v‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, sourceRadiusSq, Fin.sum_univ_two,
    Complex.normSq_eq_norm_sq]

theorem coneInner_cauchy (v w : Fin 2 → ℂ) :
    Complex.normSq (coneInner v w) ≤ sourceRadiusSq v * sourceRadiusSq w := by
  have he : sourceRadiusSq v * sourceRadiusSq w - Complex.normSq (coneInner v w) =
      Complex.normSq (v 0 * w 1 - v 1 * w 0) := by
    simp [sourceRadiusSq, coneInner, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  linarith [Complex.normSq_nonneg (v 0 * w 1 - v 1 * w 0)]

theorem sourceRadiusSq_mulVec_le (K : SourceOverlapMatrix) (v : Fin 2 → ℂ) :
    sourceRadiusSq (K *ᵥ v) ≤ overlapOperatorNorm K ^ 2 * sourceRadiusSq v := by
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) K).le_opNorm (toLp 2 v)
  simp only [Matrix.toEuclideanCLM_toLp] at h
  rw [sourceRadiusSq_eq_norm_sq, sourceRadiusSq_eq_norm_sq]
  unfold overlapOperatorNorm
  nlinarith [norm_nonneg (toLp 2 (K *ᵥ v)), norm_nonneg (toLp 2 v),
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 2) K)]

theorem sourceRadiusSq_mulVec_le_frobenius (K : SourceOverlapMatrix) (v : Fin 2 → ℂ) :
    sourceRadiusSq (K *ᵥ v) ≤ overlapFrobeniusSq K * sourceRadiusSq v := by
  have h0 := coneInner_cauchy (fun j ↦ star (K 0 j)) v
  have h1 := coneInner_cauchy (fun j ↦ star (K 1 j)) v
  simp only [coneInner, sourceRadiusSq, Complex.star_def,
    Complex.normSq_conj] at h0 h1
  simpa [sourceRadiusSq, overlapFrobeniusSq, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, add_mul] using add_le_add h0 h1

theorem overlapOperatorNorm_sq_le_frobenius (K : SourceOverlapMatrix) :
    overlapOperatorNorm K ^ 2 ≤ overlapFrobeniusSq K := by
  have hF := overlapFrobeniusSq_nonneg K
  have h : overlapOperatorNorm K ≤ Real.sqrt (overlapFrobeniusSq K) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro v
    have hh := sourceRadiusSq_mulVec_le_frobenius K (ofLp v)
    rw [sourceRadiusSq_eq_norm_sq, sourceRadiusSq_eq_norm_sq] at hh
    simp only [toLp_ofLp] at hh
    change ‖toLp 2 (K *ᵥ ofLp v)‖ ≤ Real.sqrt (overlapFrobeniusSq K) * ‖v‖
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg v))).mp
    rw [mul_pow, Real.sq_sqrt hF]
    exact hh
  nlinarith [Real.sq_sqrt hF, overlapOperatorNorm_nonneg K,
    Real.sqrt_nonneg (overlapFrobeniusSq K)]

def overlapColumnEnergy (K : SourceOverlapMatrix) (j : Fin 2) : ℝ :=
  Complex.normSq (K 0 j) + Complex.normSq (K 1 j)

def overlapColumnCross (K : SourceOverlapMatrix) : ℂ :=
  star (K 0 0) * K 0 1 + star (K 1 0) * K 1 1

theorem overlapColumnEnergy_le (K : SourceOverlapMatrix) (j : Fin 2) :
    overlapColumnEnergy K j ≤ overlapOperatorNorm K ^ 2 := by
  have h := sourceRadiusSq_mulVec_le K (Pi.single j 1)
  fin_cases j <;> simpa [overlapColumnEnergy, sourceRadiusSq, Matrix.mulVec_single] using h

theorem overlapDeterminant_columns (K : SourceOverlapMatrix) :
    overlapDeterminant K =
      (1 - overlapColumnEnergy K 0) * (1 - overlapColumnEnergy K 1) -
        Complex.normSq (overlapColumnCross K) := by
  simp [overlapDeterminant, overlapColumnEnergy, overlapColumnCross, Matrix.det_fin_two,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem overlapDeterminant_pos {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1) :
    0 < overlapDeterminant K := by
  have hρ := overlapOperatorNorm_nonneg K
  have hρ2 : overlapOperatorNorm K ^ 2 < 1 := by nlinarith
  have hA : 0 < 1 - overlapColumnEnergy K 0 := by
    have h := overlapColumnEnergy_le K 0
    linarith
  let v : Fin 2 → ℂ := ![overlapColumnCross K, (1 - overlapColumnEnergy K 0 : ℝ)]
  have he : sourceRadiusSq v - sourceRadiusSq (K *ᵥ v) =
      (1 - overlapColumnEnergy K 0) * overlapDeterminant K := by
    simp [v, sourceRadiusSq, overlapDeterminant, overlapColumnEnergy, overlapColumnCross,
      Matrix.det_fin_two, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.normSq_apply,
      Complex.mul_re, Complex.mul_im]
    ring
  have hv : 0 < sourceRadiusSq v := by
    have hn := Complex.normSq_nonneg (overlapColumnCross K)
    simp only [v, sourceRadiusSq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Complex.normSq_ofReal]
    nlinarith
  have h := sourceRadiusSq_mulVec_le K v
  have hgap := mul_pos (sub_pos.mpr hρ2) hv
  have hp : 0 < (1 - overlapColumnEnergy K 0) * overlapDeterminant K := by
    nlinarith [he]
  exact (mul_pos_iff.mp hp).resolve_right (by intro hh; linarith [hh.1]) |>.2

end ConeMatrixBounds

end NLA.FR05
