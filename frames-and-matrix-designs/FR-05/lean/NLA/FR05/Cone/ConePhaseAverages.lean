import NLA.FR05.Cone.ConeSchur

/-!
# Cone phase averages, moments, and Gaussian ratios

The sections develop `ConePhaseAverages`, `ConeMomentBound`, `ConeGaussianRatio`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section ConePhaseAverages

open MeasureTheory Complex Real Matrix
open scoped ENNReal

def conePairBase (K : SourceOverlapMatrix) (t s : ℝ) (p : ConePhase × ConePhase) : ℝ :=
  (coneSchurU (coneRotatedOverlap K t s p.1 p.2))⁻¹

def conePairFirst (K : SourceOverlapMatrix) (t s : ℝ) (p : ConePhase × ConePhase) : ℝ :=
  Complex.normSq (coneRotatedOverlap K t s p.1 p.2 0 1) * conePairBase K t s p ^ 2

def conePairSecond (K : SourceOverlapMatrix) (t s : ℝ) (p : ConePhase × ConePhase) : ℝ :=
  Complex.normSq (coneRotatedOverlap K t s p.1 p.2 1 0) * conePairBase K t s p ^ 2

theorem conePair_u_pos {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) (p : ConePhase × ConePhase) :
    0 < coneSchurU (coneRotatedOverlap K t s p.1 p.2) :=
  coneSchurU_pos (lt_of_le_of_lt (coneRotatedOverlap_norm_le ht hs K p.1 p.2) hK)

theorem continuous_conePairBase {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    Continuous (conePairBase K t s) := by
  apply Continuous.inv₀
  · unfold coneSchurU
    fun_prop
  · exact fun p ↦ (conePair_u_pos hK ht hs p).ne'

theorem continuous_conePairFirst {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    Continuous (conePairFirst K t s) := by
  unfold conePairFirst
  apply Continuous.mul _ ((continuous_conePairBase hK ht hs).pow 2)
  fun_prop

theorem continuous_conePairSecond {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    Continuous (conePairSecond K t s) := by
  unfold conePairSecond
  apply Continuous.mul _ ((continuous_conePairBase hK ht hs).pow 2)
  fun_prop

theorem conePairBase_apply (K : SourceOverlapMatrix) (t s : ℝ) (φ ψ : ConePhase) :
    conePairBase K t s (φ, ψ) =
      (1 - Complex.normSq (coneInner (coneNormal t (conePhasePoint φ)) (coneImage K s ψ)))⁻¹ := by
  rw [conePairBase, coneSchurU, coneRotatedOverlap_apply]
  rfl

theorem coneBaseIntegral_eq_double {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| < 1) (hs : |s| ≤ 1) :
    coneBaseIntegral K t s =
      ∫ ψ, ∫ φ, conePairBase K t s (φ, ψ) ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  unfold coneBaseIntegral
  apply integral_congr_ae
  filter_upwards with ψ
  simp_rw [conePairBase_apply]
  exact (integral_coneNormal_inv ht (coneImage_energy_lt_one hs hK ψ)).symm

theorem conePairBase_adjoint (K : SourceOverlapMatrix) (t s : ℝ) (φ ψ : ConePhase) :
    conePairBase Kᴴ s t (ψ, φ) = conePairBase K t s (φ, ψ) := by
  simp [conePairBase, ← coneRotatedOverlap_adjoint, coneSchurU, Matrix.conjTranspose_apply]

theorem conePairSecond_adjoint (K : SourceOverlapMatrix) (t s : ℝ) (φ ψ : ConePhase) :
    conePairFirst Kᴴ s t (ψ, φ) = conePairSecond K t s (φ, ψ) := by
  simp [conePairFirst, conePairSecond, ← coneRotatedOverlap_adjoint,
    conePairBase_adjoint, Matrix.conjTranspose_apply]

theorem coneBaseIntegral_adjoint {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| < 1) (hs : |s| < 1) :
    coneBaseIntegral Kᴴ s t = coneBaseIntegral K t s := by
  have hK' : overlapOperatorNorm Kᴴ < 1 := by rwa [overlapOperatorNorm_conjTranspose]
  rw [coneBaseIntegral_eq_double hK' hs ht.le, coneBaseIntegral_eq_double hK ht hs.le]
  simp_rw [conePairBase_adjoint]
  exact integral_integral_swap
    ((continuous_conePairBase hK ht.le hs.le).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

theorem integral_conePairFirst {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| < 1) (hs : |s| ≤ 1) (ψ : ConePhase) :
    (∫ φ, conePairFirst K t s (φ, ψ) ∂AddCircle.haarAddCircle) =
      conePhaseJ t (coneImage K s ψ) *
        (1 - (1 - sourceRadiusSq (coneImage K s ψ)) * conePhaseU t (coneImage K s ψ) /
          conePhaseR t (coneImage K s ψ) ^ 2) := by
  have he (φ : ConePhase) : coneRotatedOverlap K t s φ ψ 0 1 =
      coneInner (coneDirection t (conePhasePoint φ)) (coneImage K s ψ) := by
    rw [coneRotatedOverlap_apply]
    rfl
  simp only [conePairFirst, conePairBase_apply, he]
  simpa only [div_eq_mul_inv, inv_pow] using
    integral_cone_radial_correction ht (coneImage_energy_lt_one hs hK ψ)

theorem integral_conePairFirst_lower {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    (3 / 64 * overlapOperatorNorm K ^ 2 - 2 * t ^ 2) * coneBaseIntegral K t s ≤
      ∫ ψ, ∫ φ, conePairFirst K t s (φ, ψ)
        ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hs' : |s| ≤ 1 := le_trans hs (by norm_num)
  have hJ := continuous_conePhaseJ_image ht' hs' hK
  have hx : Continuous (fun ψ ↦ sourceRadiusSq (coneImage K s ψ)) := by
    unfold sourceRadiusSq
    fun_prop
  have hiJ := hJ.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hixJ : Integrable (fun ψ ↦ sourceRadiusSq (coneImage K s ψ) * conePhaseJ t (coneImage K s ψ))
      AddCircle.haarAddCircle :=
    (hx.mul hJ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp := (continuous_conePairFirst hK ht'.le hs').integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hmono := integral_mono ((hixJ.const_mul (3 / 8)).sub (hiJ.const_mul (2 * t ^ 2)))
    hp.integral_prod_right (fun ψ ↦ ?_)
  · simp only [Pi.sub_apply] at hmono
    rw [integral_sub (hixJ.const_mul _) (hiJ.const_mul _), integral_const_mul,
      integral_const_mul] at hmono
    have hweight := coneBaseIntegral_weighted_lower hK ht hs
    change (3 / 8) * _ - 2 * t ^ 2 * coneBaseIntegral K t s ≤ _ at hmono
    nlinarith
  · simp only [Pi.sub_apply]
    rw [integral_conePairFirst hK ht' hs' ψ]
    have h := mul_le_mul_of_nonneg_right
      (cone_radial_correction_pointwise ht (coneImage_energy_lt_one hs' hK ψ))
      (le_trans zero_le_one (conePhaseJ_ge_one ht' (coneImage_energy_lt_one hs' hK ψ)))
    nlinarith only [h]

theorem integral_conePairSecond_lower {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    (3 / 64 * overlapOperatorNorm K ^ 2 - 2 * s ^ 2) * coneBaseIntegral K t s ≤
      ∫ ψ, ∫ φ, conePairSecond K t s (φ, ψ)
        ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hs' : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hK' : overlapOperatorNorm Kᴴ < 1 := by rwa [overlapOperatorNorm_conjTranspose]
  have h := integral_conePairFirst_lower hK' hs ht
  rw [overlapOperatorNorm_conjTranspose, coneBaseIntegral_adjoint hK ht' hs'] at h
  simp_rw [conePairSecond_adjoint] at h
  have hp := (continuous_conePairSecond hK ht'.le hs'.le).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  rwa [integral_integral_swap (f := fun φ ψ ↦ conePairSecond K t s (φ, ψ)) hp] at h

end ConePhaseAverages

section ConeMomentBound

open MeasureTheory Complex Real Matrix
open scoped ENNReal

def coneRayMoment (L : SourceOverlapMatrix) : ℝ :=
  ((1 - sourceEta) ^ 2 +
    sourceEta * (1 - sourceEta) * (coneSchurFirst L + coneSchurSecond L) +
    sourceEta ^ 2 * (coneSchurFirst L * coneSchurSecond L + Complex.normSq (coneSchurCross L))) /
      coneSchurU L

def conePairQuadratic (K : SourceOverlapMatrix) (t s : ℝ) (p : ConePhase × ConePhase) : ℝ :=
  let L := coneRotatedOverlap K t s p.1 p.2
  (coneSchurFirst L * coneSchurSecond L + Complex.normSq (coneSchurCross L)) / coneSchurU L

def coneMomentCorrelation (K : SourceOverlapMatrix) (t s : ℝ) : ℝ :=
  ∫ p, coneRayMoment (coneRotatedOverlap K t s p.1 p.2)
    ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle

theorem continuous_conePairQuadratic {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    Continuous (conePairQuadratic K t s) := by
  have hu (p : ConePhase × ConePhase) : coneSchurU (coneRotatedOverlap K t s p.1 p.2) ≠ 0 :=
    (conePair_u_pos hK ht hs p).ne'
  have huc (p : ConePhase × ConePhase) :
      (coneSchurU (coneRotatedOverlap K t s p.1 p.2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hu p)
  have hU : Continuous coneSchurU := by unfold coneSchurU; fun_prop
  unfold conePairQuadratic coneSchurFirst coneSchurSecond coneSchurCross
  dsimp only
  fun_prop (disch := first | exact hu _ | exact huc _)

theorem coneRayMoment_decomposition (K : SourceOverlapMatrix) (t s : ℝ)
    (p : ConePhase × ConePhase) (hu : coneSchurU (coneRotatedOverlap K t s p.1 p.2) ≠ 0) :
    coneRayMoment (coneRotatedOverlap K t s p.1 p.2) =
      conePairBase K t s p -
        sourceEta * (1 - sourceEta) * (conePairFirst K t s p + conePairSecond K t s p) +
        sourceEta ^ 2 * (conePairQuadratic K t s p - conePairBase K t s p) := by
  unfold coneRayMoment conePairBase conePairFirst conePairSecond conePairQuadratic
  unfold conePairBase
  unfold coneSchurFirst coneSchurSecond
  field_simp [hu]
  ring

theorem continuous_coneRayMoment_pair {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) :
    Continuous (fun p : ConePhase × ConePhase ↦ coneRayMoment (coneRotatedOverlap K t s p.1 p.2)) := by
  have he := funext (fun p ↦ coneRayMoment_decomposition K t s p (conePair_u_pos hK ht hs p).ne')
  rw [he]
  exact ((continuous_conePairBase hK ht hs).sub
    (((continuous_conePairFirst hK ht hs).add (continuous_conePairSecond hK ht hs)).const_mul _)).add
      (((continuous_conePairQuadratic hK ht hs).sub (continuous_conePairBase hK ht hs)).const_mul _)

theorem coneBaseIntegral_eq_prod {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| < 1) (hs : |s| ≤ 1) :
    coneBaseIntegral K t s =
      ∫ p, conePairBase K t s p ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
  rw [integral_prod_symm]
  · exact coneBaseIntegral_eq_double hK ht hs
  · exact (continuous_conePairBase hK ht.le hs).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem conePair_correction_bound {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    (3 / 32 * overlapOperatorNorm K ^ 2 - 2 * (t ^ 2 + s ^ 2)) * coneBaseIntegral K t s ≤
      ∫ p, (conePairFirst K t s p + conePairSecond K t s p)
        ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle := by
  have ht' : |t| ≤ 1 := le_trans ht (by norm_num)
  have hs' : |s| ≤ 1 := le_trans hs (by norm_num)
  have hif := (continuous_conePairFirst hK ht' hs').integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have his := (continuous_conePairSecond hK ht' hs').integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  rw [integral_add hif his, integral_prod_symm _ hif, integral_prod_symm _ his]
  have hf := integral_conePairFirst_lower hK ht hs
  have hs := integral_conePairSecond_lower hK ht hs
  nlinarith

theorem conePair_quadratic_bound {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1) (p : ConePhase × ConePhase) :
    conePairQuadratic K t s p - conePairBase K t s p ≤
      4 * overlapOperatorNorm K ^ 2 * conePairBase K t s p := by
  let L := coneRotatedOverlap K t s p.1 p.2
  have hnorm : overlapOperatorNorm L ≤ overlapOperatorNorm K := coneRotatedOverlap_norm_le ht hs K p.1 p.2
  have hL : overlapOperatorNorm L < 1 := lt_of_le_of_lt hnorm hK
  have h := coneSchur_quadratic_bound hL
  have hr : overlapOperatorNorm L ^ 2 ≤ overlapOperatorNorm K ^ 2 :=
    (sq_le_sq₀ (overlapOperatorNorm_nonneg L) (overlapOperatorNorm_nonneg K)).mpr hnorm
  have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4))
    (inv_nonneg.mpr (coneSchurU_pos hL).le)
  change _ ≤ _ * (coneSchurU L)⁻¹
  have he : conePairQuadratic K t s p - conePairBase K t s p =
      (coneSchurFirst L * coneSchurSecond L + Complex.normSq (coneSchurCross L) - 1) / coneSchurU L := by
    unfold conePairQuadratic conePairBase
    change (_ / coneSchurU L) - (coneSchurU L)⁻¹ = _
    rw [sub_div, one_div]
  rw [he]
  exact le_trans h (by simpa only [div_eq_mul_inv] using h')

theorem coneMomentCorrelation_decomposition {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K < 1) {t s : ℝ} (ht : |t| < 1) (hs : |s| ≤ 1) :
    coneMomentCorrelation K t s =
      coneBaseIntegral K t s -
        sourceEta * (1 - sourceEta) *
          (∫ p, conePairFirst K t s p + conePairSecond K t s p
            ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) +
        sourceEta ^ 2 * ((∫ p, conePairQuadratic K t s p
          ∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) - coneBaseIntegral K t s) := by
  have hiB := (continuous_conePairBase hK ht.le hs).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hiD : Integrable (fun p ↦ conePairFirst K t s p + conePairSecond K t s p)
      (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) :=
    ((continuous_conePairFirst hK ht.le hs).add (continuous_conePairSecond hK ht.le hs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiQ := (continuous_conePairQuadratic hK ht.le hs).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hiBD : Integrable (fun p ↦ conePairBase K t s p -
      sourceEta * (1 - sourceEta) * (conePairFirst K t s p + conePairSecond K t s p))
        (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) := hiB.sub (hiD.const_mul _)
  have hiQB : Integrable (fun p ↦ conePairQuadratic K t s p - conePairBase K t s p)
      (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) := hiQ.sub hiB
  unfold coneMomentCorrelation
  simp_rw [coneRayMoment_decomposition K t s _ (conePair_u_pos hK ht.le hs _).ne']
  rw [integral_add hiBD (hiQB.const_mul _), integral_sub hiB (hiD.const_mul _),
    integral_const_mul, integral_const_mul, integral_sub hiQ hiB, ← coneBaseIntegral_eq_prod hK ht hs]

theorem coneMomentCorrelation_bound {K : SourceOverlapMatrix} (hK : overlapOperatorNorm K < 1)
    {t s : ℝ} (ht : |t| ≤ 1 / 4) (hs : |s| ≤ 1 / 4) :
    coneMomentCorrelation K t s ≤
      Real.exp (t ^ 2 + s ^ 2 - overlapOperatorNorm K ^ 2 / 2000) *
        (Real.sqrt (Real.sqrt (overlapDeterminant K)))⁻¹ := by
  have ht' : |t| < 1 := lt_of_le_of_lt ht (by norm_num)
  have hs' : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  apply cone_radial_exponential_arithmetic (coneBaseIntegral_exp_bound hK ht hs)
  rw [coneMomentCorrelation_decomposition hK ht' hs'.le]
  apply cone_radial_final_arithmetic (le_trans zero_le_one (coneBaseIntegral_ge_one hK ht' hs'.le))
    (conePair_correction_bound hK ht hs)
  have hiB := (continuous_conePairBase hK ht'.le hs'.le).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  have hiQ := (continuous_conePairQuadratic hK ht'.le hs'.le).integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  rw [coneBaseIntegral_eq_prod hK ht' hs'.le, ← integral_sub hiQ hiB, ← integral_const_mul]
  exact integral_mono (hiQ.sub hiB) (hiB.const_mul _) (conePair_quadratic_bound hK ht'.le hs'.le)

end ConeMomentBound

section ConeGaussianRatio

open MeasureTheory Complex Real Matrix
open scoped BigOperators

def overlapResidualMatrix (K : SourceOverlapMatrix) : SourceOverlapMatrix := 1 - Kᴴ * K

/-- Gaussian likelihood ratio for covariance [[I,K],[K*,I]], in conditional coordinates. -/
def overlapGaussianRatio (K : SourceOverlapMatrix) (z w : Fin 2 → ℂ) : ℝ :=
  (overlapDeterminant K)⁻¹ *
    Real.exp (sourceRadiusSq w -
      (coneInner (w - Kᴴ *ᵥ z) ((overlapResidualMatrix K)⁻¹ *ᵥ (w - Kᴴ *ᵥ z))).re)

theorem overlapResidualMatrix_eq (K : SourceOverlapMatrix) :
    overlapResidualMatrix K =
      !![((1 - overlapColumnEnergy K 0 : ℝ) : ℂ), -overlapColumnCross K;
        -star (overlapColumnCross K), ((1 - overlapColumnEnergy K 1 : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [overlapResidualMatrix, overlapColumnEnergy, overlapColumnCross,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.ext_iff, Complex.mul_re, Complex.mul_im] <;> ring_nf
  all_goals simp

theorem overlapResidualMatrix_det (K : SourceOverlapMatrix) :
    (overlapResidualMatrix K).det = (overlapDeterminant K : ℂ) := by
  rw [overlapResidualMatrix_eq, Matrix.det_fin_two, overlapDeterminant_columns]
  simp [Complex.ext_iff, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem coneBasis_unitary {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    (coneBasis t z)ᴴ * coneBasis t z = 1 := by
  obtain ⟨hp, hm⟩ := cone_sqrt_sq ht
  let p : ℂ := Real.sqrt ((1 + t) / 2)
  let m : ℂ := Real.sqrt ((1 - t) / 2)
  have hpstar : star p = p := by simp [p]
  have hmstar : star m = m := by simp [m]
  have hpm : p ^ 2 + m ^ 2 = 1 := by
    dsimp [p, m]
    exact_mod_cast (show Real.sqrt ((1 + t) / 2) ^ 2 + Real.sqrt ((1 - t) / 2) ^ 2 = 1 by linarith)
  have hz' : star z * z = (1 : ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · change star p * p + star (z * m) * (z * m) = 1
    rw [star_mul, hpstar, hmstar]
    linear_combination hpm + m ^ 2 * hz'
  · change star p * m + star (z * m) * (-z * p) = 0
    rw [star_mul, hpstar, hmstar]
    linear_combination -p * m * hz'
  · change star m * p + star (-z * p) * (z * m) = 0
    rw [star_mul, star_neg, hpstar, hmstar]
    linear_combination -p * m * hz'
  · change star m * m + star (-z * p) * (-z * p) = 1
    rw [star_mul, star_neg, hpstar, hmstar]
    linear_combination hpm + p ^ 2 * hz'

theorem coneBasis_unitary_right {t : ℝ} (ht : |t| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    coneBasis t z * (coneBasis t z)ᴴ = 1 :=
  (mul_eq_one_comm).mp (coneBasis_unitary ht hz)

theorem coneInner_adjoint (A : SourceOverlapMatrix) (v w : Fin 2 → ℂ) :
    coneInner (A *ᵥ v) w = coneInner v (Aᴴ *ᵥ w) := by
  simp [coneInner, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  ring

theorem coneInner_unitary (V : SourceOverlapMatrix) (hV : Vᴴ * V = 1)
    (v w : Fin 2 → ℂ) : coneInner (V *ᵥ v) (V *ᵥ w) = coneInner v w := by
  rw [coneInner_adjoint, Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]

theorem coneRotatedOverlap_residualMatrix {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1)
    (K : SourceOverlapMatrix) (φ ψ : ConePhase) :
    overlapResidualMatrix (coneRotatedOverlap K t s φ ψ) =
      (coneBasis s (conePhasePoint ψ))ᴴ * overlapResidualMatrix K * coneBasis s (conePhasePoint ψ) := by
  have hU := coneBasis_unitary_right ht (norm_conePhasePoint φ)
  have hV := coneBasis_unitary hs (norm_conePhasePoint ψ)
  have hUc (X : SourceOverlapMatrix) :
      coneBasis t (conePhasePoint φ) * ((coneBasis t (conePhasePoint φ))ᴴ * X) = X := by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  simp [overlapResidualMatrix, coneRotatedOverlap, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, hUc, Matrix.mul_sub, Matrix.sub_mul, hV]

theorem coneRotatedOverlap_determinant {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1)
    (K : SourceOverlapMatrix) (φ ψ : ConePhase) :
    overlapDeterminant (coneRotatedOverlap K t s φ ψ) = overlapDeterminant K := by
  have h := congrArg Matrix.det (coneRotatedOverlap_residualMatrix ht hs K φ ψ)
  rw [overlapResidualMatrix_det, Matrix.det_mul, Matrix.det_mul,
    overlapResidualMatrix_det] at h
  have hdet := congrArg Matrix.det (coneBasis_unitary hs (norm_conePhasePoint ψ))
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have he : (overlapDeterminant (coneRotatedOverlap K t s φ ψ) : ℂ) =
      (overlapDeterminant K : ℂ) := by
    calc
      _ = _ := h
      _ = (overlapDeterminant K : ℂ) *
          ((coneBasis s (conePhasePoint ψ))ᴴ.det * (coneBasis s (conePhasePoint ψ)).det) := by ring
      _ = _ := by rw [hdet, mul_one]
  exact_mod_cast he

theorem coneRotatedOverlap_residualInverse {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1)
    (K : SourceOverlapMatrix) (φ ψ : ConePhase) :
    (overlapResidualMatrix (coneRotatedOverlap K t s φ ψ))⁻¹ =
      (coneBasis s (conePhasePoint ψ))ᴴ * (overlapResidualMatrix K)⁻¹ * coneBasis s (conePhasePoint ψ) := by
  rw [coneRotatedOverlap_residualMatrix ht hs, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hV := coneBasis_unitary hs (norm_conePhasePoint ψ)
  have hV' := coneBasis_unitary_right hs (norm_conePhasePoint ψ)
  rw [Matrix.inv_eq_left_inv hV, Matrix.inv_eq_left_inv hV']
  simp only [Matrix.mul_assoc]

theorem coneRotatedOverlap_residual {t s : ℝ} (hs : |s| ≤ 1)
    (K : SourceOverlapMatrix) (φ ψ : ConePhase) (z w : Fin 2 → ℂ) :
    coneBasis s (conePhasePoint ψ) *ᵥ w - Kᴴ *ᵥ (coneBasis t (conePhasePoint φ) *ᵥ z) =
      coneBasis s (conePhasePoint ψ) *ᵥ (w - (coneRotatedOverlap K t s φ ψ)ᴴ *ᵥ z) := by
  have hV := coneBasis_unitary_right hs (norm_conePhasePoint ψ)
  have hVc (X : SourceOverlapMatrix) :
      coneBasis s (conePhasePoint ψ) * ((coneBasis s (conePhasePoint ψ))ᴴ * X) = X := by
    rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  simp [coneRotatedOverlap, Matrix.conjTranspose_mul, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, hVc]

theorem overlapGaussianRatio_coneBasis {t s : ℝ} (ht : |t| ≤ 1) (hs : |s| ≤ 1)
    (K : SourceOverlapMatrix) (φ ψ : ConePhase) (z w : Fin 2 → ℂ) :
    overlapGaussianRatio K (coneBasis t (conePhasePoint φ) *ᵥ z)
      (coneBasis s (conePhasePoint ψ) *ᵥ w) =
        overlapGaussianRatio (coneRotatedOverlap K t s φ ψ) z w := by
  rw [overlapGaussianRatio, overlapGaussianRatio, coneRotatedOverlap_determinant ht hs,
    coneBasis_energy hs (norm_conePhasePoint ψ), coneRotatedOverlap_residual hs,
    coneRotatedOverlap_residualInverse ht hs]
  congr 2
  rw [coneInner_adjoint]
  congr 1
  simp only [← Matrix.mulVec_mulVec]

end ConeGaussianRatio

end NLA.FR05
