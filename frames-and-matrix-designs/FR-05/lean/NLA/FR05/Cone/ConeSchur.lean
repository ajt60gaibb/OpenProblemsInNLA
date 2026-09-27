import NLA.FR05.Cone.ConeImageEstimates

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Real Matrix
open scoped BigOperators

namespace NLA.FR05

def coneSchurU (L : SourceOverlapMatrix) : ℝ := 1 - Complex.normSq (L 1 1)

def coneSchurFirst (L : SourceOverlapMatrix) : ℝ :=
  1 - Complex.normSq (L 0 1) / coneSchurU L

def coneSchurSecond (L : SourceOverlapMatrix) : ℝ :=
  1 - Complex.normSq (L 1 0) / coneSchurU L

def coneSchurCross (L : SourceOverlapMatrix) : ℂ :=
  L 0 0 + L 0 1 * star (L 1 1) * L 1 0 / (coneSchurU L : ℂ)

theorem overlap_entry_normSq_le (L : SourceOverlapMatrix) (i j : Fin 2) :
    Complex.normSq (L i j) ≤ overlapOperatorNorm L ^ 2 := by
  have hc := overlapColumnEnergy_le L j
  have h0 := Complex.normSq_nonneg (L 0 j)
  have h1 := Complex.normSq_nonneg (L 1 j)
  unfold overlapColumnEnergy at hc
  fin_cases i <;> dsimp <;> linarith

theorem overlap_entry_norm_le (L : SourceOverlapMatrix) (i j : Fin 2) :
    ‖L i j‖ ≤ overlapOperatorNorm L := by
  have h := overlap_entry_normSq_le L i j
  rw [Complex.normSq_eq_norm_sq] at h
  exact (sq_le_sq₀ (norm_nonneg _) (overlapOperatorNorm_nonneg _)).mp h

theorem coneSchurU_pos {L : SourceOverlapMatrix} (hL : overlapOperatorNorm L < 1) :
    0 < coneSchurU L := by
  have h := overlap_entry_normSq_le L 1 1
  have hρ := overlapOperatorNorm_nonneg L
  unfold coneSchurU
  nlinarith

theorem coneSchurFirst_bounds {L : SourceOverlapMatrix} (hL : overlapOperatorNorm L < 1) :
    0 < coneSchurFirst L ∧ coneSchurFirst L ≤ 1 := by
  have hu := coneSchurU_pos hL
  have h := overlapColumnEnergy_le L 1
  have hρ := overlapOperatorNorm_nonneg L
  unfold overlapColumnEnergy at h
  constructor
  · unfold coneSchurFirst
    have hh : Complex.normSq (L 0 1) / coneSchurU L < 1 := by
      apply (div_lt_one hu).mpr
      unfold coneSchurU
      nlinarith
    linarith
  · unfold coneSchurFirst
    exact sub_le_self _ (div_nonneg (Complex.normSq_nonneg _) hu.le)

theorem coneSchurSecond_bounds {L : SourceOverlapMatrix} (hL : overlapOperatorNorm L < 1) :
    0 < coneSchurSecond L ∧ coneSchurSecond L ≤ 1 := by
  have hL' : overlapOperatorNorm Lᴴ < 1 := by rwa [overlapOperatorNorm_conjTranspose]
  simpa [coneSchurFirst, coneSchurSecond, coneSchurU, Matrix.conjTranspose_apply] using
    coneSchurFirst_bounds hL'

theorem coneSchur_determinant (L : SourceOverlapMatrix) (hu : coneSchurU L ≠ 0) :
    coneSchurFirst L * coneSchurSecond L - Complex.normSq (coneSchurCross L) =
      overlapDeterminant L / coneSchurU L := by
  simp only [coneSchurFirst, coneSchurSecond, coneSchurCross, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  field_simp [hu]
  rw [overlapDeterminant_identity]
  simp [coneSchurU, overlapFrobeniusSq, Matrix.det_fin_two, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem coneSchurCross_normSq_le {L : SourceOverlapMatrix} (hL : overlapOperatorNorm L < 1) :
    Complex.normSq (coneSchurCross L) ≤ coneSchurFirst L * coneSchurSecond L := by
  have h := coneSchur_determinant L (coneSchurU_pos hL).ne'
  have hp := div_pos (overlapDeterminant_pos hL) (coneSchurU_pos hL)
  linarith

theorem coneSchurCross_normSq_le_one {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) : Complex.normSq (coneSchurCross L) ≤ 1 := by
  obtain ⟨hf0, hf1⟩ := coneSchurFirst_bounds hL
  obtain ⟨hs0, hs1⟩ := coneSchurSecond_bounds hL
  have h := coneSchurCross_normSq_le hL
  nlinarith [mul_le_mul hf1 hs1 hs0.le zero_le_one]

theorem coneSchurCross_normSq_le_four {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) :
    Complex.normSq (coneSchurCross L) ≤ 4 * overlapOperatorNorm L ^ 2 := by
  let ρ := overlapOperatorNorm L
  have hρ : 0 ≤ ρ := overlapOperatorNorm_nonneg L
  by_cases hsmall : ρ ≤ 1 / 2
  · have hu := coneSchurU_pos hL
    have hc := overlap_entry_normSq_le L 1 1
    have hden : ρ ^ 2 ≤ coneSchurU L := by
      unfold coneSchurU
      dsimp [ρ] at *
      nlinarith
    have hprod : ‖L 0 1 * star (L 1 1) * L 1 0‖ ≤ ρ ^ 3 := by
      rw [norm_mul, norm_mul, norm_star]
      exact le_trans
        (mul_le_mul (mul_le_mul (overlap_entry_norm_le L 0 1)
          (overlap_entry_norm_le L 1 1) (norm_nonneg _) hρ)
          (overlap_entry_norm_le L 1 0) (norm_nonneg _) (mul_nonneg hρ hρ))
        (by dsimp [ρ]; ring_nf; rfl)
    have hcross : ‖coneSchurCross L‖ ≤ 2 * ρ := by
      calc
        _ ≤ ‖L 0 0‖ + ‖L 0 1 * star (L 1 1) * L 1 0 / (coneSchurU L : ℂ)‖ := norm_add_le _ _
        _ = ‖L 0 0‖ + ‖L 0 1 * star (L 1 1) * L 1 0‖ / coneSchurU L := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
        _ ≤ ρ + ρ ^ 3 / coneSchurU L :=
          add_le_add (overlap_entry_norm_le L 0 0) (div_le_div_of_nonneg_right hprod hu.le)
        _ ≤ 2 * ρ := by
          have hh : ρ ^ 3 / coneSchurU L ≤ ρ := (div_le_iff₀ hu).mpr (by
            nlinarith [mul_le_mul_of_nonneg_left hden hρ])
          linarith
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (coneSchurCross L)]
  · have hlarge : 1 / 2 ≤ ρ := le_of_lt (lt_of_not_ge hsmall)
    have h := coneSchurCross_normSq_le_one hL
    change Complex.normSq (coneSchurCross L) ≤ 4 * ρ ^ 2
    nlinarith

theorem coneSchur_quadratic_bound {L : SourceOverlapMatrix}
    (hL : overlapOperatorNorm L < 1) :
    (coneSchurFirst L * coneSchurSecond L + Complex.normSq (coneSchurCross L) - 1) /
        coneSchurU L ≤ 4 * overlapOperatorNorm L ^ 2 / coneSchurU L := by
  apply div_le_div_of_nonneg_right _ (coneSchurU_pos hL).le
  obtain ⟨hf0, hf1⟩ := coneSchurFirst_bounds hL
  obtain ⟨hs0, hs1⟩ := coneSchurSecond_bounds hL
  have h := coneSchurCross_normSq_le_four hL
  nlinarith [mul_le_mul hf1 hs1 hs0.le zero_le_one]

end NLA.FR05
