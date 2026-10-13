import NLA.Proofs.SP14.FiniteBackgroundDeviationWiener
import NLA.Proofs.SP14.CanonicalFirstWienerSizes
import NLA.Proofs.SP14.NegativeRatioW0
import NLA.Proofs.SP14.ActualNegativeWienerBound

/-!
An actual nonzero two-mode endpoint-contact finite background satisfying the
five first-smallness inequalities for any supplied positive threshold. This
does not construct the later-stage packets or background inverse.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

def twoModeCoeff (ε : ℝ) : Fin 2 → ℝ := fun _ => ε

def twoModeMinusQuot (ε : ℝ) : Fin 2 → ℝ :=
  fun j => if j.val = 1 then ε else 0

def twoModePlusQuot (ε : ℝ) : Fin 2 → ℝ :=
  fun j => if j.val = 0 then ε else 0

private theorem twoModeMinusQuot_factor (ε : ℝ) (s : Circle) :
    negativeLaurent 2 (twoModeCoeff ε) s =
      (1 + (s : ℂ)) * negativeLaurent 2 (twoModeMinusQuot ε) s := by
  have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
  simp [negativeLaurent, twoModeCoeff, twoModeMinusQuot, Fin.sum_univ_two]
  field_simp
  ring

private theorem twoModePlusQuot_factor (ε : ℝ) (s : Circle) :
    positiveLaurent 2 (twoModeCoeff ε) s =
      (1 + (s : ℂ)) * positiveLaurent 2 (twoModePlusQuot ε) s := by
  simp [positiveLaurent, twoModeCoeff, twoModePlusQuot, Fin.sum_univ_two]
  ring

private theorem twoMinus_contact (ε : ℝ) :
    negativeLaurent 2 (twoModeCoeff ε) (-1 : Circle) = 0 := by
  rw [twoModeMinusQuot_factor]
  norm_num

private theorem twoPlus_contact (ε : ℝ) :
    positiveLaurent 2 (twoModeCoeff ε) (-1 : Circle) = 0 := by
  rw [twoModePlusQuot_factor]
  norm_num

private theorem twoMinus_W0 (ε : ℝ) (hε : 0 ≤ ε) :
    wienerSizeAt 0 (negativeLaurent 2 (twoModeCoeff ε)) = 2 * ε := by
  rw [negativeLaurent_W0_eq]
  simp [twoModeCoeff, abs_of_nonneg hε]

private theorem twoPlus_W4 (ε : ℝ) (hε : 0 ≤ ε) :
    wienerSizeAt 4 (positiveLaurent 2 (twoModeCoeff ε)) = 97 * ε := by
  rw [positiveLaurent_W4_eq]
  simp [twoModeCoeff, Fin.sum_univ_two, abs_of_nonneg hε]
  ring

private theorem twoModeMinusQuot_W (ε : ℝ) (hε : 0 ≤ ε) :
    weightedWienerSize (negativeLaurent 2 (twoModeMinusQuot ε)) =
      (3 : ℝ) ^ (9 / 8 : ℝ) * ε := by
  rw [negativeLaurent_wiener_eq]
  simp [finiteNegativeWienerSize, twoModeMinusQuot, Fin.sum_univ_two,
    wienerWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  norm_num

private theorem twoModePlusQuot_W (ε : ℝ) (hε : 0 ≤ ε) :
    weightedWienerSize (positiveLaurent 2 (twoModePlusQuot ε)) =
      (2 : ℝ) ^ (9 / 8 : ℝ) * ε := by
  rw [positiveLaurent_wiener_eq]
  simp [finitePositiveWienerSize, twoModePlusQuot, Fin.sum_univ_two,
    wienerWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  norm_num

private theorem twoMinus_W (ε : ℝ) (hε : 0 ≤ ε) :
    weightedWienerSize (negativeLaurent 2 (twoModeCoeff ε)) =
      ((2 : ℝ) ^ (9 / 8 : ℝ) + (3 : ℝ) ^ (9 / 8 : ℝ)) * ε := by
  rw [negativeLaurent_wiener_eq]
  simp [finiteNegativeWienerSize, twoModeCoeff, Fin.sum_univ_two,
    wienerWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  ring

private theorem twoPlus_W (ε : ℝ) (hε : 0 ≤ ε) :
    weightedWienerSize (positiveLaurent 2 (twoModeCoeff ε)) =
      ((2 : ℝ) ^ (9 / 8 : ℝ) + (3 : ℝ) ^ (9 / 8 : ℝ)) * ε := by
  rw [positiveLaurent_wiener_eq]
  simp [finitePositiveWienerSize, twoModeCoeff, Fin.sum_univ_two,
    wienerWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
  ring

private theorem twoMode_source_bounds (ε : ℝ) (hε : 0 ≤ ε) :
    wienerSizeAt 0 (negativeLaurent 2 (twoModeCoeff ε)) = 2 * ε ∧
    wienerSizeAt 4 (positiveLaurent 2 (twoModeCoeff ε)) = 97 * ε ∧
    wienerSizeAt 0 (negativeRatioExtension 2 (twoModeMinusQuot ε)) ≤
      wienerSizeAt 0 baseExteriorFactor * ε ∧
    weightedWienerSize
        (fun s => baseExteriorFactor s * negativeLaurent 2 (twoModeCoeff ε) s) ≤
      weightedWienerSize regularizedBaseFactor *
        (3 : ℝ) ^ (9 / 8 : ℝ) * ε ∧
    weightedWienerSize
        (fun s : Circle =>
          finiteBackgroundCurve 2 2 (twoModeCoeff ε) (twoModeCoeff ε) s - (s : ℂ)) ≤
      2 * (2 : ℝ) ^ (9 / 8 : ℝ) * weightedWienerSize regularizedBaseFactor *
        (((3 : ℝ) ^ (9 / 8 : ℝ) + (2 : ℝ) ^ (9 / 8 : ℝ)) * ε) +
      (2 : ℝ) ^ (9 / 8 : ℝ) *
        (2 * ((2 : ℝ) ^ (9 / 8 : ℝ) + (3 : ℝ) ^ (9 / 8 : ℝ)) * ε) ^ 2 := by
  refine ⟨twoMinus_W0 ε hε, twoPlus_W4 ε hε, ?_, ?_, ?_⟩
  · have h := negativeRatioExtension_W0_le 2 (twoModeMinusQuot ε)
    convert h using 1
    simp [twoModeMinusQuot, Fin.sum_univ_two, abs_of_nonneg hε]
  · have heq :
        (fun s : Circle => baseExteriorFactor s * negativeLaurent 2 (twoModeCoeff ε) s) =
        (fun s => regularizedBaseFactor s * negativeLaurent 2 (twoModeMinusQuot ε) s) := by
      funext s
      rw [twoModeMinusQuot_factor]
      simp [regularizedBaseFactor]
      ring
    rw [heq]
    have h := weightedWienerSize_mul_negativeLaurent_le
      regularizedBaseFactor continuous_regularizedBaseFactor
      summable_regularizedBaseFactor_wiener 2 (twoModeMinusQuot ε)
    rw [← negativeLaurent_wiener_eq,
      twoModeMinusQuot_W ε hε] at h
    nlinarith [h]
  · have h := (finiteBackgroundCurve_deviation_wiener_of_factors
      2 2 (twoModeCoeff ε) (twoModeCoeff ε)
      (twoModeMinusQuot ε) (twoModePlusQuot ε)
      (twoModeMinusQuot_factor ε) (twoModePlusQuot_factor ε)).2
    rw [twoModeMinusQuot_W ε hε, twoModePlusQuot_W ε hε,
      twoMinus_W ε hε, twoPlus_W ε hε] at h
    convert h using 1 <;> ring

/-- A nonzero first finite background meets all five literal source Wiener
smallness inequalities for any chosen positive threshold. -/
theorem exists_twoMode_firstSmallness (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε : ℝ, 0 < ε ∧
      negativeLaurent 2 (twoModeCoeff ε) (-1 : Circle) = 0 ∧
      positiveLaurent 2 (twoModeCoeff ε) (-1 : Circle) = 0 ∧
      weightedWienerSize
        (fun s : Circle =>
          finiteBackgroundCurve 2 2 (twoModeCoeff ε) (twoModeCoeff ε) s - (s : ℂ)) < γ ∧
      wienerSizeAt 0 (negativeLaurent 2 (twoModeCoeff ε)) < γ ∧
      wienerSizeAt 0 (negativeRatioExtension 2 (twoModeMinusQuot ε)) < γ ∧
      weightedWienerSize
        (fun s => baseExteriorFactor s * negativeLaurent 2 (twoModeCoeff ε) s) < γ ∧
      wienerSizeAt 4 (positiveLaurent 2 (twoModeCoeff ε)) < γ := by
  let w1 : ℝ := (2 : ℝ) ^ (9 / 8 : ℝ)
  let w2 : ℝ := (3 : ℝ) ^ (9 / 8 : ℝ)
  let A : ℝ := weightedWienerSize regularizedBaseFactor
  let C0 : ℝ := wienerSizeAt 0 baseExteriorFactor
  let c : ℝ := w1 + w2
  let linear : ℝ := 2 * w1 * A * (w2 + w1) + 4 * w1 * c ^ 2
  let D : ℝ := 1 + 2 + 97 + C0 + A * w2 + linear
  have hw1 : 0 ≤ w1 := by dsimp [w1]; positivity
  have hw2 : 0 ≤ w2 := by dsimp [w2]; positivity
  have hA : 0 ≤ A := by
    dsimp [A, weightedWienerSize]
    apply tsum_nonneg
    intro k
    exact mul_nonneg (by unfold wienerWeight; positivity) (norm_nonneg _)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0, wienerSizeAt]
    apply tsum_nonneg
    intro k
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hAw2 : 0 ≤ A * w2 := mul_nonneg hA hw2
  have hlin : 0 ≤ linear := by dsimp [linear]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  let ε : ℝ := min 1 (γ / (2 * D))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεγ : ε ≤ γ / (2 * D) := min_le_right _ _
  have hεsq : ε ^ 2 ≤ ε := by
    have hh : 0 ≤ ε * (1 - ε) :=
      mul_nonneg (le_of_lt hε) (sub_nonneg.mpr hε1)
    nlinarith
  have hDε : D * ε < γ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp hεγ
    nlinarith
  have h2D : 2 ≤ D := by dsimp [D]; nlinarith
  have h97D : 97 ≤ D := by dsimp [D]; nlinarith
  have hC0D : C0 ≤ D := by dsimp [D]; nlinarith
  have hAw2D : A * w2 ≤ D := by dsimp [D]; nlinarith
  have hlinD : linear ≤ D := by dsimp [D]; nlinarith
  have hbounds := twoMode_source_bounds ε (le_of_lt hε)
  rcases hbounds with ⟨hminus0, hplus4, hratio, hbase, hcurve⟩
  have hquad : 4 * w1 * c ^ 2 * ε ^ 2 ≤
      4 * w1 * c ^ 2 * ε :=
    mul_le_mul_of_nonneg_left hεsq (by positivity)
  have hcurveD :
      2 * w1 * A * ((w2 + w1) * ε) +
          w1 * (2 * c * ε) ^ 2 ≤ D * ε := by
    have hlinε : linear * ε ≤ D * ε :=
      mul_le_mul_of_nonneg_right hlinD (le_of_lt hε)
    dsimp [linear] at hlinε
    nlinarith [hquad]
  have hminusD : 2 * ε ≤ D * ε :=
    mul_le_mul_of_nonneg_right h2D (le_of_lt hε)
  have hplusD : 97 * ε ≤ D * ε :=
    mul_le_mul_of_nonneg_right h97D (le_of_lt hε)
  have hratioD : C0 * ε ≤ D * ε :=
    mul_le_mul_of_nonneg_right hC0D (le_of_lt hε)
  have hbaseD : A * w2 * ε ≤ D * ε := by
    have hh := mul_le_mul_of_nonneg_right hAw2D (le_of_lt hε)
    nlinarith
  refine ⟨ε, hε, twoMinus_contact ε, twoPlus_contact ε, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [w1, w2, A, c] at hcurveD
    exact lt_of_le_of_lt (hcurve.trans hcurveD) hDε
  · rw [hminus0]
    exact lt_of_le_of_lt hminusD hDε
  · exact lt_of_le_of_lt (hratio.trans hratioD) hDε
  · dsimp [A, w2] at hbaseD
    exact lt_of_le_of_lt (hbase.trans hbaseD) hDε
  · rw [hplus4]
    exact lt_of_le_of_lt hplusD hDε

#assert_trust kernel exists_twoMode_firstSmallness

end NLA.Proofs.SP14
