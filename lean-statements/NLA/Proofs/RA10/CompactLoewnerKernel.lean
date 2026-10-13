import NLA.Proofs.RA10.RidgeScalar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! A finite-measure formulation of the positive Löwner representation.
The endpoint at parameter zero is defined as the constant atom, including at
x = 0. This preserves f(0) and the selected zero eigenspaces in RA-10.
No existence theorem for the representing measure is asserted here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory

namespace NLA.Proofs.RA10

abbrev LoewnerParameter := Set.Icc (0 : ℝ) 1

/-- The normalized harmonic atom, with both endpoints retained. -/
noncomputable def loewnerAtom (t : LoewnerParameter) (x : ℝ) : ℝ :=
  if (t : ℝ) = 0 then 1 else x / ((t : ℝ) + (1 - (t : ℝ)) * x)

theorem loewnerAtom_zero (x : ℝ) : loewnerAtom ⟨0, by norm_num⟩ x = 1 := by
  simp [loewnerAtom]

theorem loewnerAtom_one (x : ℝ) : loewnerAtom ⟨1, by norm_num⟩ x = x := by
  simp [loewnerAtom]

theorem loewnerAtom_at_one (t : LoewnerParameter) : loewnerAtom t 1 = 1 := by
  simp [loewnerAtom]

theorem loewnerAtom_eq_scaled_ridge (t : LoewnerParameter)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) (x : ℝ) :
    loewnerAtom t x = (1 - (t : ℝ))⁻¹ * ridgeAtom ((t : ℝ) / (1 - (t : ℝ))) x := by
  rw [loewnerAtom, if_neg ht0.ne']
  unfold ridgeAtom
  have hc : 1 - (t : ℝ) ≠ 0 := sub_ne_zero.mpr (ne_of_gt ht1)
  have hd : (t : ℝ) / (1 - (t : ℝ)) + x =
      ((t : ℝ) + (1 - (t : ℝ)) * x) / (1 - (t : ℝ)) := by
    field_simp
  rw [hd, div_div_eq_mul_div]
  calc
    _ = ((1 - (t : ℝ))⁻¹ * (1 - (t : ℝ))) *
        (x / ((t : ℝ) + (1 - (t : ℝ)) * x)) := by rw [inv_mul_cancel₀ hc, one_mul]
    _ = _ := by ring

theorem loewnerAtom_nonneg (t : LoewnerParameter) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ loewnerAtom t x := by
  unfold loewnerAtom
  split_ifs
  · norm_num
  · exact div_nonneg hx (add_nonneg t.property.1
      (mul_nonneg (sub_nonneg.mpr t.property.2) hx))

/-- Uniform domination is independent of the parameter, including its endpoints. -/
theorem loewnerAtom_le_max (t : LoewnerParameter) {x : ℝ} (hx : 0 ≤ x) :
    loewnerAtom t x ≤ max 1 x := by
  unfold loewnerAtom
  split_ifs with ht
  · exact le_max_left _ _
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hden : 0 < (t : ℝ) + (1 - (t : ℝ)) * x :=
      add_pos_of_pos_of_nonneg htpos (mul_nonneg (sub_nonneg.mpr t.property.2) hx)
    rw [div_le_iff₀ hden]
    by_cases hx1 : x ≤ 1
    · rw [max_eq_left hx1]
      nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr hx1)]
    · rw [max_eq_right (by linarith)]
      have : 1 ≤ (t : ℝ) + (1 - (t : ℝ)) * x := by
        nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2) (show 0 ≤ x - 1 by linarith)]
      nlinarith

theorem loewnerAtom_measurable (x : ℝ) : Measurable (fun t => loewnerAtom t x) := by
  unfold loewnerAtom
  exact Measurable.ite (measurableSet_eq_fun measurable_subtype_coe measurable_const)
    measurable_const (measurable_const.div
      (measurable_subtype_coe.add ((measurable_const.sub measurable_subtype_coe).mul
        measurable_const)))

theorem loewnerAtom_integrable (μ : Measure LoewnerParameter) [IsFiniteMeasure μ]
    {x : ℝ} (hx : 0 ≤ x) : Integrable (fun t => loewnerAtom t x) μ := by
  apply Integrable.mono' (integrable_const (max 1 x))
    (loewnerAtom_measurable x).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (loewnerAtom_nonneg t hx)] using
      loewnerAtom_le_max t hx

/-- Internal representation predicate. Its existence for the frozen
`AdmissibleFunction` is proved in `OperatorMonotoneRepresentation`. -/
def HasCompactLoewnerRepresentation (f : ℝ → ℝ) : Prop :=
  ∃ μ : Measure LoewnerParameter, IsFiniteMeasure μ ∧
    ∀ x : ℝ, 0 ≤ x → f x = ∫ t, loewnerAtom t x ∂μ

#assert_trust kernel loewnerAtom_zero
#assert_trust kernel loewnerAtom_one
#assert_trust kernel loewnerAtom_at_one
#assert_trust kernel loewnerAtom_eq_scaled_ridge
#assert_trust kernel loewnerAtom_nonneg
#assert_trust kernel loewnerAtom_le_max
#assert_trust kernel loewnerAtom_measurable
#assert_trust kernel loewnerAtom_integrable
#print axioms loewnerAtom_integrable

end NLA.Proofs.RA10
