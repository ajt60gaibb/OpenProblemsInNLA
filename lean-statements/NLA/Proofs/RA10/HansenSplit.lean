import NLA.Proofs.RA10.HarmonicExtremePoints
import NLA.Proofs.RA10.OperatorMonotoneDifferentiability
import NLA.Proofs.RA10.BendatSherman
import Mathlib.Analysis.Calculus.DSlope

/-! Explicit candidates for the analytic Hansen split.
For x ≠ 1 they are x(f(x)-1)/(x-1) and (x-f(x))/(x-1).
Their signs, sum, algebraic relation, continuity and all-size matrix
monotonicity are proved here. Bendat–Sherman and order reversal under inversion
provide both pieces, including their removable values at one. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Set Filter

namespace NLA.Proofs.RA10

noncomputable def hansenLeft (g : PositiveArgument → ℝ) (x : ℝ) : ℝ :=
  x * dslope (positiveProfileExtension g) 1 x

noncomputable def hansenRight (g : PositiveArgument → ℝ) (x : ℝ) : ℝ :=
  1 - dslope (positiveProfileExtension g) 1 x

theorem normalizedProfile_dslope_relation {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) :
    ((x : ℝ) - 1) * dslope (positiveProfileExtension g) 1 x = g x - 1 := by
  have h := sub_smul_dslope (positiveProfileExtension g) 1 (x : ℝ)
  have h1 : positiveProfileExtension g 1 = 1 := by
    simpa only [positiveProfileExtension, dif_pos zero_lt_one] using
      normalizedAdmissibleCompactClass_at_one hg
  simpa only [smul_eq_mul, positiveProfileExtension_apply, h1] using h

theorem normalizedProfile_dslope_bounds_of_ne_one {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) (hx1 : (x : ℝ) ≠ 1) :
    dslope (positiveProfileExtension g) 1 x ∈ Set.Icc (0 : ℝ) 1 := by
  have h := normalizedProfile_dslope_relation hg x
  have hb := normalizedAdmissibleCompactClass_bounds hg x
  rcases lt_or_gt_of_ne hx1 with hx | hx
  · rw [min_eq_right hx.le, max_eq_left hx.le] at hb
    constructor
    · by_contra hs
      have hs' : dslope (positiveProfileExtension g) 1 x < 0 := lt_of_not_ge hs
      have hp := mul_pos_of_neg_of_neg (sub_neg.mpr hx) hs'
      linarith
    · by_contra hs
      have hs' : 1 < dslope (positiveProfileExtension g) 1 x := lt_of_not_ge hs
      have hp := mul_neg_of_neg_of_pos (sub_neg.mpr hx) (sub_pos.mpr hs')
      nlinarith
  · rw [min_eq_left hx.le, max_eq_right hx.le] at hb
    constructor
    · by_contra hs
      have hs' : dslope (positiveProfileExtension g) 1 x < 0 := lt_of_not_ge hs
      have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hx) hs'
      linarith
    · by_contra hs
      have hs' : 1 < dslope (positiveProfileExtension g) 1 x := lt_of_not_ge hs
      have hp := mul_pos (sub_pos.mpr hx) (sub_pos.mpr hs')
      nlinarith

/-- The derivative is genuine: automatic differentiability on the positive
half-line has already been established independently of the Hansen split. -/
theorem normalizedProfile_deriv_bounds {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    deriv (positiveProfileExtension g) 1 ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := normalizedProfile_differentiableAt hg zero_lt_one
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hs : Tendsto s atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimx : Tendsto (fun n => 1 + s n) atTop (nhds (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hs :
      Tendsto (fun n => 1 + s n) atTop (nhds ((1 : ℝ) + 0)))
  have hlim := (continuousAt_dslope_same.mpr hd).tendsto.comp hlimx
  simp only [Function.comp_def, dslope_same] at hlim
  have hb (n : ℕ) : dslope (positiveProfileExtension g) 1 (1 + s n) ∈ Set.Icc (0 : ℝ) 1 :=
    normalizedProfile_dslope_bounds_of_ne_one hg
      ⟨1 + s n, add_pos zero_lt_one (hspos n)⟩ (by linarith [hspos n])
  exact ⟨ge_of_tendsto hlim (Eventually.of_forall fun n => (hb n).1),
    le_of_tendsto hlim (Eventually.of_forall fun n => (hb n).2)⟩

theorem normalizedProfile_dslope_bounds {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) :
    dslope (positiveProfileExtension g) 1 x ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hx : (x : ℝ) = 1
  · rw [hx, dslope_same]
    exact normalizedProfile_deriv_bounds hg
  · exact normalizedProfile_dslope_bounds_of_ne_one hg x hx

theorem hansenLeft_nonneg {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) {x : ℝ} (hx : 0 < x) :
    0 ≤ hansenLeft g x :=
  mul_nonneg hx.le (normalizedProfile_dslope_bounds hg ⟨x, hx⟩).1

theorem hansenRight_nonneg {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) {x : ℝ} (hx : 0 < x) :
    0 ≤ hansenRight g x :=
  sub_nonneg.mpr (normalizedProfile_dslope_bounds hg ⟨x, hx⟩).2

theorem hansenLeft_add_right {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) :
    hansenLeft g x + hansenRight g x = g x := by
  have h := normalizedProfile_dslope_relation hg x
  dsimp [hansenLeft, hansenRight]
  nlinarith

theorem hansenLeft_relation {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) (x : PositiveArgument) :
    hansenLeft g x * ((x : ℝ) - 1) = (x : ℝ) * (g x - 1) := by
  have h := congrArg (fun r : ℝ => (x : ℝ) * r) (normalizedProfile_dslope_relation hg x)
  dsimp [hansenLeft]
  nlinarith [h]

theorem hansenSplit_continuousOn {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    ContinuousOn (hansenLeft g) (Set.Ioi 0) ∧ ContinuousOn (hansenRight g) (Set.Ioi 0) := by
  have hc := (continuousOn_dslope (isOpen_Ioi.mem_nhds (show (0 : ℝ) < 1 by norm_num))).mpr
    ⟨normalizedAdmissibleCompactClass_continuousOn hg,
      normalizedProfile_differentiableAt hg zero_lt_one⟩
  exact ⟨continuousOn_id.mul hc, continuousOn_const.sub hc⟩

theorem hansenRight_operatorMonotone {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    OperatorMonotoneOnPositive (hansenRight g) := by
  have hm := operatorMonotone_neg_dslope
    (normalizedAdmissibleCompactClass_operatorMonotone hg)
    (normalizedAdmissibleCompactClass_continuousOn hg)
    (fun _ hx => normalizedProfile_differentiableAt hg hx) zero_lt_one
  change OperatorMonotoneOnPositive (fun x => 1 - dslope (positiveProfileExtension g) 1 x)
  simpa only [sub_eq_add_neg] using operatorMonotoneOnPositive_const_add hm 1

theorem hansenLeft_operatorMonotone {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    OperatorMonotoneOnPositive (hansenLeft g) := by
  let f := positiveProfileExtension g
  have hc : ContinuousOn (fun x : ℝ => -f x⁻¹) (Set.Ioi 0) := by
    have hi : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) :=
      continuousOn_id.inv₀ (fun x hx => ne_of_gt hx)
    have hmap : Set.MapsTo (fun x : ℝ => x⁻¹) (Set.Ioi 0) (Set.Ioi 0) := by
      intro x hx
      change 0 < x⁻¹
      exact inv_pos.mpr hx
    exact ((normalizedAdmissibleCompactClass_continuousOn hg).comp hi hmap).neg
  have hd (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ (fun y => -f y⁻¹) x :=
    ((normalizedProfile_differentiableAt hg (inv_pos.mpr hx)).comp x
      (differentiableAt_inv (ne_of_gt hx))).neg
  have hm := operatorMonotone_neg_inverse
    (operatorMonotone_neg_dslope
      (operatorMonotone_neg_inverse (normalizedAdmissibleCompactClass_operatorMonotone hg))
      hc hd zero_lt_one)
  apply operatorMonotoneOnPositive_congr hm
  intro x hx
  simpa only [neg_neg, hansenLeft] using real_dslope_neg_inverse_at_one
    (normalizedProfile_differentiableAt hg zero_lt_one) (ne_of_gt hx)

/-- Internal assembly from the two monotonicity facts. The unconditional
caller `hasNonnegativeHansenSplit` discharges both below. -/
theorem hasNonnegativeHansenSplit_of_analytic_properties {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass)
    (hleft : OperatorMonotoneOnPositive (hansenLeft g))
    (hright : OperatorMonotoneOnPositive (hansenRight g)) : HasNonnegativeHansenSplit g := by
  have hc := hansenSplit_continuousOn hg
  exact ⟨hansenLeft g, hansenRight g,
    ⟨hc.1, fun _ hx => hansenLeft_nonneg hg hx, hleft⟩,
    ⟨hc.2, fun _ hx => hansenRight_nonneg hg hx, hright⟩,
    hansenLeft_add_right hg, hansenLeft_relation hg⟩

theorem extreme_eq_loewnerProfile_of_analytic_properties {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass.extremePoints ℝ)
    (hleft : OperatorMonotoneOnPositive (hansenLeft g))
    (hright : OperatorMonotoneOnPositive (hansenRight g)) :
    ∃ t : LoewnerParameter, g = loewnerProfile t :=
  extreme_eq_loewnerProfile_of_hansenSplit hg
    (hasNonnegativeHansenSplit_of_analytic_properties hg.1 hleft hright)

theorem hasNonnegativeHansenSplit {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) : HasNonnegativeHansenSplit g :=
  hasNonnegativeHansenSplit_of_analytic_properties hg
    (hansenLeft_operatorMonotone hg) (hansenRight_operatorMonotone hg)

theorem extreme_eq_loewnerProfile {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass.extremePoints ℝ) :
    ∃ t : LoewnerParameter, g = loewnerProfile t :=
  extreme_eq_loewnerProfile_of_hansenSplit hg (hasNonnegativeHansenSplit hg.1)

#assert_trust kernel normalizedProfile_dslope_relation
#assert_trust kernel normalizedProfile_dslope_bounds_of_ne_one
#assert_trust kernel normalizedProfile_deriv_bounds
#assert_trust kernel normalizedProfile_dslope_bounds
#assert_trust kernel hansenLeft_nonneg
#assert_trust kernel hansenRight_nonneg
#assert_trust kernel hansenLeft_add_right
#assert_trust kernel hansenLeft_relation
#assert_trust kernel hansenSplit_continuousOn
#assert_trust kernel hansenRight_operatorMonotone
#assert_trust kernel hansenLeft_operatorMonotone
#assert_trust kernel hasNonnegativeHansenSplit_of_analytic_properties
#assert_trust kernel extreme_eq_loewnerProfile_of_analytic_properties
#assert_trust kernel hasNonnegativeHansenSplit
#assert_trust kernel extreme_eq_loewnerProfile
#print axioms extreme_eq_loewnerProfile

end NLA.Proofs.RA10
