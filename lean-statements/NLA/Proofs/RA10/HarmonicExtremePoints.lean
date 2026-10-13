import NLA.Proofs.RA10.OperatorMonotonePositiveCone

/-! Extremality arguments for the harmonic representation.
The two endpoint atoms are proved extreme without additional hypotheses.
For an arbitrary extreme point, a nonnegative operator-monotone Hansen split
forces the harmonic formula. Existence of that split is NOT proved here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Set

namespace NLA.Proofs.RA10

private theorem convex_eq_upper_left {a b u v z : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : u ≤ z) (hv : v ≤ z) (heq : a * u + b * v = z) : u = z := by
  by_contra hne
  have huz : u < z := lt_of_le_of_ne hu hne
  nlinarith [mul_pos ha (sub_pos.mpr huz), mul_nonneg hb (sub_nonneg.mpr hv),
    congrArg (fun r : ℝ => r * z) hab]

private theorem convex_eq_lower_left {a b u v z : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : z ≤ u) (hv : z ≤ v) (heq : a * u + b * v = z) : u = z := by
  have h := convex_eq_upper_left ha hb hab (neg_le_neg hu) (neg_le_neg hv)
    (show a * -u + b * -v = -z by nlinarith [heq])
  linarith

theorem loewnerProfile_zero_extreme :
    loewnerProfile ⟨0, by norm_num⟩ ∈ normalizedAdmissibleCompactClass.extremePoints ℝ := by
  refine ⟨loewnerProfile_mem_compactClass _, ?_⟩
  intro u hu v hv hsegment
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hsegment
  funext x
  have hx := congrFun heq x
  change a * u x + b * v x = loewnerAtom ⟨0, by norm_num⟩ x at hx
  rw [loewnerAtom_zero] at hx
  change u x = loewnerAtom ⟨0, by norm_num⟩ x
  rw [loewnerAtom_zero]
  have huB := normalizedAdmissibleCompactClass_bounds hu x
  have hvB := normalizedAdmissibleCompactClass_bounds hv x
  by_cases hx1 : (x : ℝ) ≤ 1
  · exact convex_eq_upper_left ha hb.le hab
      (by simpa [max_eq_left hx1] using huB.2)
      (by simpa [max_eq_left hx1] using hvB.2) hx
  · have h1x : 1 ≤ (x : ℝ) := le_of_not_ge hx1
    exact convex_eq_lower_left ha hb.le hab
      (by simpa [min_eq_left h1x] using huB.1)
      (by simpa [min_eq_left h1x] using hvB.1) hx

theorem loewnerProfile_one_extreme :
    loewnerProfile ⟨1, by norm_num⟩ ∈ normalizedAdmissibleCompactClass.extremePoints ℝ := by
  refine ⟨loewnerProfile_mem_compactClass _, ?_⟩
  intro u hu v hv hsegment
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hsegment
  funext x
  have hx := congrFun heq x
  change a * u x + b * v x = loewnerAtom ⟨1, by norm_num⟩ x at hx
  rw [loewnerAtom_one] at hx
  change u x = loewnerAtom ⟨1, by norm_num⟩ x
  rw [loewnerAtom_one]
  have huB := normalizedAdmissibleCompactClass_bounds hu x
  have hvB := normalizedAdmissibleCompactClass_bounds hv x
  by_cases hx1 : (x : ℝ) ≤ 1
  · exact convex_eq_lower_left ha hb.le hab
      (by simpa [min_eq_right hx1] using huB.1)
      (by simpa [min_eq_right hx1] using hvB.1) hx
  · have h1x : 1 ≤ (x : ℝ) := le_of_not_ge hx1
    exact convex_eq_upper_left ha hb.le hab
      (by simpa [max_eq_right h1x] using huB.2)
      (by simpa [max_eq_right h1x] using hvB.2) hx

/-- Any decomposition of an extreme normalized profile in the nonnegative
operator cone is proportional. Zero-weight pieces are discharged by growth
bounds; no derivative positivity theorem is needed. -/
theorem extreme_nonnegative_decomposition_proportional {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass.extremePoints ℝ)
    {u v : ℝ → ℝ} (hu : NonnegativeOperatorFunction u) (hv : NonnegativeOperatorFunction v)
    (hsum : ∀ x : PositiveArgument, u x + v x = g x) :
    u 1 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ x : PositiveArgument, u x = u 1 * g x := by
  have hu0 := hu.2.1 1 zero_lt_one
  have hv0 := hv.2.1 1 zero_lt_one
  have hmass : u 1 + v 1 = 1 := by
    simpa only [normalizedAdmissibleCompactClass_at_one hg.1] using
      hsum ⟨1, by norm_num [PositiveArgument]⟩
  refine ⟨⟨hu0, by linarith⟩, ?_⟩
  by_cases hu1 : u 1 = 0
  · intro x
    rw [hu1, zero_mul]
    exact nonnegativeOperatorFunction_eq_zero_of_one_eq_zero hu hu1 x.property
  by_cases hv1 : v 1 = 0
  · intro x
    have hvx := nonnegativeOperatorFunction_eq_zero_of_one_eq_zero hv hv1 x.property
    have hu1' : u 1 = 1 := by linarith
    simpa only [hvx, add_zero, hu1', one_mul] using hsum x
  have hu1pos : 0 < u 1 := lt_of_le_of_ne hu0 (Ne.symm hu1)
  have hv1pos : 0 < v 1 := lt_of_le_of_ne hv0 (Ne.symm hv1)
  have hU := nonnegativeOperatorFunction_normalize_mem_compactClass hu hu1pos
  have hV := nonnegativeOperatorFunction_normalize_mem_compactClass hv hv1pos
  have heq : (fun x : PositiveArgument => (u 1)⁻¹ * u x) = g := by
    apply hg.2 hU hV
    refine ⟨u 1, v 1, hu1pos, hv1pos, hmass, ?_⟩
    funext x
    change u 1 * ((u 1)⁻¹ * u x) + v 1 * ((v 1)⁻¹ * v x) = g x
    simpa only [← mul_assoc, mul_inv_cancel₀ hu1, mul_inv_cancel₀ hv1, one_mul] using hsum x
  intro x
  have hx := congrFun heq x
  change (u 1)⁻¹ * u x = g x at hx
  calc u x = u 1 * ((u 1)⁻¹ * u x) := by rw [← mul_assoc, mul_inv_cancel₀ hu1, one_mul]
       _ = u 1 * g x := by rw [hx]

/-- The analytic split required by the extremal argument. This is an explicit
premise, not an axiom or a theorem asserting that the split exists. -/
def HasNonnegativeHansenSplit (g : PositiveArgument → ℝ) : Prop :=
  ∃ u v : ℝ → ℝ, NonnegativeOperatorFunction u ∧ NonnegativeOperatorFunction v ∧
    (∀ x : PositiveArgument, u x + v x = g x) ∧
    ∀ x : PositiveArgument, u x * ((x : ℝ) - 1) = (x : ℝ) * (g x - 1)

/-- Conditional on the analytic split, the complete extremal argument yields
the harmonic formula, including parameter zero and one. -/
theorem extreme_eq_loewnerProfile_of_hansenSplit {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass.extremePoints ℝ)
    (hsplit : HasNonnegativeHansenSplit g) : ∃ t : LoewnerParameter, g = loewnerProfile t := by
  obtain ⟨u, v, hu, hv, hsum, hrelation⟩ := hsplit
  obtain ⟨ht, hproportional⟩ := extreme_nonnegative_decomposition_proportional hg hu hv hsum
  let t : LoewnerParameter := ⟨u 1, ht⟩
  refine ⟨t, ?_⟩
  funext x
  change g x = loewnerAtom t x
  rw [loewnerAtom_eq_fraction t x.property]
  apply (eq_div_iff (loewnerAtom_denominator_pos t x.property).ne').mpr
  have hx := hrelation x
  rw [hproportional x] at hx
  change g x * (u 1 + (1 - u 1) * (x : ℝ)) = (x : ℝ)
  nlinarith [hx]

theorem extremePoints_subset_loewnerProfiles_of_hansenSplits
    (hsplit : ∀ g ∈ normalizedAdmissibleCompactClass.extremePoints ℝ,
      HasNonnegativeHansenSplit g) :
    normalizedAdmissibleCompactClass.extremePoints ℝ ⊆ Set.range loewnerProfile := by
  intro g hg
  obtain ⟨t, ht⟩ := extreme_eq_loewnerProfile_of_hansenSplit hg (hsplit g hg)
  exact ⟨t, ht.symm⟩

#assert_trust kernel convex_eq_upper_left
#assert_trust kernel convex_eq_lower_left
#assert_trust kernel loewnerProfile_zero_extreme
#assert_trust kernel loewnerProfile_one_extreme
#assert_trust kernel extreme_nonnegative_decomposition_proportional
#assert_trust kernel extreme_eq_loewnerProfile_of_hansenSplit
#assert_trust kernel extremePoints_subset_loewnerProfiles_of_hansenSplits
#print axioms extreme_eq_loewnerProfile_of_hansenSplit

end NLA.Proofs.RA10
