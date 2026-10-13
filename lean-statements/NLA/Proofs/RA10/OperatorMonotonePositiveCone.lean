import NLA.Proofs.RA10.LoewnerAtomMonotonicity

/-! The unnormalized nonnegative operator-monotone cone on the open half-line.
Growth bounds and the zero case allow extremal decompositions to be handled
without assuming differentiability or a strictly interior derivative. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Set Filter

namespace NLA.Proofs.RA10

def NonnegativeOperatorFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ioi 0) ∧ (∀ x : ℝ, 0 < x → 0 ≤ f x) ∧
    OperatorMonotoneOnPositive f

theorem operatorMonotoneOnPositive_smul {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnPositive f) {c : ℝ} (hc : 0 ≤ c) :
    OperatorMonotoneOnPositive (fun x => c * f x) := by
  intro d hd H G a b QH QG ha hb hH hG hHG
  rw [functionMatrix_smul, functionMatrix_smul, ← smul_sub]
  apply (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr
  exact ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (hf d hd H G a b QH QG ha hb hH hG hHG)).smul hc

theorem nonnegativeOperatorFunction_smul {f : ℝ → ℝ}
    (hf : NonnegativeOperatorFunction f) {c : ℝ} (hc : 0 ≤ c) :
    NonnegativeOperatorFunction (fun x => c * f x) :=
  ⟨continuousOn_const.mul hf.1, fun x hx => mul_nonneg hc (hf.2.1 x hx),
    operatorMonotoneOnPositive_smul hf.2.2 hc⟩

theorem nonnegativeOperatorFunction_bounds {f : ℝ → ℝ}
    (hf : NonnegativeOperatorFunction f) {x : ℝ} (hx : 0 < x) :
    min 1 x * f 1 ≤ f x ∧ f x ≤ max 1 x * f 1 := by
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hs : Tendsto s atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim (y : ℝ) (hy : 0 < y) :
      Tendsto (fun n => f (y + s n)) atTop (nhds (f y)) := by
    apply (hf.1.continuousAt (isOpen_Ioi.mem_nhds hy)).tendsto.comp
    simpa only [add_zero] using (tendsto_const_nhds.add hs :
      Tendsto (fun n => y + s n) atTop (nhds (y + 0)))
  have hb (n : ℕ) := admissibleFunction_bounds
    (admissibleFunction_positive_shift hf.1 hf.2.1 hf.2.2 (hspos n)) hx.le
  exact ⟨le_of_tendsto_of_tendsto' ((hlim 1 zero_lt_one).const_mul _) (hlim x hx)
      (fun n => (hb n).1),
    le_of_tendsto_of_tendsto' (hlim x hx) ((hlim 1 zero_lt_one).const_mul _)
      (fun n => (hb n).2)⟩

theorem nonnegativeOperatorFunction_eq_zero_of_one_eq_zero {f : ℝ → ℝ}
    (hf : NonnegativeOperatorFunction f) (h1 : f 1 = 0) {x : ℝ} (hx : 0 < x) :
    f x = 0 := by
  have hb := (nonnegativeOperatorFunction_bounds hf hx).2
  rw [h1, mul_zero] at hb
  exact le_antisymm hb (hf.2.1 x hx)

theorem nonnegativeOperatorFunction_pos_of_one_pos {f : ℝ → ℝ}
    (hf : NonnegativeOperatorFunction f) (h1 : 0 < f 1) {x : ℝ} (hx : 0 < x) :
    0 < f x :=
  (mul_pos (lt_min zero_lt_one hx) h1).trans_le (nonnegativeOperatorFunction_bounds hf hx).1

theorem nonnegativeOperatorFunction_normalize_mem_compactClass {f : ℝ → ℝ}
    (hf : NonnegativeOperatorFunction f) (h1 : 0 < f 1) :
    (fun x : PositiveArgument => (f 1)⁻¹ * f x) ∈ normalizedAdmissibleCompactClass := by
  have hn := nonnegativeOperatorFunction_smul hf (inv_nonneg.mpr h1.le)
  exact positiveOperatorMonotone_mem_compactClass hn.1
    (fun x hx => mul_pos (inv_pos.mpr h1) (nonnegativeOperatorFunction_pos_of_one_pos hf h1 hx))
    hn.2.2 (inv_mul_cancel₀ h1.ne')

theorem normalizedAdmissibleCompactClass_nonnegativeOperatorFunction
    {g : PositiveArgument → ℝ} (hg : g ∈ normalizedAdmissibleCompactClass) :
    NonnegativeOperatorFunction (positiveProfileExtension g) := by
  refine ⟨normalizedAdmissibleCompactClass_continuousOn hg, ?_,
    normalizedAdmissibleCompactClass_operatorMonotone hg⟩
  intro x hx
  simpa only [positiveProfileExtension, dif_pos hx] using
    (normalizedAdmissibleCompactClass_pos hg ⟨x, hx⟩).le

#assert_trust kernel operatorMonotoneOnPositive_smul
#assert_trust kernel nonnegativeOperatorFunction_smul
#assert_trust kernel nonnegativeOperatorFunction_bounds
#assert_trust kernel nonnegativeOperatorFunction_eq_zero_of_one_eq_zero
#assert_trust kernel nonnegativeOperatorFunction_pos_of_one_pos
#assert_trust kernel nonnegativeOperatorFunction_normalize_mem_compactClass
#assert_trust kernel normalizedAdmissibleCompactClass_nonnegativeOperatorFunction
#print axioms nonnegativeOperatorFunction_normalize_mem_compactClass

end NLA.Proofs.RA10
