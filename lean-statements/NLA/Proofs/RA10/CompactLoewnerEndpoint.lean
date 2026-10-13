import NLA.Proofs.RA10.CompactLoewnerNormalization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! Extend a representation on the open half-line to zero using the frozen
continuity assumption. The difficult existence theorem may therefore be stated
on strictly positive scalar arguments, as in the usual literature. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory NLA.Statements.RA10 Filter

namespace NLA.Proofs.RA10

theorem loewnerAtom_continuousOn (t : LoewnerParameter) :
    ContinuousOn (loewnerAtom t) (Set.Ici 0) := by
  unfold loewnerAtom
  by_cases ht : (t : ℝ) = 0
  · simp only [ht, ↓reduceIte]
    exact continuousOn_const
  simp only [if_neg ht]
  apply continuousOn_id.div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
  intro x hx
  exact ne_of_gt (add_pos_of_pos_of_nonneg
    (lt_of_le_of_ne t.property.1 (Ne.symm ht))
    (mul_nonneg (sub_nonneg.mpr t.property.2) hx))

/-- A finite positive representation on x > 0 already determines the correct
value at zero, including the constant atom. -/
theorem compactLoewnerRepresentation_extend_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Ici 0)) (μ : Measure LoewnerParameter) [IsFiniteMeasure μ]
    (hrep : ∀ x : ℝ, 0 < x → f x = ∫ t, loewnerAtom t x ∂μ) :
    ∀ x : ℝ, 0 ≤ x → f x = ∫ t, loewnerAtom t x ∂μ := by
  have hseqpos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hseqle (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop
      (nhdsWithin 0 (Set.Ici 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (hseqpos n).le⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (loewnerAtom_measurable (1 / ((n : ℝ) + 1))).aestronglyMeasurable)
    (integrable_const 1)
    (fun n => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (loewnerAtom_nonneg t (hseqpos n).le)]
      exact (loewnerAtom_le_max t (hseqpos n).le).trans_eq (max_eq_left (hseqle n)))
    (Eventually.of_forall fun t =>
      ((loewnerAtom_continuousOn t) 0 (by simp)).tendsto.comp hseq)
  have hflim := (hf 0 (by simp)).tendsto.comp hseq
  have heq : (fun n : ℕ => f (1 / ((n : ℝ) + 1))) =
      (fun n : ℕ => ∫ t, loewnerAtom t (1 / ((n : ℝ) + 1)) ∂μ) :=
    funext fun n => hrep _ (hseqpos n)
  simp only [Function.comp_def] at hflim
  rw [heq] at hflim
  have hzero : f 0 = ∫ t, loewnerAtom t 0 ∂μ := tendsto_nhds_unique hflim hlim
  intro x hx
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · exact hzero
  · exact hrep x hxpos

/-- An alternative assembly using representation existence only on the open
half-line. The unconditional result is in `OperatorMonotoneRepresentation`. -/
theorem target_of_normalized_positive_representation
    (hexists : ∀ f : ℝ → ℝ, AdmissibleFunction f → f 1 = 1 →
      ∃ μ : Measure LoewnerParameter, IsFiniteMeasure μ ∧
        ∀ x : ℝ, 0 < x → f x = ∫ t, loewnerAtom t x ∂μ) : Target := by
  apply target_of_normalized_compactLoewnerRepresentation
  intro f hf h1
  obtain ⟨μ, hμ, hrep⟩ := hexists f hf h1
  let : IsFiniteMeasure μ := hμ
  exact ⟨μ, hμ, compactLoewnerRepresentation_extend_zero hf.1 μ hrep⟩

#assert_trust kernel loewnerAtom_continuousOn
#assert_trust kernel compactLoewnerRepresentation_extend_zero
#assert_trust kernel target_of_normalized_positive_representation
#print axioms target_of_normalized_positive_representation

end NLA.Proofs.RA10
