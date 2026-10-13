import NLA.Proofs.RA10.HansenSplit

/-! The positive Löwner representation and the complete frozen RA-10 target.
The representing measure is obtained from the proved extreme-point
classification, Krein–Milman and compactness of probability measures. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 MeasureTheory Set

namespace NLA.Proofs.RA10

theorem normalizedAdmissible_extremePoints_subset_loewnerProfile :
    normalizedAdmissibleCompactClass.extremePoints ℝ ⊆ Set.range loewnerProfile := by
  intro g hg
  obtain ⟨t, ht⟩ := extreme_eq_loewnerProfile hg
  exact ⟨t, ht.symm⟩

theorem normalizedProfile_probabilityRepresentation {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleCompactClass) :
    ∃ μ : ProbabilityMeasure LoewnerParameter, ∀ x : PositiveArgument,
      g x = ∫ t, loewnerAtom t x ∂μ := by
  apply exists_probabilityMeasure_of_mem_closedConvexHull
  rw [← normalizedAdmissibleCompactClass_eq_closedConvexHull_extremePoints] at hg
  exact closure_mono
    (convexHull_mono normalizedAdmissible_extremePoints_subset_loewnerProfile) hg

theorem admissibleFunction_hasCompactLoewnerRepresentation {f : ℝ → ℝ}
    (hf : AdmissibleFunction f) : HasCompactLoewnerRepresentation f :=
  hasCompactLoewnerRepresentation_of_normalized
    (fun _ hg h1 => normalizedAdmissible_representation_of_extremePoints
      normalizedAdmissible_extremePoints_subset_loewnerProfile hg h1) hf

/-- The universal constant 11 works with exactly the frozen assumptions. -/
theorem transferBound_eleven : TransferBound 11 :=
  transferBound_eleven_of_compactLoewnerRepresentation
    (fun _ hf => admissibleFunction_hasCompactLoewnerRepresentation hf)

/-- Complete proof of the original RA-10 target. -/
theorem ra10_target : NLA.Statements.RA10.Target :=
  ⟨11, by norm_num, transferBound_eleven⟩

#assert_trust kernel normalizedAdmissible_extremePoints_subset_loewnerProfile
#assert_trust kernel normalizedProfile_probabilityRepresentation
#assert_trust kernel admissibleFunction_hasCompactLoewnerRepresentation
#assert_trust kernel transferBound_eleven
#assert_trust kernel ra10_target
#print axioms admissibleFunction_hasCompactLoewnerRepresentation
#print axioms transferBound_eleven
#print axioms ra10_target

end NLA.Proofs.RA10
