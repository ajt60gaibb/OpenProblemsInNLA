import NLA.Proofs.RA10.LoewnerMeasureConstruction
import Mathlib.Analysis.Convex.KreinMilman

/-! A compact convex class containing all normalized admissible profiles.
We close restrictions to the open half-line, so continuity at zero is not
incorrectly assumed to survive pointwise limits. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10 Set

namespace NLA.Proofs.RA10

theorem operatorMonotoneOnNonnegative_add {f g : ℝ → ℝ}
    (hf : OperatorMonotoneOnNonnegative f) (hg : OperatorMonotoneOnNonnegative g) :
    OperatorMonotoneOnNonnegative (fun x => f x + g x) := by
  intro d hd H G a b QH QG hH hG hHG
  rw [functionMatrix_add, functionMatrix_add]
  have heq : FunctionMatrix f a QH + FunctionMatrix g a QH -
      (FunctionMatrix f b QG + FunctionMatrix g b QG) =
      (FunctionMatrix f a QH - FunctionMatrix f b QG) +
        (FunctionMatrix g a QH - FunctionMatrix g b QG) := by abel
  rw [heq]
  apply (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr
  exact ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (hf d hd H G a b QH QG hH hG hHG)).add
      ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
        (hg d hd H G a b QH QG hH hG hHG))

theorem admissibleFunction_add {f g : ℝ → ℝ}
    (hf : AdmissibleFunction f) (hg : AdmissibleFunction g) :
    AdmissibleFunction (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, fun x hx => add_nonneg (hf.2.1 x hx) (hg.2.1 x hx),
    operatorMonotoneOnNonnegative_add hf.2.2 hg.2.2⟩

def normalizedAdmissibleProfiles : Set (PositiveArgument → ℝ) :=
  {g | ∃ f : ℝ → ℝ, AdmissibleFunction f ∧ f 1 = 1 ∧ (fun x : PositiveArgument => f x) = g}

def normalizedAdmissibleCompactClass : Set (PositiveArgument → ℝ) :=
  closure normalizedAdmissibleProfiles

theorem normalizedAdmissibleProfiles_convex : Convex ℝ normalizedAdmissibleProfiles := by
  intro u hu v hv a b ha hb hab
  obtain ⟨f, hf, hf1, rfl⟩ := hu
  obtain ⟨g, hg, hg1, rfl⟩ := hv
  refine ⟨fun x => a * f x + b * g x,
    admissibleFunction_add (admissibleFunction_smul hf ha) (admissibleFunction_smul hg hb),
    ?_, rfl⟩
  change a * f 1 + b * g 1 = 1
  simpa [hf1, hg1] using hab

theorem normalizedAdmissibleCompactClass_convex : Convex ℝ normalizedAdmissibleCompactClass :=
  normalizedAdmissibleProfiles_convex.closure

theorem normalizedAdmissibleProfiles_bounds {g : PositiveArgument → ℝ}
    (hg : g ∈ normalizedAdmissibleProfiles) (x : PositiveArgument) :
    g x ∈ Set.Icc (0 : ℝ) (max 1 (x : ℝ)) := by
  obtain ⟨f, hf, hf1, rfl⟩ := hg
  refine ⟨hf.2.1 x x.property.le, ?_⟩
  simpa [hf1] using (admissibleFunction_bounds hf x.property.le).2

/-- The previously proved growth bound makes the closed class compact by Tychonoff. -/
theorem normalizedAdmissibleCompactClass_isCompact : IsCompact normalizedAdmissibleCompactClass := by
  have hbox : IsCompact {g : PositiveArgument → ℝ | ∀ x : PositiveArgument,
      g x ∈ Set.Icc 0 (max 1 (x : ℝ))} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  exact hbox.of_isClosed_subset isClosed_closure
    (closure_minimal (fun _ hg x => normalizedAdmissibleProfiles_bounds hg x) hbox.isClosed)

theorem normalizedAdmissible_mem_compactClass {f : ℝ → ℝ}
    (hf : AdmissibleFunction f) (h1 : f 1 = 1) :
    (fun x : PositiveArgument => f x) ∈ normalizedAdmissibleCompactClass :=
  subset_closure ⟨f, hf, h1, rfl⟩

/-- Krein–Milman is fully discharged for this particular function class. -/
theorem normalizedAdmissibleCompactClass_eq_closedConvexHull_extremePoints :
    closure (convexHull ℝ (normalizedAdmissibleCompactClass.extremePoints ℝ)) =
      normalizedAdmissibleCompactClass :=
  closure_convexHull_extremePoints normalizedAdmissibleCompactClass_isCompact
    normalizedAdmissibleCompactClass_convex

/-- Once extreme points are classified, the measure is constructed by the
already proved compactness argument, with no measure-existence premise. -/
theorem normalizedAdmissible_representation_of_extremePoints
    (hextreme : normalizedAdmissibleCompactClass.extremePoints ℝ ⊆ Set.range loewnerProfile)
    {f : ℝ → ℝ} (hf : AdmissibleFunction f) (h1 : f 1 = 1) :
    HasCompactLoewnerRepresentation f := by
  apply hasCompactLoewnerRepresentation_of_mem_closedConvexHull hf.1
  have hmem := normalizedAdmissible_mem_compactClass hf h1
  rw [← normalizedAdmissibleCompactClass_eq_closedConvexHull_extremePoints] at hmem
  exact closure_mono (convexHull_mono hextreme) hmem

/-- Internal assembly from extreme-point classification, discharged by
`OperatorMonotoneRepresentation`. -/
theorem target_of_normalizedAdmissible_extremePoints
    (hextreme : normalizedAdmissibleCompactClass.extremePoints ℝ ⊆ Set.range loewnerProfile) :
    Target :=
  target_of_normalized_compactLoewnerRepresentation fun _ hf h1 =>
    normalizedAdmissible_representation_of_extremePoints hextreme hf h1

#assert_trust kernel operatorMonotoneOnNonnegative_add
#assert_trust kernel admissibleFunction_add
#assert_trust kernel normalizedAdmissibleProfiles_convex
#assert_trust kernel normalizedAdmissibleCompactClass_convex
#assert_trust kernel normalizedAdmissibleProfiles_bounds
#assert_trust kernel normalizedAdmissibleCompactClass_isCompact
#assert_trust kernel normalizedAdmissible_mem_compactClass
#assert_trust kernel normalizedAdmissibleCompactClass_eq_closedConvexHull_extremePoints
#assert_trust kernel normalizedAdmissible_representation_of_extremePoints
#assert_trust kernel target_of_normalizedAdmissible_extremePoints
#print axioms target_of_normalizedAdmissible_extremePoints

end NLA.Proofs.RA10
