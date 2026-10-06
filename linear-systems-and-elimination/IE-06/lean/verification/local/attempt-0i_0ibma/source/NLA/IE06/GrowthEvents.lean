import NLA.IE06.GaussianTies
import NLA.IE06.GaussianDenominator

/-! Exact all-path to canonical-path and input-normalization event bridges.
Preimplementation review: `reviews/growth-events-specification.md`. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace NLA.IE06

/-- The numerator of the original all-active-Schur growth factor. -/
def rawSchurMax {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n =>
    activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ)

def selectedExceedanceEvent (n : ℕ) (t : ℝ) : Set (Mat n) :=
  {A | 0 < n ∧ A.det ≠ 0 ∧ AdmissiblePath A (firstPath A) ∧
    t < growth A (firstPath A)}

def canonicalRawEvent (n : ℕ) (t : ℝ) : Set (Mat n) :=
  {A | t < rawSchurMax A (firstPath A)}

theorem rawSchurMax_nonneg {n : ℕ} (A : Mat n) (path : PivotPath n) :
    0 ≤ rawSchurMax A path := NNReal.coe_nonneg _

theorem growth_eq_rawSchurMax_div {n : ℕ} (A : Mat n) (path : PivotPath n) :
    growth A path = rawSchurMax A path / entryMax A := rfl

theorem growth_le_rawSchurMax {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hA : 1 ≤ entryMax A) : growth A path ≤ rawSchurMax A path := by
  rw [growth_eq_rawSchurMax_div]
  exact div_le_self (rawSchurMax_nonneg A path) hA

theorem exceedanceEvent_ae_selected (n : ℕ) (t : ℝ) :
    exceedanceEvent n t =ᵐ[gaussianMatrix n] selectedExceedanceEvent n t := by
  filter_upwards [gaussianMatrix_admissiblePath_eq_firstPath_ae n] with A hA
  apply propext
  constructor
  · rintro ⟨hn, hdet, path, hp, ht⟩
    have heq := hA path hp
    subst path
    exact ⟨hn, hdet, hp, ht⟩
  · rintro ⟨hn, hdet, hp, ht⟩
    exact ⟨hn, hdet, firstPath A, hp, ht⟩

theorem exceedanceEvent_measure_eq_selected (n : ℕ) (t : ℝ) :
    gaussianMatrix n (exceedanceEvent n t) =
      gaussianMatrix n (selectedExceedanceEvent n t) :=
  measure_congr (exceedanceEvent_ae_selected n t)

theorem exceedanceEvent_measure_le_raw_add_normalization (n : ℕ) (t : ℝ) :
    gaussianMatrix n (exceedanceEvent n t) ≤
      gaussianMatrix n (canonicalRawEvent n t) +
      gaussianMatrix n {A : Mat n | entryMax A < 1} := by
  apply le_trans (measure_mono_ae (t := canonicalRawEvent n t ∪
    {A : Mat n | entryMax A < 1}) ?_) (measure_union_le _ _)
  filter_upwards [gaussianMatrix_admissiblePath_eq_firstPath_ae n] with A hA
  rintro ⟨hn, hdet, path, hp, ht⟩
  by_cases hsmall : entryMax A < 1
  · exact Or.inr hsmall
  · left
    have heq := hA path hp
    subst path
    exact lt_of_lt_of_le ht (growth_le_rawSchurMax A (firstPath A) (le_of_not_gt hsmall))

theorem exceedanceEvent_measure_le_raw_add_exact_normalization (n : ℕ) (t : ℝ) :
    gaussianMatrix n (exceedanceEvent n t) ≤
      gaussianMatrix n (canonicalRawEvent n t) +
      ENNReal.ofReal (gaussianUnitIntervalMass ^ (n^2)) := by
  simpa only [gaussian_entryMax_lt_one_probability] using
    exceedanceEvent_measure_le_raw_add_normalization n t

#assert_trust kernel rawSchurMax_nonneg
#assert_trust kernel growth_eq_rawSchurMax_div
#assert_trust kernel growth_le_rawSchurMax
#assert_trust kernel exceedanceEvent_ae_selected
#assert_trust kernel exceedanceEvent_measure_eq_selected
#assert_trust kernel exceedanceEvent_measure_le_raw_add_normalization
#assert_trust kernel exceedanceEvent_measure_le_raw_add_exact_normalization
#print axioms exceedanceEvent_measure_eq_selected
#print axioms exceedanceEvent_measure_le_raw_add_exact_normalization
end NLA.IE06
