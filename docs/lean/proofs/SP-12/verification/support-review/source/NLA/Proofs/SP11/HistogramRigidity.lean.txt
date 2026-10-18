import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanCert.Tactic.Verification

/-!
# Equality rigidity for shared-variable occurrence histograms

Equal monomial exponents give equal sums of every additive variable weight.
If the canonical weight is a lower bound at every occurrence, equality of
the total forces equality at each occurrence, even when variables repeat.
A weight may be zero outside a chosen vertex class, so no ordering of all
variable names is required. The graph-specific lower bounds and reconstruction
of conduit choices are separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

variable {ι σ : Type*}

/-- Equality of exponent histograms preserves every natural-valued variable weight. -/
theorem weight_sum_eq_of_occurrence_histogram_eq (s : Finset ι)
    (best actual : ι → σ)
    (h : (∑ a ∈ s, Finsupp.single (actual a) 1) =
      (∑ a ∈ s, Finsupp.single (best a) 1)) (weight : σ → ℕ) :
    (∑ a ∈ s, weight (actual a)) = ∑ a ∈ s, weight (best a) := by
  have hw := congrArg (Finsupp.linearCombination ℕ weight) h
  simpa only [map_sum, Finsupp.linearCombination_single, one_smul] using hw

/-- No occurrence can strictly exceed its canonical lower weight if the
shared-variable exponent histograms agree. Distinct variable names are not required. -/
theorem occurrence_weight_eq_of_histogram_eq (s : Finset ι)
    (best actual : ι → σ) (weight : σ → ℕ)
    (h : (∑ a ∈ s, Finsupp.single (actual a) 1) =
      (∑ a ∈ s, Finsupp.single (best a) 1))
    (hbound : ∀ a ∈ s, weight (best a) ≤ weight (actual a)) :
    ∀ a ∈ s, weight (actual a) = weight (best a) := by
  intro a ha
  by_contra hne
  have hstrict : weight (best a) < weight (actual a) :=
    lt_of_le_of_ne (hbound a ha) (Ne.symm hne)
  have hlt := Finset.sum_lt_sum hbound ⟨a, ha, hstrict⟩
  have hsum := weight_sum_eq_of_occurrence_histogram_eq s best actual h weight
  rw [hsum] at hlt
  exact lt_irrefl _ hlt

#assert_trust kernel weight_sum_eq_of_occurrence_histogram_eq
#assert_trust kernel occurrence_weight_eq_of_histogram_eq
#print axioms occurrence_weight_eq_of_histogram_eq

end NLA.Proofs.SP11
