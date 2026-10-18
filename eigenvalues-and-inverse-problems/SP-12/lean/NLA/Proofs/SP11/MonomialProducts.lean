import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanCert.Tactic.Verification

/-!
# Repeated-variable products and a unique coefficient

Occurrences may reuse the same polynomial variable. If every occurrence's
variable weakly worsens in priority and one strictly worsens, their exponent
sum strictly worsens in the lexicographic monomial order. In particular,
different occurrences cannot compensate for each other by sharing a variable.

These are generic algebraic helpers. The SP-11 garden construction must still
prove the per-occurrence comparisons; no graph noncancellation is proved here.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators MonomialOrder

namespace NLA.Proofs.SP11

variable {ι σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- Earlier variable indices have higher monomial priority. Occurrences need
not have distinct variable names. -/
theorem occurrenceExponent_le (s : Finset ι) (best actual : ι → σ)
    (h : ∀ a ∈ s, best a ≤ actual a) :
    (∑ a ∈ s, Finsupp.single (actual a) 1) ≼[MonomialOrder.lex]
      (∑ a ∈ s, Finsupp.single (best a) 1) := by
  rw [map_sum, map_sum]
  exact Finset.sum_le_sum (fun a ha => Finsupp.Lex.single_le_iff.mpr (h a ha))

/-- If one occurrence strictly worsens and none improves, the entire product
strictly worsens, including repeated uses of one variable. -/
theorem occurrenceExponent_lt (s : Finset ι) (best actual : ι → σ)
    (h : ∀ a ∈ s, best a ≤ actual a)
    (hlt : ∃ a ∈ s, best a < actual a) :
    (∑ a ∈ s, Finsupp.single (actual a) 1) ≺[MonomialOrder.lex]
      (∑ a ∈ s, Finsupp.single (best a) 1) := by
  rw [map_sum, map_sum]
  apply Finset.sum_lt_sum
  · intro a ha
    exact Finsupp.Lex.single_le_iff.mpr (h a ha)
  · obtain ⟨a, ha, hstrict⟩ := hlt
    exact ⟨a, ha, Finsupp.Lex.single_lt_iff.mpr hstrict⟩

/-- Equality of the shared-variable exponent histograms forces every
occurrence's choice to equal its lower bound, given the one-sided bounds. -/
theorem occurrenceExponent_eq_iff (s : Finset ι) (best actual : ι → σ)
    (h : ∀ a ∈ s, best a ≤ actual a) :
    (∑ a ∈ s, Finsupp.single (actual a) 1) =
        (∑ a ∈ s, Finsupp.single (best a) 1) ↔
      ∀ a ∈ s, actual a = best a := by
  constructor
  · intro heq a ha
    by_contra hne
    have hstrict : best a < actual a := lt_of_le_of_ne (h a ha) (Ne.symm hne)
    have hlt := occurrenceExponent_lt s best actual h ⟨a, ha, hstrict⟩
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro heq
    exact Finset.sum_congr rfl (fun a ha => by rw [heq a ha])

section Coefficient

variable {α τ R : Type*} [CommSemiring R]

/-- A distinguished exponent with exactly one nonzero contributing summand
has precisely that summand's coefficient. Zero summands may share its exponent. -/
theorem coeff_sum_monomial_of_unique (s : Finset α) (e : α → τ →₀ ℕ)
    (c : α → R) (a₀ : α) (ha₀ : a₀ ∈ s)
    (hunique : ∀ a ∈ s, c a ≠ 0 → e a = e a₀ → a = a₀) :
    MvPolynomial.coeff (e a₀) (∑ a ∈ s, MvPolynomial.monomial (e a) (c a)) = c a₀ := by
  classical
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single a₀]
  · simp
  · intro a ha hne
    by_cases hc : c a = 0
    · simp [hc]
    · have he : e a ≠ e a₀ := fun he => hne (hunique a ha hc he)
      simp [MvPolynomial.coeff_monomial, he]
  · exact fun hnot => False.elim (hnot ha₀)

/-- A unique nonzero contribution to one coefficient prevents the full
polynomial from vanishing. This assumes no independence between occurrences. -/
theorem sum_monomial_ne_zero_of_unique (s : Finset α) (e : α → τ →₀ ℕ)
    (c : α → R) (a₀ : α) (ha₀ : a₀ ∈ s) (hc₀ : c a₀ ≠ 0)
    (hunique : ∀ a ∈ s, c a ≠ 0 → e a = e a₀ → a = a₀) :
    (∑ a ∈ s, MvPolynomial.monomial (e a) (c a)) ≠ 0 := by
  intro hzero
  have hcoeff := coeff_sum_monomial_of_unique s e c a₀ ha₀ hunique
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  exact hc₀ hcoeff.symm

end Coefficient

#assert_trust kernel occurrenceExponent_le
#assert_trust kernel occurrenceExponent_lt
#assert_trust kernel occurrenceExponent_eq_iff
#assert_trust kernel coeff_sum_monomial_of_unique
#assert_trust kernel sum_monomial_ne_zero_of_unique
#print axioms occurrenceExponent_eq_iff
#print axioms sum_monomial_ne_zero_of_unique

end NLA.Proofs.SP11
