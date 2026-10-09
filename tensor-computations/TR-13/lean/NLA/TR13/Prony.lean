import NLA.TR13.Definitions
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.Resultant.Basic

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace NLA.TR13

/-- The recurrence polynomial, with its leading coefficient left unnormalized. -/
def recurrencePolynomial (r : ℕ) (δ : ℂ) (d : Fin r → ℂ) : ℂ[X] :=
  C δ * X ^ r - Polynomial.ofFn r d

lemma recurrencePolynomial_natDegree {r : ℕ} (hr : 0 < r)
    {δ : ℂ} (hδ : δ ≠ 0) (d : Fin r → ℂ) :
    (recurrencePolynomial r δ d).natDegree = r := by
  unfold recurrencePolynomial
  rw [natDegree_sub_eq_left_of_natDegree_lt]
  · simp [hδ]
  · simpa [hδ] using Polynomial.ofFn_natDegree_lt hr d

lemma recurrencePolynomial_eval (r : ℕ) (δ : ℂ) (d : Fin r → ℂ) (t : ℂ) :
    (recurrencePolynomial r δ d).eval t =
      δ * t ^ r - ∑ j, d j * t ^ j.val := by
  simp [recurrencePolynomial, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]

/-- A separable complex polynomial of degree `r` has an injectively indexed family
of exactly `r` roots. -/
lemma indexed_roots {p : ℂ[X]} {r : ℕ} (hp : p.Separable)
    (hdegree : p.natDegree = r) :
    ∃ t : Fin r → ℂ, Function.Injective t ∧ ∀ j, p.eval (t j) = 0 := by
  classical
  have hc : Fintype.card (p.rootSet ℂ) = r := by
    rw [Polynomial.card_rootSet_eq_natDegree hp (IsAlgClosed.splits _), hdegree]
  let e : p.rootSet ℂ ≃ Fin r := Fintype.equivFinOfCardEq hc
  refine ⟨fun j => (e.symm j).val, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · intro j
    simpa using Polynomial.aeval_eq_zero_of_mem_rootSet (e.symm j).property

/-- Distinct nodes interpolate an arbitrary vector of initial moments. -/
lemma initial_moment_weights {r : ℕ} (t : Fin r → ℂ)
    (ht : Function.Injective t) (h : ℕ → ℂ) :
    ∃ c : Fin r → ℂ, ∀ i : Fin r, h i = ∑ j, c j * t j ^ i.val := by
  classical
  let V : Matrix (Fin r) (Fin r) ℂ := (Matrix.vandermonde t).transpose
  have hV : IsUnit V.det := by
    simpa [V, isUnit_iff_ne_zero] using Matrix.det_vandermonde_ne_zero_iff.mpr ht
  refine ⟨V⁻¹ *ᵥ (fun i : Fin r => h i), ?_⟩
  intro i
  have he := congrFun (show V *ᵥ (V⁻¹ *ᵥ (fun i : Fin r => h i)) =
      (fun i : Fin r => h i) by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hV, Matrix.one_mulVec]) i
  simpa [V, Matrix.mulVec, dotProduct, mul_comm] using he.symm

/-- Every exponential moment sequence satisfies the recurrence of its nodes. -/
lemma exponential_moment_recurrence {r : ℕ} (δ : ℂ) (d c t : Fin r → ℂ)
    (ht : ∀ j, (recurrencePolynomial r δ d).eval (t j) = 0) (i : ℕ) :
    δ * (∑ j, c j * t j ^ (i + r)) =
      ∑ k, d k * (∑ j, c j * t j ^ (i + k.val)) := by
  have ht' (j : Fin r) : δ * t j ^ r = ∑ k, d k * t j ^ k.val := by
    exact sub_eq_zero.mp ((recurrencePolynomial_eval r δ d (t j)).symm.trans (ht j))
  simp_rw [pow_add, Finset.mul_sum]
  calc
    (∑ j, δ * (c j * (t j ^ i * t j ^ r))) =
        ∑ j, (c j * t j ^ i) * (δ * t j ^ r) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j, (c j * t j ^ i) * (∑ k, d k * t j ^ k.val) := by
      simp_rw [ht']
    _ = ∑ k, ∑ j, d k * (c j * (t j ^ i * t j ^ k.val)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Prony reconstruction from a nonsingular recurrence with distinct roots.
Only `2*r` moments are required. -/
theorem prony_representation {r : ℕ} (hr : 0 < r) (h : ℕ → ℂ)
    {δ : ℂ} (hδ : δ ≠ 0) (d : Fin r → ℂ)
    (hrec : ∀ i : Fin r, δ * h (i.val + r) = ∑ j, d j * h (i.val + j.val))
    (hsep : (recurrencePolynomial r δ d).Separable) :
    ∃ c t : Fin r → ℂ, ∀ i < 2 * r, h i = ∑ j, c j * t j ^ i := by
  obtain ⟨t, ht, hroots⟩ := indexed_roots hsep (recurrencePolynomial_natDegree hr hδ d)
  obtain ⟨c, hc⟩ := initial_moment_weights t ht h
  refine ⟨c, t, ?_⟩
  intro i hi
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hir : i < r
    · exact hc ⟨i, hir⟩
    · have hsub : i - r < r := by omega
      have hir' : i - r + r = i := Nat.sub_add_cancel (by omega)
      apply mul_left_cancel₀ hδ
      rw [← hir', hrec ⟨i - r, hsub⟩,
        exponential_moment_recurrence δ d c t hroots]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (i - r + j.val) (by omega) (by omega)]

end NLA.TR13
