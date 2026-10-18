import NLA.Proofs.SP11.GramBridge
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Simultaneous polynomial faithfulness for SP-11

Hall's construction gives polynomial vectors whose nonedge inner products
vanish identically. The unique-monomial lemma must separately show that every
edge and diagonal inner-product polynomial is nonzero. Over the infinite field
of reals, these finitely many nonzero polynomials can then be made nonzero at
one common parameter value. No probability or genericity oracle is used here.

Source: H. Tracy Hall, *The Delta Theorem*, arXiv:2601.01211v1,
Lemma 5.14 and the proof of Theorem 3.20. The unique-monomial lemma itself
is not proved by this module.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- Coordinates of a polynomial-valued real representation. -/
noncomputable def polynomialGram {σ : Type*} {n d : ℕ}
    (P : Matrix (Fin n) (Fin d) (MvPolynomial σ ℝ)) (i j : Fin n) :
    MvPolynomial σ ℝ := ∑ k, P i k * P j k

/-- A nonzero real polynomial is nonzero at some actual assignment, even
when the ambient variable type is infinite. -/
theorem exists_real_eval_ne_zero {σ : Type*} (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
    ∃ x : σ → ℝ, MvPolynomial.eval x p ≠ 0 := by
  by_contra! h
  apply hp
  apply MvPolynomial.funext
  intro x
  simpa using h x

/-- All finitely many nonzero polynomial constraints hold at the same point. -/
theorem exists_simultaneous_real_eval_ne_zero {σ α : Type*}
    (s : Finset α) (p : α → MvPolynomial σ ℝ)
    (hp : ∀ a ∈ s, p a ≠ 0) :
    ∃ x : σ → ℝ, ∀ a ∈ s, MvPolynomial.eval x (p a) ≠ 0 := by
  classical
  have hprod : (∏ a ∈ s, p a) ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  obtain ⟨x, hx⟩ := exists_real_eval_ne_zero _ hprod
  refine ⟨x, ?_⟩
  have hxprod : (∏ a ∈ s, MvPolynomial.eval x (p a)) ≠ 0 := by
    simpa only [map_prod] using hx
  exact Finset.prod_ne_zero_iff.mp hxprod

/-- Evaluating polynomial vectors commutes exactly with their Gram entries. -/
theorem eval_polynomialGram {σ : Type*} {n d : ℕ}
    (P : Matrix (Fin n) (Fin d) (MvPolynomial σ ℝ)) (x : σ → ℝ) (i j : Fin n) :
    MvPolynomial.eval x (polynomialGram P i j) =
      gram (fun i k => MvPolynomial.eval x (P i k)) i j := by
  change MvPolynomial.eval x (polynomialGram P i j) =
    ∑ k, MvPolynomial.eval x (P i k) * MvPolynomial.eval x (P j k)
  simp [polynomialGram]

/-- Identically orthogonal nonedges and nonzero edge/diagonal polynomials
produce one faithful real representation with every row nonzero. Both
polynomial hypotheses remain explicit obligations for Hall's construction. -/
theorem exists_faithful_real_evaluation {σ : Type*} {n d : ℕ}
    (G : SimpleGraph (Fin n))
    (P : Matrix (Fin n) (Fin d) (MvPolynomial σ ℝ))
    (hzero : ∀ i j, i ≠ j → ¬ G.Adj i j → polynomialGram P i j = 0)
    (hnonzero : ∀ i j, i = j ∨ G.Adj i j → polynomialGram P i j ≠ 0) :
    ∃ x : σ → ℝ,
      NLA.Statements.SP11.HasPattern G
        (gram (fun i k => MvPolynomial.eval x (P i k))) ∧
      ∀ i, (fun k => MvPolynomial.eval x (P i k)) ≠ 0 := by
  classical
  let s := (Finset.univ : Finset (Fin n × Fin n)).filter
    (fun ij => ij.1 = ij.2 ∨ G.Adj ij.1 ij.2)
  obtain ⟨x, hx⟩ := exists_simultaneous_real_eval_ne_zero s
    (fun ij => polynomialGram P ij.1 ij.2)
    (by intro ij hij; exact hnonzero _ _ (Finset.mem_filter.mp hij).2)
  have hgram : ∀ i j, i = j ∨ G.Adj i j →
      gram (fun i k => MvPolynomial.eval x (P i k)) i j ≠ 0 := by
    intro i j hij
    rw [← eval_polynomialGram]
    exact hx (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
  refine ⟨x, gram_hasPattern G _ ?_, ?_⟩
  · intro i j hij
    constructor
    · intro hdot
      by_contra hnot
      have hz := congrArg (MvPolynomial.eval x) (hzero i j hij hnot)
      simp only [eval_polynomialGram, map_zero] at hz
      change (∑ k, MvPolynomial.eval x (P i k) * MvPolynomial.eval x (P j k)) = 0 at hz
      exact hdot hz
    · intro hadj
      exact hgram i j (Or.inr hadj)
  · intro i hi
    apply hgram i i (Or.inl rfl)
    change (∑ k, MvPolynomial.eval x (P i k) * MvPolynomial.eval x (P i k)) = 0
    have hcoord : ∀ k, MvPolynomial.eval x (P i k) = 0 :=
      fun k => congrFun hi k
    simp [hcoord]

/-- Hall's polynomial-vector obligations, including the ambient dimension bound,
are sufficient for the exact frozen target. The uniform construction and its
non-cancellation proof must still supply every witness in `h`. -/
theorem target_of_polynomial_representations
    (h : ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
      ∃ d : ℕ, ∃ σ : Type, ∃ P : Matrix (Fin n) (Fin d) (MvPolynomial σ ℝ),
        d + NLA.Statements.SP11.MinimumDegree G ≤ n ∧
        (∀ i j, i ≠ j → ¬ G.Adj i j → polynomialGram P i j = 0) ∧
        (∀ i j, i = j ∨ G.Adj i j → polynomialGram P i j ≠ 0)) :
    NLA.Statements.SP11.Target := by
  intro n hn G
  obtain ⟨d, σ, P, hd, hzero, hnonzero⟩ := h n hn G
  obtain ⟨x, hpattern, _⟩ := exists_faithful_real_evaluation G P hzero hnonzero
  exact ⟨gram (fun i k => MvPolynomial.eval x (P i k)), hpattern,
    minDegree_le_gram_nullity G _ hd⟩

#assert_trust kernel exists_real_eval_ne_zero
#assert_trust kernel exists_simultaneous_real_eval_ne_zero
#assert_trust kernel eval_polynomialGram
#assert_trust kernel exists_faithful_real_evaluation
#assert_trust kernel target_of_polynomial_representations
#print axioms exists_faithful_real_evaluation
#print axioms target_of_polynomial_representations

end NLA.Proofs.SP11
