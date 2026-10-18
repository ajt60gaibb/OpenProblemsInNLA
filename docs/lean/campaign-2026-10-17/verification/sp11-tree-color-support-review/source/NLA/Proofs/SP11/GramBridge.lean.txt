import NLA.Statements.SP11
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Faithful Gram matrices for SP-11

This is the final linear-algebra step in Hall's proof of the delta theorem.
A faithful real representation in dimension at most `n - δ(G)` supplies the
exact symmetric matrix required by the frozen SP-11 statement. The difficult
existence of the representation is not assumed to have been proved here.

Source: H. Tracy Hall, *The Delta Theorem*, arXiv:2601.01211v1,
Theorem 3.20 and Corollary 3.24. These deductions use Mathlib's matrix rank.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- Rows are the representing vectors; every entry is their ordinary real dot product. -/
def gram {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  R * R.transpose

@[simp] theorem gram_apply {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ)
    (i j : Fin n) : gram R i j = ∑ k, R i k * R j k := rfl

/-- Faithfulness imposes the exact off-diagonal graph pattern, in both directions. -/
theorem gram_hasPattern {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ)
    (h : ∀ i j, i ≠ j → ((∑ k, R i k * R j k) ≠ 0 ↔ G.Adj i j)) :
    NLA.Statements.SP11.HasPattern G (gram R) := by
  constructor
  · intro i j
    simp only [gram_apply]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _
  · exact h

/-- Ambient dimension bounds Gram rank, even for a dependent or empty vector family. -/
theorem gram_rank_le {n d : ℕ} (R : Matrix (Fin n) (Fin d) ℝ) :
    (gram R).rank ≤ d :=
  (Matrix.rank_mul_le_left R R.transpose).trans R.rank_le_width

/-- Rank-nullity gives the required weak bound without assuming full row rank. -/
theorem minDegree_le_gram_nullity {n d : ℕ} (G : SimpleGraph (Fin n))
    (R : Matrix (Fin n) (Fin d) ℝ)
    (hd : d + NLA.Statements.SP11.MinimumDegree G ≤ n) :
    NLA.Statements.SP11.MinimumDegree G ≤ n - (gram R).rank := by
  have hr := gram_rank_le R
  omega

/-- The explicit faithful-representation existence obligation implies the entire
frozen target. This theorem does not discharge that existence obligation. -/
theorem target_of_faithful_representations
    (h : ∀ n : ℕ, 0 < n → ∀ G : SimpleGraph (Fin n),
      ∃ d : ℕ, ∃ R : Matrix (Fin n) (Fin d) ℝ,
        d + NLA.Statements.SP11.MinimumDegree G ≤ n ∧
        ∀ i j, i ≠ j → ((∑ k, R i k * R j k) ≠ 0 ↔ G.Adj i j)) :
    NLA.Statements.SP11.Target := by
  intro n hn G
  obtain ⟨d, R, hd, hR⟩ := h n hn G
  exact ⟨gram R, gram_hasPattern G R hR, minDegree_le_gram_nullity G R hd⟩

#assert_trust kernel gram_hasPattern
#assert_trust kernel gram_rank_le
#assert_trust kernel minDegree_le_gram_nullity
#assert_trust kernel target_of_faithful_representations
#print axioms target_of_faithful_representations

end NLA.Proofs.SP11
