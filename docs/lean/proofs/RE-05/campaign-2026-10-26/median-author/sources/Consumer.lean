import NLA.Proofs.RE05.MedianRobust
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

example (l : List ℝ) (hs : l.Pairwise (· ≤ ·)) (k : ℕ) (hk : k < l.length)
    (b : ℝ) (hc : k + 1 ≤ l.countP (fun x => decide (x ≤ b))) : l[k] ≤ b :=
  sorted_get_le_of_count l hs k hk b hc

example (s t : Finset (Fin 15)) (hs : 8 ≤ s.card) (ht : 8 ≤ t.card) :
    ∃ j, j ∈ s ∧ j ∈ t := eight_intersection s t hs ht

example {n q : ℕ} (P : Basis n q) (schedule : Fin 15 → Plan n)
    (responses : List (Fin n → ℝ)) (center : Fin (q + 1) → ℝ) (ρ : ℝ)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses j) center ≤ ρ).card) :
    coefficientDistance P (postprocess P schedule responses) center ≤ 3 * ρ :=
  postprocess_distance_of_eight P schedule responses center ρ hgood

example {n q : ℕ} (P : Basis n q) (A : Square n)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 ≤
      (1 + squaredAccuracy ε) * NLA.Computation.LinearFamilyQuery.optimum P A ^ 2).card) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (postprocess P schedule responses)) ≤
      (1 + ε) * NLA.Computation.LinearFamilyQuery.optimum P A :=
  postprocess_relative_of_eight P A schedule responses ε hε hgood

-- Exact membership/zero-optimum specialization of the same actual selector.
example {n q : ℕ} (P : Basis n q) (A : Square n)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hz : NLA.Computation.LinearFamilyQuery.optimum P A = 0)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 ≤
      (1 + squaredAccuracy ε) * NLA.Computation.LinearFamilyQuery.optimum P A ^ 2).card) :
    A = represent P (postprocess P schedule responses) := by
  have h := postprocess_relative_of_eight P A schedule responses ε hε hgood
  rw [hz, mul_zero] at h
  apply (frobenius_eq_zero_iff A _).mp
  exact le_antisymm h (Real.sqrt_nonneg _)

#assert_trust kernel sorted_get_le_of_count
#assert_trust kernel sorted_count_le_get
#assert_trust kernel medianRadius_le_of_eight
#assert_trust kernel medianRadius_eight
#assert_trust kernel foldl_score_minimum
#assert_trust kernel chooseCopy_le
#assert_trust kernel coefficientDistance_symm
#assert_trust kernel coefficientDistance_triangle
#assert_trust kernel eight_intersection
#assert_trust kernel postprocess_distance_of_eight
#assert_trust kernel postprocess_relative_of_eight
#print axioms sorted_get_le_of_count
#print axioms sorted_count_le_get
#print axioms medianRadius_le_of_eight
#print axioms medianRadius_eight
#print axioms foldl_score_minimum
#print axioms chooseCopy_le
#print axioms coefficientDistance_symm
#print axioms coefficientDistance_triangle
#print axioms eight_intersection
#print axioms postprocess_distance_of_eight
#print axioms postprocess_relative_of_eight
