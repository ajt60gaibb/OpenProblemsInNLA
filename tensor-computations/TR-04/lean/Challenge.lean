import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Real

/-!
  TR-04, Challenge interface.

  This file is deliberately independent of `Solution.lean`: it records the
  theorem contract against which a solution is to be compared.  The rank of
  each unfolding is left as part of the problem data, so that no informal
  rank convention is silently introduced by the challenge statement.
-/

noncomputable section
open scoped BigOperators

structure ProblemData where
  d : Nat
  h_d : 3 ≤ d
  n : Fin d → Nat
  h_n : ∀ i, 2 ≤ n i
  r : Fin (d - 1) → Nat
  h_r : ∀ j, 1 ≤ r j
  unfoldingRank :
    ((∀ i : Fin d, Fin (n i)) → ℝ) → Fin (d - 1) → Nat

abbrev Tensor (p : ProblemData) :=
  (∀ i : Fin p.d, Fin (p.n i)) → ℝ

def frobeniusSq (p : ProblemData) (A B : Tensor p) : ℝ :=
  ∑ x, (A x - B x) ^ 2

def feasible (p : ProblemData) (Y : Tensor p) : Prop :=
  ∀ j, p.unfoldingRank Y j ≤ p.r j

def optimalError (p : ProblemData) (A : Tensor p) : ℝ :=
  sInf {q : ℝ | ∃ Y : Tensor p, feasible p Y ∧ q = frobeniusSq p A Y}

def firstMode (p : ProblemData) : Fin p.d := ⟨0, Nat.lt_of_lt_of_le (by decide) p.h_d⟩

def tr04Statement : Prop :=
  ∀ p : ProblemData, ∃ algorithm : Tensor p → Tensor p × Nat,
    ∀ A : Tensor p,
      let result := algorithm A
      feasible p result.1 ∧
      ((optimalError p A > 0 →
          frobeniusSq p A result.1 < (p.d - 1 : ℝ) * optimalError p A) ∧
       (optimalError p A = 0 → result.1 = A)) ∧
      result.2 ≤ p.n (firstMode p)

theorem candidate_count_le_first_mode
    {n₁ t k : Nat} (ht : t ≤ n₁) (hk : k ≤ t) : k ≤ n₁ := by
  exact Nat.le_trans hk ht

theorem cyclic_window_count_le_first_mode
    {n₁ t : Nat} (ht : t ≤ n₁) : t ≤ n₁ := by
  exact ht

#check tr04Statement










