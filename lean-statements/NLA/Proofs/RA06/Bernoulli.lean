import NLA.Proofs.RA06.Basic

/-! Exact finite Bernoulli marginals and expected support size. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

private def factor {n : ℕ} (q : Fin n → ℝ)
    (kept : Fin n → Bool) (i : Fin n) : ℝ :=
  if kept i = true then q i else 1 - q i

private theorem bernoulli_marginal {n : ℕ} (q : Fin n → ℝ) (i : Fin n) :
    (∑ kept : Fin n → Bool,
      (∏ j : Fin n, factor q kept j) *
        (if kept i = true then (1 : ℝ) else 0)) = q i := by
  classical
  let g : (j : Fin n) → Bool → ℝ := fun j b =>
    (if b = true then q j else 1 - q j) *
      (if j = i then (if b = true then 1 else 0) else 1)
  have hterm (kept : Fin n → Bool) :
      (∏ j : Fin n, factor q kept j) *
          (if kept i = true then (1 : ℝ) else 0) =
        ∏ j : Fin n, g j (kept j) := by
    simp only [g, factor, Finset.prod_mul_distrib]
    simp
  calc
    (∑ kept : Fin n → Bool,
      (∏ j : Fin n, factor q kept j) *
        (if kept i = true then (1 : ℝ) else 0)) =
        ∑ kept : Fin n → Bool, ∏ j : Fin n, g j (kept j) := by
      apply Finset.sum_congr rfl
      intro kept _
      exact hterm kept
    _ = ∏ j : Fin n, ∑ b : Bool, g j b := by
      simpa only using (Fintype.prod_sum g).symm
    _ = q i := by
      simp [g]

def RetainedCount {n : ℕ} (kept : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => kept i = true)).card

/-- The target's `ExpectedSize` is exactly the Bernoulli expectation of the
realized number of retained rows, even with unequal probabilities. -/
theorem expectedSize_eq_sum_count {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α : ℝ) :
    ExpectedSize A p α =
      ∑ kept : Fin n → Bool,
        OutcomeWeight A p α kept * (RetainedCount kept : ℝ) := by
  classical
  let q : Fin n → ℝ := RetentionProbability A p α
  have hcount (kept : Fin n → Bool) :
      (RetainedCount kept : ℝ) =
        ∑ i : Fin n, if kept i = true then (1 : ℝ) else 0 := by
    simp [RetainedCount]
  calc
    ExpectedSize A p α = ∑ i : Fin n, q i := rfl
    _ = ∑ i : Fin n, ∑ kept : Fin n → Bool,
          (∏ j : Fin n, factor q kept j) *
            (if kept i = true then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (bernoulli_marginal q i).symm
    _ = ∑ kept : Fin n → Bool, ∑ i : Fin n,
          (∏ j : Fin n, factor q kept j) *
            (if kept i = true then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ kept : Fin n → Bool,
          OutcomeWeight A p α kept * (RetainedCount kept : ℝ) := by
      apply Finset.sum_congr rfl
      intro kept _
      rw [hcount, Finset.mul_sum]
      rfl

/-- A pointwise lower bound on every successful outcome transfers to the
expected sample size with the exact success-probability factor. -/
theorem expectedSize_lower_of_success_count_bound {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p α ε L : ℝ)
    (hA : FullColumnRank A) (hn : 0 < n) (hd : 0 < d)
    (hα : 0 < α)
    (hcount : ∀ kept : Fin n → Bool,
      Embedding A p α ε kept → L ≤ (RetainedCount kept : ℝ)) :
    SuccessProbability A p α ε * L ≤ ExpectedSize A p α := by
  classical
  rw [expectedSize_eq_sum_count]
  unfold SuccessProbability
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro kept _
  by_cases he : Embedding A p α ε kept
  · simp only [if_pos he]
    exact mul_le_mul_of_nonneg_left (hcount kept he)
      (outcomeWeight_nonneg A p α hA hn hd hα kept)
  · simp only [if_neg he, zero_mul]
    exact mul_nonneg
      (outcomeWeight_nonneg A p α hA hn hd hα kept)
      (Nat.cast_nonneg _)

#print axioms expectedSize_eq_sum_count
#print axioms expectedSize_lower_of_success_count_bound

end NLA.Proofs.RA06
