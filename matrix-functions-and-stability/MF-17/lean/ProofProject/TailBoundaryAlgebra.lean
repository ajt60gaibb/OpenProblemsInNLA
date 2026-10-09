import ProofProject.EndpointDeficit
import ProofProject.FiniteMomentOrthogonality

/-! Coefficient splits and the two adjacent-tail boundary statements. -/

noncomputable section

namespace ProofProject

def sourceTailCoefficients {n : ℕ} (c : Fin n → ℂ) (k : ℕ) (j : Fin n) : ℂ :=
  if k ≤ j.val then c j else 0

def sourceHeadCoefficients {n : ℕ} (c : Fin n → ℂ) (k : ℕ) (j : Fin n) : ℂ :=
  if j.val < k then c j else 0

lemma sourceTailCoefficients_support {n k : ℕ} (c : Fin n → ℂ) (j : Fin n)
    (hj : sourceTailCoefficients c k j ≠ 0) : k ≤ j.val := by
  by_contra h
  exact hj (if_neg h)

lemma sourceHeadCoefficients_support {n k : ℕ} (c : Fin n → ℂ) (j : Fin n)
    (hj : sourceHeadCoefficients c k j ≠ 0) : j.val < k := by
  by_contra h
  exact hj (if_neg h)

lemma sourceTailCoefficients_add_head {n : ℕ} (c : Fin n → ℂ) (k : ℕ) :
    sourceTailCoefficients c k + sourceHeadCoefficients c k = c := by
  funext j
  by_cases h : k ≤ j.val
  · simp [sourceTailCoefficients, sourceHeadCoefficients, h, Nat.not_lt.mpr h]
  · simp [sourceTailCoefficients, sourceHeadCoefficients, h, Nat.lt_of_not_ge h]

lemma sourcePolynomial_add {n : ℕ} (a b : Fin n → ℂ) (θ : ℝ) :
    sourcePolynomial (a + b) θ = sourcePolynomial a θ + sourcePolynomial b θ := by
  simp only [sourcePolynomial, Pi.add_apply, add_mul, Finset.sum_add_distrib]

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

lemma finiteSynthesis_tailCoefficients (f : Fin n → H) (c : Fin n → ℂ) (k : ℕ) :
    finiteSynthesis f (sourceTailCoefficients c k) = synthesisTail f c k := by
  simp only [finiteSynthesis, sourceTailCoefficients, synthesisTail, ite_smul, zero_smul]

lemma finiteSynthesis_update (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) (t : ℂ) :
    finiteSynthesis f (Function.update a i t) = replicationBase f a i + t • f i := by
  classical
  have heq : (fun j => Function.update a i t j • f j) =
      (fun j => (if j = i then 0 else a j • f j) + if j = i then t • f i else 0) := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  rw [finiteSynthesis, heq, Finset.sum_add_distrib]
  simp only [replicationBase, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma synthesisTail_update_succ (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) (t : ℂ) :
    synthesisTail f (Function.update a i t) (i.val + 1) = replicationTail f a i := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.val + 1 ≤ j.val
  · have hij : i < j := by exact h
    have hji : j ≠ i := ne_of_gt hij
    simp only [h, ite_true, hij, Function.update_of_ne hji]
  · have hij : ¬ i < j := by exact h
    simp only [h, ite_false, hij]

lemma synthesisTail_update_self (f : Fin n → H) (a : Fin n → ℂ) (i : Fin n) (t : ℂ) :
    synthesisTail f (Function.update a i t) i.val = replicationTail f a i + t • f i := by
  have h := synthesisTail_sub_succ f (Function.update a i t) i
  rw [synthesisTail_update_succ, Function.update_self] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- Adjacent-tail estimates for arbitrary polynomials give exactly the two
endpoint inequalities used by coefficient replication. -/
theorem hasBoundaryEstimate_of_adjacent_tails
    (f : Fin n → H) (M B : ℝ)
    (h : ∀ (c : Fin n → ℂ) (i : Fin n) (k : ℕ), i.val ≤ k → k ≤ i.val + 1 →
      ‖c i‖ ^ 2 + ‖inner ℂ (f i) (synthesisTail f c k)‖ ^ 2 ≤
        B * (M ^ 2 * ‖finiteSynthesis f c‖ ^ 2 - ‖synthesisTail f c k‖ ^ 2)) :
    HasBoundaryEstimate f M B := by
  intro a i t
  constructor
  · simpa only [Function.update_self, finiteSynthesis_update, synthesisTail_update_succ,
      coefficientDeficit, zero_mul, zero_smul, add_zero] using
      h (Function.update a i t) i (i.val + 1) (by omega) le_rfl
  · simpa only [Function.update_self, finiteSynthesis_update, synthesisTail_update_self,
      coefficientDeficit, one_mul] using
      h (Function.update a i t) i i.val le_rfl (by omega)

end ProofProject
