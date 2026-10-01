import ProofProject.WeightedCircleProjection
import ProofProject.CirclePolynomialDefs

/-!
# The ordinary polynomial of a reverse-frequency Gram weight

Mathlib's complex inner product conjugates its first argument. Consequently
the weight of `∑ j, z⁻ʲ • v j` has coefficient `inner ℂ (v i) (v j)` at
frequency `i-j`. Multiplication by `z^(n-1)` gives the polynomial below.
-/

noncomputable section

namespace ProofProject

universe u

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

/-- The shifted Gram polynomial for the negative-frequency vector polynomial. -/
def circleGramPolynomial (v : Fin n → H) : Polynomial ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    Polynomial.monomial (n - 1 + i.val - j.val) (inner ℂ (v i) (v j))

lemma circleGramPolynomial_natDegree_le (v : Fin n → H) (hn : 1 ≤ n) :
    (circleGramPolynomial v).natDegree ≤ 2 * (n - 1) := by
  unfold circleGramPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

lemma circleGram_fourier_nat (k : ℕ) (z : AddCircle (1 : ℝ)) :
    fourier (k : ℤ) z = (fourier 1 z) ^ k := by
  induction k with
  | zero => simp
  | succ k hk => rw [Nat.cast_add, Nat.cast_one, fourier_add, hk, pow_succ]

set_option backward.isDefEq.respectTransparency.types false in
/-- The complex form of the exact finite Gram expansion. -/
lemma reverseCircleWeight_complex_eq (v : Fin n → H) (z : AddCircle (1 : ℝ)) :
    (reverseCircleWeight v z : ℂ) =
      ∑ i : Fin n, ∑ j : Fin n,
        fourier ((i.val : ℤ) - (j.val : ℤ)) z * inner ℂ (v i) (v j) := by
  have hself : (reverseCircleWeight v z : ℂ) =
      inner ℂ (reverseCirclePolynomial v z) (reverseCirclePolynomial v z) := by
    simpa only [reverseCircleWeight, Complex.ofReal_pow] using!
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (reverseCirclePolynomial v z)).symm
  rw [hself]
  unfold reverseCirclePolynomial
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_left, inner_smul_right]
  have hc : starRingEnd ℂ (fourier (-(i.val : ℤ)) z) = fourier (i.val : ℤ) z := by
    rw [fourier_neg]
    simp
  rw [hc, sub_eq_add_neg, fourier_add]
  ring

lemma circleGramPolynomial_eval_fourier (v : Fin n → H) (hn : 1 ≤ n)
    (z : AddCircle (1 : ℝ)) :
    (circleGramPolynomial v).eval (fourier 1 z) =
      (fourier 1 z) ^ (n - 1) * (reverseCircleWeight v z : ℂ) := by
  simp only [circleGramPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [reverseCircleWeight_complex_eq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← circleGram_fourier_nat, ← circleGram_fourier_nat]
  have hexp : ((n - 1 + i.val - j.val : ℕ) : ℤ) =
      ((n - 1 : ℕ) : ℤ) + ((i.val : ℤ) - (j.val : ℤ)) := by omega
  rw [hexp, fourier_add]
  ring

/-- A strictly positive reverse-frequency weight gives exactly the positive
circle-phase premise of the finite Fejér–Riesz factorization. -/
theorem circleGramPolynomial_positive_phase (v : Fin n → H) (hn : 1 ≤ n)
    (hpos : ∀ z : AddCircle (1 : ℝ), 0 < reverseCircleWeight v z) :
    HasPositiveCirclePhase (n - 1) (circleGramPolynomial v) := by
  intro z hz
  let zc : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨t, ht⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective zc
  have hfourier : fourier 1 t = z := by
    rw [fourier_one, ← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact congrArg (fun c : Circle => (c : ℂ)) ht
  refine ⟨reverseCircleWeight v t, hpos t, ?_⟩
  simpa only [hfourier] using circleGramPolynomial_eval_fourier v hn t

theorem circleGramPolynomial_positive_phase_of_tail_bound {v : Fin n → H} {K : ℝ}
    (h : HasSynthesisTailBound v K) (hv : ∃ j, v j ≠ 0) :
    HasPositiveCirclePhase (n - 1) (circleGramPolynomial v) := by
  have hn : 1 ≤ n := by obtain ⟨j, _⟩ := hv; have := j.isLt; omega
  exact circleGramPolynomial_positive_phase v hn (reverseCircleWeight_pos h hv)

end ProofProject
