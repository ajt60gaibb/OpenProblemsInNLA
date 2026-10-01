import ProofProject.CircleGramPolynomial

/-! Ordinary and conjugated polynomials as finite Laurent polynomials. -/

noncomputable section

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def polynomialLaurentCoefficients (p : Polynomial ℂ) : ℤ →₀ ℂ :=
  p.toFinsupp.coeff.embDomain Nat.castEmbedding

def negativePolynomialEmbedding : ℕ ↪ ℤ :=
  ⟨fun k => -(k : ℤ) - 1, by
    intro i j h
    change -(i : ℤ) - 1 = -(j : ℤ) - 1 at h
    omega⟩

def negativePolynomialLaurentCoefficients (p : Polynomial ℂ) : ℤ →₀ ℂ :=
  (p.map (starRingEnd ℂ)).toFinsupp.coeff.embDomain negativePolynomialEmbedding

lemma polynomialLaurentCoefficients_negative (p : Polynomial ℂ) (k : ℤ) (hk : k < 0) :
    polynomialLaurentCoefficients p k = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨j, hj⟩
  change (j : ℤ) = k at hj
  omega

lemma negativePolynomialLaurentCoefficients_nonnegative (p : Polynomial ℂ) (k : ℤ)
    (hk : 0 ≤ k) : negativePolynomialLaurentCoefficients p k = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨j, hj⟩
  change -(j : ℤ) - 1 = k at hj
  omega

lemma polynomialLaurentCoefficients_eval (p : Polynomial ℂ) (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial (polynomialLaurentCoefficients p) z =
      p.eval (fourier 1 z) := by
  change (p.toFinsupp.coeff.embDomain Nat.castEmbedding).sum
      (fun k c => c * fourier k z) = _
  rw [Finsupp.sum_embDomain]
  simp only [Nat.castEmbedding_apply, circleGram_fourier_nat]
  exact (Polynomial.eval_eq_sum (p := p)).symm

lemma negativePolynomialLaurentCoefficients_eval (p : Polynomial ℂ)
    (z : AddCircle (1 : ℝ)) :
    laurentCirclePolynomial (negativePolynomialLaurentCoefficients p) z =
      fourier (-1) z * starRingEnd ℂ (p.eval (fourier 1 z)) := by
  change ((p.map (starRingEnd ℂ)).toFinsupp.coeff.embDomain negativePolynomialEmbedding).sum
      (fun k c => c * fourier k z) = _
  rw [Finsupp.sum_embDomain]
  change (p.map (starRingEnd ℂ)).sum
      (fun k c => c * fourier (-(k : ℤ) - 1) z) = _
  rw [Polynomial.sum_def, Polynomial.support_map_of_injective _ (starRingEnd ℂ).injective]
  simp only [Polynomial.coeff_map]
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show -(k : ℤ) - 1 = -1 + -(k : ℤ) by omega, fourier_add]
  simp only [fourier_neg, circleGram_fourier_nat, map_mul]
  ring

end ProofProject
