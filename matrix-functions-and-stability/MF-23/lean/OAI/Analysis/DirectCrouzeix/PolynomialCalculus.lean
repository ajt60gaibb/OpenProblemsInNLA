import OAI.Analysis.DirectCrouzeix.Resolvent

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def exteriorCorrection (h q : ℂ → ℂ) (ζ μ : ℂ) : ℂ :=
  q ζ / (h ζ - h μ) - ζ / (ζ - μ)

def exteriorKernel (h q : ℂ → ℂ) (ζ μ : ℂ) : ℝ :=
  1 + (exteriorCorrection h q ζ μ).re + (star (exteriorCorrection h q ζ μ)).re

theorem re_circle_fraction {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1)
    (hne : ζ ≠ μ) : 2 * (ζ / (ζ - μ)).re = 1 := by
  have hnζ : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq ζ = 1 by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num)
  have hnμ : μ.re ^ 2 + μ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using
      (show Complex.normSq μ = 1 by rw [Complex.normSq_eq_norm_sq, hμ]; norm_num)
  have hd : Complex.normSq (ζ - μ) ≠ 0 := by
    exact mt Complex.normSq_eq_zero.mp (sub_ne_zero.mpr hne)
  rw [Complex.div_re]
  field_simp
  simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at *
  nlinarith

theorem exteriorKernel_nonneg_off_diagonal (h q : ℂ → ℂ)
    {ζ μ : ℂ} (hζ : ‖ζ‖ = 1) (hμ : ‖μ‖ = 1) (hne : ζ ≠ μ)
    (hs : 0 ≤ (star (q ζ) * (h ζ - h μ)).re) :
    0 ≤ exteriorKernel h q ζ μ := by
  have hfrac := re_circle_fraction hζ hμ hne
  have hp : 0 ≤ (q ζ / (h ζ - h μ)).re := by
    rw [Complex.div_re, ← add_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simpa [Complex.mul_re] using hs
  simp only [exteriorKernel, exteriorCorrection, Complex.sub_re, Complex.star_def,
    Complex.conj_re]
  linarith

def coefficientEmbedding (n m : ℕ) :
    Matrix (Fin m) (Fin m) ℂ →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun B := (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' B C := Matrix.kronecker_add _ B C
  map_mul' B C := by
    simpa using Matrix.mul_kronecker_mul
      (1 : Matrix (Fin n) (Fin n) ℂ) 1 B C

def tensorPolynomial {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) →+*
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  Polynomial.eval₂RingHom' (coefficientEmbedding n m)
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) (by
      intro B
      change (1 ⊗ₖ B) * (A ⊗ₖ 1) = (A ⊗ₖ 1) * (1 ⊗ₖ B)
      rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp)

def coefficientPolynomial {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    Polynomial (Matrix (Fin m) (Fin m) ℂ) :=
  ∑ k : Fin (d + 1), Polynomial.C (B k) * Polynomial.X ^ (k : ℕ)

theorem kronecker_pow_one {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    (A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)) ^ k = (A ^ k) ⊗ₖ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← Matrix.mul_kronecker_mul]
    simp [pow_succ]

@[simp] theorem tensorPolynomial_C {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (Polynomial.C B) = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ B := by
  exact Polynomial.eval₂_C _ _

@[simp] theorem tensorPolynomial_X {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    tensorPolynomial (m := m) A Polynomial.X = A ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ) := by
  exact Polynomial.eval₂_X _ _

theorem tensorPolynomial_coefficientPolynomial {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    tensorPolynomial A (coefficientPolynomial B) = tensorEvaluation A B := by
  simp only [coefficientPolynomial, map_sum, map_mul, map_pow,
    tensorPolynomial_C, tensorPolynomial_X, kronecker_pow_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, tensorEvaluation]

theorem tensorPolynomial_mul {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F G : Polynomial (Matrix (Fin m) (Fin m) ℂ)) :
    tensorPolynomial A (F * G) = tensorPolynomial A F * tensorPolynomial A G :=
  map_mul _ _ _

end DirectCrouzeix

end

end OAI
