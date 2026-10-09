import ProofProject.FiniteToeplitz

/-!
# Polynomial algebra of the finite Toeplitz action

The Toeplitz output is the first coefficients of a polynomial product. This
identification proves multiplication and congruence modulo `X^N`, for arbitrary
polynomial degrees and including the empty coefficient space.
-/

noncomputable section

open Polynomial

namespace ProofProject

/-- The polynomial of a finite coefficient vector. -/
def finiteCoefficientPolynomial {N : ℕ} (x : Fin N → ℂ) : Polynomial ℂ :=
  ∑ j : Fin N, monomial j.val (x j)

lemma finiteCoefficientPolynomial_coeff {N : ℕ} (x : Fin N → ℂ) (i : Fin N) :
    (finiteCoefficientPolynomial x).coeff i.val = x i := by
  classical
  simp only [finiteCoefficientPolynomial, finsetSum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hv : j.val ≠ i.val := fun hh => hji (Fin.ext hh)
    simp only [coeff_monomial, if_neg hv]
  · simp

/-- Multiplication by `P` followed by coefficient truncation is precisely the
lower triangular Toeplitz action attached to `P.coeff`. -/
lemma finiteToeplitzApply_eq_coeff_mul {N : ℕ} (P : Polynomial ℂ)
    (x : Fin N → ℂ) (i : Fin N) :
    finiteToeplitzApply P.coeff x i = (P * finiteCoefficientPolynomial x).coeff i.val := by
  simp only [finiteToeplitzApply, finiteCoefficientPolynomial, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [← C_mul_X_pow_eq_monomial, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C]

lemma X_pow_dvd_finiteCoefficientPolynomial_action_sub {N : ℕ}
    (P : Polynomial ℂ) (x : Fin N → ℂ) :
    X ^ N ∣ finiteCoefficientPolynomial (finiteToeplitzApply P.coeff x) -
      P * finiteCoefficientPolynomial x := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  let i : Fin N := ⟨k, hk⟩
  have he := finiteCoefficientPolynomial_coeff (finiteToeplitzApply P.coeff x) i
  rw [finiteToeplitzApply_eq_coeff_mul] at he
  rw [coeff_sub]
  exact sub_eq_zero.mpr he

/-- Congruent polynomials have identical actions on the first `N` coefficients. -/
lemma finiteToeplitzApply_poly_congr {N : ℕ} {P Q : Polynomial ℂ}
    (h : X ^ N ∣ P - Q) (x : Fin N → ℂ) :
    finiteToeplitzApply P.coeff x = finiteToeplitzApply Q.coeff x := by
  funext i
  apply finiteToeplitzApply_congr_prefix _ x i
  intro k hk
  exact sub_eq_zero.mp (by simpa only [coeff_sub] using (X_pow_dvd_iff.mp h) k hk)

/-- The full finite polynomial multiplication identity, with no degree assumptions. -/
lemma finiteToeplitzApply_poly_mul {N : ℕ} (P Q : Polynomial ℂ) (x : Fin N → ℂ) :
    finiteToeplitzApply (P * Q).coeff x =
      finiteToeplitzApply P.coeff (finiteToeplitzApply Q.coeff x) := by
  have hd : X ^ N ∣ P * finiteCoefficientPolynomial (finiteToeplitzApply Q.coeff x) -
      P * (Q * finiteCoefficientPolynomial x) := by
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right (X_pow_dvd_finiteCoefficientPolynomial_action_sub Q x) P
  funext i
  have hc := (X_pow_dvd_iff.mp hd) i.val i.isLt
  rw [coeff_sub, sub_eq_zero] at hc
  calc
    finiteToeplitzApply (P * Q).coeff x i =
        (P * (Q * finiteCoefficientPolynomial x)).coeff i.val := by
      rw [finiteToeplitzApply_eq_coeff_mul, mul_assoc]
    _ = (P * finiteCoefficientPolynomial (finiteToeplitzApply Q.coeff x)).coeff i.val := hc.symm
    _ = finiteToeplitzApply P.coeff (finiteToeplitzApply Q.coeff x) i :=
      (finiteToeplitzApply_eq_coeff_mul P _ i).symm

@[simp]
lemma finiteToeplitzApply_poly_one {N : ℕ} (x : Fin N → ℂ) :
    finiteToeplitzApply (1 : Polynomial ℂ).coeff x = x := by
  funext i
  rw [finiteToeplitzApply_eq_coeff_mul, one_mul, finiteCoefficientPolynomial_coeff]

@[simp]
lemma finiteToeplitzApply_poly_zero {N : ℕ} (x : Fin N → ℂ) :
    finiteToeplitzApply (0 : Polynomial ℂ).coeff x = 0 := by
  funext i
  simp only [finiteToeplitzApply_eq_coeff_mul, zero_mul, coeff_zero, Pi.zero_apply]

lemma finiteToeplitzApply_poly_add {N : ℕ} (P Q : Polynomial ℂ) (x : Fin N → ℂ) :
    finiteToeplitzApply (P + Q).coeff x =
      fun i => finiteToeplitzApply P.coeff x i + finiteToeplitzApply Q.coeff x i := by
  funext i
  simp only [finiteToeplitzApply_eq_coeff_mul, add_mul, coeff_add]

lemma finiteToeplitzApply_poly_sub {N : ℕ} (P Q : Polynomial ℂ) (x : Fin N → ℂ) :
    finiteToeplitzApply (P - Q).coeff x =
      fun i => finiteToeplitzApply P.coeff x i - finiteToeplitzApply Q.coeff x i := by
  funext i
  simp only [finiteToeplitzApply_eq_coeff_mul, sub_mul, coeff_sub]

lemma finiteToeplitzApply_poly_C {N : ℕ} (a : ℂ) (x : Fin N → ℂ) :
    finiteToeplitzApply (C a).coeff x = fun i => a * x i := by
  funext i
  rw [finiteToeplitzApply_eq_coeff_mul, coeff_C_mul, finiteCoefficientPolynomial_coeff]

lemma finiteToeplitzApply_poly_C_mul {N : ℕ} (a : ℂ) (P : Polynomial ℂ) (x : Fin N → ℂ) :
    finiteToeplitzApply (C a * P).coeff x = fun i => a * finiteToeplitzApply P.coeff x i := by
  rw [finiteToeplitzApply_poly_mul, finiteToeplitzApply_poly_C]

/-- An inverse modulo `X^N` is a right inverse of the finite Toeplitz action. -/
lemma finiteToeplitzApply_poly_rightInverse {N : ℕ} {Q R : Polynomial ℂ}
    (h : X ^ N ∣ Q * R - 1) (x : Fin N → ℂ) :
    finiteToeplitzApply Q.coeff (finiteToeplitzApply R.coeff x) = x := by
  rw [← finiteToeplitzApply_poly_mul, finiteToeplitzApply_poly_congr h,
    finiteToeplitzApply_poly_one]

end ProofProject
