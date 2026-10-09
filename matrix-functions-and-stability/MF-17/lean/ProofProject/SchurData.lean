import Mathlib

/-!
# Finite polynomial inverse and Schur data

A nonzero constant coefficient gives an inverse modulo every power of `X`
by a finite geometric sum. Applying it to `1-conj(a)*P` produces the finite
Schur data congruence. This module makes no contraction or interpolation claim.
-/

noncomputable section

open Polynomial

namespace ProofProject

/-- A finite geometric inverse of a polynomial, modulo `X^m`. -/
def polynomialGeometricInverse (Q : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  C ((Q.coeff 0)⁻¹) * ∑ j ∈ Finset.range m, (1 - C ((Q.coeff 0)⁻¹) * Q) ^ j

lemma polynomial_mul_geometricInverse (Q : Polynomial ℂ) (m : ℕ) :
    Q * polynomialGeometricInverse Q m =
      1 - (1 - C ((Q.coeff 0)⁻¹) * Q) ^ m := by
  let W : Polynomial ℂ := 1 - C ((Q.coeff 0)⁻¹) * Q
  calc
    Q * polynomialGeometricInverse Q m = (1 - W) * ∑ j ∈ Finset.range m, W ^ j := by
      dsimp [polynomialGeometricInverse, W]
      ring
    _ = 1 - W ^ m := mul_neg_geom_sum W m

/-- The finite geometric inverse has the required coefficient congruence,
including the vacuous modulus `X^0=1`. -/
theorem polynomialGeometricInverse_spec (Q : Polynomial ℂ) (hQ : Q.coeff 0 ≠ 0)
    (m : ℕ) : X ^ m ∣ Q * polynomialGeometricInverse Q m - 1 := by
  have hW : (X : Polynomial ℂ) ∣ 1 - C ((Q.coeff 0)⁻¹) * Q := by
    apply X_dvd_iff.mpr
    simp only [coeff_sub, coeff_one_zero, mul_coeff_zero, coeff_C_zero,
      inv_mul_cancel₀ hQ, sub_self]
  have hp := pow_dvd_pow_of_dvd hW m
  rw [polynomial_mul_geometricInverse]
  convert dvd_neg.mpr hp using 1 <;> ring

/-- A polynomial with nonzero constant coefficient admits an inverse modulo
any prescribed power of the indeterminate. -/
theorem exists_polynomial_inverse_mod_X_pow (Q : Polynomial ℂ)
    (hQ : Q.coeff 0 ≠ 0) (m : ℕ) :
    ∃ R : Polynomial ℂ, X ^ m ∣ Q * R - 1 :=
  ⟨polynomialGeometricInverse Q m, polynomialGeometricInverse_spec Q hQ m⟩

/-- The first Schur denominator has nonzero constant coefficient whenever
the initial coefficient lies strictly inside the unit disk. -/
lemma schurData_denominator_coeff_zero_ne {P : Polynomial ℂ} {a : ℂ}
    (ha0 : P.coeff 0 = a) (ha : ‖a‖ < 1) :
    (1 - C (starRingEnd ℂ a) * P).coeff 0 ≠ 0 := by
  have hδ : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hnorm : starRingEnd ℂ a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [coeff_sub, coeff_one_zero, mul_coeff_zero, coeff_C_zero, ha0, hnorm,
    ← Complex.ofReal_one, ← Complex.ofReal_sub]
  exact Complex.ofReal_ne_zero.mpr hδ.ne'

/-- Construct the reduced Schur data purely at the finite coefficient level.
No boundedness assertion is made here; that comes from the Toeplitz energy step. -/
theorem exists_schurData_congruence (m : ℕ) (P : Polynomial ℂ) {a : ℂ}
    (ha0 : P.coeff 0 = a) (ha : ‖a‖ < 1) :
    ∃ S : Polynomial ℂ, X ^ (m + 1) ∣
      P - C a - X * S * (1 - C (starRingEnd ℂ a) * P) := by
  let Q : Polynomial ℂ := 1 - C (starRingEnd ℂ a) * P
  obtain ⟨R, hR⟩ := exists_polynomial_inverse_mod_X_pow Q
    (schurData_denominator_coeff_zero_ne ha0 ha) (m + 1)
  have hX : (X : Polynomial ℂ) ∣ (P - C a) * R := by
    apply X_dvd_iff.mpr
    simp only [mul_coeff_zero, coeff_sub, coeff_C_zero, ha0, sub_self, zero_mul]
  obtain ⟨S, hS⟩ := hX
  refine ⟨S, ?_⟩
  change X ^ (m + 1) ∣ P - C a - X * S * Q
  have he : P - C a - X * S * Q = -(P - C a) * (Q * R - 1) := by
    rw [← hS]
    ring
  rw [he]
  exact dvd_mul_of_dvd_right hR _

end ProofProject
