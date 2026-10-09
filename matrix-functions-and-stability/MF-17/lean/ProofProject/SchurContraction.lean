import ProofProject.FiniteToeplitz
import ProofProject.SchurFraction
import ProofProject.SchurData
import ProofProject.ToeplitzPolynomial
import ProofProject.ToeplitzPadding

/-!
# Exact contraction in a finite Schur step

The modular inverse supplies an algebraic preimage. Its norm is never
estimated, so the shorter data retain the exact contraction constant one.
-/

noncomputable section

namespace ProofProject

open Polynomial

/-- Summing the scalar Möbius identity in the actual Euclidean energy. -/
lemma schur_energy_sub {N : ℕ} (a : ℂ) (u v : Fin N → ℂ) :
    (∑ i, ‖v i - starRingEnd ℂ a * u i‖ ^ 2) -
      (∑ i, ‖u i - a * v i‖ ^ 2) =
        (1 - ‖a‖ ^ 2) * ((∑ i, ‖v i‖ ^ 2) - ∑ i, ‖u i‖ ^ 2) := by
  rw [← Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := schurFraction_norm_sq_sub (-a) (u i) (v i)
  rw [← mul_sub]
  simpa only [map_neg, neg_mul, norm_neg, sub_eq_add_neg, add_comm] using h

lemma schur_energy_le {N : ℕ} {a : ℂ} (ha : ‖a‖ ≤ 1)
    (u v : Fin N → ℂ) (huv : (∑ i, ‖u i‖ ^ 2) ≤ ∑ i, ‖v i‖ ^ 2) :
    (∑ i, ‖u i - a * v i‖ ^ 2) ≤
      ∑ i, ‖v i - starRingEnd ℂ a * u i‖ ^ 2 := by
  have hnonneg : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have h := mul_nonneg hnonneg (sub_nonneg.mpr huv)
  rw [← schur_energy_sub a u v] at h
  exact sub_nonneg.mp h

set_option maxHeartbeats 1000000 in
/-- A finite Schur relation transfers the exact contraction bound to the
shorter Toeplitz matrix. Neither polynomial requires a degree bound. -/
theorem schurData_toeplitz_contraction {m : ℕ} {P S : Polynomial ℂ} {a : ℂ}
    (ha0 : P.coeff 0 = a) (ha : ‖a‖ < 1)
    (hP : HasFiniteToeplitzBound P.coeff (m + 1) 1)
    (hS : X ^ (m + 1) ∣ P - C a - X * S * (1 - C (starRingEnd ℂ a) * P)) :
    HasFiniteToeplitzBound S.coeff m 1 := by
  let Q : Polynomial ℂ := 1 - C (starRingEnd ℂ a) * P
  obtain ⟨R, hR⟩ := exists_polynomial_inverse_mod_X_pow Q
    (schurData_denominator_coeff_zero_ne ha0 ha) (m + 1)
  apply HasFiniteToeplitzBound.of_X_mul
  intro y
  let x := finiteToeplitzApply R.coeff y
  have hQx : finiteToeplitzApply Q.coeff x = y :=
    finiteToeplitzApply_poly_rightInverse (Q := Q) (R := R) hR y
  have hS' : X ^ (m + 1) ∣ (P - C a) - (X * S * Q) := hS
  have hcongr := finiteToeplitzApply_poly_congr (N := m + 1)
    (P := P - C a) (Q := X * S * Q) hS' x
  have hPx : finiteToeplitzApply (P - C a).coeff x =
      finiteToeplitzApply (X * S).coeff y := by
    calc
      _ = finiteToeplitzApply (X * S * Q).coeff x :=
        hcongr
      _ = finiteToeplitzApply (X * S).coeff (finiteToeplitzApply Q.coeff x) :=
        finiteToeplitzApply_poly_mul _ _ x
      _ = _ := by rw [hQx]
  have he := schur_energy_le ha.le (finiteToeplitzApply P.coeff x) x
    (by simpa only [one_pow, one_mul] using hP x)
  have hQform : finiteToeplitzApply Q.coeff x =
      fun i => x i - starRingEnd ℂ a * finiteToeplitzApply P.coeff x i := by
    simp only [Q, finiteToeplitzApply_poly_sub, finiteToeplitzApply_poly_one,
      finiteToeplitzApply_poly_C_mul]
  have hPform : finiteToeplitzApply (P - C a).coeff x =
      fun i => finiteToeplitzApply P.coeff x i - a * x i := by
    simp only [finiteToeplitzApply_poly_sub, finiteToeplitzApply_poly_C]
  have he' : (∑ i, ‖finiteToeplitzApply (P - C a).coeff x i‖ ^ 2) ≤
      ∑ i, ‖finiteToeplitzApply Q.coeff x i‖ ^ 2 := by
    simpa only [hPform, hQform] using he
  rw [hPx, hQx] at he'
  simpa only [one_pow, one_mul] using he'

end ProofProject
