import Mathlib

/-!
# One polynomial-fraction step of the Schur recursion

This file proves the disk bound, nonvanishing denominator, and coefficient
congruence for one inverse Schur transform. It does not assert existence of
Schur data or of an interpolating fraction.
-/

noncomputable section

namespace ProofProject

open Polynomial

def schurFractionNumerator (a : ℂ) (A₁ B₁ : Polynomial ℂ) : Polynomial ℂ :=
  C a * B₁ + X * A₁

def schurFractionDenominator (a : ℂ) (A₁ B₁ : Polynomial ℂ) : Polynomial ℂ :=
  B₁ + C (starRingEnd ℂ a) * X * A₁

/-- The exact disk Möbius norm identity, before taking a quotient. -/
lemma schurFraction_norm_sq_sub (a u v : ℂ) :
    ‖v + starRingEnd ℂ a * u‖ ^ 2 - ‖a * v + u‖ ^ 2 =
      (1 - ‖a‖ ^ 2) * (‖v‖ ^ 2 - ‖u‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma schurFraction_scalar_norm_le {a u v : ℂ} (ha : ‖a‖ ≤ 1)
    (huv : ‖u‖ ≤ ‖v‖) : ‖a * v + u‖ ≤ ‖v + starRingEnd ℂ a * u‖ := by
  have ha2 : 0 ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have huv2 : 0 ≤ ‖v‖ ^ 2 - ‖u‖ ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) huv 2)
  have hnonneg := mul_nonneg ha2 huv2
  have hid := schurFraction_norm_sq_sub a u v
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith

lemma schurFraction_norm_le {a : ℂ} (ha : ‖a‖ ≤ 1) (A₁ B₁ : Polynomial ℂ)
    (hAB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖A₁.eval z‖ ≤ ‖B₁.eval z‖)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(schurFractionNumerator a A₁ B₁).eval z‖ ≤
      ‖(schurFractionDenominator a A₁ B₁).eval z‖ := by
  have hu : ‖z * A₁.eval z‖ ≤ ‖B₁.eval z‖ := by
    calc
      _ = ‖z‖ * ‖A₁.eval z‖ := norm_mul _ _
      _ ≤ 1 * ‖A₁.eval z‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ ‖B₁.eval z‖ := by simpa only [one_mul] using hAB z hz
  simpa only [schurFractionNumerator, schurFractionDenominator,
    eval_add, eval_mul, eval_C, eval_X, mul_assoc] using schurFraction_scalar_norm_le ha hu

/-- Strictness is needed only for the denominator: the new denominator has
no zeros even when the child fraction attains norm one on the boundary. -/
lemma schurFraction_denominator_ne_zero {a : ℂ} (ha : ‖a‖ < 1)
    (A₁ B₁ : Polynomial ℂ)
    (hB : ∀ z : ℂ, ‖z‖ ≤ 1 → B₁.eval z ≠ 0)
    (hAB : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖A₁.eval z‖ ≤ ‖B₁.eval z‖)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : (schurFractionDenominator a A₁ B₁).eval z ≠ 0 := by
  have hu : ‖z * A₁.eval z‖ ≤ ‖B₁.eval z‖ := by
    calc
      _ = ‖z‖ * ‖A₁.eval z‖ := norm_mul _ _
      _ ≤ 1 * ‖A₁.eval z‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ ‖B₁.eval z‖ := by simpa only [one_mul] using hAB z hz
  have hsmall : ‖starRingEnd ℂ a * (z * A₁.eval z)‖ < ‖B₁.eval z‖ := by
    calc
      _ = ‖a‖ * ‖z * A₁.eval z‖ := by rw [norm_mul, RCLike.norm_conj]
      _ ≤ ‖a‖ * ‖B₁.eval z‖ := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ < 1 * ‖B₁.eval z‖ := mul_lt_mul_of_pos_right ha (norm_pos_iff.mpr (hB z hz))
      _ = ‖B₁.eval z‖ := one_mul _
  intro he
  simp only [schurFractionDenominator, eval_add, eval_mul, eval_C, eval_X, mul_assoc] at he
  have hnorm : ‖B₁.eval z‖ = ‖starRingEnd ℂ a * (z * A₁.eval z)‖ := by
    rw [eq_neg_of_add_eq_zero_left he, norm_neg]
  exact (ne_of_lt hsmall) hnorm.symm

/-- Lifting the child coefficient congruence through the inverse Schur step.
The first premise is the defining finite Schur relation for the data `P,S`.
It has a minus sign before `X*S*(1-conj(a)*P)`. -/
theorem schurFraction_congruence (m : ℕ) (a : ℂ) (A₁ B₁ P S : Polynomial ℂ)
    (hP : X ^ (m + 1) ∣ P - C a - X * S * (1 - C (starRingEnd ℂ a) * P))
    (hS : X ^ m ∣ A₁ - B₁ * S) :
    X ^ (m + 1) ∣ schurFractionNumerator a A₁ B₁ -
      schurFractionDenominator a A₁ B₁ * P := by
  have hXS : X ^ (m + 1) ∣ X * (A₁ - B₁ * S) := by
    obtain ⟨Q, hQ⟩ := hS
    refine ⟨Q, ?_⟩
    rw [hQ, pow_succ]
    ring
  have hid : schurFractionNumerator a A₁ B₁ - schurFractionDenominator a A₁ B₁ * P =
      (-B₁) * (P - C a - X * S * (1 - C (starRingEnd ℂ a) * P)) +
        (X * (A₁ - B₁ * S)) * (1 - C (starRingEnd ℂ a) * P) := by
    unfold schurFractionNumerator schurFractionDenominator
    ring
  rw [hid]
  exact dvd_add (dvd_mul_of_dvd_right hP _) (dvd_mul_of_dvd_left hXS _)

end ProofProject
