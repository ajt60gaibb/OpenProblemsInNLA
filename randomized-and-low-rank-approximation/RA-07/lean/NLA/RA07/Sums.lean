/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Finite-sum certificate for Matthew J. Colbrook's affirmative resolution of RA-07.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA07.Algebra

set_option autoImplicit false
open scoped BigOperators Polynomial Classical
noncomputable section

namespace NLA.RA07
open Polynomial

theorem finite_product_derivatives {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∏ i ∈ s, (1 + C (x i) * X)).derivative.eval 0 = ∑ i ∈ s, x i ∧
    (∏ i ∈ s, (1 + C (x i) * X)).derivative.derivative.eval 0 =
      (∑ i ∈ s, x i) ^ 2 - ∑ i ∈ s, x i ^ 2 ∧
    (∏ i ∈ s, (1 + C (x i) * X)).derivative.derivative.derivative.eval 0 =
      (∑ i ∈ s, x i) ^ 3 - 3 * (∑ i ∈ s, x i) * (∑ i ∈ s, x i ^ 2) +
        2 * ∑ i ∈ s, x i ^ 3 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rcases ih with ⟨h1, h2, h3⟩
    have h0 : (∏ i ∈ s, (1 + C (x i) * X)).eval 0 = 1 := by
      simp only [eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X,
        mul_zero, add_zero, Finset.prod_const_one]
    simp only [Finset.prod_insert ha, Finset.sum_insert ha,
      derivative_mul, derivative_add, derivative_one, derivative_C, derivative_X,
      derivative_zero, eval_add, eval_mul, eval_zero, eval_one, eval_C, eval_X,
      h0, h1, h2, h3]
    constructor
    · ring
    constructor <;> ring

theorem generating_derivatives {m : ℕ} (μ : Fin m → ℝ) :
    (generatingPolynomial μ).derivative.eval 0 = powerSum μ 1 ∧
    (generatingPolynomial μ).derivative.derivative.eval 0 =
      powerSum μ 1 ^ 2 - powerSum μ 2 ∧
    (generatingPolynomial μ).derivative.derivative.derivative.eval 0 =
      powerSum μ 1 ^ 3 - 3 * powerSum μ 1 * powerSum μ 2 + 2 * powerSum μ 3 := by
  simpa only [generatingPolynomial, powerSum, pow_one] using
    finite_product_derivatives (Finset.univ : Finset (Fin m)) μ

theorem sum_strict_upper_half {m : ℕ} (f : Fin m → Fin m → ℝ)
    (hs : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0) :
    (∑ a : Fin m, ∑ b : Fin m, f a b) =
      2 * ∑ a : Fin m, ∑ b ∈ (Finset.univ : Finset (Fin m)).filter (fun b => a < b),
        f a b := by
  have hsplit (a b : Fin m) : f a b =
      (if a < b then f a b else 0) + (if b < a then f b a else 0) := by
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt_of_ge h.le]
    · subst b; simp [hd]
    · simp [h, not_lt_of_ge h.le, hs]
  calc
    _ = ∑ a : Fin m, ∑ b : Fin m,
        ((if a < b then f a b else 0) + (if b < a then f b a else 0)) := by
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsplit a b
    _ = (∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0) +
        (∑ a : Fin m, ∑ b : Fin m, if b < a then f b a else 0) := by
      simp only [Finset.sum_add_distrib]
    _ = (∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0) +
        (∑ a : Fin m, ∑ b : Fin m, if a < b then f a b else 0) := by
      congr 1
      exact Finset.sum_comm
    _ = _ := by
      simp only [Finset.sum_filter]
      ring

theorem pair_gap_identity {m : ℕ} (μ : Fin m → ℝ) :
    powerSum μ 1 * powerSum μ 3 - powerSum μ 2 ^ 2 = pairGap μ := by
  let f (a b : Fin m) : ℝ := μ a * μ b * (μ a - μ b) ^ 2
  have hs (a b : Fin m) : f a b = f b a := by dsimp [f]; ring
  have hd (a : Fin m) : f a a = 0 := by simp [f]
  have hhalf : (∑ a : Fin m, ∑ b : Fin m, f a b) = 2 * pairGap μ :=
    sum_strict_upper_half f hs hd
  have hexpand : (∑ a : Fin m, ∑ b : Fin m, f a b) =
      2 * (powerSum μ 1 * powerSum μ 3 - powerSum μ 2 ^ 2) := by
    calc
      _ = ∑ a : Fin m, ∑ b : Fin m,
          (μ a ^ 3 * μ b + μ a * μ b ^ 3 - 2 * μ a ^ 2 * μ b ^ 2) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        dsimp [f]
        ring
      _ = _ := by
        simp only [powerSum, pow_one, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul]
        ring
  linarith

theorem sum_square_difference_pair {m : ℕ} (μ : Fin m → ℝ) :
    powerSum μ 1 ^ 2 - powerSum μ 2 =
      2 * ∑ a : Fin m, ∑ b ∈ (Finset.univ : Finset (Fin m)).filter (fun b => a < b),
        μ a * μ b := by
  let f (a b : Fin m) : ℝ := if a = b then 0 else μ a * μ b
  have hs (a b : Fin m) : f a b = f b a := by simp [f, eq_comm, mul_comm]
  have hd (a : Fin m) : f a a = 0 := by simp [f]
  have hhalf := sum_strict_upper_half f hs hd
  have he : (∑ a : Fin m, ∑ b : Fin m, f a b) + powerSum μ 2 = powerSum μ 1 ^ 2 := by
    calc
      _ = ∑ a : Fin m, ∑ b : Fin m, (f a b + if a = b then μ a ^ 2 else 0) := by
        simp [powerSum, Finset.sum_add_distrib]
      _ = ∑ a : Fin m, ∑ b : Fin m, μ a * μ b := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        by_cases hab : a = b
        · subst b; simp [f, pow_two]
        · simp [f, hab]
      _ = _ := by
        simp only [powerSum, pow_one, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hordered :
      (∑ a : Fin m, ∑ b ∈ (Finset.univ : Finset (Fin m)).filter (fun b => a < b), f a b) =
      ∑ a : Fin m, ∑ b ∈ (Finset.univ : Finset (Fin m)).filter (fun b => a < b), μ a * μ b := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b hb
    simp only [f, if_neg (ne_of_lt (Finset.mem_filter.mp hb).2)]
  rw [hordered] at hhalf
  linarith

theorem power_sum_certificate_proved {m : ℕ} (μ : Fin m → ℝ)
    (hm : 2 ≤ m) (hμ : ∀ a, 0 < μ a) :
    0 < certificateDenominator μ ∧
    powerSum μ 1 * powerSum μ 3 - powerSum μ 2 ^ 2 = pairGap μ ∧
    0 ≤ pairGap μ := by
  have hs1 : 0 < powerSum μ 1 := by
    simp only [powerSum, pow_one]
    apply Finset.sum_pos (fun a _ => hμ a)
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hs2 : 0 < powerSum μ 1 ^ 2 - powerSum μ 2 := by
    rw [sum_square_difference_pair μ]
    apply mul_pos (by norm_num)
    apply Finset.sum_pos'
    · intro a _
      exact Finset.sum_nonneg fun b _ => mul_nonneg (hμ a).le (hμ b).le
    · let a : Fin m := ⟨0, by omega⟩
      let b : Fin m := ⟨1, by omega⟩
      refine ⟨a, Finset.mem_univ _, ?_⟩
      apply Finset.sum_pos'
      · intro b _
        exact mul_nonneg (hμ a).le (hμ b).le
      · exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change 0 < 1; omega⟩,
          mul_pos (hμ a) (hμ b)⟩
  refine ⟨mul_pos hs1 hs2, pair_gap_identity μ, ?_⟩
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (mul_nonneg (hμ a).le (hμ b).le) (sq_nonneg _)

end NLA.RA07
