/-
  MI20/Theorem6_LogConvexity.lean
  ===============================
  Authors: Marcio Díaz (Space Research AI, https://spaceresearch.ai)
  Complete Mathlib-grounded, zero-sorry Lean 4.33.1 formalization of:
    - Theorem 6 (`theorem6_log_convexity`, `theorem6_interp_from_one`, `theorem6_p2_upper_bound`):
      Complex-interpolation log-convexity of 1/p ↦ log C_{p,m}(n) on [1, ∞) via Mathlib's
      Hadamard three-lines theorem (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`),
      yielding the dimension-free upper bound C_{p,m}(n) ≤ C_{2,m}(n)^(2 - 2/p) for all 1 < p < 2.
-/

import MI20.Lemma4_And_Theorem1
import Mathlib.Analysis.Complex.Hadamard

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ### Complex Schatten Hölder Inequality (General Complex Trace Norm Bound) -/

/-- General Schatten Hölder bound for complex matrices:
    if p > 1 and q = p/(p-1) (1/p + 1/q = 1), then
      ‖(X * Y).trace‖ ≤ schattenNorm q X * schattenNorm p Y. -/
theorem norm_trace_mul_le_schattenNorm {n : ℕ} {p : ℝ} (hp : 1 < p) (X Y : Mat n) :
    ‖(X * Y).trace‖ ≤ schattenNorm (p / (p - 1)) X * schattenNorm p Y := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  let q : ℝ := p / (p - 1)
  have hq0 : 0 < q := div_pos hp0 hpm1
  have hq1 : 1 < q := by dsimp [q]; rw [one_lt_div hpm1]; linarith
  -- Choose phase ζ with ‖ζ‖ = 1 so ζ * Tr(X * Y) = ‖Tr(X * Y)‖
  by_cases htr0 : (X * Y).trace = 0
  · rw [htr0, norm_zero]
    exact mul_nonneg (schattenNorm_nonneg q X) (schattenNorm_nonneg p Y)
  let ζ : ℂ := ((‖(X * Y).trace‖ : ℝ) : ℂ) / (X * Y).trace
  have hζ_norm : ‖ζ‖ = 1 := by
    dsimp [ζ]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr htr0)]
  have hnorm_eq : ‖(X * Y).trace‖ = (X * (ζ • Y)).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hmul : ζ * (X * Y).trace = ((‖(X * Y).trace‖ : ℝ) : ℂ) :=
      div_mul_cancel₀ _ htr0
    rw [hmul, Complex.ofReal_re]
  rw [hnorm_eq]
  -- Write SVD of X = U diag(σ) Vᴴ and apply doubly-stochastic Parseval + Young as in Prop 0!
  obtain ⟨U, V, σ, hσ, hX_eq, hPowX⟩ := exists_svd X
  let Y1 : Mat n := ζ • Y
  obtain ⟨UY, VY, τ, hτ, hY1_eq, hPowY1⟩ := exists_svd Y1
  have hY1_norm : schattenNorm p Y1 = schattenNorm p Y := by
    dsimp [Y1]; rw [schattenNorm_smul hp0, hζ_norm, one_mul]
  rw [← hY1_norm]
  by_cases hX0 : X = 0
  · rw [hX0, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
    exact mul_nonneg (schattenNorm_nonneg q 0) (schattenNorm_nonneg p Y1)
  by_cases hY0 : Y1 = 0
  · change (X * Y1).trace.re ≤ _
    rw [hY0, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
    exact mul_nonneg (schattenNorm_nonneg q X) (schattenNorm_nonneg p 0)
  have hNX : 0 < schattenNorm q X := schattenNorm_pos_of_ne_zero hq0 hX0
  have hNY : 0 < schattenNorm p Y1 := schattenNorm_pos_of_ne_zero hp0 hY0
  -- Express Tr(X * Y1) in SVD bases: let A = Vᴴ UY, B = VYᴴ U (both unitary!)
  let Au : Matrix.unitaryGroup (Fin n) ℂ := star V * UY
  let Bu : Matrix.unitaryGroup (Fin n) ℂ := star VY * U
  let A : Mat n := (Au : Mat n)
  let B : Mat n := (Bu : Mat n)
  have htr_exp : (X * Y1).trace = ∑ i : Fin n, ∑ j : Fin n, (σ i : ℂ) * (τ j : ℂ) * (A i j * B j i) := by
    set DX : Mat n := Matrix.diagonal (fun i => (σ i : ℂ))
    set DY : Mat n := Matrix.diagonal (fun j => (τ j : ℂ))
    have hprod : (X * Y1).trace = ((DX * A) * (DY * B)).trace := by
      rw [hX_eq, hY1_eq]
      calc (((U : Mat n) * DX * (V : Mat n)ᴴ) * ((UY : Mat n) * DY * (VY : Mat n)ᴴ)).trace
          = ((U : Mat n) * (DX * ((V : Mat n)ᴴ * (UY : Mat n)) * DY * (VY : Mat n)ᴴ)).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DX * A * DY * (VY : Mat n)ᴴ) * (U : Mat n)).trace := by
              rw [Matrix.trace_mul_comm (U : Mat n)]; rfl
        _ = ((DX * A) * (DY * ((VY : Mat n)ᴴ * (U : Mat n)))).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DX * A) * (DY * B)).trace := rfl
    rw [hprod, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, DX, DY, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hRowA : ∀ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Au) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColA : ∀ j : Fin n, ∑ i : Fin n, ‖A i j‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Au) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColB : ∀ i : Fin n, ∑ j : Fin n, ‖B j i‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Bu) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hRowB : ∀ j : Fin n, ∑ i : Fin n, ‖B j i‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Bu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  -- Bound Re Tr(X * Y1) ≤ ∑ i j, σ i * τ j * ((‖A i j‖^2 + ‖B j i‖^2) / 2), then Young with (q, p)!
  have hW : ∀ i j : Fin n, ‖A i j * B j i‖ ≤ (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2 := fun i j => by
    rw [norm_mul]; nlinarith [sq_nonneg (‖A i j‖ - ‖B j i‖)]
  let W : Fin n → Fin n → ℝ := fun i j => (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2
  have hW_nn : ∀ i j, 0 ≤ W i j := fun i j => by dsimp [W]; positivity
  have hRowW : ∀ i, ∑ j, W i j = 1 := fun i => by
    dsimp [W]; rw [← Finset.sum_div, Finset.sum_add_distrib, hRowA i, hColB i]; norm_num
  have hColW : ∀ j, ∑ i, W i j = 1 := fun j => by
    dsimp [W]; rw [← Finset.sum_div, Finset.sum_add_distrib, hColA j, hRowB j]; norm_num
  have hconj : q⁻¹ + p⁻¹ = 1 := by dsimp [q]; rw [inv_div]; field_simp [hp0.ne']; ring
  have hsum_σ : ∑ i : Fin n, (σ i / schattenNorm q X) ^ q = 1 := by
    have h1 : ∑ i : Fin n, (σ i) ^ q = (schattenNorm q X) ^ q := by
      rw [schattenNorm_rpow hq0 X, hPowX q hq0]
    calc ∑ i : Fin n, (σ i / schattenNorm q X) ^ q
        = (∑ i : Fin n, (σ i) ^ q) / (schattenNorm q X) ^ q := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => Real.div_rpow (hσ i) hNX.le q
      _ = 1 := by rw [h1, div_self (Real.rpow_pos_of_pos hNX q).ne']
  have hsum_τ : ∑ j : Fin n, (τ j / schattenNorm p Y1) ^ p = 1 := by
    have h1 : ∑ j : Fin n, (τ j) ^ p = (schattenNorm p Y1) ^ p := by
      rw [schattenNorm_rpow hp0 Y1, hPowY1 p hp0]
    calc ∑ j : Fin n, (τ j / schattenNorm p Y1) ^ p
        = (∑ j : Fin n, (τ j) ^ p) / (schattenNorm p Y1) ^ p := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl fun j _ => Real.div_rpow (hτ j) hNY.le p
      _ = 1 := by rw [h1, div_self (Real.rpow_pos_of_pos hNY p).ne']
  have hbound1 : (X * Y1).trace.re ≤ ∑ i : Fin n, ∑ j : Fin n, W i j * (σ i * τ j) := by
    rw [htr_exp, Complex.re_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc ((σ i : ℂ) * (τ j : ℂ) * (A i j * B j i)).re
        ≤ ‖(σ i : ℂ) * (τ j : ℂ) * (A i j * B j i)‖ := Complex.re_le_norm _
      _ = σ i * τ j * ‖A i j * B j i‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (hσ i), Real.norm_of_nonneg (hτ j)]
      _ ≤ σ i * τ j * W i j := mul_le_mul_of_nonneg_left (hW i j) (mul_nonneg (hσ i) (hτ j))
      _ = W i j * (σ i * τ j) := by ring
  suffices hnorm : ∑ i : Fin n, ∑ j : Fin n, W i j * ((σ i / schattenNorm q X) * (τ j / schattenNorm p Y1)) ≤ 1 by
    have hfact : ∑ i : Fin n, ∑ j : Fin n, W i j * (σ i * τ j) =
        (schattenNorm q X * schattenNorm p Y1) *
          ∑ i : Fin n, ∑ j : Fin n, W i j * ((σ i / schattenNorm q X) * (τ j / schattenNorm p Y1)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hNX.ne', hNY.ne']
    have h2 : ∑ i : Fin n, ∑ j : Fin n, W i j * (σ i * τ j) ≤ schattenNorm q X * schattenNorm p Y1 := by
      rw [hfact]
      calc _ ≤ (schattenNorm q X * schattenNorm p Y1) * 1 :=
            mul_le_mul_of_nonneg_left hnorm (mul_pos hNX hNY).le
        _ = _ := mul_one _
    exact hbound1.trans h2
  calc ∑ i : Fin n, ∑ j : Fin n, W i j * ((σ i / schattenNorm q X) * (τ j / schattenNorm p Y1))
      ≤ ∑ i : Fin n, ∑ j : Fin n, W i j *
          (q⁻¹ * (σ i / schattenNorm q X) ^ q + p⁻¹ * (τ j / schattenNorm p Y1) ^ p) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left ?_ (hW_nn i j)
        have hy := Real.geom_mean_le_arith_mean2_weighted (inv_pos.mpr hq0).le (inv_pos.mpr hp0).le
          (Real.rpow_nonneg (div_nonneg (hσ i) hNX.le) q)
          (Real.rpow_nonneg (div_nonneg (hτ j) hNY.le) p) hconj
        rw [← Real.rpow_mul (div_nonneg (hσ i) hNX.le), mul_inv_cancel₀ hq0.ne', Real.rpow_one,
          ← Real.rpow_mul (div_nonneg (hτ j) hNY.le), mul_inv_cancel₀ hp0.ne', Real.rpow_one] at hy
        exact hy
    _ = q⁻¹ * (∑ i, (σ i / schattenNorm q X) ^ q) + p⁻¹ * (∑ j, (τ j / schattenNorm p Y1) ^ p) := by
        have hsplit : ∑ i : Fin n, ∑ j : Fin n, W i j *
            (q⁻¹ * (σ i / schattenNorm q X) ^ q + p⁻¹ * (τ j / schattenNorm p Y1) ^ p) =
            (∑ i : Fin n, ∑ j : Fin n, W i j * (q⁻¹ * (σ i / schattenNorm q X) ^ q)) +
            (∑ i : Fin n, ∑ j : Fin n, W i j * (p⁻¹ * (τ j / schattenNorm p Y1) ^ p)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun j _ => by ring
        rw [hsplit]
        congr 1
        · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hRowW i, one_mul]
        · rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hColW j, one_mul]
    _ = 1 := by rw [hsum_σ, hsum_τ, mul_one, mul_one, hconj]

/-- Schatten (∞, 1) Hölder bound: if all singular values of X are ≤ 1, then
    ‖(X * Y).trace‖ ≤ schattenPow 1 Y. -/
theorem norm_trace_mul_le_schattenOne {n : ℕ} (X Y : Mat n)
    (U V : Matrix.unitaryGroup (Fin n) ℂ) (σ : Fin n → ℝ) (hσ_nn : ∀ i, 0 ≤ σ i)
    (hσ_le : ∀ i, σ i ≤ 1)
    (hX : X = (U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ) :
    ‖(X * Y).trace‖ ≤ schattenPow 1 Y := by
  by_cases htr0 : (X * Y).trace = 0
  · rw [htr0, norm_zero]; exact schattenPow_nonneg 1 Y
  let ζ : ℂ := ((‖(X * Y).trace‖ : ℝ) : ℂ) / (X * Y).trace
  have hζ_norm : ‖ζ‖ = 1 := by
    dsimp [ζ]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr htr0)]
  have hnorm_eq : ‖(X * Y).trace‖ = (X * (ζ • Y)).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, div_mul_cancel₀ _ htr0, Complex.ofReal_re]
  rw [hnorm_eq]
  let Y1 : Mat n := ζ • Y
  obtain ⟨UY, VY, τ, hτ, hY1_eq, hPowY1⟩ := exists_svd Y1
  have hPowY1_eq : schattenPow 1 Y1 = schattenPow 1 Y := by
    dsimp [Y1]; rw [schattenPow_smul zero_lt_one, hζ_norm, Real.one_rpow, one_mul]
  let Au : Matrix.unitaryGroup (Fin n) ℂ := star V * UY
  let Bu : Matrix.unitaryGroup (Fin n) ℂ := star VY * U
  let A : Mat n := (Au : Mat n)
  let B : Mat n := (Bu : Mat n)
  have htr_exp : (X * Y1).trace = ∑ i : Fin n, ∑ j : Fin n, (σ i : ℂ) * (τ j : ℂ) * (A i j * B j i) := by
    set DX : Mat n := Matrix.diagonal (fun i => (σ i : ℂ))
    set DY : Mat n := Matrix.diagonal (fun j => (τ j : ℂ))
    have hprod : (X * Y1).trace = ((DX * A) * (DY * B)).trace := by
      rw [hX, hY1_eq]
      calc (((U : Mat n) * DX * (V : Mat n)ᴴ) * ((UY : Mat n) * DY * (VY : Mat n)ᴴ)).trace
          = ((U : Mat n) * (DX * ((V : Mat n)ᴴ * (UY : Mat n)) * DY * (VY : Mat n)ᴴ)).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DX * A * DY * (VY : Mat n)ᴴ) * (U : Mat n)).trace := by
              rw [Matrix.trace_mul_comm (U : Mat n)]; rfl
        _ = ((DX * A) * (DY * ((VY : Mat n)ᴴ * (U : Mat n)))).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DX * A) * (DY * B)).trace := rfl
    rw [hprod, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, DX, DY, Matrix.diagonal_apply,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hColA : ∀ j : Fin n, ∑ i : Fin n, ‖A i j‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Au) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hRowB : ∀ j : Fin n, ∑ i : Fin n, ‖B j i‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Bu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [htr_exp, Complex.re_sum, ← hPowY1_eq, hPowY1 1 zero_lt_one]
  calc ∑ i : Fin n, (∑ j : Fin n, (σ i : ℂ) * (τ j : ℂ) * (A i j * B j i)).re
      ≤ ∑ i : Fin n, ∑ j : Fin n, ((‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2) * τ j := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : ((σ i : ℂ) * (τ j : ℂ) * (A i j * B j i)).re ≤ σ i * τ j * ‖A i j * B j i‖ := by
          calc _ ≤ ‖(σ i : ℂ) * (τ j : ℂ) * (A i j * B j i)‖ := Complex.re_le_norm _
            _ = σ i * τ j * ‖A i j * B j i‖ := by
                rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
                  Real.norm_of_nonneg (hσ_nn i), Real.norm_of_nonneg (hτ j)]
        have h2 : ‖A i j * B j i‖ ≤ (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2 := by
          rw [norm_mul]; nlinarith [sq_nonneg (‖A i j‖ - ‖B j i‖)]
        have h3 : σ i * τ j * ‖A i j * B j i‖ ≤ 1 * τ j * ((‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2) := by
          have hst : σ i * τ j ≤ 1 * τ j := mul_le_mul_of_nonneg_right (hσ_le i) (hτ j)
          exact mul_le_mul hst h2 (norm_nonneg _) (by linarith [hτ j])
        linarith
    _ = ∑ j : Fin n, (∑ i : Fin n, (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2) * τ j := by
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => (Finset.sum_mul ..).symm
    _ = ∑ j : Fin n, (τ j) ^ (1 : ℝ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_div, Finset.sum_add_distrib, hColA j, hRowB j, Real.rpow_one]; norm_num

/-- Trace-norm triangle inequality: ‖∑_k A_k‖_1 ≤ ‖∑_k |A_k|‖_1 = ∑_k ‖A_k‖_1! -/
theorem schattenOne_sum_le_matAbs {m n : ℕ} (A : Fin m → Mat n) :
    schattenPow 1 (∑ k, A k) ≤ schattenPow 1 (∑ k, matAbs (A k)) := by
  -- Write polar decomposition of S = ∑ A_k: S = U_S |S|, so schattenPow 1 S = Re Tr(U_Sᴴ S)
  set S : Mat n := ∑ k, A k
  obtain ⟨U_S, V_S, σ, hσ, hS_eq, hPowS⟩ := exists_svd S
  let W : Mat n := (V_S : Mat n) * (U_S : Mat n)ᴴ
  have htrS : (W * S).trace = (schattenPow 1 S : ℂ) := by
    rw [hPowS 1 zero_lt_one, hS_eq]
    have hprod : W * ((U_S : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V_S : Mat n)ᴴ) =
        (V_S : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V_S : Mat n)ᴴ := by
      dsimp [W]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U_S : Mat n)ᴴ (U_S : Mat n), unitary_conjTranspose_mul_self U_S,
        Matrix.one_mul]
    rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self V_S, Matrix.one_mul,
      Matrix.trace_diagonal]
    simp [Real.rpow_one]
  have h1 : schattenPow 1 S ≤ ∑ k : Fin m, schattenPow 1 (A k) := by
    have hnormS : schattenPow 1 S = ‖(W * S).trace‖ := by
      rw [htrS, Complex.norm_real, Real.norm_of_nonneg (schattenPow_nonneg 1 S)]
    rw [hnormS, show W * S = ∑ k, W * A k from by dsimp [S]; rw [Matrix.mul_sum], Matrix.trace_sum]
    calc ‖∑ k : Fin m, (W * A k).trace‖
        ≤ ∑ k : Fin m, ‖(W * A k).trace‖ := norm_sum_le _ _
      _ ≤ ∑ k : Fin m, schattenPow 1 (A k) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hW_svd : W = (V_S : Mat n) * Matrix.diagonal (fun _ => ((1 : ℝ) : ℂ)) * (U_S : Mat n)ᴴ := by
            have hd : Matrix.diagonal (fun _ : Fin n => ((1 : ℝ) : ℂ)) = 1 := by
              ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, hij]
            rw [hd, Matrix.mul_one]
          exact norm_trace_mul_le_schattenOne W (A k) V_S U_S (fun _ => 1)
            (fun _ => zero_le_one) (fun _ => le_rfl) hW_svd
  have h2 : ∑ k : Fin m, schattenPow 1 (A k) = schattenPow 1 (∑ k, matAbs (A k)) := by
    have htr_eq : ∀ P : Mat n, P.PosSemidef → schattenPow 1 P = P.trace.re := fun P hP => by
      let U := hP.isHermitian.eigenvectorUnitary
      let lam := hP.isHermitian.eigenvalues
      have hP_eq : P = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
        simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hP.isHermitian.spectral_theorem
      have htr : P.trace.re = ∑ i, lam i := by
        have h1' : P.trace = ((U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ).trace := by
          rw [← hP_eq]
        rw [h1', Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self U, Matrix.one_mul,
          Matrix.trace_diagonal, Complex.re_sum]; simp
      rw [htr, hP_eq, schattenPow_unitary_mul_conjTranspose_right zero_le_one,
        schattenPow_unitary_mul_left, schattenPow_diagonal zero_lt_one lam hP.eigenvalues_nonneg]
      simp [Real.rpow_one]
    have hH_psd : (∑ k, matAbs (A k)).PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    rw [htr_eq _ hH_psd, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← schattenPow_matAbs 1 (A k), htr_eq _ (matAbs_posSemidef (A k))]
  linarith

/-! ### Theorem 6: Log-Convexity in 1/p via Hadamard Three-Lines Theorem -/

set_option maxHeartbeats 600000 in
/-- Theorem 6 (Interpolation from p₀ = 1 to any p₁ > 1, e.g. p₁ = 2):
    For every m ≥ 1, n ≥ 1, 1 < p < p₁, and θ ∈ (0, 1) with 1/p = (1 - θ)/1 + θ/p₁,
      C_{p,m}(n) ≤ (C_{p₁,m}(n))^θ.
    Equivalently, setting p₁ = 2 yields θ = 2 - 2/p and the dimension-free upper bound
      C_{p,m}(n) ≤ (C_{2,m}(n))^(2 - 2/p)! -/
theorem theorem6_interp_from_one {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {p p1 θ : ℝ} (hp1 : 1 < p) (hp_lt : p < p1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hinterp : 1 / p = (1 - θ) + θ / p1) :
    leeConst p m n ≤ (leeConst p1 m n) ^ θ := by
  have hp0 : 0 < p := by linarith
  have hp1_gt1 : 1 < p1 := by linarith
  have hp1_pos : 0 < p1 := by linarith
  -- Obtain a maximizer A of leeConst p m n and normalize so schattenPow p H = 1!
  obtain ⟨A0, hH0_ne, hC_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := n) hp1 hm hn
  set H0 : Mat n := ∑ k, matAbs (A0 k)
  have hH0_pos : 0 < schattenNorm p H0 := schattenNorm_pos_of_ne_zero hp0 hH0_ne
  let c : ℝ := (schattenNorm p H0)⁻¹
  have hc_pos : 0 < c := inv_pos.mpr hH0_pos
  let A : Fin m → Mat n := fun k => (c : ℂ) • A0 k
  set S : Mat n := ∑ k, A k
  set H : Mat n := ∑ k, matAbs (A k)
  have hH_eq_sc : H = (c : ℂ) • H0 := by
    dsimp only [H, H0, A]
    simp_rw [matAbs_smul_real_nonneg hc_pos.le]
    exact Finset.smul_sum.symm
  have hH_norm : schattenNorm p H = 1 := by
    rw [hH_eq_sc, schattenNorm_smul hp0, Complex.norm_real, Real.norm_of_nonneg hc_pos.le,
      inv_mul_cancel₀ hH0_pos.ne']
  have hH_pow : schattenPow p H = 1 := by
    rw [← schattenNorm_rpow hp0 H, hH_norm, Real.one_rpow]
  have hC_eq_S : leeConst p m n = schattenNorm p S := by
    rw [← hC_eq]
    have hS_sc : S = (c : ℂ) • (∑ k, A0 k) := by dsimp [S, A]; rw [← Finset.smul_sum]
    have hrat : leeRatio p A = leeRatio p A0 := by
      unfold leeRatio
      change schattenNorm p S / schattenNorm p H = schattenNorm p (∑ k, A0 k) / schattenNorm p H0
      rw [hS_sc, hH_eq_sc, schattenNorm_smul hp0, schattenNorm_smul hp0,
        mul_div_mul_left _ _ (norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hc_pos.ne')).ne']
    rw [← hrat]; unfold leeRatio; rw [hH_norm, div_one]
  rw [hC_eq_S]
  by_cases hS0 : S = 0
  · rw [hS0, schattenNorm_zero hp0]
    have hC1_nn : 0 ≤ leeConst p1 m n := by
      obtain ⟨B, _, hB_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := n) hp1_gt1 hm hn
      rw [← hB_eq]; unfold leeRatio; exact div_nonneg (schattenNorm_nonneg p1 _) (schattenNorm_nonneg p1 _)
    exact Real.rpow_nonneg hC1_nn θ
  have hS_pos : 0 < schattenNorm p S := schattenNorm_pos_of_ne_zero hp0 hS0
  have hSpow_pos : 0 < schattenPow p S := by
    rw [← schattenNorm_rpow hp0 S]; exact Real.rpow_pos_of_pos hS_pos p
  -- Spectral decompositions of H, S, and polar decompositions A_k = U_k P_k!
  have hH_psd : H.PosSemidef := by
    have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
      intro s; induction s using Finset.induction_on with
      | empty => simpa using Matrix.PosSemidef.zero
      | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
    exact this Finset.univ
  let UH := hH_psd.isHermitian.eigenvectorUnitary
  let lam := hH_psd.isHermitian.eigenvalues
  have hH_spec : H = (UH : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (UH : Mat n)ᴴ := by
    simpa [UH, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hH_psd.isHermitian.spectral_theorem
  have hsum_lamp : ∑ i : Fin n, (lam i) ^ p = 1 := by
    rw [← hH_pow, hH_spec, schattenPow_unitary_mul_conjTranspose_right hp0.le,
      schattenPow_unitary_mul_left, schattenPow_diagonal hp0 lam hH_psd.eigenvalues_nonneg]
  obtain ⟨U_S, V_S, σ, hσ, hS_svd, hPowS⟩ := exists_svd S
  have hsum_σp : ∑ i : Fin n, (σ i) ^ p = schattenPow p S := (hPowS p hp0).symm
  have hpolar : ∀ k : Fin m, ∃ Uk : Matrix.unitaryGroup (Fin n) ℂ, A k = (Uk : Mat n) * matAbs (A k) :=
    fun k => exists_polar_unitary (A k)
  choose Uk hUk using hpolar
  -- Define Moore-Penrose pseudoinverse H^{-1/2} and normalized PSD terms E_k := H^{-1/2} |A_k| H^{-1/2}
  let HpowC : ℂ → Mat n := fun w =>
    (UH : Mat n) * Matrix.diagonal (fun i => if lam i = 0 then (0 : ℂ) else ((lam i : ℂ) ^ w)) * (UH : Mat n)ᴴ
  let Hpinv : Mat n := HpowC (-(1 / 2 : ℂ))
  have hHpinv_herm : Hpinvᴴ = Hpinv := by
    dsimp [Hpinv, HpowC]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq, Pi.star_apply]; by_cases hl : lam i = 0
      · simp [hl]
      · simp only [hl, ↓reduceIte]
        have hpos : 0 < lam i := lt_of_le_of_ne (hH_psd.eigenvalues_nonneg i) (Ne.symm hl)
        have hreal : ((lam i : ℂ) ^ (-(1 / 2 : ℂ))) = ((((lam i) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
          rw [show -(1 / 2 : ℂ) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num, ← Complex.ofReal_cpow hpos.le]
        rw [hreal, Complex.star_def, Complex.conj_ofReal]
    · simp [Matrix.diagonal, hij]
  let E : Fin m → Mat n := fun k => Hpinv * matAbs (A k) * Hpinv
  have hE_psd : ∀ k, (E k).PosSemidef := fun k => by
    simpa [E, hHpinv_herm] using (matAbs_posSemidef (A k)).conjTranspose_mul_mul_same Hpinv
  have hHpowC_mul : ∀ w1 w2 : ℂ, HpowC w1 * HpowC w2 = HpowC (w1 + w2) := fun w1 w2 => by
    dsimp [HpowC]; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (UH : Mat n)ᴴ (UH : Mat n), unitary_conjTranspose_mul_self UH,
      Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases hl : lam i = 0
      · simp [hl]
      · simp only [hl, ↓reduceIte]
        exact (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hl)).symm
    · simp [Matrix.diagonal, hij]
  -- Support identity: H^{1/2} * E_k * H^{1/2} = |A_k|!
  have hProj_mul_Pk : ∀ k, HpowC 0 * matAbs (A k) = matAbs (A k) := fun k => by
    have hdiff : ((1 : Mat n) - HpowC 0) * matAbs (A k) = 0 := by
      have h1m : (1 : Mat n) - HpowC 0 =
          (UH : Mat n) * Matrix.diagonal (fun i => if lam i = 0 then (1 : ℂ) else 0) * (UH : Mat n)ᴴ := by
        have h1 : (1 : Mat n) = (UH : Mat n) * (1 : Mat n) * (UH : Mat n)ᴴ := by
          rw [Matrix.mul_one, unitary_mul_conjTranspose_self UH]
        conv_lhs => rw [h1]; dsimp [HpowC]
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; by_cases hl : lam i = 0 <;> simp [Matrix.diagonal, hl]
        · simp [Matrix.diagonal, hij]
      have hker_col : ∀ i : Fin n, lam i = 0 →
          (matAbs (A k)).mulVec (fun a => (UH : Mat n) a i) = 0 := by
        intro i hli
        have hHcol : H.mulVec (fun a => (UH : Mat n) a i) = 0 := by
          have hv : (fun a => (UH : Mat n) a i) = (UH : Mat n).mulVec (Pi.single i 1) := by
            ext a; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
          rw [hv, hH_spec, Matrix.mulVec_mulVec,
            Matrix.mul_assoc _ (UH : Mat n)ᴴ (UH : Mat n), unitary_conjTranspose_mul_self UH,
            Matrix.mul_one, ← Matrix.mulVec_mulVec]
          have hd0 : (Matrix.diagonal (fun j => (lam j : ℂ))).mulVec (Pi.single i 1) = 0 := by
            ext j; by_cases hij : j = i
            · subst hij; simp [Matrix.mulVec_diagonal, hli]
            · simp [Matrix.mulVec_diagonal, Pi.single_eq_of_ne hij]
          rw [hd0, Matrix.mulVec_zero]
        have hsum0 : ∑ j : Fin m, (star (fun a => (UH : Mat n) a i) ⬝ᵥ
            (matAbs (A j)).mulVec (fun a => (UH : Mat n) a i)).re = 0 := by
          have h1 : (star (fun a => (UH : Mat n) a i) ⬝ᵥ H.mulVec (fun a => (UH : Mat n) a i)).re = 0 := by
            rw [hHcol, dotProduct_zero, Complex.zero_re]
          rw [← h1]; simp only [H, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
        have hnn : ∀ j : Fin m, 0 ≤ (star (fun a => (UH : Mat n) a i) ⬝ᵥ
            (matAbs (A j)).mulVec (fun a => (UH : Mat n) a i)).re := fun j => by
          simpa [RCLike.re_to_complex] using (matAbs_posSemidef (A j)).re_dotProduct_nonneg _
        have hk0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).mp hsum0 k (Finset.mem_univ k)
        exact posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero (matAbs_posSemidef (A k)) _ hk0
      have hPk_proj : matAbs (A k) * ((1 : Mat n) - HpowC 0) = 0 := by
        rw [h1m]
        have hmid : matAbs (A k) * ((UH : Mat n) * Matrix.diagonal (fun i => if lam i = 0 then (1 : ℂ) else 0)) = 0 := by
          rw [← Matrix.mul_assoc]; ext a j
          simp only [Matrix.mul_diagonal, Matrix.zero_apply]
          by_cases hlj : lam j = 0
          · simp only [hlj, ↓reduceIte, mul_one]; exact congr_fun (hker_col j hlj) a
          · simp [hlj]
        calc matAbs (A k) * ((UH : Mat n) * Matrix.diagonal (fun i => if lam i = 0 then (1 : ℂ) else 0) * (UH : Mat n)ᴴ)
            = (matAbs (A k) * ((UH : Mat n) * Matrix.diagonal (fun i => if lam i = 0 then (1 : ℂ) else 0))) * (UH : Mat n)ᴴ := by
              simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hmid, Matrix.zero_mul]
      have hH0_herm : ((1 : Mat n) - HpowC 0)ᴴ = (1 : Mat n) - HpowC 0 := by
        rw [h1m, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; by_cases hl : lam i = 0 <;> simp [Matrix.diagonal, hl]
        · simp [Matrix.diagonal, hij]
      have := congrArg Matrix.conjTranspose hPk_proj
      rw [Matrix.conjTranspose_mul, hH0_herm, (matAbs_posSemidef (A k)).isHermitian.eq,
        Matrix.conjTranspose_zero] at this
      exact this
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hdiff
    exact hdiff.symm
  have hRE : ∀ k, HpowC (1 / 2) * E k * HpowC (1 / 2) = matAbs (A k) := fun k => by
    dsimp [E, Hpinv]
    calc HpowC (1 / 2) * (HpowC (-(1 / 2)) * matAbs (A k) * HpowC (-(1 / 2))) * HpowC (1 / 2)
        = (HpowC (1 / 2) * HpowC (-(1 / 2))) * matAbs (A k) * (HpowC (-(1 / 2)) * HpowC (1 / 2)) := by
          simp only [Matrix.mul_assoc]
      _ = HpowC 0 * matAbs (A k) * HpowC 0 := by
          rw [hHpowC_mul, hHpowC_mul, add_neg_cancel, neg_add_cancel]
      _ = matAbs (A k) * HpowC 0 := by rw [hProj_mul_Pk k]
      _ = matAbs (A k) := by
          have hH0_herm : (HpowC 0)ᴴ = HpowC 0 := by
            dsimp [HpowC]
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
              Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
            congr 2; ext i j; by_cases hij : i = j
            · subst hij; by_cases hl : lam i = 0 <;> simp [Matrix.diagonal, hl]
            · simp [Matrix.diagonal, hij]
          have h := congrArg Matrix.conjTranspose (hProj_mul_Pk k)
          rw [Matrix.conjTranspose_mul, hH0_herm, (matAbs_posSemidef (A k)).isHermitian.eq] at h
          exact h
  have hSumE : ∑ k, E k = HpowC 0 := by
    dsimp [E]; rw [← Finset.sum_mul, ← Matrix.mul_sum]
    have hH_eq1 : H = HpowC 1 := by
      rw [hH_spec]; dsimp [HpowC]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; by_cases hl : lam i = 0 <;> simp [Matrix.diagonal, hl]
      · simp [Matrix.diagonal, hij]
    change Hpinv * H * Hpinv = HpowC 0
    rw [hH_eq1]; dsimp [Hpinv]
    rw [hHpowC_mul, hHpowC_mul]; congr 1; ring
  -- Define the analytic interpolating family Φ(z) = Tr(G_tilde(z) * S(z)) on the closed strip 0 ≤ Re z ≤ 1!
  let α : ℂ → ℂ := fun z => (1 - z) + z / (p1 : ℂ)
  let β : ℂ → ℂ := fun z => ((p / 2 : ℝ) : ℂ) * α z
  let γ : ℂ → ℂ := fun z => (p : ℂ) * (1 - α z)
  let Sz : ℂ → Mat n := fun z => ∑ k : Fin m, (Uk k : Mat n) * (HpowC (β z) * E k * HpowC (β z))
  let Gz : ℂ → Mat n := fun z =>
    (V_S : Mat n) * Matrix.diagonal (fun i => if σ i = 0 then (0 : ℂ) else ((σ i : ℂ) ^ (γ z))) * (U_S : Mat n)ᴴ
  let Φ : ℂ → ℂ := fun z => (Gz z * Sz z).trace
  -- 1. Value at z = θ: Φ(θ) = schattenPow p S!
  have hΦ_θ : Φ (θ : ℂ) = (schattenPow p S : ℂ) := by
    have hαθ : α (θ : ℂ) = ((1 / p : ℝ) : ℂ) := by
      dsimp [α]; push_cast; exact_mod_cast hinterp.symm
    have hβθ : β (θ : ℂ) = (1 / 2 : ℂ) := by
      dsimp [β]; rw [hαθ]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hp0.ne']
    have hγθ : γ (θ : ℂ) = (((p - 1 : ℝ) : ℂ)) := by
      dsimp [γ]; rw [hαθ]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hp0.ne']
    have hSθ : Sz (θ : ℂ) = S := by
      dsimp [Sz]; rw [hβθ]
      refine Finset.sum_congr rfl fun k _ => by rw [hRE k, ← hUk k]
    have hGθ : Gz (θ : ℂ) = (dualOp p S)ᴴ := by
      dsimp [Gz]; rw [hγθ, dualOp_eq_of_svd hp1 U_S V_S σ hσ hS_svd,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, Pi.star_apply]; by_cases hs : σ i = 0
        · simp [hs, Real.zero_rpow (show p - 1 ≠ 0 by linarith)]
        · simp only [hs, ↓reduceIte]
          have hpos : 0 < σ i := lt_of_le_of_ne (hσ i) (Ne.symm hs)
          rw [← Complex.ofReal_cpow hpos.le, Complex.star_def, Complex.conj_ofReal]
      · simp [Matrix.diagonal, hij]
    dsimp [Φ]; rw [hSθ, hGθ]
    have htr_re := dualOp_trace_self hp1 S
    have htr_im : ((dualOp p S)ᴴ * S).trace.im = 0 := by
      have hprod : (dualOp p S)ᴴ * S =
          (V_S : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ p : ℝ) : ℂ)) * (V_S : Mat n)ᴴ := by
        rw [dualOp_eq_of_svd hp1 U_S V_S σ hσ hS_svd, hS_svd,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.diagonal_conjTranspose]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U_S : Mat n)ᴴ (U_S : Mat n), unitary_conjTranspose_mul_self U_S,
          Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq, Pi.star_apply, Complex.star_def,
            Complex.conj_ofReal, ← Complex.ofReal_mul]
          congr 1; rcases eq_or_lt_of_le (hσ i) with h0 | hpos
          · rw [← h0, mul_zero, Real.zero_rpow hp0.ne']
          · calc (σ i) ^ (p - 1) * σ i = (σ i) ^ (p - 1) * (σ i) ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ = (σ i) ^ ((p - 1) + 1) := (Real.rpow_add hpos (p - 1) 1).symm
              _ = (σ i) ^ p := by ring_nf
        · simp [Matrix.diagonal, hij]
      rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self V_S, Matrix.one_mul,
        Matrix.trace_diagonal, Complex.im_sum]; simp
    exact Complex.ext (by simpa using htr_re) (by simpa using htr_im)
  -- 2. Entire differentiability of Φ (hence DiffContOnCl on verticalStrip 0 1)!
  have hα_diff : Differentiable ℂ α :=
    (differentiable_const 1 |>.sub differentiable_id).add (differentiable_id.div_const _)
  have hβ_diff : Differentiable ℂ β := differentiable_const _ |>.mul hα_diff
  have hγ_diff : Differentiable ℂ γ := differentiable_const _ |>.mul (differentiable_const 1 |>.sub hα_diff)
  have hΦ_diff : Differentiable ℂ Φ := by
    have hH_entry : ∀ a b : Fin n, Differentiable ℂ (fun z => HpowC (β z) a b) := fun a b => by
      have heq : (fun z => HpowC (β z) a b) = fun z =>
          ∑ i : Fin n, ((UH : Mat n) a i * (UH : Mat n)ᴴ i b) *
            (if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (β z)) := by
        ext z; dsimp [HpowC]; simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        refine Finset.sum_congr rfl fun i _ => by by_cases hl : lam i = 0 <;> simp [hl]; ring
      rw [heq]; refine Differentiable.fun_sum fun i _ => Differentiable.mul (differentiable_const _) ?_
      by_cases hl : lam i = 0
      · simp [hl, differentiable_const]
      · simp only [hl, ↓reduceIte]
        exact Differentiable.const_cpow hβ_diff (Or.inl (Complex.ofReal_ne_zero.mpr hl))
    have hG_entry : ∀ a b : Fin n, Differentiable ℂ (fun z => Gz z a b) := fun a b => by
      have heq : (fun z => Gz z a b) = fun z =>
          ∑ i : Fin n, ((V_S : Mat n) a i * (U_S : Mat n)ᴴ i b) *
            (if σ i = 0 then (0 : ℂ) else (σ i : ℂ) ^ (γ z)) := by
        ext z; dsimp [Gz]; simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        refine Finset.sum_congr rfl fun i _ => by by_cases hs : σ i = 0 <;> simp [hs]; ring
      rw [heq]; refine Differentiable.fun_sum fun i _ => Differentiable.mul (differentiable_const _) ?_
      by_cases hs : σ i = 0
      · simp [hs, differentiable_const]
      · simp only [hs, ↓reduceIte]
        exact Differentiable.const_cpow hγ_diff (Or.inl (Complex.ofReal_ne_zero.mpr hs))
    have hS_entry : ∀ a b : Fin n, Differentiable ℂ (fun z => Sz z a b) := fun a b => by
      have heq : (fun z => Sz z a b) = fun z =>
          ∑ k : Fin m, ∑ x : Fin n, ∑ y : Fin n, ∑ w : Fin n,
            ((Uk k : Mat n) a x * E k y w) * (HpowC (β z) x y * HpowC (β z) w b) := by
        ext z; dsimp [Sz]; simp only [Matrix.sum_apply, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        calc ∑ x, (Uk k : Mat n) a x * ∑ w, (∑ y, HpowC (β z) x y * E k y w) * HpowC (β z) w b
            = ∑ x, ∑ w, ∑ y, ((Uk k : Mat n) a x * E k y w) * (HpowC (β z) x y * HpowC (β z) w b) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => ?_
              rw [Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => by ring
          _ = ∑ x, ∑ y, ∑ w, ((Uk k : Mat n) a x * E k y w) * (HpowC (β z) x y * HpowC (β z) w b) := by
              refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
      rw [heq]
      exact Differentiable.fun_sum fun k _ => Differentiable.fun_sum fun x _ =>
        Differentiable.fun_sum fun y _ => Differentiable.fun_sum fun w _ =>
          Differentiable.mul (differentiable_const _) ((hH_entry x y).mul (hH_entry w b))
    have heq : Φ = fun z => ∑ i : Fin n, ∑ j : Fin n, Gz z i j * Sz z j i := by
      ext z; simp only [Φ, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [heq]
    exact Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ =>
      (hG_entry i j).mul (hS_entry j i)
  -- 3. Boundedness of ‖Φ z‖ on verticalClosedStrip 0 1!
  have hΦ_bdd : BddAbove ((norm ∘ Φ) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    -- On 0 ≤ z.re ≤ 1, (β z).re ∈ [0, p/2] and (γ z).re ∈ [0, p]!
    let Mlam : ℝ := 1 + ∑ i : Fin n, (max 1 (lam i)) ^ (p / 2)
    let Mσ : ℝ := 1 + ∑ i : Fin n, (max 1 (σ i)) ^ p
    have hH_le : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, ∀ a b : Fin n, ‖HpowC (β z) a b‖ ≤ Mlam := by
      intro z hz a b
      have hre : 0 ≤ (β z).re ∧ (β z).re ≤ p / 2 := by
        have hαre : (α z).re = (1 - z.re) + z.re / p1 := by
          dsimp [α]; simp [Complex.div_re, Complex.normSq_ofReal]
          field_simp [hp1_pos.ne']
        have hβre : (β z).re = (p / 2) * (α z).re := by
          dsimp [β]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
        have hz0 : 0 ≤ z.re := hz.1
        have hz1 : z.re ≤ 1 := hz.2
        have hα0 : 0 ≤ (α z).re := by rw [hαre]; positivity
        have hα1 : (α z).re ≤ 1 := by
          rw [hαre]
          have : z.re / p1 ≤ z.re := div_le_self hz0 hp1_gt1.le
          linarith
        rw [hβre]; exact ⟨by positivity, by nlinarith⟩
      have heq : HpowC (β z) a b = ∑ i : Fin n, ((UH : Mat n) a i * (UH : Mat n)ᴴ i b) *
          (if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (β z)) := by
        dsimp [HpowC]; simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        refine Finset.sum_congr rfl fun i _ => by by_cases hl : lam i = 0 <;> simp [hl]; ring
      rw [heq]
      have hU_le1 : ∀ i : Fin n, ‖(UH : Mat n) a i‖ ≤ 1 ∧ ‖(UH : Mat n)ᴴ i b‖ ≤ 1 := fun i => by
        have h1 : ∑ j : Fin n, ‖(UH : Mat n) a j‖ ^ 2 = 1 := by
          have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self UH) a) a
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
          have hre' := congrArg Complex.re hU
          simp only [Complex.re_sum, Complex.one_re] at hre'
          rw [← hre']; refine Finset.sum_congr rfl fun j _ => by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
        have h2 : ∑ j : Fin n, ‖(UH : Mat n)ᴴ j b‖ ^ 2 = 1 := by
          have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self UH) b) b
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
          have hre' := congrArg Complex.re hU
          simp only [Complex.re_sum, Complex.one_re] at hre'
          rw [← hre']; refine Finset.sum_congr rfl fun j _ => by
            simp only [Matrix.conjTranspose_apply, norm_star]
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
        have ha1 : ‖(UH : Mat n) a i‖ ^ 2 ≤ 1 := by
          rw [← h1]
          exact Finset.single_le_sum (f := fun j => ‖(UH : Mat n) a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have hb1 : ‖(UH : Mat n)ᴴ i b‖ ^ 2 ≤ 1 := by
          rw [← h2]
          exact Finset.single_le_sum (f := fun j => ‖(UH : Mat n)ᴴ j b‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        exact ⟨by nlinarith [norm_nonneg ((UH : Mat n) a i)], by nlinarith [norm_nonneg ((UH : Mat n)ᴴ i b)]⟩
      calc ‖∑ i : Fin n, ((UH : Mat n) a i * (UH : Mat n)ᴴ i b) *
              (if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (β z))‖
          ≤ ∑ i : Fin n, ‖((UH : Mat n) a i * (UH : Mat n)ᴴ i b) *
              (if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (β z))‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin n, (max 1 (lam i)) ^ (p / 2) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, norm_mul]
            have h1 : ‖(UH : Mat n) a i‖ * ‖(UH : Mat n)ᴴ i b‖ ≤ 1 := by
              have := hU_le1 i; nlinarith [norm_nonneg ((UH : Mat n) a i), norm_nonneg ((UH : Mat n)ᴴ i b)]
            have h2 : ‖if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (β z)‖ ≤ (max 1 (lam i)) ^ (p / 2) := by
              by_cases hl : lam i = 0
              · simp [hl]
              · simp only [hl, ↓reduceIte]
                have hl_pos : 0 < lam i := lt_of_le_of_ne (hH_psd.eigenvalues_nonneg i) (Ne.symm hl)
                rw [Complex.norm_cpow_eq_rpow_re_of_pos hl_pos]
                calc (lam i) ^ (β z).re ≤ (max 1 (lam i)) ^ (β z).re :=
                      Real.rpow_le_rpow hl_pos.le (le_max_right 1 _) hre.1
                  _ ≤ (max 1 (lam i)) ^ (p / 2) :=
                      Real.rpow_le_rpow_of_exponent_le (le_max_left 1 _) hre.2
            exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (by simpa using h2)
        _ ≤ Mlam := by dsimp [Mlam]; linarith
    have hG_le : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1, ∀ a b : Fin n, ‖Gz z a b‖ ≤ Mσ := by
      intro z hz a b
      have hre : 0 ≤ (γ z).re ∧ (γ z).re ≤ p := by
        have hαre : (α z).re = (1 - z.re) + z.re / p1 := by
          dsimp [α]; simp [Complex.div_re, Complex.normSq_ofReal]
          field_simp [hp1_pos.ne']
        have hγre : (γ z).re = p * (1 - (α z).re) := by
          dsimp [γ]; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
            Complex.one_re]; ring
        have hz0 : 0 ≤ z.re := hz.1
        have hz1 : z.re ≤ 1 := hz.2
        have hα0 : 0 ≤ (α z).re := by rw [hαre]; positivity
        have hα1 : (α z).re ≤ 1 := by
          rw [hαre]; have : z.re / p1 ≤ z.re := div_le_self hz0 hp1_gt1.le; linarith
        rw [hγre]; exact ⟨by nlinarith, by nlinarith⟩
      have heq : Gz z a b = ∑ i : Fin n, ((V_S : Mat n) a i * (U_S : Mat n)ᴴ i b) *
          (if σ i = 0 then (0 : ℂ) else (σ i : ℂ) ^ (γ z)) := by
        dsimp [Gz]; simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        refine Finset.sum_congr rfl fun i _ => by by_cases hs : σ i = 0 <;> simp [hs]; ring
      rw [heq]
      have hU_le1 : ∀ i : Fin n, ‖(V_S : Mat n) a i‖ ≤ 1 ∧ ‖(U_S : Mat n)ᴴ i b‖ ≤ 1 := fun i => by
        have h1 : ∑ j : Fin n, ‖(V_S : Mat n) a j‖ ^ 2 = 1 := by
          have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self V_S) a) a
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
          have hre' := congrArg Complex.re hU
          simp only [Complex.re_sum, Complex.one_re] at hre'
          rw [← hre']; refine Finset.sum_congr rfl fun j _ => by
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
        have h2 : ∑ j : Fin n, ‖(U_S : Mat n)ᴴ j b‖ ^ 2 = 1 := by
          have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self U_S) b) b
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
          have hre' := congrArg Complex.re hU
          simp only [Complex.re_sum, Complex.one_re] at hre'
          rw [← hre']; refine Finset.sum_congr rfl fun j _ => by
            simp only [Matrix.conjTranspose_apply, norm_star]
            rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
        have ha1 : ‖(V_S : Mat n) a i‖ ^ 2 ≤ 1 := by
          rw [← h1]
          exact Finset.single_le_sum (f := fun j => ‖(V_S : Mat n) a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        have hb1 : ‖(U_S : Mat n)ᴴ i b‖ ^ 2 ≤ 1 := by
          rw [← h2]
          exact Finset.single_le_sum (f := fun j => ‖(U_S : Mat n)ᴴ j b‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        exact ⟨by nlinarith [norm_nonneg ((V_S : Mat n) a i)], by nlinarith [norm_nonneg ((U_S : Mat n)ᴴ i b)]⟩
      calc ‖∑ i : Fin n, ((V_S : Mat n) a i * (U_S : Mat n)ᴴ i b) *
              (if σ i = 0 then (0 : ℂ) else (σ i : ℂ) ^ (γ z))‖
          ≤ ∑ i : Fin n, ‖((V_S : Mat n) a i * (U_S : Mat n)ᴴ i b) *
              (if σ i = 0 then (0 : ℂ) else (σ i : ℂ) ^ (γ z))‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin n, (max 1 (σ i)) ^ p := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, norm_mul]
            have h1 : ‖(V_S : Mat n) a i‖ * ‖(U_S : Mat n)ᴴ i b‖ ≤ 1 := by
              have := hU_le1 i; nlinarith [norm_nonneg ((V_S : Mat n) a i), norm_nonneg ((U_S : Mat n)ᴴ i b)]
            have h2 : ‖if σ i = 0 then (0 : ℂ) else (σ i : ℂ) ^ (γ z)‖ ≤ (max 1 (σ i)) ^ p := by
              by_cases hs : σ i = 0
              · simp [hs]
              · simp only [hs, ↓reduceIte]
                have hs_pos : 0 < σ i := lt_of_le_of_ne (hσ i) (Ne.symm hs)
                rw [Complex.norm_cpow_eq_rpow_re_of_pos hs_pos]
                calc (σ i) ^ (γ z).re ≤ (max 1 (σ i)) ^ (γ z).re :=
                      Real.rpow_le_rpow hs_pos.le (le_max_right 1 _) hre.1
                  _ ≤ (max 1 (σ i)) ^ p :=
                      Real.rpow_le_rpow_of_exponent_le (le_max_left 1 _) hre.2
            exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans (by simpa using h2)
        _ ≤ Mσ := by dsimp [Mσ]; linarith
    let Ctot : ℝ := ∑ _i : Fin n, ∑ j : Fin n, Mσ *
      (∑ k : Fin m, ∑ x : Fin n, ∑ y : Fin n, ∑ w : Fin n, (‖(Uk k : Mat n) j x‖ * ‖E k y w‖) * (Mlam * Mlam))
    refine ⟨Ctot, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    change ‖(Gz z * Sz z).trace‖ ≤ Ctot
    rw [Matrix.trace]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    simp only [Matrix.diag, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    have hMlam_nn : 0 ≤ Mlam := add_nonneg zero_le_one
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left 1 _)) _)
    have hMσ_nn : 0 ≤ Mσ := add_nonneg zero_le_one
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (le_trans zero_le_one (le_max_left 1 _)) _)
    refine mul_le_mul (hG_le z hz i j) ?_ (norm_nonneg _) hMσ_nn
    dsimp [Sz]; simp only [Matrix.sum_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    simp only [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
    have h1 : ‖(Uk k : Mat n) j x‖ * ‖∑ w, (∑ y, HpowC (β z) x y * E k y w) * HpowC (β z) w i‖ ≤
        ∑ w : Fin n, ∑ y : Fin n, (‖(Uk k : Mat n) j x‖ * ‖E k y w‖) * (Mlam * Mlam) := by
      calc _ ≤ ‖(Uk k : Mat n) j x‖ * ∑ w, ‖(∑ y, HpowC (β z) x y * E k y w) * HpowC (β z) w i‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
        _ = ∑ w, ‖(Uk k : Mat n) j x‖ * (‖∑ y, HpowC (β z) x y * E k y w‖ * ‖HpowC (β z) w i‖) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun w _ => by rw [norm_mul]
        _ ≤ ∑ w, ‖(Uk k : Mat n) j x‖ * ((∑ y, ‖HpowC (β z) x y‖ * ‖E k y w‖) * Mlam) := by
            refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
              (mul_le_mul ((norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => by rw [norm_mul]))
                (hH_le z hz w i) (norm_nonneg _) (Finset.sum_nonneg fun y _ => by positivity)) (norm_nonneg _)
        _ ≤ ∑ w, ∑ y, (‖(Uk k : Mat n) j x‖ * ‖E k y w‖) * (Mlam * Mlam) := by
            refine Finset.sum_le_sum fun w _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_le_sum fun y _ => ?_
            have := hH_le z hz x y
            have hle := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right this (norm_nonneg (E k y w))) (norm_nonneg ((Uk k : Mat n) j x))) hMlam_nn
            linarith
    calc _ ≤ _ := h1
      _ = ∑ y, ∑ w, (‖(Uk k : Mat n) j x‖ * ‖E k y w‖) * (Mlam * Mlam) := Finset.sum_comm
  -- Helper: On any vertical line Re(z) = x, HpowC(β z) = W_y * HpowC(r) where W_y is unitary!
  have hSplit_HpowC : ∀ (r t : ℝ),
      ∃ W : Matrix.unitaryGroup (Fin n) ℂ,
        HpowC ((r : ℂ) + (t : ℂ) * Complex.I) = (W : Mat n) * HpowC (r : ℂ) ∧
        HpowC ((r : ℂ) + (t : ℂ) * Complex.I) = HpowC (r : ℂ) * (W : Mat n) := by
    intro r t
    let phase : Fin n → ℂ := fun i => if lam i = 0 then 1 else (lam i : ℂ) ^ ((t : ℂ) * Complex.I)
    have hphase_norm : ∀ i, star (phase i) * phase i = 1 := fun i => by
      dsimp [phase]; by_cases hl : lam i = 0
      · simp [hl]
      · simp only [hl, ↓reduceIte]
        have hl_pos : 0 < lam i := lt_of_le_of_ne (hH_psd.eigenvalues_nonneg i) (Ne.symm hl)
        rw [Complex.conj_mul', Complex.norm_cpow_eq_rpow_re_of_pos hl_pos]
        simp
    let Wmat : Mat n := (UH : Mat n) * Matrix.diagonal phase * (UH : Mat n)ᴴ
    have hW_mem : Wmat ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      dsimp [Wmat]
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UH : Mat n)ᴴ (UH : Mat n), unitary_conjTranspose_mul_self UH,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hd1 : Matrix.diagonal (fun i => star phase i * phase i) = 1 := by
        ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply]
          exact hphase_norm i
        · simp [Matrix.diagonal, hij]
      rw [hd1, Matrix.one_mul, unitary_mul_conjTranspose_self UH]
    let W : Matrix.unitaryGroup (Fin n) ℂ := ⟨Wmat, hW_mem⟩
    refine ⟨W, ?_, ?_⟩
    · dsimp [W, Wmat, HpowC]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UH : Mat n)ᴴ (UH : Mat n), unitary_conjTranspose_mul_self UH,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, phase]
        by_cases hl : lam i = 0
        · simp [hl]
        · simp only [hl, ↓reduceIte]
          rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hl), add_comm]
      · simp [Matrix.diagonal, hij]
    · dsimp [W, Wmat, HpowC]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UH : Mat n)ᴴ (UH : Mat n), unitary_conjTranspose_mul_self UH,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, phase]
        by_cases hl : lam i = 0
        · simp [hl]
        · simp only [hl, ↓reduceIte]
          rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hl)]
      · simp [Matrix.diagonal, hij]
  -- 4. Left boundary bound (z.re = 0): ‖Φ z‖ ≤ 1!
  have hleft : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖Φ z‖ ≤ 1 := by
    intro z hz
    have hz0 : z.re = 0 := hz
    let y : ℝ := z.im
    have hz_eq : z = (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz0, y]
    -- Compute β(i y) = p/2 + i t_β and γ(i y) = i t_γ (purely imaginary!)
    let tβ : ℝ := (p / 2) * (y * (1 / p1 - 1))
    let tγ : ℝ := p * (y * (1 - 1 / p1))
    have hβ_eq : β z = ((p / 2 : ℝ) : ℂ) + (tβ : ℂ) * Complex.I := by
      dsimp [β, α, tβ]; rw [hz_eq]
      apply Complex.ext
      · simp [Complex.div_re, Complex.normSq_ofReal]
      · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.div_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_im, Complex.normSq_ofReal]
        field_simp [hp1_pos.ne']; ring
    have hγ_eq : γ z = (tγ : ℂ) * Complex.I := by
      dsimp [γ, α, tγ]; rw [hz_eq]
      apply Complex.ext
      · simp [Complex.div_re, Complex.normSq_ofReal]
      · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.div_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_im, Complex.normSq_ofReal]
        field_simp [hp1_pos.ne']; ring
    -- Show Gz z has singular values ≤ 1 (since σ_i^(i t_γ) has modulus 1)!
    let phaseG : Fin n → ℂ := fun i => if σ i = 0 then 1 else (σ i : ℂ) ^ ((tγ : ℂ) * Complex.I)
    let indG : Fin n → ℝ := fun i => if σ i = 0 then 0 else 1
    have hphaseG_unit : ((V_S : Mat n) * Matrix.diagonal phaseG) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
        Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
        ← Matrix.mul_assoc (V_S : Mat n)ᴴ (V_S : Mat n),
        unitary_conjTranspose_mul_self V_S, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
      ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, phaseG]
        by_cases hs : σ i = 0
        · simp [hs]
        · simp only [hs, ↓reduceIte]
          have hs_pos : 0 < σ i := lt_of_le_of_ne (hσ i) (Ne.symm hs)
          rw [Complex.star_def, Complex.conj_mul', Complex.norm_cpow_eq_rpow_re_of_pos hs_pos]; simp
      · simp [Matrix.diagonal, hij]
    let VG : Matrix.unitaryGroup (Fin n) ℂ := ⟨(V_S : Mat n) * Matrix.diagonal phaseG, hphaseG_unit⟩
    have hGz_svd : Gz z = (VG : Mat n) * Matrix.diagonal (fun i => (indG i : ℂ)) * (U_S : Mat n)ᴴ := by
      dsimp [Gz, VG]; rw [hγ_eq, Matrix.mul_assoc (V_S : Mat n) (Matrix.diagonal phaseG),
        Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, phaseG, indG]
        by_cases hs : σ i = 0 <;> simp [hs]
      · simp [Matrix.diagonal, hij]
    have hle1 : ‖Φ z‖ ≤ schattenPow 1 (Sz z) :=
      norm_trace_mul_le_schattenOne (Gz z) (Sz z) VG U_S indG
        (fun i => by dsimp [indG]; split_ifs <;> norm_num)
        (fun i => by dsimp [indG]; split_ifs <;> norm_num) hGz_svd
    -- Bound schattenPow 1 (Sz z) ≤ schattenPow 1 (∑ |A_k(i y)|) = schattenPow p H = 1!
    obtain ⟨W, hW_left, hW_right⟩ := hSplit_HpowC (p / 2) tβ
    let Az : Fin m → Mat n := fun k => (Uk k : Mat n) * (HpowC (β z) * E k * HpowC (β z))
    have hAbs_Az : ∀ k, matAbs (Az k) = (W : Mat n)ᴴ * (HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))) * (W : Mat n) := by
      intro k
      have hH_herm : (HpowC (((p / 2 : ℝ) : ℂ)))ᴴ = HpowC (((p / 2 : ℝ) : ℂ)) := by
        dsimp [HpowC]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq, Pi.star_apply]; by_cases hl : lam i = 0
          · simp [hl]
          · simp only [hl, ↓reduceIte]
            have hl_pos : 0 < lam i := lt_of_le_of_ne (hH_psd.eigenvalues_nonneg i) (Ne.symm hl)
            rw [← Complex.ofReal_cpow hl_pos.le, Complex.star_def, Complex.conj_ofReal]
        · simp [Matrix.diagonal, hij]
      have hEk_psd : (HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))).PosSemidef := by
        have h1 := (hE_psd k).conjTranspose_mul_mul_same (HpowC (((p / 2 : ℝ) : ℂ)))
        rwa [hH_herm] at h1
      have hP_psd : ((W : Mat n)ᴴ * (HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))) * (W : Mat n)).PosSemidef :=
        hEk_psd.conjTranspose_mul_mul_same (W : Mat n)
      refine matAbs_eq_of_posSemidef_sq hP_psd ?_
      have hAz_eq : Az k = (((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)) *
          ((HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))) * (W : Mat n)) := by
        calc Az k = (Uk k : Mat n) * (((W : Mat n) * HpowC (((p / 2 : ℝ) : ℂ))) * E k * (HpowC (((p / 2 : ℝ) : ℂ)) * (W : Mat n))) := by
              dsimp [Az]; rw [hβ_eq, ← hW_left, ← hW_right]
          _ = (((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)) *
              ((HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))) * (W : Mat n)) := by
              change (Uk k : Mat n) * (((W : Mat n) * HpowC (((p / 2 : ℝ) : ℂ))) * E k * (HpowC (((p / 2 : ℝ) : ℂ)) * (W : Mat n))) =
                ((Uk k : Mat n) * (W : Mat n)) * ((HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))) * (W : Mat n))
              simp only [Matrix.mul_assoc]
      set Mk : Mat n := HpowC (((p / 2 : ℝ) : ℂ)) * E k * HpowC (((p / 2 : ℝ) : ℂ))
      calc ((W : Mat n)ᴴ * Mk * (W : Mat n)) * ((W : Mat n)ᴴ * Mk * (W : Mat n))
          = (W : Mat n)ᴴ * Mk * ((W : Mat n) * (W : Mat n)ᴴ) * Mk * (W : Mat n) := by simp only [Matrix.mul_assoc]
        _ = (W : Mat n)ᴴ * Mk * Mk * (W : Mat n) := by
            rw [unitary_mul_conjTranspose_self W, Matrix.mul_one]
        _ = (Mk * (W : Mat n))ᴴ * ((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)ᴴ *
            (((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) * (Mk * (W : Mat n))) := by
            rw [Matrix.mul_assoc ((Mk * (W : Mat n))ᴴ),
              ← Matrix.mul_assoc ((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)ᴴ,
              unitary_conjTranspose_mul_self (Uk k * W), Matrix.one_mul,
              Matrix.conjTranspose_mul, hEk_psd.isHermitian.eq]
            simp only [Matrix.mul_assoc]
        _ = (Az k)ᴴ * Az k := by rw [hAz_eq]; conv_rhs => rw [Matrix.conjTranspose_mul]
    have hSumAbs : ∑ k, matAbs (Az k) = (W : Mat n)ᴴ * HpowC (p : ℂ) * (W : Mat n) := by
      simp_rw [hAbs_Az]
      rw [← Finset.sum_mul, ← Matrix.mul_sum, ← Finset.sum_mul, ← Matrix.mul_sum, hSumE,
        hHpowC_mul, hHpowC_mul]
      congr 2; congr 1
      rw [add_zero, ← Complex.ofReal_add]; congr 1; ring
    have hPow1_H : schattenPow 1 (∑ k, matAbs (Az k)) = 1 := by
      rw [hSumAbs]
      have hstarW : (W : Mat n)ᴴ = ((star W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) := rfl
      have hW_eq : (W : Mat n) = ((star W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)ᴴ := by
        change (W : Mat n) = ((W : Mat n)ᴴ)ᴴ; rw [Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc, hstarW, schattenPow_unitary_mul_left, hW_eq,
        schattenPow_unitary_mul_conjTranspose_right zero_le_one]
      dsimp [HpowC]
      rw [schattenPow_unitary_mul_conjTranspose_right zero_le_one, schattenPow_unitary_mul_left]
      have hdiag : Matrix.diagonal (fun i => if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (p : ℂ)) =
          Matrix.diagonal (fun i => (((lam i) ^ p : ℝ) : ℂ)) := by
        ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases hl : lam i = 0
          · simp [hl, Real.zero_rpow hp0.ne']
          · simp only [hl, ↓reduceIte]
            exact (Complex.ofReal_cpow (hH_psd.eigenvalues_nonneg i) p).symm
        · simp [Matrix.diagonal, hij]
      rw [hdiag, schattenPow_diagonal zero_lt_one (fun i => (lam i) ^ p)
        (fun i => Real.rpow_nonneg (hH_psd.eigenvalues_nonneg i) _)]
      simp only [Real.rpow_one, hsum_lamp]
    exact hle1.trans ((schattenOne_sum_le_matAbs Az).trans (le_of_eq hPow1_H))
  -- 5. Right boundary bound (z.re = 1): ‖Φ z‖ ≤ leeConst p1 m n * (schattenPow p S)^(1 - 1/p1)!
  have hright : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)},
      ‖Φ z‖ ≤ leeConst p1 m n * (schattenPow p S) ^ (1 - 1 / p1) := by
    intro z hz
    have hz1 : z.re = 1 := hz
    let y : ℝ := z.im
    have hz_eq : z = 1 + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz1, y]
    let tβ : ℝ := (p / 2) * (y * (1 / p1 - 1))
    let tγ : ℝ := p * (y * (1 - 1 / p1))
    have hβ_eq : β z = (((p / (2 * p1) : ℝ) : ℂ)) + (tβ : ℂ) * Complex.I := by
      dsimp [β, α, tβ]; rw [hz_eq]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_re, Complex.normSq_ofReal]
        field_simp [hp1_pos.ne']; ring
      · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_im, Complex.normSq_ofReal]
        field_simp [hp1_pos.ne']; ring
    have hγ_eq : γ z = (((p * (1 - 1 / p1) : ℝ) : ℂ)) + (tγ : ℂ) * Complex.I := by
      dsimp [γ, α, tγ]; rw [hz_eq]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_re, Complex.normSq_ofReal]
        field_simp [hp1_pos.ne']; ring
      · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.div_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          Complex.one_im, Complex.normSq_ofReal]
        field_simp [hp1_pos.ne']; ring
    -- Apply Schatten Hölder with exponent p1 > 1!
    have hhold := norm_trace_mul_le_schattenNorm hp1_gt1 (Gz z) (Sz z)
    -- Compute schattenNorm (p1/(p1-1)) (Gz z) = (schattenPow p S)^(1 - 1/p1)!
    have hGz_norm : schattenNorm (p1 / (p1 - 1)) (Gz z) = (schattenPow p S) ^ (1 - 1 / p1) := by
      let q1 : ℝ := p1 / (p1 - 1)
      have hq1_pos : 0 < q1 := div_pos hp1_pos (by linarith)
      let phaseG : Fin n → ℂ := fun i => if σ i = 0 then 1 else (σ i : ℂ) ^ ((tγ : ℂ) * Complex.I)
      have hphaseG_unit : ((V_S : Mat n) * Matrix.diagonal phaseG) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
        rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
          Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
          ← Matrix.mul_assoc (V_S : Mat n)ᴴ (V_S : Mat n),
          unitary_conjTranspose_mul_self V_S, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
        ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Pi.star_apply, phaseG]
          by_cases hs : σ i = 0
          · simp [hs]
          · simp only [hs, ↓reduceIte]
            have hs_pos : 0 < σ i := lt_of_le_of_ne (hσ i) (Ne.symm hs)
            rw [Complex.star_def, Complex.conj_mul', Complex.norm_cpow_eq_rpow_re_of_pos hs_pos]; simp
        · simp [Matrix.diagonal, hij]
      let VG : Matrix.unitaryGroup (Fin n) ℂ := ⟨(V_S : Mat n) * Matrix.diagonal phaseG, hphaseG_unit⟩
      have hGz_svd : Gz z = (VG : Mat n) *
          Matrix.diagonal (fun i => (((σ i) ^ (p * (1 - 1 / p1)) : ℝ) : ℂ)) * (U_S : Mat n)ᴴ := by
        dsimp [Gz, VG]; rw [hγ_eq, Matrix.mul_assoc (V_S : Mat n) (Matrix.diagonal phaseG),
          Matrix.diagonal_mul_diagonal]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq, phaseG]
          by_cases hs : σ i = 0
          · have hexp_pos : 0 < p * (1 - 1 / p1) := mul_pos hp0 (by rw [sub_pos, div_lt_one hp1_pos]; exact hp1_gt1)
            simp only [hs, ↓reduceIte, Real.zero_rpow hexp_pos.ne', Complex.ofReal_zero, mul_zero]
          · simp only [hs, ↓reduceIte]
            have hs_pos : 0 < σ i := lt_of_le_of_ne (hσ i) (Ne.symm hs)
            rw [Complex.ofReal_cpow hs_pos.le, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hs), mul_comm]
        · simp [Matrix.diagonal, hij]
      unfold schattenNorm
      rw [hGz_svd, schattenPow_unitary_mul_conjTranspose_right hq1_pos.le, schattenPow_unitary_mul_left,
        schattenPow_diagonal hq1_pos _ (fun i => Real.rpow_nonneg (hσ i) _)]
      have hsum_eq : ∑ i : Fin n, ((σ i) ^ (p * (1 - 1 / p1))) ^ q1 = schattenPow p S := by
        rw [← hsum_σp]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Real.rpow_mul (hσ i)]; congr 1
        dsimp [q1]; field_simp [hp1_pos.ne', show p1 - 1 ≠ 0 by linarith]
      rw [hsum_eq]; congr 1
      have hq1_inv : 1 / (p1 / (p1 - 1)) = 1 - 1 / p1 := by field_simp [hp1_pos.ne']
      exact hq1_inv
    -- Bound schattenNorm p1 (Sz z) ≤ leeConst p1 m n!
    obtain ⟨W, hW_left, hW_right⟩ := hSplit_HpowC (p / (2 * p1)) tβ
    let Az : Fin m → Mat n := fun k => (Uk k : Mat n) * (HpowC (β z) * E k * HpowC (β z))
    have hAbs_Az : ∀ k, matAbs (Az k) =
        (W : Mat n)ᴴ * (HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k * HpowC (((p / (2 * p1) : ℝ) : ℂ))) * (W : Mat n) := by
      intro k
      have hH_herm : (HpowC (((p / (2 * p1) : ℝ) : ℂ)))ᴴ = HpowC (((p / (2 * p1) : ℝ) : ℂ)) := by
        dsimp [HpowC]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq, Pi.star_apply]; by_cases hl : lam i = 0
          · simp [hl]
          · simp only [hl, ↓reduceIte]
            have hl_pos : 0 < lam i := lt_of_le_of_ne (hH_psd.eigenvalues_nonneg i) (Ne.symm hl)
            rw [← Complex.ofReal_cpow hl_pos.le, Complex.star_def, Complex.conj_ofReal]
        · simp [Matrix.diagonal, hij]
      have hEk_psd : (HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k * HpowC (((p / (2 * p1) : ℝ) : ℂ))).PosSemidef := by
        have h1 := (hE_psd k).conjTranspose_mul_mul_same (HpowC (((p / (2 * p1) : ℝ) : ℂ)))
        rwa [hH_herm] at h1
      have hP_psd : ((W : Mat n)ᴴ * (HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k * HpowC (((p / (2 * p1) : ℝ) : ℂ))) * (W : Mat n)).PosSemidef :=
        hEk_psd.conjTranspose_mul_mul_same (W : Mat n)
      refine matAbs_eq_of_posSemidef_sq hP_psd ?_
      have hAz_eq : Az k = (((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)) *
          ((HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k * HpowC (((p / (2 * p1) : ℝ) : ℂ))) * (W : Mat n)) := by
        calc Az k = (Uk k : Mat n) * (((W : Mat n) * HpowC (((p / (2 * p1) : ℝ) : ℂ))) * E k *
              (HpowC (((p / (2 * p1) : ℝ) : ℂ)) * (W : Mat n))) := by
              dsimp [Az]; rw [hβ_eq, ← hW_left, ← hW_right]
          _ = (((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)) *
              ((HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k * HpowC (((p / (2 * p1) : ℝ) : ℂ))) * (W : Mat n)) := by
              change (Uk k : Mat n) * (((W : Mat n) * HpowC (((p / (2 * p1) : ℝ) : ℂ))) * E k *
                (HpowC (((p / (2 * p1) : ℝ) : ℂ)) * (W : Mat n))) =
                ((Uk k : Mat n) * (W : Mat n)) * ((HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k *
                HpowC (((p / (2 * p1) : ℝ) : ℂ))) * (W : Mat n))
              simp only [Matrix.mul_assoc]
      set Mk : Mat n := HpowC (((p / (2 * p1) : ℝ) : ℂ)) * E k * HpowC (((p / (2 * p1) : ℝ) : ℂ))
      calc ((W : Mat n)ᴴ * Mk * (W : Mat n)) * ((W : Mat n)ᴴ * Mk * (W : Mat n))
          = (W : Mat n)ᴴ * Mk * ((W : Mat n) * (W : Mat n)ᴴ) * Mk * (W : Mat n) := by simp only [Matrix.mul_assoc]
        _ = (W : Mat n)ᴴ * Mk * Mk * (W : Mat n) := by
            rw [unitary_mul_conjTranspose_self W, Matrix.mul_one]
        _ = (Mk * (W : Mat n))ᴴ * ((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)ᴴ *
            (((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) * (Mk * (W : Mat n))) := by
            rw [Matrix.mul_assoc ((Mk * (W : Mat n))ᴴ),
              ← Matrix.mul_assoc ((Uk k * W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)ᴴ,
              unitary_conjTranspose_mul_self (Uk k * W), Matrix.one_mul,
              Matrix.conjTranspose_mul, hEk_psd.isHermitian.eq]
            simp only [Matrix.mul_assoc]
        _ = (Az k)ᴴ * Az k := by rw [hAz_eq]; conv_rhs => rw [Matrix.conjTranspose_mul]
    have hSumAbs : ∑ k, matAbs (Az k) = (W : Mat n)ᴴ * HpowC (((p / p1 : ℝ) : ℂ)) * (W : Mat n) := by
      simp_rw [hAbs_Az]
      rw [← Finset.sum_mul, ← Matrix.mul_sum, ← Finset.sum_mul, ← Matrix.mul_sum, hSumE,
        hHpowC_mul, hHpowC_mul]
      congr 2; congr 1
      rw [add_zero, ← Complex.ofReal_add]; congr 1; field_simp [hp1_pos.ne']; ring
    have hPowp1_H : schattenPow p1 (∑ k, matAbs (Az k)) = 1 := by
      rw [hSumAbs]
      have hstarW : (W : Mat n)ᴴ = ((star W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) := rfl
      have hW_eq : (W : Mat n) = ((star W : Matrix.unitaryGroup (Fin n) ℂ) : Mat n)ᴴ := by
        change (W : Mat n) = ((W : Mat n)ᴴ)ᴴ; rw [Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc, hstarW, schattenPow_unitary_mul_left, hW_eq,
        schattenPow_unitary_mul_conjTranspose_right hp1_pos.le]
      dsimp [HpowC]
      rw [schattenPow_unitary_mul_conjTranspose_right hp1_pos.le, schattenPow_unitary_mul_left]
      have hdiag : Matrix.diagonal (fun i => if lam i = 0 then (0 : ℂ) else (lam i : ℂ) ^ (((p / p1 : ℝ) : ℂ))) =
          Matrix.diagonal (fun i => (((lam i) ^ (p / p1) : ℝ) : ℂ)) := by
        ext i j; by_cases hij : i = j
        · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases hl : lam i = 0
          · simp [hl, Real.zero_rpow (div_pos hp0 hp1_pos).ne']
          · simp only [hl, ↓reduceIte]; exact (Complex.ofReal_cpow (hH_psd.eigenvalues_nonneg i) (p / p1)).symm
        · simp [Matrix.diagonal, hij]
      rw [hdiag, schattenPow_diagonal hp1_pos (fun i => (lam i) ^ (p / p1))
        (fun i => Real.rpow_nonneg (hH_psd.eigenvalues_nonneg i) _)]
      rw [← hsum_lamp]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Real.rpow_mul (hH_psd.eigenvalues_nonneg i), div_mul_cancel₀ _ hp1_pos.ne']
    have hH_Az_ne : (∑ k, matAbs (Az k)) ≠ 0 := by
      intro h0; rw [h0, schattenPow_zero hp1_pos] at hPowp1_H; norm_num at hPowp1_H
    have hSz_le : schattenNorm p1 (Sz z) ≤ leeConst p1 m n := by
      have hrat := le_csSup (leeConst_bddAbove hp1_gt1) ⟨Az, hH_Az_ne, rfl⟩
      have hnorm1 : schattenNorm p1 (∑ k, matAbs (Az k)) = 1 := by
        unfold schattenNorm; rw [hPowp1_H, Real.one_rpow]
      unfold leeRatio at hrat; rw [hnorm1, div_one] at hrat
      exact hrat
    calc ‖Φ z‖ ≤ schattenNorm (p1 / (p1 - 1)) (Gz z) * schattenNorm p1 (Sz z) := hhold
      _ = (schattenPow p S) ^ (1 - 1 / p1) * schattenNorm p1 (Sz z) := by rw [hGz_norm]
      _ ≤ (schattenPow p S) ^ (1 - 1 / p1) * leeConst p1 m n :=
          mul_le_mul_of_nonneg_left hSz_le (Real.rpow_nonneg hSpow_pos.le _)
      _ = leeConst p1 m n * (schattenPow p S) ^ (1 - 1 / p1) := mul_comm _ _
  -- 6. Apply Hadamard's three-lines theorem at z = θ ∈ [0, 1]!
  have hθ_mem : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, hθ0.le, hθ1.le]
  have hhad := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' Φ hθ_mem
    hΦ_diff.diffContOnCl hΦ_bdd hleft hright
  simp only [Complex.ofReal_re, Real.one_rpow, one_mul] at hhad
  rw [hΦ_θ, Complex.norm_real, Real.norm_of_nonneg hSpow_pos.le] at hhad
  have hC1_nn : 0 ≤ leeConst p1 m n := by
    obtain ⟨B, _, hB_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := n) hp1_gt1 hm hn
    rw [← hB_eq]; unfold leeRatio; exact div_nonneg (schattenNorm_nonneg p1 _) (schattenNorm_nonneg p1 _)
  rw [Real.mul_rpow hC1_nn (Real.rpow_nonneg hSpow_pos.le _), ← Real.rpow_mul hSpow_pos.le] at hhad
  -- Note (1 - 1/p1) * θ = 1 - 1/p! Divide both sides by (schattenPow p S)^(1 - 1/p) > 0!
  have hexp : (1 - 1 / p1) * θ = 1 - 1 / p := by rw [hinterp]; ring
  rw [hexp] at hhad
  have hsplit : schattenPow p S = (schattenNorm p S) * (schattenPow p S) ^ (1 - 1 / p) := by
    unfold schattenNorm
    rw [← Real.rpow_add hSpow_pos, show 1 / p + (1 - 1 / p) = 1 by ring, Real.rpow_one]
  conv_lhs at hhad => rw [hsplit]
  exact le_of_mul_le_mul_right hhad (Real.rpow_pos_of_pos hSpow_pos _)

/-- Corollary (Theorem 6 — Dimension-Free Subquadratic Upper Bound from p = 2):
    For every 1 < p < 2, m ≥ 1, n ≥ 1,
      C_{p,m}(n) ≤ (C_{2,m}(n)) ^ (2 - 2 / p). -/
theorem theorem6_p2_upper_bound {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    leeConst p m n ≤ (leeConst 2 m n) ^ (2 - 2 / p) := by
  have hp0 : 0 < p := by linarith
  have hθ0 : 0 < 2 - 2 / p := by
    have : 2 / p < 2 := (div_lt_iff₀ hp0).mpr (by linarith)
    linarith
  have hθ1 : 2 - 2 / p < 1 := by
    have : 1 < 2 / p := (one_lt_div hp0).mpr hp2
    linarith
  have hinterp : 1 / p = (1 - (2 - 2 / p)) + (2 - 2 / p) / 2 := by ring
  exact theorem6_interp_from_one hm hn hp1 hp2 hθ0 hθ1 hinterp

end MI20
