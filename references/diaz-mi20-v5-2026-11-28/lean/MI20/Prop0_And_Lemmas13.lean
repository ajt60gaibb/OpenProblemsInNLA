/-
  MI20/Prop0_And_Lemmas13.lean
  ============================
  Author: Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Proposition 0 (Schatten-p subgradient bound), Lemma 1 (universal rank deficiency), and Lemma 3 (polar optimality).
-/

import MI20.SpectralBasics
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ### Canonical Dual Operator G_S := U_S * diag(σ^(p-1)) * V_Sᴴ -/

/-- Dual operator G_S built from an SVD of S, satisfying G_Sᴴ * S = diag(σ^p) in V-basis. -/
def dualOp (p : ℝ) {n : ℕ} (S : Mat n) : Mat n :=
  let h := exists_svd S
  let U := h.choose
  let V := h.choose_spec.choose
  let σ := h.choose_spec.choose_spec.choose
  (U : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (V : Mat n)ᴴ

lemma exists_svd_dualOp (p : ℝ) {n : ℕ} (S : Mat n) :
    ∃ (U V : Matrix.unitaryGroup (Fin n) ℂ) (σ : Fin n → ℝ),
      (∀ i, 0 ≤ σ i) ∧
      S = (U : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (V : Mat n)ᴴ ∧
      dualOp p S = (U : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (V : Mat n)ᴴ ∧
      ∀ q : ℝ, 0 < q → schattenPow q S = ∑ i : Fin n, (σ i) ^ q := by
  dsimp only [dualOp]
  exact ⟨_, _, _, (exists_svd S).choose_spec.choose_spec.choose_spec.1,
    (exists_svd S).choose_spec.choose_spec.choose_spec.2.1, rfl,
    (exists_svd S).choose_spec.choose_spec.choose_spec.2.2⟩

lemma dualOp_trace_self {n : ℕ} {p : ℝ} (hp : 1 < p) (S : Mat n) :
    ((dualOp p S)ᴴ * S).trace.re = schattenPow p S := by
  obtain ⟨U, V, σ, hσ_nn, hSVD, hDual, hPow⟩ := exists_svd_dualOp p S
  rw [hDual]
  have hD : (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)))ᴴ =
      Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) := by
    ext i j; by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hprod : ((U : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (V : Mat n)ᴴ)ᴴ * S =
      (V : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ p : ℝ) : ℂ)) * (V : Mat n)ᴴ := by
    conv_lhs => rw [hSVD]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      rw [← Complex.ofReal_mul]
      congr 1
      by_cases h0 : σ i = 0
      · rw [h0, Real.zero_rpow (by linarith : p - 1 ≠ 0), zero_mul, Real.zero_rpow (by linarith : p ≠ 0)]
      · have hpos : 0 < σ i := lt_of_le_of_ne (hσ_nn i) (Ne.symm h0)
        rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
    · simp [Matrix.diagonal, hij]
  rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self V, Matrix.one_mul,
    Matrix.trace_diagonal, Complex.re_sum, hPow p (by linarith)]
  simp

/-! ### Proposition 0: Elementary Schatten-p Subgradient Bound (via Doubly-Stochastic Parseval + Young) -/

/-- Doubly-stochastic Parseval + AM-GM + Young bound:
    Re Tr(G_Sᴴ Y) ≤ ((p - 1)/p) ‖S‖_p^p + (1/p) ‖Y‖_p^p. -/
theorem re_trace_dualOp_le {n : ℕ} {p : ℝ} (hp : 1 < p) (S Y : Mat n) :
    ((dualOp p S)ᴴ * Y).trace.re ≤
      ((p - 1) / p) * schattenPow p S + (1 / p) * schattenPow p Y := by
  obtain ⟨Us, Vs, σ, hσ_nn, _, hDual, hPowS⟩ := exists_svd_dualOp p S
  obtain ⟨Uy, Vy, τ, hτ_nn, hSVDy, hPowY⟩ := exists_svd Y
  rw [hDual, hPowS p (by linarith), hPowY p (by linarith)]
  -- Set A := Usᴴ * Uy and B := Vyᴴ * Vs (both unitary!)
  let Au : Matrix.unitaryGroup (Fin n) ℂ := star Us * Uy
  let Bu : Matrix.unitaryGroup (Fin n) ℂ := star Vy * Vs
  let A : Mat n := (Au : Mat n)
  let B : Mat n := (Bu : Mat n)
  have hA_unit : A ∈ Matrix.unitaryGroup (Fin n) ℂ := Au.2
  have hB_unit : B ∈ Matrix.unitaryGroup (Fin n) ℂ := Bu.2
  -- Compute Tr(G_Sᴴ * Y) = ∑ i, ∑ j, σ_i^(p-1) * τ_j * (A i j * B j i)
  have hD : (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)))ᴴ =
      Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) := by
    ext i j; by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hTr : (((Us : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (Vs : Mat n)ᴴ)ᴴ * Y).trace =
      ∑ i : Fin n, ∑ j : Fin n,
        (((σ i) ^ (p - 1) * τ j : ℝ) : ℂ) * (A i j * B j i) := by
    conv_lhs => rw [hSVDy]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD]
    -- Cycle Vs to the right to form B = Vyᴴ * Vs and A = Usᴴ * Uy
    have hA_eq : (Us : Mat n)ᴴ * (Uy : Mat n) = A := rfl
    have hB_eq : (Vy : Mat n)ᴴ * (Vs : Mat n) = B := rfl
    have h1 : ((Vs : Mat n) * (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * (Us : Mat n)ᴴ)) *
        ((Uy : Mat n) * Matrix.diagonal (fun j => (τ j : ℂ)) * (Vy : Mat n)ᴴ) =
        (Vs : Mat n) * (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * A *
          Matrix.diagonal (fun j => (τ j : ℂ)) * (Vy : Mat n)ᴴ) := by
      simp only [← hA_eq, Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm (Vs : Mat n)]
    have h2 : (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * A *
        Matrix.diagonal (fun j => (τ j : ℂ)) * (Vy : Mat n)ᴴ) * (Vs : Mat n) =
        (Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) * A) *
        (Matrix.diagonal (fun j => (τ j : ℂ)) * B) := by
      simp only [← hB_eq, Matrix.mul_assoc]
    rw [h2, Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    push_cast; ring
  rw [hTr, Complex.re_sum]
  simp_rw [Complex.re_sum]
  -- Define doubly stochastic matrix W i j := (‖A i j‖^2 + ‖B j i‖^2) / 2
  let W : Fin n → Fin n → ℝ := fun i j => (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2
  have hW_nn : ∀ i j, 0 ≤ W i j := fun i j => by positivity
  -- Row sums of W equal 1
  have hRowA : ∀ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Au) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ‖A i j‖ ^ 2 = (A i j * star (A i j)).re
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColA : ∀ j : Fin n, ∑ i : Fin n, ‖A i j‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Au) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖A i j‖ ^ 2 = (star (A i j) * A i j).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hRowB : ∀ j : Fin n, ∑ i : Fin n, ‖B j i‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Bu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖B j i‖ ^ 2 = (B j i * star (B j i)).re
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColB : ∀ i : Fin n, ∑ j : Fin n, ‖B j i‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Bu) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ‖B j i‖ ^ 2 = (star (B j i) * B j i).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hW_row : ∀ i : Fin n, ∑ j : Fin n, W i j = 1 := fun i => by
    simp only [W, ← Finset.sum_div, Finset.sum_add_distrib, hRowA i, hColB i]; norm_num
  have hW_col : ∀ j : Fin n, ∑ i : Fin n, W i j = 1 := fun j => by
    simp only [W, ← Finset.sum_div, Finset.sum_add_distrib, hColA j, hRowB j]; norm_num
  -- Pointwise bound: Re((σ_i^(p-1) τ_j) * (A i j * B j i)) ≤ W i j * (((p-1)/p) σ_i^p + (1/p) τ_j^p)
  have hterm : ∀ i j : Fin n,
      ((((σ i) ^ (p - 1) * τ j : ℝ) : ℂ) * (A i j * B j i)).re ≤
        W i j * (((p - 1) / p) * (σ i) ^ p + (1 / p) * (τ j) ^ p) := by
    intro i j
    have hcoeff_nn : 0 ≤ (σ i) ^ (p - 1) * τ j :=
      mul_nonneg (Real.rpow_nonneg (hσ_nn i) _) (hτ_nn j)
    have hre1 : ((((σ i) ^ (p - 1) * τ j : ℝ) : ℂ) * (A i j * B j i)).re =
        ((σ i) ^ (p - 1) * τ j) * (A i j * B j i).re := by simp
    rw [hre1]
    have hAM : (A i j * B j i).re ≤ W i j := by
      change (A i j * B j i).re ≤ (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2
      have h1 : (A i j * B j i).re ≤ ‖A i j * B j i‖ := Complex.re_le_norm _
      have h2 : ‖A i j * B j i‖ = ‖A i j‖ * ‖B j i‖ := norm_mul _ _
      have h3 : ‖A i j‖ * ‖B j i‖ ≤ (‖A i j‖ ^ 2 + ‖B j i‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖A i j‖ - ‖B j i‖)]
      linarith
    have hYoung : (σ i) ^ (p - 1) * τ j ≤ ((p - 1) / p) * (σ i) ^ p + (1 / p) * (τ j) ^ p := by
      have hp0 : 0 < p := by linarith
      have hw1 : 0 ≤ (p - 1) / p := by positivity
      have hw2 : 0 ≤ 1 / p := by positivity
      have hsum : (p - 1) / p + 1 / p = 1 := by field_simp [hp0.ne']; ring
      have hY := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
        (Real.rpow_nonneg (hσ_nn i) p) (Real.rpow_nonneg (hτ_nn j) p) hsum
      have hL1 : ((σ i) ^ p) ^ ((p - 1) / p) = (σ i) ^ (p - 1) := by
        rw [← Real.rpow_mul (hσ_nn i)]
        congr 1; field_simp [hp0.ne']
      have hL2 : ((τ j) ^ p) ^ (1 / p) = τ j := by
        rw [← Real.rpow_mul (hτ_nn j)]
        have : p * (1 / p) = 1 := by field_simp [hp0.ne']
        rw [this, Real.rpow_one]
      rwa [hL1, hL2] at hY
    calc ((σ i) ^ (p - 1) * τ j) * (A i j * B j i).re
        ≤ ((σ i) ^ (p - 1) * τ j) * W i j := mul_le_mul_of_nonneg_left hAM hcoeff_nn
      _ = W i j * ((σ i) ^ (p - 1) * τ j) := mul_comm _ _
      _ ≤ W i j * (((p - 1) / p) * (σ i) ^ p + (1 / p) * (τ j) ^ p) :=
          mul_le_mul_of_nonneg_left hYoung (hW_nn i j)
  calc ∑ i : Fin n, ∑ j : Fin n, ((((σ i) ^ (p - 1) * τ j : ℝ) : ℂ) * (A i j * B j i)).re
      ≤ ∑ i : Fin n, ∑ j : Fin n, W i j * (((p - 1) / p) * (σ i) ^ p + (1 / p) * (τ j) ^ p) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (W i j * (((p - 1) / p) * (σ i) ^ p) + W i j * ((1 / p) * (τ j) ^ p)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ i : Fin n, ∑ j : Fin n, W i j * (((p - 1) / p) * (σ i) ^ p)) +
        (∑ i : Fin n, ∑ j : Fin n, W i j * ((1 / p) * (τ j) ^ p)) := by
        simp only [Finset.sum_add_distrib]
    _ = ((p - 1) / p) * ∑ i : Fin n, (σ i) ^ p + (1 / p) * ∑ j : Fin n, (τ j) ^ p := by
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_mul, hW_row i, one_mul]
        · rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, hW_col j, one_mul]

/-- Proposition 0 (Elementary Schatten-p Subgradient Bound):
    (1/p) ‖Y‖_p^p ≥ (1/p) ‖S‖_p^p + Re Tr(G_Sᴴ (Y - S)). -/
theorem prop0_subgradient_bound {n : ℕ} {p : ℝ} (hp : 1 < p) (S Y : Mat n) :
    (1 / p) * schattenPow p S + ((dualOp p S)ᴴ * (Y - S)).trace.re ≤
      (1 / p) * schattenPow p Y := by
  have h1 := re_trace_dualOp_le hp S Y
  have h2 := dualOp_trace_self hp S
  have hsub : ((dualOp p S)ᴴ * (Y - S)).trace.re =
      ((dualOp p S)ᴴ * Y).trace.re - ((dualOp p S)ᴴ * S).trace.re := by
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  have hp0 : p ≠ 0 := by linarith
  have hsplit : ((p - 1) / p) * schattenPow p S + (1 / p) * schattenPow p S = schattenPow p S := by
    have : (p - 1) / p + 1 / p = 1 := by field_simp [hp0]; ring
    rw [← add_mul, this, one_mul]
  linarith

/-! ### Lemma 3: Polar Optimality (A_k G_Sᴴ ⪰ 0 and G_Sᴴ(ker A_kᴴ) ⊆ ker A_k) -/

/-- Lemma 3 (Polar Optimality): At any maximizer (A_1,...,A_m) of leeRatio p,
    A_k * (dualOp p S)ᴴ is positive semidefinite for every k. -/
theorem lemma3_polar_optimality {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Mat n)
    (hmax : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) = (∑ j, matAbs (A j)) →
      schattenPow p (∑ j, B j) ≤ schattenPow p (∑ j, A j))
    (k : Fin m) :
    (A k * (dualOp p (∑ j, A j))ᴴ).PosSemidef := by
  set S : Mat n := ∑ j, A j
  set G : Mat n := dualOp p S
  obtain ⟨Uk, hUk⟩ := exists_polar_unitary (A k)
  set Pk : Mat n := matAbs (A k)
  set Z : Mat n := Pk * Gᴴ
  obtain ⟨W1, W2, σ, hσ_nn, hSVD_Z, _⟩ := exists_svd Z
  -- Variational inequality: for every unitary U, Re Tr(Z * U) ≤ Re Tr(Z * Uk)
  have hvar : ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (Z * (U : Mat n)).trace.re ≤ (Z * (Uk : Mat n)).trace.re := by
    intro U
    let B : Fin m → Mat n := Function.update A k ((U : Mat n) * Pk)
    have hH : ∑ j, matAbs (B j) = ∑ j, matAbs (A j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjk : j = k
      · subst hjk
        simp only [B, Function.update_self, matAbs_unitary_mul, Pk, matAbs_of_posSemidef (matAbs_posSemidef _)]
      · simp [B, Function.update_of_ne hjk]
    have hle : schattenPow p (∑ j, B j) ≤ schattenPow p S := hmax B hH
    have hdiff : (∑ j, B j) - S = ((U : Mat n) - (Uk : Mat n)) * Pk := by
      have hsum : ∑ j, B j = S - A k + (U : Mat n) * Pk := by
        have h1 := Finset.sum_update_of_mem (Finset.mem_univ k) A ((U : Mat n) * Pk)
        have h2 := Finset.add_sum_erase Finset.univ A (Finset.mem_univ k)
        change ∑ j, Function.update A k ((U : Mat n) * Pk) j = _
        rw [h1, Finset.sdiff_singleton_eq_erase]
        change A k + ∑ x ∈ Finset.univ.erase k, A x = S at h2
        have h3 : ∑ j ∈ Finset.univ.erase k, A j = S - A k := by rw [← h2]; abel
        rw [h3]; abel
      rw [hsum, hUk]
      simp only [Matrix.sub_mul]
      abel
    have hsub := prop0_subgradient_bound hp S (∑ j, B j)
    have hnonpos : (Gᴴ * ((∑ j, B j) - S)).trace.re ≤ 0 := by
      have hp0 : 0 < 1 / p := one_div_pos.mpr (by linarith)
      nlinarith
    rw [hdiff] at hnonpos
    have hcyc : (Gᴴ * (((U : Mat n) - (Uk : Mat n)) * Pk)).trace =
        (Z * (U : Mat n)).trace - (Z * (Uk : Mat n)).trace := by
      rw [Matrix.trace_mul_comm Gᴴ, Matrix.mul_assoc,
        Matrix.trace_mul_comm ((U : Mat n) - (Uk : Mat n)), Matrix.mul_sub, Matrix.trace_sub]
    rw [hcyc, Complex.sub_re] at hnonpos
    linarith
  -- Test U := W2 * star W1 (so Z * U = W1 * diag(σ) * W1ᴴ has trace ∑ σ_i)
  let Utest : Matrix.unitaryGroup (Fin n) ℂ := W2 * star W1
  have hTrTest : (Z * (Utest : Mat n)).trace.re = ∑ i : Fin n, σ i := by
    change (Z * ((W2 : Mat n) * (W1 : Mat n)ᴴ)).trace.re = _
    rw [hSVD_Z]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (W2 : Mat n)ᴴ (W2 : Mat n), unitary_conjTranspose_mul_self W2,
      Matrix.one_mul, Matrix.trace_mul_comm (W1 : Mat n), Matrix.mul_assoc,
      unitary_conjTranspose_mul_self W1, Matrix.mul_one, Matrix.trace_diagonal, Complex.re_sum]
    simp
  -- Set Q := W2ᴴ * Uk * W1 (unitary); then Re Tr(diag(σ) * Q) = ∑ σ_i * Re(Q i i) ≥ ∑ σ_i
  let Q : Matrix.unitaryGroup (Fin n) ℂ := star W2 * Uk * W1
  set Qm : Mat n := (Q : Mat n)
  have hTrQ : (Z * (Uk : Mat n)).trace.re = ∑ i : Fin n, σ i * (Qm i i).re := by
    rw [hSVD_Z]
    have h1 : ((W1 : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (W2 : Mat n)ᴴ * (Uk : Mat n)).trace =
        (Matrix.diagonal (fun i => (σ i : ℂ)) * Qm).trace := by
      change ((W1 : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (W2 : Mat n)ᴴ * (Uk : Mat n)).trace =
        (Matrix.diagonal (fun i => (σ i : ℂ)) * ((W2 : Mat n)ᴴ * (Uk : Mat n) * (W1 : Mat n))).trace
      rw [Matrix.mul_assoc (W1 : Mat n), Matrix.mul_assoc (W1 : Mat n), Matrix.trace_mul_comm (W1 : Mat n)]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace]
    simp [Matrix.diag, Matrix.mul_apply, Matrix.diagonal, Complex.re_sum]
  have hQ_col_norm : ∀ i : Fin n, ∑ k : Fin n, ‖Qm k i‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Q) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun k _ => ?_
    change ‖Qm k i‖ ^ 2 = (star (Qm k i) * Qm k i).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hQ_le : ∀ i : Fin n, (Qm i i).re ≤ 1 := by
    intro i
    have h1 : (Qm i i).re ≤ ‖Qm i i‖ := Complex.re_le_norm _
    have h2 : ‖Qm i i‖ ^ 2 ≤ 1 := by
      rw [← hQ_col_norm i]
      exact Finset.single_le_sum (f := fun k => ‖Qm k i‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [norm_nonneg (Qm i i)]
  have hsum_ge : ∑ i : Fin n, σ i ≤ ∑ i : Fin n, σ i * (Qm i i).re := by
    rw [← hTrTest, ← hTrQ]; exact hvar Utest
  -- Equality forces for every i with σ i > 0: Q i i = 1 and Q j i = 0 for j ≠ i!
  have hQ_diag : ∀ i : Fin n, σ i ≠ 0 → Qm i i = 1 ∧ ∀ j, j ≠ i → Qm j i = 0 := by
    intro i hσi
    have hσpos : 0 < σ i := lt_of_le_of_ne (hσ_nn i) (Ne.symm hσi)
    have hRe_eq : (Qm i i).re = 1 := by
      by_contra hne
      have hlt : (Qm i i).re < 1 := lt_of_le_of_ne (hQ_le i) hne
      have hstrict : ∑ k : Fin n, σ k * (Qm k k).re < ∑ k : Fin n, σ k := by
        apply Finset.sum_lt_sum
        · intro k _; nlinarith [hσ_nn k, hQ_le k]
        · exact ⟨i, Finset.mem_univ i, by nlinarith⟩
      linarith
    have hColNorm := hQ_col_norm i
    have hQii_ge : 1 ≤ ‖Qm i i‖ ^ 2 := by
      have h1 : (Qm i i).re ≤ ‖Qm i i‖ := Complex.re_le_norm _
      nlinarith
    have hQii_le : ‖Qm i i‖ ^ 2 ≤ 1 := by
      rw [← hColNorm]
      exact Finset.single_le_sum (f := fun j => ‖Qm j i‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hQii_im : (Qm i i).im = 0 := by
      have hsq : ‖Qm i i‖ ^ 2 = (Qm i i).re ^ 2 + (Qm i i).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      nlinarith
    have hQii_one : Qm i i = 1 := Complex.ext (by simpa using hRe_eq) (by simpa using hQii_im)
    refine ⟨hQii_one, fun j hji => ?_⟩
    have hrest : ∑ k ∈ Finset.univ.erase i, ‖Qm k i‖ ^ 2 = 0 := by
      have hadd := Finset.add_sum_erase Finset.univ (fun k => ‖Qm k i‖ ^ 2) (Finset.mem_univ i)
      linarith
    have hj0 : ‖Qm j i‖ ^ 2 = 0 := by
      have hle' := Finset.single_le_sum (f := fun k => ‖Qm k i‖ ^ 2)
        (fun k _ => sq_nonneg ‖Qm k i‖) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      linarith [sq_nonneg ‖Qm j i‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj0)
  -- Therefore Q * diag(σ) = diag(σ)!
  have hQ_mul_D : Qm * Matrix.diagonal (fun i => (σ i : ℂ)) =
      Matrix.diagonal (fun i => (σ i : ℂ)) := by
    ext j i
    simp only [Matrix.mul_diagonal]
    by_cases hσi : σ i = 0
    · by_cases hji : j = i <;> simp [hσi, Matrix.diagonal, hji]
    · obtain ⟨h1, h0⟩ := hQ_diag i hσi
      by_cases hji : j = i
      · subst hji; simp [h1]
      · simp [h0 j hji, Matrix.diagonal, hji]
  -- Hence A k * Gᴴ = Uk * Z = W2 * (Q * diag(σ)) * W2ᴴ = W2 * diag(σ) * W2ᴴ ⪰ 0!
  have hEq : A k * Gᴴ = (W2 : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (W2 : Mat n)ᴴ := by
    calc A k * Gᴴ = (Uk : Mat n) * Z := by rw [hUk, Matrix.mul_assoc]
      _ = (Uk : Mat n) * ((W1 : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (W2 : Mat n)ᴴ) := by rw [hSVD_Z]
      _ = (W2 : Mat n) * ((W2 : Mat n)ᴴ * (Uk : Mat n) * (W1 : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ))) * (W2 : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc (W2 : Mat n) (W2 : Mat n)ᴴ, unitary_mul_conjTranspose_self W2, Matrix.one_mul]
      _ = (W2 : Mat n) * (Qm * Matrix.diagonal (fun i => (σ i : ℂ))) * (W2 : Mat n)ᴴ := rfl
      _ = (W2 : Mat n) * Matrix.diagonal (fun i => (σ i : ℂ)) * (W2 : Mat n)ᴴ := by rw [hQ_mul_D]
  rw [hEq]
  have hdiag : (Matrix.diagonal (fun i => (σ i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i; exact_mod_cast hσ_nn i
  simpa using hdiag.mul_mul_conjTranspose_same (W2 : Mat n)

/-- Corollary of Lemma 3: G_Sᴴ maps ker(A_kᴴ) into ker(A_k). -/
theorem lemma3_kernel_map {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Mat n)
    (hmax : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) = (∑ j, matAbs (A j)) →
      schattenPow p (∑ j, B j) ≤ schattenPow p (∑ j, A j))
    (k : Fin m) (u : Fin n → ℂ) (hu : (A k)ᴴ.mulVec u = 0) :
    (A k).mulVec ((dualOp p (∑ j, A j))ᴴ.mulVec u) = 0 := by
  have hH : (A k * (dualOp p (∑ j, A j))ᴴ).IsHermitian :=
    (lemma3_polar_optimality hp A hmax k).isHermitian
  rw [Matrix.mulVec_mulVec, ← hH.eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]

/-! ### Helper lemmas for Hermitian and PSD quadratic forms -/

lemma isHermitian_im_dotProduct_mulVec_self {n : ℕ} {M : Mat n} (hM : M.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ M.mulVec x).im = 0 := by
  have hstar : star (star x ⬝ᵥ M.mulVec x) = star x ⬝ᵥ M.mulVec x := by
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Pi.star_apply, star_star,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : star (M j i) = M i j := by
      have := congr_fun (congr_fun hM.eq i) j
      simpa [Matrix.conjTranspose_apply] using this
    rw [hij]; ring
  have him := congrArg Complex.im hstar
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

lemma posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero {n : ℕ} {M : Mat n} (hM : M.PosSemidef)
    (x : Fin n → ℂ) (hx : (star x ⬝ᵥ M.mulVec x).re = 0) : M.mulVec x = 0 := by
  let S : Mat n := CFC.sqrt M
  have hM_nn : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  have hS_sq : S * S = M := CFC.sqrt_mul_sqrt_self M hM_nn
  have hS_herm : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian
  have hdot : star (S.mulVec x) ⬝ᵥ S.mulVec x = star x ⬝ᵥ M.mulVec x := by
    rw [← hS_sq, ← Matrix.mulVec_mulVec]
    have hlin := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin S)
      (WithLp.toLp 2 x) (Matrix.toEuclideanLin S (WithLp.toLp 2 x))
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hS_herm.eq] at hlin
    simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
      Matrix.toEuclideanLin] at hlin
    rw [dotProduct_comm (star (S *ᵥ x)), dotProduct_comm (star x)]
    exact hlin.symm
  have hsum : ∑ i : Fin n, ‖(S.mulVec x) i‖ ^ 2 = 0 := by
    have hre := congrArg Complex.re hdot
    rw [hx] at hre
    rw [← hre]
    simp only [dotProduct, Complex.re_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hSx : S.mulVec x = 0 := by
    ext i
    have hi : ‖(S.mulVec x) i‖ ^ 2 = 0 := by
      have hle := Finset.single_le_sum (f := fun k => ‖(S.mulVec x) k‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      linarith [sq_nonneg ‖(S.mulVec x) i‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  rw [← hS_sq, ← Matrix.mulVec_mulVec, hSx, Matrix.mulVec_zero]

/-! ### Lemma 1: Universal Rank Deficiency of Maximizers (5-line scaling proof!) -/

/-- Lemma 1 (Universal Rank Deficiency): At any maximizer with C > 1,
    for every k there exists a nonzero v ∈ ran(H) with A_k *ᵥ v = 0. -/
theorem lemma1_universal_rank_deficiency {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Mat n)
    (hH_ne : (∑ j, matAbs (A j)) ≠ 0)
    (hC_gt : 1 < leeRatio p A)
    (hmax : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) ≠ 0 → leeRatio p B ≤ leeRatio p A)
    (k : Fin m) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧ v ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))) ∧
      (A k).mulVec v = 0 := by
  set S : Mat n := ∑ j, A j
  set H : Mat n := ∑ j, matAbs (A j)
  set C : ℝ := leeRatio p A
  set Pk : Mat n := matAbs (A k)
  have hH_psd : H.PosSemidef := by
    have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using Matrix.PosSemidef.zero
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (matAbs_posSemidef (A a)).add ih
    exact this Finset.univ
  -- Suppose for contradiction that ker(A_k) ∩ ran(H) = {0}.
  by_contra hno
  push Not at hno
  -- Step 1: Show ∃ δ > 0 such that Pk - δ • H is PosSemidef!
  have hker_sub : ∀ x : Fin n → ℂ, H.mulVec x = 0 → Pk.mulVec x = 0 := by
    intro x hx
    have h0 : (star x ⬝ᵥ H.mulVec x).re = 0 := by rw [hx, dotProduct_zero, Complex.zero_re]
    have hle : (star x ⬝ᵥ Pk.mulVec x).re ≤ (star x ⬝ᵥ H.mulVec x).re := by
      have hdiff : (H - Pk).PosSemidef := by
        have heq : H - Pk = ∑ j ∈ Finset.univ.erase k, matAbs (A j) := by
          have := Finset.add_sum_erase Finset.univ (fun j => matAbs (A j)) (Finset.mem_univ k)
          change (∑ j, matAbs (A j)) - matAbs (A k) = _
          rw [← this]; abel
        rw [heq]
        have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
          intro s; induction s using Finset.induction_on with
          | empty => simpa using Matrix.PosSemidef.zero
          | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
        exact this _
      have hnn : 0 ≤ (star x ⬝ᵥ (H - Pk).mulVec x).re := by
        simpa [RCLike.re_to_complex] using hdiff.re_dotProduct_nonneg x
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hnn
      linarith
    have hge : 0 ≤ (star x ⬝ᵥ Pk.mulVec x).re := by
      simpa [RCLike.re_to_complex] using (matAbs_posSemidef (A k)).re_dotProduct_nonneg x
    exact posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero (matAbs_posSemidef (A k)) x (by linarith)
  -- Using orthogonal projection onto ran(H), decompose any x into ran(H) + ker(H)
  have hdelta : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ (Pk - (δ : ℂ) • H).PosSemidef := by
    let V : Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
      LinearMap.range (Matrix.toEuclideanLin H)
    let SV : Set (EuclideanSpace ℂ (Fin n)) := { v | v ∈ V ∧ ‖v‖ = 1 }
    have hSV_compact : IsCompact SV := by
      have hSV_eq : SV = (V : Set (EuclideanSpace ℂ (Fin n))) ∩ Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 := by
        ext v; simp [SV]
      rw [hSV_eq]
      exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).inter_left
        (Submodule.closed_of_finiteDimensional V)
    have hSV_ne : SV.Nonempty := by
      have hVne : ∃ v : EuclideanSpace ℂ (Fin n), v ∈ V ∧ v ≠ 0 := by
        by_contra hall; push Not at hall
        apply hH_ne
        apply Matrix.toEuclideanLin.injective
        refine LinearMap.ext fun x => ?_
        simpa using hall (Matrix.toEuclideanLin H x) ⟨x, rfl⟩
      obtain ⟨v, hvV, hv0⟩ := hVne
      refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, V.smul_mem _ hvV, ?_⟩
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
    let f : EuclideanSpace ℂ (Fin n) → ℝ := fun v => (star v.ofLp ⬝ᵥ Pk.mulVec v.ofLp).re
    let g : EuclideanSpace ℂ (Fin n) → ℝ := fun v => (star v.ofLp ⬝ᵥ H.mulVec v.ofLp).re
    have hf_cont : Continuous f := by
      have : f = fun v => (inner ℂ v (Matrix.toEuclideanLin Pk v)).re := by
        ext v; rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
      rw [this]
      exact Complex.continuous_re.comp (continuous_id.inner (Matrix.toEuclideanLin Pk).continuous_of_finiteDimensional)
    have hg_cont : Continuous g := by
      have : g = fun v => (inner ℂ v (Matrix.toEuclideanLin H v)).re := by
        ext v; rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
      rw [this]
      exact Complex.continuous_re.comp (continuous_id.inner (Matrix.toEuclideanLin H).continuous_of_finiteDimensional)
    obtain ⟨vMin, hvMin_mem, hvMin_le⟩ := hSV_compact.exists_isMinOn hSV_ne hf_cont.continuousOn
    obtain ⟨vMax, hvMax_mem, hvMax_ge⟩ := hSV_compact.exists_isMaxOn hSV_ne hg_cont.continuousOn
    have hf_pos : 0 < f vMin := by
      have hge : 0 ≤ f vMin := by
        simpa [f, RCLike.re_to_complex] using (matAbs_posSemidef (A k)).re_dotProduct_nonneg vMin.ofLp
      refine lt_of_le_of_ne hge (Ne.symm fun h0 => ?_)
      have hPk0 : Pk.mulVec vMin.ofLp = 0 :=
        posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero (matAbs_posSemidef (A k)) vMin.ofLp h0
      have hAk0 : (A k).mulVec vMin.ofLp = 0 := by
        have hsq : ((A k)ᴴ * A k).mulVec vMin.ofLp = 0 := by
          rw [← matAbs_mul_self, ← Matrix.mulVec_mulVec, hPk0, Matrix.mulVec_zero]
        have hdot : star vMin.ofLp ⬝ᵥ ((A k)ᴴ * A k).mulVec vMin.ofLp = 0 := by
          rw [hsq, dotProduct_zero]
        have hin : inner ℂ (Matrix.toEuclideanLin (A k) vMin) (Matrix.toEuclideanLin (A k) vMin) = 0 := by
          rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, ← toEuclideanLin_gram,
            EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
          exact hdot
        exact congrArg WithLp.ofLp (inner_self_eq_zero.mp hin)
      have hv_ne : vMin.ofLp ≠ 0 := by
        intro h
        have hv0 : vMin = 0 := WithLp.ofLp_injective 2 h
        have h1 : ‖vMin‖ = 1 := hvMin_mem.2
        rw [hv0, norm_zero] at h1; norm_num at h1
      have hv_ran : vMin.ofLp ∈ LinearMap.range (Matrix.mulVecLin H) := by
        obtain ⟨y, hy⟩ := hvMin_mem.1
        exact ⟨y.ofLp, congrArg WithLp.ofLp hy⟩
      exact hno vMin.ofLp hv_ne hv_ran hAk0
    have hg_pos : 0 < g vMax := by
      have hge : 0 ≤ g vMax := by
        simpa [g, RCLike.re_to_complex] using hH_psd.re_dotProduct_nonneg vMax.ofLp
      refine lt_of_le_of_ne hge (Ne.symm fun h0 => ?_)
      have hH0 : H.mulVec vMax.ofLp = 0 :=
        posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero hH_psd vMax.ofLp h0
      obtain ⟨y, hy⟩ := hvMax_mem.1
      have hnorm : inner ℂ vMax vMax = 0 := by
        calc inner ℂ vMax vMax = inner ℂ (Matrix.toEuclideanLin H y) vMax := by rw [hy]
          _ = inner ℂ y ((Matrix.toEuclideanLin H).adjoint vMax) := (LinearMap.adjoint_inner_right _ _ _).symm
          _ = inner ℂ y (Matrix.toEuclideanLin H vMax) := by
                rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH_psd.isHermitian.eq]
          _ = 0 := by
                have : Matrix.toEuclideanLin H vMax = 0 := WithLp.ofLp_injective 2 hH0
                rw [this, inner_zero_right]
      have hv0 : vMax = 0 := inner_self_eq_zero.mp hnorm
      have h1 : ‖vMax‖ = 1 := hvMax_mem.2
      rw [hv0, norm_zero] at h1; norm_num at h1
    let δ : ℝ := min (1 / 2) (f vMin / g vMax)
    have hδ_pos : 0 < δ := lt_min (by norm_num) (div_pos hf_pos hg_pos)
    have hδ_lt1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨δ, hδ_pos, hδ_lt1, ?_⟩
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    have hHerm : (Pk - (δ : ℂ) • H).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        (matAbs_isHermitian (A k)).eq, hH_psd.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
    refine ⟨hHerm, fun x => ?_⟩
    let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
    let vV : EuclideanSpace ℂ (Fin n) := V.starProjection xE
    let vK : EuclideanSpace ℂ (Fin n) := xE - vV
    have hvK_kerH : H.mulVec vK.ofLp = 0 := by
      have hvK_orth : vK ∈ Vᗮ := Submodule.sub_starProjection_mem_orthogonal xE
      have h2 : inner ℂ (Matrix.toEuclideanLin H vK) (Matrix.toEuclideanLin H vK) = 0 := by
        have hadj : (Matrix.toEuclideanLin H).adjoint = Matrix.toEuclideanLin H := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH_psd.isHermitian.eq]
        rw [← LinearMap.adjoint_inner_right, hadj]
        have hH2 : Matrix.toEuclideanLin H (Matrix.toEuclideanLin H vK) ∈ V := ⟨_, rfl⟩
        exact Submodule.inner_left_of_mem_orthogonal hH2 hvK_orth
      exact congrArg WithLp.ofLp (inner_self_eq_zero.mp h2)
    have hvK_kerPk : Pk.mulVec vK.ofLp = 0 := hker_sub vK.ofLp hvK_kerH
    have hquad : star x ⬝ᵥ (Pk - (δ : ℂ) • H).mulVec x =
        star vV.ofLp ⬝ᵥ (Pk - (δ : ℂ) • H).mulVec vV.ofLp := by
      have hx_eq : x = vV.ofLp + vK.ofLp := by
        change xE.ofLp = vV.ofLp + (xE - vV).ofLp; simp
      have hMvK : (Pk - (δ : ℂ) • H).mulVec vK.ofLp = 0 := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hvK_kerPk, hvK_kerH, smul_zero, sub_zero]
      have hMvK_left : star vK.ofLp ⬝ᵥ (Pk - (δ : ℂ) • H).mulVec vV.ofLp = 0 := by
        have hlin := LinearMap.adjoint_inner_right (Matrix.toEuclideanLin (Pk - (δ : ℂ) • H)) vK vV
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hHerm.eq] at hlin
        simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply,
          Matrix.toEuclideanLin] at hlin
        have hsym : star vK.ofLp ⬝ᵥ (Pk - (δ : ℂ) • H).mulVec vV.ofLp =
            star ((Pk - (δ : ℂ) • H).mulVec vK.ofLp) ⬝ᵥ vV.ofLp := by
          rw [dotProduct_comm (star vK.ofLp), dotProduct_comm (star ((Pk - (δ : ℂ) • H) *ᵥ vK.ofLp))]
          exact hlin
        rw [hsym, hMvK, star_zero, zero_dotProduct]
      rw [hx_eq, Matrix.mulVec_add, hMvK, add_zero, star_add, add_dotProduct, hMvK_left, add_zero]
    rw [hquad]
    have him : (star vV.ofLp ⬝ᵥ (Pk - (δ : ℂ) • H).mulVec vV.ofLp).im = 0 :=
      isHermitian_im_dotProduct_mulVec_self hHerm vV.ofLp
    rw [Complex.nonneg_iff]
    refine ⟨?_, him.symm⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hsimp : (star vV.ofLp ⬝ᵥ Pk.mulVec vV.ofLp).re -
        (δ * (star vV.ofLp ⬝ᵥ H.mulVec vV.ofLp).re - 0 * (star vV.ofLp ⬝ᵥ H.mulVec vV.ofLp).im) =
        f vV - δ * g vV := by ring
    rw [hsimp]
    by_cases hvV0 : vV = 0
    · simp [hvV0, f, g]
    · let u : EuclideanSpace ℂ (Fin n) := ((‖vV‖⁻¹ : ℝ) : ℂ) • vV
      have hu_mem : u ∈ SV := ⟨V.smul_mem _ (Submodule.starProjection_apply_mem V xE), by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hvV0)]⟩
      have hf_scale : f vV = ‖vV‖ ^ 2 * f u := by
        have : vV = ((‖vV‖ : ℝ) : ℂ) • u := by
          simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvV0),
            Complex.ofReal_one, one_smul]
        conv_lhs => rw [this]
        simp only [f, WithLp.ofLp_smul, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
        have : ((‖vV‖ : ℂ) * ((‖vV‖ : ℂ) * (star u.ofLp ⬝ᵥ Pk.mulVec u.ofLp))).re =
            ‖vV‖ ^ 2 * (star u.ofLp ⬝ᵥ Pk.mulVec u.ofLp).re := by
          rw [← mul_assoc, ← Complex.ofReal_mul, ← sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        exact this
      have hg_scale : g vV = ‖vV‖ ^ 2 * g u := by
        have : vV = ((‖vV‖ : ℝ) : ℂ) • u := by
          simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvV0),
            Complex.ofReal_one, one_smul]
        conv_lhs => rw [this]
        simp only [g, WithLp.ofLp_smul, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
          smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
        have : ((‖vV‖ : ℂ) * ((‖vV‖ : ℂ) * (star u.ofLp ⬝ᵥ H.mulVec u.ofLp))).re =
            ‖vV‖ ^ 2 * (star u.ofLp ⬝ᵥ H.mulVec u.ofLp).re := by
          rw [← mul_assoc, ← Complex.ofReal_mul, ← sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
          ring
        exact this
      have hfu : f vMin ≤ f u := hvMin_le hu_mem
      have hgu : g u ≤ g vMax := hvMax_ge hu_mem
      have hgu_nn : 0 ≤ g u := hH_psd.re_dotProduct_nonneg u.ofLp
      have hδ_le : δ ≤ f vMin / g vMax := min_le_right _ _
      have h1 : δ * g u ≤ f u := by
        calc δ * g u ≤ (f vMin / g vMax) * g vMax := mul_le_mul hδ_le hgu hgu_nn (by positivity)
          _ = f vMin := div_mul_cancel₀ _ hg_pos.ne'
          _ ≤ f u := hfu
      rw [hf_scale, hg_scale]
      nlinarith [sq_nonneg ‖vV‖]
  -- Step 2: 5-line scaling proof! Replace A_k = Uk * Pk by Uk * (Pk - t • H) for 0 < t ≤ δ!
  obtain ⟨δ, hδ_pos, hδ_lt1, hPk_sub⟩ := hdelta
  obtain ⟨Uk, hUk⟩ := exists_polar_unitary (A k)
  have hp0 : 0 < p := by linarith
  have hH_norm_pos : 0 < schattenNorm p H := (schattenNorm_pos_iff hp0 H).mpr hH_ne
  have hS_pow_eq : schattenPow p S = C ^ p * schattenPow p H := by
    have h1 : schattenNorm p S = C * schattenNorm p H := by
      simp only [C, leeRatio]; exact (div_mul_cancel₀ _ hH_norm_pos.ne').symm
    have h2 : schattenPow p S = (schattenNorm p S) ^ p := by
      rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p S), one_div_mul_cancel hp0.ne', Real.rpow_one]
    have h3 : schattenPow p H = (schattenNorm p H) ^ p := by
      rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p H), one_div_mul_cancel hp0.ne', Real.rpow_one]
    rw [h2, h1, Real.mul_rpow (by linarith : 0 ≤ C) (schattenNorm_nonneg p H), h3]
  have hS_pow_pos : 0 < schattenPow p S := by
    rw [hS_pow_eq]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) p) ((schattenPow_pos_iff hp0 H).mpr hH_ne)
  -- For every t ∈ (0, δ], (1 - (1 - t)^p) / (p * t) * ‖S‖_p^p ≤ Re Tr(G_Sᴴ (Uk * H))!
  have hbound_t : ∀ t : ℝ, 0 < t → t ≤ δ →
      ((1 - (1 - t) ^ p) / (p * t)) * schattenPow p S ≤
        ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re := by
    intro t ht_pos ht_le
    have ht_lt1 : t < 1 := lt_of_le_of_lt ht_le hδ_lt1
    have hPkt_psd : (Pk - (t : ℂ) • H).PosSemidef := by
      have hdecomp : Pk - (t : ℂ) • H = (t / δ : ℝ) • (Pk - (δ : ℂ) • H) + (1 - t / δ : ℝ) • Pk := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          Complex.real_smul]
        have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ_pos.ne'
        push_cast; field_simp [hδ0]; ring
      rw [hdecomp]
      exact (hPk_sub.smul (by positivity : (0 : ℝ) ≤ t / δ)).add
        ((matAbs_posSemidef (A k)).smul (by
          have : t / δ ≤ 1 := (div_le_one hδ_pos).mpr ht_le
          linarith : (0 : ℝ) ≤ 1 - t / δ))
    let B : Fin m → Mat n := Function.update A k ((Uk : Mat n) * (Pk - (t : ℂ) • H))
    have hHB : ∑ j, matAbs (B j) = ((1 - t : ℝ) : ℂ) • H := by
      have h1 : ∀ j, matAbs (B j) = Function.update (fun i => matAbs (A i)) k (Pk - (t : ℂ) • H) j := by
        intro j
        by_cases hjk : j = k
        · subst hjk
          simp only [B, Function.update_self, matAbs_unitary_mul]
          exact matAbs_of_posSemidef hPkt_psd
        · simp [B, Function.update_of_ne hjk]
      simp_rw [h1]
      rw [Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
      have hsum_er : ∑ j ∈ Finset.univ.erase k, matAbs (A j) = H - Pk := by
        have := Finset.add_sum_erase Finset.univ (fun j => matAbs (A j)) (Finset.mem_univ k)
        change _ = (∑ j, matAbs (A j)) - matAbs (A k)
        rw [← this]; abel
      rw [hsum_er]
      ext i j; simp; ring
    have hHB_ne : ∑ j, matAbs (B j) ≠ 0 := by
      rw [hHB]
      intro h0
      have h1 : ((1 - t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
      exact hH_ne ((smul_eq_zero.mp h0).resolve_left h1)
    have hSB : ∑ j, B j = S - (t : ℂ) • ((Uk : Mat n) * H) := by
      have h1 := Finset.sum_update_of_mem (Finset.mem_univ k) A ((Uk : Mat n) * (Pk - (t : ℂ) • H))
      change ∑ j, Function.update A k _ j = _
      rw [h1, Finset.sdiff_singleton_eq_erase]
      have hsum_er : ∑ j ∈ Finset.univ.erase k, A j = S - A k := by
        have := Finset.add_sum_erase Finset.univ A (Finset.mem_univ k)
        change A k + _ = S at this
        rw [← this]; abel
      rw [hsum_er, hUk, Matrix.mul_sub, Matrix.mul_smul]
      abel
    have hopt := hmax B hHB_ne
    have hSB_pow_le : schattenPow p (∑ j, B j) ≤ (1 - t) ^ p * schattenPow p S := by
      have hHB_norm_pos : 0 < schattenNorm p (∑ j, matAbs (B j)) := (schattenNorm_pos_iff hp0 _).mpr hHB_ne
      have hnorm_le : schattenNorm p (∑ j, B j) ≤ C * schattenNorm p (∑ j, matAbs (B j)) := by
        have := (div_le_iff₀ hHB_norm_pos).mp hopt; exact this
      have hpow_le : schattenPow p (∑ j, B j) ≤ C ^ p * schattenPow p (∑ j, matAbs (B j)) := by
        have hL : schattenPow p (∑ j, B j) = (schattenNorm p (∑ j, B j)) ^ p := by
          rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p _), one_div_mul_cancel hp0.ne', Real.rpow_one]
        have hR : schattenPow p (∑ j, matAbs (B j)) = (schattenNorm p (∑ j, matAbs (B j))) ^ p := by
          rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p _), one_div_mul_cancel hp0.ne', Real.rpow_one]
        rw [hL, hR, ← Real.mul_rpow (by linarith : 0 ≤ C) (schattenNorm_nonneg p _)]
        exact Real.rpow_le_rpow (schattenNorm_nonneg p _) hnorm_le hp0.le
      rw [hHB, schattenPow_smul hp0, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at hpow_le
      rw [hS_pow_eq]; linarith
    have hprop0 := prop0_subgradient_bound hp S (∑ j, B j)
    have hdiff_tr : ((dualOp p S)ᴴ * ((∑ j, B j) - S)).trace.re =
        -t * ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re := by
      have hsub : (∑ j, B j) - S = -((t : ℂ) • ((Uk : Mat n) * H)) := by rw [hSB]; abel
      rw [hsub, Matrix.mul_neg, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul,
        Complex.neg_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hdiff_tr] at hprop0
    have hineq : t * ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re ≥
        ((1 - (1 - t) ^ p) / p) * schattenPow p S := by
      have h1 : (1 / p) * schattenPow p S - t * ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re ≤
          (1 / p) * ((1 - t) ^ p * schattenPow p S) := by
        have := mul_le_mul_of_nonneg_left hSB_pow_le (one_div_pos.mpr hp0).le
        linarith
      have h2 : (1 / p) * schattenPow p S - (1 / p) * ((1 - t) ^ p * schattenPow p S) =
          ((1 - (1 - t) ^ p) / p) * schattenPow p S := by ring
      linarith
    have h3 := (div_le_iff₀ ht_pos).mpr (by linarith : ((1 - (1 - t) ^ p) / p) * schattenPow p S ≤
      ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re * t)
    have h3eq : ((1 - (1 - t) ^ p) / p * schattenPow p S) / t =
        (1 - (1 - t) ^ p) / (p * t) * schattenPow p S := by ring
    rwa [h3eq] at h3
  -- Step 3: Let t → 0⁺ via HasDerivAt!
  have hge_S : schattenPow p S ≤ ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re := by
    have hderiv : HasDerivAt (fun t : ℝ => (1 - t) ^ p) (-p) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub (1 : ℝ)
      have h2 := HasDerivAt.rpow_const h1 (p := p) (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
      simpa using h2
    have htend : Filter.Tendsto (fun t : ℝ => ((1 - (1 - t) ^ p) / (p * t)) * schattenPow p S)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 * schattenPow p S)) := by
      have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
      have hslope_right : Filter.Tendsto (fun t : ℝ => ((1 - t) ^ p - 1) / t)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (-p)) := by
        have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
          nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)
        have h : Filter.Tendsto (fun t : ℝ => slope (fun s => (1 - s) ^ p) 0 t)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (-p)) := hslope.mono_left hsub
        simpa [slope_def_field] using h
      have hdiv : Filter.Tendsto (fun t : ℝ => -(((1 - t) ^ p - 1) / t) / p)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(-p) / p)) :=
        (hslope_right.neg).div_const p
      have hnorm : -(-p) / p = 1 := by field_simp [hp0.ne']
      rw [hnorm] at hdiv
      have hmul := hdiv.mul_const (schattenPow p S)
      refine hmul.congr' (Filter.eventually_of_mem self_mem_nhdsWithin fun t (ht : 0 < t) => ?_)
      field_simp [hp0.ne', ht.ne']; ring
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ((1 - (1 - t) ^ p) / (p * t)) * schattenPow p S ≤
          ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re := by
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with t ht
      exact hbound_t t ht.1 ht.2.le
    simpa [one_mul] using le_of_tendsto htend hev
  -- Step 4: Apply Prop 0 to Y := C • (Uk * H) (which has schattenPow p Y = C^p ‖H‖_p^p = ‖S‖_p^p)!
  have hY_pow : schattenPow p ((C : ℂ) • ((Uk : Mat n) * H)) = schattenPow p S := by
    rw [schattenPow_smul hp0, Complex.norm_real, Real.norm_of_nonneg (by linarith),
      schattenPow_unitary_mul_left, hS_pow_eq]
  have hPropY := re_trace_dualOp_le hp S ((C : ℂ) • ((Uk : Mat n) * H))
  rw [hY_pow] at hPropY
  have hTrY : ((dualOp p S)ᴴ * ((C : ℂ) • ((Uk : Mat n) * H))).trace.re =
      C * ((dualOp p S)ᴴ * ((Uk : Mat n) * H)).trace.re := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hTrY] at hPropY
  have hsplit : ((p - 1) / p) * schattenPow p S + (1 / p) * schattenPow p S = schattenPow p S := by
    have hp_ne : p ≠ 0 := hp0.ne'
    field_simp [hp_ne]; ring
  rw [hsplit] at hPropY
  have hC_le1 : C * schattenPow p S ≤ schattenPow p S :=
    le_trans (mul_le_mul_of_nonneg_left hge_S (by linarith : 0 ≤ C)) hPropY
  have : C ≤ 1 := by nlinarith
  linarith

end MI20
