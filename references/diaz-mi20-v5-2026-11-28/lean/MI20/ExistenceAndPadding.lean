/-
  MI20/ExistenceAndPadding.lean
  =============================
  Author: Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Schatten triangle inequality, continuity, compactness, zero-padding monotonicity, and maximizer existence.
-/

import MI20.Prop0_And_Lemmas13
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.Elementwise
noncomputable section

namespace MI20

/-! ### Basic Schatten Norm Helpers -/

lemma schattenNorm_zero {n : ℕ} {p : ℝ} (hp : 0 < p) : schattenNorm p (0 : Mat n) = 0 := by
  rw [schattenNorm, schattenPow_zero hp, Real.zero_rpow (one_div_pos.mpr hp).ne']

lemma schattenNorm_smul {n : ℕ} {p : ℝ} (hp : 0 < p) (c : ℂ) (A : Mat n) :
    schattenNorm p (c • A) = ‖c‖ * schattenNorm p A := by
  simp only [schattenNorm, schattenPow_smul hp,
    Real.mul_rpow (Real.rpow_nonneg (norm_nonneg c) p) (schattenPow_nonneg p A),
    ← Real.rpow_mul (norm_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

lemma schattenPow_unitary_mul_conjTranspose_right {n : ℕ} {p : ℝ} (hp : 0 ≤ p)
    (A : Mat n) (V : Matrix.unitaryGroup (Fin n) ℂ) :
    schattenPow p (A * (V : Mat n)ᴴ) = schattenPow p A := by
  have h : (V : Mat n)ᴴ = ((star V : Matrix.unitaryGroup (Fin n) ℂ) : Mat n) := rfl
  rw [h, schattenPow_unitary_mul_right hp]

/-! ### Schatten Hölder, Triangle Inequality, PSD Monotonicity, and Continuity -/

/-- Schatten Hölder inequality from Proposition 0:
    Re Tr(G_Sᴴ X) ≤ ‖S‖_p^(p-1) * ‖X‖_p for all p > 1. -/
theorem re_trace_dualOp_le_mul {n : ℕ} {p : ℝ} (hp : 1 < p) (S X : Mat n) :
    ((dualOp p S)ᴴ * X).trace.re ≤ (schattenNorm p S) ^ (p - 1) * schattenNorm p X := by
  have hp0 : 0 < p := by linarith
  by_cases hS : S = 0
  · subst hS
    obtain ⟨U, V, σ, hσ_nn, _, hDual, hPow⟩ := exists_svd_dualOp p (0 : Mat n)
    have hσ0 : ∀ i, σ i = 0 := by
      intro i
      have hsum : ∑ j : Fin n, σ j ^ p = 0 := by rw [← hPow p hp0, schattenPow_zero hp0]
      have hle : σ i ^ p ≤ ∑ j : Fin n, σ j ^ p :=
        Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hσ_nn j) p) (Finset.mem_univ i)
      have h0 : σ i ^ p = 0 := le_antisymm (hsum ▸ hle) (Real.rpow_nonneg (hσ_nn i) p)
      exact (Real.rpow_eq_zero (hσ_nn i) hp0.ne').mp h0
    have hDual0 : dualOp p (0 : Mat n) = 0 := by
      rw [hDual]
      have hdiag0 : Matrix.diagonal (fun i => (((σ i) ^ (p - 1) : ℝ) : ℂ)) = 0 := by
        ext i j; by_cases hij : i = j
        · subst hij; simp [hσ0 i, Real.zero_rpow (by linarith : p - 1 ≠ 0)]
        · simp [Matrix.diagonal, hij]
      rw [hdiag0, Matrix.mul_zero, Matrix.zero_mul]
    rw [hDual0, Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
    exact mul_nonneg (Real.rpow_nonneg (schattenNorm_nonneg p _) _) (schattenNorm_nonneg p X)
  · by_cases hX : X = 0
    · subst hX
      rw [Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
      exact mul_nonneg (Real.rpow_nonneg (schattenNorm_nonneg p _) _) (schattenNorm_nonneg p _)
    · have hSn : 0 < schattenNorm p S := (schattenNorm_pos_iff hp0 S).mpr hS
      have hXn : 0 < schattenNorm p X := (schattenNorm_pos_iff hp0 X).mpr hX
      set t : ℝ := schattenNorm p S / schattenNorm p X
      have ht_pos : 0 < t := div_pos hSn hXn
      have hProp := re_trace_dualOp_le hp S ((t : ℂ) • X)
      have hTr : ((dualOp p S)ᴴ * ((t : ℂ) • X)).trace.re = t * ((dualOp p S)ᴴ * X).trace.re := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im]; ring
      have hPowX : schattenPow p ((t : ℂ) • X) = schattenPow p S := by
        rw [schattenPow_smul hp0, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
        have h1 : schattenPow p X = (schattenNorm p X) ^ p := by
          rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p X), one_div_mul_cancel hp0.ne', Real.rpow_one]
        have h2 : schattenPow p S = (schattenNorm p S) ^ p := by
          rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p S), one_div_mul_cancel hp0.ne', Real.rpow_one]
        rw [h1, h2, ← Real.mul_rpow ht_pos.le hXn.le, show t * schattenNorm p X = schattenNorm p S from
          div_mul_cancel₀ _ hXn.ne']
      rw [hTr, hPowX] at hProp
      have hsplit : (p - 1) / p * schattenPow p S + 1 / p * schattenPow p S = schattenPow p S := by
        have : (p - 1) / p + 1 / p = 1 := by field_simp [hp0.ne']; ring
        rw [← add_mul, this, one_mul]
      rw [hsplit] at hProp
      have hSpow : schattenPow p S = (schattenNorm p S) ^ p := by
        rw [schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p S), one_div_mul_cancel hp0.ne', Real.rpow_one]
      have hdiv : ((dualOp p S)ᴴ * X).trace.re ≤ schattenPow p S / t := (le_div_iff₀' ht_pos).mpr hProp
      refine hdiv.trans (le_of_eq ?_)
      rw [hSpow, show schattenNorm p S ^ p / t = (schattenNorm p S ^ p / schattenNorm p S) * schattenNorm p X by
        simp only [t]; field_simp [hSn.ne', hXn.ne']]
      congr 1
      rw [← Real.rpow_sub_one hSn.ne']

/-- Schatten p-norm triangle inequality for all p > 1. -/
theorem schattenNorm_add_le {n : ℕ} {p : ℝ} (hp : 1 < p) (X Y : Mat n) :
    schattenNorm p (X + Y) ≤ schattenNorm p X + schattenNorm p Y := by
  have hp0 : 0 < p := by linarith
  by_cases hXY : X + Y = 0
  · rw [hXY, schattenNorm_zero hp0]
    exact add_nonneg (schattenNorm_nonneg p X) (schattenNorm_nonneg p Y)
  · have hpos : 0 < schattenNorm p (X + Y) := (schattenNorm_pos_iff hp0 _).mpr hXY
    have hself := dualOp_trace_self hp (X + Y)
    have hadd : ((dualOp p (X + Y))ᴴ * (X + Y)).trace.re =
        ((dualOp p (X + Y))ᴴ * X).trace.re + ((dualOp p (X + Y))ᴴ * Y).trace.re := by
      rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hX := re_trace_dualOp_le_mul hp (X + Y) X
    have hY := re_trace_dualOp_le_mul hp (X + Y) Y
    have hpow : schattenPow p (X + Y) = (schattenNorm p (X + Y)) ^ (p - 1) * schattenNorm p (X + Y) := by
      rw [← Real.rpow_add_one hpos.ne', sub_add_cancel, schattenNorm,
        ← Real.rpow_mul (schattenPow_nonneg p _), one_div_mul_cancel hp0.ne', Real.rpow_one]
    have hpm1_pos : 0 < (schattenNorm p (X + Y)) ^ (p - 1) := Real.rpow_pos_of_pos hpos _
    have hineq : (schattenNorm p (X + Y)) ^ (p - 1) * schattenNorm p (X + Y) ≤
        (schattenNorm p (X + Y)) ^ (p - 1) * (schattenNorm p X + schattenNorm p Y) := by
      linarith
    exact le_of_mul_le_mul_left hineq hpm1_pos

/-- Triangle inequality for finite sums in Schatten p-norm. -/
theorem schattenNorm_sum_le {ι : Type*} {n : ℕ} {p : ℝ} (hp : 1 < p)
    (s : Finset ι) (f : ι → Mat n) :
    schattenNorm p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, schattenNorm p (f i) := by
  have hp0 : 0 < p := by linarith
  induction s using Finset.induction_on with
  | empty => simp [schattenNorm_zero hp0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have htri := schattenNorm_add_le hp (f a) (∑ i ∈ s, f i)
    linarith

/-- PSD trace nonnegativity: if A and B are positive semidefinite, Re Tr(A * B) ≥ 0. -/
lemma re_trace_mul_nonneg_of_posSemidef {n : ℕ} {A B : Mat n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  let S : Mat n := CFC.sqrt A
  have hS_sq : S * S = A := CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have hS_herm : S.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSBS : (S * B * Sᴴ).PosSemidef := hB.mul_mul_conjTranspose_same S
  have htr : (A * B).trace = (S * B * Sᴴ).trace := by
    rw [← hS_sq, Matrix.mul_assoc S S B, Matrix.trace_mul_comm S (S * B)]
    nth_rw 2 [← hS_herm.eq]
  rw [htr, Matrix.trace, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have hdiag : (S * B * Sᴴ).diag i = star (Pi.single i 1) ⬝ᵥ (S * B * Sᴴ).mulVec (Pi.single i 1) := by
    simp [Matrix.diag, Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hdiag]
  simpa [RCLike.re_to_complex] using hSBS.re_dotProduct_nonneg (Pi.single i 1)

/-- PSD monotonicity of Schatten p-power: 0 ⪯ X ⪯ Y implies ‖X‖_p^p ≤ ‖Y‖_p^p for p > 1. -/
theorem schattenPow_mono_of_posSemidef {n : ℕ} {p : ℝ} (hp : 1 < p) {X Y : Mat n}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : (Y - X).PosSemidef) :
    schattenPow p X ≤ schattenPow p Y := by
  have hp0 : 0 < p := by linarith
  let Ux := hX.isHermitian.eigenvectorUnitary
  let lam := hX.isHermitian.eigenvalues
  let Uy := hY.isHermitian.eigenvectorUnitary
  let mu := hY.isHermitian.eigenvalues
  have hlam_nn : ∀ i, 0 ≤ lam i := hX.eigenvalues_nonneg
  have hmu_nn : ∀ i, 0 ≤ mu i := hY.eigenvalues_nonneg
  have hX_eq : X = (Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ := by
    simpa [Ux, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hX.isHermitian.spectral_theorem
  have hY_eq : Y = (Uy : Mat n) * Matrix.diagonal (fun i => (mu i : ℂ)) * (Uy : Mat n)ᴴ := by
    simpa [Uy, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hY.isHermitian.spectral_theorem
  have hPowX : schattenPow p X = ∑ i : Fin n, (lam i) ^ p := by
    rw [hX_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hp0 lam hlam_nn]
  have hPowY : schattenPow p Y = ∑ i : Fin n, (mu i) ^ p := by
    rw [hY_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hp0 mu hmu_nn]
  let G : Mat n := (Ux : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ)) * (Ux : Mat n)ᴴ
  have hG_psd : G.PosSemidef := by
    have hd : (Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i
      exact_mod_cast Real.rpow_nonneg (hlam_nn i) (p - 1)
    simpa [G] using hd.mul_mul_conjTranspose_same (Ux : Mat n)
  have hTr_le : (G * X).trace.re ≤ (G * Y).trace.re := by
    have hnn := re_trace_mul_nonneg_of_posSemidef hG_psd hXY
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hnn
    linarith
  have hTrGX : (G * X).trace.re = ∑ i : Fin n, (lam i) ^ p := by
    have hprod : G * X = (Ux : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ p : ℝ) : ℂ)) * (Ux : Mat n)ᴴ := by
      simp only [G]
      conv_lhs => rw [hX_eq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Ux : Mat n)ᴴ (Ux : Mat n), unitary_conjTranspose_mul_self Ux,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, ← Complex.ofReal_mul]; congr 1
        by_cases h0 : lam i = 0
        · rw [h0, Real.zero_rpow (by linarith : p - 1 ≠ 0), zero_mul, Real.zero_rpow hp0.ne']
        · have hpos : 0 < lam i := lt_of_le_of_ne (hlam_nn i) (Ne.symm h0)
          rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
      · simp [Matrix.diagonal, hij]
    rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self Ux, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]
    simp
  let Qu : Matrix.unitaryGroup (Fin n) ℂ := star Ux * Uy
  let Q : Mat n := (Qu : Mat n)
  have hTrGY : (G * Y).trace.re = ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((lam i) ^ (p - 1) * mu j) := by
    have hQeq : (Ux : Mat n)ᴴ * (Uy : Mat n) = Q := rfl
    have hQHeq : (Uy : Mat n)ᴴ * (Ux : Mat n) = Qᴴ := by
      change (Uy : Mat n)ᴴ * (Ux : Mat n) = ((Ux : Mat n)ᴴ * (Uy : Mat n))ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    set DL : Mat n := Matrix.diagonal (fun i => (((lam i) ^ (p - 1) : ℝ) : ℂ))
    set DM : Mat n := Matrix.diagonal (fun j => (mu j : ℂ))
    have hprod : (G * Y).trace = ((DL * Q) * (DM * Qᴴ)).trace := by
      have hG_eq : G = (Ux : Mat n) * DL * (Ux : Mat n)ᴴ := rfl
      have hY_eq' : Y = (Uy : Mat n) * DM * (Uy : Mat n)ᴴ := hY_eq
      calc (G * Y).trace
          = ((Ux : Mat n) * (DL * ((Ux : Mat n)ᴴ * (Uy : Mat n)) * DM * (Uy : Mat n)ᴴ)).trace := by
              rw [hG_eq, hY_eq']; congr 1; simp only [Matrix.mul_assoc]
        _ = ((DL * Q * DM * (Uy : Mat n)ᴴ) * (Ux : Mat n)).trace := by
              rw [hQeq, Matrix.trace_mul_comm (Ux : Mat n)]
        _ = ((DL * Q) * (DM * ((Uy : Mat n)ᴴ * (Ux : Mat n)))).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DL * Q) * (DM * Qᴴ)).trace := by rw [hQHeq]
    rw [hprod, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, DL, DM, Matrix.diagonal_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Matrix.conjTranspose_apply]
    have hmul : ((((lam i) ^ (p - 1) : ℝ) : ℂ) * Q i j * (((mu j : ℝ) : ℂ) * star (Q i j))) =
        ((((lam i) ^ (p - 1) * mu j : ℝ) : ℂ) * (Q i j * star (Q i j))) := by push_cast; ring
    rw [hmul, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have hRowQ : ∀ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Qu) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ‖Q i j‖ ^ 2 = (Q i j * star (Q i j)).re
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColQ : ∀ j : Fin n, ∑ i : Fin n, ‖Q i j‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Qu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖Q i j‖ ^ 2 = (star (Q i j) * Q i j).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hYoung : ∀ i j : Fin n,
      (lam i) ^ (p - 1) * mu j ≤ ((p - 1) / p) * (lam i) ^ p + (1 / p) * (mu j) ^ p := by
    intro i j
    have hw1 : 0 ≤ (p - 1) / p := by positivity
    have hw2 : 0 ≤ 1 / p := by positivity
    have hsum : (p - 1) / p + 1 / p = 1 := by field_simp [hp0.ne']; ring
    have hY := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_nonneg (hlam_nn i) p) (Real.rpow_nonneg (hmu_nn j) p) hsum
    have hL1 : ((lam i) ^ p) ^ ((p - 1) / p) = (lam i) ^ (p - 1) := by
      rw [← Real.rpow_mul (hlam_nn i)]; congr 1; field_simp [hp0.ne']
    have hL2 : ((mu j) ^ p) ^ (1 / p) = mu j := by
      rw [← Real.rpow_mul (hmu_nn j)]
      rw [show p * (1 / p) = 1 by field_simp [hp0.ne'], Real.rpow_one]
    rwa [hL1, hL2] at hY
  have hUp : (G * Y).trace.re ≤ ((p - 1) / p) * ∑ i, (lam i) ^ p + (1 / p) * ∑ j, (mu j) ^ p := by
    rw [hTrGY]
    calc ∑ i, ∑ j, ‖Q i j‖ ^ 2 * ((lam i) ^ (p - 1) * mu j)
        ≤ ∑ i, ∑ j, ‖Q i j‖ ^ 2 * (((p - 1) / p) * (lam i) ^ p + (1 / p) * (mu j) ^ p) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hYoung i j) (sq_nonneg _)
      _ = (∑ i, ∑ j, ‖Q i j‖ ^ 2 * (((p - 1) / p) * (lam i) ^ p)) +
          (∑ i, ∑ j, ‖Q i j‖ ^ 2 * ((1 / p) * (mu j) ^ p)) := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = ((p - 1) / p) * ∑ i, (lam i) ^ p + (1 / p) * ∑ j, (mu j) ^ p := by
          congr 1
          · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.sum_mul, hRowQ i, one_mul]
          · rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.sum_mul, hColQ j, one_mul]
  rw [hPowX, hPowY]
  have hcomb : ∑ i, (lam i) ^ p ≤ ((p - 1) / p) * ∑ i, (lam i) ^ p + (1 / p) * ∑ j, (mu j) ^ p := by
    linarith
  have hdiff : (1 / p) * ∑ i, (lam i) ^ p ≤ (1 / p) * ∑ j, (mu j) ^ p := by
    have hsp : (p - 1) / p + 1 / p = 1 := by field_simp [hp0.ne']; ring
    have : ((p - 1) / p) * ∑ i, (lam i) ^ p + (1 / p) * ∑ i, (lam i) ^ p = ∑ i, (lam i) ^ p := by
      rw [← add_mul, hsp, one_mul]
    linarith
  exact le_of_mul_le_mul_left hdiff (one_div_pos.mpr hp0)

/-- Universal upper bound leeRatio p A ≤ m for all p > 1. -/
theorem leeRatio_le_card {m n : ℕ} {p : ℝ} (hp : 1 < p) (A : Fin m → Mat n) :
    leeRatio p A ≤ (m : ℝ) := by
  have hp0 : 0 < p := by linarith
  set H : Mat n := ∑ k, matAbs (A k)
  by_cases hH : H = 0
  · simp [leeRatio, H, hH, schattenNorm_zero hp0]
  · have hH_pos : 0 < schattenNorm p H := (schattenNorm_pos_iff hp0 H).mpr hH
    have hH_psd : H.PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    have hterm : ∀ k : Fin m, schattenNorm p (A k) ≤ schattenNorm p H := by
      intro k
      have hdiff : (H - matAbs (A k)).PosSemidef := by
        have heq : H - matAbs (A k) = ∑ j ∈ Finset.univ.erase k, matAbs (A j) := by
          have := Finset.add_sum_erase Finset.univ (fun j => matAbs (A j)) (Finset.mem_univ k)
          change (∑ j, matAbs (A j)) - matAbs (A k) = _; rw [← this]; abel
        rw [heq]
        have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
          intro s; induction s using Finset.induction_on with
          | empty => simpa using Matrix.PosSemidef.zero
          | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
        exact this _
      have hpow : schattenPow p (A k) ≤ schattenPow p H := by
        rw [← schattenPow_matAbs]
        exact schattenPow_mono_of_posSemidef hp (matAbs_posSemidef (A k)) hH_psd hdiff
      exact Real.rpow_le_rpow (schattenPow_nonneg p _) hpow (one_div_pos.mpr hp0).le
    have hnum : schattenNorm p (∑ k, A k) ≤ (m : ℝ) * schattenNorm p H := by
      calc schattenNorm p (∑ k, A k) ≤ ∑ k : Fin m, schattenNorm p (A k) := schattenNorm_sum_le hp _ _
        _ ≤ ∑ _k : Fin m, schattenNorm p H := Finset.sum_le_sum fun k _ => hterm k
        _ = (m : ℝ) * schattenNorm p H := by simp
    exact (div_le_iff₀ hH_pos).mpr hnum

/-- Frobenius squared norm equals Schatten 2-power: ∑ i j, ‖A i j‖^2 = schattenPow 2 A. -/
lemma sum_sq_norm_eq_schattenPow_two {n : ℕ} (A : Mat n) :
    ∑ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 = schattenPow 2 A := by
  obtain ⟨U, V, σ, hσ_nn, hSVD, hPow⟩ := exists_svd A
  rw [hPow 2 (by norm_num)]
  have htr : (Aᴴ * A).trace.re = ∑ i : Fin n, σ i ^ (2 : ℝ) := by
    have hprod : Aᴴ * A = (V : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ 2 : ℝ) : ℂ)) * (V : Mat n)ᴴ := by
      rw [hSVD]
      have hD : (Matrix.diagonal (fun i => (σ i : ℂ)))ᴴ = Matrix.diagonal (fun i => (σ i : ℂ)) := by
        ext i j; by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.diagonal, hij, Ne.symm hij]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul,
        ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp [sq]
      · simp [Matrix.diagonal, hij]
    rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self V, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Complex.ofReal_re, Real.rpow_two]
  rw [← htr, Matrix.trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Continuity of schattenNorm p on Mat n (via Lipschitz bound against sup norm). -/
theorem continuous_schattenNorm {n : ℕ} {p : ℝ} (hp : 1 < p) :
    Continuous (schattenNorm p : Mat n → ℝ) := by
  have hp0 : 0 < p := by linarith
  have hbound : ∀ Z : Mat n, schattenNorm p Z ≤ ((n : ℝ) ^ (1 / p) * (n : ℝ)) * ‖Z‖ := by
    intro Z
    obtain ⟨U, V, σ, hσ_nn, _, hPow⟩ := exists_svd Z
    have hfrob : ∑ i : Fin n, σ i ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ‖Z i j‖ ^ 2 := by
      rw [sum_sq_norm_eq_schattenPow_two, hPow 2 (by norm_num)]
      simp
    have hfrob_le : ∑ i : Fin n, σ i ^ 2 ≤ ((n : ℝ) * ‖Z‖) ^ 2 := by
      rw [hfrob]
      have hentry : ∀ i j : Fin n, ‖Z i j‖ ≤ ‖Z‖ := fun i j =>
        (norm_le_pi_norm (Z i) j).trans (norm_le_pi_norm Z i)
      calc ∑ i : Fin n, ∑ j : Fin n, ‖Z i j‖ ^ 2
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖Z‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
        _ = (n : ℝ) * ((n : ℝ) * ‖Z‖ ^ 2) := by simp
        _ = ((n : ℝ) * ‖Z‖) ^ 2 := by ring
    have hσ_le : ∀ i : Fin n, σ i ≤ (n : ℝ) * ‖Z‖ := by
      intro i
      have hsq : σ i ^ 2 ≤ ((n : ℝ) * ‖Z‖) ^ 2 :=
        (Finset.single_le_sum (fun j _ => sq_nonneg (σ j)) (Finset.mem_univ i)).trans hfrob_le
      nlinarith [hσ_nn i, mul_nonneg (Nat.cast_nonneg n) (norm_nonneg Z)]
    have hpow_le : schattenPow p Z ≤ (n : ℝ) * ((n : ℝ) * ‖Z‖) ^ p := by
      rw [hPow p hp0]
      calc ∑ i : Fin n, σ i ^ p
          ≤ ∑ _i : Fin n, ((n : ℝ) * ‖Z‖) ^ p :=
            Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (hσ_nn i) (hσ_le i) hp0.le
        _ = (n : ℝ) * ((n : ℝ) * ‖Z‖) ^ p := by simp
    have hnn : 0 ≤ (n : ℝ) * ‖Z‖ := mul_nonneg (Nat.cast_nonneg n) (norm_nonneg Z)
    calc schattenNorm p Z = (schattenPow p Z) ^ (1 / p) := rfl
      _ ≤ ((n : ℝ) * ((n : ℝ) * ‖Z‖) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (schattenPow_nonneg p Z) hpow_le (one_div_pos.mpr hp0).le
      _ = (n : ℝ) ^ (1 / p) * (((n : ℝ) * ‖Z‖) ^ p) ^ (1 / p) :=
          Real.mul_rpow (Nat.cast_nonneg n) (Real.rpow_nonneg hnn p)
      _ = ((n : ℝ) ^ (1 / p) * (n : ℝ)) * ‖Z‖ := by
          rw [← Real.rpow_mul hnn, mul_one_div_cancel hp0.ne', Real.rpow_one]; ring
  refine Metric.continuous_iff.mpr fun A ε hε => ?_
  set C : ℝ := (n : ℝ) ^ (1 / p) * (n : ℝ) + 1
  have hC_pos : 0 < C := by positivity
  refine ⟨ε / C, div_pos hε hC_pos, fun B hB => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have hdiff1 : schattenNorm p B - schattenNorm p A ≤ schattenNorm p (B - A) := by
    have := schattenNorm_add_le hp (B - A) A; simpa [sub_add_cancel] using this
  have hdiff2 : schattenNorm p A - schattenNorm p B ≤ schattenNorm p (A - B) := by
    have := schattenNorm_add_le hp (A - B) B; simpa [sub_add_cancel] using this
  have h1 : schattenNorm p (B - A) < ε := by
    have hle := hbound (B - A)
    have hlt : ‖B - A‖ < ε / C := by simpa [dist_eq_norm] using hB
    have hC1 : (n : ℝ) ^ (1 / p) * (n : ℝ) < C := by linarith
    have : ((n : ℝ) ^ (1 / p) * (n : ℝ)) * ‖B - A‖ ≤ C * ‖B - A‖ :=
      mul_le_mul_of_nonneg_right hC1.le (norm_nonneg _)
    have : C * ‖B - A‖ < C * (ε / C) := mul_lt_mul_of_pos_left hlt hC_pos
    rw [mul_div_cancel₀ _ hC_pos.ne'] at this
    linarith
  have h2 : schattenNorm p (A - B) < ε := by
    have hnorm : ‖A - B‖ = ‖B - A‖ := norm_sub_rev A B
    have hle := hbound (A - B)
    rw [hnorm] at hle
    have hlt : ‖B - A‖ < ε / C := by simpa [dist_eq_norm] using hB
    have hC1 : (n : ℝ) ^ (1 / p) * (n : ℝ) < C := by linarith
    have : ((n : ℝ) ^ (1 / p) * (n : ℝ)) * ‖B - A‖ ≤ C * ‖B - A‖ :=
      mul_le_mul_of_nonneg_right hC1.le (norm_nonneg _)
    have : C * ‖B - A‖ < C * (ε / C) := mul_lt_mul_of_pos_left hlt hC_pos
    rw [mul_div_cancel₀ _ hC_pos.ne'] at this
    linarith
  constructor <;> linarith

/-- Helper: elementwise matrix norm bound ‖M‖ ≤ r iff every entry has ‖M i j‖ ≤ r (for r ≥ 0). -/
lemma mat_norm_le_iff {n : ℕ} {M : Mat n} {r : ℝ} (hr : 0 ≤ r) :
    ‖M‖ ≤ r ↔ ∀ i j : Fin n, ‖M i j‖ ≤ r :=
  Matrix.norm_le_iff hr

/-- Continuity of matAbs on Mat n (via compactness of PSD square-root graph in finite dimensions). -/
theorem continuous_matAbs {n : ℕ} : Continuous (matAbs : Mat n → Mat n) := by
  have hnorm_matAbs : ∀ M : Mat n, ‖matAbs M‖ ≤ (n : ℝ) * ‖M‖ := by
    intro M
    have hsq : ∑ i : Fin n, ∑ j : Fin n, ‖matAbs M i j‖ ^ 2 = ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2 := by
      rw [sum_sq_norm_eq_schattenPow_two, sum_sq_norm_eq_schattenPow_two, schattenPow_matAbs]
    have hbound_sq : ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2 ≤ ((n : ℝ) * ‖M‖) ^ 2 := by
      have hentry : ∀ i j : Fin n, ‖M i j‖ ≤ ‖M‖ := fun i j =>
        (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
      calc ∑ i : Fin n, ∑ j : Fin n, ‖M i j‖ ^ 2
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, ‖M‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hentry i j) 2
        _ = ((n : ℝ) * ‖M‖) ^ 2 := by simp; ring
    rw [mat_norm_le_iff (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg M))]
    intro i j
    have hij_sq : ‖matAbs M i j‖ ^ 2 ≤ ((n : ℝ) * ‖M‖) ^ 2 := by
      have h1 : ‖matAbs M i j‖ ^ 2 ≤ ∑ b : Fin n, ‖matAbs M i b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖matAbs M i b‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ j)
      have h2 : ∑ b : Fin n, ‖matAbs M i b‖ ^ 2 ≤ ∑ a : Fin n, ∑ b : Fin n, ‖matAbs M a b‖ ^ 2 :=
        Finset.single_le_sum (f := fun a => ∑ b : Fin n, ‖matAbs M a b‖ ^ 2)
          (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i)
      linarith
    nlinarith [norm_nonneg (matAbs M i j), mul_nonneg (Nat.cast_nonneg n) (norm_nonneg M)]
  have hclosed_psd : IsClosed { P : Mat n | P.PosSemidef } := by
    have heq : { P : Mat n | P.PosSemidef } =
        (⋂ i : Fin n, ⋂ j : Fin n, { P : Mat n | star (P j i) = P i j }) ∩
        (⋂ x : Fin n → ℂ, { P : Mat n | 0 ≤ (star x ⬝ᵥ P.mulVec x).re }) := by
      ext P
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · intro hP
        refine ⟨fun i j => ?_, fun x => by simpa [RCLike.re_to_complex] using hP.re_dotProduct_nonneg x⟩
        have := congr_fun (congr_fun hP.isHermitian.eq i) j
        simpa [Matrix.conjTranspose_apply] using this
      · rintro ⟨hH, hre⟩
        have hHerm : P.IsHermitian := by
          ext i j; simpa [Matrix.conjTranspose_apply] using hH i j
        rw [Matrix.posSemidef_iff_dotProduct_mulVec]
        refine ⟨hHerm, fun x => ?_⟩
        rw [Complex.nonneg_iff]
        exact ⟨hre x, (isHermitian_im_dotProduct_mulVec_self hHerm x).symm⟩
    rw [heq]
    have hentry_cont : ∀ i j : Fin n, Continuous (fun P : Mat n => P i j) :=
      fun i j => (continuous_apply j).comp (continuous_apply i)
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j => ?_) (isClosed_iInter fun x => ?_)
    · exact isClosed_eq (Complex.continuous_conj.comp (hentry_cont j i)) (hentry_cont i j)
    · have hc : Continuous (fun P : Mat n => (star x ⬝ᵥ P.mulVec x).re) := by
        show Continuous (fun P : Mat n => (∑ i : Fin n, star (x i) * ∑ j : Fin n, P i j * x j).re)
        refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ =>
          Continuous.mul continuous_const (continuous_finsetSum _ fun j _ =>
            Continuous.mul (hentry_cont i j) continuous_const))
      exact isClosed_le continuous_const hc
  refine Metric.continuous_iff.mpr fun A ε hε => ?_
  by_contra hnc
  push Not at hnc
  have hex : ∀ k : ℕ, ∃ M : Mat n, dist M A < 1 / ((k : ℝ) + 1) ∧ ε ≤ dist (matAbs M) (matAbs A) :=
    fun k => hnc (1 / ((k : ℝ) + 1)) (by positivity)
  let u : ℕ → Mat n := fun k => (hex k).choose
  have hu_dist : ∀ k, dist (u k) A < 1 / ((k : ℝ) + 1) := fun k => (hex k).choose_spec.1
  have hu_far : ∀ k, ε ≤ dist (matAbs (u k)) (matAbs A) := fun k => (hex k).choose_spec.2
  have hu : Filter.Tendsto u Filter.atTop (nhds A) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, fun k hk => ?_⟩
    have hentry : dist (u k i j) (A i j) ≤ dist (u k) A := by
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : ‖(u k - A) i j‖ ≤ ‖u k - A‖ :=
        (norm_le_pi_norm ((u k - A) i) j).trans (norm_le_pi_norm (u k - A) i)
      simpa using h1
    refine hentry.trans_lt ((hu_dist k).trans ?_)
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hpos]
    have h1 : 1 / δ < (k : ℝ) + 1 := lt_of_lt_of_le hN (by exact_mod_cast (by omega : N ≤ k + 1))
    have h2 := (div_lt_iff₀ hδ).mp h1
    linarith
  have hu_bound : ∀ k, ‖u k‖ ≤ ‖A‖ + 1 := by
    intro k
    have h1 : ‖u k - A‖ < 1 := by
      have hd := hu_dist k
      rw [dist_eq_norm] at hd
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      linarith
    have htri : ‖u k‖ ≤ ‖u k - A‖ + ‖A‖ := by simpa [sub_add_cancel] using norm_add_le (u k - A) A
    linarith
  have hmem : ∀ k, matAbs (u k) ∈ Metric.closedBall (0 : Mat n) ((n : ℝ) * (‖A‖ + 1)) := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hnorm_matAbs (u k)).trans (mul_le_mul_of_nonneg_left (hu_bound k) (Nat.cast_nonneg n))
  have hcomp : IsCompact (Metric.closedBall (0 : Mat n) ((n : ℝ) * (‖A‖ + 1))) := isCompact_closedBall _ _
  have : FirstCountableTopology (Mat n) := inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  obtain ⟨P, _, ψ, hψ_strict, hψ_tend⟩ := hcomp.tendsto_subseq hmem
  have hP_psd : P.PosSemidef := hclosed_psd.mem_of_tendsto hψ_tend (Filter.Eventually.of_forall fun _ => matAbs_posSemidef _)
  have hP_sq : P * P = Aᴴ * A := by
    have hL : Filter.Tendsto (fun k => matAbs (u (ψ k)) * matAbs (u (ψ k))) Filter.atTop (nhds (P * P)) :=
      hψ_tend.mul hψ_tend
    have hA_sub : Filter.Tendsto (fun k => u (ψ k)) Filter.atTop (nhds A) :=
      hu.comp hψ_strict.tendsto_atTop
    have hconj_cont : Continuous (fun M : Mat n => Mᴴ) :=
      continuous_pi fun i => continuous_pi fun j =>
        Complex.continuous_conj.comp ((continuous_apply i).comp (continuous_apply j))
    have hR : Filter.Tendsto (fun k => (u (ψ k))ᴴ * u (ψ k)) Filter.atTop (nhds (Aᴴ * A)) :=
      (hconj_cont.tendsto A |>.comp hA_sub).mul hA_sub
    have heq : (fun k => matAbs (u (ψ k)) * matAbs (u (ψ k))) =
        (fun k => (u (ψ k))ᴴ * u (ψ k)) := funext fun k => matAbs_mul_self _
    rw [heq] at hL
    have : T2Space (Mat n) := inferInstanceAs (T2Space (Fin n → Fin n → ℂ))
    exact tendsto_nhds_unique hL hR
  have hP_eq : P = matAbs A := by
    have h1 : matAbs P = P := matAbs_of_posSemidef hP_psd
    have h2 : Pᴴ * P = Aᴴ * A := by rw [hP_psd.isHermitian.eq, hP_sq]
    rw [← h1]
    exact congrArg CFC.sqrt h2
  rw [hP_eq] at hψ_tend
  have hlim0 : Filter.Tendsto (fun k => dist (matAbs (u (ψ k))) (matAbs A)) Filter.atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hψ_tend
  have hge : ε ≤ 0 := ge_of_tendsto' hlim0 (fun k => hu_far (ψ k))
  linarith

/-! ### Zero-Padding Embedding Mat n → Mat (n + 1) -/

/-- Zero-pad an n × n matrix into the top-left corner of an (n + 1) × (n + 1) matrix. -/
def padZero {n : ℕ} (A : Mat n) : Mat (n + 1) :=
  Matrix.of fun i j =>
    if hi : i.val < n then
      if hj : j.val < n then A ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
    else 0

lemma padZero_add {n : ℕ} (A B : Mat n) : padZero (A + B) = padZero A + padZero B := by
  ext i j; simp only [padZero, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

lemma padZero_zero {n : ℕ} : padZero (0 : Mat n) = 0 := by
  ext i j; simp [padZero]

lemma padZero_sum {ι : Type*} {n : ℕ} (s : Finset ι) (f : ι → Mat n) :
    ∑ k ∈ s, padZero (f k) = padZero (∑ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty => simp [padZero_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, padZero_add]

lemma padZero_conjTranspose {n : ℕ} (A : Mat n) : (padZero A)ᴴ = padZero Aᴴ := by
  ext i j; simp only [padZero, Matrix.conjTranspose_apply, Matrix.of_apply]
  split_ifs <;> simp

lemma padZero_mul {n : ℕ} (A B : Mat n) : padZero (A * B) = padZero A * padZero B := by
  ext i j
  simp only [padZero, Matrix.of_apply, Matrix.mul_apply]
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · simp only [hi, hj, ↓reduceDIte]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Fin.val_castSucc, k.isLt]
    · simp only [hi, hj, ↓reduceDIte]
      symm; refine Finset.sum_eq_zero fun k _ => ?_
      split_ifs <;> simp
  · simp only [hi, ↓reduceDIte]
    symm; refine Finset.sum_eq_zero fun k _ => ?_
    simp

lemma padZero_injective {n : ℕ} : Function.Injective (@padZero n) := by
  intro A B h
  ext i j
  have hij := congr_fun (congr_fun h i.castSucc) j.castSucc
  simpa [padZero, i.isLt, j.isLt] using hij

lemma padZero_posSemidef {n : ℕ} {A : Mat n} (hA : A.PosSemidef) : (padZero A).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨by rw [Matrix.IsHermitian, padZero_conjTranspose, hA.isHermitian.eq], fun x => ?_⟩
  let x' : Fin n → ℂ := fun i => x i.castSucc
  have hq : star x ⬝ᵥ (padZero A).mulVec x = star x' ⬝ᵥ A.mulVec x' := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, padZero, Matrix.of_apply]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, zero_mul, Finset.sum_const_zero,
      mul_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_castSucc]
    simp [Fin.val_castSucc, i.isLt, x']
  rw [hq]
  exact hA.dotProduct_mulVec_nonneg x'

lemma matAbs_padZero {n : ℕ} (A : Mat n) : matAbs (padZero A) = padZero (matAbs A) := by
  have hP : (padZero (matAbs A)).PosSemidef := padZero_posSemidef (matAbs_posSemidef A)
  have h1 : matAbs (padZero (matAbs A)) = padZero (matAbs A) := matAbs_of_posSemidef hP
  have h2 : (padZero A)ᴴ * padZero A = (padZero (matAbs A))ᴴ * padZero (matAbs A) := by
    rw [padZero_conjTranspose, padZero_conjTranspose, ← padZero_mul, ← padZero_mul,
      (matAbs_isHermitian A).eq, matAbs_mul_self]
  rw [← h1]
  exact congrArg CFC.sqrt h2

/-- Extend an n × n unitary U to an (n + 1) × (n + 1) unitary diag(U, 1). -/
def padUnitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) : Matrix.unitaryGroup (Fin (n + 1)) ℂ :=
  ⟨Matrix.of fun i j =>
      if hi : i.val < n then
        if hj : j.val < n then (U : Mat n) ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if i = j then 1 else 0, by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.of_apply, Matrix.one_apply]
    rw [Fin.sum_univ_castSucc]
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · have hni : Fin.last n ≠ i := fun h => by rw [← h] at hi; simp at hi
        have hnj : Fin.last n ≠ j := fun h => by rw [← h] at hj; simp at hj
        simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, hni, hnj, ↓reduceIte,
          star_zero, zero_mul, add_zero, Fin.val_castSucc, Fin.is_lt, hi, hj]
        have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self U) ⟨i.val, hi⟩) ⟨j.val, hj⟩
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.mk.injEq] at hU
        rw [hU]
        simp [Fin.ext_iff]
      · have hni : Fin.last n ≠ i := fun h => by rw [← h] at hi; simp at hi
        have hij : i ≠ j := fun h => by subst h; exact hj hi
        simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, hni, ↓reduceIte, star_zero,
          zero_mul, add_zero, Fin.val_castSucc, Fin.is_lt, hi, hj, mul_zero,
          Finset.sum_const_zero, hij]
    · by_cases hj : j.val < n
      · have hnj : Fin.last n ≠ j := fun h => by rw [← h] at hj; simp at hj
        have hij : i ≠ j := fun h => by subst h; exact hi hj
        simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, hnj, ↓reduceIte, mul_zero,
          add_zero, Fin.val_castSucc, Fin.is_lt, hi, hj, star_zero, zero_mul,
          Finset.sum_const_zero, hij]
      · have hi' : i = Fin.last n := Fin.ext (by have := i.isLt; simp [Fin.val_last]; omega)
        have hj' : j = Fin.last n := Fin.ext (by have := j.isLt; simp [Fin.val_last]; omega)
        subst hi'; subst hj'
        simp⟩

lemma padUnitary_mul_padZero {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (B : Mat n) :
    (padUnitary U : Mat (n + 1)) * padZero B = padZero ((U : Mat n) * B) := by
  ext i j
  simp only [padUnitary, padZero, Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, mul_zero, add_zero, Fin.val_castSucc, Fin.is_lt]
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · simp only [hi, hj, ↓reduceDIte]
    · simp [hi, hj]
  · have hne : ∀ x : Fin n, i ≠ x.castSucc := fun x h => hi (h ▸ x.isLt)
    simp [hi, hne]

lemma padZero_mul_padUnitary_conjTranspose {n : ℕ} (B : Mat n) (V : Matrix.unitaryGroup (Fin n) ℂ) :
    padZero B * (padUnitary V : Mat (n + 1))ᴴ = padZero (B * (V : Mat n)ᴴ) := by
  ext i j
  simp only [padUnitary, padZero, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, Fin.val_castSucc, Fin.is_lt]
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · simp [hi, hj]
    · have hne : ∀ x : Fin n, j ≠ x.castSucc := fun x h => hj (h ▸ x.isLt)
      simp [hi, hj, hne]
  · simp [hi]

lemma padZero_diagonal {n : ℕ} (d : Fin n → ℂ) :
    padZero (Matrix.diagonal d) = Matrix.diagonal (fun i : Fin (n + 1) => if hi : i.val < n then d ⟨i.val, hi⟩ else 0) := by
  ext i j
  simp only [padZero, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; by_cases hi : i.val < n <;> simp [hi]
  · have hval : ∀ (hi : i.val < n) (hj : j.val < n), (⟨i.val, hi⟩ : Fin n) ≠ ⟨j.val, hj⟩ :=
      fun hi hj h => hij (Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · simp [hi, hj, hij, hval hi hj]
      · simp [hi, hj, hij]
    · simp [hi, hij]

lemma schattenPow_padZero {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Mat n) :
    schattenPow p (padZero A) = schattenPow p A := by
  obtain ⟨U, V, σ, hσ_nn, hSVD, hPow⟩ := exists_svd A
  let σExt : Fin (n + 1) → ℝ := fun i => if hi : i.val < n then σ ⟨i.val, hi⟩ else 0
  have hσExt_nn : ∀ i, 0 ≤ σExt i := fun i => by dsimp [σExt]; split_ifs <;> [exact hσ_nn _; exact le_rfl]
  have hDiag : padZero (Matrix.diagonal (fun i => (σ i : ℂ))) = Matrix.diagonal (fun i => (σExt i : ℂ)) := by
    rw [padZero_diagonal]; congr 1; ext i; dsimp [σExt]; split_ifs <;> simp
  have hEq : padZero A = (padUnitary U : Mat (n + 1)) * Matrix.diagonal (fun i => (σExt i : ℂ)) *
      (padUnitary V : Mat (n + 1))ᴴ := by
    rw [hSVD, ← padZero_mul_padUnitary_conjTranspose, ← padUnitary_mul_padZero, hDiag]
  rw [hEq, schattenPow_unitary_mul_conjTranspose_right hp.le, schattenPow_unitary_mul_left,
    schattenPow_diagonal hp σExt hσExt_nn, hPow p hp, Fin.sum_univ_castSucc]
  simp [σExt, Real.zero_rpow hp.ne']

lemma schattenNorm_padZero {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Mat n) :
    schattenNorm p (padZero A) = schattenNorm p A := by
  simp only [schattenNorm, schattenPow_padZero hp]

lemma leeRatio_padZero {m n : ℕ} {p : ℝ} (hp : 0 < p) (A : Fin m → Mat n) :
    leeRatio p (fun k => padZero (A k)) = leeRatio p A := by
  simp only [leeRatio, padZero_sum, matAbs_padZero, schattenNorm_padZero hp]

lemma leeConst_mono {m n : ℕ} {p : ℝ} (hp : 1 < p) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    leeConst p m n ≤ leeConst p m (n + 1) := by
  have hp0 : 0 < p := by linarith
  have hne : { r : ℝ | ∃ A : Fin m → Mat n, (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A }.Nonempty := by
    let A0 : Fin m → Mat n := fun _ => (1 : Mat n)
    refine ⟨leeRatio p A0, A0, ?_, rfl⟩
    have h1 : ∀ k : Fin m, matAbs (A0 k) = (1 : Mat n) := fun _ =>
      matAbs_of_posSemidef Matrix.PosSemidef.one
    simp_rw [h1]
    intro h0
    have h00 := congr_fun (congr_fun h0 ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [Matrix.sum_apply, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Matrix.zero_apply, Nat.cast_eq_zero] at h00
    omega
  have hbdd : BddAbove { r : ℝ | ∃ A : Fin m → Mat (n + 1), (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A } :=
    ⟨(m : ℝ), by rintro r ⟨A, _, rfl⟩; exact leeRatio_le_card hp A⟩
  refine csSup_le hne ?_
  rintro r ⟨A, hA_ne, rfl⟩
  refine le_csSup hbdd ⟨fun k => padZero (A k), ?_, (leeRatio_padZero hp0 A).symm⟩
  intro h0
  apply hA_ne
  apply padZero_injective
  have hsum : ∑ k, matAbs (padZero (A k)) = padZero (∑ k, matAbs (A k)) := by
    simp_rw [matAbs_padZero]; exact padZero_sum _ _
  rw [← hsum, h0, padZero_zero]

/-! ### Existence of a Finite-Dimensional Maximizer (Compactness on Unit Schatten Sphere) -/

lemma matAbs_smul_real_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (A : Mat n) :
    matAbs ((c : ℂ) • A) = (c : ℂ) • matAbs A := by
  have hP : ((c : ℂ) • matAbs A).PosSemidef := by
    have : (c : ℂ) • matAbs A = c • matAbs A := by ext i j; simp [Complex.real_smul]
    rw [this]; exact (matAbs_posSemidef A).smul hc
  have h1 := matAbs_of_posSemidef hP
  have h2 : ((c : ℂ) • A)ᴴ * ((c : ℂ) • A) = ((c : ℂ) • matAbs A)ᴴ * ((c : ℂ) • matAbs A) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, (matAbs_isHermitian A).eq, matAbs_mul_self]
  rw [← h1]
  exact congrArg CFC.sqrt h2

lemma leeRatio_smul {m n : ℕ} {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) (A : Fin m → Mat n) :
    leeRatio p (fun k => (c : ℂ) • A k) = leeRatio p A := by
  have hsum : ∑ k, (c : ℂ) • A k = (c : ℂ) • ∑ k, A k := (Finset.smul_sum).symm
  have hH : ∑ k, matAbs ((c : ℂ) • A k) = (c : ℂ) • ∑ k, matAbs (A k) := by
    simp_rw [matAbs_smul_real_nonneg hc.le]; exact (Finset.smul_sum).symm
  simp only [leeRatio, hsum, hH, schattenNorm_smul hp, Complex.norm_real, Real.norm_of_nonneg hc.le]
  exact mul_div_mul_left _ _ hc.ne'

/-- Existence of an n-dimensional maximizer attaining leeConst p m n for all p > 1, m ≥ 1, n ≥ 1. -/
theorem exists_leeConst_maximizer {m n : ℕ} {p : ℝ} (hp : 1 < p) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ A : Fin m → Mat n, (∑ k, matAbs (A k)) ≠ 0 ∧
      leeRatio p A = leeConst p m n ∧
      ∀ B : Fin m → Mat n, (∑ k, matAbs (B k)) ≠ 0 → leeRatio p B ≤ leeRatio p A := by
  have hp0 : 0 < p := by linarith
  let K : Set (Fin m → Mat n) := { A | schattenNorm p (∑ k, matAbs (A k)) = 1 }
  have hK_closed : IsClosed K := by
    have hc : Continuous (fun A : Fin m → Mat n => schattenNorm p (∑ k, matAbs (A k))) :=
      (continuous_schattenNorm hp).comp (continuous_finsetSum _ fun k _ => continuous_matAbs.comp (continuous_apply k))
    exact isClosed_eq hc continuous_const
  have hK_bdd : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : Fin m → Mat n)]
    refine ⟨Real.sqrt (n : ℝ) + 1, fun A hA => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro k
    have hH_psd : (∑ j, matAbs (A j)).PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    have hdiff : ((∑ j, matAbs (A j)) - matAbs (A k)).PosSemidef := by
      have heq : (∑ j, matAbs (A j)) - matAbs (A k) = ∑ j ∈ Finset.univ.erase k, matAbs (A j) := by
        have := Finset.add_sum_erase Finset.univ (fun j => matAbs (A j)) (Finset.mem_univ k)
        rw [← this]; abel
      rw [heq]
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this _
    have hpow_le : schattenPow p (A k) ≤ 1 := by
      have h1 : schattenPow p (A k) ≤ schattenPow p (∑ j, matAbs (A j)) := by
        rw [← schattenPow_matAbs]
        exact schattenPow_mono_of_posSemidef hp (matAbs_posSemidef (A k)) hH_psd hdiff
      have h2 : schattenPow p (∑ j, matAbs (A j)) = 1 := by
        have hA1 : schattenNorm p (∑ j, matAbs (A j)) = 1 := hA
        rw [← Real.one_rpow p, ← hA1, schattenNorm, ← Real.rpow_mul (schattenPow_nonneg p _),
          one_div_mul_cancel hp0.ne', Real.rpow_one]
      linarith
    obtain ⟨U, V, σ, hσ_nn, _, hPow⟩ := exists_svd (A k)
    have hσ_le1 : ∀ i : Fin n, σ i ≤ 1 := by
      intro i
      have hle : σ i ^ p ≤ 1 := by
        have h1 : σ i ^ p ≤ ∑ j : Fin n, σ j ^ p :=
          Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hσ_nn j) p) (Finset.mem_univ i)
        rw [← hPow p hp0] at h1; linarith
      by_contra hgt; push Not at hgt
      have : (1 : ℝ) ^ p < σ i ^ p := Real.rpow_lt_rpow (by norm_num) hgt hp0
      rw [Real.one_rpow] at this; linarith
    have hfrob_le : ∑ a : Fin n, ∑ b : Fin n, ‖A k a b‖ ^ 2 ≤ (n : ℝ) := by
      rw [sum_sq_norm_eq_schattenPow_two, hPow 2 (by norm_num)]
      simp only [Real.rpow_two]
      calc ∑ i : Fin n, σ i ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hσ_nn i) (hσ_le1 i) 2
        _ = (n : ℝ) := by simp
    rw [mat_norm_le_iff (by positivity)]
    intro a b
    have hab_sq : ‖A k a b‖ ^ 2 ≤ (n : ℝ) := by
      have h1 : ‖A k a b‖ ^ 2 ≤ ∑ c : Fin n, ‖A k a c‖ ^ 2 :=
        Finset.single_le_sum (f := fun c => ‖A k a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
      have h2 : ∑ c : Fin n, ‖A k a c‖ ^ 2 ≤ ∑ r : Fin n, ∑ c : Fin n, ‖A k r c‖ ^ 2 :=
        Finset.single_le_sum (f := fun r => ∑ c : Fin n, ‖A k r c‖ ^ 2)
          (fun r _ => Finset.sum_nonneg fun c _ => sq_nonneg _) (Finset.mem_univ a)
      linarith
    have hab_le : ‖A k a b‖ ≤ Real.sqrt (n : ℝ) := by
      rw [← Real.sqrt_sq (norm_nonneg (A k a b))]
      exact Real.sqrt_le_sqrt hab_sq
    linarith
  have hK_compact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd
  have hK_ne : K.Nonempty := by
    let A0 : Fin m → Mat n := fun _ => (1 : Mat n)
    have hH0_ne : ∑ k, matAbs (A0 k) ≠ 0 := by
      have h1 : ∀ k : Fin m, matAbs (A0 k) = (1 : Mat n) := fun _ => matAbs_of_posSemidef Matrix.PosSemidef.one
      simp_rw [h1]
      intro h0
      have h00 := congr_fun (congr_fun h0 ⟨0, by omega⟩) ⟨0, by omega⟩
      simp only [Matrix.sum_apply, Matrix.one_apply_eq, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Matrix.zero_apply, Nat.cast_eq_zero] at h00
      omega
    have hc_pos : 0 < schattenNorm p (∑ k, matAbs (A0 k)) := (schattenNorm_pos_iff hp0 _).mpr hH0_ne
    let c : ℝ := (schattenNorm p (∑ k, matAbs (A0 k)))⁻¹
    have hc_nn : 0 ≤ c := inv_nonneg.mpr hc_pos.le
    refine ⟨fun k => (c : ℂ) • A0 k, ?_⟩
    show schattenNorm p (∑ k, matAbs ((c : ℂ) • A0 k)) = 1
    simp_rw [matAbs_smul_real_nonneg hc_nn]
    rw [← Finset.smul_sum, schattenNorm_smul hp0, Complex.norm_real,
      Real.norm_of_nonneg hc_nn, inv_mul_cancel₀ hc_pos.ne']
  have hobj_cont : Continuous (fun A : Fin m → Mat n => schattenNorm p (∑ k, A k)) :=
    (continuous_schattenNorm hp).comp (continuous_finsetSum _ fun k _ => continuous_apply k)
  obtain ⟨Astar, hAstar_mem, hAstar_max⟩ := hK_compact.exists_isMaxOn hK_ne hobj_cont.continuousOn
  have hHstar_ne : ∑ k, matAbs (Astar k) ≠ 0 := by
    intro h0
    have h1 : schattenNorm p (∑ k, matAbs (Astar k)) = 1 := hAstar_mem
    rw [h0, schattenNorm_zero hp0] at h1; norm_num at h1
  have hratio_star : leeRatio p Astar = schattenNorm p (∑ k, Astar k) := by
    have h1 : schattenNorm p (∑ k, matAbs (Astar k)) = 1 := hAstar_mem
    rw [leeRatio, h1, div_one]
  have hopt : ∀ B : Fin m → Mat n, (∑ k, matAbs (B k)) ≠ 0 → leeRatio p B ≤ leeRatio p Astar := by
    intro B hB_ne
    have hc_pos : 0 < schattenNorm p (∑ k, matAbs (B k)) := (schattenNorm_pos_iff hp0 _).mpr hB_ne
    let c : ℝ := (schattenNorm p (∑ k, matAbs (B k)))⁻¹
    have hc_nn : 0 ≤ c := inv_nonneg.mpr hc_pos.le
    let B' : Fin m → Mat n := fun k => (c : ℂ) • B k
    have hB'_mem : B' ∈ K := by
      show schattenNorm p (∑ k, matAbs ((c : ℂ) • B k)) = 1
      simp_rw [matAbs_smul_real_nonneg hc_nn]
      rw [← Finset.smul_sum, schattenNorm_smul hp0, Complex.norm_real,
        Real.norm_of_nonneg hc_nn, inv_mul_cancel₀ hc_pos.ne']
    have hle : schattenNorm p (∑ k, B' k) ≤ schattenNorm p (∑ k, Astar k) := hAstar_max hB'_mem
    have hB'_ratio : leeRatio p B' = schattenNorm p (∑ k, B' k) := by
      have h1 : schattenNorm p (∑ k, matAbs (B' k)) = 1 := hB'_mem
      rw [leeRatio, h1, div_one]
    rw [← leeRatio_smul hp0 (inv_pos.mpr hc_pos) B, hB'_ratio, hratio_star]
    exact hle
  refine ⟨Astar, hHstar_ne, ?_, hopt⟩
  apply le_antisymm
  · have hbdd : BddAbove { r : ℝ | ∃ A : Fin m → Mat n, (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A } :=
      ⟨(m : ℝ), by rintro r ⟨A, _, rfl⟩; exact leeRatio_le_card hp A⟩
    exact le_csSup hbdd ⟨Astar, hHstar_ne, rfl⟩
  · refine csSup_le ⟨leeRatio p Astar, Astar, hHstar_ne, rfl⟩ ?_
    rintro r ⟨B, hB_ne, rfl⟩
    exact hopt B hB_ne

/-! ### Base Cases: C_{p,m}(1) = 1 < C_{p,m}(2) for all p > 1, m ≥ 2 -/

lemma schattenNorm_fin_one {p : ℝ} (hp : 0 < p) (A : Mat 1) :
    schattenNorm p A = ‖A 0 0‖ := by
  by_cases h0 : A 0 0 = 0
  · have hA0 : A = 0 := by ext i j; fin_cases i; fin_cases j; exact h0
    conv_lhs => rw [hA0]
    rw [schattenNorm_zero hp, h0, norm_zero]
  · let u : ℂ := A 0 0 / (‖A 0 0‖ : ℂ)
    have hu_norm : ‖u‖ = 1 := by
      simp [u, Complex.norm_real, div_self (norm_ne_zero_iff.mpr h0)]
    let U : Matrix.unitaryGroup (Fin 1) ℂ :=
      ⟨Matrix.diagonal (fun _ => u), by
        rw [Matrix.mem_unitaryGroup_iff']
        ext i j; fin_cases i; fin_cases j
        have hi0 : (⟨0, Nat.zero_lt_one⟩ : Fin 1) = 0 := rfl
        simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
          Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, Matrix.one_apply_eq,
          hi0, Matrix.diagonal_apply_eq]
        rw [Complex.star_def, Complex.conj_mul', hu_norm]; norm_num⟩
    have hfac : A = (U : Mat 1) * Matrix.diagonal (fun _ => (‖A 0 0‖ : ℂ)) := by
      ext i j; fin_cases i; fin_cases j
      have hi0 : (⟨0, Nat.zero_lt_one⟩ : Fin 1) = 0 := rfl
      simp [U, u, hi0, Matrix.mul_apply,
        div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0))]
    conv_lhs => rw [hfac]
    rw [schattenNorm, schattenPow_unitary_mul_left,
      schattenPow_diagonal hp (fun _ => ‖A 0 0‖) (fun _ => norm_nonneg _)]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- Base case 1: C_{p,m}(1) = 1 for all p > 1 and m ≥ 1. -/
theorem leeConst_one_eq_one {m : ℕ} {p : ℝ} (hp : 1 < p) (hm : 1 ≤ m) :
    leeConst p m 1 = 1 := by
  have hp0 : 0 < p := by linarith
  have h1_mem : (1 : ℝ) ∈ { r : ℝ | ∃ A : Fin m → Mat 1, (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A } := by
    let A0 : Fin m → Mat 1 := fun _ => (1 : Mat 1)
    have hH : ∑ k, matAbs (A0 k) = (m : ℂ) • (1 : Mat 1) := by
      have h1 : ∀ k, matAbs (A0 k) = (1 : Mat 1) := fun _ => matAbs_of_posSemidef Matrix.PosSemidef.one
      simp_rw [h1]; ext i j; fin_cases i; fin_cases j; simp
    have hH_ne : ∑ k, matAbs (A0 k) ≠ 0 := by
      rw [hH]; intro h0
      have h00 := congr_fun (congr_fun h0 0) 0
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply,
        Nat.cast_eq_zero] at h00
      omega
    refine ⟨A0, hH_ne, ?_⟩
    have hS : ∑ k, A0 k = (m : ℂ) • (1 : Mat 1) := by
      ext i j; fin_cases i; fin_cases j; simp [A0]
    simp only [leeRatio, hS, hH]
    rw [div_self ((schattenNorm_pos_iff hp0 _).mpr (hH ▸ hH_ne)).ne']
  apply le_antisymm
  · refine csSup_le ⟨1, h1_mem⟩ ?_
    rintro r ⟨A, hH_ne, rfl⟩
    have habs : ∀ k, (matAbs (A k)) 0 0 = (‖A k 0 0‖ : ℂ) := by
      intro k
      let D : Mat 1 := Matrix.diagonal (fun _ : Fin 1 => (‖A k 0 0‖ : ℂ))
      have hD : D.PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]; intro _; exact_mod_cast norm_nonneg _
      have h1 : matAbs (A k) = D := by
        have hm1 := matAbs_of_posSemidef hD
        have hsq : (A k)ᴴ * A k = Dᴴ * D := by
          ext i j; fin_cases i; fin_cases j
          have hi0 : (⟨0, Nat.zero_lt_one⟩ : Fin 1) = 0 := rfl
          simp only [D, hi0, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.univ_unique,
            Fin.default_eq_zero, Finset.sum_singleton, Matrix.diagonal_apply_eq]
          rw [Complex.star_def, Complex.conj_mul', Complex.conj_ofReal, sq]
        rw [← hm1]; exact congrArg CFC.sqrt hsq
      rw [h1]; simp [D]
    have hH_pos : 0 < schattenNorm p (∑ k, matAbs (A k)) := (schattenNorm_pos_iff hp0 _).mpr hH_ne
    rw [leeRatio, div_le_one hH_pos, schattenNorm_fin_one hp0, schattenNorm_fin_one hp0]
    simp only [Matrix.sum_apply, habs, ← Complex.ofReal_sum, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
    exact norm_sum_le _ _
  · have hbdd : BddAbove { r : ℝ | ∃ A : Fin m → Mat 1, (∑ k, matAbs (A k)) ≠ 0 ∧ r = leeRatio p A } :=
      ⟨(m : ℝ), by rintro r ⟨A, _, rfl⟩; exact leeRatio_le_card hp A⟩
    exact le_csSup hbdd h1_mem

/-- Base case 2: 1 < C_{p,m}(2) for all p > 1 and m ≥ 2, via elementary rank-1 witness
    A_0 = [[1, t], [0, 0]], A_1 = [[1, -t], [0, 0]] with t = √x, x = min(1/2, (1/4)^(1/(p-1))). -/
theorem one_lt_leeConst_two {m : ℕ} {p : ℝ} (hp : 1 < p) (hm : 2 ≤ m) :
    1 < leeConst p m 2 := by
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  set x : ℝ := min (1 / 2) ((1 / 4 : ℝ) ^ (1 / (p - 1)))
  have hx_pos : 0 < x := lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have hx_le_half : x ≤ 1 / 2 := min_le_left _ _
  have hx_pow : x ^ (p - 1) ≤ 1 / 4 := by
    calc x ^ (p - 1) ≤ ((1 / 4 : ℝ) ^ (1 / (p - 1))) ^ (p - 1) :=
          Real.rpow_le_rpow hx_pos.le (min_le_right _ _) hpm1.le
      _ = 1 / 4 := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hpm1.ne', Real.rpow_one]
  set t : ℝ := Real.sqrt x
  have ht_pos : 0 < t := Real.sqrt_pos.mpr hx_pos
  have ht_sq : t ^ 2 = x := Real.sq_sqrt hx_pos.le
  set r : ℝ := Real.sqrt (1 + x)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr_sq : r ^ 2 = 1 + x := Real.sq_sqrt (by linarith)
  have ht2c : (t : ℂ) ^ 2 = (x : ℂ) := by exact_mod_cast ht_sq
  have hr2c : (r : ℂ) ^ 2 = 1 + (x : ℂ) := by exact_mod_cast hr_sq
  let A0 : Mat 2 := !![1, (t : ℂ); 0, 0]
  let A1 : Mat 2 := !![1, -(t : ℂ); 0, 0]
  let G0 : Mat 2 := A0ᴴ * A0
  let G1 : Mat 2 := A1ᴴ * A1
  let P0 : Mat 2 := ((r⁻¹ : ℝ) : ℂ) • G0
  let P1 : Mat 2 := ((r⁻¹ : ℝ) : ℂ) • G1
  have hG0_entries : G0 = !![1, (t : ℂ); (t : ℂ), (x : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [G0, A0, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, ← sq, ht2c]
  have hG1_entries : G1 = !![1, -(t : ℂ); -(t : ℂ), (x : ℂ)] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [G1, A1, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, ← sq, ht2c]
  have hG0_sq : G0 * G0 = ((1 + x : ℝ) : ℂ) • G0 := by
    rw [hG0_entries]
    ext i j; fin_cases i <;> fin_cases j <;> (
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [← ht2c]; ring)
  have hG1_sq : G1 * G1 = ((1 + x : ℝ) : ℂ) • G1 := by
    rw [hG1_entries]
    ext i j; fin_cases i <;> fin_cases j <;> (
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [← ht2c]; ring)
  have hP0_psd : P0.PosSemidef := by
    have : P0 = r⁻¹ • G0 := by ext i j; simp [P0, Complex.real_smul]
    rw [this]; exact (Matrix.posSemidef_conjTranspose_mul_self A0).smul (inv_nonneg.mpr hr_pos.le)
  have hP1_psd : P1.PosSemidef := by
    have : P1 = r⁻¹ • G1 := by ext i j; simp [P1, Complex.real_smul]
    rw [this]; exact (Matrix.posSemidef_conjTranspose_mul_self A1).smul (inv_nonneg.mpr hr_pos.le)
  have hinv_sq : ((r⁻¹ : ℝ) : ℂ) * (((r⁻¹ : ℝ) : ℂ) * ((1 + x : ℝ) : ℂ)) = 1 := by
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
    push_cast
    rw [← hr2c]; field_simp [hr0]
  have hP0_abs : matAbs A0 = P0 := by
    have h1 := matAbs_of_posSemidef hP0_psd
    have hsq : A0ᴴ * A0 = P0ᴴ * P0 := by
      rw [hP0_psd.isHermitian.eq]
      change G0 = (((r⁻¹ : ℝ) : ℂ) • G0) * (((r⁻¹ : ℝ) : ℂ) • G0)
      rw [Matrix.smul_mul, Matrix.mul_smul, hG0_sq, smul_smul, smul_smul, mul_assoc, hinv_sq, one_smul]
    rw [← h1]; exact congrArg CFC.sqrt hsq
  have hP1_abs : matAbs A1 = P1 := by
    have h1 := matAbs_of_posSemidef hP1_psd
    have hsq : A1ᴴ * A1 = P1ᴴ * P1 := by
      rw [hP1_psd.isHermitian.eq]
      change G1 = (((r⁻¹ : ℝ) : ℂ) • G1) * (((r⁻¹ : ℝ) : ℂ) • G1)
      rw [Matrix.smul_mul, Matrix.mul_smul, hG1_sq, smul_smul, smul_smul, mul_assoc, hinv_sq, one_smul]
    rw [← h1]; exact congrArg CFC.sqrt hsq
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; norm_num [i0, i1] at this
  let A : Fin m → Mat 2 := fun k => if k = i0 then A0 else if k = i1 then A1 else 0
  let dS : Fin 2 → ℝ := fun i => if i = 0 then 2 else 0
  let dH : Fin 2 → ℝ := fun i => if i = 0 then 2 / r else 2 * x / r
  have hS : ∑ k, A k = Matrix.diagonal (fun i => (dS i : ℂ)) := by
    have hsum : ∑ k, A k = A0 + A1 := by
      have h1 := Finset.add_sum_erase Finset.univ A (Finset.mem_univ i0)
      rw [← h1]
      have h2 := Finset.add_sum_erase (Finset.univ.erase i0) A
        (Finset.mem_erase.mpr ⟨hi01.symm, Finset.mem_univ i1⟩)
      rw [← h2]
      have hrest : ∑ k ∈ (Finset.univ.erase i0).erase i1, A k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk1 : k ≠ i1 := (Finset.mem_erase.mp hk).1
        have hk0 : k ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        simp [A, hk0, hk1]
      simp [A, hi01.symm, hrest]
    rw [hsum]
    ext i j; fin_cases i <;> fin_cases j <;> simp [A0, A1, dS, Matrix.diagonal]; norm_num
  have hH : ∑ k, matAbs (A k) = Matrix.diagonal (fun i => (dH i : ℂ)) := by
    have hsum : ∑ k, matAbs (A k) = P0 + P1 := by
      have h1 := Finset.add_sum_erase Finset.univ (fun k => matAbs (A k)) (Finset.mem_univ i0)
      rw [← h1]
      have h2 := Finset.add_sum_erase (Finset.univ.erase i0) (fun k => matAbs (A k))
        (Finset.mem_erase.mpr ⟨hi01.symm, Finset.mem_univ i1⟩)
      rw [← h2]
      have hrest : ∑ k ∈ (Finset.univ.erase i0).erase i1, matAbs (A k) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk1 : k ≠ i1 := (Finset.mem_erase.mp hk).1
        have hk0 : k ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
        simp [A, hk0, hk1, matAbs_zero]
      simp [A, hi01.symm, hrest, hP0_abs, hP1_abs]
    rw [hsum]
    simp only [P0, P1, hG0_entries, hG1_entries]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [dH, Matrix.diagonal] <;> ring
  have hH_ne : ∑ k, matAbs (A k) ≠ 0 := by
    rw [hH]; intro h0
    have h00 := congr_fun (congr_fun h0 0) 0
    simp only [Matrix.diagonal_apply_eq, dH, ↓reduceIte, Matrix.zero_apply, Complex.ofReal_eq_zero] at h00
    have : 0 < 2 / r := div_pos (by norm_num) hr_pos
    linarith
  have hPowS : schattenPow p (∑ k, A k) = 2 ^ p := by
    rw [hS, schattenPow_diagonal hp0 dS (fun i => by fin_cases i <;> simp [dS]), Fin.sum_univ_two]
    simp [dS, Real.zero_rpow hp0.ne']
  have hPowH : schattenPow p (∑ k, matAbs (A k)) = (2 / r) ^ p * (1 + x ^ p) := by
    rw [hH, schattenPow_diagonal hp0 dH (fun i => by fin_cases i <;> dsimp [dH] <;> positivity), Fin.sum_univ_two]
    simp only [dH, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
    rw [show 2 * x / r = (2 / r) * x by ring, Real.mul_rpow (by positivity) hx_pos.le]
    ring
  have hstrict : 1 + x ^ p < r ^ p := by
    have hx_p : x ^ p ≤ x / 4 := by
      have : x ^ p = x * x ^ (p - 1) := by
        rw [mul_comm, ← Real.rpow_add_one hx_pos.ne', sub_add_cancel]
      rw [this]; nlinarith
    have hr_gt : 1 + x / 3 < r := by
      have hsq1 : (1 + x / 3) ^ 2 < 1 + x := by nlinarith
      rw [← hr_sq] at hsq1
      nlinarith [hr_pos]
    have hr_lt_pow : r < r ^ p := by
      have hr1 : 1 < r := by linarith
      simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hr1 hp
    linarith
  have hPow_lt : schattenPow p (∑ k, matAbs (A k)) < schattenPow p (∑ k, A k) := by
    rw [hPowH, hPowS, Real.div_rpow (by norm_num) hr_pos.le]
    have h2p : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
    have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr_pos p
    rw [div_mul_eq_mul_div, div_lt_iff₀ hrp]
    exact mul_lt_mul_of_pos_left hstrict h2p
  have hratio_gt : 1 < leeRatio p A := by
    have hH_pos : 0 < schattenNorm p (∑ k, matAbs (A k)) := (schattenNorm_pos_iff hp0 _).mpr hH_ne
    rw [leeRatio, one_lt_div hH_pos]
    exact Real.rpow_lt_rpow (schattenPow_nonneg p _) hPow_lt (one_div_pos.mpr hp0)
  have hbdd : BddAbove { r : ℝ | ∃ B : Fin m → Mat 2, (∑ k, matAbs (B k)) ≠ 0 ∧ r = leeRatio p B } :=
    ⟨(m : ℝ), by rintro r ⟨B, _, rfl⟩; exact leeRatio_le_card hp B⟩
  exact lt_of_lt_of_le hratio_gt (le_csSup hbdd ⟨A, hH_ne, rfl⟩)

end MI20
