/-
  MI20/V5_NewTheorems.lean
  ========================
  Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Purpose:     Complete Mathlib-grounded, zero-sorry, zero-warning Lean 4.33.1 formalization
               of the MI-20 V5 mathematical breakthroughs:
                 1. Quantitative Power-Variance Lemma (with exact equality characterization)
                    and Universal Spectral-Gap Theorem (finite-dimensional exact eigenvector form).
                 2. Exact Closed-Form 3-Term Bogomolny / SOS Identity at p = 4/3 (all Λ ≥ 8)
                    and 1-Line Vacuum-Defect Cubic Identity in Y = h_+ D - H ⪰ 0.
                 3. Exact Closed-Form 4-Term Bogomolny / SOS Identity at p = 3/2 (all Λ ≥ 4,
                    purely rational in m_+ = √h_+ ≥ 1).
                 4. Exact Pinching Energy Decompositions at p = 4/3 (degree 4) and p = 3/2
                    (degree 6, with all three subtracted off-diagonal penalties nonnegative).
                 5. Exact Action-Ray Convexity at p = 4/3 (t² g''(t) ≥ (1/2) g(t) > 0) and
                    p = 3/2 (t² g''(t) ≥ (1/4) g(t) > 0).
                 6. Exact 2×2 Negative Trace Drift at p = 4/3 (all Λ > 0) and the unconditional
                    Master-Trace ⟹ Global Optimality (Open Piece 1) Implication (all 1 < p < 2,
                    all m ≥ 2, including degenerate D / non-commuting Φ_j via Grassmann
                    codimension / eigenspace dimension-counting).
                 7. Exact Matrix-Pencil Factorizations, Disjoint Left Kernels, Right-Half-Plane
                    Roots, Lemma 0 (Λ σ_-(Λ) > 1), and Explicit SOS Proof of Uniform S_p
                    Branching Contraction ρ_{2κ}(s) < 1/2 at p ∈ {4/3, 3/2} for all m ≥ 2.
                 8. Exact Rational 2-Vector Rank-1 Spectral-Gap Certificates at p = 4/3
                    (d_v < 4/17 at μ = 0 and d_v < 20/73 for all μ ∈ [-0.049, +0.1616]
                    across the bracket Λ ∈ [8.6042904, 8.6042906]).
                 9. Exact 5th Universal Quadratic Moment Identity (all κ > 1, all quadratic q).
-/

import MI20.Theorem10B_SharpUniversalAndSuperexp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ==========================================================================
    PART 0: Hilbert-Schmidt, Trace, and Complex Quadratic-Form Helpers
    ========================================================================== -/

/-- Hilbert-Schmidt (Frobenius) norm squared ‖X‖_HS² = Re Tr(Xᴴ X) for complex n × n matrices. -/
def hsNormSq {n : ℕ} (X : Mat n) : ℝ :=
  (Xᴴ * X).trace.re

/-- Real Hilbert-Schmidt inner product ⟨X, Y⟩_HS = Re Tr(Xᴴ Y). -/
def hsInner {n : ℕ} (X Y : Mat n) : ℝ :=
  (Xᴴ * Y).trace.re

private lemma v5_dotProduct_star_self_im {n : ℕ} (x : Fin n → ℂ) : (star x ⬝ᵥ x).im = 0 := by
  rw [dotProduct, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_im]

private lemma v5_dotProduct_star_comm {n : ℕ} (x y : Fin n → ℂ) :
    star x ⬝ᵥ y = starRingEnd ℂ (star y ⬝ᵥ x) := by
  rw [dotProduct, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

private lemma v5_herm_dotProduct_mulVec_im {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ A.mulVec x).im = 0 := by
  have h1 : star x ⬝ᵥ A.mulVec x = starRingEnd ℂ (star x ⬝ᵥ A.mulVec x) := by
    calc star x ⬝ᵥ A.mulVec x
        = starRingEnd ℂ (star (A.mulVec x) ⬝ᵥ x) := v5_dotProduct_star_comm x (A.mulVec x)
      _ = starRingEnd ℂ ((star x ᵥ* Aᴴ) ⬝ᵥ x) := by rw [← Matrix.star_mulVec]
      _ = starRingEnd ℂ ((star x ᵥ* A) ⬝ᵥ x) := by rw [hA.eq]
      _ = starRingEnd ℂ (star x ⬝ᵥ A.mulVec x) := by rw [Matrix.dotProduct_mulVec]
  have him := congrArg Complex.im h1
  rw [Complex.conj_im] at him
  linarith

lemma hsNormSq_eq_sum_norm_sq {n : ℕ} (X : Mat n) :
    hsNormSq X = ∑ i : Fin n, ∑ j : Fin n, ‖X j i‖ ^ 2 := by
  unfold hsNormSq
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma hsNormSq_nonneg {n : ℕ} (X : Mat n) : 0 ≤ hsNormSq X := by
  rw [hsNormSq_eq_sum_norm_sq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

lemma hsNormSq_eq_zero_iff {n : ℕ} (X : Mat n) : hsNormSq X = 0 ↔ X = 0 := by
  rw [hsNormSq_eq_sum_norm_sq]
  constructor
  · intro h
    ext j i
    have hi : ∑ k : Fin n, ‖X k i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
        Finset.sum_nonneg fun b _ => sq_nonneg _).mp h i (Finset.mem_univ i)
    have hj : ‖X j i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => sq_nonneg _).mp hi j (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
  · intro h; subst h; simp

lemma trace_conjTranspose {n : ℕ} (A : Mat n) :
    Aᴴ.trace = starRingEnd ℂ A.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.conjTranspose_apply, map_sum, Complex.star_def]

lemma trace_re_conjTranspose {n : ℕ} (A : Mat n) :
    Aᴴ.trace.re = A.trace.re := by
  rw [trace_conjTranspose, Complex.conj_re]

lemma trace_re_mul_comm {n : ℕ} (A B : Mat n) :
    (A * B).trace.re = (B * A).trace.re := by
  rw [Matrix.trace_mul_comm]

lemma trace_re_mul_cycle {n : ℕ} (A B C : Mat n) :
    (A * B * C).trace.re = (C * A * B).trace.re := by
  rw [Matrix.trace_mul_cycle]

lemma trace_re_smul_real {n : ℕ} (c : ℝ) (A : Mat n) :
    (((c : ℂ) • A).trace).re = c * A.trace.re := by
  rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

lemma hsInner_comm {n : ℕ} (X Y : Mat n) : hsInner X Y = hsInner Y X := by
  unfold hsInner
  rw [← trace_re_conjTranspose (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma hsNormSq_add {n : ℕ} (X Y : Mat n) :
    hsNormSq (X + Y) = hsNormSq X + 2 * hsInner X Y + hsNormSq Y := by
  unfold hsNormSq hsInner
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Complex.add_re, Complex.add_re, Complex.add_re]
  have hsym : (Yᴴ * X).trace.re = (Xᴴ * Y).trace.re := by
    rw [← trace_re_conjTranspose (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  linarith

lemma hsNormSq_sub {n : ℕ} (X Y : Mat n) :
    hsNormSq (X - Y) = hsNormSq X - 2 * hsInner X Y + hsNormSq Y := by
  unfold hsNormSq hsInner
  rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Complex.sub_re, Complex.sub_re, Complex.sub_re]
  have hsym : (Yᴴ * X).trace.re = (Xᴴ * Y).trace.re := by
    rw [← trace_re_conjTranspose (Xᴴ * Y), Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  linarith

lemma hsNormSq_smul_real {n : ℕ} (c : ℝ) (X : Mat n) :
    hsNormSq ((c : ℂ) • X) = c ^ 2 * hsNormSq X := by
  unfold hsNormSq
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul,
    ← Complex.ofReal_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

lemma hsInner_smul_right_real {n : ℕ} (c : ℝ) (X Y : Mat n) :
    hsInner X ((c : ℂ) • Y) = c * hsInner X Y := by
  unfold hsInner
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

lemma trace_re_posSemidef_mul_nonneg {n : ℕ} {A B : Mat n}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have hA_sq : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have hB_sq : CFC.sqrt B * CFC.sqrt B = B :=
    CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB)
  have hAh : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hBh : (CFC.sqrt B).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian
  have heq : (A * B).trace.re = hsNormSq (CFC.sqrt B * CFC.sqrt A) := by
    unfold hsNormSq
    rw [Matrix.conjTranspose_mul, hAh.eq, hBh.eq]
    calc (A * B).trace.re
        = ((CFC.sqrt A * CFC.sqrt A) * (CFC.sqrt B * CFC.sqrt B)).trace.re := by rw [hA_sq, hB_sq]
      _ = ((CFC.sqrt A * (CFC.sqrt B * CFC.sqrt B)) * CFC.sqrt A).trace.re := by
            rw [Matrix.mul_assoc (CFC.sqrt A) (CFC.sqrt A), Matrix.trace_mul_comm]
      _ = ((CFC.sqrt A * CFC.sqrt B) * (CFC.sqrt B * CFC.sqrt A)).trace.re := by
            simp only [Matrix.mul_assoc]
  rw [heq]
  exact hsNormSq_nonneg _

lemma trace_re_posDef_mul_pos {n : ℕ} (hn : 1 ≤ n) {A B : Mat n}
    (hA : A.PosDef) (hB : B.PosDef) : 0 < (A * B).trace.re := by
  let Ah := posDefPow (1 / 2 : ℝ) hA
  let Bh := posDefPow (1 / 2 : ℝ) hB
  have hAh_pd : Ah.PosDef := posDefPow_posDef (1 / 2) hA
  have hBh_pd : Bh.PosDef := posDefPow_posDef (1 / 2) hB
  have hA_sq : Ah * Ah = A := by
    dsimp [Ah]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hA
  have hB_sq : Bh * Bh = B := by
    dsimp [Bh]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hB
  have heq : (A * B).trace.re = hsNormSq (Bh * Ah) := by
    unfold hsNormSq
    rw [Matrix.conjTranspose_mul, hAh_pd.isHermitian.eq, hBh_pd.isHermitian.eq]
    calc (A * B).trace.re
        = ((Ah * Ah) * (Bh * Bh)).trace.re := by rw [hA_sq, hB_sq]
      _ = ((Ah * (Bh * Bh)) * Ah).trace.re := by
            rw [Matrix.mul_assoc Ah Ah, Matrix.trace_mul_comm]
      _ = ((Ah * Bh) * (Bh * Ah)).trace.re := by simp only [Matrix.mul_assoc]
  rw [heq]
  have hne : Bh * Ah ≠ 0 := by
    intro h0
    let e0 : Fin n → ℂ := Pi.single ⟨0, by omega⟩ 1
    have he0 : e0 ≠ 0 := by
      intro h; have := congr_fun h ⟨0, by omega⟩; simp [e0] at this
    have h1 := posDef_mulVec_ne_zero hBh_pd (posDef_mulVec_ne_zero hAh_pd he0)
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec] at h1
    exact h1 rfl
  exact lt_of_le_of_ne (hsNormSq_nonneg _) (Ne.symm (mt (hsNormSq_eq_zero_iff _).mp hne))

lemma posDef_pow_eq_posDefPow {n : ℕ} {A : Mat n} (hA : A.PosDef) (m : ℕ) :
    A ^ m = posDefPow (m : ℝ) hA := by
  induction m with
  | zero => simpa using (posDefPow_zero hA).symm
  | succ m ih =>
      calc A ^ (m + 1) = A ^ m * A := pow_succ A m
        _ = posDefPow (m : ℝ) hA * posDefPow 1 hA := by rw [ih, posDefPow_one hA]
        _ = posDefPow ((m : ℝ) + 1) hA := posDefPow_mul_posDefPow (m : ℝ) 1 hA
        _ = posDefPow ((m + 1 : ℕ) : ℝ) hA := by push_cast; rfl

lemma posDef_pow {n : ℕ} {A : Mat n} (hA : A.PosDef) (m : ℕ) : (A ^ m).PosDef := by
  rw [posDef_pow_eq_posDefPow hA m]
  exact posDefPow_posDef (m : ℝ) hA

lemma trace_re_posDef_pos {n : ℕ} (hn : 1 ≤ n) {A : Mat n} (hA : A.PosDef) :
    0 < A.trace.re := by
  have h := trace_re_posDef_mul_pos hn hA Matrix.PosDef.one
  simpa using h

lemma posSemidef_quad_re_nonneg {n : ℕ} {A : Mat n} (hA : A.PosSemidef) (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ A.mulVec x).re := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA).2 x
  exact (Complex.le_def.mp h).1

private lemma mat_pow_two {n : ℕ} (A : Mat n) : A ^ 2 = A * A := sq A
private lemma mat_pow_three {n : ℕ} (A : Mat n) : A ^ 3 = A * A * A := by rw [pow_succ, sq]
private lemma mat_pow_four {n : ℕ} (A : Mat n) : A ^ 4 = A * A * A * A := by rw [pow_succ, mat_pow_three]

private lemma tr_eq {n : ℕ} {A B : Mat n} (h : A = B) : A.trace = B.trace := congrArg Matrix.trace h
private lemma tr_re_eq {n : ℕ} {A B : Mat n} (h : A = B) : A.trace.re = B.trace.re :=
  congrArg (fun X : Mat n => X.trace.re) h

private lemma posSemidef_mul_conjTranspose_self {n : ℕ} (A : Mat n) :
    (A * Aᴴ).PosSemidef := by
  simpa [Matrix.conjTranspose_conjTranspose] using Matrix.posSemidef_conjTranspose_mul_self Aᴴ

lemma posSemidef_pow_mul_self_posSemidef {n : ℕ} {A : Mat n} (hA : A.PosSemidef) :
    (A ^ 3).PosSemidef := by
  have hsq : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have hsh : (CFC.sqrt A).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hA3_eq : A ^ 3 = (A * CFC.sqrt A) * (A * CFC.sqrt A)ᴴ := by
    rw [Matrix.conjTranspose_mul, hsh.eq, hA.isHermitian.eq]
    calc A ^ 3 = A * A * A := mat_pow_three A
      _ = A * (CFC.sqrt A * CFC.sqrt A) * A := by rw [hsq]
      _ = (A * CFC.sqrt A) * (CFC.sqrt A * A) := by simp only [Matrix.mul_assoc]
  rw [hA3_eq]
  exact posSemidef_mul_conjTranspose_self (A * CFC.sqrt A)

lemma posSemidef_sq {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : (A ^ 2).PosSemidef := by
  have h : A ^ 2 = A * Aᴴ := by rw [sq, hA.eq]
  rw [h]
  exact posSemidef_mul_conjTranspose_self A

-- Generic noncommutative ring expansion helpers (instant over abstract [Ring R], zero Matrix unfolding!)
private lemma ring_add_pow_four {R : Type*} [Ring R] (A B : R) :
    (A + B) ^ 4 =
      A ^ 4 + A ^ 3 * B + A ^ 2 * B * A + A * B * A ^ 2 + B * A ^ 3 +
      A ^ 2 * B ^ 2 + A * B ^ 2 * A + B * A ^ 2 * B + B ^ 2 * A ^ 2 +
      A * B * A * B + B * A * B * A +
      A * B ^ 3 + B * A * B ^ 2 + B ^ 2 * A * B + B ^ 3 * A + B ^ 4 := by
  noncomm_ring

private lemma ring_add_pow_three {R : Type*} [Ring R] (A B : R) :
    (A + B) ^ 3 =
      A ^ 3 + (A ^ 2 * B + A * B * A + B * A ^ 2) +
      (A * B * B + B * A * B + B * B * A) + B ^ 3 := by
  noncomm_ring

private lemma ring_add_pow_three_sq {R : Type*} [Ring R] (A B : R) :
    (A + B) ^ 3 =
      A ^ 3 + (A ^ 2 * B + A * B * A + B * A ^ 2) +
      (A * B ^ 2 + B * A * B + B ^ 2 * A) + B ^ 3 := by
  noncomm_ring

private lemma ring_add_pow_three_mul_right {R : Type*} [Ring R] (A B : R) :
    (A + B) ^ 3 * B =
      A ^ 3 * B + A ^ 2 * B ^ 2 + A * B * A * B + B * A ^ 2 * B +
      A * B ^ 3 + B * A * B ^ 2 + B ^ 2 * A * B + B ^ 4 := by
  noncomm_ring

private lemma ring_mul_add_mul_add {R : Type*} [Ring R] (D H0 V : R) :
    D * (H0 + V) * D * (H0 + V) =
      D * H0 * D * H0 + D * H0 * D * V + D * V * D * H0 + D * V * D * V := by
  noncomm_ring

private lemma ring_mul_add_mul_mul {R : Type*} [Ring R] (D H0 V : R) :
    D * (H0 + V) * D * V = D * H0 * D * V + D * V * D * V := by
  noncomm_ring

private lemma ring_p32_split {R : Type*} [Ring R] (D M0 V : R) :
    D + (M0 + V) * D * (M0 + V) =
      (D + M0 * D * M0) + (M0 * D * V + V * D * M0) + V * D * V := by
  noncomm_ring

private lemma ring_add3_pow_three {R : Type*} [Ring R] (X0 X1 X2 : R) :
    (X0 + X1 + X2) ^ 3 =
      X0 ^ 3 + (X0 ^ 2 * X2 + X0 * X2 * X0 + X2 * X0 ^ 2) +
      (X0 * X1 ^ 2 + X1 * X0 * X1 + X1 ^ 2 * X0) +
      (X0 * X2 ^ 2 + X2 * X0 * X2 + X2 ^ 2 * X0) +
      (X1 ^ 2 * X2 + X1 * X2 * X1 + X2 * X1 ^ 2) + X2 ^ 3 +
      (X0 ^ 2 * X1 + X0 * X1 * X0 + X1 * X0 ^ 2) +
      (X0 * X1 * X2 + X0 * X2 * X1 + X1 * X0 * X2 + X1 * X2 * X0 + X2 * X0 * X1 + X2 * X1 * X0) +
      (X2 ^ 2 * X1 + X2 * X1 * X2 + X1 * X2 ^ 2) + X1 ^ 3 := by
  noncomm_ring

private lemma ring_add3_sq_mul {R : Type*} [Ring R] (X0 X1 X2 Y : R) :
    (X0 + X1 + X2) ^ 2 * Y =
      X0 ^ 2 * Y + X0 * X1 * Y + X0 * X2 * Y + X1 * X0 * Y + X1 ^ 2 * Y +
      X1 * X2 * Y + X2 * X0 * Y + X2 * X1 * Y + X2 ^ 2 * Y := by
  noncomm_ring

private lemma ring_add3_sq_mul_X1 {R : Type*} [Ring R] (X0 X1 X2 : R) :
    (X0 + X1 + X2) ^ 2 * X1 =
      X0 ^ 2 * X1 + X0 * X1 ^ 2 + X0 * X2 * X1 + X1 * X0 * X1 + X1 ^ 3 +
      X1 * X2 * X1 + X2 * X0 * X1 + X2 * X1 ^ 2 + X2 ^ 2 * X1 := by
  noncomm_ring

private lemma ring_add3_sq_mul_X2 {R : Type*} [Ring R] (X0 X1 X2 : R) :
    (X0 + X1 + X2) ^ 2 * X2 =
      X0 ^ 2 * X2 + X0 * X1 * X2 + X0 * X2 ^ 2 + X1 * X0 * X2 + X1 ^ 2 * X2 +
      X1 * X2 ^ 2 + X2 * X0 * X2 + X2 * X1 * X2 + X2 ^ 3 := by
  noncomm_ring

private lemma ring_p32_X12 {R : Type*} [Ring R] (D M0 V : R) :
    M0 * D * V + V * D * M0 + (V * D * V + V * D * V) =
      (M0 + V) * D * V + V * D * (M0 + V) := by
  noncomm_ring

private lemma ring_p32_DM_expand {R : Type*} [Ring R] (D M0 V : R) :
    (D * (M0 + V) * D) * ((M0 + V) * D * V) =
      (D * M0) ^ 2 * (D * V) + D * M0 * D * V * D * V +
      D * V * D * M0 * D * V + (D * V) ^ 3 := by
  noncomm_ring

/-! ==========================================================================
    PART 1: Quantitative Power-Variance Lemma & Universal Spectral-Gap Theorem
    ========================================================================== -/

/-- Key pointwise lower bound for α > 1, a > 0, x > 0:
    a^(2(α - 1)) * (x - a)^2 ≤ (x^α - a^α)^2, with strict inequality whenever x ≠ a. -/
lemma rpow_sub_rpow_sq_ge {α a x : ℝ} (hα : 1 < α) (ha : 0 < a) (hx : 0 < x) :
    a ^ (2 * (α - 1)) * (x - a) ^ 2 ≤ (x ^ α - a ^ α) ^ 2 ∧
    (x ≠ a → a ^ (2 * (α - 1)) * (x - a) ^ 2 < (x ^ α - a ^ α) ^ 2) := by
  have ha_pow_pos : 0 < a ^ α := Real.rpow_pos_of_pos ha α
  have hkey : a ^ (2 * (α - 1)) * (x - a) ^ 2 = (a ^ (α - 1) * (x - a)) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (a ^ (α - 1)) 2, ← Real.rpow_mul ha.le]
    congr 2; push_cast; ring
  have hscale : a ^ (α - 1) * (x - a) = a ^ α * (x / a - 1) := by
    have ha1 : a ^ (α - 1) * a = a ^ α := by
      calc a ^ (α - 1) * a = a ^ (α - 1) * a ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = a ^ ((α - 1) + 1) := (Real.rpow_add ha _ _).symm
        _ = a ^ α := by congr 1; ring
    calc a ^ (α - 1) * (x - a) = (a ^ (α - 1) * a) * (x / a - 1) := by field_simp [ha.ne']
      _ = a ^ α * (x / a - 1) := by rw [ha1]
  have hscale_pow : x ^ α - a ^ α = a ^ α * ((x / a) ^ α - 1) := by
    rw [Real.div_rpow hx.le ha.le]
    field_simp [ha_pow_pos.ne']
  have hstrict : x ≠ a → a ^ (2 * (α - 1)) * (x - a) ^ 2 < (x ^ α - a ^ α) ^ 2 := by
    intro hne
    rw [hkey, hscale, hscale_pow, mul_pow, mul_pow]
    refine mul_lt_mul_of_pos_left ?_ (sq_pos_of_pos ha_pow_pos)
    set t : ℝ := x / a
    have ht_pos : 0 < t := div_pos hx ha
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have ht1 : t < 1 := (div_lt_one ha).mpr hlt
      have hta : t ^ α < t := by
        simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt ht_pos ht1 hα
      have h1 : 0 < 1 - t := by linarith
      have h2 : 1 - t < 1 - t ^ α := by linarith
      nlinarith
    · have ht1 : 1 < t := (one_lt_div ha).mpr hgt
      have hta : t < t ^ α := by
        simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt ht1 hα
      have h1 : 0 < t - 1 := by linarith
      have h2 : t - 1 < t ^ α - 1 := by linarith
      nlinarith
  refine ⟨?_, hstrict⟩
  by_cases hxa : x = a
  · subst hxa; simp
  · exact (hstrict hxa).le

/-- Quantitative Power-Variance Lemma (`#6`, `ver_audit.md` §1, `p2_proof.md` Thm 5A):
    For any finite positive random variable (weights w_i ≥ 0, ∑ w_i = 1, values y_i > 0),
    exponent α > 1, gap μ > 0, and root a > 1 of a^α - a = μ:
      E[Y^α] - E[Y] ≥ μ  ⟹  Var(Y^α) ≥ a^(2(α - 1)) Var(Y),
    with equality if and only if Y is constant on its support {i : w_i > 0} (with value c ≥ a). -/
theorem quantitative_power_variance_lemma {n : ℕ} {w y : Fin n → ℝ} {α μ a : ℝ}
    (hα : 1 < α) (_hμ : 0 < μ) (ha : 1 < a) (ha_eq : a ^ α - a = μ)
    (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i : Fin n, w i = 1) (hy : ∀ i, 0 < y i)
    (hgap : μ ≤ (∑ i : Fin n, w i * (y i) ^ α) - (∑ i : Fin n, w i * y i)) :
    let m := ∑ i : Fin n, w i * y i
    let ν := ∑ i : Fin n, w i * (y i) ^ α
    let varY := ∑ i : Fin n, w i * (y i) ^ 2 - m ^ 2
    let varYa := ∑ i : Fin n, w i * ((y i) ^ α) ^ 2 - ν ^ 2
    a ^ (2 * (α - 1)) * varY ≤ varYa ∧
    (a ^ (2 * (α - 1)) * varY = varYa ↔ ∃ c : ℝ, a ≤ c ∧ ∀ i : Fin n, 0 < w i → y i = c) := by
  intro m ν varY varYa
  have ha0 : 0 < a := by linarith
  have hα0 : 0 < α := by linarith
  have hshiftY : ∀ c : ℝ, ∑ i : Fin n, w i * (y i - c) ^ 2 = varY + (c - m) ^ 2 := by
    intro c
    have hexp : ∀ i : Fin n, w i * (y i - c) ^ 2 =
        w i * (y i) ^ 2 - 2 * c * (w i * y i) + c ^ 2 * w i := fun i => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, mul_one]
    dsimp [varY, m]; ring
  have hshiftYa : ∀ c : ℝ, ∑ i : Fin n, w i * ((y i) ^ α - c) ^ 2 = varYa + (c - ν) ^ 2 := by
    intro c
    have hexp : ∀ i : Fin n, w i * ((y i) ^ α - c) ^ 2 =
        w i * ((y i) ^ α) ^ 2 - 2 * c * (w i * (y i) ^ α) + c ^ 2 * w i := fun i => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, mul_one]
    dsimp [varYa, ν]; ring
  have hvarY_nn : 0 ≤ varY := by
    have h := hshiftY m
    have hnn : 0 ≤ ∑ i : Fin n, w i * (y i - m) ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
    linarith
  have heq_mpr : (∃ c : ℝ, a ≤ c ∧ ∀ i : Fin n, 0 < w i → y i = c) →
      a ^ (2 * (α - 1)) * varY = varYa := by
    rintro ⟨c, _, hc⟩
    have hm_eq : m = c := by
      calc m = ∑ i : Fin n, w i * c := Finset.sum_congr rfl fun i _ => by
            rcases eq_or_lt_of_le (hw i) with h0 | hpos
            · rw [← h0, zero_mul, zero_mul]
            · rw [hc i hpos]
        _ = c := by rw [← Finset.sum_mul, hw_sum, one_mul]
    have hν_eq : ν = c ^ α := by
      calc ν = ∑ i : Fin n, w i * c ^ α := Finset.sum_congr rfl fun i _ => by
            rcases eq_or_lt_of_le (hw i) with h0 | hpos
            · rw [← h0, zero_mul, zero_mul]
            · rw [hc i hpos]
        _ = c ^ α := by rw [← Finset.sum_mul, hw_sum, one_mul]
    have hvarY0 : varY = 0 := by
      have h1 := hshiftY c
      have hsum0 : ∑ i : Fin n, w i * (y i - c) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rcases eq_or_lt_of_le (hw i) with h0 | hpos
          · rw [← h0, zero_mul]
          · rw [hc i hpos, sub_self, zero_pow two_ne_zero, mul_zero]
      rw [hsum0, hm_eq, sub_self, zero_pow two_ne_zero, add_zero] at h1; linarith
    have hvarYa0 : varYa = 0 := by
      have h1 := hshiftYa (c ^ α)
      have hsum0 : ∑ i : Fin n, w i * ((y i) ^ α - c ^ α) ^ 2 = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rcases eq_or_lt_of_le (hw i) with h0 | hpos
          · rw [← h0, zero_mul]
          · rw [hc i hpos, sub_self, zero_pow two_ne_zero, mul_zero]
      rw [hsum0, hν_eq, sub_self, zero_pow two_ne_zero, add_zero] at h1; linarith
    rw [hvarY0, hvarYa0, mul_zero]
  by_cases hcase : a ^ α ≤ ν
  · have hν_pos : 0 < ν := lt_of_lt_of_le (Real.rpow_pos_of_pos ha0 α) hcase
    set b : ℝ := ν ^ (1 / α)
    have hb_pos : 0 < b := Real.rpow_pos_of_pos hν_pos _
    have hb_pow : b ^ α = ν := by
      dsimp [b]; rw [← Real.rpow_mul hν_pos.le, one_div_mul_cancel hα0.ne', Real.rpow_one]
    have hab : a ≤ b := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg ha0.le α) hcase (one_div_nonneg.mpr hα0.le)
      rw [← Real.rpow_mul ha0.le, mul_one_div_cancel hα0.ne', Real.rpow_one] at h1
      exact h1
    have hab_pow : a ^ (2 * (α - 1)) ≤ b ^ (2 * (α - 1)) :=
      Real.rpow_le_rpow ha0.le hab (by linarith)
    have hpt_le : ∀ i : Fin n,
        w i * (b ^ (2 * (α - 1)) * (y i - b) ^ 2) ≤ w i * ((y i) ^ α - b ^ α) ^ 2 := fun i =>
      mul_le_mul_of_nonneg_left (rpow_sub_rpow_sq_ge hα hb_pos (hy i)).1 (hw i)
    have hsum_le : b ^ (2 * (α - 1)) * (varY + (b - m) ^ 2) ≤ varYa := by
      calc b ^ (2 * (α - 1)) * (varY + (b - m) ^ 2)
          = b ^ (2 * (α - 1)) * ∑ i : Fin n, w i * (y i - b) ^ 2 := by rw [hshiftY b]
        _ = ∑ i : Fin n, w i * (b ^ (2 * (α - 1)) * (y i - b) ^ 2) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i : Fin n, w i * ((y i) ^ α - b ^ α) ^ 2 := Finset.sum_le_sum fun i _ => hpt_le i
        _ = varYa := by rw [hshiftYa (b ^ α), hb_pow, sub_self, zero_pow two_ne_zero, add_zero]
    have hmain : a ^ (2 * (α - 1)) * varY ≤ varYa := by
      have h1 : a ^ (2 * (α - 1)) * varY ≤ b ^ (2 * (α - 1)) * varY :=
        mul_le_mul_of_nonneg_right hab_pow hvarY_nn
      have h2 : 0 ≤ b ^ (2 * (α - 1)) * (b - m) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hb_pos.le _) (sq_nonneg _)
      linarith
    refine ⟨hmain, ⟨fun heq => ?_, heq_mpr⟩⟩
    have hdiff_sum0 : ∑ i : Fin n,
        (w i * ((y i) ^ α - b ^ α) ^ 2 - w i * (b ^ (2 * (α - 1)) * (y i - b) ^ 2)) = 0 := by
      rw [Finset.sum_sub_distrib, hshiftYa (b ^ α), hb_pow, sub_self, zero_pow two_ne_zero, add_zero]
      have hL : ∑ i : Fin n, w i * (b ^ (2 * (α - 1)) * (y i - b) ^ 2) =
          b ^ (2 * (α - 1)) * (varY + (b - m) ^ 2) := by
        rw [← hshiftY b, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [hL]
      have h1 : a ^ (2 * (α - 1)) * varY ≤ b ^ (2 * (α - 1)) * varY :=
        mul_le_mul_of_nonneg_right hab_pow hvarY_nn
      have h2 : 0 ≤ b ^ (2 * (α - 1)) * (b - m) ^ 2 :=
        mul_nonneg (Real.rpow_nonneg hb_pos.le _) (sq_nonneg _)
      linarith
    refine ⟨b, hab, fun i hwi => ?_⟩
    have hterm0 : w i * ((y i) ^ α - b ^ α) ^ 2 - w i * (b ^ (2 * (α - 1)) * (y i - b) ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sub_nonneg.mpr (hpt_le k)).mp
        hdiff_sum0 i (Finset.mem_univ i)
    by_contra hne
    have hlt := (rpow_sub_rpow_sq_ge hα hb_pos (hy i)).2 hne
    have hmlt := mul_lt_mul_of_pos_left hlt hwi
    linarith
  · push Not at hcase
    have hpt_le : ∀ i : Fin n,
        w i * (a ^ (2 * (α - 1)) * (y i - a) ^ 2) ≤ w i * ((y i) ^ α - a ^ α) ^ 2 := fun i =>
      mul_le_mul_of_nonneg_left (rpow_sub_rpow_sq_ge hα ha0 (hy i)).1 (hw i)
    have hsum_le : a ^ (2 * (α - 1)) * (varY + (a - m) ^ 2) ≤ varYa + (a ^ α - ν) ^ 2 := by
      calc a ^ (2 * (α - 1)) * (varY + (a - m) ^ 2)
          = a ^ (2 * (α - 1)) * ∑ i : Fin n, w i * (y i - a) ^ 2 := by rw [hshiftY a]
        _ = ∑ i : Fin n, w i * (a ^ (2 * (α - 1)) * (y i - a) ^ 2) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i : Fin n, w i * ((y i) ^ α - a ^ α) ^ 2 := Finset.sum_le_sum fun i _ => hpt_le i
        _ = varYa + (a ^ α - ν) ^ 2 := hshiftYa (a ^ α)
    have hdiff_pos : 0 < a ^ α - ν := by linarith
    have hdiff_le : a ^ α - ν ≤ a - m := by linarith
    have ha_pow_gt1 : 1 < a ^ (2 * (α - 1)) := Real.one_lt_rpow ha (by linarith)
    have hsq_lt : (a ^ α - ν) ^ 2 < a ^ (2 * (α - 1)) * (a - m) ^ 2 := by
      have hsq1 : (a ^ α - ν) ^ 2 ≤ (a - m) ^ 2 := by nlinarith
      have hsq_pos : 0 < (a - m) ^ 2 := sq_pos_of_pos (by linarith)
      nlinarith
    have hstrict : a ^ (2 * (α - 1)) * varY < varYa := by linarith
    refine ⟨hstrict.le, ⟨fun heq => by linarith, heq_mpr⟩⟩

private lemma norm_sq_mulVec_le_of_le_smul {n : ℕ} {dmax : ℝ} (hdmax : 0 < dmax)
    {D : Mat n} (hD : D.PosDef) (hD_le : ((dmax : ℂ) • (1 : Mat n) - D).PosSemidef)
    (x : Fin n → ℂ) :
    (star (D.mulVec x) ⬝ᵥ D.mulVec x).re ≤ dmax ^ 2 * (star x ⬝ᵥ x).re := by
  let UD := hD.isHermitian.eigenvectorUnitary
  let dlam := hD.isHermitian.eigenvalues
  have hdlam_le : ∀ i : Fin n, dlam i ≤ dmax := by
    intro i
    let vi : Fin n → ℂ := (hD.isHermitian.eigenvectorBasis i).ofLp
    have hmul : D.mulVec vi = (dlam i : ℂ) • vi := hD.isHermitian.mulVec_eigenvectorBasis i
    have hnn := posSemidef_quad_re_nonneg hD_le vi
    have hnorm : star vi ⬝ᵥ vi = 1 := by
      have hin := orthonormal_iff_ite.mp hD.isHermitian.eigenvectorBasis.orthonormal i i
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hin
      simpa [vi] using hin
    have hq : star vi ⬝ᵥ ((dmax : ℂ) • (1 : Mat n) - D).mulVec vi = ((dmax - dlam i : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hmul,
        dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, hnorm, mul_one, mul_one]
      push_cast; ring
    rw [hq, Complex.ofReal_re] at hnn; linarith
  have hD_eq : D = (UD : Mat n) * Matrix.diagonal (fun i => (dlam i : ℂ)) * (UD : Mat n)ᴴ := by
    simpa [UD, dlam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hD.isHermitian.spectral_theorem
  let cy : Fin n → ℂ := (UD : Mat n)ᴴ.mulVec x
  have hLHS : (star (D.mulVec x) ⬝ᵥ D.mulVec x).re = ∑ i : Fin n, (dlam i) ^ 2 * ‖cy i‖ ^ 2 := by
    have hDx : D.mulVec x = (UD : Mat n).mulVec ((Matrix.diagonal (fun i => (dlam i : ℂ))).mulVec cy) := by
      rw [hD_eq]; simp only [cy, ← Matrix.mulVec_mulVec]
    rw [hDx, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UD, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, star_mul', Complex.star_def, Complex.conj_ofReal]
    have h1 : (dlam i : ℂ) * starRingEnd ℂ (cy i) * ((dlam i : ℂ) * cy i) =
        (((dlam i) ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (cy i) * cy i) := by push_cast; ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hRHS : (star x ⬝ᵥ x).re = ∑ i : Fin n, ‖cy i‖ ^ 2 := by
    have hx_back : x = (UD : Mat n).mulVec cy := by
      simp only [cy, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UD, Matrix.one_mulVec]
    conv_lhs => rw [hx_back]
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UD, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hLHS, hRHS, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 : 0 < dlam i := hD.eigenvalues_pos i
  have hsq : (dlam i) ^ 2 ≤ dmax ^ 2 := by nlinarith [hdlam_le i]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Finite-dimensional Universal Spectral-Gap Theorem (`#6`, `p2_proof.md` Thm 5B):
    On any finite-dimensional solution (D, H) ≻ 0 of Holden's equation with D ⪯ dmax·I,
    if v ≠ 0 is a joint eigenvector with D v = d_v v and Φ v = μ d_v^(2κ) v (μ > 0, g > 1
    solving g^κ - g^(κ-1) = μ), then EITHER v is a decoupled 1×1 h_+-eigenvector
    (H v = g d_v v and (1 + g)^(2κ - 1) = Λ g^(κ - 1)), OR d_v < dmax / g strictly! -/
theorem universal_spectral_gap_theorem {n : ℕ} {κ Λ μ g dv dmax : ℝ}
    (hκ : 1 < κ) (_hΛ : 0 < Λ) (hμ : 0 < μ) (hg : 1 < g)
    (hg_eq : g ^ κ - g ^ (κ - 1) = μ) (hdmax : 0 < dmax)
    {D H : Mat n} (hD : D.PosDef) (hD_le : ((dmax : ℂ) • (1 : Mat n) - D).PosSemidef)
    (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = (dv : ℂ) • v)
    (hPhiv : (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) -
      D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) * D).mulVec v =
      ((μ * dv ^ (2 * κ) : ℝ) : ℂ) • v) :
    (H.mulVec v = ((g * dv : ℝ) : ℂ) • v ∧ (1 + g) ^ (2 * κ - 1) = Λ * g ^ (κ - 1)) ∨
    dv < dmax / g := by
  have hdv : 0 < dv := (posDefPow_mulVec_of_eig 1 hD hv hDv).1
  have hkm1 : 0 < κ - 1 := by linarith
  have hv_norm_pos : 0 < (star v ⬝ᵥ v).re := by
    rw [dotProduct, Complex.re_sum]
    obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by by_contra h; push Not at h; exact hv (funext h)
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg _
    · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_pos_of_pos (norm_pos_iff.mpr hi0)
  let nv : ℝ := Real.sqrt (star v ⬝ᵥ v).re
  have hnv : 0 < nv := Real.sqrt_pos.mpr hv_norm_pos
  let u : Fin n → ℂ := ((nv⁻¹ : ℝ) : ℂ) • v
  have hu_norm : (star u ⬝ᵥ u).re = 1 := by
    have hst : star u = ((nv⁻¹ : ℝ) : ℂ) • star v := by ext i; simp [u]
    rw [hst]
    change (((nv⁻¹ : ℝ) : ℂ) • star v ⬝ᵥ ((nv⁻¹ : ℝ) : ℂ) • v).re = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hmul : ((nv⁻¹ : ℝ) : ℂ) * (((nv⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ v)) =
        ((nv⁻¹ * nv⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ v) := by push_cast; ring
    rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hsq : nv * nv = (star v ⬝ᵥ v).re := Real.mul_self_sqrt hv_norm_pos.le
    field_simp [hnv.ne']; linarith
  have hDu : D.mulVec u = (dv : ℂ) • u := by
    change D.mulVec (((nv⁻¹ : ℝ) : ℂ) • v) = (dv : ℂ) • (((nv⁻¹ : ℝ) : ℂ) • v)
    rw [Matrix.mulVec_smul, hDv, smul_comm]
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
  let G := Dhalf * H * Dhalf
  let Gkm1 := posDefPow (κ - 1) hG
  let Gk := posDefPow κ hG
  have hPhiu : (Gk - D * Gkm1 * D).mulVec u = ((μ * dv ^ (2 * κ) : ℝ) : ℂ) • u := by
    change (Gk - D * Gkm1 * D).mulVec (((nv⁻¹ : ℝ) : ℂ) • v) =
      ((μ * dv ^ (2 * κ) : ℝ) : ℂ) • (((nv⁻¹ : ℝ) : ℂ) • v)
    rw [Matrix.mulVec_smul, hPhiv, smul_comm]
  let UG := hG.isHermitian.eigenvectorUnitary
  let lam := hG.isHermitian.eigenvalues
  let z : Fin n → ℂ := (UG : Mat n)ᴴ.mulVec u
  let w : Fin n → ℝ := fun i => ‖z i‖ ^ 2
  let y : Fin n → ℝ := fun i => (lam i / dv ^ 2) ^ (κ - 1)
  let α : ℝ := κ / (κ - 1)
  let a : ℝ := g ^ (κ - 1)
  have hα : 1 < α := by dsimp [α]; rw [one_lt_div hkm1]; linarith
  have ha : 1 < a := Real.one_lt_rpow hg hkm1
  have ha_eq : a ^ α - a = μ := by
    dsimp [a, α]
    rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ g), mul_div_cancel₀ κ hkm1.ne']
    exact hg_eq
  have hw_nn : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have hy_pos : ∀ i, 0 < y i := fun i =>
    Real.rpow_pos_of_pos (div_pos (hG.eigenvalues_pos i) (sq_pos_of_pos hdv)) _
  have hya : ∀ i, (y i) ^ α = (lam i / dv ^ 2) ^ κ := fun i => by
    dsimp [y, α]
    rw [← Real.rpow_mul (div_nonneg (hG.eigenvalues_pos i).le (sq_nonneg dv))]
    congr 1; exact mul_div_cancel₀ κ hkm1.ne'
  have hw_sum : ∑ i : Fin n, w i = 1 := by
    have hu : u = (UG : Mat n).mulVec z := by
      simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UG, Matrix.one_mulVec]
    have h1 : (star u ⬝ᵥ u).re = ∑ i : Fin n, w i := by
      conv_lhs => rw [hu]
      rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
        unitary_conjTranspose_mul_self UG, Matrix.vecMul_one, dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    linarith
  have hquad_G : ∀ r : ℝ, (star u ⬝ᵥ (posDefPow r hG).mulVec u).re = ∑ i : Fin n, w i * (lam i) ^ r := by
    intro r
    unfold posDefPow
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hst : star u ᵥ* (UG : Mat n) = star z := by
      simp only [z, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    change (star u ᵥ* (UG : Mat n) ⬝ᵥ (Matrix.diagonal fun i => (((lam i) ^ r : ℝ) : ℂ)).mulVec z).re = _
    rw [hst, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have h1 : starRingEnd ℂ (z i) * ((((lam i) ^ r : ℝ) : ℂ) * z i) =
        (((lam i) ^ r : ℝ) : ℂ) * (starRingEnd ℂ (z i) * z i) := by ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  let mY : ℝ := ∑ i : Fin n, w i * y i
  let νY : ℝ := ∑ i : Fin n, w i * (y i) ^ α
  have hdv2_pow : ∀ r : ℝ, (dv ^ 2) ^ r = dv ^ (2 * r) := fun r => by
    rw [← Real.rpow_natCast dv 2, ← Real.rpow_mul hdv.le]; push_cast; ring_nf
  have hstar_Du : star u ᵥ* D = (dv : ℂ) • star u := by
    have h1 := (Matrix.star_mulVec D u).symm
    rw [hD.isHermitian.eq, hDu] at h1
    ext i; have hi := congr_fun h1 i; simpa using hi
  have hE_gap : νY - mY = μ := by
    have h1 : (star u ⬝ᵥ (Gk - D * Gkm1 * D).mulVec u).re = μ * dv ^ (2 * κ) := by
      rw [hPhiu, dotProduct_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hu_norm, mul_one]
    have h2 : (star u ⬝ᵥ (Gk - D * Gkm1 * D).mulVec u).re =
        (star u ⬝ᵥ Gk.mulVec u).re - dv ^ 2 * (star u ⬝ᵥ Gkm1.mulVec u).re := by
      have hmul3 : (D * Gkm1 * D).mulVec u = (dv : ℂ) • D.mulVec (Gkm1.mulVec u) := by
        calc (D * Gkm1 * D).mulVec u
            = (D * Gkm1).mulVec (D.mulVec u) := (Matrix.mulVec_mulVec u (D * Gkm1) D).symm
          _ = (D * Gkm1).mulVec ((dv : ℂ) • u) := by rw [hDu]
          _ = (dv : ℂ) • D.mulVec (Gkm1.mulVec u) := by rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
      have hterm2 : (star u ⬝ᵥ ((dv : ℂ) • D.mulVec (Gkm1.mulVec u))).re =
          dv ^ 2 * (star u ⬝ᵥ Gkm1.mulVec u).re := by
        rw [dotProduct_smul, smul_eq_mul, Matrix.dotProduct_mulVec, hstar_Du,
          smul_dotProduct, smul_eq_mul]
        have hsqc : (dv : ℂ) * ((dv : ℂ) * (star u ⬝ᵥ Gkm1.mulVec u)) =
            ((dv ^ 2 : ℝ) : ℂ) * (star u ⬝ᵥ Gkm1.mulVec u) := by push_cast; ring
        rw [hsqc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hmul3, hterm2]
    rw [hquad_G κ, hquad_G (κ - 1)] at h2
    have hν_eq : ∑ i : Fin n, w i * (lam i) ^ κ = dv ^ (2 * κ) * νY := by
      dsimp [νY]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [hya i, Real.div_rpow (hG.eigenvalues_pos i).le (sq_nonneg dv), hdv2_pow]
      have hne : dv ^ (2 * κ) ≠ 0 := (Real.rpow_pos_of_pos hdv _).ne'
      dsimp only [lam]; field_simp [hne]
    have hm_eq : dv ^ 2 * ∑ i : Fin n, w i * (lam i) ^ (κ - 1) = dv ^ (2 * κ) * mY := by
      dsimp [mY]; rw [Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [y]; rw [Real.div_rpow (hG.eigenvalues_pos i).le (sq_nonneg dv), hdv2_pow]
      have hpow : dv ^ 2 * dv ^ (2 * (κ - 1)) = dv ^ (2 * κ) := by
        calc dv ^ 2 * dv ^ (2 * (κ - 1))
            = dv ^ (2 : ℝ) * dv ^ (2 * (κ - 1)) := by rw [← Real.rpow_natCast dv 2]; norm_cast
          _ = dv ^ ((2 : ℝ) + 2 * (κ - 1)) := (Real.rpow_add hdv _ _).symm
          _ = dv ^ (2 * κ) := by congr 1; ring
      have hne : dv ^ (2 * (κ - 1)) ≠ 0 := (Real.rpow_pos_of_pos hdv _).ne'
      dsimp only [lam]
      calc dv ^ 2 * (w i * (hG.isHermitian.eigenvalues i) ^ (κ - 1))
          = (dv ^ 2 * dv ^ (2 * (κ - 1))) *
              (w i * ((hG.isHermitian.eigenvalues i) ^ (κ - 1) / dv ^ (2 * (κ - 1)))) := by
              field_simp [hne]
        _ = dv ^ (2 * κ) * (w i * ((hG.isHermitian.eigenvalues i) ^ (κ - 1) / dv ^ (2 * (κ - 1)))) := by
              rw [hpow]
    have hdv2k_pos : 0 < dv ^ (2 * κ) := Real.rpow_pos_of_pos hdv _
    rw [hν_eq, hm_eq] at h2
    have hmul_eq : dv ^ (2 * κ) * (νY - mY) = dv ^ (2 * κ) * μ := by linarith
    exact mul_left_cancel₀ hdv2k_pos.ne' hmul_eq
  let w_orth : Fin n → ℂ := Gkm1.mulVec u - ((mY * dv ^ (2 * (κ - 1)) : ℝ) : ℂ) • u
  let z_orth : Fin n → ℂ := Gk.mulVec u - ((νY * dv ^ (2 * κ) : ℝ) : ℂ) • u
  have hz_eq_Dw : z_orth = (dv : ℂ) • D.mulVec w_orth := by
    have hmul3 : (D * Gkm1 * D).mulVec u = (dv : ℂ) • D.mulVec (Gkm1.mulVec u) := by
      calc (D * Gkm1 * D).mulVec u
          = (D * Gkm1).mulVec (D.mulVec u) := (Matrix.mulVec_mulVec u (D * Gkm1) D).symm
        _ = (D * Gkm1).mulVec ((dv : ℂ) • u) := by rw [hDu]
        _ = (dv : ℂ) • D.mulVec (Gkm1.mulVec u) := by rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    have h1 : Gk.mulVec u - (dv : ℂ) • D.mulVec (Gkm1.mulVec u) = ((μ * dv ^ (2 * κ) : ℝ) : ℂ) • u := by
      have := hPhiu; rw [Matrix.sub_mulVec, hmul3] at this; exact this
    have hpow : dv * dv * dv ^ (2 * (κ - 1)) = dv ^ (2 * κ) := by
      calc dv * dv * dv ^ (2 * (κ - 1))
          = dv ^ (2 : ℝ) * dv ^ (2 * (κ - 1)) := by
              rw [← sq, ← Real.rpow_natCast dv 2]; norm_cast
        _ = dv ^ ((2 : ℝ) + 2 * (κ - 1)) := (Real.rpow_add hdv _ _).symm
        _ = dv ^ (2 * κ) := by congr 1; ring
    change Gk.mulVec u - ((νY * dv ^ (2 * κ) : ℝ) : ℂ) • u =
      (dv : ℂ) • D.mulVec (Gkm1.mulVec u - ((mY * dv ^ (2 * (κ - 1)) : ℝ) : ℂ) • u)
    conv_rhs => rw [Matrix.mulVec_sub]; arg 2; arg 2; rw [Matrix.mulVec_smul, hDu]
    rw [smul_sub, smul_smul, smul_smul]
    ext i
    have hi := congr_fun h1 i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    have hcoef : ((νY * dv ^ (2 * κ) : ℝ) : ℂ) - ((μ * dv ^ (2 * κ) : ℝ) : ℂ) =
        (dv : ℂ) * (((mY * dv ^ (2 * (κ - 1)) : ℝ) : ℂ) * (dv : ℂ)) := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1; rw [← hE_gap, ← hpow]; ring
    have hui : u i = ((nv⁻¹ : ℝ) : ℂ) * v i := rfl
    rw [hui] at hi ⊢
    linear_combination hi - hcoef * (((nv⁻¹ : ℝ) : ℂ) * v i)
  have hD_norm_le := norm_sq_mulVec_le_of_le_smul hdmax hD hD_le w_orth
  let varY : ℝ := ∑ i : Fin n, w i * (y i) ^ 2 - mY ^ 2
  let varYa : ℝ := ∑ i : Fin n, w i * ((y i) ^ α) ^ 2 - νY ^ 2
  have hw_orth_norm : (star w_orth ⬝ᵥ w_orth).re = dv ^ (4 * (κ - 1)) * varY := by
    have hvec : w_orth = (UG : Mat n).mulVec (fun i =>
        (((dv ^ (2 * (κ - 1)) * (y i - mY) : ℝ) : ℂ)) * z i) := by
      have hu : u = (UG : Mat n).mulVec z := by
        simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UG, Matrix.one_mulVec]
      have hGkm1u : Gkm1.mulVec u = (UG : Mat n).mulVec (fun i => (((lam i) ^ (κ - 1) : ℝ) : ℂ) * z i) := by
        change ((UG : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (κ - 1) : ℝ) : ℂ)) * (UG : Mat n)ᴴ).mulVec u = _
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        congr 1; ext i; simp [z, Matrix.mulVec_diagonal]
      change Gkm1.mulVec u - ((mY * dv ^ (2 * (κ - 1)) : ℝ) : ℂ) • u = _
      rw [hGkm1u]; conv_lhs => rw [hu]
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
      congr 1; ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hl : (lam i) ^ (κ - 1) = dv ^ (2 * (κ - 1)) * y i := by
        dsimp [y, lam]; rw [Real.div_rpow (hG.eigenvalues_pos i).le (sq_nonneg dv), hdv2_pow]
        field_simp [(Real.rpow_pos_of_pos hdv _).ne']
      rw [hl]; push_cast; ring
    rw [hvec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UG, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    have hstep : ∑ i : Fin n, (star (fun k => (((dv ^ (2 * (κ - 1)) * (y k - mY) : ℝ) : ℂ)) * z k) i *
        ((((dv ^ (2 * (κ - 1)) * (y i - mY) : ℝ) : ℂ)) * z i)).re =
        dv ^ (4 * (κ - 1)) * ∑ i : Fin n, w i * (y i - mY) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      have h1 : ((((dv ^ (2 * (κ - 1)) * (y i - mY) : ℝ) : ℂ)) * starRingEnd ℂ (z i)) *
          ((((dv ^ (2 * (κ - 1)) * (y i - mY) : ℝ) : ℂ)) * z i) =
          ((((dv ^ (2 * (κ - 1)) * (y i - mY)) ^ 2 : ℝ) : ℂ)) * (starRingEnd ℂ (z i) * z i) := by
        push_cast; ring
      rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hsq : (dv ^ (2 * (κ - 1))) ^ 2 = dv ^ (4 * (κ - 1)) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hdv.le]; congr 1; push_cast; ring
      rw [mul_pow, hsq]; ring
    rw [hstep]; congr 1
    have hexp : ∀ i : Fin n, w i * (y i - mY) ^ 2 = w i * (y i) ^ 2 - 2 * mY * (w i * y i) + mY ^ 2 * w i :=
      fun i => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, mul_one]
    dsimp [varY, mY]; ring
  have hz_orth_norm : (star z_orth ⬝ᵥ z_orth).re = dv ^ (4 * κ) * varYa := by
    have hvec : z_orth = (UG : Mat n).mulVec (fun i =>
        (((dv ^ (2 * κ) * ((y i) ^ α - νY) : ℝ) : ℂ)) * z i) := by
      have hu : u = (UG : Mat n).mulVec z := by
        simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UG, Matrix.one_mulVec]
      have hGku : Gk.mulVec u = (UG : Mat n).mulVec (fun i => (((lam i) ^ κ : ℝ) : ℂ) * z i) := by
        change ((UG : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ κ : ℝ) : ℂ)) * (UG : Mat n)ᴴ).mulVec u = _
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        congr 1; ext i; simp [z, Matrix.mulVec_diagonal]
      change Gk.mulVec u - ((νY * dv ^ (2 * κ) : ℝ) : ℂ) • u = _
      rw [hGku]; conv_lhs => rw [hu]
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
      congr 1; ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hl : (lam i) ^ κ = dv ^ (2 * κ) * (y i) ^ α := by
        rw [hya i]; dsimp [lam]; rw [Real.div_rpow (hG.eigenvalues_pos i).le (sq_nonneg dv), hdv2_pow]
        field_simp [(Real.rpow_pos_of_pos hdv _).ne']
      rw [hl]; push_cast; ring
    rw [hvec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UG, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    have hstep : ∑ i : Fin n, (star (fun k => (((dv ^ (2 * κ) * ((y k) ^ α - νY) : ℝ) : ℂ)) * z k) i *
        ((((dv ^ (2 * κ) * ((y i) ^ α - νY) : ℝ) : ℂ)) * z i)).re =
        dv ^ (4 * κ) * ∑ i : Fin n, w i * ((y i) ^ α - νY) ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [w, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
      have h1 : ((((dv ^ (2 * κ) * ((y i) ^ α - νY) : ℝ) : ℂ)) * starRingEnd ℂ (z i)) *
          ((((dv ^ (2 * κ) * ((y i) ^ α - νY) : ℝ) : ℂ)) * z i) =
          ((((dv ^ (2 * κ) * ((y i) ^ α - νY)) ^ 2 : ℝ) : ℂ)) * (starRingEnd ℂ (z i) * z i) := by
        push_cast; ring
      rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hsq : (dv ^ (2 * κ)) ^ 2 = dv ^ (4 * κ) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hdv.le]; congr 1; push_cast; ring
      rw [mul_pow, hsq]; ring
    rw [hstep]; congr 1
    have hexp : ∀ i : Fin n, w i * ((y i) ^ α - νY) ^ 2 =
        w i * ((y i) ^ α) ^ 2 - 2 * νY * (w i * (y i) ^ α) + νY ^ 2 * w i := fun i => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, mul_one]
    dsimp [varYa, νY]; ring
  have hvar_upper : dv ^ 2 * varYa ≤ dmax ^ 2 * varY := by
    have hz_norm_le : (star z_orth ⬝ᵥ z_orth).re ≤ dv ^ 2 * dmax ^ 2 * (star w_orth ⬝ᵥ w_orth).re := by
      have hst : star z_orth = (dv : ℂ) • star (D.mulVec w_orth) := by
        rw [hz_eq_Dw]; ext i; simp
      rw [hst, hz_eq_Dw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hsq : (dv : ℂ) * ((dv : ℂ) * (star (D.mulVec w_orth) ⬝ᵥ D.mulVec w_orth)) =
          ((dv ^ 2 : ℝ) : ℂ) * (star (D.mulVec w_orth) ⬝ᵥ D.mulVec w_orth) := by push_cast; ring
      rw [hsq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith [hD_norm_le, sq_nonneg dv]
    rw [hz_orth_norm, hw_orth_norm] at hz_norm_le
    have hpow4 : dv ^ (4 * κ) = dv ^ 2 * dv ^ (4 * (κ - 1)) * dv ^ 2 := by
      calc dv ^ (4 * κ) = dv ^ ((2 : ℝ) + (4 * (κ - 1) + 2)) := by congr 1; ring
        _ = dv ^ (2 : ℝ) * dv ^ (4 * (κ - 1) + 2) := Real.rpow_add hdv _ _
        _ = dv ^ (2 : ℝ) * (dv ^ (4 * (κ - 1)) * dv ^ (2 : ℝ)) := by rw [Real.rpow_add hdv]
        _ = dv ^ 2 * dv ^ (4 * (κ - 1)) * dv ^ 2 := by
              rw [← Real.rpow_natCast dv 2]; push_cast; ring
    have hfac_pos : 0 < dv ^ 2 * dv ^ (4 * (κ - 1)) :=
      mul_pos (sq_pos_of_pos hdv) (Real.rpow_pos_of_pos hdv _)
    rw [hpow4] at hz_norm_le
    have h1 : dv ^ 2 * dv ^ (4 * (κ - 1)) * (dv ^ 2 * varYa) ≤
        dv ^ 2 * dv ^ (4 * (κ - 1)) * (dmax ^ 2 * varY) := by linarith
    exact le_of_mul_le_mul_left h1 hfac_pos
  have ha_exp : a ^ (2 * (α - 1)) = g ^ 2 := by
    dsimp [a, α]
    rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ g)]
    have hexp : (κ - 1) * (2 * (κ / (κ - 1) - 1)) = (2 : ℕ) := by
      field_simp [hkm1.ne']; push_cast; ring
    rw [hexp, Real.rpow_natCast]
  obtain ⟨hqpv, hqpv_eq⟩ := quantitative_power_variance_lemma hα hμ ha ha_eq hw_nn hw_sum hy_pos hE_gap.ge
  change a ^ (2 * (α - 1)) * varY ≤ varYa at hqpv
  change (a ^ (2 * (α - 1)) * varY = varYa ↔ ∃ c, a ≤ c ∧ ∀ i, 0 < w i → y i = c) at hqpv_eq
  rw [ha_exp] at hqpv hqpv_eq
  by_cases hvar0 : varY = 0
  · left
    have hvarYa0 : varYa = 0 := by
      have hnn : 0 ≤ varYa := by
        have h1 : 0 ≤ dv ^ (4 * κ) * varYa := by
          rw [← hz_orth_norm, dotProduct, Complex.re_sum]
          exact Finset.sum_nonneg fun i _ => by
            simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
            exact sq_nonneg _
        exact nonneg_of_mul_nonneg_right h1 (Real.rpow_pos_of_pos hdv _)
      nlinarith [sq_pos_of_pos hdv]
    obtain ⟨c, hac, hc⟩ := hqpv_eq.mp (by rw [hvar0, hvarYa0, mul_zero])
    have hca : c = a := by
      have hm_eq : mY = c := by
        calc mY = ∑ i : Fin n, w i * c := Finset.sum_congr rfl fun i _ => by
              rcases eq_or_lt_of_le (hw_nn i) with h0 | hpos
              · rw [← h0, zero_mul, zero_mul]
              · rw [hc i hpos]
          _ = c := by rw [← Finset.sum_mul, hw_sum, one_mul]
      have hν_eq : νY = c ^ α := by
        calc νY = ∑ i : Fin n, w i * c ^ α := Finset.sum_congr rfl fun i _ => by
              rcases eq_or_lt_of_le (hw_nn i) with h0 | hpos
              · rw [← h0, zero_mul, zero_mul]
              · rw [hc i hpos]
          _ = c ^ α := by rw [← Finset.sum_mul, hw_sum, one_mul]
      have hceq : c ^ α - c = a ^ α - a := by rw [← hν_eq, ← hm_eq, hE_gap, ha_eq]
      rcases eq_or_lt_of_le hac with heq | hlt
      · exact heq.symm
      · exfalso
        have h1 := (rpow_sub_rpow_sq_ge hα (by linarith : 0 < a) (by linarith : 0 < c)).2 hlt.ne'
        have hpos : 0 < c - a := by linarith
        have hpos2 : 0 < c ^ α - a ^ α := by
          have := Real.rpow_lt_rpow (by linarith) hlt (by linarith : (0 : ℝ) < α); linarith
        have hsq : (a ^ (α - 1) * (c - a)) ^ 2 < (c ^ α - a ^ α) ^ 2 := by
          have he : (a ^ (α - 1) * (c - a)) ^ 2 = a ^ (2 * (α - 1)) * (c - a) ^ 2 := by
            rw [mul_pow, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by linarith : 0 ≤ a)]
            congr 2; push_cast; ring
          linarith
        have h2 : a ^ (α - 1) * (c - a) < c ^ α - a ^ α := by
          nlinarith only [hsq, hpos, hpos2, Real.rpow_pos_of_pos (by linarith only [ha] : 0 < a) (α - 1)]
        have ha1 : 1 < a ^ (α - 1) := Real.one_lt_rpow ha (by linarith only [hα])
        nlinarith only [hceq, h2, ha1, hpos]
    have hlam_eq : ∀ i : Fin n, z i ≠ 0 → lam i = g * dv ^ 2 := by
      intro i hzi
      have hwi : 0 < w i := sq_pos_of_pos (norm_pos_iff.mpr hzi)
      have hyi : (lam i / dv ^ 2) ^ (κ - 1) = g ^ (κ - 1) := by
        simpa [y, a, hca] using hc i hwi
      have hinv := congrArg (fun t => t ^ (κ - 1)⁻¹) hyi
      rw [← Real.rpow_mul (div_nonneg (hG.eigenvalues_pos i).le (sq_nonneg dv)),
        ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ g), mul_inv_cancel₀ hkm1.ne',
        Real.rpow_one, Real.rpow_one] at hinv
      exact (div_eq_iff (sq_pos_of_pos hdv).ne').mp hinv
    have hGu : G.mulVec u = ((g * dv ^ 2 : ℝ) : ℂ) • u := by
      have hG_eq : G = (UG : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (UG : Mat n)ᴴ := by
        simpa [UG, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hG.isHermitian.spectral_theorem
      have hdiag_z : (Matrix.diagonal (fun i => (lam i : ℂ))).mulVec z = ((g * dv ^ 2 : ℝ) : ℂ) • z := by
        ext i; simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases hzi : z i = 0
        · simp [hzi]
        · rw [hlam_eq i hzi]
      rw [hG_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      change (UG : Mat n).mulVec ((Matrix.diagonal (fun i => (lam i : ℂ))).mulVec z) = _
      rw [hdiag_z, Matrix.mulVec_smul]
      simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UG, Matrix.one_mulVec]
    have hGv : G.mulVec v = ((g * dv ^ 2 : ℝ) : ℂ) • v := by
      have h1 := congrArg (fun x => ((nv : ℝ) : ℂ) • x) hGu
      have hnvu : ((nv : ℝ) : ℂ) • u = v := by
        change ((nv : ℝ) : ℂ) • (((nv⁻¹ : ℝ) : ℂ) • v) = v
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnv.ne', Complex.ofReal_one, one_smul]
      rw [← Matrix.mulVec_smul, hnvu, smul_comm, hnvu] at h1; exact h1
    have hDhalf_v : Dhalf.mulVec v = ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ) • v :=
      (posDefPow_mulVec_of_eig (1 / 2) hD hv hDv).2
    have hHv : H.mulVec v = ((g * dv : ℝ) : ℂ) • v := by
      have h1 : Dhalf.mulVec (H.mulVec v) = Dhalf.mulVec (((g * dv : ℝ) : ℂ) • v) := by
        have hstep : Dhalf.mulVec (H.mulVec (Dhalf.mulVec v)) = ((g * dv ^ 2 : ℝ) : ℂ) • v := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; exact hGv
        rw [hDhalf_v, Matrix.mulVec_smul, Matrix.mulVec_smul] at hstep
        rw [Matrix.mulVec_smul, hDhalf_v, smul_smul]
        have hdh_pos : 0 < dv ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hdv _
        have hmul_eq : ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ) • Dhalf.mulVec (H.mulVec v) =
            ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ) • ((((g * dv : ℝ) : ℂ) * ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ)) • v) := by
          rw [hstep, smul_smul]
          congr 1; rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1
          have hsq : dv ^ (1 / 2 : ℝ) * dv ^ (1 / 2 : ℝ) = dv := by
            rw [← Real.rpow_add hdv]; norm_num
          calc g * dv ^ 2 = g * dv * (dv ^ (1 / 2 : ℝ) * dv ^ (1 / 2 : ℝ)) := by rw [hsq]; ring
            _ = dv ^ (1 / 2 : ℝ) * (g * dv * dv ^ (1 / 2 : ℝ)) := by ring
        exact smul_right_injective (Fin n → ℂ) (Complex.ofReal_ne_zero.mpr hdh_pos.ne') hmul_eq
      have h0 : Dhalf.mulVec (H.mulVec v - ((g * dv : ℝ) : ℂ) • v) = 0 := by
        rw [Matrix.mulVec_sub, h1, sub_self]
      by_contra hne
      exact posDef_mulVec_ne_zero (posDefPow_posDef (1 / 2) hD) (sub_ne_zero.mpr hne) h0
    refine ⟨hHv, ?_⟩
    have hDHv : (D + H).mulVec v = (((1 + g) * dv : ℝ) : ℂ) • v := by
      rw [Matrix.add_mulVec, hDv, hHv, ← add_smul]; congr 1; push_cast; ring
    have hL := (posDefPow_mulVec_of_eig (2 * κ - 1) (hD.add hH) hv hDHv).2
    have hGkm1_v := (posDefPow_mulVec_of_eig (κ - 1) hG hv hGv).2
    have hR : (posDefPow (2 * κ - 1) (hD.add hH)).mulVec v =
        ((Λ * ((g * dv ^ 2) ^ (κ - 1) * dv) : ℝ) : ℂ) • v := by
      rw [hEq, Matrix.smul_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hDhalf_v, Matrix.mulVec_smul, hGkm1_v, Matrix.mulVec_smul, Matrix.mulVec_smul, hDhalf_v,
        smul_smul, smul_smul, smul_smul]
      congr 1; rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1
      have hsq : dv ^ (1 / 2 : ℝ) * dv ^ (1 / 2 : ℝ) = dv := by
        rw [← Real.rpow_add hdv]; norm_num
      calc Λ * dv ^ (1 / 2 : ℝ) * (g * dv ^ 2) ^ (κ - 1) * dv ^ (1 / 2 : ℝ)
          = Λ * ((g * dv ^ 2) ^ (κ - 1) * (dv ^ (1 / 2 : ℝ) * dv ^ (1 / 2 : ℝ))) := by ring
        _ = Λ * ((g * dv ^ 2) ^ (κ - 1) * dv) := by rw [hsq]
    have heq_v : ((((1 + g) * dv) ^ (2 * κ - 1) : ℝ) : ℂ) • v =
        ((Λ * ((g * dv ^ 2) ^ (κ - 1) * dv) : ℝ) : ℂ) • v := hL.symm.trans hR
    have hsc_c : ((((1 + g) * dv) ^ (2 * κ - 1) : ℝ) : ℂ) =
        ((Λ * ((g * dv ^ 2) ^ (κ - 1) * dv) : ℝ) : ℂ) := by
      obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by by_contra h; push Not at h; exact hv (funext h)
      have hi := congr_fun heq_v i0
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      exact mul_right_cancel₀ hi0 hi
    have hsc := Complex.ofReal_injective hsc_c
    rw [Real.mul_rpow (by linarith) hdv.le,
      Real.mul_rpow (by linarith) (sq_nonneg dv), hdv2_pow] at hsc
    have hdv_exp : dv ^ (2 * (κ - 1)) * dv = dv ^ (2 * κ - 1) := by
      calc dv ^ (2 * (κ - 1)) * dv = dv ^ (2 * (κ - 1)) * dv ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = dv ^ (2 * (κ - 1) + 1) := (Real.rpow_add hdv _ _).symm
        _ = dv ^ (2 * κ - 1) := by congr 1; ring
    have hdv2km1_pos : 0 < dv ^ (2 * κ - 1) := Real.rpow_pos_of_pos hdv _
    have hsc2 : (1 + g) ^ (2 * κ - 1) * dv ^ (2 * κ - 1) =
        (Λ * g ^ (κ - 1)) * dv ^ (2 * κ - 1) := by
      calc (1 + g) ^ (2 * κ - 1) * dv ^ (2 * κ - 1)
          = Λ * (g ^ (κ - 1) * dv ^ (2 * (κ - 1)) * dv) := hsc
        _ = Λ * (g ^ (κ - 1) * (dv ^ (2 * (κ - 1)) * dv)) := by ring
        _ = (Λ * g ^ (κ - 1)) * dv ^ (2 * κ - 1) := by rw [hdv_exp]; ring
    exact mul_right_cancel₀ hdv2km1_pos.ne' hsc2
  · right
    have hvar_pos : 0 < varY := by
      have hnn : 0 ≤ dv ^ (4 * (κ - 1)) * varY := by
        rw [← hw_orth_norm, dotProduct, Complex.re_sum]
        exact Finset.sum_nonneg fun i _ => by
          simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          exact sq_nonneg _
      exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right hnn (Real.rpow_pos_of_pos hdv _)) (Ne.symm hvar0)
    have hqpv_strict : g ^ 2 * varY < varYa := by
      refine lt_of_le_of_ne hqpv fun heq => ?_
      obtain ⟨c, _, hc⟩ := hqpv_eq.mp heq
      have hm_eq : mY = c := by
        calc mY = ∑ i : Fin n, w i * c := Finset.sum_congr rfl fun i _ => by
              rcases eq_or_lt_of_le (hw_nn i) with h0 | hpos
              · rw [← h0, zero_mul, zero_mul]
              · rw [hc i hpos]
          _ = c := by rw [← Finset.sum_mul, hw_sum, one_mul]
      have h0 : varY = 0 := by
        have hsum0 : ∑ i : Fin n, w i * (y i - c) ^ 2 = 0 :=
          Finset.sum_eq_zero fun i _ => by
            rcases eq_or_lt_of_le (hw_nn i) with h0 | hpos
            · rw [← h0, zero_mul]
            · rw [hc i hpos, sub_self, zero_pow two_ne_zero, mul_zero]
        have hexp : ∑ i : Fin n, w i * (y i - c) ^ 2 = varY + (c - mY) ^ 2 := by
          have h1 : ∀ i, w i * (y i - c) ^ 2 = w i * (y i) ^ 2 - 2 * c * (w i * y i) + c ^ 2 * w i :=
            fun i => by ring
          simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, mul_one]
          dsimp [varY, mY]; ring
        rw [hsum0, hm_eq, sub_self, zero_pow two_ne_zero, add_zero] at hexp; linarith
      exact hvar0 h0
    have hsq_lt : (dv * g) ^ 2 < dmax ^ 2 := by
      have h1 : dv ^ 2 * (g ^ 2 * varY) < dv ^ 2 * varYa :=
        mul_lt_mul_of_pos_left hqpv_strict (sq_pos_of_pos hdv)
      have h2 : (dv * g) ^ 2 * varY < dmax ^ 2 * varY := by linarith
      exact lt_of_mul_lt_mul_right h2 hvar_pos.le
    have hmul_lt : dv * g < dmax := by nlinarith [mul_pos hdv (by linarith : 0 < g)]
    exact (lt_div_iff₀ (by linarith : 0 < g)).mpr hmul_lt

/-! ==========================================================================
    PART 2: Exact p = 4/3 Bogomolny / SOS Identity & Vacuum-Defect Cubic Identity
    ========================================================================== -/

/-- Four times the p = 4/3 vacuum-shifted Bogomolny energy:
    4 W_Λ(D, H) = Re Tr((D + H)^4) - 2 Λ Re Tr(D H D H) + Λ (h² - h) Re Tr(D^4). -/
def fourW43 {n : ℕ} (Λ h : ℝ) (D H : Mat n) : ℝ :=
  ((D + H) ^ 4).trace.re - 2 * Λ * (D * H * D * H).trace.re +
    Λ * (h ^ 2 - h) * (D ^ 4).trace.re

/-- Bridge connecting Tr(G²) with Tr(D H D H) for G = D^(1/2) H D^(1/2). -/
lemma trace_G_sq_eq_DHDH {n : ℕ} {D H : Mat n} (hD : D.PosDef) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    ((Dhalf * H * Dhalf) * (Dhalf * H * Dhalf)).trace = (D * H * D * H).trace := by
  intro Dhalf
  have hsq : Dhalf * Dhalf = D := by
    dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
  calc ((Dhalf * H * Dhalf) * (Dhalf * H * Dhalf)).trace
      = (Dhalf * H * (Dhalf * Dhalf) * H * Dhalf).trace := by simp only [Matrix.mul_assoc]
    _ = (Dhalf * (Dhalf * H * (Dhalf * Dhalf) * H)).trace := Matrix.trace_mul_comm _ _
    _ = ((Dhalf * Dhalf) * H * (Dhalf * Dhalf) * H).trace := by simp only [Matrix.mul_assoc]
    _ = (D * H * D * H).trace := by rw [hsq]

private lemma trace_add_pow_four {n : ℕ} (A B : Mat n) :
    ((A + B) ^ 4).trace =
      (A ^ 4).trace + 4 * (A ^ 3 * B).trace + 4 * (A ^ 2 * B ^ 2).trace +
      2 * (A * B * A * B).trace + 4 * (A * B ^ 3).trace + (B ^ 4).trace := by
  have hexp := ring_add_pow_four A B
  rw [hexp]; simp only [Matrix.trace_add]
  have h1 : (A ^ 2 * B * A).trace = (A ^ 3 * B).trace := by
    rw [Matrix.trace_mul_comm (A ^ 2 * B) A]; apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have h2 : (A * B * A ^ 2).trace = (A ^ 3 * B).trace := by
    rw [Matrix.trace_mul_comm (A * B) (A ^ 2)]; apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have h3 : (B * A ^ 3).trace = (A ^ 3 * B).trace := Matrix.trace_mul_comm _ _
  have h4 : (A * B ^ 2 * A).trace = (A ^ 2 * B ^ 2).trace := by
    rw [Matrix.trace_mul_comm (A * B ^ 2) A]; apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have h5 : (B * A ^ 2 * B).trace = (A ^ 2 * B ^ 2).trace := by
    calc (B * A ^ 2 * B).trace = (B * (B * A ^ 2)).trace := Matrix.trace_mul_comm _ _
      _ = (B ^ 2 * A ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (A ^ 2 * B ^ 2).trace := Matrix.trace_mul_comm _ _
  have h6 : (B ^ 2 * A ^ 2).trace = (A ^ 2 * B ^ 2).trace := Matrix.trace_mul_comm _ _
  have h7 : (B * A * B * A).trace = (A * B * A * B).trace := by
    rw [Matrix.trace_mul_comm (B * A * B) A]; apply tr_eq; simp only [Matrix.mul_assoc]
  have h8 : (B * A * B ^ 2).trace = (A * B ^ 3).trace := by
    calc (B * A * B ^ 2).trace = (B ^ 2 * (B * A)).trace := Matrix.trace_mul_comm _ _
      _ = (B ^ 3 * A).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = (A * B ^ 3).trace := Matrix.trace_mul_comm _ _
  have h9 : (B ^ 2 * A * B).trace = (A * B ^ 3).trace := by
    calc (B ^ 2 * A * B).trace = (B * (B ^ 2 * A)).trace := Matrix.trace_mul_comm _ _
      _ = (B ^ 3 * A).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = (A * B ^ 3).trace := Matrix.trace_mul_comm _ _
  have h10 : (B ^ 3 * A).trace = (A * B ^ 3).trace := Matrix.trace_mul_comm _ _
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]; ring

private lemma trace_re_add_pow_four {n : ℕ} (A B : Mat n) :
    ((A + B) ^ 4).trace.re =
      (A ^ 4).trace.re + 4 * (A ^ 3 * B).trace.re + 4 * (A ^ 2 * B ^ 2).trace.re +
      2 * (A * B * A * B).trace.re + 4 * (A * B ^ 3).trace.re + (B ^ 4).trace.re := by
  have h := congrArg Complex.re (trace_add_pow_four A B)
  simpa only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] using h

/-- Exact Closed-Form 3-Term Bogomolny / SOS Identity at p = 4/3 (`#15.2`, `#16`, `p1_proof.md` Thm 3.1):
    For ALL Λ ≥ 8, h ≥ 1 with (1 + h)³ = Λ h, and ALL complex PosDef matrices D, H ≻ 0:
      4 W_Λ(D, H) = ‖H² + α(DH + HD) - β D²‖_HS² + γ ‖[D, H]‖_HS² + c ‖H^(1/2)(H - h D)D^(1/2)‖_HS² ≥ 0,
    with equality if and only if H = h D. -/
theorem bogomolny_sos_identity_p43 {n : ℕ} {Λ h : ℝ} (hh : 1 ≤ h)
    (hSc : (1 + h) ^ 3 = Λ * h) {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef) :
    let β := Real.sqrt (1 + Λ * (h ^ 2 - h))
    let α := (β - h ^ 2) / (2 * h)
    let γ := Λ - 1 + α ^ 2
    let c := 4 * (1 - α)
    (0 ≤ α ∧ α < 1 ∧ 0 < γ ∧ 0 < c) ∧
    fourW43 Λ h D H =
      hsNormSq (H ^ 2 + (α : ℂ) • (D * H + H * D) - (β : ℂ) • D ^ 2) +
      γ * hsNormSq (D * H - H * D) +
      c * hsNormSq (posDefPow (1 / 2 : ℝ) hH * (H - (h : ℂ) • D) * posDefPow (1 / 2 : ℝ) hD) ∧
    0 ≤ fourW43 Λ h D H ∧
    (fourW43 Λ h D H = 0 ↔ H = (h : ℂ) • D) := by
  intro β α γ c
  have hh0 : 0 < h := by linarith
  have hΛ_ge8 : 8 ≤ Λ := by
    have h1 : (1 + h) ^ 3 - 8 * h = (h - 1) ^ 2 * (h + 5) + 4 * (h - 1) := by ring
    have h2 : 8 * h ≤ (1 + h) ^ 3 := by nlinarith
    nlinarith
  have hβ_arg : 1 + Λ * (h ^ 2 - h) = h ^ 4 + 2 * h * (h ^ 2 - 1) := by
    have h1 : Λ * (h ^ 2 - h) = (Λ * h) * (h - 1) := by ring
    rw [h1, ← hSc]; ring
  have hβ_sq : β ^ 2 = h ^ 4 + 2 * h * (h ^ 2 - 1) := by
    dsimp [β]; rw [hβ_arg]; exact Real.sq_sqrt (by nlinarith)
  have hβ_ge : h ^ 2 ≤ β := by
    dsimp [β]; rw [hβ_arg]
    calc h ^ 2 = Real.sqrt ((h ^ 2) ^ 2) := (Real.sqrt_sq (sq_nonneg h)).symm
      _ ≤ Real.sqrt (h ^ 4 + 2 * h * (h ^ 2 - 1)) := Real.sqrt_le_sqrt (by nlinarith)
  have hβ_lt : β < h ^ 2 + 2 * h := by
    dsimp [β]; rw [hβ_arg]
    calc Real.sqrt (h ^ 4 + 2 * h * (h ^ 2 - 1))
        < Real.sqrt ((h ^ 2 + 2 * h) ^ 2) := Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)
      _ = h ^ 2 + 2 * h := Real.sqrt_sq (by nlinarith)
  have hα_nn : 0 ≤ α := div_nonneg (by linarith) (by linarith)
  have hα_lt1 : α < 1 := by dsimp [α]; rw [div_lt_one (by linarith)]; linarith
  have hγ_pos : 0 < γ := by dsimp [γ]; nlinarith [sq_nonneg α]
  have hc_pos : 0 < c := by dsimp [c]; linarith
  set tD4 : ℝ := (D ^ 4).trace.re
  set tD3H : ℝ := (D ^ 3 * H).trace.re
  set tD2H2 : ℝ := (D ^ 2 * H ^ 2).trace.re
  set tDHDH : ℝ := (D * H * D * H).trace.re
  set tDH3 : ℝ := (D * H ^ 3).trace.re
  set tH4 : ℝ := (H ^ 4).trace.re
  have hDh : Dᴴ = D := hD.isHermitian.eq
  have hHh : Hᴴ = H := hH.isHermitian.eq
  -- Canonical trace reductions (right-associated and power forms)
  have htr_H2DH : (H ^ 2 * (D * H)).trace = (D * H ^ 3).trace := by
    calc (H ^ 2 * (D * H)).trace = ((H ^ 2 * D) * H).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (H * (H ^ 2 * D)).trace := Matrix.trace_mul_comm _ _
      _ = (H ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = (D * H ^ 3).trace := Matrix.trace_mul_comm _ _
  have htr_H2HD : (H ^ 2 * (H * D)).trace = (D * H ^ 3).trace := by
    calc (H ^ 2 * (H * D)).trace = (H ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = (D * H ^ 3).trace := Matrix.trace_mul_comm _ _
  have htr_DHH2 : (D * H * H ^ 2).trace = (D * H ^ 3).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have htr_HDH2 : (H * D * H ^ 2).trace = (D * H ^ 3).trace := by
    calc (H * D * H ^ 2).trace = (H ^ 2 * (H * D)).trace := Matrix.trace_mul_comm _ _
      _ = (D * H ^ 3).trace := htr_H2HD
  have htr_H2D2 : (H ^ 2 * D ^ 2).trace = (D ^ 2 * H ^ 2).trace := Matrix.trace_mul_comm _ _
  have htr_DHHD : (D * H * (H * D)).trace = (D ^ 2 * H ^ 2).trace := by
    calc (D * H * (H * D)).trace = ((D * H ^ 2) * D).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D * (D * H ^ 2)).trace := Matrix.trace_mul_comm _ _
      _ = (D ^ 2 * H ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have htr_HDDH : (H * D * (D * H)).trace = (D ^ 2 * H ^ 2).trace := by
    calc (H * D * (D * H)).trace = ((H * D ^ 2) * H).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (H * (H * D ^ 2)).trace := Matrix.trace_mul_comm _ _
      _ = (H ^ 2 * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D ^ 2 * H ^ 2).trace := Matrix.trace_mul_comm _ _
  have htr_HDHD : (H * D * (H * D)).trace = (D * H * D * H).trace := by
    calc (H * D * (H * D)).trace = ((H * D * H) * D).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = (D * (H * D * H)).trace := Matrix.trace_mul_comm _ _
      _ = (D * H * D * H).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
  have htr_DHDH2 : (D * H * (D * H)).trace = (D * H * D * H).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
  have htr_DHD2 : (D * H * D ^ 2).trace = (D ^ 3 * H).trace := by
    calc (D * H * D ^ 2).trace = (D ^ 2 * (D * H)).trace := Matrix.trace_mul_comm _ _
      _ = (D ^ 3 * H).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have htr_HDD2 : (H * D * D ^ 2).trace = (D ^ 3 * H).trace := by
    calc (H * D * D ^ 2).trace = (H * D ^ 3).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = (D ^ 3 * H).trace := Matrix.trace_mul_comm _ _
  have htr_D2DH : (D ^ 2 * (D * H)).trace = (D ^ 3 * H).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have htr_D2HD : (D ^ 2 * (H * D)).trace = (D ^ 3 * H).trace := by
    calc (D ^ 2 * (H * D)).trace = ((D ^ 2 * H) * D).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D * (D ^ 2 * H)).trace := Matrix.trace_mul_comm _ _
      _ = (D ^ 3 * H).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  -- Term 1: Z1 = H^2 + α(DH + HD) - β D^2 (Hermitian)
  let Z1 : Mat n := H ^ 2 + (α : ℂ) • (D * H + H * D) - (β : ℂ) • D ^ 2
  have hZ1h : Z1ᴴ = Z1 := by
    change (H ^ 2 + (α : ℂ) • (D * H + H * D) - (β : ℂ) • D ^ 2)ᴴ = _
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_pow, Matrix.conjTranspose_mul, hDh, hHh, add_comm (H * D)]
    simp only [Complex.star_def, Complex.conj_ofReal]; rfl
  have hT1 : hsNormSq Z1 =
      tH4 + 4 * α * tDH3 + (2 * α ^ 2 - 2 * β) * tD2H2 +
      2 * α ^ 2 * tDHDH - 4 * α * β * tD3H + β ^ 2 * tD4 := by
    unfold hsNormSq
    rw [hZ1h]
    change ((H ^ 2 + (α : ℂ) • (D * H + H * D) - (β : ℂ) • D ^ 2) *
        (H ^ 2 + (α : ℂ) • (D * H + H * D) - (β : ℂ) • D ^ 2)).trace.re = _
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_add,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      htr_H2DH, htr_H2HD, htr_DHH2, htr_HDH2, htr_H2D2, htr_DHHD, htr_HDDH, htr_HDHD, htr_DHDH2,
      htr_DHD2, htr_HDD2, htr_D2DH, htr_D2HD,
      show H ^ 2 * H ^ 2 = H ^ 4 by simp only [mat_pow_two, mat_pow_four, Matrix.mul_assoc],
      show D ^ 2 * D ^ 2 = D ^ 4 by simp only [mat_pow_two, mat_pow_four, Matrix.mul_assoc],
      Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    dsimp [tH4, tDH3, tD2H2, tDHDH, tD3H, tD4]; ring
  -- Term 2: [D, H] = D*H - H*D
  have hT2 : hsNormSq (D * H - H * D) = 2 * tD2H2 - 2 * tDHDH := by
    unfold hsNormSq
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDh, hHh]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
      htr_HDDH, htr_HDHD, htr_DHHD, htr_DHDH2, Complex.sub_re]
    dsimp [tD2H2, tDHDH]; ring
  -- Term 3: H^(1/2) (H - h D) D^(1/2)
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let Hhalf := posDefPow (1 / 2 : ℝ) hH
  have hDhalf_sq : Dhalf * Dhalf = D := by
    dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
  have hHhalf_sq : Hhalf * Hhalf = H := by
    dsimp [Hhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hH
  have hT3 : hsNormSq (Hhalf * (H - (h : ℂ) • D) * Dhalf) =
      tDH3 - 2 * h * tD2H2 + h ^ 2 * tD3H := by
    unfold hsNormSq
    have hDh2 : Dhalfᴴ = Dhalf := (posDefPow_posDef (1 / 2) hD).isHermitian.eq
    have hHh2 : Hhalfᴴ = Hhalf := (posDefPow_posDef (1 / 2) hH).isHermitian.eq
    have hZ3h : (Hhalf * (H - (h : ℂ) • D) * Dhalf)ᴴ = Dhalf * (H - (h : ℂ) • D) * Hhalf := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Complex.star_def, Complex.conj_ofReal, hDh, hHh, hDh2, hHh2, Matrix.mul_assoc]
    rw [hZ3h]
    have hcyc : (Dhalf * (H - (h : ℂ) • D) * Hhalf * (Hhalf * (H - (h : ℂ) • D) * Dhalf)).trace =
        ((H - (h : ℂ) • D) * H * (H - (h : ℂ) • D) * D).trace := by
      calc (Dhalf * (H - (h : ℂ) • D) * Hhalf * (Hhalf * (H - (h : ℂ) • D) * Dhalf)).trace
          = (Dhalf * (H - (h : ℂ) • D) * (Hhalf * Hhalf) * (H - (h : ℂ) • D) * Dhalf).trace := by
              simp only [Matrix.mul_assoc]
        _ = (Dhalf * (Dhalf * (H - (h : ℂ) • D) * H * (H - (h : ℂ) • D))).trace := by
              rw [hHhalf_sq, Matrix.trace_mul_comm]
        _ = ((Dhalf * Dhalf) * ((H - (h : ℂ) • D) * H * (H - (h : ℂ) • D))).trace := by
              simp only [Matrix.mul_assoc]
        _ = ((H - (h : ℂ) • D) * H * (H - (h : ℂ) • D) * D).trace := by
              rw [hDhalf_sq, Matrix.trace_mul_comm]
    rw [hcyc]
    have htr_H3D : (H * H * H * D).trace = (D * H ^ 3).trace := by
      calc (H * H * H * D).trace = (H ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_three, Matrix.mul_assoc]
        _ = (D * H ^ 3).trace := Matrix.trace_mul_comm _ _
    have htr_DH2D : (D * H * H * D).trace = (D ^ 2 * H ^ 2).trace := by
      calc (D * H * H * D).trace = (D * (D * H * H)).trace := Matrix.trace_mul_comm _ _
        _ = (D ^ 2 * H ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
    have htr_H2D2' : (H * H * D * D).trace = (D ^ 2 * H ^ 2).trace := by
      calc (H * H * D * D).trace = (H ^ 2 * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D ^ 2 * H ^ 2).trace := Matrix.trace_mul_comm _ _
    have htr_DHD2' : (D * H * D * D).trace = (D ^ 3 * H).trace := by
      calc (D * H * D * D).trace = (D * H * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D ^ 3 * H).trace := htr_DHD2
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      htr_H3D, htr_DH2D, htr_H2D2', htr_DHD2',
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    dsimp [tDH3, tD2H2, tD3H]; ring
  have hLHS : fourW43 Λ h D H =
      (1 + Λ * (h ^ 2 - h)) * tD4 + 4 * tD3H + 4 * tD2H2 +
      (2 - 2 * Λ) * tDHDH + 4 * tDH3 + tH4 := by
    unfold fourW43
    rw [trace_re_add_pow_four D H]
    dsimp [tD4, tD3H, tD2H2, tDHDH, tDH3, tH4]; ring
  have hcoeff_D4 : β ^ 2 = 1 + Λ * (h ^ 2 - h) := by rw [hβ_sq, hβ_arg]
  have hcoeff_D3H : -4 * α * β + c * h ^ 2 = 4 := by
    dsimp [α, c]
    have h1 : -4 * ((β - h ^ 2) / (2 * h)) * β + 4 * (1 - (β - h ^ 2) / (2 * h)) * h ^ 2 =
        4 * h ^ 2 - 2 * (β ^ 2 - h ^ 4) / h := by field_simp [hh0.ne']; ring
    rw [h1, hβ_sq]; field_simp [hh0.ne']; ring
  have hcoeff_D2H2 : (2 * α ^ 2 - 2 * β) + 2 * γ - 2 * h * c = 4 := by
    dsimp [γ, c, α]
    have hΛ_eq : Λ = (1 + h) ^ 3 / h := by field_simp [hh0.ne']; linarith
    have h1 : (2 * ((β - h ^ 2) / (2 * h)) ^ 2 - 2 * β) +
        2 * (Λ - 1 + ((β - h ^ 2) / (2 * h)) ^ 2) - 2 * h * (4 * (1 - (β - h ^ 2) / (2 * h))) =
        (β ^ 2 - h ^ 4 + 2 * h ^ 4) / h ^ 2 + 2 * Λ - 2 - 8 * h - 4 * h ^ 2 := by
      field_simp [hh0.ne']; ring
    rw [h1, hβ_sq, hΛ_eq]; field_simp [hh0.ne']; ring
  have hcoeff_DHDH : 2 * α ^ 2 - 2 * γ = 2 - 2 * Λ := by dsimp [γ]; ring
  have hcoeff_DH3 : 4 * α + c = 4 := by dsimp [c]; ring
  have hId : fourW43 Λ h D H =
      hsNormSq Z1 + γ * hsNormSq (D * H - H * D) +
      c * hsNormSq (Hhalf * (H - (h : ℂ) • D) * Dhalf) := by
    rw [hLHS, hT1, hT2, hT3]
    linear_combination -tD4 * hcoeff_D4 - tD3H * hcoeff_D3H - tD2H2 * hcoeff_D2H2 -
      tDHDH * hcoeff_DHDH - tDH3 * hcoeff_DH3
  have hnn : 0 ≤ fourW43 Λ h D H := by
    rw [hId]
    exact add_nonneg (add_nonneg (hsNormSq_nonneg _) (mul_nonneg hγ_pos.le (hsNormSq_nonneg _)))
      (mul_nonneg hc_pos.le (hsNormSq_nonneg _))
  refine ⟨⟨hα_nn, hα_lt1, hγ_pos, hc_pos⟩, hId, hnn, ?_⟩
  constructor
  · intro hzero
    rw [hId] at hzero
    have h3zero : hsNormSq (Hhalf * (H - (h : ℂ) • D) * Dhalf) = 0 := by
      have h1 := hsNormSq_nonneg Z1
      have h2 := mul_nonneg hγ_pos.le (hsNormSq_nonneg (D * H - H * D))
      have h3 := hsNormSq_nonneg (Hhalf * (H - (h : ℂ) • D) * Dhalf)
      nlinarith
    have hmat0 : Hhalf * (H - (h : ℂ) • D) * Dhalf = 0 := (hsNormSq_eq_zero_iff _).mp h3zero
    have hmid : Hhalf * (H - (h : ℂ) • D) = 0 :=
      posDef_mul_right_cancel (posDefPow_posDef (1 / 2) hD) (by rw [Matrix.zero_mul]; exact hmat0)
    have hsub0 : H - (h : ℂ) • D = 0 :=
      posDef_mul_left_cancel (posDefPow_posDef (1 / 2) hH) (by rw [Matrix.mul_zero]; exact hmid)
    exact sub_eq_zero.mp hsub0
  · intro hHD
    dsimp only [Z1] at hId
    rw [hId, hHD]
    have hZ3 : Hhalf * ((h : ℂ) • D - (h : ℂ) • D) * Dhalf = 0 := by simp
    have hZ2 : D * ((h : ℂ) • D) - (h : ℂ) • D * D = 0 := by
      rw [Matrix.mul_smul, Matrix.smul_mul, sub_self]
    have hZ1_0 : ((h : ℂ) • D) ^ 2 + (α : ℂ) • (D * ((h : ℂ) • D) + (h : ℂ) • D * D) -
        (β : ℂ) • D ^ 2 = 0 := by
      have hsq : ((h : ℂ) • D) ^ 2 = ((h ^ 2 : ℝ) : ℂ) • D ^ 2 := by
        rw [mat_pow_two ((h : ℂ) • D), mat_pow_two D, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        push_cast; rw [sq]
      have hmid : D * ((h : ℂ) • D) + (h : ℂ) • D * D = ((2 * h : ℝ) : ℂ) • D ^ 2 := by
        rw [Matrix.mul_smul, Matrix.smul_mul, ← add_smul, ← mat_pow_two D]
        congr 1; push_cast; ring
      rw [hsq, hmid, smul_smul, ← add_smul, ← sub_smul]
      have hcoef0 : ((h ^ 2 : ℝ) : ℂ) + (α : ℂ) * ((2 * h : ℝ) : ℂ) - (β : ℂ) = 0 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_sub, Complex.ofReal_eq_zero]
        dsimp [α]; field_simp [hh0.ne']; ring
      rw [hcoef0, zero_smul]
    rw [hZ1_0, hZ2, hZ3, (hsNormSq_eq_zero_iff 0).mpr rfl]; ring

/-- 1-Line Vacuum-Defect Cubic Identity at p = 4/3 (`#21`, `p1_proof.md` Thm 4.3):
    For any solution (D, H) of (D + H)³ = Λ D H D with (1 + h)³ = Λ h, setting Y := h D - H:
      4 W_Λ(D, H) = 2(1 + h) Re Tr(D Y³) - Re Tr(Y⁴) = Re Tr(Y³ ((2 + h) D + H)),
    and whenever h > 0, D ≻ 0, H ≻ 0, and Y ⪰ 0, 4 W_Λ(D, H) ≥ 0 immediately! -/
theorem vacuum_defect_cubic_identity_p43 {n : ℕ} {Λ h : ℝ}
    (hSc : (1 + h) ^ 3 = Λ * h) {D H : Mat n}
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D)) :
    let Y := (h : ℂ) • D - H
    fourW43 Λ h D H = 2 * (1 + h) * (D * Y ^ 3).trace.re - (Y ^ 4).trace.re ∧
    fourW43 Λ h D H = (Y ^ 3 * (((2 + h : ℝ) : ℂ) • D + H)).trace.re ∧
    (0 < h → D.PosDef → H.PosDef → Y.PosSemidef → 0 ≤ fourW43 Λ h D H) := by
  intro Y
  set t : ℝ := 1 + h
  have hH_eq : H = (h : ℂ) • D - Y := by dsimp [Y]; abel
  have hDH_eq : D + H = (t : ℂ) • D - Y := by
    rw [hH_eq]; dsimp [t]; rw [add_smul, one_smul]; abel
  have hY_eq0 : (Y * ((D + H) ^ 3 - (Λ : ℂ) • (D * H * D))).trace.re = 0 := by
    rw [hEq, sub_self, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  have hW_exp : fourW43 Λ h D H =
      4 * t ^ 2 * (D ^ 2 * Y ^ 2).trace.re + (2 * t ^ 2 - 2 * Λ) * (D * Y * D * Y).trace.re -
      4 * t * (D * Y ^ 3).trace.re + (Y ^ 4).trace.re := by
    unfold fourW43
    rw [hDH_eq, hH_eq]
    have h1 : (((t : ℂ) • D - Y) ^ 4).trace.re =
        t ^ 4 * (D ^ 4).trace.re - 4 * t ^ 3 * (D ^ 3 * Y).trace.re +
        4 * t ^ 2 * (D ^ 2 * Y ^ 2).trace.re + 2 * t ^ 2 * (D * Y * D * Y).trace.re -
        4 * t * (D * Y ^ 3).trace.re + (Y ^ 4).trace.re := by
      have hsub : (t : ℂ) • D - Y = (t : ℂ) • D + (-Y) := sub_eq_add_neg _ _
      rw [hsub, trace_re_add_pow_four]
      have hp4 : ((t : ℂ) • D) ^ 4 = ((t ^ 4 : ℝ) : ℂ) • D ^ 4 := by
        simp only [mat_pow_four, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        push_cast; ring_nf
      have hp3 : ((t : ℂ) • D) ^ 3 * (-Y) = -(((t ^ 3 : ℝ) : ℂ) • (D ^ 3 * Y)) := by
        simp only [mat_pow_three, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_neg]
        push_cast; ring_nf
      have hp2 : ((t : ℂ) • D) ^ 2 * (-Y) ^ 2 = ((t ^ 2 : ℝ) : ℂ) • (D ^ 2 * Y ^ 2) := by
        simp only [sq, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
        push_cast; ring_nf
      have hpal : ((t : ℂ) • D) * (-Y) * ((t : ℂ) • D) * (-Y) = ((t ^ 2 : ℝ) : ℂ) • (D * Y * D * Y) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_neg, smul_smul]
        push_cast; ring_nf
      have hp1 : ((t : ℂ) • D) * (-Y) ^ 3 = -((t : ℂ) • (D * Y ^ 3)) := by
        simp only [mat_pow_three, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      have hp0 : (-Y) ^ 4 = Y ^ 4 := by
        simp only [mat_pow_four, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      rw [hp4, hp3, hp2, hpal, hp1, hp0]
      simp only [Matrix.trace_neg, Complex.neg_re, trace_re_smul_real]
      ring
    have h2 : (D * ((h : ℂ) • D - Y) * D * ((h : ℂ) • D - Y)).trace.re =
        h ^ 2 * (D ^ 4).trace.re - 2 * h * (D ^ 3 * Y).trace.re + (D * Y * D * Y).trace.re := by
      have hD4 : (D * D * D * D).trace = (D ^ 4).trace := by apply tr_eq; simp only [mat_pow_four, Matrix.mul_assoc]
      have hD3Y : (D * D * D * Y).trace = (D ^ 3 * Y).trace := by apply tr_eq; simp only [mat_pow_three, Matrix.mul_assoc]
      have hDYD2 : (D * Y * D * D).trace = (D ^ 3 * Y).trace := by
        calc (D * Y * D * D).trace = ((D * Y) * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
          _ = (D ^ 2 * (D * Y)).trace := Matrix.trace_mul_comm _ _
          _ = (D ^ 3 * Y).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hD4, hD3Y, hDYD2,
        Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    rw [h1, h2]
    have ht3 : t ^ 3 = Λ * h := hSc
    have hc4 : t ^ 4 - 2 * Λ * h ^ 2 + Λ * (h ^ 2 - h) = 0 := by
      calc t ^ 4 - 2 * Λ * h ^ 2 + Λ * (h ^ 2 - h) = t * t ^ 3 - Λ * h * (h + 1) := by ring
        _ = t * (Λ * h) - Λ * h * t := by rw [ht3]; dsimp [t]; ring
        _ = 0 := by ring
    have hc3 : -4 * t ^ 3 + 4 * Λ * h = 0 := by linarith
    linear_combination (D ^ 4).trace.re * hc4 + (D ^ 3 * Y).trace.re * hc3
  have hE_exp : (Y * ((D + H) ^ 3 - (Λ : ℂ) • (D * H * D))).trace.re =
      -2 * t ^ 2 * (D ^ 2 * Y ^ 2).trace.re + (Λ - t ^ 2) * (D * Y * D * Y).trace.re +
      3 * t * (D * Y ^ 3).trace.re - (Y ^ 4).trace.re := by
    rw [hDH_eq, hH_eq]
    have hcube : ((t : ℂ) • D - Y) ^ 3 = ((t : ℂ) • D - Y) * ((t : ℂ) • D - Y) * ((t : ℂ) • D - Y) := by
      exact mat_pow_three _
    rw [hcube]
    have hYD3 : (Y * (D * D * D)).trace = (D ^ 3 * Y).trace := by
      calc (Y * (D * D * D)).trace = (Y * D ^ 3).trace := by apply tr_eq; simp only [mat_pow_three, Matrix.mul_assoc]
        _ = (D ^ 3 * Y).trace := Matrix.trace_mul_comm _ _
    have hYDDY : (Y * (D * D * Y)).trace = (D ^ 2 * Y ^ 2).trace := by
      calc (Y * (D * D * Y)).trace = ((Y * D ^ 2) * Y).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (Y * (Y * D ^ 2)).trace := Matrix.trace_mul_comm _ _
        _ = (Y ^ 2 * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D ^ 2 * Y ^ 2).trace := Matrix.trace_mul_comm _ _
    have hYYDD : (Y * (Y * D * D)).trace = (D ^ 2 * Y ^ 2).trace := by
      calc (Y * (Y * D * D)).trace = (Y ^ 2 * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D ^ 2 * Y ^ 2).trace := Matrix.trace_mul_comm _ _
    have hYDYD : (Y * (D * Y * D)).trace = (D * Y * D * Y).trace := by
      calc (Y * (D * Y * D)).trace = ((Y * D * Y) * D).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
        _ = (D * (Y * D * Y)).trace := Matrix.trace_mul_comm _ _
        _ = (D * Y * D * Y).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
    have hYDYY : (Y * (D * Y * Y)).trace = (D * Y ^ 3).trace := by
      calc (Y * (D * Y * Y)).trace = ((Y * D) * Y ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (Y ^ 2 * (Y * D)).trace := Matrix.trace_mul_comm _ _
        _ = (Y ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
        _ = (D * Y ^ 3).trace := Matrix.trace_mul_comm _ _
    have hYYDY : (Y * (Y * D * Y)).trace = (D * Y ^ 3).trace := by
      calc (Y * (Y * D * Y)).trace = ((Y ^ 2 * D) * Y).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (Y * (Y ^ 2 * D)).trace := Matrix.trace_mul_comm _ _
        _ = (Y ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
        _ = (D * Y ^ 3).trace := Matrix.trace_mul_comm _ _
    have hYYYD : (Y * (Y * Y * D)).trace = (D * Y ^ 3).trace := by
      calc (Y * (Y * Y * D)).trace = (Y ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_three, Matrix.mul_assoc]
        _ = (D * Y ^ 3).trace := Matrix.trace_mul_comm _ _
    have hY4 : (Y * (Y * Y * Y)).trace = (Y ^ 4).trace := by apply tr_eq; simp only [mat_pow_four, Matrix.mul_assoc]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
      hYD3, hYDDY, hYYDD, hYDYD, hYDYY, hYYDY, hYYYD, hY4,
      ← Complex.ofReal_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have ht3 : t ^ 3 - Λ * h = 0 := sub_eq_zero.mpr hSc
    linear_combination (D ^ 3 * Y).trace.re * ht3
  have hId1 : fourW43 Λ h D H = 2 * (1 + h) * (D * Y ^ 3).trace.re - (Y ^ 4).trace.re := by
    rw [hY_eq0] at hE_exp; dsimp [t] at hW_exp hE_exp; linarith
  have hId2 : fourW43 Λ h D H = (Y ^ 3 * (((2 + h : ℝ) : ℂ) • D + H)).trace.re := by
    rw [hId1]
    have hsum : (((2 + h : ℝ) : ℂ) • D + H) = ((2 * (1 + h) : ℝ) : ℂ) • D - Y := by
      rw [hH_eq, ← add_sub_assoc, ← add_smul]
      have hsc : ((2 + h : ℝ) : ℂ) + (h : ℂ) = ((2 * (1 + h) : ℝ) : ℂ) := by push_cast; ring
      rw [hsc]
    rw [hsum, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Complex.sub_re,
      trace_re_smul_real, Matrix.trace_mul_comm (Y ^ 3) D, show Y ^ 3 * Y = Y ^ 4 by simp only [mat_pow_three, mat_pow_four, Matrix.mul_assoc]]
  refine ⟨hId1, hId2, fun hh0 hD hH hY => ?_⟩
  rw [hId2]
  have hB : ((((2 + h : ℝ) : ℂ) • D + H)).PosSemidef := by
    have h1 : (((2 + h : ℝ) : ℂ) • D) = (2 + h : ℝ) • D := by ext i j; simp [Complex.real_smul]
    rw [h1]
    exact (hD.posSemidef.smul (by linarith)).add hH.posSemidef
  exact trace_re_posSemidef_mul_nonneg (posSemidef_pow_mul_self_posSemidef hY) hB

/-! ==========================================================================
    PART 3: Exact Closed-Form 4-Term Bogomolny / SOS Identity at p = 3/2
    ========================================================================== -/

/-- Three times the p = 3/2 vacuum-shifted Bogomolny energy in root coordinates H = M D M:
    3 W_Λ(D, M D M) = Re Tr((D + M D M)³) - 2 Λ Re Tr((D M)³) + Λ (m³ - m) Re Tr(D³). -/
def threeW32 {n : ℕ} (Λ m : ℝ) (D M : Mat n) : ℝ :=
  ((D + M * D * M) ^ 3).trace.re - 2 * Λ * ((D * M) ^ 3).trace.re +
    Λ * (m ^ 3 - m) * (D ^ 3).trace.re

/-- Bridge connecting Tr(G^(3/2)) = Tr((D^(1/2) M D^(1/2))³) with Tr((D M)³). -/
lemma trace_G32_eq_DM_cube {n : ℕ} {D M : Mat n} (hD : D.PosDef) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    ((Dhalf * M * Dhalf) ^ 3).trace = ((D * M) ^ 3).trace := by
  intro Dhalf
  have hsq : Dhalf * Dhalf = D := by
    dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
  calc ((Dhalf * M * Dhalf) ^ 3).trace
      = (Dhalf * M * (Dhalf * Dhalf) * M * (Dhalf * Dhalf) * M * Dhalf).trace := by
          simp only [mat_pow_three, Matrix.mul_assoc]
    _ = (Dhalf * (Dhalf * M * D * M * D * M)).trace := by
          rw [hsq, Matrix.trace_mul_comm]
    _ = ((Dhalf * Dhalf) * M * D * M * D * M).trace := by simp only [Matrix.mul_assoc]
    _ = ((D * M) ^ 3).trace := by
          rw [hsq]; simp only [mat_pow_three, Matrix.mul_assoc]

/-- Exact Closed-Form 4-Term Bogomolny / SOS Identity at p = 3/2 (`#31`, `ver_audit.md` §11.1):
    For ALL Λ ≥ 4, m ≥ 1 with (1 + m²)² = Λ m, and ALL complex PosDef D, M ≻ 0:
      3 W_Λ(D, M D M)
        = (1 - 1/m²) ‖(m² D - M D M) D^(1/2)‖_HS²
        + ‖W₁ - (m/2) W₂ + (m/2) W₃‖_HS²
        + (3 m² / 4) ‖W₂ - W₃‖_HS²
        + (2 + 1/m²) ‖W₂‖_HS² ≥ 0,
    where W₁ = (m³ D - M D M²) D^(1/2), W₂ = (m D M - M D M) D^(1/2), W₃ = (m M D - D M²) D^(1/2),
    with equality if and only if M = m I. -/
theorem bogomolny_sos_identity_p32 {n : ℕ} {Λ m : ℝ} (hm : 1 ≤ m)
    (hSc : (1 + m ^ 2) ^ 2 = Λ * m) {D M : Mat n} (hD : D.PosDef) (hM : M.PosDef) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let T1 := (((m ^ 2 : ℝ) : ℂ) • D - M * D * M) * Dhalf
    let W1 := (((m ^ 3 : ℝ) : ℂ) • D - M * D * M ^ 2) * Dhalf
    let W2 := ((m : ℂ) • (D * M) - M * D * M) * Dhalf
    let W3 := ((m : ℂ) • (M * D) - D * M ^ 2) * Dhalf
    (0 ≤ 1 - 1 / m ^ 2 ∧ 0 < 3 * m ^ 2 / 4 ∧ 0 < 2 + 1 / m ^ 2) ∧
    threeW32 Λ m D M =
      (1 - 1 / m ^ 2) * hsNormSq T1 +
      hsNormSq (W1 - ((m / 2 : ℝ) : ℂ) • W2 + ((m / 2 : ℝ) : ℂ) • W3) +
      (3 * m ^ 2 / 4) * hsNormSq (W2 - W3) +
      (2 + 1 / m ^ 2) * hsNormSq W2 ∧
    0 ≤ threeW32 Λ m D M ∧
    (threeW32 Λ m D M = 0 ↔ M = (m : ℂ) • (1 : Mat n)) := by
  intro Dhalf T1 W1 W2 W3
  have hm0 : 0 < m := by linarith
  have hm2_ge1 : 1 ≤ m ^ 2 := by nlinarith
  have hc1_nn : 0 ≤ 1 - 1 / m ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hm2_ge1
  have hc3_pos : 0 < 3 * m ^ 2 / 4 := by positivity
  have hc4_pos : 0 < 2 + 1 / m ^ 2 := by positivity
  have hpol : hsNormSq (W1 - ((m / 2 : ℝ) : ℂ) • W2 + ((m / 2 : ℝ) : ℂ) • W3) +
      (3 * m ^ 2 / 4) * hsNormSq (W2 - W3) =
      hsNormSq W1 - m * hsInner W1 (W2 - W3) + m ^ 2 * hsNormSq (W2 - W3) := by
    have hrewrite : W1 - ((m / 2 : ℝ) : ℂ) • W2 + ((m / 2 : ℝ) : ℂ) • W3 =
        W1 - ((m / 2 : ℝ) : ℂ) • (W2 - W3) := by rw [smul_sub]; abel
    rw [hrewrite, hsNormSq_sub, hsInner_smul_right_real, hsNormSq_smul_real]; ring
  have hDhalf_h : Dhalfᴴ = Dhalf := (posDefPow_posDef (1 / 2) hD).isHermitian.eq
  have hDhalf_sq : Dhalf * Dhalf = D := by
    dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
  have hDh : Dᴴ = D := hD.isHermitian.eq
  have hMh : Mᴴ = M := hM.isHermitian.eq
  have hInD : ∀ A B : Mat n, hsInner (A * Dhalf) (B * Dhalf) = (Aᴴ * B * D).trace.re := fun A B => by
    unfold hsInner
    rw [Matrix.conjTranspose_mul, hDhalf_h]
    calc (Dhalf * Aᴴ * (B * Dhalf)).trace.re
        = ((Dhalf * Aᴴ * B) * Dhalf).trace.re := by simp only [Matrix.mul_assoc]
      _ = (Dhalf * (Dhalf * Aᴴ * B)).trace.re := trace_re_mul_comm _ _
      _ = ((Dhalf * Dhalf) * (Aᴴ * B)).trace.re := by simp only [Matrix.mul_assoc]
      _ = (Aᴴ * B * D).trace.re := by rw [hDhalf_sq, trace_re_mul_comm]
  have hNormD : ∀ A : Mat n, hsNormSq (A * Dhalf) = (Aᴴ * A * D).trace.re := fun A => hInD A A
  -- Canonical 8 real trace monomials
  set cDDD : ℝ := (D ^ 3).trace.re
  set cDDDMM : ℝ := (D ^ 3 * M ^ 2).trace.re
  set cDDMDM : ℝ := (D ^ 2 * M * D * M).trace.re
  set cDDMDMM : ℝ := (D ^ 2 * M * D * M ^ 2).trace.re
  set cDDMMDMM : ℝ := (D ^ 2 * M ^ 2 * D * M ^ 2).trace.re
  set cDMDMDM : ℝ := ((D * M) ^ 3).trace.re
  set cDMDMDMM : ℝ := (D * M * D * M * D * M ^ 2).trace.re
  set cDMMDMMDMM : ℝ := ((M * D * M) ^ 3).trace.re
  -- Helper cyclic + adjoint trace-re equalities (using noncomm_ring for associativity/powers!)
  have r_D3 : (D * D * D).trace.re = cDDD := by dsimp [cDDD]; apply tr_re_eq; simp only [mat_pow_three, Matrix.mul_assoc]
  have r_DMDMDM : (D * M * D * M * D * M).trace.re = cDMDMDM := by dsimp [cDMDMDM]; apply tr_re_eq; simp only [mat_pow_three, Matrix.mul_assoc]
  have r_MDMDMD : (M * D * M * D * M * D).trace.re = cDMDMDM := by
    rw [trace_re_mul_comm (M * D * M * D * M) D]; dsimp [cDMDMDM]; apply tr_re_eq; simp only [mat_pow_three, Matrix.mul_assoc]
  have r_DDMDM : (D * D * M * D * M).trace.re = cDDMDM := by dsimp [cDDMDM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_MDMD2 : (M * D * M * D * D).trace.re = cDDMDM := by
    calc (M * D * M * D * D).trace.re = ((M * D * M) * D ^ 2).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D ^ 2 * (M * D * M)).trace.re := trace_re_mul_comm _ _
      _ = cDDMDM := by dsimp [cDDMDM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_DMDMD : (D * M * D * M * D).trace.re = cDDMDM := by
    rw [trace_re_mul_comm (D * M * D * M) D]; dsimp [cDDMDM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_MD2MD : (M * D * D * M * D).trace.re = cDDMDM := by
    calc (M * D * D * M * D).trace.re = (D * (M * D * D * M)).trace.re := trace_re_mul_comm _ _
      _ = ((D * M * D ^ 2) * M).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (M * (D * M * D ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = (M * D * M * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = cDDMDM := r_MDMD2
  have r_DM2D2 : (D * M ^ 2 * D * D).trace.re = cDDDMM := by
    calc (D * M ^ 2 * D * D).trace.re = ((D * M ^ 2) * D ^ 2).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D ^ 2 * (D * M ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = cDDDMM := by dsimp [cDDDMM]; apply tr_re_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have r_M2D3 : (M ^ 2 * D * D * D).trace.re = cDDDMM := by
    calc (M ^ 2 * D * D * D).trace.re = (M ^ 2 * D ^ 3).trace.re := by apply tr_re_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = cDDDMM := trace_re_mul_comm _ _
  have r_D2M2D : (D * D * M ^ 2 * D).trace.re = cDDDMM := by
    rw [trace_re_mul_comm (D * D * M ^ 2) D]; dsimp [cDDDMM]; apply tr_re_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
  have r_MD3M : (M * D * D * D * M).trace.re = cDDDMM := by
    calc (M * D * D * D * M).trace.re = (M * (M * D ^ 3)).trace.re := by
            rw [trace_re_mul_comm (M * D * D * D) M]; apply tr_re_eq; simp only [mat_pow_three, Matrix.mul_assoc]
      _ = (M ^ 2 * D ^ 3).trace.re := by apply tr_re_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      _ = cDDDMM := trace_re_mul_comm _ _
  have r_MDM2D2 : (M * D * M ^ 2 * D * D).trace.re = cDDMDMM := by
    calc (M * D * M ^ 2 * D * D).trace.re = ((M * D * M ^ 2) * D ^ 2).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D ^ 2 * (M * D * M ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = cDDMDMM := by dsimp [cDDMDMM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_M2DMD2 : (M ^ 2 * D * M * D * D).trace.re = cDDMDMM := by
    calc (M ^ 2 * D * M * D * D).trace.re = ((M ^ 2 * D * M * D ^ 2)ᴴ).trace.re := by
            rw [trace_re_conjTranspose]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D ^ 2 * M * D * M ^ 2).trace.re := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hDh, hMh]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_DMDM2D : (D * M * D * M ^ 2 * D).trace.re = cDDMDMM := by
    rw [trace_re_mul_comm (D * M * D * M ^ 2) D]; dsimp [cDDMDMM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_DM2DMD : (D * M ^ 2 * D * M * D).trace.re = cDDMDMM := by
    calc (D * M ^ 2 * D * M * D).trace.re = ((D * M ^ 2 * D * M * D)ᴴ).trace.re := (trace_re_conjTranspose _).symm
      _ = (D * M * D * M ^ 2 * D).trace.re := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hDh, hMh]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = cDDMDMM := r_DMDM2D
  have r_M2D2M2D : (M ^ 2 * D * D * M ^ 2 * D).trace.re = cDDMMDMM := by
    calc (M ^ 2 * D * D * M ^ 2 * D).trace.re = ((M ^ 2 * D ^ 2) * (M ^ 2 * D)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((M ^ 2 * D) * (M ^ 2 * D ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = ((M ^ 2 * D * M ^ 2) * D ^ 2).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = (D ^ 2 * (M ^ 2 * D * M ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = cDDMMDMM := by dsimp [cDDMMDMM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_MDMM_D : (M * D * M * (M * D * M) * D).trace.re = cDMDMDMM := by
    calc (M * D * M * (M * D * M) * D).trace.re
        = ((M * D * M ^ 2 * D) * (M * D)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((M * D) * (M * D * M ^ 2 * D)).trace.re := trace_re_mul_comm _ _
      _ = ((M * D * M * D * M ^ 2 * D)ᴴ).trace.re := by
            rw [trace_re_conjTranspose]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((D * M ^ 2) * (D * M * D * M)).trace.re := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hDh, hMh]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((D * M * D * M) * (D * M ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = cDMDMDMM := by dsimp [cDMDMDMM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_M2DMDMD : (M ^ 2 * D * M * D * M * D).trace.re = cDMDMDMM := by
    calc (M ^ 2 * D * M * D * M * D).trace.re = (M ^ 2 * (D * M * D * M * D)).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
      _ = ((D * M * D * M * D) * M ^ 2).trace.re := trace_re_mul_comm _ _
      _ = cDMDMDMM := rfl
  have r_MDM_M2D : (M * D * M * D * M ^ 2 * D).trace.re = cDMDMDMM := by
    calc (M * D * M * D * M ^ 2 * D).trace.re = ((M * D * M * D * M ^ 2 * D)ᴴ).trace.re :=
            (trace_re_conjTranspose _).symm
      _ = ((D * M ^ 2) * (D * M * D * M)).trace.re := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hDh, hMh]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((D * M * D * M) * (D * M ^ 2)).trace.re := trace_re_mul_comm _ _
      _ = cDMDMDMM := by dsimp [cDMDMDMM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  have r_M2D2MDM : (M ^ 2 * D * M * (M * D * M ^ 2) * D).trace.re = cDMMDMMDMM := by
    calc (M ^ 2 * D * M * (M * D * M ^ 2) * D).trace.re
        = (M * (M * D * M * M * D * M * M * D)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((M * D * M * M * D * M * M * D) * M).trace.re := trace_re_mul_comm _ _
      _ = cDMMDMMDMM := by dsimp [cDMMDMMDMM]; apply tr_re_eq; simp only [mat_pow_three, Matrix.mul_assoc]
  -- Cancellation of the M-degree-5 conjugates in ⟨W1, W2 - W3⟩!
  have r_deg5_cancel : (M ^ 2 * D * M * (D * M ^ 2) * D).trace.re =
      (M ^ 2 * D * M * (M * D * M) * D).trace.re := by
    calc (M ^ 2 * D * M * (D * M ^ 2) * D).trace.re
        = ((M ^ 2 * D * M * D * M ^ 2 * D)ᴴ).trace.re := by
            rw [trace_re_conjTranspose]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((D * M ^ 2 * D) * (M * D * M ^ 2)).trace.re := by
            simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hDh, hMh]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((M * D * M ^ 2) * (D * M ^ 2 * D)).trace.re := trace_re_mul_comm _ _
      _ = ((M * D * M) * (M * D * M ^ 2 * D)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      _ = ((M * D * M ^ 2 * D) * (M * D * M)).trace.re := trace_re_mul_comm _ _
      _ = (M ^ 2 * D * M * (M * D * M) * D).trace.re := by
            calc ((M * D * M ^ 2 * D) * (M * D * M)).trace.re
                = ((M * D) * (M ^ 2 * D * M * D * M)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
              _ = ((M ^ 2 * D * M * D * M) * (M * D)).trace.re := trace_re_mul_comm _ _
              _ = ((M ^ 2 * D * M * D * M ^ 2 * D)ᴴ).trace.re := by
                    rw [trace_re_conjTranspose]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
              _ = ((D * M ^ 2) * (D * M * D * M ^ 2)).trace.re := by
                    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hDh, hMh]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
              _ = ((D * M * D * M ^ 2) * (D * M ^ 2)).trace.re := trace_re_mul_comm _ _
              _ = ((D * M) * (D * M ^ 2 * D * M ^ 2)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
              _ = ((D * M ^ 2 * D * M ^ 2) * (D * M)).trace.re := trace_re_mul_comm _ _
              _ = (M ^ 2 * D * M * (M * D * M) * D).trace.re := by
                    calc ((D * M ^ 2 * D * M ^ 2) * (D * M)).trace.re
                        = (D * (M ^ 2 * D * M ^ 2 * D * M)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
                      _ = ((M ^ 2 * D * M ^ 2 * D * M) * D).trace.re := trace_re_mul_comm _ _
                      _ = (M ^ 2 * D * M * (M * D * M) * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
  -- Also cancellation of M-degree-1 terms in ⟨W1, W2 - W3⟩: Re Tr(D*D*M*D) = Re Tr(D*M*D*D)
  have r_deg1_cancel : (D * (D * M) * D).trace.re = (D * (M * D) * D).trace.re := by
    calc (D * (D * M) * D).trace.re = (D * (D * (D * M))).trace.re := trace_re_mul_comm _ _
      _ = (D * (M * D) * D).trace.re := by
            calc (D * (D * (D * M))).trace.re = ((D * D * D) * M).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
              _ = (M * (D * D * D)).trace.re := trace_re_mul_comm _ _
              _ = ((M * D * D) * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
              _ = (D * (M * D * D)).trace.re := trace_re_mul_comm _ _
              _ = (D * (M * D) * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
  -- Expand the 5 HS quadratic forms!
  have hT1_val : hsNormSq T1 = m ^ 4 * cDDD - 2 * m ^ 2 * cDDMDM + cDMDMDMM := by
    change hsNormSq ((((m ^ 2 : ℝ) : ℂ) • D - M * D * M) * Dhalf) = _; rw [hNormD]
    have hA : (((m ^ 2 : ℝ) : ℂ) • D - M * D * M)ᴴ = ((m ^ 2 : ℝ) : ℂ) • D - M * D * M := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Complex.star_def, Complex.conj_ofReal, hDh, hMh, Matrix.mul_assoc]
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [r_D3, show (D * (M * D * M) * D).trace.re = cDDMDM by
          calc (D * (M * D * M) * D).trace.re = (D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDDMDM := r_DMDMD,
      r_MDMD2, r_MDMM_D]
    ring
  have hW1_val : hsNormSq W1 = m ^ 6 * cDDD - 2 * m ^ 3 * cDDMDMM + cDMMDMMDMM := by
    change hsNormSq ((((m ^ 3 : ℝ) : ℂ) • D - M * D * M ^ 2) * Dhalf) = _; rw [hNormD]
    have hA : (((m ^ 3 : ℝ) : ℂ) • D - M * D * M ^ 2)ᴴ = ((m ^ 3 : ℝ) : ℂ) • D - M ^ 2 * D * M := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_pow, Complex.star_def, Complex.conj_ofReal, hDh, hMh, Matrix.mul_assoc]
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [r_D3, show (D * (M * D * M ^ 2) * D).trace.re = cDDMDMM by
          calc (D * (M * D * M ^ 2) * D).trace.re = (D * M * D * M ^ 2 * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_DMDM2D,
      r_M2DMD2, r_M2D2MDM]
    ring
  have hW2_val : hsNormSq W2 = m ^ 2 * cDDMDM - 2 * m * cDMDMDM + cDMDMDMM := by
    change hsNormSq (((m : ℂ) • (D * M) - M * D * M) * Dhalf) = _; rw [hNormD]
    have hA : ((m : ℂ) • (D * M) - M * D * M)ᴴ = (m : ℂ) • (M * D) - M * D * M := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Complex.star_def, Complex.conj_ofReal, hDh, hMh, Matrix.mul_assoc]
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [show (M * D * (D * M) * D).trace.re = cDDMDM by
          calc (M * D * (D * M) * D).trace.re = (M * D * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDDMDM := r_MD2MD,
      show (M * D * (M * D * M) * D).trace.re = cDMDMDM by
          calc (M * D * (M * D * M) * D).trace.re = (M * D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDMDMDM := r_MDMDMD,
      show (M * D * M * (D * M) * D).trace.re = cDMDMDM by
          calc (M * D * M * (D * M) * D).trace.re = (M * D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDMDMDM := r_MDMDMD,
      r_MDMM_D]
    ring
  have hW23_eq : W2 - W3 = ((m : ℂ) • (D * M) - (m : ℂ) • (M * D) + D * M ^ 2 - M * D * M) * Dhalf := by
    dsimp [W2, W3]; rw [← Matrix.sub_mul]; congr 1; abel
  have hW1_W23 : hsInner W1 (W2 - W3) =
      m ^ 3 * cDDDMM - m ^ 3 * cDDMDM + m * cDDMMDMM - m * cDMDMDMM := by
    rw [hW23_eq]
    change hsInner ((((m ^ 3 : ℝ) : ℂ) • D - M * D * M ^ 2) * Dhalf) _ = _
    rw [hInD]
    have hA : (((m ^ 3 : ℝ) : ℂ) • D - M * D * M ^ 2)ᴴ = ((m ^ 3 : ℝ) : ℂ) • D - M ^ 2 * D * M := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_pow, Complex.star_def, Complex.conj_ofReal, hDh, hMh, Matrix.mul_assoc]
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [r_deg1_cancel, r_deg5_cancel,
      show (D * (D * M ^ 2) * D).trace.re = cDDDMM by
        calc (D * (D * M ^ 2) * D).trace.re = (D * D * M ^ 2 * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = cDDDMM := r_D2M2D,
      show (D * (M * D * M) * D).trace.re = cDDMDM by
        calc (D * (M * D * M) * D).trace.re = (D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = cDDMDM := r_DMDMD,
      show (M ^ 2 * D * M * (D * M) * D).trace.re = cDMDMDMM by
        calc (M ^ 2 * D * M * (D * M) * D).trace.re = (M ^ 2 * D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = cDMDMDMM := r_M2DMDMD,
      show (M ^ 2 * D * M * (M * D) * D).trace.re = cDDMMDMM by
        calc (M ^ 2 * D * M * (M * D) * D).trace.re = ((M ^ 2 * D * M ^ 2) * D ^ 2).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
          _ = (D ^ 2 * (M ^ 2 * D * M ^ 2)).trace.re := trace_re_mul_comm _ _
          _ = cDDMMDMM := by dsimp [cDDMMDMM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]]
    ring
  have hW23_val : hsNormSq (W2 - W3) =
      m ^ 2 * cDDDMM - m ^ 2 * cDDMDM + 2 * m * cDDMDMM + cDDMMDMM - 2 * m * cDMDMDM - cDMDMDMM := by
    rw [hW23_eq, hNormD]
    have hA : ((m : ℂ) • (D * M) - (m : ℂ) • (M * D) + D * M ^ 2 - M * D * M)ᴴ =
        (m : ℂ) • (M * D) - (m : ℂ) • (D * M) + M ^ 2 * D - M * D * M := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, Complex.star_def, Complex.conj_ofReal,
        hDh, hMh, Matrix.mul_assoc]
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
      Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [show (M * D * (D * M) * D).trace.re = cDDMDM by
          calc (M * D * (D * M) * D).trace.re = (M * D * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDDMDM := r_MD2MD,
      show (M * D * (M * D) * D).trace.re = cDDMDM by
          calc (M * D * (M * D) * D).trace.re = (M * D * M * D * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDDMDM := r_MDMD2,
      show (M * D * (D * M ^ 2) * D).trace.re = cDDMDMM by
          calc (M * D * (D * M ^ 2) * D).trace.re = (D * (M * D * (D * M ^ 2))).trace.re := trace_re_mul_comm _ _
            _ = ((D * M * D ^ 2) * M ^ 2).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = (M ^ 2 * (D * M * D ^ 2)).trace.re := trace_re_mul_comm _ _
            _ = (M ^ 2 * D * M * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_M2DMD2,
      show (M * D * (M * D * M) * D).trace.re = cDMDMDM by
          calc (M * D * (M * D * M) * D).trace.re = (M * D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDMDMDM := r_MDMDMD,
      show (D * M * (D * M) * D).trace.re = cDDMDM by
          calc (D * M * (D * M) * D).trace.re = (D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDDMDM := r_DMDMD,
      show (D * M * (M * D) * D).trace.re = cDDDMM by
          calc (D * M * (M * D) * D).trace.re = (D * M ^ 2 * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDDMM := r_DM2D2,
      show (D * M * (D * M ^ 2) * D).trace.re = cDDMDMM by
          calc (D * M * (D * M ^ 2) * D).trace.re = (D * M * D * M ^ 2 * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_DMDM2D,
      show (D * M * (M * D * M) * D).trace.re = cDDMDMM by
          calc (D * M * (M * D * M) * D).trace.re = (D * M ^ 2 * D * M * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_DM2DMD,
      show (M ^ 2 * D * (D * M) * D).trace.re = cDDMDMM by
          calc (M ^ 2 * D * (D * M) * D).trace.re = ((M ^ 2 * D ^ 2) * (M * D)).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = ((M * D) * (M ^ 2 * D ^ 2)).trace.re := trace_re_mul_comm _ _
            _ = (M * D * M ^ 2 * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_MDM2D2,
      show (M ^ 2 * D * (M * D) * D).trace.re = cDDMDMM by
          calc (M ^ 2 * D * (M * D) * D).trace.re = (M ^ 2 * D * M * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_M2DMD2,
      show (M ^ 2 * D * (D * M ^ 2) * D).trace.re = cDDMMDMM by
          calc (M ^ 2 * D * (D * M ^ 2) * D).trace.re = (M ^ 2 * D * D * M ^ 2 * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMMDMM := r_M2D2M2D,
      show (M ^ 2 * D * (M * D * M) * D).trace.re = cDMDMDMM by
          calc (M ^ 2 * D * (M * D * M) * D).trace.re = (M ^ 2 * D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDMDMDMM := r_M2DMDMD,
      show (M * D * M * (D * M) * D).trace.re = cDMDMDM by
          calc (M * D * M * (D * M) * D).trace.re = (M * D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDMDMDM := r_MDMDMD,
      show (M * D * M * (M * D) * D).trace.re = cDDMDMM by
          calc (M * D * M * (M * D) * D).trace.re = (M * D * M ^ 2 * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = cDDMDMM := r_MDM2D2,
      show (M * D * M * (D * M ^ 2) * D).trace.re = cDMDMDMM by
          calc (M * D * M * (D * M ^ 2) * D).trace.re = (M * D * M * D * M ^ 2 * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
            _ = cDMDMDMM := r_MDM_M2D,
      r_MDMM_D]
    ring
  -- Expand LHS = threeW32 Λ m D M
  have hLHS : threeW32 Λ m D M =
      (1 + Λ * (m ^ 3 - m)) * cDDD + 3 * cDDMDM - 2 * Λ * cDMDMDM +
      3 * cDMDMDMM + cDMMDMMDMM := by
    unfold threeW32
    have hcube := ring_add_pow_three D (M * D * M)
    rw [hcube]
    simp only [Matrix.trace_add, Complex.add_re]
    rw [show (D ^ 2 * (M * D * M)).trace.re = cDDMDM by dsimp [cDDMDM]; apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc],
      show (D * (M * D * M) * D).trace.re = cDDMDM by
        calc (D * (M * D * M) * D).trace.re = (D * M * D * M * D).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = cDDMDM := r_DMDMD,
      show ((M * D * M) * D ^ 2).trace.re = cDDMDM by
        calc ((M * D * M) * D ^ 2).trace.re = (M * D * M * D * D).trace.re := by apply tr_re_eq; simp only [mat_pow_two, Matrix.mul_assoc]
          _ = cDDMDM := r_MDMD2,
      show (D * (M * D * M) * (M * D * M)).trace.re = cDMDMDMM by
        calc (D * (M * D * M) * (M * D * M)).trace.re = (D * ((M * D * M) * (M * D * M))).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = (((M * D * M) * (M * D * M)) * D).trace.re := trace_re_mul_comm _ _
          _ = cDMDMDMM := r_MDMM_D,
      show ((M * D * M) * D * (M * D * M)).trace.re = cDMDMDMM by
        calc ((M * D * M) * D * (M * D * M)).trace.re = ((M * D * M) * (D * (M * D * M))).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = ((D * (M * D * M)) * (M * D * M)).trace.re := trace_re_mul_comm _ _
          _ = (D * ((M * D * M) * (M * D * M))).trace.re := by apply tr_re_eq; simp only [Matrix.mul_assoc]
          _ = (((M * D * M) * (M * D * M)) * D).trace.re := trace_re_mul_comm _ _
          _ = cDMDMDMM := r_MDMM_D,
      r_MDMM_D]
    dsimp [cDDD, cDMDMDM, cDMMDMMDMM]; ring
  have hΛ_eq : Λ = (1 + m ^ 2) ^ 2 / m := by field_simp [hm0.ne']; linarith
  have hId : threeW32 Λ m D M =
      (1 - 1 / m ^ 2) * hsNormSq T1 +
      hsNormSq (W1 - ((m / 2 : ℝ) : ℂ) • W2 + ((m / 2 : ℝ) : ℂ) • W3) +
      (3 * m ^ 2 / 4) * hsNormSq (W2 - W3) +
      (2 + 1 / m ^ 2) * hsNormSq W2 := by
    rw [hLHS, add_assoc ((1 - 1 / m ^ 2) * hsNormSq T1), hpol,
      hT1_val, hW1_val, hW1_W23, hW23_val, hW2_val, hΛ_eq]
    field_simp [hm0.ne']; ring
  have hnn : 0 ≤ threeW32 Λ m D M := by
    rw [hId]
    exact add_nonneg (add_nonneg (add_nonneg (mul_nonneg hc1_nn (hsNormSq_nonneg _)) (hsNormSq_nonneg _))
      (mul_nonneg hc3_pos.le (hsNormSq_nonneg _))) (mul_nonneg hc4_pos.le (hsNormSq_nonneg _))
  refine ⟨⟨hc1_nn, hc3_pos, hc4_pos⟩, hId, hnn, ?_⟩
  constructor
  · intro hzero
    rw [hId] at hzero
    have hW2_zero : hsNormSq W2 = 0 := by
      have h1 := mul_nonneg hc1_nn (hsNormSq_nonneg T1)
      have h2 := hsNormSq_nonneg (W1 - ((m / 2 : ℝ) : ℂ) • W2 + ((m / 2 : ℝ) : ℂ) • W3)
      have h3 := mul_nonneg hc3_pos.le (hsNormSq_nonneg (W2 - W3))
      have h4 := hsNormSq_nonneg W2
      nlinarith only [hzero, h1, h2, h3, h4, hc4_pos]
    have hmat0 : ((m : ℂ) • (D * M) - M * D * M) * Dhalf = 0 := (hsNormSq_eq_zero_iff _).mp hW2_zero
    have h1 : (m : ℂ) • (D * M) - M * D * M = 0 :=
      posDef_mul_right_cancel (posDefPow_posDef (1 / 2) hD) (by rw [Matrix.zero_mul]; exact hmat0)
    have h2 : ((m : ℂ) • (1 : Mat n) - M) * D * M = 0 := by
      calc ((m : ℂ) • (1 : Mat n) - M) * D * M = (m : ℂ) • (D * M) - M * D * M := by
            rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = 0 := h1
    have h3 : ((m : ℂ) • (1 : Mat n) - M) * D = 0 :=
      posDef_mul_right_cancel hM (by rw [Matrix.zero_mul]; exact h2)
    have h4 : (m : ℂ) • (1 : Mat n) - M = 0 :=
      posDef_mul_right_cancel hD (by rw [Matrix.zero_mul]; exact h3)
    exact (sub_eq_zero.mp h4).symm
  · intro hMm
    rw [hId]
    have hM2 : ((m : ℂ) • (1 : Mat n)) ^ 2 = ((m ^ 2 : ℝ) : ℂ) • (1 : Mat n) := by
      rw [mat_pow_two, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      push_cast; rw [sq]
    have hT1_0 : T1 = 0 := by
      change (((m ^ 2 : ℝ) : ℂ) • D - M * D * M) * Dhalf = 0
      rw [hMm]
      have : ((m ^ 2 : ℝ) : ℂ) • D - (m : ℂ) • (1 : Mat n) * D * (m : ℂ) • (1 : Mat n) = 0 := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
        push_cast; rw [sq, sub_self]
      rw [this, Matrix.zero_mul]
    have hW1_0 : W1 = 0 := by
      change (((m ^ 3 : ℝ) : ℂ) • D - M * D * M ^ 2) * Dhalf = 0
      rw [hMm, hM2]
      have : ((m ^ 3 : ℝ) : ℂ) • D - (m : ℂ) • (1 : Mat n) * D * ((m ^ 2 : ℝ) : ℂ) • (1 : Mat n) = 0 := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
        rw [← sub_smul]; have : ((m ^ 3 : ℝ) : ℂ) - ((m ^ 2 : ℝ) : ℂ) * (m : ℂ) = 0 := by push_cast; ring
        rw [this, zero_smul]
      rw [this, Matrix.zero_mul]
    have hW2_0 : W2 = 0 := by
      change ((m : ℂ) • (D * M) - M * D * M) * Dhalf = 0
      rw [hMm]
      have : (m : ℂ) • (D * (m : ℂ) • (1 : Mat n)) - (m : ℂ) • (1 : Mat n) * D * (m : ℂ) • (1 : Mat n) = 0 := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, sub_self]
      rw [this, Matrix.zero_mul]
    have hW3_0 : W3 = 0 := by
      change ((m : ℂ) • (M * D) - D * M ^ 2) * Dhalf = 0
      rw [hMm, hM2]
      have : (m : ℂ) • ((m : ℂ) • (1 : Mat n) * D) - D * ((m ^ 2 : ℝ) : ℂ) • (1 : Mat n) = 0 := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
        push_cast; rw [sq, sub_self]
      rw [this, Matrix.zero_mul]
    rw [hT1_0, hW1_0, hW2_0, hW3_0]
    simp only [smul_zero, sub_zero, add_zero, (hsNormSq_eq_zero_iff 0).mpr rfl, mul_zero]

/-! ==========================================================================
    PART 4: Exact p = 4/3 & p = 3/2 Pinching Energy Decompositions
    ========================================================================== -/

private lemma trace_eq_zero_of_conj_neg {n : ℕ} {J X : Mat n}
    (hJ2 : J * J = 1) (hneg : J * X * J = -X) : X.trace = 0 := by
  have h1 : (J * X * J).trace = X.trace := by
    calc (J * X * J).trace = (J * (J * X)).trace := Matrix.trace_mul_comm _ _
      _ = ((J * J) * X).trace := by rw [Matrix.mul_assoc]
      _ = X.trace := by rw [hJ2, Matrix.one_mul]
  rw [hneg, Matrix.trace_neg] at h1
  have h2 : (2 : ℂ) * X.trace = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma orth_proj_decomp_helpers {n : ℕ} {P D X : Mat n}
    (hP_idem : P * P = P) (hPD : P * D = D * P) :
    let Q : Mat n := 1 - P
    let J : Mat n := (2 : ℂ) • P - 1
    let X0 : Mat n := P * X * P + Q * X * Q
    let V : Mat n := X - X0
    Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧ Q * D = D * Q ∧
    J * J = 1 ∧ J * D * J = D ∧ J * X0 * J = X0 ∧ J * V * J = -V ∧
    D = P * D * P + Q * D * Q ∧ V = P * X * Q + Q * X * P := by
  intro Q J X0 V
  have hQ2 : Q * Q = Q := by
    dsimp [Q]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_idem]; abel
  have hPQ : P * Q = 0 := by
    dsimp [Q]; rw [Matrix.mul_sub, Matrix.mul_one, hP_idem, sub_self]
  have hQP : Q * P = 0 := by
    dsimp [Q]; rw [Matrix.sub_mul, Matrix.one_mul, hP_idem, sub_self]
  have hQD : Q * D = D * Q := by
    dsimp [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPD]
  have hJ_eq : J = P - Q := by
    dsimp [J, Q]; rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]; abel
  have hJ2 : J * J = 1 := by
    calc J * J = (P - Q) * (P - Q) := by rw [hJ_eq]
      _ = P * P - P * Q - Q * P + Q * Q := by
            rw [Matrix.sub_mul, Matrix.mul_sub P P Q, Matrix.mul_sub Q P Q]; abel
      _ = P + Q := by rw [hP_idem, hPQ, hQP, hQ2]; abel
      _ = 1 := by dsimp [Q]; abel
  have hJP : J * P = P := by
    rw [hJ_eq, Matrix.sub_mul, hP_idem, hQP, sub_zero]
  have hPJ : P * J = P := by
    rw [hJ_eq, Matrix.mul_sub, hP_idem, hPQ, sub_zero]
  have hJQ : J * Q = -Q := by
    rw [hJ_eq, Matrix.sub_mul, hPQ, hQ2, zero_sub]
  have hQJ : Q * J = -Q := by
    rw [hJ_eq, Matrix.mul_sub, hQP, hQ2, zero_sub]
  have hD_split : D = P * D * P + Q * D * Q := by
    have h1 : P * D * P = P * D := by rw [Matrix.mul_assoc, ← hPD, ← Matrix.mul_assoc, hP_idem]
    have h2 : Q * D * Q = Q * D := by rw [Matrix.mul_assoc, ← hQD, ← Matrix.mul_assoc, hQ2]
    rw [h1, h2, ← Matrix.add_mul]
    have hPQ1 : P + Q = 1 := by dsimp [Q]; abel
    rw [hPQ1, Matrix.one_mul]
  have hJDJ : J * D * J = D := by
    conv_lhs => rw [hD_split]
    rw [Matrix.mul_add, Matrix.add_mul]
    have t1 : J * (P * D * P) * J = P * D * P := by
      calc J * (P * D * P) * J = (J * P) * D * (P * J) := by simp only [Matrix.mul_assoc]
        _ = P * D * P := by rw [hJP, hPJ]
    have t2 : J * (Q * D * Q) * J = Q * D * Q := by
      calc J * (Q * D * Q) * J = (J * Q) * D * (Q * J) := by simp only [Matrix.mul_assoc]
        _ = (-Q) * D * (-Q) := by rw [hJQ, hQJ]
        _ = Q * D * Q := by simp
    rw [t1, t2, ← hD_split]
  have hJX0J : J * X0 * J = X0 := by
    dsimp [X0]; rw [Matrix.mul_add, Matrix.add_mul]
    have t1 : J * (P * X * P) * J = P * X * P := by
      calc J * (P * X * P) * J = (J * P) * X * (P * J) := by simp only [Matrix.mul_assoc]
        _ = P * X * P := by rw [hJP, hPJ]
    have t2 : J * (Q * X * Q) * J = Q * X * Q := by
      calc J * (Q * X * Q) * J = (J * Q) * X * (Q * J) := by simp only [Matrix.mul_assoc]
        _ = (-Q) * X * (-Q) := by rw [hJQ, hQJ]
        _ = Q * X * Q := by simp
    rw [t1, t2]
  have hV_eq : V = P * X * Q + Q * X * P := by
    have hX1 : (P + Q) * X * (P + Q) = X := by
      have : P + Q = 1 := by dsimp [Q]; abel
      rw [this, Matrix.one_mul, Matrix.mul_one]
    calc V = (P + Q) * X * (P + Q) - (P * X * P + Q * X * Q) := by dsimp [V, X0]; rw [hX1]
      _ = P * X * Q + Q * X * P := by
            rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]; abel
  have hJVJ : J * V * J = -V := by
    rw [hV_eq, Matrix.mul_add, Matrix.add_mul]
    have t1 : J * (P * X * Q) * J = -(P * X * Q) := by
      calc J * (P * X * Q) * J = (J * P) * X * (Q * J) := by simp only [Matrix.mul_assoc]
        _ = P * X * (-Q) := by rw [hJP, hQJ]
        _ = -(P * X * Q) := by simp
    have t2 : J * (Q * X * P) * J = -(Q * X * P) := by
      calc J * (Q * X * P) * J = (J * Q) * X * (P * J) := by simp only [Matrix.mul_assoc]
        _ = (-Q) * X * P := by rw [hJQ, hPJ]
        _ = -(Q * X * P) := by simp
    rw [t1, t2]; abel
  exact ⟨hQ2, hPQ, hQP, hQD, hJ2, hJDJ, hJX0J, hJVJ, hD_split, hV_eq⟩

private lemma orth_block_add_pow {n : ℕ} {A B : Mat n} (hAB : A * B = 0) (hBA : B * A = 0) :
    ∀ k : ℕ, 1 ≤ k → (A + B) ^ k = A ^ k + B ^ k
  | 0, hk => by omega
  | 1, _ => by simp
  | k + 2, _ => by
      have ih := orth_block_add_pow hAB hBA (k + 1) (by omega)
      rw [pow_succ, ih, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      have hAkB : A ^ (k + 1) * B = 0 := by
        rw [pow_succ, Matrix.mul_assoc, hAB, Matrix.mul_zero]
      have hBkA : B ^ (k + 1) * A = 0 := by
        rw [pow_succ, Matrix.mul_assoc, hBA, Matrix.mul_zero]
      rw [hAkB, hBkA, add_zero, zero_add, ← pow_succ, ← pow_succ]

/-- Exact p = 4/3 Pinching Energy Decomposition (`#15.3`, `#16`, `p1_proof.md` Thm 3.2):
    For any solution (D, H) of (D + H)³ = Λ D H D and any orthogonal projection P commuting with D,
    setting Q = I - P, H₀ = P H P + Q H Q, V = H - H₀ = P H Q + Q H P:
      4 W_Λ(D, H) = 4 W_Λ(P D P, P H P) + 4 W_Λ(Q D Q, Q H Q) - Re Tr(V⁴),
    where Re Tr(V⁴) = 2 ‖P H Q H P‖_HS² ≥ 0! -/
theorem pinching_decomposition_p43 {n : ℕ} {Λ h : ℝ} {D H P : Mat n}
    (hH : H.IsHermitian) (hP_herm : P.IsHermitian) (hP_idem : P * P = P) (hPD : P * D = D * P)
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D)) :
    let Q := 1 - P
    let H0 := P * H * P + Q * H * Q
    let V := H - H0
    fourW43 Λ h D H =
      fourW43 Λ h (P * D * P) (P * H * P) + fourW43 Λ h (Q * D * Q) (Q * H * Q) -
      (V ^ 4).trace.re ∧
    (V ^ 4).trace.re = 2 * hsNormSq (P * H * Q * H * P) ∧
    0 ≤ (V ^ 4).trace.re := by
  intro Q H0 V
  let J : Mat n := (2 : ℂ) • P - 1
  obtain ⟨hQ2, hPQ, hQP, hQD, hJ2, hJDJ, hJH0J, hJVJ, hD_split, hV_eq⟩ :=
    orth_proj_decomp_helpers (X := H) hP_idem hPD
  change Q * Q = Q at hQ2
  change P * Q = 0 at hPQ
  change Q * P = 0 at hQP
  change Q * D = D * Q at hQD
  change J * J = 1 at hJ2
  change J * D * J = D at hJDJ
  change J * H0 * J = H0 at hJH0J
  change J * V * J = -V at hJVJ
  change D = P * D * P + Q * D * Q at hD_split
  change V = P * H * Q + Q * H * P at hV_eq
  let A0 : Mat n := D + H0
  have hJA0J : J * A0 * J = A0 := by
    dsimp [A0]; rw [Matrix.mul_add, Matrix.add_mul, hJDJ, hJH0J]
  have hH_split : H = H0 + V := by dsimp [V]; abel
  have hA_split : D + H = A0 + V := by dsimp [A0]; rw [hH_split]; abel
  -- Parity vanishing via J: any trace with odd V-count is 0!
  have hJ_mul : ∀ X Y : Mat n, (J * X * J) * (J * Y * J) = J * (X * Y) * J := fun X Y => by
    calc (J * X * J) * (J * Y * J) = J * X * (J * J) * Y * J := by simp only [Matrix.mul_assoc]
      _ = J * (X * Y) * J := by rw [hJ2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hodd_A03V : (A0 ^ 3 * V).trace = 0 := by
    apply trace_eq_zero_of_conj_neg hJ2
    have : J * (A0 ^ 3 * V) * J = (J * A0 * J) * (J * A0 * J) * (J * A0 * J) * (J * V * J) := by
      rw [hJ_mul, hJ_mul, hJ_mul]; simp only [mat_pow_three, Matrix.mul_assoc]
    rw [this, hJA0J, hJVJ]; simp only [Matrix.mul_neg, mat_pow_three, Matrix.mul_assoc]
  have hodd_A0V3 : (A0 * V ^ 3).trace = 0 := by
    apply trace_eq_zero_of_conj_neg hJ2
    have : J * (A0 * V ^ 3) * J = (J * A0 * J) * (J * V * J) * (J * V * J) * (J * V * J) := by
      rw [hJ_mul, hJ_mul, hJ_mul]; simp only [mat_pow_three, Matrix.mul_assoc]
    rw [this, hJA0J, hJVJ]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, mat_pow_three, Matrix.mul_assoc]
  have hodd_DH0DV : (D * H0 * D * V).trace = 0 := by
    apply trace_eq_zero_of_conj_neg hJ2
    have : J * (D * H0 * D * V) * J = (J * D * J) * (J * H0 * J) * (J * D * J) * (J * V * J) := by
      simp only [hJ_mul]
    rw [this, hJDJ, hJH0J, hJVJ]; simp
  have hodd_DVH0D : (D * V * D * H0).trace = 0 := by
    rw [Matrix.trace_mul_comm (D * V * D) H0]
    calc (H0 * (D * V * D)).trace = ((H0 * D * V) * D).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = (D * (H0 * D * V)).trace := Matrix.trace_mul_comm _ _
      _ = (D * H0 * D * V).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = 0 := hodd_DH0DV
  -- Step 1: Expand fourW43 Λ h D H - fourW43 Λ h D H0
  have hstep1 : fourW43 Λ h D H - fourW43 Λ h D H0 =
      4 * (A0 ^ 2 * V ^ 2).trace.re + 2 * (A0 * V * A0 * V).trace.re -
      2 * Λ * (D * V * D * V).trace.re + (V ^ 4).trace.re := by
    unfold fourW43
    rw [hA_split, trace_re_add_pow_four A0 V, hodd_A03V, hodd_A0V3, Complex.zero_re]
    have hDHDH : (D * H * D * H).trace.re = (D * H0 * D * H0).trace.re + (D * V * D * V).trace.re := by
      conv_lhs => rw [hH_split]
      have hexp := ring_mul_add_mul_add D H0 V
      rw [hexp]; simp only [Matrix.trace_add, hodd_DH0DV, hodd_DVH0D, add_zero, Complex.add_re]
    rw [hDHDH]; dsimp [A0]; ring
  -- Step 2: Stationarity Tr(((D + H)^3 - Λ D H D) * V) = 0 gives
  --         2 Tr(A0^2 V^2) + Tr(A0 V A0 V) - Λ Tr(D V D V) + Tr(V^4) = 0!
  have hstat : 2 * (A0 ^ 2 * V ^ 2).trace.re + (A0 * V * A0 * V).trace.re -
      Λ * (D * V * D * V).trace.re + (V ^ 4).trace.re = 0 := by
    have h0 : (((D + H) ^ 3 - (Λ : ℂ) • (D * H * D)) * V).trace.re = 0 := by
      rw [hEq, sub_self, Matrix.zero_mul, Matrix.trace_zero, Complex.zero_re]
    rw [hA_split, hH_split] at h0
    have hexp : ((A0 + V) ^ 3 - (Λ : ℂ) • (D * (H0 + V) * D)) * V =
        (A0 ^ 3 * V + A0 ^ 2 * V ^ 2 + A0 * V * A0 * V + V * A0 ^ 2 * V +
         A0 * V ^ 3 + V * A0 * V ^ 2 + V ^ 2 * A0 * V + V ^ 4) -
        (Λ : ℂ) • (D * H0 * D * V + D * V * D * V) := by
      rw [Matrix.sub_mul, Matrix.smul_mul]
      congr 1
      · exact ring_add_pow_three_mul_right A0 V
      · congr 1; exact ring_mul_add_mul_mul D H0 V
    rw [hexp, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_add, smul_eq_mul] at h0
    have hVA02V : (V * A0 ^ 2 * V).trace = (A0 ^ 2 * V ^ 2).trace := by
      calc (V * A0 ^ 2 * V).trace = (V * (V * A0 ^ 2)).trace := Matrix.trace_mul_comm _ _
        _ = (V ^ 2 * A0 ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (A0 ^ 2 * V ^ 2).trace := Matrix.trace_mul_comm _ _
    have hVA0V2 : (V * A0 * V ^ 2).trace = 0 := by
      calc (V * A0 * V ^ 2).trace = (V ^ 2 * (V * A0)).trace := Matrix.trace_mul_comm _ _
        _ = (V ^ 3 * A0).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
        _ = (A0 * V ^ 3).trace := Matrix.trace_mul_comm _ _
        _ = 0 := hodd_A0V3
    have hV2A0V : (V ^ 2 * A0 * V).trace = 0 := by
      calc (V ^ 2 * A0 * V).trace = (V * (V ^ 2 * A0)).trace := Matrix.trace_mul_comm _ _
        _ = (V ^ 3 * A0).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
        _ = (A0 * V ^ 3).trace := Matrix.trace_mul_comm _ _
        _ = 0 := hodd_A0V3
    rw [hodd_A03V, hVA02V, hodd_A0V3, hVA0V2, hV2A0V, hodd_DH0DV] at h0
    simp only [zero_add, add_zero, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h0
    linarith
  -- Step 3: Block additivity fourW43 Λ h D H0 = fourW43 (P D P) (P H P) + fourW43 (Q D Q) (Q H Q)
  have hblock : fourW43 Λ h D H0 =
      fourW43 Λ h (P * D * P) (P * H * P) + fourW43 Λ h (Q * D * Q) (Q * H * Q) := by
    unfold fourW43
    have hPD_QD : (P * D * P) * (Q * D * Q) = 0 := by
      calc (P * D * P) * (Q * D * Q) = P * D * (P * Q) * D * Q := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPQ]; simp
    have hQD_PD : (Q * D * Q) * (P * D * P) = 0 := by
      calc (Q * D * Q) * (P * D * P) = Q * D * (Q * P) * D * P := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQP]; simp
    have hD4 : D ^ 4 = (P * D * P) ^ 4 + (Q * D * Q) ^ 4 := by
      conv_lhs => rw [hD_split]
      exact orth_block_add_pow hPD_QD hQD_PD 4 (by norm_num)
    have hA_bl : D + H0 = (P * D * P + P * H * P) + (Q * D * Q + Q * H * Q) := by
      conv_lhs => rw [hD_split]
      dsimp [H0]; abel
    have hPQ_A : (P * D * P + P * H * P) * (Q * D * Q + Q * H * Q) = 0 := by
      simp only [Matrix.add_mul, Matrix.mul_add]
      have z1 : ∀ X Y : Mat n, (P * X * P) * (Q * Y * Q) = 0 := fun X Y => by
        calc (P * X * P) * (Q * Y * Q) = P * X * (P * Q) * Y * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      rw [z1, z1, z1, z1]; simp
    have hQP_A : (Q * D * Q + Q * H * Q) * (P * D * P + P * H * P) = 0 := by
      simp only [Matrix.add_mul, Matrix.mul_add]
      have z1 : ∀ X Y : Mat n, (Q * X * Q) * (P * Y * P) = 0 := fun X Y => by
        calc (Q * X * Q) * (P * Y * P) = Q * X * (Q * P) * Y * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      rw [z1, z1, z1, z1]; simp
    have hA4 : (D + H0) ^ 4 = (P * D * P + P * H * P) ^ 4 + (Q * D * Q + Q * H * Q) ^ 4 := by
      rw [hA_bl]; exact orth_block_add_pow hPQ_A hQP_A 4 (by norm_num)
    have hDH0 : D * H0 = (P * D * P) * (P * H * P) + (Q * D * Q) * (Q * H * Q) := by
      conv_lhs => rw [hD_split]
      dsimp [H0]; simp only [Matrix.add_mul, Matrix.mul_add]
      have z1 : (P * D * P) * (Q * H * Q) = 0 := by
        calc (P * D * P) * (Q * H * Q) = P * D * (P * Q) * H * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have z2 : (Q * D * Q) * (P * H * P) = 0 := by
        calc (Q * D * Q) * (P * H * P) = Q * D * (Q * P) * H * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      rw [z1, z2, add_zero, zero_add]
    have hDHDH0 : D * H0 * D * H0 =
        (P * D * P) * (P * H * P) * (P * D * P) * (P * H * P) +
        (Q * D * Q) * (Q * H * Q) * (Q * D * Q) * (Q * H * Q) := by
      have : D * H0 * D * H0 = (D * H0) ^ 2 := by simp only [mat_pow_two, Matrix.mul_assoc]
      rw [this, hDH0]
      have z1 : ((P * D * P) * (P * H * P)) * ((Q * D * Q) * (Q * H * Q)) = 0 := by
        calc _ = P * D * P * P * H * (P * Q) * D * Q * Q * H * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have z2 : ((Q * D * Q) * (Q * H * Q)) * ((P * D * P) * (P * H * P)) = 0 := by
        calc _ = Q * D * Q * Q * H * (Q * P) * D * P * P * H * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      rw [orth_block_add_pow z1 z2 2 (by norm_num)]; simp only [sq, Matrix.mul_assoc]
    rw [hA4, hD4, hDHDH0]
    simp only [Matrix.trace_add, Complex.add_re]; ring
  -- Step 4: (V^4).trace.re = 2 * hsNormSq (P * H * Q * H * P) ≥ 0
  have hV4_eq : (V ^ 4).trace.re = 2 * hsNormSq (P * H * Q * H * P) := by
    have hV2 : V * V = P * H * Q * H * P + Q * H * P * H * Q := by
      rw [hV_eq]; simp only [Matrix.add_mul, Matrix.mul_add]
      have z1 : (P * H * Q) * (P * H * Q) = 0 := by
        calc _ = P * H * (Q * P) * H * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      have z2 : (Q * H * P) * (Q * H * P) = 0 := by
        calc _ = Q * H * (P * Q) * H * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have t1 : (P * H * Q) * (Q * H * P) = P * H * Q * H * P := by
        calc _ = P * H * (Q * Q) * H * P := by simp only [Matrix.mul_assoc]
          _ = P * H * Q * H * P := by rw [hQ2]
      have t2 : (Q * H * P) * (P * H * Q) = Q * H * P * H * Q := by
        calc _ = Q * H * (P * P) * H * Q := by simp only [Matrix.mul_assoc]
          _ = Q * H * P * H * Q := by rw [hP_idem]
      rw [z1, z2, t1, t2, zero_add, add_zero]; exact add_comm _ _
    have hV4 : V ^ 4 = (P * H * Q * H * P) ^ 2 + (Q * H * P * H * Q) ^ 2 := by
      have : V ^ 4 = (V * V) ^ 2 := by simp only [mat_pow_two, mat_pow_four, Matrix.mul_assoc]
      rw [this, hV2]
      have z1 : (P * H * Q * H * P) * (Q * H * P * H * Q) = 0 := by
        calc _ = P * H * Q * H * (P * Q) * H * P * H * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have z2 : (Q * H * P * H * Q) * (P * H * Q * H * P) = 0 := by
        calc _ = Q * H * P * H * (Q * P) * H * Q * H * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      exact orth_block_add_pow z1 z2 2 (by norm_num)
    have hQ_eq_P : ((Q * H * P * H * Q) ^ 2).trace = ((P * H * Q * H * P) ^ 2).trace := by
      calc ((Q * H * P * H * Q) ^ 2).trace
          = ((Q * H * P) * (H * Q * Q * H * P * H * Q)).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = ((H * Q * Q * H * P * H * Q) * (Q * H * P)).trace := Matrix.trace_mul_comm _ _
        _ = ((H * (Q * Q) * H * P * H * (Q * Q) * H * P)).trace := by simp only [Matrix.mul_assoc]
        _ = ((H * Q * H * P * H * Q * H) * P).trace := by rw [hQ2]
        _ = (P * (H * Q * H * P * H * Q * H)).trace := Matrix.trace_mul_comm _ _
        _ = ((P * H * Q * H * P) * (P * H * Q * H * P)).trace := by
              calc (P * (H * Q * H * P * H * Q * H)).trace
                  = ((P * H * Q * H) * (P * H * Q * H)).trace := by simp only [Matrix.mul_assoc]
                _ = (((P * P) * H * Q * H) * ((P * P) * H * Q * H)).trace := by rw [hP_idem]
                _ = (P * ((P * H * Q * H * P) * (P * H * Q * H))).trace := by simp only [Matrix.mul_assoc]
                _ = (((P * H * Q * H * P) * (P * H * Q * H)) * P).trace := Matrix.trace_mul_comm _ _
                _ = ((P * H * Q * H * P) * (P * H * Q * H * P)).trace := by simp only [Matrix.mul_assoc]
        _ = ((P * H * Q * H * P) ^ 2).trace := by rw [sq]
    have hQh : Qᴴ = Q := by dsimp [Q]; rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm.eq]
    have hB_herm : (P * H * Q * H * P)ᴴ = P * H * Q * H * P := by
      simp only [Matrix.conjTranspose_mul, hP_herm.eq, hQh, hH.eq, Matrix.mul_assoc]
    rw [hV4, Matrix.trace_add, hQ_eq_P, Complex.add_re]
    unfold hsNormSq; rw [hB_herm, sq]; ring
  refine ⟨by linarith [hstep1, hstat, hblock], hV4_eq, ?_⟩
  rw [hV4_eq]; exact mul_nonneg (by norm_num) (hsNormSq_nonneg _)

/-- Exact p = 3/2 Degree-6 Pinching Energy Decomposition (`#31`, `ver_audit.md` §11.1):
    For any solution (D, M) ≻ 0 of (D + M D M)² = Λ D M D and any orthogonal projection P
    commuting with D, setting Q = I - P, M₀ = P M P + Q M Q, V = M - M₀,
    X₀ = D + M₀ D M₀, X₁ = M₀ D V + V D M₀, X₂ = V D V:
      3 W_Λ(D, M D M) = 3 W_Λ(P D P, P M P) + 3 W_Λ(Q D Q, Q M Q)
                        - 3 Re Tr(X₀ X₂²) - 3 Re Tr(X₁² X₂) - 2 Re Tr(X₂³),
    where ALL THREE subtracted off-diagonal penalty terms are unconditionally nonnegative! -/
theorem pinching_decomposition_p32 {n : ℕ} {Λ m : ℝ} {D M P : Mat n}
    (hD : D.PosDef) (hM : M.PosDef) (hP_herm : P.IsHermitian) (hP_idem : P * P = P)
    (hPD : P * D = D * P)
    (hEq : (D + M * D * M) ^ 2 = (Λ : ℂ) • (D * M * D)) :
    let Q := 1 - P
    let M0 := P * M * P + Q * M * Q
    let V := M - M0
    let X0 := D + M0 * D * M0
    let X1 := M0 * D * V + V * D * M0
    let X2 := V * D * V
    threeW32 Λ m D M =
      threeW32 Λ m (P * D * P) (P * M * P) + threeW32 Λ m (Q * D * Q) (Q * M * Q) -
      3 * (X0 * X2 ^ 2).trace.re - 3 * (X1 ^ 2 * X2).trace.re - 2 * (X2 ^ 3).trace.re ∧
    0 ≤ (X0 * X2 ^ 2).trace.re ∧ 0 ≤ (X1 ^ 2 * X2).trace.re ∧ 0 ≤ (X2 ^ 3).trace.re := by
  intro Q M0 V X0 X1 X2
  let J : Mat n := (2 : ℂ) • P - 1
  obtain ⟨hQ2, hPQ, hQP, hQD, hJ2, hJDJ, hJM0J, hJVJ, hD_split, _⟩ :=
    orth_proj_decomp_helpers (X := M) hP_idem hPD
  change Q * Q = Q at hQ2
  change P * Q = 0 at hPQ
  change Q * P = 0 at hQP
  change Q * D = D * Q at hQD
  change J * J = 1 at hJ2
  change J * D * J = D at hJDJ
  change J * M0 * J = M0 at hJM0J
  change J * V * J = -V at hJVJ
  change D = P * D * P + Q * D * Q at hD_split
  have hJ_mul : ∀ A B : Mat n, (J * A * J) * (J * B * J) = J * (A * B) * J := fun A B => by
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hJX0J : J * X0 * J = X0 := by
    dsimp [X0]; rw [Matrix.mul_add, Matrix.add_mul, hJDJ]
    have : J * (M0 * D * M0) * J = (J * M0 * J) * (J * D * J) * (J * M0 * J) := by
      simp only [hJ_mul]
    rw [this, hJM0J, hJDJ]
  have hJX1J : J * X1 * J = -X1 := by
    dsimp [X1]; rw [Matrix.mul_add, Matrix.add_mul]
    have t1 : J * (M0 * D * V) * J = -(M0 * D * V) := by
      have : J * (M0 * D * V) * J = (J * M0 * J) * (J * D * J) * (J * V * J) := by
        simp only [hJ_mul]
      rw [this, hJM0J, hJDJ, hJVJ]; simp
    have t2 : J * (V * D * M0) * J = -(V * D * M0) := by
      have : J * (V * D * M0) * J = (J * V * J) * (J * D * J) * (J * M0 * J) := by
        simp only [hJ_mul]
      rw [this, hJM0J, hJDJ, hJVJ]; simp
    rw [t1, t2]; abel
  have hJX2J : J * X2 * J = X2 := by
    dsimp [X2]
    have : J * (V * D * V) * J = (J * V * J) * (J * D * J) * (J * V * J) := by
      simp only [hJ_mul]
    rw [this, hJVJ, hJDJ]; simp
  have hM_split : M = M0 + V := by dsimp [V]; abel
  have hA_split : D + M * D * M = X0 + X1 + X2 := by
    rw [hM_split]; dsimp [X0, X1, X2]; exact ring_p32_split D M0 V
  -- Helper: any product with J-sign -1 has trace 0
  have hodd3 : ∀ A B C : Mat n,
      (J * A * J) * (J * B * J) * (J * C * J) = -(A * B * C) → (A * B * C).trace = 0 := fun A B C h => by
    apply trace_eq_zero_of_conj_neg hJ2
    calc J * (A * B * C) * J = (J * A * J) * (J * B * J) * (J * C * J) := by
          simp only [hJ_mul]
      _ = -(A * B * C) := h
  have hodd_X02X1 : (X0 ^ 2 * X1).trace = 0 := by
    have h := hodd3 X0 X0 X1 (by rw [hJX0J, hJX1J]; simp)
    simpa [sq] using h
  have hodd_X0X2X1 : (X0 * X2 * X1).trace = 0 :=
    hodd3 X0 X2 X1 (by rw [hJX0J, hJX2J, hJX1J]; simp)
  have hodd_X2X0X1 : (X2 * X0 * X1).trace = 0 :=
    hodd3 X2 X0 X1 (by rw [hJX0J, hJX2J, hJX1J]; simp)
  have hodd_X22X1 : (X2 ^ 2 * X1).trace = 0 := by
    have h := hodd3 X2 X2 X1 (by rw [hJX2J, hJX1J]; simp)
    simpa [sq] using h
  have hodd_X13 : (X1 ^ 3).trace = 0 := by
    have h := hodd3 X1 X1 X1 (by rw [hJX1J]; simp)
    simpa [mat_pow_three] using h
  have hJDM0J : J * (D * M0) * J = D * M0 := by
    calc J * (D * M0) * J = (J * D * J) * (J * M0 * J) := (hJ_mul D M0).symm
      _ = D * M0 := by rw [hJDJ, hJM0J]
  have hJDVJ : J * (D * V) * J = -(D * V) := by
    calc J * (D * V) * J = (J * D * J) * (J * V * J) := (hJ_mul D V).symm
      _ = -(D * V) := by rw [hJDJ, hJVJ]; simp
  have hodd_DM02_DV : ((D * M0) ^ 2 * (D * V)).trace = 0 := by
    have h := hodd3 (D * M0) (D * M0) (D * V) (by rw [hJDM0J, hJDVJ]; simp)
    simpa [sq] using h
  have hodd_DV3 : ((D * V) ^ 3).trace = 0 := by
    have h := hodd3 (D * V) (D * V) (D * V) (by rw [hJDVJ]; simp)
    simpa [mat_pow_three] using h
  -- Step 1: Expand threeW32 Λ m D M - threeW32 Λ m D M0
  have hcube_A : ((X0 + X1 + X2) ^ 3).trace =
      (X0 ^ 3).trace + 3 * (X0 ^ 2 * X2).trace + 3 * (X0 * X1 ^ 2).trace +
      3 * (X0 * X2 ^ 2).trace + 3 * (X1 ^ 2 * X2).trace + (X2 ^ 3).trace := by
    have hexp := ring_add3_pow_three X0 X1 X2
    rw [hexp]; simp only [Matrix.trace_add]
    have cyc3 : ∀ U W : Mat n, (U * W * U).trace = (U ^ 2 * W).trace := fun U W => by
      rw [Matrix.trace_mul_comm (U * W) U]; apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
    have cyc3b : ∀ U W : Mat n, (W * U ^ 2).trace = (U ^ 2 * W).trace := fun U W => Matrix.trace_mul_comm _ _
    have cyc_a : (X0 * X1 * X2).trace = (X2 * X0 * X1).trace := by
      rw [Matrix.trace_mul_comm (X0 * X1) X2, ← Matrix.mul_assoc]
    have cyc_b : (X1 * X0 * X2).trace = (X0 * X2 * X1).trace := by
      rw [Matrix.mul_assoc X1 X0 X2, Matrix.trace_mul_comm X1 (X0 * X2)]
    have cyc_c : (X1 * X2 * X0).trace = (X2 * X0 * X1).trace := by
      rw [Matrix.mul_assoc X1 X2 X0, Matrix.trace_mul_comm X1 (X2 * X0)]
    have cyc_d : (X2 * X1 * X0).trace = (X0 * X2 * X1).trace := by
      rw [Matrix.trace_mul_comm (X2 * X1) X0, ← Matrix.mul_assoc]
    rw [cyc3 X0 X2, cyc3b X0 X2, cyc3 X1 X0, cyc3b X1 X0,
      cyc3 X2 X0, cyc3b X2 X0, cyc3 X1 X2, cyc3b X1 X2,
      cyc3 X0 X1, cyc3b X0 X1, cyc3 X2 X1, cyc3b X2 X1,
      cyc_a, cyc_b, cyc_c, cyc_d,
      hodd_X02X1, hodd_X0X2X1, hodd_X2X0X1, hodd_X22X1, hodd_X13]
    have hX12X0 : (X1 ^ 2 * X0).trace = (X0 * X1 ^ 2).trace := Matrix.trace_mul_comm _ _
    have hX22X0 : (X2 ^ 2 * X0).trace = (X0 * X2 ^ 2).trace := Matrix.trace_mul_comm _ _
    rw [hX12X0, hX22X0]; ring
  have hcube_DM : ((D * M) ^ 3).trace = ((D * M0) ^ 3).trace + 3 * (D * M0 * D * X2).trace := by
    have hDM : D * M = D * M0 + D * V := by rw [hM_split, Matrix.mul_add]
    rw [hDM]
    have hexp := ring_add_pow_three_sq (D * M0) (D * V)
    rw [hexp]; simp only [Matrix.trace_add]
    have cyc3 : ∀ U W : Mat n, (U * W * U).trace = (U ^ 2 * W).trace := fun U W => by
      rw [Matrix.trace_mul_comm (U * W) U]; apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
    have cyc3b : ∀ U W : Mat n, (W * U ^ 2).trace = (U ^ 2 * W).trace := fun U W => Matrix.trace_mul_comm _ _
    rw [cyc3 (D * M0) (D * V), cyc3b (D * M0) (D * V),
      cyc3 (D * V) (D * M0), cyc3b (D * V) (D * M0),
      hodd_DM02_DV, hodd_DV3]
    have hDV2 : ((D * V) ^ 2 * (D * M0)).trace = (D * M0 * D * X2).trace := by
      calc ((D * V) ^ 2 * (D * M0)).trace = ((D * M0) * (D * V) ^ 2).trace := Matrix.trace_mul_comm _ _
        _ = (D * M0 * D * X2).trace := by dsimp [X2]; apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
    rw [hDV2]; ring
  have hstep1 : threeW32 Λ m D M - threeW32 Λ m D M0 =
      3 * (X0 ^ 2 * X2).trace.re + 3 * (X0 * X1 ^ 2).trace.re - 6 * Λ * (D * M0 * D * X2).trace.re +
      3 * (X0 * X2 ^ 2).trace.re + 3 * (X1 ^ 2 * X2).trace.re + (X2 ^ 3).trace.re := by
    unfold threeW32
    rw [hA_split]
    have h1 := congrArg Complex.re hcube_A
    have h2 := congrArg Complex.re hcube_DM
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at h1 h2
    rw [h1, h2]; dsimp [X0]; ring
  -- Step 2: Stationarity Tr(((D + M D M)² - Λ D M D) * (X1 + 2 X2)) = 0!
  have hstat : 2 * (X0 ^ 2 * X2).trace.re + 2 * (X0 * X1 ^ 2).trace.re +
      4 * (X0 * X2 ^ 2).trace.re + 4 * (X1 ^ 2 * X2).trace.re + 2 * (X2 ^ 3).trace.re -
      4 * Λ * (D * M0 * D * X2).trace.re = 0 := by
    have h0 : (((D + M * D * M) ^ 2 - (Λ : ℂ) • (D * M * D)) * (X1 + (2 : ℂ) • X2)).trace = 0 := by
      rw [hEq, sub_self, Matrix.zero_mul, Matrix.trace_zero]
    have hL : ((D + M * D * M) ^ 2 * (X1 + (2 : ℂ) • X2)).trace =
        2 * (X0 ^ 2 * X2).trace + 2 * (X0 * X1 ^ 2).trace +
        4 * (X0 * X2 ^ 2).trace + 4 * (X1 ^ 2 * X2).trace + 2 * (X2 ^ 3).trace := by
      rw [hA_split, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      have h1 : ((X0 + X1 + X2) ^ 2 * X1).trace =
          2 * (X0 * X1 ^ 2).trace + 2 * (X1 ^ 2 * X2).trace := by
        have hexp := ring_add3_sq_mul_X1 X0 X1 X2
        rw [hexp]; simp only [Matrix.trace_add]
        have c1 : (X1 * X0 * X1).trace = (X0 * X1 ^ 2).trace := by
          calc (X1 * X0 * X1).trace = (X1 * (X1 * X0)).trace := Matrix.trace_mul_comm _ _
            _ = (X1 ^ 2 * X0).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = (X0 * X1 ^ 2).trace := Matrix.trace_mul_comm _ _
        have c2 : (X1 * X2 * X1).trace = (X1 ^ 2 * X2).trace := by
          rw [Matrix.trace_mul_comm (X1 * X2) X1]; apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        have c3 : (X2 * X1 ^ 2).trace = (X1 ^ 2 * X2).trace := Matrix.trace_mul_comm _ _
        rw [hodd_X02X1, hodd_X0X2X1, hodd_X13, hodd_X2X0X1, hodd_X22X1, c1, c2, c3]; ring
      have h2 : ((X0 + X1 + X2) ^ 2 * X2).trace =
          (X0 ^ 2 * X2).trace + (X1 ^ 2 * X2).trace + 2 * (X0 * X2 ^ 2).trace + (X2 ^ 3).trace := by
        have hexp := ring_add3_sq_mul_X2 X0 X1 X2
        rw [hexp]; simp only [Matrix.trace_add]
        have o1 : (X0 * X1 * X2).trace = 0 := by rw [Matrix.trace_mul_comm (X0 * X1) X2, ← Matrix.mul_assoc]; exact hodd_X2X0X1
        have o2 : (X1 * X0 * X2).trace = 0 := by
          calc (X1 * X0 * X2).trace = (X1 * (X0 * X2)).trace := by simp only [Matrix.mul_assoc]
            _ = (X0 * X2 * X1).trace := Matrix.trace_mul_comm _ _
            _ = 0 := hodd_X0X2X1
        have o3 : (X1 * X2 ^ 2).trace = 0 := by rw [Matrix.trace_mul_comm]; exact hodd_X22X1
        have o4 : (X2 * X1 * X2).trace = 0 := by
          calc (X2 * X1 * X2).trace = (X2 * (X2 * X1)).trace := Matrix.trace_mul_comm _ _
            _ = (X2 ^ 2 * X1).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = 0 := hodd_X22X1
        have c1 : (X2 * X0 * X2).trace = (X0 * X2 ^ 2).trace := by
          calc (X2 * X0 * X2).trace = (X2 * (X2 * X0)).trace := Matrix.trace_mul_comm _ _
            _ = (X2 ^ 2 * X0).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
            _ = (X0 * X2 ^ 2).trace := Matrix.trace_mul_comm _ _
        rw [o1, o2, o3, o4, c1]; ring
      rw [h1, h2]; ring
    have hR : ((D * M * D) * (X1 + (2 : ℂ) • X2)).trace = 4 * (D * M0 * D * X2).trace := by
      have hX12 : X1 + (2 : ℂ) • X2 = M * D * V + V * D * M := by
        rw [hM_split]; dsimp [X1, X2]
        rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]; exact ring_p32_X12 D M0 V
      rw [hX12, Matrix.mul_add, Matrix.trace_add]
      have hsym : ((D * M * D) * (V * D * M)).trace = ((D * M * D) * (M * D * V)).trace := by
        calc ((D * M * D) * (V * D * M)).trace = ((D * M * D * V * D) * M).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
          _ = (M * (D * M * D * V * D)).trace := Matrix.trace_mul_comm _ _
          _ = ((M * D * M * D * V) * D).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
          _ = (D * (M * D * M * D * V)).trace := Matrix.trace_mul_comm _ _
          _ = ((D * M * D) * (M * D * V)).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      rw [hsym, hM_split]
      have hexp := ring_p32_DM_expand D M0 V
      rw [hexp]; simp only [Matrix.trace_add, hodd_DM02_DV, hodd_DV3, zero_add, add_zero]
      have c1 : (D * M0 * D * V * D * V).trace = (D * M0 * D * X2).trace := by
        dsimp [X2]; apply tr_eq; simp only [Matrix.mul_assoc]
      have c2 : (D * V * D * M0 * D * V).trace = (D * M0 * D * X2).trace := by
        calc (D * V * D * M0 * D * V).trace = ((D * V) * (D * M0 * D * V)).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
          _ = ((D * M0 * D * V) * (D * V)).trace := Matrix.trace_mul_comm _ _
          _ = (D * M0 * D * X2).trace := by dsimp [X2]; apply tr_eq; simp only [Matrix.mul_assoc]
      rw [c1, c2]; ring
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hL, hR] at h0
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.zero_re, zero_mul, sub_zero] at hre
    linarith
  -- Step 3: Block additivity threeW32 Λ m D M0 = threeW32 (P D P) (P M P) + threeW32 (Q D Q) (Q M Q)
  have hblock : threeW32 Λ m D M0 =
      threeW32 Λ m (P * D * P) (P * M * P) + threeW32 Λ m (Q * D * Q) (Q * M * Q) := by
    unfold threeW32
    have zPQ : ∀ A B : Mat n, (P * A * P) * (Q * B * Q) = 0 := fun A B => by
      calc (P * A * P) * (Q * B * Q) = P * A * (P * Q) * B * Q := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPQ]; simp
    have zQP : ∀ A B : Mat n, (Q * A * Q) * (P * B * P) = 0 := fun A B => by
      calc (Q * A * Q) * (P * B * P) = Q * A * (Q * P) * B * P := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQP]; simp
    have hD3 : D ^ 3 = (P * D * P) ^ 3 + (Q * D * Q) ^ 3 := by
      conv_lhs => rw [hD_split]
      exact orth_block_add_pow (zPQ D D) (zQP D D) 3 (by norm_num)
    have hDM0 : D * M0 = (P * D * P) * (P * M * P) + (Q * D * Q) * (Q * M * Q) := by
      conv_lhs => rw [hD_split]
      dsimp [M0]; simp only [Matrix.add_mul, Matrix.mul_add, zPQ, zQP, add_zero, zero_add]
    have hDM03 : (D * M0) ^ 3 =
        ((P * D * P) * (P * M * P)) ^ 3 + ((Q * D * Q) * (Q * M * Q)) ^ 3 := by
      rw [hDM0]
      have z1 : ((P * D * P) * (P * M * P)) * ((Q * D * Q) * (Q * M * Q)) = 0 := by
        calc _ = (P * D * P) * ((P * M * P) * (Q * D * Q)) * (Q * M * Q) := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [zPQ M D]; simp
      have z2 : ((Q * D * Q) * (Q * M * Q)) * ((P * D * P) * (P * M * P)) = 0 := by
        calc _ = (Q * D * Q) * ((Q * M * Q) * (P * D * P)) * (P * M * P) := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [zQP M D]; simp
      exact orth_block_add_pow z1 z2 3 (by norm_num)
    have hM0DM0 : M0 * D * M0 =
        (P * M * P) * (P * D * P) * (P * M * P) + (Q * M * Q) * (Q * D * Q) * (Q * M * Q) := by
      rw [Matrix.mul_assoc, hDM0]; dsimp [M0]
      simp only [Matrix.add_mul, Matrix.mul_add]
      have z1 : (P * M * P) * ((Q * D * Q) * (Q * M * Q)) = 0 := by
        rw [← Matrix.mul_assoc, zPQ M D, Matrix.zero_mul]
      have z2 : (Q * M * Q) * ((P * D * P) * (P * M * P)) = 0 := by
        rw [← Matrix.mul_assoc, zQP M D, Matrix.zero_mul]
      rw [z1, z2, add_zero, zero_add]; simp only [Matrix.mul_assoc]
    have hA0_bl : D + M0 * D * M0 =
        (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) +
        (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) := by
      calc D + M0 * D * M0
          = (P * D * P + Q * D * Q) +
              ((P * M * P) * (P * D * P) * (P * M * P) + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) :=
            congrArg₂ (· + ·) hD_split hM0DM0
        _ = (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) +
              (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) := by abel
    have hA03 : (D + M0 * D * M0) ^ 3 =
        (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) ^ 3 +
        (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) ^ 3 := by
      rw [hA0_bl]
      have z1 : (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) *
          (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) = 0 := by
        simp only [Matrix.add_mul, Matrix.mul_add]
        have a1 : (P * D * P) * ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) = 0 := by
          calc _ = ((P * D * P) * (Q * M * Q)) * (Q * D * Q) * (Q * M * Q) := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [zPQ D M]; simp
        have a2 : ((P * M * P) * (P * D * P) * (P * M * P)) * (Q * D * Q) = 0 := by
          calc _ = (P * M * P) * (P * D * P) * ((P * M * P) * (Q * D * Q)) := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [zPQ M D]; simp
        have a3 : ((P * M * P) * (P * D * P) * (P * M * P)) * ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) = 0 := by
          calc _ = (P * M * P) * (P * D * P) * ((P * M * P) * (Q * M * Q)) * (Q * D * Q) * (Q * M * Q) := by
                simp only [Matrix.mul_assoc]
            _ = 0 := by rw [zPQ M M]; simp
        rw [zPQ D D, a1, a2, a3]; simp
      have z2 : (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) *
          (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) = 0 := by
        simp only [Matrix.add_mul, Matrix.mul_add]
        have a1 : (Q * D * Q) * ((P * M * P) * (P * D * P) * (P * M * P)) = 0 := by
          calc _ = ((Q * D * Q) * (P * M * P)) * (P * D * P) * (P * M * P) := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [zQP D M]; simp
        have a2 : ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) * (P * D * P) = 0 := by
          calc _ = (Q * M * Q) * (Q * D * Q) * ((Q * M * Q) * (P * D * P)) := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [zQP M D]; simp
        have a3 : ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) * ((P * M * P) * (P * D * P) * (P * M * P)) = 0 := by
          calc _ = (Q * M * Q) * (Q * D * Q) * ((Q * M * Q) * (P * M * P)) * (P * D * P) * (P * M * P) := by
                simp only [Matrix.mul_assoc]
            _ = 0 := by rw [zQP M M]; simp
        rw [zQP D D, a1, a2, a3]; simp
      exact orth_block_add_pow z1 z2 3 (by norm_num)
    rw [hA03, hDM03, hD3]; simp only [Matrix.trace_add, Complex.add_re]; ring
  -- Step 4: Nonnegativity of all 3 subtracted terms!
  have hQh : Qᴴ = Q := by dsimp [Q]; rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP_herm.eq]
  have hM0_h : M0.IsHermitian := by
    rw [Matrix.IsHermitian]; dsimp [M0]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hP_herm.eq, hQh, hM.isHermitian.eq,
      Matrix.mul_assoc]
  have hV_h : V.IsHermitian := hM.isHermitian.sub hM0_h
  have hX0_psd : X0.PosSemidef := by
    dsimp [X0]
    have h1 : (M0 * D * M0).PosSemidef := by
      have : M0 * D * M0 = (M0 * posDefPow (1 / 2 : ℝ) hD) * (M0 * posDefPow (1 / 2 : ℝ) hD)ᴴ := by
        have hsq : posDefPow (1 / 2 : ℝ) hD * posDefPow (1 / 2 : ℝ) hD = D := by
          rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
        rw [Matrix.conjTranspose_mul, (posDefPow_posDef (1 / 2) hD).isHermitian.eq, hM0_h.eq]
        calc M0 * D * M0 = M0 * (posDefPow (1 / 2 : ℝ) hD * posDefPow (1 / 2 : ℝ) hD) * M0 := by rw [hsq]
          _ = (M0 * posDefPow (1 / 2 : ℝ) hD) * (posDefPow (1 / 2 : ℝ) hD * M0) := by simp only [Matrix.mul_assoc]
      rw [this]; exact posSemidef_mul_conjTranspose_self _
    exact hD.posSemidef.add h1
  have hX1_h : X1.IsHermitian := by
    rw [Matrix.IsHermitian]; dsimp [X1]
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hM0_h.eq, hD.isHermitian.eq,
      hV_h.eq, Matrix.mul_assoc, add_comm]
  have hX2_psd : X2.PosSemidef := by
    dsimp [X2]
    have : V * D * V = (V * posDefPow (1 / 2 : ℝ) hD) * (V * posDefPow (1 / 2 : ℝ) hD)ᴴ := by
      have hsq : posDefPow (1 / 2 : ℝ) hD * posDefPow (1 / 2 : ℝ) hD = D := by
        rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
      rw [Matrix.conjTranspose_mul, (posDefPow_posDef (1 / 2) hD).isHermitian.eq, hV_h.eq]
      calc V * D * V = V * (posDefPow (1 / 2 : ℝ) hD * posDefPow (1 / 2 : ℝ) hD) * V := by rw [hsq]
        _ = (V * posDefPow (1 / 2 : ℝ) hD) * (posDefPow (1 / 2 : ℝ) hD * V) := by simp only [Matrix.mul_assoc]
    rw [this]; exact posSemidef_mul_conjTranspose_self _
  have hnn1 : 0 ≤ (X0 * X2 ^ 2).trace.re :=
    trace_re_posSemidef_mul_nonneg hX0_psd (posSemidef_sq hX2_psd.isHermitian)
  have hnn2 : 0 ≤ (X1 ^ 2 * X2).trace.re :=
    trace_re_posSemidef_mul_nonneg (posSemidef_sq hX1_h) hX2_psd
  have hnn3 : 0 ≤ (X2 ^ 3).trace.re := by
    have : X2 ^ 3 = X2 ^ 2 * X2 := by simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
    rw [this]
    exact trace_re_posSemidef_mul_nonneg (posSemidef_sq hX2_psd.isHermitian) hX2_psd
  exact ⟨by linarith [hstep1, hstat, hblock], hnn1, hnn2, hnn3⟩

/-! ==========================================================================
    PART 5: Exact Action-Ray Convexity at p = 4/3 and p = 3/2
    ========================================================================== -/

/-- Action-ray function at p = 4/3 (κ = 2): g(t) = t⁻¹ Re Tr(H (D + t H)³). -/
def actionRayG43 {n : ℕ} (D H : Mat n) (t : ℝ) : ℝ :=
  t⁻¹ * (H * (D + (t : ℂ) • H) ^ 3).trace.re

/-- Action-ray function at p = 3/2 (κ = 3/2): g(t) = t⁻¹/² Re Tr(H (D + t H)²). -/
def actionRayG32 {n : ℕ} (D H : Mat n) (t : ℝ) : ℝ :=
  t ^ (-(1 / 2 : ℝ)) * (H * (D + (t : ℂ) • H) ^ 2).trace.re

/-- Eigenbasis double-sum formula: Re Tr(D^a H^b) = ∑_{i, j} ‖(U_Dᴴ U_H)_{ij}‖² d_i^a h_j^b. -/
private lemma trace_re_pow_mul_pow_spec {n : ℕ} {D H : Mat n}
    (hD : D.IsHermitian) (hH : H.IsHermitian) (a b : ℕ) :
    let Q := (hD.eigenvectorUnitary : Mat n)ᴴ * (hH.eigenvectorUnitary : Mat n)
    (D ^ a * H ^ b).trace.re =
      ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (hD.eigenvalues i) ^ a * (hH.eigenvalues j) ^ b := by
  intro Q
  let UD := hD.eigenvectorUnitary
  let UH := hH.eigenvectorUnitary
  have hpow : ∀ {A : Mat n} (hA : A.IsHermitian) (k : ℕ),
      A ^ k = (hA.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i ^ k : ℝ) : ℂ)) * (hA.eigenvectorUnitary : Mat n)ᴴ := by
    intro A hA k
    induction k with
    | zero =>
        simp only [pow_zero, Complex.ofReal_one, Matrix.diagonal_one, Matrix.mul_one,
          unitary_mul_conjTranspose_self]
    | succ k ih =>
        have hA1 : A = (hA.eigenvectorUnitary : Mat n) *
            Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * (hA.eigenvectorUnitary : Mat n)ᴴ := by
          simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
            using hA.spectral_theorem
        rw [pow_succ, ih]
        conv_lhs => rhs; rw [hA1]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (hA.eigenvectorUnitary : Mat n)ᴴ (hA.eigenvectorUnitary : Mat n),
          unitary_conjTranspose_mul_self, Matrix.one_mul,
          ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
        congr 2; ext i j
        by_cases hij : i = j
        · subst hij; simp [Matrix.diagonal, pow_succ]
        · simp [Matrix.diagonal, hij]
  rw [hpow hD a, hpow hH b]
  have hQH : (UH : Mat n)ᴴ * (UD : Mat n) = Qᴴ := by
    change (UH : Mat n)ᴴ * (UD : Mat n) = ((UD : Mat n)ᴴ * (UH : Mat n))ᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hcyc : ((UD : Mat n) * Matrix.diagonal (fun i => ((hD.eigenvalues i ^ a : ℝ) : ℂ)) * (UD : Mat n)ᴴ *
      ((UH : Mat n) * Matrix.diagonal (fun j => ((hH.eigenvalues j ^ b : ℝ) : ℂ)) * (UH : Mat n)ᴴ)).trace =
      (Matrix.diagonal (fun i => ((hD.eigenvalues i ^ a : ℝ) : ℂ)) * Q *
       Matrix.diagonal (fun j => ((hH.eigenvalues j ^ b : ℝ) : ℂ)) * Qᴴ).trace := by
    calc _ = ((UD : Mat n) * (Matrix.diagonal (fun i => ((hD.eigenvalues i ^ a : ℝ) : ℂ)) * Q *
              Matrix.diagonal (fun j => ((hH.eigenvalues j ^ b : ℝ) : ℂ)) * (UH : Mat n)ᴴ)).trace := by
              dsimp [Q, UD, UH]; simp only [Matrix.mul_assoc]
      _ = ((Matrix.diagonal (fun i => ((hD.eigenvalues i ^ a : ℝ) : ℂ)) * Q *
              Matrix.diagonal (fun j => ((hH.eigenvalues j ^ b : ℝ) : ℂ)) * (UH : Mat n)ᴴ) * (UD : Mat n)).trace :=
            Matrix.trace_mul_comm _ _
      _ = (Matrix.diagonal (fun i => ((hD.eigenvalues i ^ a : ℝ) : ℂ)) * Q *
              Matrix.diagonal (fun j => ((hH.eigenvalues j ^ b : ℝ) : ℂ)) * Qᴴ).trace := by
            rw [Matrix.mul_assoc _ (UH : Mat n)ᴴ (UD : Mat n), hQH]
  rw [hcyc, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ((hD.eigenvalues i ^ a : ℝ) : ℂ) * Q i j * ((hH.eigenvalues j ^ b : ℝ) : ℂ) * star (Q i j) =
      (((hD.eigenvalues i ^ a * hH.eigenvalues j ^ b : ℝ) : ℂ)) * (Q i j * star (Q i j)) := by
    push_cast; ring
  rw [h1, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  ring

/-- Exact Action-Ray Convexity at p = 4/3 (`#17.1`, `ver_audit.md` §10.1):
    For ALL n ≥ 1, D, H ≻ 0, and t > 0:
      g(t) = t⁻¹ Re Tr(H (D + t H)³) is twice differentiable at t,
      t² g''(t) ≥ (1/2) g(t) > 0, and g''(t) > 0 strictly! -/
theorem action_ray_convexity_p43 {n : ℕ} (hn : 1 ≤ n) {D H : Mat n}
    (hD : D.PosDef) (hH : H.PosDef) {t : ℝ} (ht : 0 < t) :
    let g := actionRayG43 D H
    let c0 := (D ^ 3 * H).trace.re
    let c2 := 3 * (D * H ^ 3).trace.re
    let c3 := (H ^ 4).trace.re
    let g' := fun s : ℝ => -s⁻¹ ^ 2 * c0 + c2 + 2 * s * c3
    let g'' := fun s : ℝ => 2 * s⁻¹ ^ 3 * c0 + 2 * c3
    HasDerivAt g (g' t) t ∧
    HasDerivAt g' (g'' t) t ∧
    0 < g t ∧
    (1 / 2 : ℝ) * g t ≤ t ^ 2 * g'' t ∧
    0 < g'' t := by
  intro g c0 c2 c3 g' g''
  set c1 : ℝ := 2 * (D ^ 2 * H ^ 2).trace.re + (D * H * D * H).trace.re
  -- Explicit Laurent expansion of g(s) for all s ≠ 0
  have hg_eq : ∀ s : ℝ, s ≠ 0 → g s = s⁻¹ * c0 + c1 + s * c2 + s ^ 2 * c3 := by
    intro s hs
    change s⁻¹ * (H * (D + (s : ℂ) • H) ^ 3).trace.re = _
    have hcube : H * (D + (s : ℂ) • H) ^ 3 =
        H * D ^ 3 + (s : ℂ) • (H * D ^ 2 * H + H * D * H * D + H ^ 2 * D ^ 2) +
        ((s ^ 2 : ℝ) : ℂ) • (H * D * H ^ 2 + H ^ 2 * D * H + H ^ 3 * D) +
        ((s ^ 3 : ℝ) : ℂ) • H ^ 4 := by
      have h3 : (D + (s : ℂ) • H) ^ 3 =
          (D + (s : ℂ) • H) * (D + (s : ℂ) • H) * (D + (s : ℂ) • H) := by
        exact mat_pow_three _
      rw [h3]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      have p2 : ((s ^ 2 : ℝ) : ℂ) = (s : ℂ) * (s : ℂ) := by push_cast; ring
      have p3 : ((s ^ 3 : ℝ) : ℂ) = (s : ℂ) * ((s : ℂ) * (s : ℂ)) := by push_cast; ring
      rw [p2, p3]
      simp only [mat_pow_two, mat_pow_three, mat_pow_four, Matrix.mul_assoc]; abel
    rw [hcube]
    have hHD3 : (H * D ^ 3).trace = (D ^ 3 * H).trace := Matrix.trace_mul_comm _ _
    have hHD2H : (H * D ^ 2 * H).trace = (D ^ 2 * H ^ 2).trace := by
      calc (H * D ^ 2 * H).trace = (H * (H * D ^ 2)).trace := Matrix.trace_mul_comm _ _
        _ = (H ^ 2 * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D ^ 2 * H ^ 2).trace := Matrix.trace_mul_comm _ _
    have hHDHD : (H * D * H * D).trace = (D * H * D * H).trace := by
      rw [Matrix.trace_mul_comm (H * D * H) D]; apply tr_eq; simp only [Matrix.mul_assoc]
    have hH2D2 : (H ^ 2 * D ^ 2).trace = (D ^ 2 * H ^ 2).trace := Matrix.trace_mul_comm _ _
    have hHDH2 : (H * D * H ^ 2).trace = (D * H ^ 3).trace := by
      calc (H * D * H ^ 2).trace = (H ^ 2 * (H * D)).trace := Matrix.trace_mul_comm _ _
        _ = (H ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
        _ = (D * H ^ 3).trace := Matrix.trace_mul_comm _ _
    have hH2DH : (H ^ 2 * D * H).trace = (D * H ^ 3).trace := by
      calc (H ^ 2 * D * H).trace = (H * (H ^ 2 * D)).trace := Matrix.trace_mul_comm _ _
        _ = (H ^ 3 * D).trace := by apply tr_eq; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]
        _ = (D * H ^ 3).trace := Matrix.trace_mul_comm _ _
    have hH3D : (H ^ 3 * D).trace = (D * H ^ 3).trace := Matrix.trace_mul_comm _ _
    simp only [Matrix.trace_add, trace_re_smul_real, Complex.add_re,
      hHD3, hHD2H, hHDHD, hH2D2, hHDH2, hH2DH, hH3D]
    dsimp [c0, c1, c2, c3]
    field_simp [hs]; ring
  have hd1 : HasDerivAt g (g' t) t := by
    have hf : HasDerivAt (fun s : ℝ => s⁻¹ * c0 + c1 + s * c2 + s ^ 2 * c3) (g' t) t := by
      have h1 : HasDerivAt (fun s : ℝ => s⁻¹ * c0) (-(t ^ 2)⁻¹ * c0) t :=
        (hasDerivAt_inv ht.ne').mul_const c0
      have h2 : HasDerivAt (fun s : ℝ => s⁻¹ * c0 + c1) (-(t ^ 2)⁻¹ * c0 + 0) t :=
        h1.add (hasDerivAt_const t c1)
      have h3 : HasDerivAt (fun s : ℝ => s * c2) (1 * c2) t := (hasDerivAt_id t).mul_const c2
      have h4 : HasDerivAt (fun s : ℝ => s ^ 2 * c3) (2 * t ^ (2 - 1) * c3) t :=
        (hasDerivAt_pow 2 t).mul_const c3
      refine ((h2.add h3).add h4).congr_deriv ?_
      dsimp [g']; rw [inv_pow]; ring
    have hev : (fun s : ℝ => s⁻¹ * c0 + c1 + s * c2 + s ^ 2 * c3) =ᶠ[nhds t] g := by
      filter_upwards [eventually_ne_nhds ht.ne'] with s hs
      exact (hg_eq s hs).symm
    exact hf.congr_of_eventuallyEq hev.symm
  have hd2 : HasDerivAt g' (g'' t) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(s⁻¹) ^ 2 * c0) (-(2 * t⁻¹ ^ 1 * (-(t ^ 2)⁻¹)) * c0) t := by
      have hinv := hasDerivAt_inv ht.ne'
      have hsq := hinv.pow 2
      simpa using (hsq.neg).mul_const c0
    have h2 : HasDerivAt (fun s : ℝ => -s⁻¹ ^ 2 * c0 + c2) (-(2 * t⁻¹ ^ 1 * (-(t ^ 2)⁻¹)) * c0 + 0) t :=
      h1.add (hasDerivAt_const t c2)
    have h3 : HasDerivAt (fun s : ℝ => 2 * s * c3) (2 * 1 * c3) t := by
      have := ((hasDerivAt_id t).const_mul 2).mul_const c3
      simpa [mul_assoc] using this
    refine (h2.add h3).congr_deriv ?_
    dsimp [g'']; field_simp [ht.ne']; ring
  -- Positivity of g(t)
  have hg_pos : 0 < g t := by
    change 0 < t⁻¹ * (H * (D + (t : ℂ) • H) ^ 3).trace.re
    have htH : ((t : ℂ) • H).PosDef := by
      have : (t : ℂ) • H = t • H := by ext i j; simp [Complex.real_smul]
      rw [this]; exact hH.smul ht
    have hcube_pd : ((D + (t : ℂ) • H) ^ 3).PosDef := posDef_pow (hD.add htH) 3
    exact mul_pos (inv_pos.mpr ht) (trace_re_posDef_mul_pos hn hH hcube_pd)
  -- Sharp inequality t² g''(t) - (1/2) g(t) = (1/4)‖[D, H]‖² + (3/(2t)) ∑ ‖Q_ij‖² h_j (d_i - t h_j)² (d_i + t h_j) ≥ 0
  have hsharp : (1 / 2 : ℝ) * g t ≤ t ^ 2 * g'' t := by
    rw [hg_eq t ht.ne']
    have hcomm : hsNormSq (D * H - H * D) = 2 * (D ^ 2 * H ^ 2).trace.re - 2 * (D * H * D * H).trace.re := by
      unfold hsNormSq
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        hD.isHermitian.eq, hH.isHermitian.eq]
      have h1 : (H * D * (D * H)).trace = (D ^ 2 * H ^ 2).trace := by
        calc (H * D * (D * H)).trace = ((H * D ^ 2) * H).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
          _ = (H * (H * D ^ 2)).trace := Matrix.trace_mul_comm _ _
          _ = (H ^ 2 * D ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
          _ = (D ^ 2 * H ^ 2).trace := Matrix.trace_mul_comm _ _
      have h2 : (D * H * (H * D)).trace = (D ^ 2 * H ^ 2).trace := by
        calc (D * H * (H * D)).trace = ((D * H ^ 2) * D).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
          _ = (D * (D * H ^ 2)).trace := Matrix.trace_mul_comm _ _
          _ = (D ^ 2 * H ^ 2).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
      have h3 : (H * D * (H * D)).trace = (D * H * D * H).trace := by
        calc (H * D * (H * D)).trace = ((H * D * H) * D).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
          _ = (D * (H * D * H)).trace := Matrix.trace_mul_comm _ _
          _ = (D * H * D * H).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      have h4 : (D * H * (D * H)).trace = (D * H * D * H).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, h1, h2, h3, h4, Complex.sub_re]
      ring
    let Q := (hD.isHermitian.eigenvectorUnitary : Mat n)ᴴ * (hH.isHermitian.eigenvectorUnitary : Mat n)
    let dv := hD.isHermitian.eigenvalues
    let hv := hH.isHermitian.eigenvalues
    have hsum_nn : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        ‖Q i j‖ ^ 2 * hv j * (dv i - t * hv j) ^ 2 * (dv i + t * hv j) := by
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
      have hdi : 0 < dv i := hD.eigenvalues_pos i
      have hhj : 0 < hv j := hH.eigenvalues_pos j
      positivity
    have hsum_eq : (∑ i : Fin n, ∑ j : Fin n,
        ‖Q i j‖ ^ 2 * hv j * (dv i - t * hv j) ^ 2 * (dv i + t * hv j)) =
        (D ^ 3 * H).trace.re - t * (D ^ 2 * H ^ 2).trace.re -
        t ^ 2 * (D * H ^ 3).trace.re + t ^ 3 * (H ^ 4).trace.re := by
      have s31 := trace_re_pow_mul_pow_spec hD.isHermitian hH.isHermitian 3 1
      have s22 := trace_re_pow_mul_pow_spec hD.isHermitian hH.isHermitian 2 2
      have s13 := trace_re_pow_mul_pow_spec hD.isHermitian hH.isHermitian 1 3
      have s04 := trace_re_pow_mul_pow_spec hD.isHermitian hH.isHermitian 0 4
      dsimp only at s31 s22 s13 s04
      rw [pow_one] at s31 s13
      rw [pow_zero, Matrix.one_mul] at s04
      rw [s31, s22, s13, s04]
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      dsimp [Q, dv, hv]; ring
    have hdiff : t ^ 2 * g'' t - (1 / 2 : ℝ) * (t⁻¹ * c0 + c1 + t * c2 + t ^ 2 * c3) =
        (1 / 4 : ℝ) * hsNormSq (D * H - H * D) +
        (3 / (2 * t)) * (∑ i : Fin n, ∑ j : Fin n,
          ‖Q i j‖ ^ 2 * hv j * (dv i - t * hv j) ^ 2 * (dv i + t * hv j)) := by
      rw [hcomm, hsum_eq]
      dsimp [g'', c0, c1, c2, c3]
      field_simp [ht.ne']; ring
    have hrhs_nn : 0 ≤ (1 / 4 : ℝ) * hsNormSq (D * H - H * D) +
        (3 / (2 * t)) * (∑ i : Fin n, ∑ j : Fin n,
          ‖Q i j‖ ^ 2 * hv j * (dv i - t * hv j) ^ 2 * (dv i + t * hv j)) :=
      add_nonneg (mul_nonneg (by norm_num) (hsNormSq_nonneg _))
        (mul_nonneg (by positivity) hsum_nn)
    linarith
  have hg2_pos : 0 < g'' t := by
    have hpos : 0 < t ^ 2 * g'' t := by linarith
    exact pos_of_mul_pos_right hpos (sq_nonneg t)
  exact ⟨hd1, hd2, hg_pos, hsharp, hg2_pos⟩

/-- Exact Action-Ray Convexity at p = 3/2 (`#17.1`, `ver_audit.md` §10.1):
    For ALL n ≥ 1, D, H ≻ 0, and t > 0:
      g(t) = t⁻¹/² Re Tr(H (D + t H)²) is twice differentiable at t,
      t² g''(t) = (1/4) g(t) + (1/2) t⁻¹/² ‖H^(1/2)(D - t H)‖_HS² ≥ (1/4) g(t) > 0,
      and g''(t) > 0 strictly! -/
theorem action_ray_convexity_p32 {n : ℕ} (hn : 1 ≤ n) {D H : Mat n}
    (hD : D.PosDef) (hH : H.PosDef) {t : ℝ} (ht : 0 < t) :
    let g := actionRayG32 D H
    let c0 := (D ^ 2 * H).trace.re
    let c1 := 2 * (D * H ^ 2).trace.re
    let c2 := (H ^ 3).trace.re
    let g' := fun s : ℝ => -(1 / 2 : ℝ) * s ^ (-(3 / 2 : ℝ)) * c0 +
      (1 / 2 : ℝ) * s ^ (-(1 / 2 : ℝ)) * c1 + (3 / 2 : ℝ) * s ^ (1 / 2 : ℝ) * c2
    let g'' := fun s : ℝ => (3 / 4 : ℝ) * s ^ (-(5 / 2 : ℝ)) * c0 -
      (1 / 4 : ℝ) * s ^ (-(3 / 2 : ℝ)) * c1 + (3 / 4 : ℝ) * s ^ (-(1 / 2 : ℝ)) * c2
    HasDerivAt g (g' t) t ∧
    HasDerivAt g' (g'' t) t ∧
    0 < g t ∧
    t ^ 2 * g'' t = (1 / 4 : ℝ) * g t +
      (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) * hsNormSq (posDefPow (1 / 2 : ℝ) hH * (D - (t : ℂ) • H)) ∧
    (1 / 4 : ℝ) * g t ≤ t ^ 2 * g'' t ∧
    0 < g'' t := by
  intro g c0 c1 c2 g' g''
  have hg_eq : ∀ s : ℝ, 0 < s →
      g s = s ^ (-(1 / 2 : ℝ)) * c0 + s ^ (1 / 2 : ℝ) * c1 + s ^ (3 / 2 : ℝ) * c2 := by
    intro s hs
    change s ^ (-(1 / 2 : ℝ)) * (H * (D + (s : ℂ) • H) ^ 2).trace.re = _
    have hsq : H * (D + (s : ℂ) • H) ^ 2 =
        H * D ^ 2 + (s : ℂ) • (H * D * H + H ^ 2 * D) + ((s ^ 2 : ℝ) : ℂ) • H ^ 3 := by
      have h2 : (D + (s : ℂ) • H) ^ 2 = (D + (s : ℂ) • H) * (D + (s : ℂ) • H) := sq _
      rw [h2]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
      have p2 : ((s ^ 2 : ℝ) : ℂ) = (s : ℂ) * (s : ℂ) := by push_cast; ring
      rw [p2]; simp only [mat_pow_two, mat_pow_three, Matrix.mul_assoc]; abel
    rw [hsq]
    have hHD2 : (H * D ^ 2).trace = (D ^ 2 * H).trace := Matrix.trace_mul_comm _ _
    have hHDH : (H * D * H).trace = (D * H ^ 2).trace := by
      calc (H * D * H).trace = (H * (H * D)).trace := Matrix.trace_mul_comm _ _
        _ = (H ^ 2 * D).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D * H ^ 2).trace := Matrix.trace_mul_comm _ _
    have hH2D : (H ^ 2 * D).trace = (D * H ^ 2).trace := Matrix.trace_mul_comm _ _
    simp only [Matrix.trace_add, trace_re_smul_real, Complex.add_re, hHD2, hHDH, hH2D]
    dsimp [c0, c1, c2]
    have hp1 : s ^ (-(1 / 2 : ℝ)) * s = s ^ (1 / 2 : ℝ) := by
      calc s ^ (-(1 / 2 : ℝ)) * s = s ^ (-(1 / 2 : ℝ)) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = s ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add hs _ _).symm
        _ = s ^ (1 / 2 : ℝ) := by congr 1; norm_num
    have hp2 : s ^ (-(1 / 2 : ℝ)) * s ^ 2 = s ^ (3 / 2 : ℝ) := by
      calc s ^ (-(1 / 2 : ℝ)) * s ^ 2 = s ^ (-(1 / 2 : ℝ)) * s ^ (2 : ℝ) := by
              rw [← Real.rpow_natCast s 2]; norm_cast
        _ = s ^ (-(1 / 2 : ℝ) + 2) := (Real.rpow_add hs _ _).symm
        _ = s ^ (3 / 2 : ℝ) := by congr 1; norm_num
    linear_combination (2 * (D * H ^ 2).trace.re) * hp1 + (H ^ 3).trace.re * hp2
  have hd1 : HasDerivAt g (g' t) t := by
    have h1 := (Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')).mul_const c0
    have h2 := (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl ht.ne')).mul_const c1
    have h3 := (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ)) (Or.inl ht.ne')).mul_const c2
    have htot : HasDerivAt (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * c0 + s ^ (1 / 2 : ℝ) * c1 + s ^ (3 / 2 : ℝ) * c2)
        (g' t) t := by
      refine ((h1.add h2).add h3).congr_deriv ?_
      dsimp [g']; norm_num
    have hev : (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * c0 + s ^ (1 / 2 : ℝ) * c1 + s ^ (3 / 2 : ℝ) * c2) =ᶠ[nhds t] g := by
      filter_upwards [eventually_gt_nhds ht] with s hs
      exact (hg_eq s hs).symm
    exact htot.congr_of_eventuallyEq hev.symm
  have hd2 : HasDerivAt g' (g'' t) t := by
    have h1 := ((Real.hasDerivAt_rpow_const (p := -(3 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (-(1 / 2 : ℝ))).mul_const c0
    have h2 := ((Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (1 / 2 : ℝ)).mul_const c1
    have h3 := ((Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (3 / 2 : ℝ)).mul_const c2
    refine ((h1.add h2).add h3).congr_deriv ?_
    dsimp [g'']; norm_num; ring
  have hg_pos : 0 < g t := by
    change 0 < t ^ (-(1 / 2 : ℝ)) * (H * (D + (t : ℂ) • H) ^ 2).trace.re
    have htH : ((t : ℂ) • H).PosDef := by
      have : (t : ℂ) • H = t • H := by ext i j; simp [Complex.real_smul]
      rw [this]; exact hH.smul ht
    have hsq_pd : ((D + (t : ℂ) • H) ^ 2).PosDef := posDef_pow (hD.add htH) 2
    exact mul_pos (Real.rpow_pos_of_pos ht _) (trace_re_posDef_mul_pos hn hH hsq_pd)
  have hhs : hsNormSq (posDefPow (1 / 2 : ℝ) hH * (D - (t : ℂ) • H)) =
      c0 - t * c1 + t ^ 2 * c2 := by
    unfold hsNormSq
    let Hhalf := posDefPow (1 / 2 : ℝ) hH
    have hHh : Hhalfᴴ = Hhalf := (posDefPow_posDef (1 / 2) hH).isHermitian.eq
    have hHsq : Hhalf * Hhalf = H := by
      dsimp [Hhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hH
    have hadj : (Hhalf * (D - (t : ℂ) • H))ᴴ = (D - (t : ℂ) • H) * Hhalf := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Complex.star_def, Complex.conj_ofReal, hHh, hD.isHermitian.eq, hH.isHermitian.eq]
    rw [hadj]
    have hcyc : ((D - (t : ℂ) • H) * Hhalf * (Hhalf * (D - (t : ℂ) • H))).trace =
        ((D - (t : ℂ) • H) ^ 2 * H).trace := by
      calc _ = ((D - (t : ℂ) • H) * (Hhalf * Hhalf) * (D - (t : ℂ) • H)).trace := by
              simp only [Matrix.mul_assoc]
        _ = ((D - (t : ℂ) • H) * ((D - (t : ℂ) • H) * H)).trace := by
              rw [hHsq, Matrix.trace_mul_comm]
        _ = ((D - (t : ℂ) • H) ^ 2 * H).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
    rw [hcyc]
    have hsq : (D - (t : ℂ) • H) ^ 2 * H =
        D ^ 2 * H - (t : ℂ) • (D * H ^ 2 + H * D * H) + ((t ^ 2 : ℝ) : ℂ) • H ^ 3 := by
      have p2 : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) * (t : ℂ) := by push_cast; ring
      rw [sq, p2]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        smul_sub, smul_add, smul_smul, mat_pow_two, mat_pow_three, Matrix.mul_assoc]
      abel
    rw [hsq]
    have hHDH : (H * D * H).trace = (D * H ^ 2).trace := by
      calc (H * D * H).trace = (H * (H * D)).trace := Matrix.trace_mul_comm _ _
        _ = (H ^ 2 * D).trace := by apply tr_eq; simp only [mat_pow_two, Matrix.mul_assoc]
        _ = (D * H ^ 2).trace := Matrix.trace_mul_comm _ _
    simp only [Matrix.trace_add, Matrix.trace_sub, trace_re_smul_real, Complex.add_re, Complex.sub_re, hHDH]
    dsimp [c0, c1, c2]; ring
  have hid : t ^ 2 * g'' t = (1 / 4 : ℝ) * g t +
      (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) * hsNormSq (posDefPow (1 / 2 : ℝ) hH * (D - (t : ℂ) • H)) := by
    rw [hg_eq t ht, hhs]
    dsimp [g'']
    have hpA : t ^ 2 * t ^ (-(5 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
      calc t ^ 2 * t ^ (-(5 / 2 : ℝ)) = t ^ (2 : ℝ) * t ^ (-(5 / 2 : ℝ)) := by
              rw [← Real.rpow_natCast t 2]; norm_cast
        _ = t ^ ((2 : ℝ) + -(5 / 2 : ℝ)) := (Real.rpow_add ht _ _).symm
        _ = t ^ (-(1 / 2 : ℝ)) := by congr 1; norm_num
    have hpB : t ^ 2 * t ^ (-(3 / 2 : ℝ)) = t ^ (1 / 2 : ℝ) := by
      calc t ^ 2 * t ^ (-(3 / 2 : ℝ)) = t ^ (2 : ℝ) * t ^ (-(3 / 2 : ℝ)) := by
              rw [← Real.rpow_natCast t 2]; norm_cast
        _ = t ^ ((2 : ℝ) + -(3 / 2 : ℝ)) := (Real.rpow_add ht _ _).symm
        _ = t ^ (1 / 2 : ℝ) := by congr 1; norm_num
    have hpC : t ^ 2 * t ^ (-(1 / 2 : ℝ)) = t ^ (3 / 2 : ℝ) := by
      calc t ^ 2 * t ^ (-(1 / 2 : ℝ)) = t ^ (2 : ℝ) * t ^ (-(1 / 2 : ℝ)) := by
              rw [← Real.rpow_natCast t 2]; norm_cast
        _ = t ^ ((2 : ℝ) + -(1 / 2 : ℝ)) := (Real.rpow_add ht _ _).symm
        _ = t ^ (3 / 2 : ℝ) := by congr 1; norm_num
    have hpD : t ^ (-(1 / 2 : ℝ)) * t = t ^ (1 / 2 : ℝ) := by
      calc t ^ (-(1 / 2 : ℝ)) * t = t ^ (-(1 / 2 : ℝ)) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = t ^ (-(1 / 2 : ℝ) + 1) := (Real.rpow_add ht _ _).symm
        _ = t ^ (1 / 2 : ℝ) := by congr 1; norm_num
    linear_combination (3 / 4 * c0) * hpA - (1 / 4 * c1) * hpB + (3 / 4 * c2) * hpC +
      (1 / 2 * c1) * hpD - (1 / 2 * c2) * hpC
  have hsharp : (1 / 4 : ℝ) * g t ≤ t ^ 2 * g'' t := by
    rw [hid]
    have hnn : 0 ≤ (1 / 2 : ℝ) * t ^ (-(1 / 2 : ℝ)) *
        hsNormSq (posDefPow (1 / 2 : ℝ) hH * (D - (t : ℂ) • H)) :=
      mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg ht.le _)) (hsNormSq_nonneg _)
    linarith
  have hg2_pos : 0 < g'' t := by
    have hpos : 0 < t ^ 2 * g'' t := by linarith
    exact pos_of_mul_pos_right hpos (sq_nonneg t)
  exact ⟨hd1, hd2, hg_pos, hid, hsharp, hg2_pos⟩


/-! ==========================================================================
    PART 6: Exact 2×2 Negative Trace Drift (p = 4/3) &
            Unconditional Master-Trace ⟹ Global Optimality (Open Piece 1)
    ========================================================================== -/

/-- Trace bridge at p = 4/3: Re Tr(G² - D G D) = Re Tr(D H D H - D³ H) for G = D^(1/2) H D^(1/2). -/
lemma trace_re_Phi_p43_eq {n : ℕ} {D H : Mat n} (hD : D.PosDef) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let G := Dhalf * H * Dhalf
    (G ^ 2 - D * G * D).trace.re = (D * H * D * H - D ^ 3 * H).trace.re := by
  intro Dhalf G
  have hsq : Dhalf * Dhalf = D := by
    dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
  have h1 : (G ^ 2).trace = (D * H * D * H).trace := by
    rw [mat_pow_two]; exact trace_G_sq_eq_DHDH hD
  have h2 : (D * G * D).trace = (D ^ 3 * H).trace := by
    dsimp [G]
    calc (D * (Dhalf * H * Dhalf) * D).trace
        = ((D * Dhalf * H) * (Dhalf * D)).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = ((Dhalf * D) * (D * Dhalf * H)).trace := Matrix.trace_mul_comm _ _
      _ = (Dhalf * (D * D * Dhalf * H)).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = ((D * D * Dhalf * H) * Dhalf).trace := Matrix.trace_mul_comm _ _
      _ = (D * D * Dhalf * (H * Dhalf)).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = ((H * Dhalf) * (D * D * Dhalf)).trace := Matrix.trace_mul_comm _ _
      _ = (H * (Dhalf * D * D * Dhalf)).trace := by apply tr_eq; simp only [Matrix.mul_assoc]
      _ = (H * (D * D * (Dhalf * Dhalf))).trace := by
            have hcomm : Dhalf * D = D * Dhalf := (posDefPow_comm_self (1 / 2) hD).symm
            apply tr_eq
            calc H * (Dhalf * D * D * Dhalf)
                = H * ((Dhalf * D) * D * Dhalf) := by simp only [Matrix.mul_assoc]
              _ = H * ((D * Dhalf) * D * Dhalf) := by rw [hcomm]
              _ = H * (D * (Dhalf * D) * Dhalf) := by simp only [Matrix.mul_assoc]
              _ = H * (D * (D * Dhalf) * Dhalf) := by rw [hcomm]
              _ = H * (D * D * (Dhalf * Dhalf)) := by simp only [Matrix.mul_assoc]
      _ = (H * D ^ 3).trace := by rw [hsq]; apply tr_eq; simp only [mat_pow_three, Matrix.mul_assoc]
      _ = (D ^ 3 * H).trace := Matrix.trace_mul_comm _ _
  rw [Matrix.trace_sub, Matrix.trace_sub, h1, h2]

/-- Exact 2×2 Negative Trace Drift at p = 4/3 (`#6`, `ver_audit.md` §3(b)):
    For ALL Λ > 0, ALL 0 < d < 1, and EVERY irreducible 2×2 PosDef solution H (H₀₁ ≠ 0)
    of (D + H)³ = Λ D H D with D = diag(1, d):
      (i)   H₁₁ < 1/2 strictly,
      (ii)  H₀₀ = d (1 - H₁₁) identically,
      (iii) Re Tr(Φ) = Re Tr(D H D H - D³ H) < -(1/2) d (1 - d)² < 0 strictly! -/
theorem negative_trace_drift_2x2_p43 {Λ d : ℝ} (hΛ : 0 < Λ) (hd0 : 0 < d) (hd1 : d < 1)
    {H : Mat 2} (hH : H.PosDef) (hc_ne : H 0 1 ≠ 0)
    (hEq : (Matrix.diagonal ![(1 : ℂ), (d : ℂ)] + H) ^ 3 =
      (Λ : ℂ) • (Matrix.diagonal ![(1 : ℂ), (d : ℂ)] * H * Matrix.diagonal ![(1 : ℂ), (d : ℂ)])) :
    let D : Mat 2 := Matrix.diagonal ![(1 : ℂ), (d : ℂ)]
    let a : ℝ := (H 0 0).re
    let b : ℝ := (H 1 1).re
    let Φ : Mat 2 := D * H * D * H - D ^ 3 * H
    b < 1 / 2 ∧
    a = d * (1 - b) ∧
    Φ.trace.re < -(1 / 2 : ℝ) * d * (1 - d) ^ 2 ∧
    Φ.trace.re < 0 := by
  intro D a b Φ
  set z : ℂ := H 0 1
  set r : ℝ := ‖z‖ ^ 2
  have hH_herm : Hᴴ = H := hH.isHermitian.eq
  have hH10 : H 1 0 = starRingEnd ℂ z := by
    have := congr_fun (congr_fun hH_herm 1) 0
    simpa [Matrix.conjTranspose_apply, Complex.star_def, z] using this.symm
  have hH00_eq : H 0 0 = (a : ℂ) := by
    have hconj : starRingEnd ℂ (H 0 0) = H 0 0 := by
      have := congr_fun (congr_fun hH_herm 0) 0
      simpa [Matrix.conjTranspose_apply, Complex.star_def] using this
    exact Complex.ext rfl (by simpa using (Complex.conj_eq_iff_im.mp hconj))
  have hH11_eq : H 1 1 = (b : ℂ) := by
    have hconj : starRingEnd ℂ (H 1 1) = H 1 1 := by
      have := congr_fun (congr_fun hH_herm 1) 1
      simpa [Matrix.conjTranspose_apply, Complex.star_def] using this
    exact Complex.ext rfl (by simpa using (Complex.conj_eq_iff_im.mp hconj))
  have ha_pos : 0 < a := by
    let e0 : Fin 2 → ℂ := ![(1 : ℂ), 0]
    have he0 : e0 ≠ 0 := by intro h; have := congr_fun h 0; simp [e0] at this
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 he0)).1
    rw [Complex.zero_re] at hpos
    have hval : (star e0 ⬝ᵥ H.mulVec e0).re = a := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e0, hH00_eq]
    linarith
  have hb_pos : 0 < b := by
    let e1 : Fin 2 → ℂ := ![0, (1 : ℂ)]
    have he1 : e1 ≠ 0 := by intro h; have := congr_fun h 1; simp [e1] at this
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 he1)).1
    rw [Complex.zero_re] at hpos
    have hval : (star e1 ⬝ᵥ H.mulVec e1).re = b := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, e1, hH11_eq]
    linarith
  have hr_pos : 0 < r := sq_pos_of_pos (norm_pos_iff.mpr hc_ne)
  have hzz : z * starRingEnd ℂ z = (r : ℂ) := by
    dsimp [r]; rw [Complex.mul_conj', Complex.ofReal_pow]
  have hzz' : starRingEnd ℂ z * z = (r : ℂ) := by
    rw [mul_comm, hzz]
  have hr_lt : r < a * b := by
    let v : Fin 2 → ℂ := ![-z, (a : ℂ)]
    have hv : v ≠ 0 := by
      intro h; have := congr_fun h 1
      simp only [v, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
        Complex.ofReal_eq_zero] at this
      exact ha_pos.ne' this
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 hv)).1
    have hval : star v ⬝ᵥ H.mulVec v = ((a * (a * b - r) : ℝ) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply, v,
        Matrix.cons_val_zero, Matrix.cons_val_one, hH00_eq, hH11_eq, hH10]
      change starRingEnd ℂ (-z) * ((a : ℂ) * (-z) + z * (a : ℂ)) +
          starRingEnd ℂ (a : ℂ) * (starRingEnd ℂ z * (-z) + (b : ℂ) * (a : ℂ)) = _
      rw [Complex.conj_ofReal]
      have h1 : (a : ℂ) * (-z) + z * (a : ℂ) = 0 := by ring
      have h2 : starRingEnd ℂ z * (-z) = -(r : ℂ) := by
        rw [mul_neg, hzz']
      rw [h1, mul_zero, zero_add, h2]; push_cast; ring
    rw [Complex.zero_re, hval, Complex.ofReal_re] at hpos
    nlinarith only [hpos, ha_pos]
  -- 2×2 Cayley-Hamilton on M = D + H
  set M : Mat 2 := D + H
  set u : ℝ := 1 + a
  set w : ℝ := d + b
  set T : ℝ := u + w
  set Δ : ℝ := u * w - r
  have hM00 : M 0 0 = (u : ℂ) := by simp [M, D, hH00_eq, u]
  have hM01 : M 0 1 = z := by simp [M, D, z]
  have hM10 : M 1 0 = starRingEnd ℂ z := by simp [M, D, hH10]
  have hM11 : M 1 1 = (w : ℂ) := by simp [M, D, hH11_eq, w]
  have hCH2 : M ^ 2 = (T : ℂ) • M - (Δ : ℂ) • (1 : Mat 2) := by
    rw [mat_pow_two]
    refine Matrix.ext fun i j => ?_
    revert i j
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, hM00, hM01, hM10]
      rw [hzz]; dsimp [T, Δ]; push_cast; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), smul_eq_mul, mul_zero, sub_zero,
        hM00, hM01, hM11]
      dsimp [T]; push_cast; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_zero, sub_zero,
        hM00, hM10, hM11]
      dsimp [T]; push_cast; ring
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, hM01, hM10, hM11]
      rw [hzz']; dsimp [T, Δ]; push_cast; ring
  have hCH3 : M ^ 3 = ((T ^ 2 - Δ : ℝ) : ℂ) • M - ((T * Δ : ℝ) : ℂ) • (1 : Mat 2) := by
    calc M ^ 3 = M ^ 2 * M := by rw [mat_pow_three, mat_pow_two]
      _ = ((T : ℂ) • M - (Δ : ℂ) • (1 : Mat 2)) * M := by rw [hCH2]
      _ = (T : ℂ) • M ^ 2 - (Δ : ℂ) • M := by
            rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, mat_pow_two]
      _ = (T : ℂ) • ((T : ℂ) • M - (Δ : ℂ) • (1 : Mat 2)) - (Δ : ℂ) • M := by rw [hCH2]
      _ = ((T ^ 2 - Δ : ℝ) : ℂ) • M - ((T * Δ : ℝ) : ℂ) • (1 : Mat 2) := by
            rw [smul_sub, smul_smul, smul_smul]
            have h1 : ((T : ℂ) * (T : ℂ)) • M - (Δ : ℂ) • M = ((T ^ 2 - Δ : ℝ) : ℂ) • M := by
              rw [← sub_smul]; congr 1; push_cast; ring
            have h2 : ((T : ℂ) * (Δ : ℂ)) • (1 : Mat 2) = ((T * Δ : ℝ) : ℂ) • (1 : Mat 2) := by
              congr 1; push_cast; ring
            rw [← h1, ← h2]; abel
  -- Compare (0,1), (0,0), (1,1) entries of M^3 = Λ D H D
  have hEq' : M ^ 3 = (Λ : ℂ) • (D * H * D) := hEq
  rw [hCH3] at hEq'
  have h01 : T ^ 2 - Δ = Λ * d := by
    have h := congr_fun (congr_fun hEq' 0) 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, mul_zero, sub_zero, hM01,
      Matrix.mul_apply, Fin.sum_univ_two, D, Matrix.diagonal_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, zero_mul, add_zero, zero_add] at h
    have h' : ((T ^ 2 - Δ : ℝ) : ℂ) * z = ((Λ * d : ℝ) : ℂ) * z := by
      rw [h]; push_cast; ring
    exact Complex.ofReal_injective (mul_right_cancel₀ hc_ne h')
  have h00 : (T ^ 2 - Δ) * u - T * Δ = Λ * a := by
    have h := congr_fun (congr_fun hEq' 0) 0
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      ↓reduceIte, mul_one, hM00, Matrix.mul_apply, Fin.sum_univ_two, D, Matrix.diagonal_apply,
      Matrix.cons_val_zero, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, one_mul, zero_mul, mul_zero, add_zero, hH00_eq] at h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hre
    linarith
  have h11 : (T ^ 2 - Δ) * w - T * Δ = Λ * d ^ 2 * b := by
    have h := congr_fun (congr_fun hEq' 1) 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      ↓reduceIte, mul_one, hM11, Matrix.mul_apply, Fin.sum_univ_two, D, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, show (0 : Fin 2) ≠ 1 by decide,
      show (1 : Fin 2) ≠ 0 by decide, zero_mul, mul_zero, zero_add, hH11_eq] at h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hre
    linarith
  have ha_eq : a = d * (1 - b) := by
    have hsub : Λ * ((1 - d) * (a - d * (1 - b))) = 0 := by
      have : (T ^ 2 - Δ) * (u - w) = Λ * (a - d ^ 2 * b) := by linarith
      rw [h01] at this
      dsimp [u, w] at this
      linear_combination -this
    have h1 : (1 - d) * (a - d * (1 - b)) = 0 := (mul_eq_zero.mp hsub).resolve_left hΛ.ne'
    have h2 : a - d * (1 - b) = 0 := (mul_eq_zero.mp h1).resolve_left (by linarith)
    linarith
  have hT_eq : T = 1 + 2 * d + b * (1 - d) := by
    dsimp [T, u, w]; rw [ha_eq]; ring
  have hT_pos : 0 < T := by nlinarith only [hT_eq, hd0, hd1, hb_pos]
  have hden_pos : 0 < 2 * T - 1 - d := by nlinarith only [hT_eq, hd0, hd1, hb_pos]
  have hcubic : Λ * d * (2 * T - 1 - d) = T ^ 3 := by
    have hΔ : Δ = T ^ 2 - Λ * d := by linarith
    rw [h01, hΔ] at h00
    dsimp [u] at h00
    linear_combination h00 + Λ * d * hT_eq + Λ * (1 - d) * ha_eq
  have hb_lt : b < 1 / 2 := by
    have hamgm : 4 * (u * w) ≤ T ^ 2 := by
      have : T ^ 2 - 4 * (u * w) = (u - w) ^ 2 := by dsimp [T]; ring
      nlinarith only [this, sq_nonneg (u - w)]
    have hr_id : r = u * w - T ^ 2 + Λ * d := by dsimp [Δ] at h01; linarith
    have hbound : 4 * (2 * T - 1 - d) * r ≤ T ^ 2 * (3 * (1 + d) - 2 * T) := by
      have h1 : 4 * (2 * T - 1 - d) * r =
          (2 * T - 1 - d) * (4 * (u * w) - 4 * T ^ 2) + 4 * (Λ * d * (2 * T - 1 - d)) := by
        rw [hr_id]; ring
      rw [h1, hcubic]
      nlinarith only [hamgm, hden_pos]
    have hpos_lhs : 0 < 4 * (2 * T - 1 - d) * r := by positivity
    have h2T_lt : 2 * T < 3 * (1 + d) := by
      nlinarith only [hbound, hpos_lhs, sq_pos_of_pos hT_pos]
    have : (1 - d) * (1 - 2 * b) > 0 := by linarith [hT_eq]
    nlinarith only [this, hd1]
  have htr_val : Φ.trace.re = a ^ 2 - a + d ^ 2 * b ^ 2 - d ^ 3 * b + 2 * d * r := by
    have hDHDH : (D * H * D * H).trace.re = a ^ 2 + 2 * d * r + d ^ 2 * b ^ 2 := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, D,
        Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
        one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, hH00_eq, hH11_eq, hH10,
        show H 0 1 = z from rfl]
      have h1 : (a : ℂ) * (a : ℂ) + z * (d : ℂ) * starRingEnd ℂ z +
          ((d : ℂ) * starRingEnd ℂ z * z + (d : ℂ) * (b : ℂ) * (d : ℂ) * (b : ℂ)) =
          ((a ^ 2 + 2 * d * r + d ^ 2 * b ^ 2 : ℝ) : ℂ) := by
        have ht1 : z * (d : ℂ) * starRingEnd ℂ z = ((d * r : ℝ) : ℂ) := by
          calc z * (d : ℂ) * starRingEnd ℂ z = (d : ℂ) * (z * starRingEnd ℂ z) := by ring
            _ = (d : ℂ) * (r : ℂ) := by rw [hzz]
            _ = ((d * r : ℝ) : ℂ) := by push_cast; rfl
        have ht2 : (d : ℂ) * starRingEnd ℂ z * z = ((d * r : ℝ) : ℂ) := by
          calc (d : ℂ) * starRingEnd ℂ z * z = (d : ℂ) * (starRingEnd ℂ z * z) := by ring
            _ = (d : ℂ) * (r : ℂ) := by rw [hzz']
            _ = ((d * r : ℝ) : ℂ) := by push_cast; rfl
        rw [ht1, ht2]; push_cast; ring
      rw [h1, Complex.ofReal_re]
    have hD3H : (D ^ 3 * H).trace.re = a + d ^ 3 * b := by
      rw [mat_pow_three]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two, D,
        Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
        one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, hH00_eq, hH11_eq]
      have h1 : (a : ℂ) + (d : ℂ) * (d : ℂ) * (d : ℂ) * (b : ℂ) = ((a + d ^ 3 * b : ℝ) : ℂ) := by
        push_cast; ring
      rw [h1, Complex.ofReal_re]
    dsimp [Φ]; rw [Matrix.trace_sub, Complex.sub_re, hDHDH, hD3H]; ring
  have htr_bound : Φ.trace.re < -(1 / 2 : ℝ) * d * (1 - d) ^ 2 := by
    have h1 : a ^ 2 - a + d ^ 2 * b ^ 2 - d ^ 3 * b + 2 * d * (a * b) =
        d * (1 - d) * (b * (1 + d) - 1) := by rw [ha_eq]; ring
    have h2 : Φ.trace.re < d * (1 - d) * (b * (1 + d) - 1) := by
      rw [htr_val]; nlinarith only [h1, hr_lt, hd0]
    have h3 : b * (1 + d) - 1 < -(1 / 2 : ℝ) * (1 - d) := by nlinarith only [hb_lt, hd0]
    have h4 : d * (1 - d) * (b * (1 + d) - 1) < d * (1 - d) * (-(1 / 2 : ℝ) * (1 - d)) :=
      mul_lt_mul_of_pos_left h3 (mul_pos hd0 (by linarith))
    linarith
  have htr_neg : Φ.trace.re < 0 := by
    have hpos : 0 < (1 / 2 : ℝ) * d * (1 - d) ^ 2 := by
      have : 0 < 1 - d := by linarith
      positivity
    linarith
  exact ⟨hb_lt, ha_eq, htr_bound, htr_neg⟩

/-- Strictly-negative spectral projection P⁻ := 1_{A < 0} of a complex Hermitian matrix A. -/
def negSpectralProj {n : ℕ} {A : Mat n} (hA : A.IsHermitian) : Mat n :=
  (hA.eigenvectorUnitary : Mat n) *
    Matrix.diagonal (fun i => if hA.eigenvalues i < 0 then (1 : ℂ) else 0) *
    (hA.eigenvectorUnitary : Mat n)ᴴ

lemma negSpectralProj_isHermitian {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    (negSpectralProj hA).IsHermitian := by
  unfold negSpectralProj
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  congr 1; congr 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij)]

lemma negSpectralProj_idem {n : ℕ} {A : Mat n} (hA : A.IsHermitian) :
    negSpectralProj hA * negSpectralProj hA = negSpectralProj hA := by
  unfold negSpectralProj
  let U := hA.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => if hA.eigenvalues i < 0 then (1 : ℂ) else 0
  calc ((U : Mat n) * Matrix.diagonal d * (U : Mat n)ᴴ) * ((U : Mat n) * Matrix.diagonal d * (U : Mat n)ᴴ)
      = (U : Mat n) * Matrix.diagonal d * ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal d * (U : Mat n)ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = (U : Mat n) * (Matrix.diagonal d * Matrix.diagonal d) * (U : Mat n)ᴴ := by
          rw [unitary_conjTranspose_mul_self U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (U : Mat n) * Matrix.diagonal d * (U : Mat n)ᴴ := by
          rw [Matrix.diagonal_mul_diagonal]
          congr 2; ext i j
          by_cases hij : i = j
          · subst hij; simp only [Matrix.diagonal_apply_eq, d]; split_ifs <;> simp
          · simp [Matrix.diagonal_apply_ne _ hij]

lemma negSpectralProj_comm {n : ℕ} {D A : Mat n} (hA : A.IsHermitian) (hcomm : D * A = A * D) :
    D * negSpectralProj hA = negSpectralProj hA * D := by
  let U := hA.eigenvectorUnitary
  let lam := hA.eigenvalues
  let B : Mat n := (U : Mat n)ᴴ * D * (U : Mat n)
  let P0 : Mat n := Matrix.diagonal (fun i => if lam i < 0 then (1 : ℂ) else 0)
  have hA_eq : A = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hA.spectral_theorem
  have hB_comm_lam : B * Matrix.diagonal (fun i => (lam i : ℂ)) =
      Matrix.diagonal (fun i => (lam i : ℂ)) * B := by
    have h1 := congrArg (fun X => (U : Mat n)ᴴ * X * (U : Mat n)) hcomm
    rw [hA_eq] at h1
    have hL : (U : Mat n)ᴴ * (D * ((U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ)) *
        (U : Mat n) = B * Matrix.diagonal (fun i => (lam i : ℂ)) := by
      dsimp [B]
      calc _ = ((U : Mat n)ᴴ * D * (U : Mat n)) * Matrix.diagonal (fun i => (lam i : ℂ)) *
                ((U : Mat n)ᴴ * (U : Mat n)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [unitary_conjTranspose_mul_self U, Matrix.mul_one]
    have hR : (U : Mat n)ᴴ * (((U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ) * D) *
        (U : Mat n) = Matrix.diagonal (fun i => (lam i : ℂ)) * B := by
      dsimp [B]
      calc _ = ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => (lam i : ℂ)) *
                ((U : Mat n)ᴴ * D * (U : Mat n)) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [unitary_conjTranspose_mul_self U, Matrix.one_mul]
    rw [hL, hR] at h1; exact h1
  have hB_comm_P0 : B * P0 = P0 * B := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, P0]
    by_cases h1 : lam i < 0 <;> by_cases h2 : lam j < 0
    · simp [h1, h2]
    · have hne : lam i ≠ lam j := by intro heq; rw [heq] at h1; exact h2 h1
      have hij := congr_fun (congr_fun hB_comm_lam i) j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
      have h0 : B i j * ((lam j : ℂ) - (lam i : ℂ)) = 0 := by linear_combination hij
      have hdiff : (lam j : ℂ) - (lam i : ℂ) ≠ 0 := by
        intro hz; exact hne (Complex.ofReal_injective (sub_eq_zero.mp hz).symm)
      have hBij : B i j = 0 := (mul_eq_zero.mp h0).resolve_right hdiff
      simp [h1, h2, hBij]
    · have hne : lam i ≠ lam j := by intro heq; rw [heq] at h1; exact h1 h2
      have hij := congr_fun (congr_fun hB_comm_lam i) j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
      have h0 : B i j * ((lam j : ℂ) - (lam i : ℂ)) = 0 := by linear_combination hij
      have hdiff : (lam j : ℂ) - (lam i : ℂ) ≠ 0 := by
        intro hz; exact hne (Complex.ofReal_injective (sub_eq_zero.mp hz).symm)
      have hBij : B i j = 0 := (mul_eq_zero.mp h0).resolve_right hdiff
      simp [h1, h2, hBij]
    · simp [h1, h2]
  have hD_eq : D = (U : Mat n) * B * (U : Mat n)ᴴ := by
    dsimp [B]
    calc D = ((U : Mat n) * (U : Mat n)ᴴ) * D * ((U : Mat n) * (U : Mat n)ᴴ) := by
            rw [unitary_mul_conjTranspose_self U, Matrix.one_mul, Matrix.mul_one]
      _ = (U : Mat n) * ((U : Mat n)ᴴ * D * (U : Mat n)) * (U : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
  unfold negSpectralProj
  change D * ((U : Mat n) * P0 * (U : Mat n)ᴴ) = ((U : Mat n) * P0 * (U : Mat n)ᴴ) * D
  conv_lhs => rw [hD_eq]
  conv_rhs => rw [hD_eq]
  calc (U : Mat n) * B * (U : Mat n)ᴴ * ((U : Mat n) * P0 * (U : Mat n)ᴴ)
      = (U : Mat n) * B * ((U : Mat n)ᴴ * (U : Mat n)) * P0 * (U : Mat n)ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = (U : Mat n) * (B * P0) * (U : Mat n)ᴴ := by
          rw [unitary_conjTranspose_mul_self U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (U : Mat n) * (P0 * B) * (U : Mat n)ᴴ := by rw [hB_comm_P0]
    _ = (U : Mat n) * P0 * ((U : Mat n)ᴴ * (U : Mat n)) * B * (U : Mat n)ᴴ := by
          rw [unitary_conjTranspose_mul_self U, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (U : Mat n) * P0 * (U : Mat n)ᴴ * ((U : Mat n) * B * (U : Mat n)ᴴ) := by
          simp only [Matrix.mul_assoc]

private lemma negSpectralProj_quad_neg {n : ℕ} {A : Mat n} (hA : A.IsHermitian)
    {v : Fin n → ℂ} (hv : v ≠ 0) (hPv : (negSpectralProj hA).mulVec v = v) :
    (star v ⬝ᵥ A.mulVec v).re < 0 := by
  let U := hA.eigenvectorUnitary
  let lam := hA.eigenvalues
  let z : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
  have hA_eq : A = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hA.spectral_theorem
  have hquad : (star v ⬝ᵥ A.mulVec v).re = ∑ i : Fin n, ‖z i‖ ^ 2 * lam i := by
    rw [hA_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hst : star v ᵥ* (U : Mat n) = star z := by
      simp only [z, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    change (star v ᵥ* (U : Mat n) ⬝ᵥ (Matrix.diagonal fun i => (lam i : ℂ)).mulVec z).re = _
    rw [hst, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have h1 : starRingEnd ℂ (z i) * ((lam i : ℂ) * z i) =
        (lam i : ℂ) * (starRingEnd ℂ (z i) * z i) := by ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  have hsupp : ∀ i : Fin n, ¬(lam i < 0) → z i = 0 := by
    intro i hi
    have hPv' : ((U : Mat n) * Matrix.diagonal (fun k => if lam k < 0 then (1 : ℂ) else 0) *
        (U : Mat n)ᴴ).mulVec v = v := hPv
    have h2 : (Matrix.diagonal (fun k => if lam k < 0 then (1 : ℂ) else 0)).mulVec z = z := by
      calc (Matrix.diagonal (fun k => if lam k < 0 then (1 : ℂ) else 0)).mulVec z
          = ((U : Mat n)ᴴ * ((U : Mat n) * Matrix.diagonal (fun k => if lam k < 0 then (1 : ℂ) else 0) *
              (U : Mat n)ᴴ)).mulVec v := by
              dsimp [z]
              rw [← Matrix.mul_assoc (U : Mat n)ᴴ, ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n),
                unitary_conjTranspose_mul_self U, Matrix.one_mul, Matrix.mulVec_mulVec]
        _ = (U : Mat n)ᴴ.mulVec v := by rw [← Matrix.mulVec_mulVec, hPv']
        _ = z := rfl
    have hi' := congr_fun h2 i
    simp [Matrix.mulVec_diagonal, hi] at hi'
    exact hi'.symm
  obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
    by_contra hz; push Not at hz
    have hz0 : z = 0 := funext hz
    have h1 := congrArg (Matrix.mulVec (U : Mat n)) hz0
    simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
    exact hv h1
  have hi0_neg : lam i0 < 0 := by by_contra h; exact hi0 (hsupp i0 h)
  rw [hquad]
  have hle : ∀ i ∈ Finset.univ, ‖z i‖ ^ 2 * lam i ≤ 0 := fun i _ => by
    by_cases h : lam i < 0
    · exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h.le
    · rw [hsupp i h, norm_zero, sq, zero_mul, zero_mul]
  have hlt : ‖z i0‖ ^ 2 * lam i0 < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos (norm_pos_iff.mpr hi0)) hi0_neg
  calc ∑ i : Fin n, ‖z i‖ ^ 2 * lam i
      = ‖z i0‖ ^ 2 * lam i0 + ∑ i ∈ Finset.univ.erase i0, ‖z i‖ ^ 2 * lam i :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i0)).symm
    _ < 0 + 0 := add_lt_add_of_lt_of_le hlt (Finset.sum_nonpos fun i _ => hle i (Finset.mem_univ i))
    _ = 0 := add_zero 0

/-- Trace of any Hermitian idempotent matrix R (Rᴴ = R, R² = R) equals the finrank of its range. -/
private lemma hermitian_idempotent_trace_eq_finrank {n : ℕ} {R : Mat n}
    (hRh : R.IsHermitian) (hR2 : R * R = R) :
    R.trace.re = (Module.finrank ℂ (LinearMap.range R.mulVecLin) : ℝ) := by
  let U := hRh.eigenvectorUnitary
  let r := hRh.eigenvalues
  have hR_eq : R = (U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, r, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hRh.spectral_theorem
  have hr_idem : ∀ i : Fin n, r i = 0 ∨ r i = 1 := by
    have hdiag : Matrix.diagonal (fun i => (r i : ℂ)) * Matrix.diagonal (fun i => (r i : ℂ)) =
        Matrix.diagonal (fun i => (r i : ℂ)) := by
      have h1 := congrArg (fun X => (U : Mat n)ᴴ * X * (U : Mat n)) hR2
      rw [hR_eq] at h1
      have hL : (U : Mat n)ᴴ * ((U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ *
          ((U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ)) * (U : Mat n) =
          Matrix.diagonal (fun i => (r i : ℂ)) * Matrix.diagonal (fun i => (r i : ℂ)) := by
        calc _ = ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => (r i : ℂ)) *
                  ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => (r i : ℂ)) *
                  ((U : Mat n)ᴴ * (U : Mat n)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [unitary_conjTranspose_mul_self U, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one]
      have hR' : (U : Mat n)ᴴ * ((U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ) *
          (U : Mat n) = Matrix.diagonal (fun i => (r i : ℂ)) := by
        calc _ = ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => (r i : ℂ)) *
                  ((U : Mat n)ᴴ * (U : Mat n)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [unitary_conjTranspose_mul_self U, Matrix.one_mul, Matrix.mul_one]
      rw [hL, hR'] at h1; exact h1
    intro i
    have hi := congr_fun (congr_fun hdiag i) i
    simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at hi
    have hre : r i * r i = r i := Complex.ofReal_injective (by simpa [Complex.ofReal_mul] using hi)
    have h0 : r i * (r i - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  let S : Finset (Fin n) := Finset.univ.filter (fun i => r i = 1)
  have htr : R.trace.re = (S.card : ℝ) := by
    have hcyc : R.trace = (Matrix.diagonal (fun i => (r i : ℂ))).trace := by
      rw [hR_eq]
      calc ((U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ).trace
          = ((U : Mat n)ᴴ * ((U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)))).trace :=
              Matrix.trace_mul_comm _ _
        _ = (((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => (r i : ℂ))).trace := by
              rw [Matrix.mul_assoc]
        _ = (Matrix.diagonal (fun i => (r i : ℂ))).trace := by
              rw [unitary_conjTranspose_mul_self U, Matrix.one_mul]
    rw [hcyc, Matrix.trace, Complex.re_sum]
    calc ∑ i : Fin n, (Matrix.diag (Matrix.diagonal (fun k => (r k : ℂ))) i).re
        = ∑ i : Fin n, if r i = 1 then (1 : ℝ) else 0 := Finset.sum_congr rfl fun i _ => by
            simp only [Matrix.diag_apply, Matrix.diagonal_apply_eq, Complex.ofReal_re]
            rcases hr_idem i with h0 | h1
            · rw [h0]; simp
            · rw [h1]; simp
      _ = (S.card : ℝ) := by
            rw [Finset.sum_boole]
  -- Explicit linear equivalence (↥S → ℂ) ≃ₗ[ℂ] range(R)
  have hmem_range : ∀ c : ↥S → ℂ,
      (U : Mat n).mulVec (fun i => if h : i ∈ S then c ⟨i, h⟩ else 0) ∈ LinearMap.range R.mulVecLin := by
    intro c
    let v : Fin n → ℂ := (U : Mat n).mulVec (fun i => if h : i ∈ S then c ⟨i, h⟩ else 0)
    refine ⟨v, ?_⟩
    change R.mulVec v = v
    dsimp [v]; rw [hR_eq]
    simp only [Matrix.mulVec_mulVec]
    have h1 : (U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ * (U : Mat n) =
        (U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) := by
      rw [Matrix.mul_assoc, unitary_conjTranspose_mul_self U, Matrix.mul_one]
    rw [h1, ← Matrix.mulVec_mulVec]
    congr 1; ext i
    simp only [Matrix.mulVec_diagonal]
    by_cases hi : i ∈ S
    · have hri : r i = 1 := (Finset.mem_filter.mp hi).2
      simp [hi, hri]
    · simp [hi]
  let eS : (↥S → ℂ) ≃ₗ[ℂ] LinearMap.range R.mulVecLin :=
    { toFun := fun c => ⟨(U : Mat n).mulVec (fun i => if h : i ∈ S then c ⟨i, h⟩ else 0), hmem_range c⟩
      invFun := fun v => fun i => ((U : Mat n)ᴴ.mulVec v.1) i.1
      map_add' := fun c1 c2 => by
        apply Subtype.ext; simp only [Submodule.coe_add, ← Matrix.mulVec_add]
        congr 1; ext i; by_cases hi : i ∈ S <;> simp [hi]
      map_smul' := fun a c => by
        apply Subtype.ext; simp only [RingHom.id_apply, SetLike.val_smul, ← Matrix.mulVec_smul]
        congr 1; ext i; by_cases hi : i ∈ S <;> simp [hi]
      left_inv := fun c => by
        ext ⟨i, hi⟩
        simp only [Matrix.mulVec_mulVec, unitary_conjTranspose_mul_self U, Matrix.one_mulVec, hi, ↓reduceDIte]
      right_inv := fun ⟨v, hv⟩ => by
        apply Subtype.ext
        obtain ⟨w, rfl⟩ := hv
        have hRv : R.mulVec (R.mulVec w) = R.mulVec w := by
          rw [Matrix.mulVec_mulVec, hR2]
        have hdiag_fix : (Matrix.diagonal (fun i => (r i : ℂ))).mulVec ((U : Mat n)ᴴ.mulVec (R.mulVec w)) =
            (U : Mat n)ᴴ.mulVec (R.mulVec w) := by
          calc (Matrix.diagonal (fun i => (r i : ℂ))).mulVec ((U : Mat n)ᴴ.mulVec (R.mulVec w))
              = ((U : Mat n)ᴴ * ((U : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U : Mat n)ᴴ)).mulVec
                  (R.mulVec w) := by
                  rw [← Matrix.mul_assoc (U : Mat n)ᴴ, ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n),
                    unitary_conjTranspose_mul_self U, Matrix.one_mul, Matrix.mulVec_mulVec]
            _ = (U : Mat n)ᴴ.mulVec (R.mulVec (R.mulVec w)) := by rw [← hR_eq, ← Matrix.mulVec_mulVec]
            _ = (U : Mat n)ᴴ.mulVec (R.mulVec w) := by rw [hRv]
        have hvec_eq : (fun i => if _ : i ∈ S then ((U : Mat n)ᴴ.mulVec (R.mulVec w)) i else 0) =
            (U : Mat n)ᴴ.mulVec (R.mulVec w) := by
          ext i
          by_cases hi : i ∈ S
          · simp [hi]
          · simp only [hi, ↓reduceDIte]
            have hri0 : r i = 0 := by
              rcases hr_idem i with h0 | h1
              · exact h0
              · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩) hi
            have h2 := congr_fun hdiag_fix i
            simp only [Matrix.mulVec_diagonal, hri0, Complex.ofReal_zero, zero_mul] at h2
            exact h2
        change (U : Mat n).mulVec (fun i => if _ : i ∈ S then ((U : Mat n)ᴴ.mulVec (R.mulVec w)) i else 0) =
            R.mulVec w
        rw [hvec_eq, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec] }
  have hfr : Module.finrank ℂ (LinearMap.range R.mulVecLin) = S.card := by
    rw [← eS.finrank_eq, Module.finrank_pi_fintype]
    simp
  rw [htr, hfr]

/-- Grassmann Codimension / Subspace Dimension-Counting Lemma (`#38`, `#39`):
    For any m ≥ 1 subspaces W_1, ..., W_m of a finite-dimensional vector space E over ℂ,
      ∑_j dim(W_j) + dim(E) ≤ m · dim(E) + dim(⋂_j W_j) unconditionally! -/
private lemma finrank_sum_le_of_iInf_eq_bot {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] :
    ∀ {m : ℕ} (_hm : 1 ≤ m) (W : Fin m → Submodule ℂ E),
      ∑ j : Fin m, Module.finrank ℂ (W j) + Module.finrank ℂ E ≤
        m * Module.finrank ℂ E + Module.finrank ℂ (⨅ j : Fin m, W j : Submodule ℂ E)
  | 0, hm, _ => by omega
  | 1, _, W => by
      simp only [Fin.sum_univ_one, one_mul]
      rw [iInf_unique]
      change Module.finrank ℂ ↥(W 0) + Module.finrank ℂ E ≤ Module.finrank ℂ E + Module.finrank ℂ ↥(W 0)
      omega
  | m + 2, _, W => by
      have ih := finrank_sum_le_of_iInf_eq_bot (m := m + 1) (by omega) (fun j => W j.castSucc)
      let I : Submodule ℂ E := ⨅ j : Fin (m + 1), W j.castSucc
      let V : Submodule ℂ E := W (Fin.last (m + 1))
      have hgrass := Submodule.finrank_sup_add_finrank_inf_eq I V
      have hsup_le : Module.finrank ℂ (I ⊔ V : Submodule ℂ E) ≤ Module.finrank ℂ E :=
        Submodule.finrank_le _
      have hiInf_eq : (⨅ j : Fin (m + 2), W j) = I ⊓ V := by
        apply le_antisymm
        · exact le_inf (le_iInf fun j => iInf_le W j.castSucc) (iInf_le W (Fin.last (m + 1)))
        · refine le_iInf fun j => Fin.lastCases ?_ (fun k => inf_le_left.trans (iInf_le _ k)) j
          exact inf_le_right
      rw [Fin.sum_univ_castSucc, hiInf_eq]
      have hstep : Module.finrank ℂ I + Module.finrank ℂ V ≤
          Module.finrank ℂ E + Module.finrank ℂ (I ⊓ V : Submodule ℂ E) := by omega
      have hmul : (m + 2) * Module.finrank ℂ E = (m + 1) * Module.finrank ℂ E + Module.finrank ℂ E := by ring
      dsimp only [I, V] at hstep ⊢
      omega

/-- Unconditional Grassmann Eigenspace Trace Inequality (`#38`, `#39`, `p1_proof.md` Thm 5):
    Valid for ALL n ≥ 1, ALL m ≥ 2, ALL κ > 1, including degenerate D and non-commuting Φ_j!
    If D ≻ 0, Φ_1, ..., Φ_m are Hermitian with [D, Φ_j] = 0 and ∑_j Φ_j = 0, then
      ∑_j Re Tr(P_j⁻ D^(2κ)) ≤ (m - 1) Re Tr(D^(2κ))! -/
theorem sum_trace_negSpectralProj_le {n m : ℕ} (hm : 1 ≤ m) {κ : ℝ} {D : Mat n} (hD : D.PosDef)
    {Φ : Fin m → Mat n} (hΦh : ∀ j, (Φ j).IsHermitian)
    (hcomm : ∀ j, D * Φ j = Φ j * D)
    (hsum0 : ∑ j : Fin m, Φ j = 0) :
    ∑ j : Fin m, (negSpectralProj (hΦh j) * posDefPow (2 * κ) hD).trace.re ≤
      ((m : ℝ) - 1) * (posDefPow (2 * κ) hD).trace.re := by
  let UD := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  let P : Fin m → Mat n := fun j => negSpectralProj (hΦh j)
  have hPh : ∀ j, (P j).IsHermitian := fun j => negSpectralProj_isHermitian (hΦh j)
  have hP2 : ∀ j, P j * P j = P j := fun j => negSpectralProj_idem (hΦh j)
  have hDP : ∀ j, D * P j = P j * D := fun j => negSpectralProj_comm (hΦh j) (hcomm j)
  -- For each distinct eigenvalue λ of D, let Q_λ be the orthogonal projection onto ker(D - λ I)
  let Q : ℝ → Mat n := fun lam =>
    (UD : Mat n) * Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) * (UD : Mat n)ᴴ
  have hQh : ∀ lam, (Q lam).IsHermitian := fun lam => by
    dsimp [Q]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    congr 1; congr 1; ext i j
    by_cases hij : i = j
    · subst hij; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq]; split_ifs <;> simp
    · simp [Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
  have hQ2 : ∀ lam, Q lam * Q lam = Q lam := fun lam => by
    dsimp [Q]
    calc _ = (UD : Mat n) * Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) *
              ((UD : Mat n)ᴴ * (UD : Mat n)) *
              Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) * (UD : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (UD : Mat n) * (Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) *
              Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0)) * (UD : Mat n)ᴴ := by
            rw [unitary_conjTranspose_mul_self UD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [Matrix.diagonal_mul_diagonal]; congr 2; ext i j
            by_cases hij : i = j
            · subst hij; simp only [Matrix.diagonal_apply_eq]; split_ifs <;> simp
            · simp [Matrix.diagonal_apply_ne _ hij]
  -- Q_λ commutes with P_j
  have hQP_comm : ∀ lam j, Q lam * P j = P j * Q lam := fun lam j => by
    let B : Mat n := (UD : Mat n)ᴴ * P j * (UD : Mat n)
    have hD_eq : D = (UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ := by
      simpa [UD, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hD.isHermitian.spectral_theorem
    have hB_comm : Matrix.diagonal (fun i => (d i : ℂ)) * B = B * Matrix.diagonal (fun i => (d i : ℂ)) := by
      have h1 := congrArg (fun X => (UD : Mat n)ᴴ * X * (UD : Mat n)) (hDP j)
      rw [hD_eq] at h1
      have hL : (UD : Mat n)ᴴ * (((UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ) * P j) *
          (UD : Mat n) = Matrix.diagonal (fun i => (d i : ℂ)) * B := by
        dsimp [B]
        calc _ = ((UD : Mat n)ᴴ * (UD : Mat n)) * Matrix.diagonal (fun i => (d i : ℂ)) *
                  ((UD : Mat n)ᴴ * P j * (UD : Mat n)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [unitary_conjTranspose_mul_self UD, Matrix.one_mul]
      have hR : (UD : Mat n)ᴴ * (P j * ((UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ)) *
          (UD : Mat n) = B * Matrix.diagonal (fun i => (d i : ℂ)) := by
        dsimp [B]
        calc _ = ((UD : Mat n)ᴴ * P j * (UD : Mat n)) * Matrix.diagonal (fun i => (d i : ℂ)) *
                  ((UD : Mat n)ᴴ * (UD : Mat n)) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [unitary_conjTranspose_mul_self UD, Matrix.mul_one]
      rw [hL, hR] at h1; exact h1
    let Q0 : Mat n := Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0)
    have hQ0B : Q0 * B = B * Q0 := by
      ext i k
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Q0]
      by_cases hi : d i = lam <;> by_cases hk : d k = lam
      · simp [hi, hk]
      · have hne : d i ≠ d k := by intro heq; exact hk (heq.symm.trans hi)
        have hik := congr_fun (congr_fun hB_comm i) k
        simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hik
        have h0 : B i k * ((d i : ℂ) - (d k : ℂ)) = 0 := by linear_combination hik
        have hdiff : (d i : ℂ) - (d k : ℂ) ≠ 0 := fun hz => hne (Complex.ofReal_injective (sub_eq_zero.mp hz))
        simp [hi, hk, (mul_eq_zero.mp h0).resolve_right hdiff]
      · have hne : d i ≠ d k := by intro heq; exact hi (heq.trans hk)
        have hik := congr_fun (congr_fun hB_comm i) k
        simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at hik
        have h0 : B i k * ((d i : ℂ) - (d k : ℂ)) = 0 := by linear_combination hik
        have hdiff : (d i : ℂ) - (d k : ℂ) ≠ 0 := fun hz => hne (Complex.ofReal_injective (sub_eq_zero.mp hz))
        simp [hi, hk, (mul_eq_zero.mp h0).resolve_right hdiff]
      · simp [hi, hk]
    have hPj_eq : P j = (UD : Mat n) * B * (UD : Mat n)ᴴ := by
      dsimp [B]
      calc P j = ((UD : Mat n) * (UD : Mat n)ᴴ) * P j * ((UD : Mat n) * (UD : Mat n)ᴴ) := by
              rw [unitary_mul_conjTranspose_self UD, Matrix.one_mul, Matrix.mul_one]
        _ = (UD : Mat n) * ((UD : Mat n)ᴴ * P j * (UD : Mat n)) * (UD : Mat n)ᴴ := by
              simp only [Matrix.mul_assoc]
    change ((UD : Mat n) * Q0 * (UD : Mat n)ᴴ) * P j = P j * ((UD : Mat n) * Q0 * (UD : Mat n)ᴴ)
    conv_lhs => rw [hPj_eq]
    conv_rhs => rw [hPj_eq]
    calc (UD : Mat n) * Q0 * (UD : Mat n)ᴴ * ((UD : Mat n) * B * (UD : Mat n)ᴴ)
        = (UD : Mat n) * Q0 * ((UD : Mat n)ᴴ * (UD : Mat n)) * B * (UD : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (UD : Mat n) * (Q0 * B) * (UD : Mat n)ᴴ := by
            rw [unitary_conjTranspose_mul_self UD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (UD : Mat n) * (B * Q0) * (UD : Mat n)ᴴ := by rw [hQ0B]
      _ = (UD : Mat n) * B * ((UD : Mat n)ᴴ * (UD : Mat n)) * Q0 * (UD : Mat n)ᴴ := by
            rw [unitary_conjTranspose_mul_self UD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = (UD : Mat n) * B * (UD : Mat n)ᴴ * ((UD : Mat n) * Q0 * (UD : Mat n)ᴴ) := by
            simp only [Matrix.mul_assoc]
  -- On every eigenspace E_λ = range(Q_λ), Grassmann codimension gives ∑_j Re Tr(P_j Q_λ) ≤ (m - 1) Re Tr(Q_λ)
  have heig_bound : ∀ lam : ℝ,
      ∑ j : Fin m, (P j * Q lam).trace.re ≤ ((m : ℝ) - 1) * (Q lam).trace.re := by
    intro lam
    let E : Submodule ℂ (Fin n → ℂ) := LinearMap.range (Q lam).mulVecLin
    let R : Fin m → Mat n := fun j => Q lam * P j
    have hRh : ∀ j, (R j).IsHermitian := fun j => by
      dsimp [R]; rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, (hQh lam).eq, (hPh j).eq, hQP_comm]
    have hR2 : ∀ j, R j * R j = R j := fun j => by
      dsimp [R]
      calc Q lam * P j * (Q lam * P j)
          = Q lam * (P j * Q lam) * P j := by simp only [Matrix.mul_assoc]
        _ = Q lam * (Q lam * P j) * P j := by rw [← hQP_comm]
        _ = (Q lam * Q lam) * (P j * P j) := by simp only [Matrix.mul_assoc]
        _ = Q lam * P j := by rw [hQ2, hP2]
    let W : Fin m → Submodule ℂ E := fun j =>
      Submodule.comap E.subtype (LinearMap.range (R j).mulVecLin)
    have hW_le : ∀ j, LinearMap.range (R j).mulVecLin ≤ E := fun j v ⟨w, hw⟩ => by
      refine ⟨(P j).mulVec w, ?_⟩
      simpa [R, Matrix.mulVec_mulVec] using hw
    have hW_finrank : ∀ j, Module.finrank ℂ (W j) = Module.finrank ℂ (LinearMap.range (R j).mulVecLin) := by
      intro j
      let eW : W j ≃ₗ[ℂ] LinearMap.range (R j).mulVecLin :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun y => ⟨⟨y.1, hW_le j y.2⟩, y.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact eW.finrank_eq
    have hiInf_bot : (⨅ j : Fin m, W j) = ⊥ := by
      rw [eq_bot_iff]
      rintro ⟨v, hvE⟩ hvW
      rw [Submodule.mem_bot]
      apply Subtype.ext
      by_contra hv0
      have hPv : ∀ j : Fin m, (P j).mulVec v = v := by
        intro j
        have hmem : v ∈ LinearMap.range (R j).mulVecLin := (Submodule.mem_iInf _).mp hvW j
        obtain ⟨w, hw⟩ := hmem
        change (R j).mulVec w = v at hw
        have h1 : (P j).mulVec v = (P j * (Q lam * P j)).mulVec w := by
          rw [← hw, Matrix.mulVec_mulVec]
        rw [h1, ← Matrix.mul_assoc, ← hQP_comm, Matrix.mul_assoc, hP2]
        exact hw
      have hneg : ∀ j : Fin m, (star v ⬝ᵥ (Φ j).mulVec v).re < 0 := fun j =>
        negSpectralProj_quad_neg (hΦh j) hv0 (hPv j)
      have hsum_neg : ∑ j : Fin m, (star v ⬝ᵥ (Φ j).mulVec v).re < 0 := by
        have h0 : (⟨0, by omega⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
        have hpos_neg : 0 < ∑ j : Fin m, -(star v ⬝ᵥ (Φ j).mulVec v).re :=
          Finset.sum_pos' (fun j _ => by linarith [hneg j]) ⟨⟨0, by omega⟩, h0, by linarith [hneg ⟨0, by omega⟩]⟩
        rw [Finset.sum_neg_distrib] at hpos_neg
        linarith
      have hsum_zero : ∑ j : Fin m, (star v ⬝ᵥ (Φ j).mulVec v).re = 0 := by
        have h1 : (star v ⬝ᵥ (∑ j : Fin m, Φ j).mulVec v).re = 0 := by
          rw [hsum0, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
        rw [← h1, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
      linarith
    have hgrass := finrank_sum_le_of_iInf_eq_bot hm W
    rw [hiInf_bot, finrank_bot, add_zero] at hgrass
    have hnat : ∑ j : Fin m, Module.finrank ℂ (LinearMap.range (R j).mulVecLin) + Module.finrank ℂ E ≤
        m * Module.finrank ℂ E := by
      simpa only [hW_finrank] using hgrass
    have hreal : (∑ j : Fin m, (Module.finrank ℂ (LinearMap.range (R j).mulVecLin) : ℝ)) +
        (Module.finrank ℂ E : ℝ) ≤ (m : ℝ) * (Module.finrank ℂ E : ℝ) := by
      exact_mod_cast hnat
    have htr_R : ∀ j, (P j * Q lam).trace.re = (Module.finrank ℂ (LinearMap.range (R j).mulVecLin) : ℝ) :=
      fun j => by rw [← hQP_comm]; exact hermitian_idempotent_trace_eq_finrank (hRh j) (hR2 j)
    have htr_Q : (Q lam).trace.re = (Module.finrank ℂ E : ℝ) :=
      hermitian_idempotent_trace_eq_finrank (hQh lam) (hQ2 lam)
    simp_rw [htr_R]; rw [htr_Q]; linarith
  -- Spectral resolution: posDefPow (2 * κ) hD = ∑_{lam ∈ image d} lam^(2κ) • Q lam
  let L : Finset ℝ := Finset.univ.image d
  have hspec_sum : posDefPow (2 * κ) hD = ∑ lam ∈ L, (((lam ^ (2 * κ) : ℝ) : ℂ)) • Q lam := by
    have hterm : ∀ lam : ℝ, (((lam ^ (2 * κ) : ℝ) : ℂ)) • Q lam =
        (UD : Mat n) * ((((lam ^ (2 * κ) : ℝ) : ℂ)) • Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0)) *
          (UD : Mat n)ᴴ := by
      intro lam
      change (((lam ^ (2 * κ) : ℝ) : ℂ)) • ((UD : Mat n) *
          Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) * (UD : Mat n)ᴴ) = _
      rw [Matrix.mul_smul, Matrix.smul_mul]
    simp_rw [hterm]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    unfold posDefPow
    refine congrArg (· * (UD : Mat n)ᴴ) (congrArg ((UD : Mat n) * ·) ?_)
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem d (Finset.mem_univ i))]
    · simp only [Matrix.diagonal_apply_ne _ hij, mul_zero, Finset.sum_const_zero]
  rw [hspec_sum]
  have hLHS : ∑ j : Fin m, (P j * ∑ lam ∈ L, (((lam ^ (2 * κ) : ℝ) : ℂ)) • Q lam).trace.re =
      ∑ lam ∈ L, lam ^ (2 * κ) * ∑ j : Fin m, (P j * Q lam).trace.re := by
    calc _ = ∑ j : Fin m, ∑ lam ∈ L, lam ^ (2 * κ) * (P j * Q lam).trace.re :=
            Finset.sum_congr rfl fun j _ => by
              rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
              refine Finset.sum_congr rfl fun lam _ => by
                rw [Matrix.mul_smul, trace_re_smul_real]
      _ = ∑ lam ∈ L, ∑ j : Fin m, lam ^ (2 * κ) * (P j * Q lam).trace.re := Finset.sum_comm
      _ = ∑ lam ∈ L, lam ^ (2 * κ) * ∑ j : Fin m, (P j * Q lam).trace.re :=
            Finset.sum_congr rfl fun lam _ => (Finset.mul_sum _ _ _).symm
  have hRHS : (((m : ℝ) - 1) * (∑ lam ∈ L, (((lam ^ (2 * κ) : ℝ) : ℂ)) • Q lam).trace.re) =
      ∑ lam ∈ L, lam ^ (2 * κ) * (((m : ℝ) - 1) * (Q lam).trace.re) := by
    rw [Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun lam _ => by
      rw [trace_re_smul_real]; ring
  rw [hLHS, hRHS]
  refine Finset.sum_le_sum fun lam hlam => ?_
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hlam
  exact mul_le_mul_of_nonneg_left (heig_bound (d i)) (Real.rpow_nonneg (hD.eigenvalues_pos i).le _)

/-- 3-Line Master-Trace ⟹ Global Optimality (Open Piece 1) Implication (`#8`, `#10C`, `#38`, `#39`):
    Valid unconditionally for ALL n ≥ 1, ALL m ≥ 2, ALL κ > 1, ALL Λ > 2^(2κ - 1),
    including arbitrary degeneracies of D and non-commuting Φ_j!
    If every solution block (D, H_j) satisfies the Single-Block Master Trace Inequality
      M_{Λ, m}(D, H_j) := Re Tr(Φ_j) - σ_+ Re Tr((1 - P_j⁻) D^(2κ)) + (σ_+/(m-1)) Re Tr(P_j⁻ D^(2κ)) ≥ 0
    (with strict inequality whenever P_j⁻ ≠ 0), then NO finite-dimensional global solution exists at Λ! -/
theorem master_trace_implies_no_global_solution {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    {κ Λ h : ℝ} (hκ : 1 < κ) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ)
    (hh : 1 < h) (_hSc : (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1))
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0)
    (hMaster : ∀ j : Fin m,
      let hG := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)
      let Φj := posDefPow κ hG - D * posDefPow (κ - 1) hG * D
      let hΦj : Φj.IsHermitian :=
        (posDefPow_posDef κ hG).isHermitian.sub
          (posDef_conj_of_posDef hD (posDefPow_posDef (κ - 1) hG)).isHermitian
      let Pj := negSpectralProj hΦj
      let σp := h ^ (κ - 1) * (h - 1)
      let D2k := posDefPow (2 * κ) hD
      0 ≤ Φj.trace.re - σp * ((1 - Pj) * D2k).trace.re +
            (σp / ((m : ℝ) - 1)) * (Pj * D2k).trace.re ∧
      (Pj ≠ 0 → 0 < Φj.trace.re - σp * ((1 - Pj) * D2k).trace.re +
            (σp / ((m : ℝ) - 1)) * (Pj * D2k).trace.re)) :
    False := by
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos zero_lt_two _) hΛ
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  set σp : ℝ := h ^ (κ - 1) * (h - 1)
  have hσp_pos : 0 < σp := mul_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let hG : ∀ j, (Dhalf * H j * Dhalf).PosDef :=
    fun j => posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)
  let Φ : Fin m → Mat n := fun j => posDefPow κ (hG j) - D * posDefPow (κ - 1) (hG j) * D
  have hΦh : ∀ j, (Φ j).IsHermitian := fun j =>
    (posDefPow_posDef κ (hG j)).isHermitian.sub
      (posDef_conj_of_posDef hD (posDefPow_posDef (κ - 1) (hG j))).isHermitian
  have hcomm : ∀ j, D * Φ j = Φ j * D := fun j =>
    universal_commutator_theorem hΛ_pos hD (hH j) (hEq1 j)
  let P : Fin m → Mat n := fun j => negSpectralProj (hΦh j)
  let D2k := posDefPow (2 * κ) hD
  -- Step 1: Unconditional Grassmann eigenspace trace bound ∑_j Re Tr(P_j D^(2κ)) ≤ (m - 1) Re Tr(D^(2κ))
  have hgrass := sum_trace_negSpectralProj_le (κ := κ) (by omega) hD hΦh hcomm hEq2
  -- Step 2: Show ∃ j1, P j1 ≠ 0 (if all P j = 0, top eigenvector gives Φ_0 v0 = 0, contradicting Λ > 2^(2κ-1))
  have hex_neg : ∃ j1 : Fin m, P j1 ≠ 0 := by
    by_contra hall; push Not at hall
    have hΦ_psd : ∀ j, (Φ j).PosSemidef := fun j => by
      have hU := (hΦh j).spectral_theorem
      have hlam_nn : ∀ i : Fin n, 0 ≤ (hΦh j).eigenvalues i := by
        intro i
        by_contra hlt; push Not at hlt
        have hP0 := congrArg (fun X => ((hΦh j).eigenvectorUnitary : Mat n)ᴴ * X *
            ((hΦh j).eigenvectorUnitary : Mat n)) (hall j)
        dsimp only [P, negSpectralProj] at hP0
        rw [Matrix.mul_zero, Matrix.zero_mul] at hP0
        have hL : ((hΦh j).eigenvectorUnitary : Mat n)ᴴ *
            (((hΦh j).eigenvectorUnitary : Mat n) *
             Matrix.diagonal (fun k => if (hΦh j).eigenvalues k < 0 then (1 : ℂ) else 0) *
             ((hΦh j).eigenvectorUnitary : Mat n)ᴴ) *
            ((hΦh j).eigenvectorUnitary : Mat n) =
            Matrix.diagonal (fun k => if (hΦh j).eigenvalues k < 0 then (1 : ℂ) else 0) := by
          calc _ = (((hΦh j).eigenvectorUnitary : Mat n)ᴴ * ((hΦh j).eigenvectorUnitary : Mat n)) *
                    Matrix.diagonal (fun k => if (hΦh j).eigenvalues k < 0 then (1 : ℂ) else 0) *
                    (((hΦh j).eigenvectorUnitary : Mat n)ᴴ * ((hΦh j).eigenvectorUnitary : Mat n)) := by
                  simp only [Matrix.mul_assoc]
            _ = _ := by rw [unitary_conjTranspose_mul_self, Matrix.one_mul, Matrix.mul_one]
        rw [hL] at hP0
        have hi := congr_fun (congr_fun hP0 i) i
        simp [hlt] at hi
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨hΦh j, fun x => ?_⟩
      let U := (hΦh j).eigenvectorUnitary
      let z := (U : Mat n)ᴴ.mulVec x
      have hre : 0 ≤ (star x ⬝ᵥ (Φ j).mulVec x).re := by
        have hΦeq : Φ j = (U : Mat n) * Matrix.diagonal (fun i => ((hΦh j).eigenvalues i : ℂ)) * (U : Mat n)ᴴ := by
          simpa [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hU
        rw [hΦeq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
        have hst : star x ᵥ* (U : Mat n) = star z := by
          simp only [z, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
        change 0 ≤ (star x ᵥ* (U : Mat n) ⬝ᵥ (Matrix.diagonal fun i => ((hΦh j).eigenvalues i : ℂ)).mulVec z).re
        rw [hst, dotProduct, Complex.re_sum]
        refine Finset.sum_nonneg fun i _ => ?_
        simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
        have h1 : starRingEnd ℂ (z i) * (((hΦh j).eigenvalues i : ℂ) * z i) =
            ((hΦh j).eigenvalues i : ℂ) * (starRingEnd ℂ (z i) * z i) := by ring
        rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
        exact mul_nonneg (hlam_nn i) (sq_nonneg _)
      exact Complex.le_def.mpr ⟨hre, (v5_herm_dotProduct_mulVec_im (hΦh j) x).symm⟩
    -- Pick top eigenvector v0 of D and show Φ 0 *ᵥ v0 = 0
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    let evalsD := hD.isHermitian.eigenvalues
    obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ evalsD Finset.univ_nonempty
    set dmax : ℝ := evalsD i_max
    have hdmax : 0 < dmax := hD.eigenvalues_pos i_max
    have hc_pos : 0 < dmax⁻¹ := inv_pos.mpr hdmax
    let UD := hD.isHermitian.eigenvectorUnitary
    let v0 : Fin n → ℂ := (UD : Mat n).mulVec (Pi.single i_max 1)
    have hv0_ne : v0 ≠ 0 := by
      intro h0
      have h1 := congrArg (Matrix.mulVec (UD : Mat n)ᴴ) h0
      simp only [v0, Matrix.mulVec_mulVec, unitary_conjTranspose_mul_self UD, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      have := congr_fun h1 i_max; simp at this
    have hDv0 : D.mulVec v0 = (dmax : ℂ) • v0 := by
      have hDeq : D = (UD : Mat n) * Matrix.diagonal (fun i => (evalsD i : ℂ)) * (UD : Mat n)ᴴ := by
        simpa [UD, evalsD, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hD.isHermitian.spectral_theorem
      conv_lhs => rw [hDeq]
      dsimp only [v0]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rw [unitary_conjTranspose_mul_self UD, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
      apply congrArg (Matrix.mulVec (UD : Mat n))
      ext i
      by_cases hi : i = i_max
      · subst hi; simp [Matrix.mulVec_diagonal, dmax]
      · simp [Matrix.mulVec_diagonal, hi]
    let j0 : Fin m := ⟨0, by omega⟩
    have hΦ0_v0 : (Φ j0).mulVec v0 = 0 := by
      have hsum_q : ∑ j : Fin m, (star v0 ⬝ᵥ (Φ j).mulVec v0).re = 0 := by
        have h1 : (star v0 ⬝ᵥ (∑ j : Fin m, Φ j).mulVec v0).re = 0 := by
          rw [hEq2, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
        rw [← h1, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
      have hq0 : (star v0 ⬝ᵥ (Φ j0).mulVec v0).re = 0 := by
        have hnn : ∀ j ∈ Finset.univ, 0 ≤ (star v0 ⬝ᵥ (Φ j).mulVec v0).re :=
          fun j _ => posSemidef_quad_re_nonneg (hΦ_psd j) v0
        exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_q j0 (Finset.mem_univ j0)
      have hsq : CFC.sqrt (Φ j0) * CFC.sqrt (Φ j0) = Φ j0 :=
        CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr (hΦ_psd j0))
      have hsh : (CFC.sqrt (Φ j0)).IsHermitian :=
        (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
      have hnorm0 : (star ((CFC.sqrt (Φ j0)).mulVec v0) ⬝ᵥ (CFC.sqrt (Φ j0)).mulVec v0).re = 0 := by
        rw [Matrix.star_mulVec, hsh.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hsq, hq0]
      have hsv0 : (CFC.sqrt (Φ j0)).mulVec v0 = 0 := by
        rw [dotProduct, Complex.re_sum] at hnorm0
        ext i
        have hnn : ∀ k ∈ Finset.univ, 0 ≤ (star ((CFC.sqrt (Φ j0)).mulVec v0 k) *
            (CFC.sqrt (Φ j0)).mulVec v0 k).re := fun k _ => by
          rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          exact sq_nonneg _
        have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnorm0 i (Finset.mem_univ i)
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] at hi
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
      calc (Φ j0).mulVec v0 = (CFC.sqrt (Φ j0) * CFC.sqrt (Φ j0)).mulVec v0 := by rw [hsq]
        _ = (CFC.sqrt (Φ j0)).mulVec ((CFC.sqrt (Φ j0)).mulVec v0) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [hsv0, Matrix.mulVec_zero]
    -- Rescale (D, H j0) by dmax⁻¹ and apply top_eigenspace_spectral_dichotomy at μ = 0!
    let D' : Mat n := dmax⁻¹ • D
    let H' : Mat n := dmax⁻¹ • H j0
    have hD' : D'.PosDef := hD.smul hc_pos
    have hH' : H'.PosDef := (hH j0).smul hc_pos
    have hD'_le : (1 - D').PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨Matrix.isHermitian_one.sub hD'.isHermitian, fun x => ?_⟩
      have hre : 0 ≤ (star x ⬝ᵥ (1 - D').mulVec x).re := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re]
        let y : Fin n → ℂ := (UD : Mat n)ᴴ.mulVec x
        have hDeq : D = (UD : Mat n) * Matrix.diagonal (fun i => (evalsD i : ℂ)) * (UD : Mat n)ᴴ := by
          simpa [UD, evalsD, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
            using hD.isHermitian.spectral_theorem
        have hD'x : (star x ⬝ᵥ D'.mulVec x).re = ∑ i : Fin n, (dmax⁻¹ * evalsD i) * ‖y i‖ ^ 2 := by
          have hsm : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
          rw [hsm, hDeq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
            ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
          have hst : star x ᵥ* (UD : Mat n) = star y := by
            simp only [y, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
          rw [hst, dotProduct, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.re_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
          have h1 : starRingEnd ℂ (y i) * ((evalsD i : ℂ) * y i) =
              (evalsD i : ℂ) * (starRingEnd ℂ (y i) * y i) := by ring
          rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
        have hxx : (star x ⬝ᵥ x).re = ∑ i : Fin n, ‖y i‖ ^ 2 := by
          have hx_back : x = (UD : Mat n).mulVec y := by
            simp only [y, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UD, Matrix.one_mulVec]
          conv_lhs => rw [hx_back]
          rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
            unitary_conjTranspose_mul_self UD, Matrix.vecMul_one, dotProduct, Complex.re_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        rw [hD'x, hxx, sub_nonneg]
        refine Finset.sum_le_sum fun i _ => ?_
        have hle1 : dmax⁻¹ * evalsD i ≤ 1 := by
          rw [inv_mul_le_iff₀ hdmax, mul_one]; exact hi_max i (Finset.mem_univ i)
        nlinarith [sq_nonneg ‖y i‖]
      exact Complex.le_def.mpr ⟨hre, (v5_herm_dotProduct_mulVec_im (Matrix.isHermitian_one.sub hD'.isHermitian) x).symm⟩
    let D'half := posDefPow (1 / 2 : ℝ) hD'
    let hG' : (D'half * H' * D'half).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH'
    have hD'half_eq : D'half = ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) • Dhalf := posDefPow_smul (1 / 2) hc_pos hD
    have hG'_eq : D'half * H' * D'half = (dmax⁻¹ ^ (2 : ℝ)) • (Dhalf * H j0 * Dhalf) := by
      rw [hD'half_eq]
      have hHj : H' = ((dmax⁻¹ : ℝ) : ℂ) • H j0 := by ext a b; simp [H', Complex.real_smul]
      rw [hHj]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hsc : dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ * dmax⁻¹ ^ (1 / 2 : ℝ)) = dmax⁻¹ ^ (2 : ℝ) := by
        calc _ = (dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (1 / 2 : ℝ)) * dmax⁻¹ ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
          _ = dmax⁻¹ ^ ((1 / 2 : ℝ) + 1 / 2) * dmax⁻¹ ^ (1 : ℝ) := by rw [Real.rpow_add hc_pos]
          _ = dmax⁻¹ ^ (((1 / 2 : ℝ) + 1 / 2) + 1) := (Real.rpow_add hc_pos _ _).symm
          _ = dmax⁻¹ ^ (2 : ℝ) := by congr 1; norm_num
      ext a b; simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
      have hsc_c : ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (((dmax⁻¹ : ℝ) : ℂ) * ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) = ((dmax⁻¹ ^ (2 : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsc]
      linear_combination (Dhalf * H j0 * Dhalf) a b * hsc_c
    have hG'pow_eq : ∀ r : ℝ, posDefPow r hG' = ((dmax⁻¹ ^ (2 * r) : ℝ) : ℂ) • posDefPow r (hG j0) := by
      intro r
      have h2pos : 0 < dmax⁻¹ ^ (2 : ℝ) := Real.rpow_pos_of_pos hc_pos 2
      have hsm := posDefPow_smul r h2pos (hG j0)
      let U := ((hG j0).smul h2pos).isHermitian.eigenvectorUnitary
      let lam := ((hG j0).smul h2pos).isHermitian.eigenvalues
      have hspec : D'half * H' * D'half = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
        rw [hG'_eq]
        simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using ((hG j0).smul h2pos).isHermitian.spectral_theorem
      rw [posDefPow_eq_of_diag r hG' U lam (fun i => ((hG j0).smul h2pos).eigenvalues_pos i) hspec]
      change posDefPow r ((hG j0).smul h2pos) = _
      rw [hsm, ← Real.rpow_mul hc_pos.le]
    have hEq' : posDefPow (2 * κ - 1) (hD'.add hH') =
        (Λ : ℂ) • (D'half * posDefPow (κ - 1) hG' * D'half) := by
      have hsum_eq : D' + H' = dmax⁻¹ • (D + H j0) := by simp [D', H', smul_add]
      have hL : posDefPow (2 * κ - 1) (hD'.add hH') =
          ((dmax⁻¹ ^ (2 * κ - 1) : ℝ) : ℂ) • posDefPow (2 * κ - 1) (hD.add (hH j0)) := by
        let U := ((hD.add (hH j0)).smul hc_pos).isHermitian.eigenvectorUnitary
        let lam := ((hD.add (hH j0)).smul hc_pos).isHermitian.eigenvalues
        have hspec : D' + H' = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
          rw [hsum_eq]
          simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
            using ((hD.add (hH j0)).smul hc_pos).isHermitian.spectral_theorem
        rw [posDefPow_eq_of_diag (2 * κ - 1) (hD'.add hH') U lam
          (fun i => ((hD.add (hH j0)).smul hc_pos).eigenvalues_pos i) hspec]
        exact posDefPow_smul (2 * κ - 1) hc_pos (hD.add (hH j0))
      rw [hL, hEq1 j0, hG'pow_eq (κ - 1), hD'half_eq]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      have hsc : dmax⁻¹ ^ (2 * κ - 1) = dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ)) := by
        calc dmax⁻¹ ^ (2 * κ - 1) = dmax⁻¹ ^ ((1 / 2 : ℝ) + (2 * (κ - 1) + 1 / 2)) := by congr 1; ring
          _ = dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (2 * (κ - 1) + 1 / 2) := Real.rpow_add hc_pos _ _
          _ = dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ)) := by
                rw [Real.rpow_add hc_pos]
      rw [hsc]; push_cast; ring
    have hD'v0 : D'.mulVec v0 = v0 := by
      have hsm : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
      rw [hsm, Matrix.smul_mulVec, hDv0, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hdmax.ne',
        Complex.ofReal_one, one_smul]
    have hΦ'v0 : (posDefPow κ hG' - D' * posDefPow (κ - 1) hG' * D').mulVec v0 = ((0 : ℝ) : ℂ) • v0 := by
      have hsm : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
      have hsc : dmax⁻¹ * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹) = dmax⁻¹ ^ (2 * κ) := by
        calc _ = dmax⁻¹ ^ (1 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 : ℝ)) := by rw [Real.rpow_one]
          _ = dmax⁻¹ ^ (1 + (2 * (κ - 1) + 1)) := by rw [← Real.rpow_add hc_pos, ← Real.rpow_add hc_pos]
          _ = dmax⁻¹ ^ (2 * κ) := by congr 1; ring
      have hPhi'_eq : posDefPow κ hG' - D' * posDefPow (κ - 1) hG' * D' =
          ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) • Φ j0 := by
        rw [hG'pow_eq κ, hG'pow_eq (κ - 1), hsm]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
        have hcoeff : ((dmax⁻¹ : ℝ) : ℂ) * (((dmax⁻¹ ^ (2 * (κ - 1)) : ℝ) : ℂ) * ((dmax⁻¹ : ℝ) : ℂ)) =
            ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) := by rw [← hsc]; push_cast; ring
        rw [hcoeff, ← smul_sub]
      rw [hPhi'_eq, Matrix.smul_mulVec, hΦ0_v0, smul_zero, Complex.ofReal_zero, zero_smul]
    obtain ⟨h0, hh0_ge, _, hSc0, hμ0⟩ :=
      top_eigenspace_spectral_dichotomy hκ hΛ_pos le_rfl hD' hD'_le hH' hEq' hv0_ne hD'v0 hΦ'v0
    have hh0_pow_pos : 0 < h0 ^ (κ - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hh0_eq1 : h0 = 1 := by
      have := (mul_eq_zero.mp hμ0.symm).resolve_left hh0_pow_pos.ne'
      linarith
    rw [hh0_eq1, Real.one_rpow, mul_one, show (1 : ℝ) + 1 = 2 by norm_num] at hSc0
    linarith
  -- Step 3: Sum Master Trace Inequality over all j = 1..m (strict at j1!) and contradict Grassmann bound!
  obtain ⟨j1, hj1⟩ := hex_neg
  have hsum_pos : 0 < ∑ j : Fin m,
      ((Φ j).trace.re - σp * ((1 - P j) * D2k).trace.re +
        (σp / ((m : ℝ) - 1)) * (P j * D2k).trace.re) :=
    Finset.sum_pos' (fun j _ => (hMaster j).1) ⟨j1, Finset.mem_univ j1, (hMaster j1).2 hj1⟩
  have hsum_Φ : ∑ j : Fin m, (Φ j).trace.re = 0 := by
    have h1 : (∑ j : Fin m, Φ j).trace.re = 0 := by rw [hEq2, Matrix.trace_zero, Complex.zero_re]
    rw [← h1, Matrix.trace_sum, Complex.re_sum]
  have hterm_eq : ∀ j : Fin m,
      (Φ j).trace.re - σp * ((1 - P j) * D2k).trace.re +
        (σp / ((m : ℝ) - 1)) * (P j * D2k).trace.re =
      (Φ j).trace.re - σp * D2k.trace.re +
        ((m : ℝ) * σp / ((m : ℝ) - 1)) * (P j * D2k).trace.re := fun j => by
    have h1 : ((1 - P j) * D2k).trace.re = D2k.trace.re - (P j * D2k).trace.re := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re]
    rw [h1]; field_simp [hm1_pos.ne']; ring
  simp_rw [hterm_eq] at hsum_pos
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum_Φ, zero_sub,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum_pos
  have hsum_le : -(↑m * (σp * D2k.trace.re)) +
      (↑m * σp / (↑m - 1)) * ∑ j : Fin m, (P j * D2k).trace.re ≤ 0 := by
    have hcoef_nn : 0 ≤ (m : ℝ) * σp / ((m : ℝ) - 1) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hgrass hcoef_nn
    have h2 : (↑m * σp / (↑m - 1)) * ((↑m - 1) * D2k.trace.re) = ↑m * (σp * D2k.trace.re) := by
      field_simp [hm1_pos.ne']
    linarith
  linarith

/-! ==========================================================================
    PART 7: Exact Spectral-Pencil Factorization, Disjoint Kernels, RHP Roots,
            Lemma 0, & Explicit SOS Proof of ρ_{2κ}(s) < 1/2 at p ∈ {4/3, 3/2}
    ========================================================================== -/

/-- Exact Matrix-Pencil Factorization at p = 4/3 (`#19`, `p2_proof.md` Thm 2 Step 2):
    For any solution (D, H) of (D + H)³ = Λ D H D with (1 + h)³ = Λ h and EVERY r ∈ ℂ:
      (A - (1 + h) r I) L₂(r) = Λ (D - r I) M₂(r),
    where A = D + H, L₂(r) = A² + (1+h) r A + (1+h)² r² I - Λ r D, M₂(r) = H D - r D + h r² I.
    Moreover, when D ≻ 0, D^(1/2) M₂(r) D^(-1/2) = G - r D + h r² I (Hermitian for r ∈ ℝ). -/
theorem spectral_pencil_factorization_p43 {n : ℕ} {Λ h : ℝ} (hSc : (1 + h) ^ 3 = Λ * h)
    {D H : Mat n} (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D)) (r : ℂ) :
    let A : Mat n := D + H
    let t : ℂ := ((1 + h : ℝ) : ℂ)
    let L2 : Mat n := A ^ 2 + (t * r) • A + (t ^ 2 * r ^ 2) • (1 : Mat n) - ((Λ : ℂ) * r) • D
    let M2 : Mat n := H * D - r • D + ((h : ℂ) * r ^ 2) • (1 : Mat n)
    (A - (t * r) • (1 : Mat n)) * L2 = (Λ : ℂ) • ((D - r • (1 : Mat n)) * M2) ∧
    (∀ hD : D.PosDef,
      posDefPow (1 / 2 : ℝ) hD * M2 * posDefPow (-(1 / 2 : ℝ)) hD =
        posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD - r • D + ((h : ℂ) * r ^ 2) • 1) := by
  intro A t L2 M2
  have ht3 : t ^ 3 = (Λ : ℂ) * (h : ℂ) := by
    dsimp [t]; rw [← Complex.ofReal_pow, hSc, Complex.ofReal_mul]
  constructor
  · set Λc : ℂ := (Λ : ℂ)
    set hc : ℂ := (h : ℂ)
    have hA3 : A * A ^ 2 = Λc • (D * H * D) := by
      rw [← pow_succ', show (2 : ℕ) + 1 = 3 by rfl]; exact hEq
    have hL : (A - (t * r) • (1 : Mat n)) * L2 =
        Λc • (D * H * D) - (Λc * hc * r ^ 3) • (1 : Mat n) -
        (Λc * r) • (D * D) - (Λc * r) • (H * D) +
        (Λc * r ^ 2) • D + (Λc * hc * r ^ 2) • D := by
      change (A - (t * r) • (1 : Mat n)) *
        (A ^ 2 + (t * r) • A + (t ^ 2 * r ^ 2) • (1 : Mat n) - (Λc * r) • D) = _
      simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
        smul_sub, smul_smul, hA3]
      have hAA : A * A = A ^ 2 := (mat_pow_two A).symm
      have hAD : A * D = D * D + H * D := by dsimp [A]; rw [Matrix.add_mul]
      rw [hAA, hAD, smul_add (Λc * r) (D * D) (H * D)]
      have hc1 : (t ^ 2 * r ^ 2) * (t * r) = Λc * hc * r ^ 3 := by
        calc _ = t ^ 3 * r ^ 3 := by ring
          _ = Λc * hc * r ^ 3 := by rw [ht3]
      have hc2 : (t * r) * (t * r) = t ^ 2 * r ^ 2 := by ring
      have hc3 : (Λc * r) * (t * r) = Λc * r ^ 2 + Λc * hc * r ^ 2 := by
        dsimp [t, Λc, hc]; push_cast; ring
      rw [hc1, hc2, hc3, add_smul]
      abel
    have hR : Λc • ((D - r • (1 : Mat n)) * M2) =
        Λc • (D * H * D) - (Λc * hc * r ^ 3) • (1 : Mat n) -
        (Λc * r) • (D * D) - (Λc * r) • (H * D) +
        (Λc * r ^ 2) • D + (Λc * hc * r ^ 2) • D := by
      change Λc • ((D - r • (1 : Mat n)) * (H * D - r • D + (hc * r ^ 2) • (1 : Mat n))) = _
      simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
        smul_sub, smul_add, smul_smul, Matrix.mul_assoc]
      have hc1 : Λc * (r * r) = Λc * r ^ 2 := by ring
      have hc2 : Λc * (hc * r ^ 2 * r) = Λc * hc * r ^ 3 := by ring
      have hc3 : Λc * (hc * r ^ 2) = Λc * hc * r ^ 2 := by ring
      rw [hc1, hc2, hc3]; abel
    rw [hL, hR]
  · intro hD
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let Dmh := posDefPow (-(1 / 2 : ℝ)) hD
    have hinv : Dhalf * Dmh = 1 := by
      dsimp [Dhalf, Dmh]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_zero hD
    have hD_Dmh : D * Dmh = Dhalf := by
      dsimp [Dhalf, Dmh]
      calc D * posDefPow (-(1 / 2 : ℝ)) hD = posDefPow 1 hD * posDefPow (-(1 / 2 : ℝ)) hD := by rw [posDefPow_one]
        _ = posDefPow (1 + -(1 / 2 : ℝ)) hD := posDefPow_mul_posDefPow _ _ hD
        _ = posDefPow (1 / 2 : ℝ) hD := by congr 1; norm_num
    have hDhalf_D : Dhalf * D * Dmh = D := by
      calc Dhalf * D * Dmh = Dhalf * (D * Dmh) := Matrix.mul_assoc _ _ _
        _ = Dhalf * Dhalf := by rw [hD_Dmh]
        _ = D := by dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
    dsimp [M2]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    change Dhalf * (H * D) * Dmh - r • (Dhalf * D * Dmh) + ((h : ℂ) * r ^ 2) • (Dhalf * Dmh) = _
    rw [hDhalf_D, hinv]
    congr 2
    calc Dhalf * (H * D) * Dmh = Dhalf * H * (D * Dmh) := by simp only [Matrix.mul_assoc]
      _ = Dhalf * H * Dhalf := by rw [hD_Dmh]

/-- Exact Matrix-Pencil Factorization at p = 3/2 (`#19`, `p2_proof.md` Thm 2 Step 2):
    For any solution (D, M) of (D + M D M)² = Λ D M D with (1 + u²)² = Λ u and EVERY r ∈ ℂ:
      (A - (1 + u²) r I) L_{3/2}(r) = Λ (D - r I) M̃_{3/2}(r),
    where A = D + M D M, L_{3/2}(r) = (A + (1+u²)r I)(M D + u r I) - Λ r D,
    M̃_{3/2}(r) = M D M D + u r M D - r D + u² r² I. -/
theorem spectral_pencil_factorization_p32 {n : ℕ} {Λ u : ℝ} (hSc : (1 + u ^ 2) ^ 2 = Λ * u)
    {D M : Mat n} (hEq : (D + M * D * M) ^ 2 = (Λ : ℂ) • (D * M * D)) (r : ℂ) :
    let A : Mat n := D + M * D * M
    let t : ℂ := ((1 + u ^ 2 : ℝ) : ℂ)
    let L32 : Mat n := (A + (t * r) • (1 : Mat n)) * (M * D + ((u : ℂ) * r) • (1 : Mat n)) -
        ((Λ : ℂ) * r) • D
    let M32 : Mat n := M * D * M * D + ((u : ℂ) * r) • (M * D) - r • D +
        (((u ^ 2 : ℝ) : ℂ) * r ^ 2) • (1 : Mat n)
    (A - (t * r) • (1 : Mat n)) * L32 = (Λ : ℂ) • ((D - r • (1 : Mat n)) * M32) := by
  intro A t L32 M32
  have ht2 : t ^ 2 = (Λ : ℂ) * (u : ℂ) := by
    dsimp [t]; rw [← Complex.ofReal_pow, hSc, Complex.ofReal_mul]
  set Λc : ℂ := (Λ : ℂ)
  set uc : ℂ := (u : ℂ)
  set u2c : ℂ := ((u ^ 2 : ℝ) : ℂ)
  have hdiff_sq : (A - (t * r) • (1 : Mat n)) * (A + (t * r) • (1 : Mat n)) =
      Λc • (D * M * D - (uc * r ^ 2) • (1 : Mat n)) := by
    have hA2 : A ^ 2 = Λc • (D * M * D) := hEq
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul, ← mat_pow_two A, hA2, smul_sub]
    have hc : (t * r) * (t * r) = Λc * (uc * r ^ 2) := by
      calc (t * r) * (t * r) = t ^ 2 * r ^ 2 := by ring
        _ = Λc * uc * r ^ 2 := by rw [ht2]
        _ = Λc * (uc * r ^ 2) := by ring
    rw [hc]; abel
  have hL : (A - (t * r) • (1 : Mat n)) * L32 =
      Λc • (D * M * D * M * D) + (Λc * uc * r) • (D * M * D) -
      (Λc * uc * r ^ 2) • (M * D) - (Λc * u2c * r ^ 3) • (1 : Mat n) -
      (Λc * r) • (D * D) - (Λc * r) • (M * D * M * D) +
      (Λc * r ^ 2) • D + (Λc * u2c * r ^ 2) • D := by
    change (A - (t * r) • (1 : Mat n)) *
      ((A + (t * r) • (1 : Mat n)) * (M * D + (uc * r) • (1 : Mat n)) - (Λc * r) • D) = _
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hdiff_sq]
    have hAD : (A - (t * r) • (1 : Mat n)) * ((Λc * r) • D) =
        (Λc * r) • (D * D) + (Λc * r) • (M * D * M * D) -
        (Λc * r ^ 2) • D - (Λc * u2c * r ^ 2) • D := by
      change (D + M * D * M - (t * r) • (1 : Mat n)) * ((Λc * r) • D) = _
      simp only [Matrix.mul_smul, Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
        Matrix.one_mul, smul_sub, smul_add, smul_smul]
      have hc : (Λc * r) * (t * r) = Λc * r ^ 2 + Λc * u2c * r ^ 2 := by
        dsimp [t, Λc, u2c]; push_cast; ring
      rw [hc, add_smul]; abel
    rw [hAD]
    simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_smul, Matrix.mul_assoc]
    have hc1 : uc * r * Λc = Λc * uc * r := by ring
    have hc2 : Λc * (uc * r ^ 2) = Λc * uc * r ^ 2 := by ring
    have hc3 : uc * r * (Λc * (uc * r ^ 2)) = Λc * u2c * r ^ 3 := by
      dsimp [Λc, uc, u2c]; push_cast; ring
    rw [hc1, hc3, hc2]; abel
  have hR : Λc • ((D - r • (1 : Mat n)) * M32) =
      Λc • (D * M * D * M * D) + (Λc * uc * r) • (D * M * D) -
      (Λc * uc * r ^ 2) • (M * D) - (Λc * u2c * r ^ 3) • (1 : Mat n) -
      (Λc * r) • (D * D) - (Λc * r) • (M * D * M * D) +
      (Λc * r ^ 2) • D + (Λc * u2c * r ^ 2) • D := by
    change Λc • ((D - r • (1 : Mat n)) *
      (M * D * M * D + (uc * r) • (M * D) - r • D + (u2c * r ^ 2) • (1 : Mat n))) = _
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_sub, smul_add, smul_smul, Matrix.mul_assoc]
    have hc1 : Λc * (uc * r) = Λc * uc * r := by ring
    have hc2 : Λc * (u2c * r ^ 2) = Λc * u2c * r ^ 2 := by ring
    have hc3 : Λc * (uc * r * r) = Λc * uc * r ^ 2 := by ring
    have hc4 : Λc * (r * r) = Λc * r ^ 2 := by ring
    have hc5 : Λc * (u2c * r ^ 2 * r) = Λc * u2c * r ^ 3 := by ring
    rw [hc1, hc2, hc3, hc4, hc5]; abel
  rw [hL, hR]

/-- Exact Disjoint Left Kernels of the Spectral Pencil M₂(r₀) at p = 4/3 (`#19`, `p2_proof.md` Thm 2 Step 3):
    Under h D - H ⪰ 0 and ker(H - h D) = {0}, for every r₀ > 0:
      (1) Every w ∈ ker(A - (1+h) r₀ I) produces a left kernel vector y₁* = w*(D - r₀ I) of M₂(r₀),
          injectively;
      (2) Every e ∈ ker(D - r₀ I) ∩ ker(Φ - (h² - h) r₀⁴ I) produces a left kernel vector
          y₂* = e*(H - h r₀ I) D of M₂(r₀), injectively;
      (3) The two subspaces are disjoint: W₁(r₀) ∩ W₂(r₀) = {0}! -/
theorem spectral_pencil_disjoint_kernels_p43 {n : ℕ} {Λ h r0 : ℝ}
    (hΛ : 0 < Λ) (_hh : 0 < h) (hr0 : 0 < r0) (hSc : (1 + h) ^ 3 = Λ * h)
    {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef)
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D))
    (hDom : ((h : ℂ) • D - H).PosSemidef)
    (hNoDec : ∀ v : Fin n → ℂ, (H - (h : ℂ) • D).mulVec v = 0 → v = 0) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let G := Dhalf * H * Dhalf
    let Φ := G ^ 2 - D * G * D
    let M2 : Mat n := H * D - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)
    (∀ w : Fin n → ℂ, (D + H).mulVec w = (((1 + h) * r0 : ℝ) : ℂ) • w →
      (star ((D - (r0 : ℂ) • (1 : Mat n)).mulVec w) ᵥ* M2 = 0) ∧
      ((D - (r0 : ℂ) • (1 : Mat n)).mulVec w = 0 → w = 0)) ∧
    (∀ e : Fin n → ℂ, D.mulVec e = (r0 : ℂ) • e →
      Φ.mulVec e = (((h ^ 2 - h) * r0 ^ 4 : ℝ) : ℂ) • e →
      (star (D.mulVec ((H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e)) ᵥ* M2 = 0) ∧
      (D.mulVec ((H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) = 0 → e = 0)) ∧
    (∀ w e : Fin n → ℂ, D.mulVec e = (r0 : ℂ) • e →
      (D - (r0 : ℂ) • (1 : Mat n)).mulVec w =
        D.mulVec ((H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) →
      e = 0 ∧ (D - (r0 : ℂ) • (1 : Mat n)).mulVec w = 0) := by
  intro Dhalf G Φ M2
  have hfac := (spectral_pencil_factorization_p43 hSc hEq (r0 : ℂ)).1
  have hM2_eq : H * D - (r0 : ℂ) • D + ((h : ℂ) * (r0 : ℂ) ^ 2) • (1 : Mat n) = M2 := by
    change H * D - (r0 : ℂ) • D + ((h : ℂ) * (r0 : ℂ) ^ 2) • (1 : Mat n) =
      H * D - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hM2_eq] at hfac
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1): W₁(r₀)
    intro w hw
    constructor
    · have hAw : ((D + H) - (((1 + h : ℝ) : ℂ) * (r0 : ℂ)) • (1 : Mat n)).mulVec w = 0 := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hw]
        have : (((1 + h : ℝ) : ℂ) * (r0 : ℂ)) = (((1 + h) * r0 : ℝ) : ℂ) := by push_cast; rfl
        rw [this, sub_self]
      have hstar_Aw : star w ᵥ* ((D + H) - (((1 + h : ℝ) : ℂ) * (r0 : ℂ)) • (1 : Mat n)) = 0 := by
        have hAh : ((D + H) - (((1 + h : ℝ) : ℂ) * (r0 : ℂ)) • (1 : Mat n))ᴴ =
            (D + H) - (((1 + h : ℝ) : ℂ) * (r0 : ℂ)) • (1 : Mat n) := by
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
            Matrix.conjTranspose_one, hD.isHermitian.eq, hH.isHermitian.eq,
            Complex.star_def, map_mul, Complex.conj_ofReal]
        rw [← hAh, ← Matrix.star_mulVec, hAw, star_zero]
      have h0 : star w ᵥ* ((Λ : ℂ) • ((D - (r0 : ℂ) • (1 : Mat n)) * M2)) = 0 := by
        rw [← hfac, ← Matrix.vecMul_vecMul, hstar_Aw, Matrix.zero_vecMul]
      rw [Matrix.vecMul_smul, ← Matrix.vecMul_vecMul] at h0
      have h1 : (star w ᵥ* (D - (r0 : ℂ) • (1 : Mat n))) ᵥ* M2 = 0 :=
        smul_right_injective (Fin n → ℂ) (Complex.ofReal_ne_zero.mpr hΛ.ne') (by simpa using h0)
      have hDr_h : (D - (r0 : ℂ) • (1 : Mat n))ᴴ = D - (r0 : ℂ) • (1 : Mat n) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          hD.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
      rwa [Matrix.star_mulVec, hDr_h]
    · intro hDw0
      have hDw : D.mulVec w = (r0 : ℂ) • w := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hDw0
        exact sub_eq_zero.mp hDw0
      have hHw : (H - (h : ℂ) • D).mulVec w = 0 := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hDw, smul_smul]
        rw [Matrix.add_mulVec, hDw] at hw
        have : H.mulVec w = (((1 + h) * r0 : ℝ) : ℂ) • w - (r0 : ℂ) • w := eq_sub_of_add_eq' hw
        rw [this, ← sub_smul, ← sub_smul]
        have hc : (((1 + h) * r0 : ℝ) : ℂ) - (r0 : ℂ) - (h : ℂ) * (r0 : ℂ) = 0 := by push_cast; ring
        rw [hc, zero_smul]
      exact hNoDec w hHw
  · -- Part (2): W₂(r₀)
    intro e hDe hΦe
    constructor
    · let P_herm : Mat n := G - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)
      have hPh : P_hermᴴ = P_herm := by
        have hGh : Gᴴ = G := (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH).isHermitian.eq
        change (G - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n))ᴴ =
          G - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_one, hGh, hD.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
      have hDGe : (D * G * D).mulVec e = (r0 : ℂ) • (D * G).mulVec e := by
        rw [← Matrix.mulVec_mulVec e (D * G) D, hDe, Matrix.mulVec_smul]
      have hprod : (P_herm * (G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n))).mulVec e = 0 := by
        have hG2e : G.mulVec (G.mulVec e) = (r0 : ℂ) • D.mulVec (G.mulVec e) +
            (((h ^ 2 - h) * r0 ^ 4 : ℝ) : ℂ) • e := by
          have hΦe' : (G ^ 2 - D * G * D).mulVec e = (((h ^ 2 - h) * r0 ^ 4 : ℝ) : ℂ) • e := hΦe
          rw [Matrix.sub_mulVec, hDGe, mat_pow_two, ← Matrix.mulVec_mulVec e G G,
            ← Matrix.mulVec_mulVec e D G] at hΦe'
          rw [add_comm]; exact eq_add_of_sub_eq hΦe'
        rw [← Matrix.mulVec_mulVec e P_herm (G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)),
          Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_sub, Matrix.mulVec_smul]
        change (G - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)).mulVec (G.mulVec e) -
          ((h * r0 ^ 2 : ℝ) : ℂ) • (G - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)).mulVec e = 0
        simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hDe, hG2e]
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        push_cast; ring
      have hGh2 : (G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n))ᴴ = G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n) := by
        have hGh : Gᴴ = G := (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH).isHermitian.eq
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          hGh, Complex.star_def, Complex.conj_ofReal]
      have hstar0 : star ((G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) ᵥ* P_herm = 0 := by
        rw [Matrix.star_mulVec, hGh2, Matrix.vecMul_vecMul]
        have h1 : (P_herm * (G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)))ᴴ =
            (G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)) * P_herm := by
          rw [Matrix.conjTranspose_mul, hPh, hGh2]
        rw [← h1, ← Matrix.star_mulVec, hprod, star_zero]
      have hsim := (spectral_pencil_factorization_p43 hSc hEq (r0 : ℂ)).2 hD
      rw [hM2_eq] at hsim
      have hP_Dhalf : P_herm * Dhalf = Dhalf * M2 := by
        have hDmh_sq : posDefPow (-(1 / 2 : ℝ)) hD * Dhalf = 1 := by
          dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_zero hD
        have hP_eq : P_herm = Dhalf * M2 * posDefPow (-(1 / 2 : ℝ)) hD := by
          rw [hsim]
          change G - (r0 : ℂ) • D + ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n) =
            G - (r0 : ℂ) • D + ((h : ℂ) * (r0 : ℂ) ^ 2) • (1 : Mat n)
          rw [Complex.ofReal_mul, Complex.ofReal_pow]
        rw [hP_eq, Matrix.mul_assoc, hDmh_sq, Matrix.mul_one]
      have hstar_M2 : (star ((G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) ᵥ* Dhalf) ᵥ* M2 = 0 := by
        rw [Matrix.vecMul_vecMul, ← hP_Dhalf, ← Matrix.vecMul_vecMul, hstar0, Matrix.zero_vecMul]
      by_cases he0 : e = 0
      · subst he0; simp
      · have hDhalf_e : Dhalf.mulVec e = ((r0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) • e :=
          (posDefPow_mulVec_of_eig (1 / 2) hD he0 hDe).2
        have hDhalf_sq : Dhalf * Dhalf = D := by
          dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
        have hDhalf_h : Dhalfᴴ = Dhalf := (posDefPow_posDef (1 / 2) hD).isHermitian.eq
        have hvec_eq : Dhalf.mulVec ((G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) =
            ((r0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) • D.mulVec ((H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) := by
          simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
            Matrix.mulVec_smul, hDhalf_e, hDe, smul_sub, smul_smul]
          have h1 : Dhalf.mulVec (G.mulVec e) = ((r0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) • D.mulVec (H.mulVec e) := by
            dsimp only [G]
            calc Dhalf.mulVec ((Dhalf * H * Dhalf).mulVec e)
                = (Dhalf * Dhalf * H).mulVec (Dhalf.mulVec e) := by
                    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
              _ = (D * H).mulVec (((r0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) • e) := by rw [hDhalf_sq, hDhalf_e]
              _ = ((r0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) • D.mulVec (H.mulVec e) := by
                    rw [Matrix.mulVec_smul, ← Matrix.mulVec_mulVec]
          rw [h1]
          ext i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast; ring
        have hstar_eq : star ((G - ((h * r0 ^ 2 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) ᵥ* Dhalf =
            ((r0 ^ (1 / 2 : ℝ) : ℝ) : ℂ) • star (D.mulVec ((H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e)) := by
          rw [← hDhalf_h, ← Matrix.star_mulVec, hvec_eq]
          ext i; simp
        rw [hstar_eq, Matrix.smul_vecMul] at hstar_M2
        exact smul_right_injective (Fin n → ℂ)
          (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hr0 _).ne') (by simpa using hstar_M2)
    · intro h0
      have h1 : (H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e = 0 := by
        by_contra hne; exact posDef_mulVec_ne_zero hD hne h0
      have h2 : (H - (h : ℂ) • D).mulVec e = 0 := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hDe, smul_smul]
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
        have : (h : ℂ) * (r0 : ℂ) = ((h * r0 : ℝ) : ℂ) := by push_cast; rfl
        rw [this]; exact h1
      exact hNoDec e h2
  · -- Part (3): Disjointness W₁(r₀) ∩ W₂(r₀) = {0}
    intro w e hDe heq
    have hdot0 : star e ⬝ᵥ (D - (r0 : ℂ) • (1 : Mat n)).mulVec w = 0 := by
      have hDr_h : (D - (r0 : ℂ) • (1 : Mat n))ᴴ = D - (r0 : ℂ) • (1 : Mat n) := by
        simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
          hD.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
      have hDre : (D - (r0 : ℂ) • (1 : Mat n)).mulVec e = 0 := by
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hDe, sub_self]
      rw [Matrix.dotProduct_mulVec, ← hDr_h, ← Matrix.star_mulVec, hDre, star_zero, zero_dotProduct]
    rw [heq] at hdot0
    have hdot_rhs : star e ⬝ᵥ D.mulVec ((H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e) =
        -((r0 : ℂ) * (star e ⬝ᵥ ((h : ℂ) • D - H).mulVec e)) := by
      rw [Matrix.dotProduct_mulVec]
      have hst : star e ᵥ* D = (r0 : ℂ) • star e := by
        rw [← hD.isHermitian.eq, ← Matrix.star_mulVec, hDe]
        ext i; simp
      rw [hst, smul_dotProduct, smul_eq_mul]
      have hvec : (H - ((h * r0 : ℝ) : ℂ) • (1 : Mat n)).mulVec e = -(((h : ℂ) • D - H).mulVec e) := by
        rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
          Matrix.one_mulVec, hDe, smul_smul]
        have : ((h * r0 : ℝ) : ℂ) = (h : ℂ) * (r0 : ℂ) := by push_cast; rfl
        rw [this]; abel
      rw [hvec, dotProduct_neg, mul_neg]
    rw [hdot_rhs, neg_eq_zero] at hdot0
    have hq0 : star e ⬝ᵥ ((h : ℂ) • D - H).mulVec e = 0 :=
      (mul_eq_zero.mp hdot0).resolve_left (Complex.ofReal_ne_zero.mpr hr0.ne')
    have hsq : CFC.sqrt ((h : ℂ) • D - H) * CFC.sqrt ((h : ℂ) • D - H) = (h : ℂ) • D - H :=
      CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hDom)
    have hsh : (CFC.sqrt ((h : ℂ) • D - H)).IsHermitian :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
    have hnorm0 : (star ((CFC.sqrt ((h : ℂ) • D - H)).mulVec e) ⬝ᵥ
        (CFC.sqrt ((h : ℂ) • D - H)).mulVec e).re = 0 := by
      rw [Matrix.star_mulVec, hsh.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hsq, hq0, Complex.zero_re]
    have hse0 : (CFC.sqrt ((h : ℂ) • D - H)).mulVec e = 0 := by
      rw [dotProduct, Complex.re_sum] at hnorm0
      ext i
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ (star ((CFC.sqrt ((h : ℂ) • D - H)).mulVec e k) *
          (CFC.sqrt ((h : ℂ) • D - H)).mulVec e k).re := fun k _ => by
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        exact sq_nonneg _
      have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hnorm0 i (Finset.mem_univ i)
      rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] at hi
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hDom_e : ((h : ℂ) • D - H).mulVec e = 0 := by
      calc ((h : ℂ) • D - H).mulVec e
          = (CFC.sqrt ((h : ℂ) • D - H) * CFC.sqrt ((h : ℂ) • D - H)).mulVec e := by rw [hsq]
        _ = (CFC.sqrt ((h : ℂ) • D - H)).mulVec ((CFC.sqrt ((h : ℂ) • D - H)).mulVec e) :=
              (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [hse0, Matrix.mulVec_zero]
    have he0 : e = 0 := hNoDec e (by
      have : H - (h : ℂ) • D = -((h : ℂ) • D - H) := by abel
      rw [this, Matrix.neg_mulVec, hDom_e, neg_zero])
    refine ⟨he0, ?_⟩
    rw [heq, he0, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Right-Half-Plane Root Theorem for the p = 4/3 Quadratic Matrix Pencil (`#19`, `p2_proof.md` Step 4):
    Every root r ∈ ℂ of (h r² I - r D + G) u = 0 (u ≠ 0, h > 0, D, G ≻ 0) satisfies Re(r) > 0 strictly! -/
theorem spectral_pencil_rhp_roots_p43 {n : ℕ} {h : ℝ} (hh : 0 < h)
    {D G : Mat n} (hD : D.PosDef) (hG : G.PosDef)
    {r : ℂ} {u : Fin n → ℂ} (hu : u ≠ 0)
    (hroot : (((h : ℂ) * r ^ 2) • (1 : Mat n) - r • D + G).mulVec u = 0) :
    0 < r.re := by
  have hdot : star u ⬝ᵥ (((h : ℂ) * r ^ 2) • (1 : Mat n) - r • D + G).mulVec u = 0 := by
    rw [hroot, dotProduct_zero]
  set nv : ℝ := (star u ⬝ᵥ u).re
  set dv : ℝ := (star u ⬝ᵥ D.mulVec u).re
  set gv : ℝ := (star u ⬝ᵥ G.mulVec u).re
  have hnv : 0 < nv := by
    dsimp [nv]; rw [dotProduct, Complex.re_sum]
    obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := by by_contra h0; push Not at h0; exact hu (funext h0)
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg _
    · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_pos_of_pos (norm_pos_iff.mpr hi0)
  have hdv : 0 < dv := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hD).2 hu)).1
  have hgv : 0 < gv := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hG).2 hu)).1
  have hnv_c : star u ⬝ᵥ u = (nv : ℂ) :=
    Complex.ext rfl (by simp [v5_dotProduct_star_self_im])
  have hdv_c : star u ⬝ᵥ D.mulVec u = (dv : ℂ) :=
    Complex.ext rfl (by simp [v5_herm_dotProduct_mulVec_im hD.isHermitian])
  have hgv_c : star u ⬝ᵥ G.mulVec u = (gv : ℂ) :=
    Complex.ext rfl (by simp [v5_herm_dotProduct_mulVec_im hG.isHermitian])
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    hnv_c, hdv_c, hgv_c] at hdot
  have hre := congrArg Complex.re hdot
  have him := congrArg Complex.im hdot
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_re, Complex.zero_im,
    sq, zero_mul, mul_zero, sub_zero, add_zero] at hre him
  ring_nf at hre him
  by_cases him0 : r.im = 0
  · rw [him0] at hre
    have h1 : dv * r.re = h * nv * (r.re * r.re) + gv := by linarith
    have hhnv : 0 < h * nv := mul_pos hh hnv
    have hpos : 0 < h * nv * (r.re * r.re) + gv := by nlinarith only [hhnv, hgv, mul_self_nonneg r.re]
    nlinarith only [h1, hpos, hdv]
  · have hfac : r.im * (2 * h * nv * r.re - dv) = 0 := by linarith
    have h2 : 2 * h * nv * r.re = dv := sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left him0)
    have hhnv : 0 < h * nv := mul_pos hh hnv
    nlinarith only [h2, hhnv, hdv]

/-- Lemma 0 (`p2_proof.md`): For ALL κ > 1 and EVERY lower root 0 < h_- < (κ - 1)/κ of
    (1 + h_-)^(2κ - 1) = Λ h_-^(κ - 1), setting σ_- := h_-^(κ - 1) (1 - h_-):
      Λ σ_- > 1 strictly!
    Consequently, whenever (m - 1) σ_- ≤ σ_+ = h_+^(κ - 1) (h_+ - 1) with (1 + h_+)^(2κ - 1) = Λ h_+^(κ - 1):
      m - 1 < (1 + h_+)^(2κ - 1) (h_+ - 1) strictly! -/
theorem lemma0_lambda_sigma_minus_gt_one {κ Λ hm : ℝ} (hκ : 1 < κ)
    (hhm0 : 0 < hm) (hhm_lt : hm < (κ - 1) / κ)
    (hSc_m : (1 + hm) ^ (2 * κ - 1) = Λ * hm ^ (κ - 1)) :
    let σm := hm ^ (κ - 1) * (1 - hm)
    1 < Λ * σm ∧
    (∀ {m : ℕ} {hp : ℝ}, 2 ≤ m → 1 < hp → (1 + hp) ^ (2 * κ - 1) = Λ * hp ^ (κ - 1) →
      ((m : ℝ) - 1) * σm ≤ hp ^ (κ - 1) * (hp - 1) →
      (m : ℝ) - 1 < (1 + hp) ^ (2 * κ - 1) * (hp - 1)) := by
  intro σm
  have hκ0 : 0 < κ := by linarith
  have hΛσm : Λ * σm = (1 + hm) ^ (2 * κ - 1) * (1 - hm) := by
    dsimp [σm]
    calc Λ * (hm ^ (κ - 1) * (1 - hm)) = (Λ * hm ^ (κ - 1)) * (1 - hm) := by ring
      _ = (1 + hm) ^ (2 * κ - 1) * (1 - hm) := by rw [hSc_m]
  have hgt1 : 1 < Λ * σm := by
    rw [hΛσm]
    let u : ℝ → ℝ := fun x => (1 + x) ^ (2 * κ - 1) * (1 - x)
    let u' : ℝ → ℝ := fun x => 2 * κ * (1 + x) ^ (2 * κ - 2) * ((κ - 1) / κ - x)
    have hcont : ContinuousOn u (Set.Icc 0 hm) :=
      ((continuousOn_const.add continuousOn_id).rpow_const
        (fun x hx => Or.inl (by linarith [hx.1] : (0 : ℝ) < 1 + x).ne')).mul
        (continuousOn_const.sub continuousOn_id)
    have hderiv : ∀ x ∈ Set.Ioo 0 hm, HasDerivAt u (u' x) x := fun x hx => by
      have hx1 : 0 < 1 + x := by linarith [hx.1]
      have h1 := ((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (p := 2 * κ - 1) (Or.inl hx1.ne')
      have h2 : HasDerivAt (fun y => 1 - y) (0 - 1) x := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
      refine (h1.mul h2).congr_deriv ?_
      dsimp [u']
      have hpow : (1 + x) ^ (2 * κ - 1) = (1 + x) ^ (2 * κ - 2) * (1 + x) := by
        calc (1 + x) ^ (2 * κ - 1) = (1 + x) ^ ((2 * κ - 2) + 1) := by congr 1; ring
          _ = (1 + x) ^ (2 * κ - 2) * (1 + x) ^ (1 : ℝ) := Real.rpow_add hx1 _ _
          _ = (1 + x) ^ (2 * κ - 2) * (1 + x) := by rw [Real.rpow_one]
      have hexp : 2 * κ - 1 - 1 = 2 * κ - 2 := by ring
      rw [hexp, hpow]
      field_simp [hκ0.ne']; ring
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope u u' hhm0 hcont hderiv
    have hu'c : 0 < u' c := by
      dsimp [u']
      have h1 : 0 < (1 + c) ^ (2 * κ - 2) := Real.rpow_pos_of_pos (by linarith [hc.1]) _
      have h2 : 0 < (κ - 1) / κ - c := by linarith [hc.2]
      positivity
    have hu0 : u 0 = 1 := by simp [u]
    have hdiv : 0 < (u hm - 1) / hm := by
      have h1 : 0 < (u hm - u 0) / (hm - 0) := by rw [← hslope]; exact hu'c
      rwa [hu0, sub_zero] at h1
    have : 0 < u hm - 1 := by
      rwa [div_pos_iff_of_pos_right hhm0] at hdiv
    dsimp [u] at this; linarith
  refine ⟨hgt1, fun {m hp} hm2 hhp hSc_p hbal => ?_⟩
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    linarith
  have hΛ_pos : 0 < Λ := by
    have h1 : 0 < (1 + hp) ^ (2 * κ - 1) := Real.rpow_pos_of_pos (by linarith) _
    have h2 : 0 < hp ^ (κ - 1) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith only [hSc_p, h1, h2]
  calc (m : ℝ) - 1 < ((m : ℝ) - 1) * (Λ * σm) := by nlinarith only [hgt1, hm1_pos]
    _ = Λ * (((m : ℝ) - 1) * σm) := by ring
    _ ≤ Λ * (hp ^ (κ - 1) * (hp - 1)) := mul_le_mul_of_nonneg_left hbal hΛ_pos.le
    _ = (Λ * hp ^ (κ - 1)) * (hp - 1) := by ring
    _ = (1 + hp) ^ (2 * κ - 1) * (hp - 1) := by rw [hSc_p]

/-- Elementary l^k ≤ l^1 power-sum inequality: for d_i ≥ 0 and k ≥ 1, ∑ d_i^k ≤ (∑ d_i)^k. -/
private lemma sum_pow_le_pow_sum {s : ℕ} {d : Fin s → ℝ} (hd : ∀ i, 0 ≤ d i) (k : ℕ) (hk : 1 ≤ k) :
    ∑ i : Fin s, (d i) ^ k ≤ (∑ i : Fin s, d i) ^ k := by
  have hle : ∀ i : Fin s, (d i) ^ k ≤ d i * (∑ j : Fin s, d j) ^ (k - 1) := fun i => by
    have hdi_le : d i ≤ ∑ j : Fin s, d j := Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
    have hpow_le : (d i) ^ (k - 1) ≤ (∑ j : Fin s, d j) ^ (k - 1) :=
      pow_le_pow_left₀ (hd i) hdi_le (k - 1)
    have hsplit : (d i) ^ k = d i * (d i) ^ (k - 1) := by
      cases k with
      | zero => omega
      | succ k' => simp [pow_succ']
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hpow_le (hd i)
  calc ∑ i : Fin s, (d i) ^ k
      ≤ ∑ i : Fin s, d i * (∑ j : Fin s, d j) ^ (k - 1) := Finset.sum_le_sum fun i _ => hle i
    _ = (∑ i : Fin s, d i) * (∑ j : Fin s, d j) ^ (k - 1) := (Finset.sum_mul _ _ _).symm
    _ = (∑ i : Fin s, d i) ^ k := by
          cases k with
          | zero => omega
          | succ k' => simp [pow_succ']

/-- Explicit SOS Proof of Uniform S_p Branching Contraction ρ₄(s) < 1/2 at p = 4/3 (`#19`, `p2_proof.md` Thm 2):
    For ALL m ≥ 2, ALL h > 1, ALL s ≥ 0, and ALL child weights d_i > 0 satisfying
      ∑ d_i < 1 / (h² + h - 1)   and   m - 1 < (1 + h)³ (h - 1):
      ρ₄ := (m - 1) ∑ d_i⁴ < (1 + h)³ (h - 1) / (h² + h - 1)⁴ < 1/2
    via the exact explicit SOS identity
      (t² + 3t + 1)⁴ - 2 t (t + 2)³ = t⁸ + 12 t⁷ + 58 t⁶ + 144 t⁵ + 193 t⁴ + 132 t³ + 30 t² + (2t - 1)² > 0!
    Plus unconditional Tree Negative Trace Drift: Tr(Φ) < -(σ_+ / (2 m)) Tr(D⁴) < 0! -/
theorem spectral_pencil_rho4_lt_half {m s : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 1 < h)
    (hm_lt : (m : ℝ) - 1 < (1 + h) ^ 3 * (h - 1))
    {d : Fin s → ℝ} (hd_pos : ∀ i, 0 < d i)
    (hsum_lt : ∑ i : Fin s, d i < 1 / (h ^ 2 + h - 1)) :
    let ρ4 : ℝ := ((m : ℝ) - 1) * ∑ i : Fin s, (d i) ^ 4
    let σp : ℝ := h * (h - 1)
    let trPhi : ℝ := σp * (-(1 / ((m : ℝ) - 1)) + ∑ i : Fin s, (d i) ^ 4)
    let trD4 : ℝ := 1 + ∑ i : Fin s, (d i) ^ 4
    ρ4 < (1 + h) ^ 3 * (h - 1) / (h ^ 2 + h - 1) ^ 4 ∧
    (1 + h) ^ 3 * (h - 1) / (h ^ 2 + h - 1) ^ 4 < 1 / 2 ∧
    ρ4 < 1 / 2 ∧
    trPhi < -(σp / (2 * (m : ℝ))) * trD4 ∧
    trPhi < 0 := by
  intro ρ4 σp trPhi trD4
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  set t : ℝ := h - 1
  have ht : 0 < t := by linarith
  have hden_pos : 0 < h ^ 2 + h - 1 := by nlinarith
  have hsum_nn : 0 ≤ ∑ i : Fin s, d i := Finset.sum_nonneg fun i _ => (hd_pos i).le
  have hpow_lt : ∑ i : Fin s, (d i) ^ 4 < (1 / (h ^ 2 + h - 1)) ^ 4 := by
    calc ∑ i : Fin s, (d i) ^ 4
        ≤ (∑ i : Fin s, d i) ^ 4 := sum_pow_le_pow_sum (fun i => (hd_pos i).le) 4 (by norm_num)
      _ < (1 / (h ^ 2 + h - 1)) ^ 4 := pow_lt_pow_left₀ hsum_lt hsum_nn (by norm_num)
  have hρ4_lt_frac : ρ4 < (1 + h) ^ 3 * (h - 1) / (h ^ 2 + h - 1) ^ 4 := by
    have h1 : ρ4 < ((m : ℝ) - 1) * (1 / (h ^ 2 + h - 1)) ^ 4 :=
      mul_lt_mul_of_pos_left hpow_lt hm1_pos
    have h2 : ((m : ℝ) - 1) * (1 / (h ^ 2 + h - 1)) ^ 4 <
        ((1 + h) ^ 3 * (h - 1)) * (1 / (h ^ 2 + h - 1)) ^ 4 :=
      mul_lt_mul_of_pos_right hm_lt (by positivity)
    have h3 : ((1 + h) ^ 3 * (h - 1)) * (1 / (h ^ 2 + h - 1)) ^ 4 =
        (1 + h) ^ 3 * (h - 1) / (h ^ 2 + h - 1) ^ 4 := by rw [one_div, inv_pow, div_eq_mul_inv]
    linarith
  have hfrac_lt_half : (1 + h) ^ 3 * (h - 1) / (h ^ 2 + h - 1) ^ 4 < 1 / 2 := by
    rw [div_lt_div_iff₀ (pow_pos hden_pos 4) two_pos]
    have hSOS : (h ^ 2 + h - 1) ^ 4 - 2 * ((1 + h) ^ 3 * (h - 1)) =
        t ^ 8 + 12 * t ^ 7 + 58 * t ^ 6 + 144 * t ^ 5 + 193 * t ^ 4 +
        132 * t ^ 3 + 30 * t ^ 2 + (2 * t - 1) ^ 2 := by dsimp [t]; ring
    have hpos : 0 < t ^ 8 + 12 * t ^ 7 + 58 * t ^ 6 + 144 * t ^ 5 + 193 * t ^ 4 +
        132 * t ^ 3 + 30 * t ^ 2 + (2 * t - 1) ^ 2 := by positivity
    linarith
  have hρ4_lt_half : ρ4 < 1 / 2 := lt_trans hρ4_lt_frac hfrac_lt_half
  have hσp_pos : 0 < σp := mul_pos (by linarith) ht
  have htrPhi_eq : trPhi = σp / ((m : ℝ) - 1) * (ρ4 - 1) := by
    dsimp [trPhi, ρ4]; field_simp [hm1_pos.ne']; ring
  have htrD4_lt : trD4 < (m : ℝ) / ((m : ℝ) - 1) := by
    have h1 : ∑ i : Fin s, (d i) ^ 4 < 1 / (2 * ((m : ℝ) - 1)) := by
      dsimp [ρ4] at hρ4_lt_half
      rw [lt_div_iff₀ (by positivity)]; linarith
    have h2 : 1 + 1 / (2 * ((m : ℝ) - 1)) < (m : ℝ) / ((m : ℝ) - 1) := by
      have : (m : ℝ) / ((m : ℝ) - 1) - (1 + 1 / (2 * ((m : ℝ) - 1))) = 1 / (2 * ((m : ℝ) - 1)) := by
        field_simp [hm1_pos.ne']; ring
      have : 0 < 1 / (2 * ((m : ℝ) - 1)) := by positivity
      linarith
    dsimp [trD4]; linarith
  have htrPhi_drift : trPhi < -(σp / (2 * (m : ℝ))) * trD4 := by
    have h1 : trPhi < -(σp / (2 * ((m : ℝ) - 1))) := by
      rw [htrPhi_eq]
      have hlt := mul_lt_mul_of_pos_left (show ρ4 - 1 < -(1 / 2 : ℝ) by linarith) (div_pos hσp_pos hm1_pos)
      have heq : σp / ((m : ℝ) - 1) * (-(1 / 2 : ℝ)) = -(σp / (2 * ((m : ℝ) - 1))) := by
        field_simp [hm1_pos.ne']
      linarith
    have h2 : -(σp / (2 * ((m : ℝ) - 1))) < -(σp / (2 * (m : ℝ))) * trD4 := by
      have h3 : (σp / (2 * (m : ℝ))) * trD4 < (σp / (2 * (m : ℝ))) * ((m : ℝ) / ((m : ℝ) - 1)) :=
        mul_lt_mul_of_pos_left htrD4_lt (by positivity)
      have h4 : (σp / (2 * (m : ℝ))) * ((m : ℝ) / ((m : ℝ) - 1)) = σp / (2 * ((m : ℝ) - 1)) := by
        field_simp [hm_pos.ne', hm1_pos.ne']
      linarith
    linarith
  have htrPhi_neg : trPhi < 0 := by
    have htrD4_pos : 0 < trD4 := by
      dsimp [trD4]
      have : 0 ≤ ∑ i : Fin s, (d i) ^ 4 := Finset.sum_nonneg fun i _ => pow_nonneg (hd_pos i).le 4
      linarith
    have : 0 < (σp / (2 * (m : ℝ))) * trD4 := by positivity
    linarith
  exact ⟨hρ4_lt_frac, hfrac_lt_half, hρ4_lt_half, htrPhi_drift, htrPhi_neg⟩

/-- Explicit Polynomial Proof of Uniform S_p Branching Contraction ρ₃(s) < 1/2 at p = 3/2 (`#19`, `p2_proof.md` Thm 2):
    For ALL m ≥ 2, ALL h > 1, ALL s ≥ 0, and ALL child weights d_i > 0 satisfying
      ∑ d_i < 1 / (h² + h - 1)   and   m - 1 < (1 + h)² (h - 1):
      ρ₃ := (m - 1) ∑ d_i³ < (1 + h)² (h - 1) / (h² + h - 1)³ < 1/2
    via the exact positive-coefficient polynomial identity
      (t² + 3t + 1)³ - 2 t (t + 2)² = t⁶ + 9 t⁵ + 30 t⁴ + 43 t³ + 22 t² + t + 1 > 0!
    Plus unconditional Tree Negative Trace Drift: Tr(Φ) < -(σ_+ / (2 m)) Tr(D³) < 0! -/
theorem spectral_pencil_rho3_lt_half {m s : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 1 < h)
    (hm_lt : (m : ℝ) - 1 < (1 + h) ^ 2 * (h - 1))
    {d : Fin s → ℝ} (hd_pos : ∀ i, 0 < d i)
    (hsum_lt : ∑ i : Fin s, d i < 1 / (h ^ 2 + h - 1)) :
    let ρ3 : ℝ := ((m : ℝ) - 1) * ∑ i : Fin s, (d i) ^ 3
    let σp : ℝ := Real.sqrt h * (h - 1)
    let trPhi : ℝ := σp * (-(1 / ((m : ℝ) - 1)) + ∑ i : Fin s, (d i) ^ 3)
    let trD3 : ℝ := 1 + ∑ i : Fin s, (d i) ^ 3
    ρ3 < (1 + h) ^ 2 * (h - 1) / (h ^ 2 + h - 1) ^ 3 ∧
    (1 + h) ^ 2 * (h - 1) / (h ^ 2 + h - 1) ^ 3 < 1 / 2 ∧
    ρ3 < 1 / 2 ∧
    trPhi < -(σp / (2 * (m : ℝ))) * trD3 ∧
    trPhi < 0 := by
  intro ρ3 σp trPhi trD3
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  set t : ℝ := h - 1
  have ht : 0 < t := by linarith
  have hden_pos : 0 < h ^ 2 + h - 1 := by nlinarith
  have hsum_nn : 0 ≤ ∑ i : Fin s, d i := Finset.sum_nonneg fun i _ => (hd_pos i).le
  have hpow_lt : ∑ i : Fin s, (d i) ^ 3 < (1 / (h ^ 2 + h - 1)) ^ 3 := by
    calc ∑ i : Fin s, (d i) ^ 3
        ≤ (∑ i : Fin s, d i) ^ 3 := sum_pow_le_pow_sum (fun i => (hd_pos i).le) 3 (by norm_num)
      _ < (1 / (h ^ 2 + h - 1)) ^ 3 := pow_lt_pow_left₀ hsum_lt hsum_nn (by norm_num)
  have hρ3_lt_frac : ρ3 < (1 + h) ^ 2 * (h - 1) / (h ^ 2 + h - 1) ^ 3 := by
    have h1 : ρ3 < ((m : ℝ) - 1) * (1 / (h ^ 2 + h - 1)) ^ 3 :=
      mul_lt_mul_of_pos_left hpow_lt hm1_pos
    have h2 : ((m : ℝ) - 1) * (1 / (h ^ 2 + h - 1)) ^ 3 <
        ((1 + h) ^ 2 * (h - 1)) * (1 / (h ^ 2 + h - 1)) ^ 3 :=
      mul_lt_mul_of_pos_right hm_lt (by positivity)
    have h3 : ((1 + h) ^ 2 * (h - 1)) * (1 / (h ^ 2 + h - 1)) ^ 3 =
        (1 + h) ^ 2 * (h - 1) / (h ^ 2 + h - 1) ^ 3 := by rw [one_div, inv_pow, div_eq_mul_inv]
    linarith
  have hfrac_lt_half : (1 + h) ^ 2 * (h - 1) / (h ^ 2 + h - 1) ^ 3 < 1 / 2 := by
    rw [div_lt_div_iff₀ (pow_pos hden_pos 3) two_pos]
    have hpoly : (h ^ 2 + h - 1) ^ 3 - 2 * ((1 + h) ^ 2 * (h - 1)) =
        t ^ 6 + 9 * t ^ 5 + 30 * t ^ 4 + 43 * t ^ 3 + 22 * t ^ 2 + t + 1 := by dsimp [t]; ring
    have hpos : 0 < t ^ 6 + 9 * t ^ 5 + 30 * t ^ 4 + 43 * t ^ 3 + 22 * t ^ 2 + t + 1 := by positivity
    linarith
  have hρ3_lt_half : ρ3 < 1 / 2 := lt_trans hρ3_lt_frac hfrac_lt_half
  have hσp_pos : 0 < σp := mul_pos (Real.sqrt_pos.mpr (by linarith)) ht
  have htrPhi_eq : trPhi = σp / ((m : ℝ) - 1) * (ρ3 - 1) := by
    dsimp [trPhi, ρ3]; field_simp [hm1_pos.ne']; ring
  have htrD3_lt : trD3 < (m : ℝ) / ((m : ℝ) - 1) := by
    have h1 : ∑ i : Fin s, (d i) ^ 3 < 1 / (2 * ((m : ℝ) - 1)) := by
      dsimp [ρ3] at hρ3_lt_half
      rw [lt_div_iff₀ (by positivity)]; linarith
    have h2 : 1 + 1 / (2 * ((m : ℝ) - 1)) < (m : ℝ) / ((m : ℝ) - 1) := by
      have : (m : ℝ) / ((m : ℝ) - 1) - (1 + 1 / (2 * ((m : ℝ) - 1))) = 1 / (2 * ((m : ℝ) - 1)) := by
        field_simp [hm1_pos.ne']; ring
      have : 0 < 1 / (2 * ((m : ℝ) - 1)) := by positivity
      linarith
    dsimp [trD3]; linarith
  have htrPhi_drift : trPhi < -(σp / (2 * (m : ℝ))) * trD3 := by
    have h1 : trPhi < -(σp / (2 * ((m : ℝ) - 1))) := by
      rw [htrPhi_eq]
      have hlt := mul_lt_mul_of_pos_left (show ρ3 - 1 < -(1 / 2 : ℝ) by linarith) (div_pos hσp_pos hm1_pos)
      have heq : σp / ((m : ℝ) - 1) * (-(1 / 2 : ℝ)) = -(σp / (2 * ((m : ℝ) - 1))) := by
        field_simp [hm1_pos.ne']
      linarith
    have h2 : -(σp / (2 * ((m : ℝ) - 1))) < -(σp / (2 * (m : ℝ))) * trD3 := by
      have h3 : (σp / (2 * (m : ℝ))) * trD3 < (σp / (2 * (m : ℝ))) * ((m : ℝ) / ((m : ℝ) - 1)) :=
        mul_lt_mul_of_pos_left htrD3_lt (by positivity)
      have h4 : (σp / (2 * (m : ℝ))) * ((m : ℝ) / ((m : ℝ) - 1)) = σp / (2 * ((m : ℝ) - 1)) := by
        field_simp [hm_pos.ne', hm1_pos.ne']
      linarith
    linarith
  have htrPhi_neg : trPhi < 0 := by
    have htrD3_pos : 0 < trD3 := by
      dsimp [trD3]
      have : 0 ≤ ∑ i : Fin s, (d i) ^ 3 := Finset.sum_nonneg fun i _ => pow_nonneg (hd_pos i).le 3
      linarith
    have : 0 < (σp / (2 * (m : ℝ))) * trD3 := by positivity
    linarith
  exact ⟨hρ3_lt_frac, hfrac_lt_half, hρ3_lt_half, htrPhi_drift, htrPhi_neg⟩

/-! ==========================================================================
    PART 8: Exact Rational 2-Vector Rank-1 Spectral-Gap Certificates at p = 4/3
    ========================================================================== -/

/-- Real quadratic-form expansion for a real 3-vector linear combination on a Hermitian matrix. -/
private lemma quad_re_lincomb3 {n : ℕ} {A : Mat n} (hA : A.IsHermitian)
    (c0 c1 c2 : ℝ) (v0 v1 v2 : Fin n → ℂ) :
    let x := (c0 : ℂ) • v0 + (c1 : ℂ) • v1 + (c2 : ℂ) • v2
    (star x ⬝ᵥ A.mulVec x).re =
      c0 ^ 2 * (star v0 ⬝ᵥ A.mulVec v0).re +
      c1 ^ 2 * (star v1 ⬝ᵥ A.mulVec v1).re +
      c2 ^ 2 * (star v2 ⬝ᵥ A.mulVec v2).re +
      2 * c0 * c1 * (star v0 ⬝ᵥ A.mulVec v1).re +
      2 * c0 * c2 * (star v0 ⬝ᵥ A.mulVec v2).re +
      2 * c1 * c2 * (star v1 ⬝ᵥ A.mulVec v2).re := by
  intro x
  have hsym : ∀ u w : Fin n → ℂ, (star w ⬝ᵥ A.mulVec u).re = (star u ⬝ᵥ A.mulVec w).re := fun u w => by
    have h1 : star w ⬝ᵥ A.mulVec u = starRingEnd ℂ (star u ⬝ᵥ A.mulVec w) := by
      calc star w ⬝ᵥ A.mulVec u
          = starRingEnd ℂ (star (A.mulVec u) ⬝ᵥ w) := v5_dotProduct_star_comm w (A.mulVec u)
        _ = starRingEnd ℂ ((star u ᵥ* Aᴴ) ⬝ᵥ w) := by rw [← Matrix.star_mulVec]
        _ = starRingEnd ℂ ((star u ᵥ* A) ⬝ᵥ w) := by rw [hA.eq]
        _ = starRingEnd ℂ (star u ⬝ᵥ A.mulVec w) := by rw [Matrix.dotProduct_mulVec]
    rw [h1, Complex.conj_re]
  have hstar_x : star x = (c0 : ℂ) • star v0 + (c1 : ℂ) • star v1 + (c2 : ℂ) • star v2 := by
    dsimp [x]; ext i; simp
  have hAx : A.mulVec x = (c0 : ℂ) • A.mulVec v0 + (c1 : ℂ) • A.mulVec v1 + (c2 : ℂ) • A.mulVec v2 := by
    dsimp [x]; rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
  rw [hstar_x, hAx]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    hsym v0 v1, hsym v0 v2, hsym v1 v2]
  ring

/-- Exact Symbolic 4-Moment Cancellation Identity for the Rank-1 Two-Vector Dual at p = 4/3
    (`#17.2`, `ver_gap_sos_cert.py`):
    For ANY Hermitian D, H with D + H ⪰ 0, R I - D ⪰ 0, unit vector v with D v = v,
    (H D H - D H D) v = μ v, and (D + H)³ v = Λ D H D v, choosing the two explicit vectors
      x = ξ₀ v + ξ₁ H v + H² v,    y = η₀(μ) v + η₁ H v + D H v,
    ALL FOUR unknown moments (a, s₂, t₂, t₃) cancel identically, yielding the universal quadratic bound
      0 ≤ Re ⟨x, (D + H) x⟩ + Re ⟨y, (R I - D) y⟩ = A μ² + B μ + C! -/
theorem two_vector_cancellation_identity_p43 {n : ℕ} {Λ μ R ξ1 : ℝ}
    (hR1 : R ≠ 1) (hξ1 : ξ1 ≠ 1) (hη1 : (R + 3 - Λ) / 2 - ξ1 + 1 ≠ 0)
    {D H : Mat n} (hD : D.IsHermitian) (hH : H.IsHermitian)
    (hDH_psd : (D + H).PosSemidef) (hRD_psd : ((R : ℂ) • (1 : Mat n) - D).PosSemidef)
    {v : Fin n → ℂ} (hv_unit : (star v ⬝ᵥ v).re = 1)
    (hDv : D.mulVec v = v)
    (hPhiv : (H * D * H - D * H * D).mulVec v = (μ : ℂ) • v)
    (hEqv : ((D + H) ^ 3).mulVec v = (Λ : ℂ) • ((D * H * D).mulVec v)) :
    let η1 := (R + 3 - Λ) / 2 - ξ1
    let ξ0 := ξ1 - R * η1 ^ 2 / (2 * (ξ1 - 1))
    let p0 := ξ0 ^ 2 + 2 * ξ0 * ξ1 + 2 * (Λ - 4) * ξ0 + (Λ - 3) * ξ1 ^ 2 + 2 * ξ1 + 6 - η1 ^ 2 + 2 * R * η1
    let p1 := -2 * ξ1 + Λ + 3
    let denom := 2 * (R - 1) * (η1 + 1)
    let e0 := -p0 / denom
    let e1 := -p1 / denom
    let m0 := ξ0 ^ 2 - 2 * ξ0 - ξ1 ^ 2 + 2 * ξ1
    let m1 := -2 * ξ0 + 2 * (Λ - 1) * ξ1 + 4
    let A := (R - 1) * e1 ^ 2
    let B := m1 + 2 * (R - 1) * e0 * e1 - η1 ^ 2 + 2 * R * η1
    let C := m0 + (R - 1) * e0 ^ 2
    0 ≤ A * μ ^ 2 + B * μ + C := by
  intro η1 ξ0 p0 p1 denom e0 e1 m0 m1 A B C
  let η0 : ℝ := e0 + e1 * μ
  -- Basis vectors for M1 ({v, Hv, H²v}) and M2 ({v, Hv, DHv})
  let u1 : Fin n → ℂ := H.mulVec v
  let wH : Fin n → ℂ := H.mulVec u1
  let wD : Fin n → ℂ := D.mulVec u1
  -- Fundamental scalar moments
  set a : ℝ := (star v ⬝ᵥ u1).re
  set s2 : ℝ := (star u1 ⬝ᵥ u1).re
  set t1 : ℝ := (star u1 ⬝ᵥ wD).re
  set t2 : ℝ := (star wD ⬝ᵥ wD).re
  set t3 : ℝ := (star wD ⬝ᵥ D.mulVec wD).re
  set s3 : ℝ := (star u1 ⬝ᵥ wH).re
  set s4 : ℝ := (star wH ⬝ᵥ wH).re
  set q3 : ℝ := (star wH ⬝ᵥ (D + H).mulVec wH).re
  -- Adjoint / star shift helpers
  have hst_D : star v ᵥ* D = star v := by
    rw [← hD.eq, ← Matrix.star_mulVec, hDv]
  have hst_H : star v ᵥ* H = star u1 := by
    rw [← hH.eq, ← Matrix.star_mulVec]
  have hst_Hu1 : star u1 ᵥ* H = star wH := by
    rw [← hH.eq, ← Matrix.star_mulVec]
  have hst_Du1 : star u1 ᵥ* D = star wD := by
    rw [← hD.eq, ← Matrix.star_mulVec]
  -- Core vector identities from hPhiv and hEqv
  have hHDHv : H.mulVec wD = wD + (μ : ℂ) • v := by
    have h1 := hPhiv
    rw [Matrix.sub_mulVec] at h1
    have hL : (H * D * H).mulVec v = H.mulVec wD := by
      dsimp [wD, u1]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hR : (D * H * D).mulVec v = wD := by
      dsimp [wD, u1]; rw [← Matrix.mulVec_mulVec v (D * H) D, hDv, Matrix.mulVec_mulVec]
    rw [hL, hR] at h1
    exact eq_add_of_sub_eq' h1
  have hDH_wH : (D + H).mulVec wH = (Λ : ℂ) • wD - (D + H).mulVec (v + u1 + wD) := by
    have hsq : ((D + H) ^ 2).mulVec v = v + u1 + wD + wH := by
      rw [mat_pow_two, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec v D D, ← Matrix.mulVec_mulVec v D H,
        ← Matrix.mulVec_mulVec v H D, ← Matrix.mulVec_mulVec v H H, hDv, hDv]
      dsimp [u1, wD, wH]; abel
    have h3 : ((D + H) ^ 3).mulVec v = (D + H).mulVec (v + u1 + wD) + (D + H).mulVec wH := by
      have : (D + H) ^ 3 = (D + H) * (D + H) ^ 2 := by rw [mat_pow_three, mat_pow_two, Matrix.mul_assoc]
      rw [this, ← Matrix.mulVec_mulVec, hsq, Matrix.mulVec_add]
    have hR : (D * H * D).mulVec v = wD := by
      dsimp [wD, u1]; rw [← Matrix.mulVec_mulVec v (D * H) D, hDv, Matrix.mulVec_mulVec]
    rw [h3, hR] at hEqv
    exact eq_sub_of_add_eq' hEqv
  -- Exact pairwise inner products
  have hip_v_wD : (star v ⬝ᵥ wD).re = a := by
    dsimp [wD]; rw [Matrix.dotProduct_mulVec, hst_D]
  have hip_v_wH : (star v ⬝ᵥ wH).re = s2 := by
    dsimp [wH]; rw [Matrix.dotProduct_mulVec, hst_H]
  have hip_u1_HwD : (star u1 ⬝ᵥ H.mulVec wD).re = t1 + μ * a := by
    rw [hHDHv, dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h1 : (star u1 ⬝ᵥ v).re = a := by
      rw [v5_dotProduct_star_comm u1 v, Complex.conj_re]
    rw [h1]
  have hip_wH_wD : (star wH ⬝ᵥ wD).re = t1 + μ * a := by
    calc (star wH ⬝ᵥ wD).re = (star u1 ⬝ᵥ H.mulVec wD).re := by rw [← hst_Hu1, ← Matrix.dotProduct_mulVec]
      _ = t1 + μ * a := hip_u1_HwD
  have hip_u1_DwH : (star u1 ⬝ᵥ D.mulVec wH).re = t1 + μ * a := by
    calc (star u1 ⬝ᵥ D.mulVec wH).re = (star wD ⬝ᵥ wH).re := by rw [Matrix.dotProduct_mulVec, hst_Du1]
      _ = (star wH ⬝ᵥ wD).re := by rw [v5_dotProduct_star_comm wD wH, Complex.conj_re]
      _ = t1 + μ * a := hip_wH_wD
  have hip_v_DwH : (star v ⬝ᵥ D.mulVec wH).re = s2 := by
    rw [Matrix.dotProduct_mulVec, hst_D, hip_v_wH]
  have hip_v_HwH : (star v ⬝ᵥ H.mulVec wH).re = s3 := by
    rw [Matrix.dotProduct_mulVec, hst_H]
  have hip_u1_HwH : (star u1 ⬝ᵥ H.mulVec wH).re = s4 := by
    rw [Matrix.dotProduct_mulVec, hst_Hu1]
  have hip_v_DwD : (star v ⬝ᵥ D.mulVec wD).re = a := by
    rw [Matrix.dotProduct_mulVec, hst_D, hip_v_wD]
  have hip_u1_DwD : (star u1 ⬝ᵥ D.mulVec wD).re = t2 := by
    rw [Matrix.dotProduct_mulVec, hst_Du1]
  have hip_wD_HwD : (star wD ⬝ᵥ H.mulVec wD).re = t2 + μ * a := by
    rw [hHDHv, dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have h1 : (star wD ⬝ᵥ v).re = a := by
      rw [v5_dotProduct_star_comm wD v, Complex.conj_re, hip_v_wD]
    rw [h1]
  -- Derive the 4 linear moment relations: t1, s3, s4, q3
  have ht1_eq : t1 = a + μ := by
    have h1 := congrArg (fun z => (star v ⬝ᵥ z).re) hHDHv
    rw [Matrix.dotProduct_mulVec, hst_H, dotProduct_add, dotProduct_smul, smul_eq_mul,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hip_v_wD, hv_unit, mul_one] at h1
    exact h1
  have hs3_eq : s3 = (Λ - 4) * a - 2 * s2 - 1 - μ := by
    have h1 := congrArg (fun z => (star v ⬝ᵥ z).re) hDH_wH
    simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hDv, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hv_unit, hip_v_wD, hip_v_DwH, hip_v_HwH,
      hip_v_DwD] at h1
    have hv_HwD : (star v ⬝ᵥ H.mulVec wD).re = t1 := by rw [Matrix.dotProduct_mulVec, hst_H]
    rw [hv_HwD, ht1_eq] at h1
    change s2 + s3 = _ at h1
    linarith
  have hs4_eq : s4 = Λ * t1 - a - s2 - 3 * t1 - 2 * μ * a - s3 - t2 := by
    have h1 := congrArg (fun z => (star u1 ⬝ᵥ z).re) hDH_wH
    simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hDv, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hip_u1_DwH, hip_u1_HwH, hip_u1_DwD, hip_u1_HwD] at h1
    have hu1_v : (star u1 ⬝ᵥ v).re = a := by rw [v5_dotProduct_star_comm u1 v, Complex.conj_re]
    rw [hu1_v] at h1
    change t1 + μ * a + s4 = Λ * t1 - (a + s2 + (t1 + s3) + (t2 + (t1 + μ * a))) at h1
    linarith
  have hq3_eq : q3 = t3 + Λ * (t1 + μ * a - t2) + a + t1 + 2 * t2 + μ * a - s2 - s3 - s4 := by
    have h4 : (star wD ⬝ᵥ (D + H).mulVec wH).re = Λ * t2 - a - 2 * t1 - 2 * t2 - 2 * μ * a - t3 := by
      have h1 := congrArg (fun z => (star wD ⬝ᵥ z).re) hDH_wH
      have hL : (star wD ⬝ᵥ (D + H).mulVec wH).re = (star wD ⬝ᵥ D.mulVec wH).re + (star wD ⬝ᵥ H.mulVec wH).re := by
        rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
      simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, dotProduct_sub, dotProduct_smul,
        smul_eq_mul, hDv, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hip_wD_HwD] at h1
      have hwD_v : (star wD ⬝ᵥ v).re = a := by rw [v5_dotProduct_star_comm wD v, Complex.conj_re, hip_v_wD]
      have hwD_u1 : (star wD ⬝ᵥ u1).re = t1 := by rw [v5_dotProduct_star_comm wD u1, Complex.conj_re]
      have hwD_wH : (star wD ⬝ᵥ wH).re = t1 + μ * a := by
        rw [v5_dotProduct_star_comm wD wH, Complex.conj_re, hip_wH_wD]
      rw [hwD_v, hwD_u1, hwD_wH] at h1
      change (star wD ⬝ᵥ D.mulVec wH).re + (star wD ⬝ᵥ H.mulVec wH).re =
        Λ * t2 - (a + t1 + (t2 + (t1 + μ * a)) + (t3 + (t2 + μ * a))) at h1
      linarith [hL, h1]
    have h1 := congrArg (fun z => (star wH ⬝ᵥ z).re) hDH_wH
    have hLq3 : q3 = (star wH ⬝ᵥ D.mulVec wH).re + (star wH ⬝ᵥ H.mulVec wH).re := by
      dsimp [q3]; rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    simp only [Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hDv, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hip_wH_wD] at h1
    have hwH_v : (star wH ⬝ᵥ v).re = s2 := by rw [v5_dotProduct_star_comm wH v, Complex.conj_re, hip_v_wH]
    have hwH_u1 : (star wH ⬝ᵥ u1).re = s3 := by rw [v5_dotProduct_star_comm wH u1, Complex.conj_re]
    have hwH_wD_sym : (star wH ⬝ᵥ (D + H).mulVec wD).re = (star wD ⬝ᵥ (D + H).mulVec wH).re := by
      have hdh : (D + H).IsHermitian := hD.add hH
      have hc : star wH ⬝ᵥ (D + H).mulVec wD = starRingEnd ℂ (star wD ⬝ᵥ (D + H).mulVec wH) := by
        calc _ = starRingEnd ℂ (star ((D + H).mulVec wD) ⬝ᵥ wH) := v5_dotProduct_star_comm _ _
          _ = starRingEnd ℂ ((star wD ᵥ* (D + H)ᴴ) ⬝ᵥ wH) := by rw [← Matrix.star_mulVec]
          _ = starRingEnd ℂ ((star wD ᵥ* (D + H)) ⬝ᵥ wH) := by rw [hdh.eq]
          _ = starRingEnd ℂ (star wD ⬝ᵥ (D + H).mulVec wH) := by rw [← Matrix.dotProduct_mulVec]
      rw [hc, Complex.conj_re]
    have hcomb : (star wH ⬝ᵥ D.mulVec wD).re + (star wH ⬝ᵥ H.mulVec wD).re =
        (star wH ⬝ᵥ (D + H).mulVec wD).re := by
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    rw [hwH_v, hwH_u1] at h1
    change (star wH ⬝ᵥ D.mulVec wH).re + (star wH ⬝ᵥ H.mulVec wH).re =
      Λ * (t1 + μ * a) - (s2 + s3 + ((star wH ⬝ᵥ wD).re + s4) +
        ((star wH ⬝ᵥ D.mulVec wD).re + (star wH ⬝ᵥ H.mulVec wD).re)) at h1
    rw [hip_wH_wD] at h1
    linarith [hLq3, h1, hcomb, hwH_wD_sym, h4]
  -- Evaluate ⟨x, (D + H) x⟩ ≥ 0 and ⟨y, (R I - D) y⟩ ≥ 0 via quad_re_lincomb3!
  let x : Fin n → ℂ := (ξ0 : ℂ) • v + (ξ1 : ℂ) • u1 + (1 : ℂ) • wH
  let y : Fin n → ℂ := (η0 : ℂ) • v + (η1 : ℂ) • u1 + (1 : ℂ) • wD
  have hx_nn : 0 ≤ (star x ⬝ᵥ (D + H).mulVec x).re := posSemidef_quad_re_nonneg hDH_psd x
  have hy_nn : 0 ≤ (star y ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec y).re := posSemidef_quad_re_nonneg hRD_psd y
  have hx_val : (star x ⬝ᵥ (D + H).mulVec x).re =
      ξ0 ^ 2 * (1 + a) + ξ1 ^ 2 * (t1 + s3) + q3 +
      2 * ξ0 * ξ1 * (a + s2) + 2 * ξ0 * (s2 + s3) + 2 * ξ1 * (t1 + μ * a + s4) := by
    have hq := quad_re_lincomb3 (hD.add hH) ξ0 ξ1 1 v u1 wH
    change (star x ⬝ᵥ (D + H).mulVec x).re = _ at hq
    rw [hq]
    have e00 : (star v ⬝ᵥ (D + H).mulVec v).re = 1 + a := by
      rw [Matrix.add_mulVec, hDv, dotProduct_add, Complex.add_re, hv_unit]
    have e11 : (star u1 ⬝ᵥ (D + H).mulVec u1).re = t1 + s3 := by
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    have e01 : (star v ⬝ᵥ (D + H).mulVec u1).re = a + s2 := by
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hip_v_wD, hip_v_wH]
    have e02 : (star v ⬝ᵥ (D + H).mulVec wH).re = s2 + s3 := by
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hip_v_DwH, hip_v_HwH]
    have e12 : (star u1 ⬝ᵥ (D + H).mulVec wH).re = t1 + μ * a + s4 := by
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hip_u1_DwH, hip_u1_HwH]
    rw [e00, e11, e01, e02, e12]; ring
  have hy_val : (star y ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec y).re =
      η0 ^ 2 * (R - 1) + η1 ^ 2 * (R * s2 - t1) + (R * t2 - t3) +
      2 * η0 * η1 * ((R - 1) * a) + 2 * η0 * ((R - 1) * a) + 2 * η1 * (R * t1 - t2) := by
    have hRDh : ((R : ℂ) • (1 : Mat n) - D).IsHermitian := hRD_psd.isHermitian
    have hq := quad_re_lincomb3 hRDh η0 η1 1 v u1 wD
    change (star y ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec y).re = _ at hq
    rw [hq]
    have f00 : (star v ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec v).re = R - 1 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hDv, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hv_unit, mul_one]
    have f11 : (star u1 ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec u1).re = R * s2 - t1 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    have f22 : (star wD ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec wD).re = R * t2 - t3 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
    have f01 : (star v ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec u1).re = (R - 1) * a := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hip_v_wD]; ring
    have f02 : (star v ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec wD).re = (R - 1) * a := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hip_v_wD, hip_v_DwD]; ring
    have f12 : (star u1 ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec wD).re = R * t1 - t2 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hip_u1_DwD]
    rw [f00, f11, f22, f01, f02, f12]; ring
  -- EXACT SYMBOLIC CANCELLATION OF ALL FOUR UNKNOWN MOMENTS (a, s2, t2, t3)!
  have hcancel : (star x ⬝ᵥ (D + H).mulVec x).re +
      (star y ⬝ᵥ ((R : ℂ) • (1 : Mat n) - D).mulVec y).re =
      A * μ ^ 2 + B * μ + C := by
    rw [hx_val, hy_val, hq3_eq, hs4_eq, hs3_eq, ht1_eq]
    have hR1' : R - 1 ≠ 0 := sub_ne_zero.mpr hR1
    have hξ1' : ξ1 - 1 ≠ 0 := sub_ne_zero.mpr hξ1
    have hden' : 2 * (R - 1) * (η1 + 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero hR1') hη1
    have h_t2 : R + 3 - Λ - 2 * ξ1 - 2 * η1 = 0 := by dsimp [η1]; ring
    have h_s2 : 2 * (ξ1 - 1) * (ξ0 - ξ1) + R * η1 ^ 2 = 0 := by
      dsimp [ξ0]; field_simp [hξ1']; ring
    have h_a0 : 2 * (R - 1) * (η1 + 1) * e0 + p0 = 0 := by
      change denom * (-p0 / denom) + p0 = 0
      rw [mul_div_cancel₀ (-p0) hden', neg_add_cancel]
    have h_a1 : 2 * (R - 1) * (η1 + 1) * e1 + p1 = 0 := by
      change denom * (-p1 / denom) + p1 = 0
      rw [mul_div_cancel₀ (-p1) hden', neg_add_cancel]
    dsimp [A, B, C, m0, m1, η0]
    dsimp [p0, p1] at h_a0 h_a1
    linear_combination t2 * h_t2 + s2 * h_s2 + a * h_a0 + (a * μ) * h_a1
  linarith

/-- Rescaling bridge for Part 8 certificates: given (D, H) ≻ 0 solving (D+H)³ = Λ D H D with
    D v = dv v, (G² - D G D) v = (μ dv⁴) v, D ⪯ dmax I, if dmax / dv ≤ R0 then the rescaled pair
    satisfies all hypotheses of two_vector_cancellation_identity_p43 at R = R0! -/
private lemma rescale_for_cert_p43 {n : ℕ} {Λ μ dv dmax R0 : ℝ}
    (hdv : 0 < dv) (hR0 : dmax / dv ≤ R0)
    {D H : Mat n} (hD : D.PosDef) (hD_le : ((dmax : ℂ) • (1 : Mat n) - D).PosSemidef)
    (hH : H.PosDef) (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = (dv : ℂ) • v)
    (hPhiv : ((posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) ^ 2 -
      D * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * D).mulVec v =
      ((μ * dv ^ 4 : ℝ) : ℂ) • v) :
    ∃ (D' H' : Mat n) (u : Fin n → ℂ),
      D'.IsHermitian ∧ H'.IsHermitian ∧
      (D' + H').PosSemidef ∧ ((R0 : ℂ) • (1 : Mat n) - D').PosSemidef ∧
      (star u ⬝ᵥ u).re = 1 ∧ D'.mulVec u = u ∧
      (H' * D' * H' - D' * H' * D').mulVec u = (μ : ℂ) • u ∧
      ((D' + H') ^ 3).mulVec u = (Λ : ℂ) • ((D' * H' * D').mulVec u) := by
  have hc_pos : 0 < dv⁻¹ := inv_pos.mpr hdv
  let D' : Mat n := dv⁻¹ • D
  let H' : Mat n := dv⁻¹ • H
  have hD' : D'.PosDef := hD.smul hc_pos
  have hH' : H'.PosDef := hH.smul hc_pos
  have hD'c : D' = ((dv⁻¹ : ℝ) : ℂ) • D := by ext i j; simp [D', Complex.real_smul]
  have hH'c : H' = ((dv⁻¹ : ℝ) : ℂ) • H := by ext i j; simp [H', Complex.real_smul]
  have hv_norm_pos : 0 < (star v ⬝ᵥ v).re := by
    rw [dotProduct, Complex.re_sum]
    obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by by_contra h0; push Not at h0; exact hv (funext h0)
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg _
    · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_pos_of_pos (norm_pos_iff.mpr hi0)
  let nv : ℝ := Real.sqrt (star v ⬝ᵥ v).re
  have hnv : 0 < nv := Real.sqrt_pos.mpr hv_norm_pos
  let u : Fin n → ℂ := ((nv⁻¹ : ℝ) : ℂ) • v
  have hu_norm : (star u ⬝ᵥ u).re = 1 := by
    have hst : star u = ((nv⁻¹ : ℝ) : ℂ) • star v := by ext i; simp [u]
    rw [hst, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hsq : ((nv⁻¹ : ℝ) : ℂ) * (((nv⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ v)) =
        (((nv⁻¹) ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ v) := by push_cast; ring
    rw [hsq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      inv_pow, Real.sq_sqrt hv_norm_pos.le, inv_mul_cancel₀ hv_norm_pos.ne']
  have hD'u : D'.mulVec u = u := by
    rw [hD'c, Matrix.smul_mulVec, Matrix.mulVec_smul, hDv, smul_smul, smul_smul,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have : dv⁻¹ * nv⁻¹ * dv = nv⁻¹ := by field_simp [hdv.ne']
    rw [this]
  have hR0D'_psd : ((R0 : ℂ) • (1 : Mat n) - D').PosSemidef := by
    have hsplit : (R0 : ℂ) • (1 : Mat n) - D' =
        (R0 - dmax / dv) • (1 : Mat n) + dv⁻¹ • ((dmax : ℂ) • (1 : Mat n) - D) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, Complex.real_smul, hD'c]
      split_ifs <;> (push_cast; field_simp [hdv.ne']; ring)
    rw [hsplit]
    exact (Matrix.PosSemidef.one.smul (by linarith)).add (hD_le.smul hc_pos.le)
  have hEq' : (D' + H') ^ 3 = (Λ : ℂ) • (D' * H' * D') := by
    have hsum : D' + H' = ((dv⁻¹ : ℝ) : ℂ) • (D + H) := by rw [hD'c, hH'c, smul_add]
    rw [hsum, mat_pow_three, hD'c, hH'c]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [← mat_pow_three, hEq, smul_smul]
    congr 1; ring
  have hPhiu : (H' * D' * H' - D' * H' * D').mulVec u = (μ : ℂ) • u := by
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    have hDhalf_sq : Dhalf * Dhalf = D := by
      dsimp [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
    have hDhalf_v : Dhalf.mulVec v = ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ) • v :=
      (posDefPow_mulVec_of_eig (1 / 2) hD hv hDv).2
    have hfac_eq : (Dhalf * H * Dhalf) ^ 2 - D * (Dhalf * H * Dhalf) * D =
        Dhalf * (H * D * H - D * H * D) * Dhalf := by
      rw [mat_pow_two, Matrix.mul_sub, Matrix.sub_mul]
      refine congrArg₂ (· - ·) ?_ ?_
      · calc Dhalf * H * Dhalf * (Dhalf * H * Dhalf)
            = Dhalf * H * (Dhalf * Dhalf) * H * Dhalf := by simp only [Matrix.mul_assoc]
          _ = Dhalf * (H * D * H) * Dhalf := by rw [hDhalf_sq]; simp only [Matrix.mul_assoc]
      · have hcomm : D * Dhalf = Dhalf * D := posDefPow_comm_self (1 / 2) hD
        calc D * (Dhalf * H * Dhalf) * D
            = (D * Dhalf) * H * (Dhalf * D) := by simp only [Matrix.mul_assoc]
          _ = (Dhalf * D) * H * (D * Dhalf) := by rw [hcomm]
          _ = Dhalf * (D * H * D) * Dhalf := by simp only [Matrix.mul_assoc]
    rw [hfac_eq, ← Matrix.mulVec_mulVec v (Dhalf * (H * D * H - D * H * D)) Dhalf,
      hDhalf_v, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec v Dhalf] at hPhiv
    have hdh_pos : 0 < dv ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hdv _
    have hdh_sq : dv ^ (1 / 2 : ℝ) * dv ^ (1 / 2 : ℝ) = dv := by rw [← Real.rpow_add hdv]; norm_num
    have h2 : Dhalf.mulVec ((H * D * H - D * H * D).mulVec v - ((μ * dv ^ 3 : ℝ) : ℂ) • v) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hDhalf_v, smul_smul]
      have h3 : ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ) • Dhalf.mulVec ((H * D * H - D * H * D).mulVec v) =
          ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ) • ((((μ * dv ^ 3 : ℝ) : ℂ) * ((dv ^ (1 / 2 : ℝ) : ℝ) : ℂ)) • v) := by
        rw [hPhiv, smul_smul]
        congr 1; rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; congr 1
        calc μ * dv ^ 4 = μ * dv ^ 3 * (dv ^ (1 / 2 : ℝ) * dv ^ (1 / 2 : ℝ)) := by rw [hdh_sq]; ring
          _ = dv ^ (1 / 2 : ℝ) * (μ * dv ^ 3 * dv ^ (1 / 2 : ℝ)) := by ring
      have h4 := smul_right_injective (Fin n → ℂ) (Complex.ofReal_ne_zero.mpr hdh_pos.ne') h3
      rw [h4, sub_self]
    have hHDHv : (H * D * H - D * H * D).mulVec v = ((μ * dv ^ 3 : ℝ) : ℂ) • v := by
      by_contra hne
      exact posDef_mulVec_ne_zero (posDefPow_posDef (1 / 2) hD) (sub_ne_zero.mpr hne) h2
    have hmat_sc : H' * D' * H' - D' * H' * D' = ((dv⁻¹ ^ 3 : ℝ) : ℂ) • (H * D * H - D * H * D) := by
      rw [hD'c, hH'c]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← smul_sub]
      congr 1; push_cast; ring
    dsimp only [u]
    rw [hmat_sc, Matrix.smul_mulVec, Matrix.mulVec_smul, hHDHv, smul_smul, smul_smul, smul_smul,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    refine congrArg (fun c : ℝ => (c : ℂ) • v) ?_
    calc dv⁻¹ ^ 3 * nv⁻¹ * (μ * dv ^ 3) = (dv⁻¹ * dv) ^ 3 * (μ * nv⁻¹) := by ring
      _ = μ * nv⁻¹ := by rw [inv_mul_cancel₀ hdv.ne', one_pow, one_mul]
  refine ⟨D', H', u, hD'.isHermitian, hH'.isHermitian, (hD'.add hH').posSemidef, hR0D'_psd,
    hu_norm, hD'u, hPhiu, by rw [hEq', Matrix.smul_mulVec]⟩

/-- Exact Rational 2-Vector Rank-1 Spectral-Gap Certificate at p = 4/3, μ = 0 (`#17.2`, `ver_gap_sos_cert.py`):
    For EVERY Λ ∈ [8.6042904, 8.6042906] (containing Λ_tree(∞) ≈ 8.604290478), EVERY n ≥ 1,
    EVERY PosDef solution (D, H) of (D + H)³ = Λ D H D with 0 ≺ D ⪯ d_max I, and EVERY
    joint zero-flux eigenvector (D v = d_v v, Φ v = 0):
      d_v < (4 / 17) d_max   (strictly, zero floating-point arithmetic)! -/
theorem spectral_gap_cert_mu0_p43 {n : ℕ} {Λ dv dmax : ℝ}
    (hΛ_lo : (86042904 : ℝ) / 10000000 ≤ Λ) (hΛ_hi : Λ ≤ (86042906 : ℝ) / 10000000)
    (hdv : 0 < dv) {D H : Mat n} (hD : D.PosDef)
    (hD_le : ((dmax : ℂ) • (1 : Mat n) - D).PosSemidef) (hH : H.PosDef)
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = (dv : ℂ) • v)
    (hPhiv : ((posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) ^ 2 -
      D * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * D).mulVec v = 0) :
    dv < (4 / 17 : ℝ) * dmax := by
  by_contra hge; push Not at hge
  have hR0 : dmax / dv ≤ (17 / 4 : ℝ) := by
    rw [div_le_iff₀ hdv]; linarith
  have hPhiv' : ((posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) ^ 2 -
      D * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * D).mulVec v =
      ((0 * dv ^ 4 : ℝ) : ℂ) • v := by simpa using hPhiv
  obtain ⟨D', H', u, hD'h, hH'h, hDH_psd, hRD_psd, hu_unit, hD'u, hPhiu, hEqu⟩ :=
    rescale_for_cert_p43 hdv hR0 hD hD_le hH hEq hv hDv hPhiv'
  set R : ℝ := 17 / 4
  set ξ1 : ℝ := -(2 / 5 : ℝ)
  set η1 : ℝ := (R + 3 - Λ) / 2 - ξ1
  have hη1_lo : -(138573 : ℝ) / 500000 ≤ η1 := by dsimp [η1, R, ξ1]; linarith
  have hη1_hi : η1 ≤ -(55429 : ℝ) / 200000 := by dsimp [η1, R, ξ1]; linarith
  have hη1_ne : (R + 3 - Λ) / 2 - ξ1 + 1 ≠ 0 := by change η1 + 1 ≠ 0; linarith
  have hcert := two_vector_cancellation_identity_p43 (Λ := Λ) (μ := 0) (R := R) (ξ1 := ξ1)
    (by dsimp [R]; norm_num) (by dsimp [ξ1]; norm_num) hη1_ne
    hD'h hH'h hDH_psd hRD_psd hu_unit hD'u hPhiu hEqu
  set ξ0 : ℝ := ξ1 - R * η1 ^ 2 / (2 * (ξ1 - 1))
  set p0 : ℝ := ξ0 ^ 2 + 2 * ξ0 * ξ1 + 2 * (Λ - 4) * ξ0 + (Λ - 3) * ξ1 ^ 2 + 2 * ξ1 + 6 - η1 ^ 2 + 2 * R * η1
  set p1 : ℝ := -2 * ξ1 + Λ + 3
  set denom : ℝ := 2 * (R - 1) * (η1 + 1)
  set e0 : ℝ := -p0 / denom
  set e1 : ℝ := -p1 / denom
  set m0 : ℝ := ξ0 ^ 2 - 2 * ξ0 - ξ1 ^ 2 + 2 * ξ1
  set m1 : ℝ := -2 * ξ0 + 2 * (Λ - 1) * ξ1 + 4
  have hC_nn : 0 ≤ m0 + (R - 1) * e0 ^ 2 := by
    change 0 ≤ (R - 1) * e1 ^ 2 * (0 : ℝ) ^ 2 +
      (m1 + 2 * (R - 1) * e0 * e1 - η1 ^ 2 + 2 * R * η1) * 0 + (m0 + (R - 1) * e0 ^ 2) at hcert
    linarith only [hcert]
  have hη1_sq_lo : (76809 : ℝ) / 1000000 ≤ η1 ^ 2 := by nlinarith only [hη1_lo, hη1_hi]
  have hη1_sq_hi : η1 ^ 2 ≤ (7681 : ℝ) / 100000 := by nlinarith only [hη1_lo, hη1_hi]
  have hξ0_eq : ξ0 = -2 / 5 + 85 / 56 * η1 ^ 2 := by dsimp [ξ0, R, ξ1]; ring
  have hξ0_lo : -(56683 : ℝ) / 200000 ≤ ξ0 := by linarith only [hξ0_eq, hη1_sq_lo]
  have hξ0_hi : ξ0 ≤ -(283413 : ℝ) / 1000000 := by linarith only [hξ0_eq, hη1_sq_hi]
  have hξ0_sq_lo : (40161 : ℝ) / 500000 ≤ ξ0 ^ 2 := by nlinarith only [hξ0_lo, hξ0_hi]
  have hξ0_sq_hi : ξ0 ^ 2 ≤ (3213 : ℝ) / 40000 := by nlinarith only [hξ0_lo, hξ0_hi]
  have hΛξ0_lo : -(652463 : ℝ) / 500000 ≤ (Λ - 4) * ξ0 := by nlinarith only [hΛ_lo, hΛ_hi, hξ0_lo, hξ0_hi]
  have hΛξ0_hi : (Λ - 4) * ξ0 ≤ -(260983 : ℝ) / 200000 := by nlinarith only [hΛ_lo, hΛ_hi, hξ0_lo, hξ0_hi]
  have hp0_lo : (272267 : ℝ) / 200000 ≤ p0 := by
    have hp0_eq : p0 = ξ0 ^ 2 - 4 / 5 * ξ0 + 2 * ((Λ - 4) * ξ0) + 4 / 25 * Λ + 118 / 25 - η1 ^ 2 + 17 / 2 * η1 := by
      dsimp [p0, R, ξ1]; ring
    linarith only [hp0_eq, hξ0_sq_lo, hξ0_hi, hΛξ0_lo, hΛ_lo, hη1_sq_hi, hη1_lo]
  have hp0_hi : p0 ≤ (340343 : ℝ) / 250000 := by
    have hp0_eq : p0 = ξ0 ^ 2 - 4 / 5 * ξ0 + 2 * ((Λ - 4) * ξ0) + 4 / 25 * Λ + 118 / 25 - η1 ^ 2 + 17 / 2 * η1 := by
      dsimp [p0, R, ξ1]; ring
    linarith only [hp0_eq, hξ0_sq_hi, hξ0_lo, hΛξ0_hi, hΛ_hi, hη1_sq_lo, hη1_hi]
  have hden_lo : (4698551 : ℝ) / 1000000 ≤ denom := by dsimp [denom, R]; linarith only [hη1_lo]
  have he0_lo : -(289743 : ℝ) / 1000000 ≤ e0 := by
    dsimp [e0]; rw [le_div_iff₀ (by linarith only [hden_lo])]; nlinarith only [hp0_hi, hden_lo]
  have he0_hi : e0 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [hp0_lo]) (by linarith only [hden_lo])
  have he0_sq_hi : e0 ^ 2 ≤ (5247 : ℝ) / 62500 := by nlinarith only [he0_lo, he0_hi]
  have hm0_hi : m0 ≤ -(62569 : ℝ) / 200000 := by
    have hm0_eq : m0 = ξ0 ^ 2 - 2 * ξ0 - 24 / 25 := by dsimp [m0, ξ1]; ring
    linarith only [hm0_eq, hξ0_sq_hi, hξ0_lo]
  have hC_neg : m0 + (R - 1) * e0 ^ 2 < 0 := by
    have hR_eq : R - 1 = 13 / 4 := by dsimp [R]; norm_num
    rw [hR_eq]; linarith only [hm0_hi, he0_sq_hi]
  linarith only [hC_nn, hC_neg]

/-- Exact Rational 2-Vector Rank-1 Interval Spectral-Gap Certificate at p = 4/3 (`#17.2`, `ver_gap_sos_cert.py`):
    For EVERY Λ ∈ [8.6042904, 8.6042906], EVERY μ ∈ [-49/1000, +1616/10000], EVERY n ≥ 1,
    EVERY PosDef solution (D, H) of (D + H)³ = Λ D H D with 0 ≺ D ⪯ d_max I, and EVERY
    joint eigenvector (D v = d_v v, Φ v = μ d_v⁴ v):
      d_v < (20 / 73) d_max   (strictly, across the entire 2D rectangle [Λ_lo, Λ_hi] × [μ_lo, μ_hi])! -/
theorem spectral_gap_cert_interval_p43 {n : ℕ} {Λ μ dv dmax : ℝ}
    (hΛ_lo : (86042904 : ℝ) / 10000000 ≤ Λ) (hΛ_hi : Λ ≤ (86042906 : ℝ) / 10000000)
    (hμ_lo : -(49 : ℝ) / 1000 ≤ μ) (hμ_hi : μ ≤ (1616 : ℝ) / 10000)
    (hdv : 0 < dv) {D H : Mat n} (hD : D.PosDef)
    (hD_le : ((dmax : ℂ) • (1 : Mat n) - D).PosSemidef) (hH : H.PosDef)
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = (dv : ℂ) • v)
    (hPhiv : ((posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) ^ 2 -
      D * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * D).mulVec v =
      ((μ * dv ^ 4 : ℝ) : ℂ) • v) :
    dv < (20 / 73 : ℝ) * dmax := by
  by_contra hge; push Not at hge
  have hR0 : dmax / dv ≤ (73 / 20 : ℝ) := by
    rw [div_le_iff₀ hdv]; linarith
  obtain ⟨D', H', u, hD'h, hH'h, hDH_psd, hRD_psd, hu_unit, hD'u, hPhiu, hEqu⟩ :=
    rescale_for_cert_p43 hdv hR0 hD hD_le hH hEq hv hDv hPhiv
  set R : ℝ := 73 / 20
  set ξ1 : ℝ := -(131 / 200 : ℝ)
  set η1 : ℝ := (R + 3 - Λ) / 2 - ξ1
  have hη1_lo : -(161073 : ℝ) / 500000 ≤ η1 := by dsimp [η1, R, ξ1]; linarith
  have hη1_hi : η1 ≤ -(64429 : ℝ) / 200000 := by dsimp [η1, R, ξ1]; linarith
  have hη1_ne : (R + 3 - Λ) / 2 - ξ1 + 1 ≠ 0 := by change η1 + 1 ≠ 0; linarith
  have hcert := two_vector_cancellation_identity_p43 (Λ := Λ) (μ := μ) (R := R) (ξ1 := ξ1)
    (by dsimp [R]; norm_num) (by dsimp [ξ1]; norm_num) hη1_ne
    hD'h hH'h hDH_psd hRD_psd hu_unit hD'u hPhiu hEqu
  set ξ0 : ℝ := ξ1 - R * η1 ^ 2 / (2 * (ξ1 - 1))
  set p0 : ℝ := ξ0 ^ 2 + 2 * ξ0 * ξ1 + 2 * (Λ - 4) * ξ0 + (Λ - 3) * ξ1 ^ 2 + 2 * ξ1 + 6 - η1 ^ 2 + 2 * R * η1
  set p1 : ℝ := -2 * ξ1 + Λ + 3
  set denom : ℝ := 2 * (R - 1) * (η1 + 1)
  set e0 : ℝ := -p0 / denom
  set e1 : ℝ := -p1 / denom
  set m0 : ℝ := ξ0 ^ 2 - 2 * ξ0 - ξ1 ^ 2 + 2 * ξ1
  set m1 : ℝ := -2 * ξ0 + 2 * (Λ - 1) * ξ1 + 4
  set A : ℝ := (R - 1) * e1 ^ 2
  set B : ℝ := m1 + 2 * (R - 1) * e0 * e1 - η1 ^ 2 + 2 * R * η1
  set C : ℝ := m0 + (R - 1) * e0 ^ 2
  change 0 ≤ A * μ ^ 2 + B * μ + C at hcert
  have hη1_sq_lo : (103777 : ℝ) / 1000000 ≤ η1 ^ 2 := by nlinarith only [hη1_lo, hη1_hi]
  have hη1_sq_hi : η1 ^ 2 ≤ (103779 : ℝ) / 1000000 := by nlinarith only [hη1_lo, hη1_hi]
  have hξ0_eq : ξ0 = -131 / 200 + 365 / 331 * η1 ^ 2 := by dsimp [ξ0, R, ξ1]; ring
  have hξ0_lo : -(135141 : ℝ) / 250000 ≤ ξ0 := by linarith only [hξ0_eq, hη1_sq_lo]
  have hξ0_hi : ξ0 ≤ -(6757 : ℝ) / 12500 := by linarith only [hξ0_eq, hη1_sq_hi]
  have hξ0_sq_lo : (58441 : ℝ) / 200000 ≤ ξ0 ^ 2 := by nlinarith only [hξ0_lo, hξ0_hi]
  have hξ0_sq_hi : ξ0 ^ 2 ≤ (29221 : ℝ) / 100000 := by nlinarith only [hξ0_lo, hξ0_hi]
  have hΛξ0_lo : -(1244457 : ℝ) / 500000 ≤ (Λ - 4) * ξ0 := by nlinarith only [hΛ_lo, hΛ_hi, hξ0_lo, hξ0_hi]
  have hΛξ0_hi : (Λ - 4) * ξ0 ≤ -(497779 : ℝ) / 200000 := by nlinarith only [hΛ_lo, hΛ_hi, hξ0_lo, hξ0_hi]
  have hp0_eq : p0 = ξ0 ^ 2 - 131 / 100 * ξ0 + 2 * ((Λ - 4) * ξ0) +
      17161 / 40000 * Λ + 136117 / 40000 - η1 ^ 2 + 73 / 10 * η1 := by
    dsimp [p0, R, ξ1]; ring
  have hp0_lo : (330723 : ℝ) / 500000 ≤ p0 := by
    linarith only [hp0_eq, hξ0_sq_lo, hξ0_hi, hΛξ0_lo, hΛ_lo, hη1_sq_hi, hη1_lo]
  have hp0_hi : p0 ≤ (132301 : ℝ) / 200000 := by
    linarith only [hp0_eq, hξ0_sq_hi, hξ0_lo, hΛξ0_hi, hΛ_hi, hη1_sq_lo, hη1_hi]
  have hp1_lo : (1291429 : ℝ) / 100000 ≤ p1 := by dsimp [p1, ξ1]; linarith only [hΛ_lo]
  have hp1_hi : p1 ≤ (12914291 : ℝ) / 1000000 := by dsimp [p1, ξ1]; linarith only [hΛ_hi]
  have hden_lo : (1796313 : ℝ) / 500000 ≤ denom := by dsimp [denom, R]; linarith only [hη1_lo]
  have hden_hi : denom ≤ (449079 : ℝ) / 125000 := by dsimp [denom, R]; linarith only [hη1_hi]
  have he0_lo : -(184129 : ℝ) / 1000000 ≤ e0 := by
    dsimp [e0]; rw [le_div_iff₀ (by linarith only [hden_lo])]; nlinarith only [hp0_hi, hden_lo]
  have he0_hi : e0 ≤ -(184111 : ℝ) / 1000000 := by
    dsimp [e0]; rw [div_le_iff₀ (by linarith only [hden_lo])]; nlinarith only [hp0_lo, hden_hi]
  have he1_lo : -(3594667 : ℝ) / 1000000 ≤ e1 := by
    dsimp [e1]; rw [le_div_iff₀ (by linarith only [hden_lo])]; nlinarith only [hp1_hi, hden_lo]
  have he1_hi : e1 ≤ -(3594659 : ℝ) / 1000000 := by
    dsimp [e1]; rw [div_le_iff₀ (by linarith only [hden_lo])]; nlinarith only [hp1_lo, hden_hi]
  have he0_sq_hi : e0 ^ 2 ≤ (2119 : ℝ) / 62500 := by nlinarith only [he0_lo, he0_hi]
  have he1_sq_lo : (12921573 : ℝ) / 1000000 ≤ e1 ^ 2 := by nlinarith only [he1_lo, he1_hi]
  have he1_sq_hi : e1 ^ 2 ≤ (12921631 : ℝ) / 1000000 := by nlinarith only [he1_lo, he1_hi]
  have hm0_hi : m0 ≤ -(365687 : ℝ) / 1000000 := by
    have hm0_eq : m0 = ξ0 ^ 2 - 2 * ξ0 - 69561 / 40000 := by dsimp [m0, ξ1]; ring
    linarith only [hm0_eq, hξ0_sq_hi, hξ0_lo]
  have hm1_eq : m1 = -2 * ξ0 - 131 / 100 * Λ + 531 / 100 := by dsimp [m1, ξ1]; ring
  have hm1_lo : -(4880501 : ℝ) / 1000000 ≤ m1 := by linarith only [hm1_eq, hξ0_hi, hΛ_hi]
  have hm1_hi : m1 ≤ -(1220123 : ℝ) / 250000 := by linarith only [hm1_eq, hξ0_lo, hΛ_lo]
  have hA_eq : A = 53 / 20 * e1 ^ 2 := by dsimp [A, R]; ring
  have hA_lo : (4280271 : ℝ) / 125000 ≤ A := by linarith only [hA_eq, he1_sq_lo]
  have hA_hi : A ≤ (34242323 : ℝ) / 1000000 := by linarith only [hA_eq, he1_sq_hi]
  have he0e1_lo : (82727 : ℝ) / 125000 ≤ e0 * e1 := by nlinarith only [he0_lo, he0_hi, he1_lo, he1_hi]
  have he0e1_hi : e0 * e1 ≤ (661883 : ℝ) / 1000000 := by nlinarith only [he0_lo, he0_hi, he1_lo, he1_hi]
  have hB_eq : B = m1 + 53 / 10 * (e0 * e1) - η1 ^ 2 + 73 / 10 * η1 := by dsimp [B, R]; ring
  have hB_lo : -(3828321 : ℝ) / 1000000 ≤ B := by linarith only [hB_eq, hm1_lo, he0e1_lo, hη1_sq_hi, hη1_lo]
  have hB_hi : B ≤ -(3827947 : ℝ) / 1000000 := by linarith only [hB_eq, hm1_hi, he0e1_hi, hη1_sq_lo, hη1_hi]
  have hC_hi : C ≤ -(275841 : ℝ) / 1000000 := by
    have hC_eq : C = m0 + 53 / 20 * e0 ^ 2 := by dsimp [C, R]; ring
    linarith only [hC_eq, hm0_hi, he0_sq_hi]
  set μlo : ℝ := -(49 : ℝ) / 1000
  set μhi : ℝ := (1616 : ℝ) / 10000
  have hv_lo : A * μlo ^ 2 + B * μlo + C < 0 := by
    have h1 : 1000000 * (A * μlo ^ 2 + B * μlo + C) = 2401 * A - 49000 * B + 1000000 * C := by
      dsimp [μlo]; ring
    have h2 : 2401 * A - 49000 * B + 1000000 * C < 0 := by linarith only [hA_hi, hB_lo, hC_hi]
    linarith only [h1, h2]
  have hv_hi : A * μhi ^ 2 + B * μhi + C < 0 := by
    have h1 : 1562500 * (A * μhi ^ 2 + B * μhi + C) = 40804 * A + 252500 * B + 1562500 * C := by
      dsimp [μhi]; ring
    have h2 : 40804 * A + 252500 * B + 1562500 * C < 0 := by linarith only [hA_hi, hB_hi, hC_hi]
    linarith only [h1, h2]
  have hconv_id : (μhi - μlo) * (A * μ ^ 2 + B * μ + C) =
      (μhi - μ) * (A * μlo ^ 2 + B * μlo + C) +
      (μ - μlo) * (A * μhi ^ 2 + B * μhi + C) -
      (μhi - μlo) * A * (μ - μlo) * (μhi - μ) := by ring
  have hspan_pos : 0 < μhi - μlo := by dsimp [μlo, μhi]; norm_num
  have hA_pos : 0 < A := by linarith only [hA_lo]
  have hterm1 : (μhi - μ) * (A * μlo ^ 2 + B * μlo + C) +
      (μ - μlo) * (A * μhi ^ 2 + B * μhi + C) < 0 := by
    have ht1 : (μhi - μ) * (A * μlo ^ 2 + B * μlo + C) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith only [hμ_hi]) hv_lo.le
    by_cases hμeq : μ = μlo
    · rw [hμeq, sub_self, zero_mul, add_zero]
      exact mul_neg_of_pos_of_neg hspan_pos hv_lo
    · have hgt : 0 < μ - μlo := lt_of_le_of_ne (by linarith only [hμ_lo]) (Ne.symm (sub_ne_zero.mpr hμeq))
      have hlt2 : (μ - μlo) * (A * μhi ^ 2 + B * μhi + C) < 0 := mul_neg_of_pos_of_neg hgt hv_hi
      linarith only [ht1, hlt2]
  have hterm3 : 0 ≤ (μhi - μlo) * A * (μ - μlo) * (μhi - μ) := by
    have h1 : 0 ≤ μ - μlo := by linarith only [hμ_lo]
    have h2 : 0 ≤ μhi - μ := by linarith only [hμ_hi]
    positivity
  have hquad_neg : A * μ ^ 2 + B * μ + C < 0 := by nlinarith only [hconv_id, hspan_pos, hterm1, hterm3]
  linarith only [hcert, hquad_neg]

/-! ==========================================================================
    PART 9 (BONUS): Exact 5th Universal Quadratic Moment Identity (All κ > 1)
    ========================================================================== -/

private lemma quad_moment_step2 {n : ℕ} {Λ : ℂ} {A P Q G Dhalf : Mat n} {v : Fin n → ℂ}
    (hAh : Aᴴ = A) (h1Gh : (1 + G)ᴴ = 1 + G)
    (hcommA : A * P = P * A) (hcommG : (1 + G) * Q = Q * (1 + G))
    (hP_eq : P = Λ • (Dhalf * Q * Dhalf))
    (hDhalf_Av : Dhalf.mulVec (A.mulVec v) = (1 + G).mulVec v)
    (hst_Dhalf_Av : star (A.mulVec v) ᵥ* Dhalf = star ((1 + G).mulVec v)) :
    star v ⬝ᵥ (P * A ^ 2).mulVec v = Λ * (star v ⬝ᵥ (Q * (1 + G) ^ 2).mulVec v) := by
  have hst_Av : star v ᵥ* A = star (A.mulVec v) := by rw [Matrix.star_mulVec, hAh]
  have s1 : star v ⬝ᵥ (P * A ^ 2).mulVec v = star v ⬝ᵥ (A * P * A).mulVec v := by
    rw [mat_pow_two, ← Matrix.mul_assoc P A A, ← hcommA]
  have s2 : star v ⬝ᵥ (A * P * A).mulVec v = star (A.mulVec v) ⬝ᵥ P.mulVec (A.mulVec v) := by
    rw [← Matrix.mulVec_mulVec v (A * P) A, ← Matrix.mulVec_mulVec (A.mulVec v) A P,
      Matrix.dotProduct_mulVec, hst_Av]
  have s3 : star (A.mulVec v) ⬝ᵥ P.mulVec (A.mulVec v) =
      Λ * (star ((1 + G).mulVec v) ⬝ᵥ Q.mulVec ((1 + G).mulVec v)) := by
    rw [hP_eq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← Matrix.mulVec_mulVec (A.mulVec v) (Dhalf * Q) Dhalf, hDhalf_Av,
      ← Matrix.mulVec_mulVec ((1 + G).mulVec v) Dhalf Q, Matrix.dotProduct_mulVec, hst_Dhalf_Av]
  have s4 : Λ * (star ((1 + G).mulVec v) ⬝ᵥ Q.mulVec ((1 + G).mulVec v)) =
      Λ * (star v ⬝ᵥ ((1 + G) * Q * (1 + G)).mulVec v) := by
    refine congrArg (Λ * ·) ?_
    rw [Matrix.star_mulVec, h1Gh, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec ((1 + G).mulVec v) (1 + G) Q,
      Matrix.mulVec_mulVec v ((1 + G) * Q) (1 + G)]
  have s5 : Λ * (star v ⬝ᵥ ((1 + G) * Q * (1 + G)).mulVec v) =
      Λ * (star v ⬝ᵥ (Q * (1 + G) ^ 2).mulVec v) := by
    rw [hcommG, Matrix.mul_assoc, mat_pow_two]
  exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- 1-Line 5th Universal Quadratic Moment Identity (`#29`, `#34`, `#39`):
    For ALL κ > 1, Λ > 0, PosDef D, H ≻ 0 solving (D + H)^(2κ - 1) = Λ D^(1/2) G^(κ - 1) D^(1/2),
    and ANY eigenvector v ≠ 0 with D v = v:
      (i)  D^(1/2) (D + H) v = (1 + G) v,
      (ii) For EVERY quadratic polynomial q(t) = c₀ + c₁ t + c₂ t² (c₀, c₁, c₂ ∈ ℝ):
             Re ⟨v, (D + H)^(2κ - 1) q(D + H) v⟩ = Λ Re ⟨v, G^(κ - 1) q(1 + G) v⟩! -/
theorem fifth_universal_quadratic_moment_identity {n : ℕ} {κ Λ : ℝ}
    {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = v) (c0 c1 c2 : ℝ) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
    let G := Dhalf * H * Dhalf
    Dhalf.mulVec ((D + H).mulVec v) = (1 + G).mulVec v ∧
    (star v ⬝ᵥ (posDefPow (2 * κ - 1) (hD.add hH) *
        ((c0 : ℂ) • (1 : Mat n) + (c1 : ℂ) • (D + H) + (c2 : ℂ) • (D + H) ^ 2)).mulVec v).re =
      Λ * (star v ⬝ᵥ (posDefPow (κ - 1) hG *
        ((c0 : ℂ) • (1 : Mat n) + (c1 : ℂ) • (1 + G) + (c2 : ℂ) • (1 + G) ^ 2)).mulVec v).re := by
  intro Dhalf hG G
  have hDv1 : D.mulVec v = ((1 : ℝ) : ℂ) • v := by simpa using hDv
  have hDhalf_v : Dhalf.mulVec v = v := by
    have h := (posDefPow_mulVec_of_eig (1 / 2) hD hv hDv1).2
    simpa [Dhalf] using h
  have hDhalf_h : Dhalfᴴ = Dhalf := (posDefPow_posDef (1 / 2) hD).isHermitian.eq
  have hDhalf_DHv : Dhalf.mulVec ((D + H).mulVec v) = (1 + G).mulVec v := by
    rw [Matrix.add_mulVec, hDv, Matrix.mulVec_add, hDhalf_v, Matrix.add_mulVec, Matrix.one_mulVec]
    congr 1
    dsimp [G]
    calc Dhalf.mulVec (H.mulVec v)
        = Dhalf.mulVec (H.mulVec (Dhalf.mulVec v)) := by rw [hDhalf_v]
      _ = (Dhalf * H * Dhalf).mulVec v := by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨hDhalf_DHv, ?_⟩
  let A : Mat n := D + H
  let P : Mat n := posDefPow (2 * κ - 1) (hD.add hH)
  let Q : Mat n := posDefPow (κ - 1) hG
  have hst_Dhalf : star v ᵥ* Dhalf = star v := by
    rw [← hDhalf_h, ← Matrix.star_mulVec, hDhalf_v]
  have hst_Dhalf_Av : star (A.mulVec v) ᵥ* Dhalf = star ((1 + G).mulVec v) := by
    rw [← hDhalf_h, ← Matrix.star_mulVec, hDhalf_DHv]
  have h0 : star v ⬝ᵥ P.mulVec v = (Λ : ℂ) * (star v ⬝ᵥ Q.mulVec v) := by
    dsimp [P, Q]
    rw [hEq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← Matrix.mulVec_mulVec v (Dhalf * posDefPow (κ - 1) hG) Dhalf, hDhalf_v,
      ← Matrix.mulVec_mulVec v Dhalf, Matrix.dotProduct_mulVec, hst_Dhalf]
  have h1 : star v ⬝ᵥ (P * A).mulVec v = (Λ : ℂ) * (star v ⬝ᵥ (Q * (1 + G)).mulVec v) := by
    dsimp [P, Q, A]
    rw [← Matrix.mulVec_mulVec v (posDefPow (2 * κ - 1) (hD.add hH)) (D + H), hEq,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← Matrix.mulVec_mulVec ((D + H).mulVec v) (Dhalf * posDefPow (κ - 1) hG) Dhalf, hDhalf_DHv,
      ← Matrix.mulVec_mulVec ((1 + G).mulVec v) Dhalf, Matrix.dotProduct_mulVec, hst_Dhalf,
      Matrix.mulVec_mulVec]
  have h2 : star v ⬝ᵥ (P * A ^ 2).mulVec v = (Λ : ℂ) * (star v ⬝ᵥ (Q * (1 + G) ^ 2).mulVec v) :=
    quad_moment_step2 (hD.add hH).isHermitian.eq (Matrix.isHermitian_one.add hG.isHermitian).eq
      (posDefPow_comm_self (2 * κ - 1) (hD.add hH))
      (by rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
            posDefPow_comm_self (κ - 1) hG])
      hEq hDhalf_DHv hst_Dhalf_Av
  have htot : star v ⬝ᵥ (P * ((c0 : ℂ) • (1 : Mat n) + (c1 : ℂ) • A + (c2 : ℂ) • A ^ 2)).mulVec v =
      (Λ : ℂ) * (star v ⬝ᵥ (Q * ((c0 : ℂ) • (1 : Mat n) + (c1 : ℂ) • (1 + G) + (c2 : ℂ) • (1 + G) ^ 2)).mulVec v) := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.add_mulVec, Matrix.smul_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, h0, h1, h2]
    ring
  have hre := congrArg Complex.re htot
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hre

/-! ==========================================================================
    AXIOM AUDIT: Confirm ONLY standard axioms [propext, Classical.choice, Quot.sound]
    ========================================================================== -/

#print axioms quantitative_power_variance_lemma
#print axioms universal_spectral_gap_theorem
#print axioms bogomolny_sos_identity_p43
#print axioms vacuum_defect_cubic_identity_p43
#print axioms bogomolny_sos_identity_p32
#print axioms pinching_decomposition_p43
#print axioms pinching_decomposition_p32
#print axioms action_ray_convexity_p43
#print axioms action_ray_convexity_p32
#print axioms negative_trace_drift_2x2_p43
#print axioms sum_trace_negSpectralProj_le
#print axioms master_trace_implies_no_global_solution
#print axioms spectral_pencil_factorization_p43
#print axioms spectral_pencil_factorization_p32
#print axioms spectral_pencil_disjoint_kernels_p43
#print axioms spectral_pencil_rhp_roots_p43
#print axioms lemma0_lambda_sigma_minus_gt_one
#print axioms spectral_pencil_rho4_lt_half
#print axioms spectral_pencil_rho3_lt_half
#print axioms two_vector_cancellation_identity_p43
#print axioms spectral_gap_cert_mu0_p43
#print axioms spectral_gap_cert_interval_p43
#print axioms fifth_universal_quadratic_moment_identity

end MI20
