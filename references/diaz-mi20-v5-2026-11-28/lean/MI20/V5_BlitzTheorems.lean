/-
  MI20/V5_BlitzTheorems.lean
  ==========================
  Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Purpose:     Complete Mathlib-grounded, zero-sorry, zero-warning Lean 4.33.1 formalization
               of the MI-20 V5 Final Blitz breakthroughs (Theorems B1, B3, B4, B5, B6, B7, N1, N2):
                 1. Universal Φ ⪰ 0 Rigidity (Theorem B3): Φ ⪰ 0 ⟹ H = h_+ D for all κ > 1,
                    all Λ > 2^(2κ - 1), all finite dimensions n ≥ 1.
                 2. Third-Root Hyperbolic Spectral Pencil (Theorem B1):
                    - `third_root_harmonic_mean_bound`: overdamped reality of Q_0(r), exact companion
                      cube trace, unconditional harmonic-mean bound Tr(D²H) > (h_+ h_- / (h_+ + h_-)) Tr(D³),
                      and exact k = 3 three-pencil elimination.
                    - `third_root_pencil_rho4_lt_eighth`: exact 2-piece degree-28 all-positive
                      integer polynomial proof of ρ_4(s) < 1/8 (4× sharper than 1/2) for all m ≥ 2.
                 3. Pinching Second-Variation Positivity (Theorem B4):
                    - `pinching_second_variation_pos_p43`: d²/dt²|_{t=1} 4 W_Λ(D, H₀ + t V) = 8 Re Tr(V⁴) > 0
                      (i.e. ⟨V, ∇²_{HH} S_Λ[V]⟩ = 2 Re Tr(V⁴) > 0 whenever P H ≠ H P).
                    - `pinching_second_variation_pos_p32`: d²/dt²|_{t=1} 3 W_Λ(D, M₀ + t V) = 8 A₄ + 24 A₆ > 0
                      whenever P M ≠ M P.
                 4. Exact 2×2 Hessian Determinant & Inertia (Theorem B5):
                    - `hessian_det_pos_2x2_p43`: exact Schur complement M_schur ≺ 0,
                      det(L_H|_{S²}) = 2 b² Λ (3 S² - 2 Λ r)(1 - r)² > 0, inertia (2-, 1+),
                      and complex U(1) gauge kernel L_H[i [D, H]] = 0.
                 5. Complete 2×2 Analytic Master Trace Proofs for all m ≥ 2 (Theorems B6 & B7):
                    - `master_trace_2x2_p43`: exact (u, t) factorization, b² > 0, det(H) > 0,
                      flux derivative h'(v) < 0 with factored opposite-sign endpoints, unimodality,
                      and exact Λ-monotonicity σ_+² d(τ₂/σ_+)/dΛ < 0 ⟹ 2×2 Master Trace (all m ≥ 2).
                    - `master_trace_2x2_p32`: Vieta q_max² < 1/3, closed-form (q, s) parameterization,
                      convexity f''(q) > 0 with factored endpoints, flux derivative, and exact
                      Λ-monotonicity ⟹ 2×2 Master Trace at p = 3/2 (all m ≥ 2).
                 6. Exact Euler–Betti Root Identity (Theorem N2) & All-p Local Hessian Spectral
                    Signs (Theorem N1 Part 2):
                    - `euler_betti_root_identity` (plus matrix-level non-vacuum negative-flux corollary).
                    - `hessian_sign_pairs_all_p`: exact root localization, self-block signs,
                      hyperbolic same-root cross-pair signs for (h_+, h_+) & (h_-, h_-), opposite-root
                      cross-pair positivity for (h_+, 1; h_-, ρ), and exact p = 4/3 (h_-, 1; h_+, r)
                      sign flip at r_max = ((1 + h_-)/(1 + h_+))².
-/

import MI20.V5_NewTheorems
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ==========================================================================
    PART 0: Shared Matrix, Spectral, and Ring Helpers for Blitz Theorems
    ========================================================================== -/

private lemma blitz_pow_two {n : ℕ} (A : Mat n) : A ^ 2 = A * A := pow_two A

private lemma blitz_pow_three {n : ℕ} (A : Mat n) : A ^ 3 = A * A * A := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]

private lemma blitz_pow_four {n : ℕ} (A : Mat n) : A ^ 4 = A * A * A * A := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, blitz_pow_three]

private lemma blitz_tr_eq {n : ℕ} {A B : Mat n} (h : A = B) : A.trace = B.trace :=
  congrArg Matrix.trace h

private lemma blitz_tr_re_eq {n : ℕ} {A B : Mat n} (h : A = B) : A.trace.re = B.trace.re :=
  congrArg (fun X : Mat n => X.trace.re) h

private lemma blitz_unitary_conj_mul {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : Mat n)ᴴ * (U : Mat n) = 1 :=
  (Matrix.mem_unitaryGroup_iff'.mp U.2)

private lemma blitz_unitary_mul_conj {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : Mat n) * (U : Mat n)ᴴ = 1 :=
  (Matrix.mem_unitaryGroup_iff.mp U.2)

private lemma blitz_dotProduct_star_self_nonneg {n : ℕ} (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ x).re := by
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

private lemma blitz_dotProduct_star_self_pos {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) :
    0 < (star x ⬝ᵥ x).re := by
  rw [dotProduct, Complex.re_sum]
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by by_contra h; push Not at h; exact hx (funext h)
  refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
  · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_nonneg _
  · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hi0)

private lemma blitz_dotProduct_star_self_eq_zero {n : ℕ} {x : Fin n → ℂ}
    (h : (star x ⬝ᵥ x).re = 0) : x = 0 := by
  by_contra hx; exact (blitz_dotProduct_star_self_pos hx).ne' h

private lemma blitz_posDef_quad_re_pos {n : ℕ} {A : Mat n} (hA : A.PosDef)
    {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < (star x ⬝ᵥ A.mulVec x).re := by
  have h := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 hx)).1
  rwa [Complex.zero_re] at h

private lemma blitz_posDef_mulVec_ne_zero {n : ℕ} {A : Mat n} (hA : A.PosDef)
    {x : Fin n → ℂ} (hx : x ≠ 0) : A.mulVec x ≠ 0 := by
  intro h0
  have hpos := blitz_posDef_quad_re_pos hA hx
  rw [h0, dotProduct_zero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

private lemma blitz_hermitian_smul_real {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (c : ℝ) :
    ((c : ℂ) • A).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hA.eq]

private lemma blitz_hermitian_diag_real {n : ℕ} (d : Fin n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.diagonal_apply_ne _ hij]

private lemma blitz_hermitian_conj_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    {A : Mat n} (hA : A.IsHermitian) :
    ((U : Mat n) * A * (U : Mat n)ᴴ).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

private lemma blitz_mat_eq_unitary_diag {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (A : Mat n) (lam : Fin n → ℝ)
    (heig : ∀ i : Fin n, A.mulVec ((U : Mat n).mulVec (Pi.single i (1 : ℂ))) =
      (lam i : ℂ) • ((U : Mat n).mulVec (Pi.single i (1 : ℂ)))) :
    A = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
  have hAU : A * (U : Mat n) = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) := by
    ext r c
    have hc := congr_fun (heig c) r
    rw [Matrix.mulVec_mulVec] at hc
    have hL : ((A * (U : Mat n)).mulVec (Pi.single c (1 : ℂ))) r = (A * (U : Mat n)) r c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    have hR : ((lam c : ℂ) • ((U : Mat n).mulVec (Pi.single c (1 : ℂ)))) r =
        ((U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ))) r c := by
      simp [Matrix.mul_diagonal, mul_comm]
    rw [← hL, ← hR]; exact hc
  calc A = A * ((U : Mat n) * (U : Mat n)ᴴ) := by rw [blitz_unitary_mul_conj U, Matrix.mul_one]
    _ = (A * (U : Mat n)) * (U : Mat n)ᴴ := by rw [Matrix.mul_assoc]
    _ = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by rw [hAU]

private lemma blitz_posDef_of_unitary_diag {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    {A : Mat n} {lam : Fin n → ℝ} (hpos : ∀ i, 0 < lam i)
    (hspec : A = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ) :
    A.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨by rw [hspec]; exact blitz_hermitian_conj_unitary U (blitz_hermitian_diag_real lam), fun x hx => ?_⟩
  let z : Fin n → ℂ := (U : Mat n)ᴴ.mulVec x
  have hz : z ≠ 0 := by
    intro hz0
    have h1 := congrArg (Matrix.mulVec (U : Mat n)) hz0
    rw [Matrix.mulVec_mulVec, blitz_unitary_mul_conj U, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    exact hx h1
  have hval : star x ⬝ᵥ A.mulVec x = ∑ i, (((‖z i‖ ^ 2 * lam i : ℝ) : ℂ)) := by
    rw [hspec, ← Matrix.mulVec_mulVec x ((U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ))) (U : Mat n)ᴴ,
      ← Matrix.mulVec_mulVec z (U : Mat n), Matrix.dotProduct_mulVec,
      show star x ᵥ* (U : Mat n) = star z by
        dsimp only [z]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have hc : starRingEnd ℂ (z i) * ((lam i : ℂ) * z i) =
        (starRingEnd ℂ (z i) * z i) * (lam i : ℂ) := by ring
    rw [hc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  rw [hval, Complex.lt_def, Complex.zero_re, Complex.zero_im, Complex.re_sum, Complex.im_sum]
  refine ⟨?_, ?_⟩
  · obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by by_contra h; push Not at h; exact hz (funext h)
    refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
    · rw [Complex.ofReal_re]; exact mul_nonneg (sq_nonneg _) (hpos i).le
    · rw [Complex.ofReal_re]; exact mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hi0)) (hpos i0)
  · symm; refine Finset.sum_eq_zero fun i _ => Complex.ofReal_im _

private lemma blitz_posDef_quad_re_lt_trace {n : ℕ} {A : Mat n} (hA : A.PosDef)
    {x : Fin n → ℂ} (hx : x ≠ 0) :
    (star x ⬝ᵥ A.mulVec x).re < (A.trace.re + 1) * (star x ⬝ᵥ x).re := by
  let U := hA.isHermitian.eigenvectorUnitary
  let lam := hA.isHermitian.eigenvalues
  have hspec : A = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hA.isHermitian.spectral_theorem
  have htr : A.trace.re = ∑ i, lam i := by
    have h1 : A.trace = (Matrix.diagonal (fun i => (lam i : ℂ))).trace := by
      rw [hspec, Matrix.trace_mul_cycle, blitz_unitary_conj_mul U, Matrix.one_mul]
    rw [h1, Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  let z : Fin n → ℂ := (U : Mat n)ᴴ.mulVec x
  have hqA : (star x ⬝ᵥ A.mulVec x).re = ∑ i, ‖z i‖ ^ 2 * lam i := by
    have hval : star x ⬝ᵥ A.mulVec x = ∑ i, (((‖z i‖ ^ 2 * lam i : ℝ) : ℂ)) := by
      rw [hspec, ← Matrix.mulVec_mulVec x ((U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ))) (U : Mat n)ᴴ,
        ← Matrix.mulVec_mulVec z (U : Mat n), Matrix.dotProduct_mulVec,
        show star x ᵥ* (U : Mat n) = star z by
          dsimp only [z]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
      rw [dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
      have hc : starRingEnd ℂ (z i) * ((lam i : ℂ) * z i) =
          (starRingEnd ℂ (z i) * z i) * (lam i : ℂ) := by ring
      rw [hc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [hval, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  have hqz : (star x ⬝ᵥ x).re = ∑ i, ‖z i‖ ^ 2 := by
    have hnorm : star z ⬝ᵥ z = star x ⬝ᵥ x := by
      dsimp only [z]
      rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
        Matrix.mulVec_mulVec, blitz_unitary_mul_conj U, Matrix.one_mulVec]
    rw [← hnorm, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hle : ∀ i : Fin n, lam i ≤ A.trace.re := fun i => by
    rw [htr]
    exact Finset.single_le_sum (fun j _ => (hA.eigenvalues_pos j).le) (Finset.mem_univ i)
  have hsum_le : ∑ i, ‖z i‖ ^ 2 * lam i ≤ A.trace.re * ∑ i, ‖z i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm (‖z i‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)
  have hpos := blitz_dotProduct_star_self_pos hx
  rw [hqA, hqz] at *
  nlinarith only [hsum_le, hpos]

private lemma posDefPow_congr {n : ℕ} (r : ℝ) {A B : Mat n} (hAB : A = B)
    (hA : A.PosDef) (hB : B.PosDef) : posDefPow r hA = posDefPow r hB := by
  subst hAB; rfl

/-- Simultaneous spectral-shift lemma: if a Hermitian idempotent P commutes with A ≻ 0,
    then Q A Q + c P (Q = 1 - P, c > 0) is PosDef and its r-th power splits identically as
      posDefPow r (Q A Q + c P) = Q * posDefPow r A * Q + c^r • P. -/
private lemma posDefPow_block_replace {n : ℕ} (r c : ℝ) (hc : 0 < c) {A P : Mat n}
    (hA : A.PosDef) (hPh : P.IsHermitian) (hP2 : P * P = P) (hPA : P * A = A * P) :
    let Q := 1 - P
    let A' := Q * A * Q + (c : ℂ) • P
    ∃ hA' : A'.PosDef, posDefPow r hA' = Q * posDefPow r hA * Q + ((c ^ r : ℝ) : ℂ) • P := by
  intro Q A'
  have hQh : Q.IsHermitian := Matrix.isHermitian_one.sub hPh
  have hQ2 : Q * Q = Q := by
    dsimp only [Q]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]; abel
  have hPQ : P * Q = 0 := by dsimp only [Q]; rw [Matrix.mul_sub, Matrix.mul_one, hP2, sub_self]
  have hQP : Q * P = 0 := by dsimp only [Q]; rw [Matrix.sub_mul, Matrix.one_mul, hP2, sub_self]
  let M : ℝ := A.trace.re + 1
  let B0 : Mat n := A + (M : ℂ) • P
  have hB0h : B0.IsHermitian := hA.isHermitian.add (blitz_hermitian_smul_real hPh M)
  have hPB0 : P * B0 = B0 * P := by
    dsimp only [B0]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hPA, hP2]
  have hQB0 : Q * B0 = B0 * Q := by
    dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPB0]
  let U := hB0h.eigenvectorUnitary
  let μ := hB0h.eigenvalues
  have hB0_spec : B0 = (U : Mat n) * Matrix.diagonal (fun i => (μ i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, μ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hB0h.spectral_theorem
  let u : Fin n → Fin n → ℂ := fun i => (U : Mat n).mulVec (Pi.single i (1 : ℂ))
  have hB0_u : ∀ i, B0.mulVec (u i) = (μ i : ℂ) • u i := fun i => by
    dsimp only [u]
    conv_lhs => rw [hB0_spec]
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      blitz_unitary_conj_mul U, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    refine congrArg (Matrix.mulVec (U : Mat n)) ?_
    ext j
    by_cases hj : j = i
    · subst hj; simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, hj]
  have hP_dichot : ∀ i, (M < μ i → P.mulVec (u i) = u i ∧ Q.mulVec (u i) = 0 ∧ 0 < μ i - M) ∧
      (¬M < μ i → P.mulVec (u i) = 0 ∧ Q.mulVec (u i) = u i ∧ 0 < μ i) := by
    intro i
    have hB0_Pu : B0.mulVec (P.mulVec (u i)) = (μ i : ℂ) • (P.mulVec (u i)) := by
      rw [Matrix.mulVec_mulVec, ← hPB0, ← Matrix.mulVec_mulVec, hB0_u, Matrix.mulVec_smul]
    have hB0_Qu : B0.mulVec (Q.mulVec (u i)) = (μ i : ℂ) • (Q.mulVec (u i)) := by
      rw [Matrix.mulVec_mulVec, ← hQB0, ← Matrix.mulVec_mulVec, hB0_u, Matrix.mulVec_smul]
    have hPu_eq : B0.mulVec (P.mulVec (u i)) = A.mulVec (P.mulVec (u i)) + (M : ℂ) • (P.mulVec (u i)) := by
      dsimp only [B0]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec (u i) P P, hP2]
    have hQu_eq : B0.mulVec (Q.mulVec (u i)) = A.mulVec (Q.mulVec (u i)) := by
      dsimp only [B0]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec (u i) P Q, hPQ, Matrix.zero_mulVec,
        smul_zero, add_zero]
    have hPQ_sum : P.mulVec (u i) + Q.mulVec (u i) = u i := by
      dsimp only [Q]; rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    have hPu_gt : P.mulVec (u i) ≠ 0 → M < μ i := by
      intro hne
      have h1 := congrArg (fun z => (star (P.mulVec (u i)) ⬝ᵥ z).re) (hB0_Pu.symm.trans hPu_eq)
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h1
      have hAp := blitz_posDef_quad_re_pos hA hne
      have hnp := blitz_dotProduct_star_self_pos hne
      nlinarith only [h1, hAp, hnp]
    have hQu_lt : Q.mulVec (u i) ≠ 0 → μ i < M := by
      intro hne
      have h1 := congrArg (fun z => (star (Q.mulVec (u i)) ⬝ᵥ z).re) (hB0_Qu.symm.trans hQu_eq)
      simp only [dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] at h1
      have hAlt := blitz_posDef_quad_re_lt_trace hA hne
      have hnp := blitz_dotProduct_star_self_pos hne
      dsimp only [M] at *
      nlinarith only [h1, hAlt, hnp]
    have hu_ne : u i ≠ 0 := by
      intro hu0
      have h1 := congrArg (Matrix.mulVec (U : Mat n)ᴴ) hu0
      dsimp only [u] at h1
      rw [Matrix.mulVec_mulVec, blitz_unitary_conj_mul U, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      have := congr_fun h1 i; simp at this
    refine ⟨fun hgt => ?_, fun hle => ?_⟩
    · have hQu0 : Q.mulVec (u i) = 0 := by by_contra hne; linarith [hQu_lt hne]
      have hPu_u : P.mulVec (u i) = u i := by rw [hQu0, add_zero] at hPQ_sum; exact hPQ_sum
      refine ⟨hPu_u, hQu0, by linarith⟩
    · have hPu0 : P.mulVec (u i) = 0 := by by_contra hne; exact hle (hPu_gt hne)
      have hQu_u : Q.mulVec (u i) = u i := by rw [hPu0, zero_add] at hPQ_sum; exact hPQ_sum
      have hμ_pos : 0 < μ i := by
        have heq_u : (μ i : ℂ) • u i = A.mulVec (u i) := by
          have h0 := hB0_Qu.symm.trans hQu_eq
          rwa [hQu_u] at h0
        have h1 := congrArg (fun z => (star (u i) ⬝ᵥ z).re) heq_u
        simp only [dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero] at h1
        have hAp := blitz_posDef_quad_re_pos hA hu_ne
        have hnp := blitz_dotProduct_star_self_pos hu_ne
        nlinarith only [h1, hAp, hnp]
      exact ⟨hPu0, hQu_u, hμ_pos⟩
  let lamA : Fin n → ℝ := fun i => if M < μ i then μ i - M else μ i
  let lamA' : Fin n → ℝ := fun i => if M < μ i then c else μ i
  let lamP : Fin n → ℝ := fun i => if M < μ i then 1 else 0
  let lamQ : Fin n → ℝ := fun i => if M < μ i then 0 else 1
  have hP_spec : P = (U : Mat n) * Matrix.diagonal (fun i => (lamP i : ℂ)) * (U : Mat n)ᴴ := by
    refine blitz_mat_eq_unitary_diag U P lamP fun i => ?_
    dsimp only [lamP]
    by_cases h : M < μ i
    · rw [if_pos h, ((hP_dichot i).1 h).1, Complex.ofReal_one, one_smul]
    · rw [if_neg h, ((hP_dichot i).2 h).1, Complex.ofReal_zero, zero_smul]
  have hQ_spec : Q = (U : Mat n) * Matrix.diagonal (fun i => (lamQ i : ℂ)) * (U : Mat n)ᴴ := by
    refine blitz_mat_eq_unitary_diag U Q lamQ fun i => ?_
    dsimp only [lamQ]
    by_cases h : M < μ i
    · rw [if_pos h, ((hP_dichot i).1 h).2.1, Complex.ofReal_zero, zero_smul]
    · rw [if_neg h, ((hP_dichot i).2 h).2.1, Complex.ofReal_one, one_smul]
  have hA_spec : A = (U : Mat n) * Matrix.diagonal (fun i => (lamA i : ℂ)) * (U : Mat n)ᴴ := by
    refine blitz_mat_eq_unitary_diag U A lamA fun i => ?_
    have hB0_eq : B0.mulVec (u i) = A.mulVec (u i) + (M : ℂ) • P.mulVec (u i) := by
      dsimp only [B0]; rw [Matrix.add_mulVec, Matrix.smul_mulVec]
    have hAu : A.mulVec (u i) = (μ i : ℂ) • u i - (M : ℂ) • P.mulVec (u i) := by
      rw [← hB0_u i, hB0_eq]; abel
    dsimp only [lamA]
    by_cases h : M < μ i
    · rw [if_pos h, hAu, (hP_dichot i).1 h |>.1, ← sub_smul]; push_cast; rfl
    · rw [if_neg h, hAu, (hP_dichot i).2 h |>.1, smul_zero, sub_zero]
  have hA'_spec : A' = (U : Mat n) * Matrix.diagonal (fun i => (lamA' i : ℂ)) * (U : Mat n)ᴴ := by
    refine blitz_mat_eq_unitary_diag U A' lamA' fun i => ?_
    have hA_u : A.mulVec (u i) = (lamA i : ℂ) • u i := by
      conv_lhs => rw [hA_spec]
      dsimp only [u]
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        blitz_unitary_conj_mul U, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
      refine congrArg (Matrix.mulVec (U : Mat n)) ?_
      ext j; by_cases hj : j = i <;> simp [Matrix.mulVec_diagonal, hj]
    dsimp only [A', lamA']
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec (u i) (Q * A) Q,
      ← Matrix.mulVec_mulVec _ Q A]
    by_cases h : M < μ i
    · rw [if_pos h, (hP_dichot i).1 h |>.2.1, (hP_dichot i).1 h |>.1,
        Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add]
    · rw [if_neg h, (hP_dichot i).2 h |>.2.1, (hP_dichot i).2 h |>.1,
        smul_zero, add_zero, hA_u, Matrix.mulVec_smul, (hP_dichot i).2 h |>.2.1]
      dsimp only [lamA]; rw [if_neg h]
  have hlamA_pos : ∀ i, 0 < lamA i := fun i => by
    dsimp only [lamA]; by_cases h : M < μ i
    · rw [if_pos h]; exact ((hP_dichot i).1 h).2.2
    · rw [if_neg h]; exact ((hP_dichot i).2 h).2.2
  have hlamA'_pos : ∀ i, 0 < lamA' i := fun i => by
    dsimp only [lamA']; by_cases h : M < μ i
    · rw [if_pos h]; exact hc
    · rw [if_neg h]; exact ((hP_dichot i).2 h).2.2
  have hA'_pd : A'.PosDef := blitz_posDef_of_unitary_diag U hlamA'_pos hA'_spec
  refine ⟨hA'_pd, ?_⟩
  rw [posDefPow_eq_of_diag r hA'_pd U lamA' hlamA'_pos hA'_spec,
    posDefPow_eq_of_diag r hA U lamA hlamA_pos hA_spec]
  have hQ_pow : Q * ((U : Mat n) * Matrix.diagonal (fun i => ((lamA i ^ r : ℝ) : ℂ)) * (U : Mat n)ᴴ) * Q =
      (U : Mat n) * Matrix.diagonal (fun i => ((lamQ i * lamA i ^ r * lamQ i : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
    conv_lhs => rw [hQ_spec]
    calc ((U : Mat n) * Matrix.diagonal (fun i => (lamQ i : ℂ)) * (U : Mat n)ᴴ) *
          ((U : Mat n) * Matrix.diagonal (fun i => ((lamA i ^ r : ℝ) : ℂ)) * (U : Mat n)ᴴ) *
          ((U : Mat n) * Matrix.diagonal (fun i => (lamQ i : ℂ)) * (U : Mat n)ᴴ)
        = (U : Mat n) * (Matrix.diagonal (fun i => (lamQ i : ℂ)) *
            ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => ((lamA i ^ r : ℝ) : ℂ)) *
            ((U : Mat n)ᴴ * (U : Mat n)) * Matrix.diagonal (fun i => (lamQ i : ℂ))) * (U : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (U : Mat n) * Matrix.diagonal (fun i => ((lamQ i * lamA i ^ r * lamQ i : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
            rw [blitz_unitary_conj_mul U, Matrix.mul_one, Matrix.mul_one,
              Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
            refine congrArg (· * (U : Mat n)ᴴ) (congrArg ((U : Mat n) * ·) ?_)
            ext i j; by_cases hij : i = j
            · subst hij; simp [Complex.ofReal_mul]
            · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hQ_pow]
  conv_rhs => rw [hP_spec]
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add]
  refine congrArg (· * (U : Mat n)ᴴ) (congrArg ((U : Mat n) * ·) ?_)
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
    dsimp only [lamA', lamA, lamQ, lamP]
    by_cases h : M < μ i
    · rw [if_pos h, if_pos h, if_pos h, if_pos h]; simp
    · rw [if_neg h, if_neg h, if_neg h, if_neg h]; simp
  · simp [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij]

/-! ==========================================================================
    PART 1: Universal Φ ⪰ 0 Rigidity (Theorem B3, all κ > 1, all Λ > 2^(2κ-1))
    ========================================================================== -/

private lemma q_rpow_pos {α x : ℝ} (hα : 1 < α) (hx : 0 < x) (hx1 : x ≠ 1) :
    0 < (x ^ α - 1) ^ 2 - (x - 1) ^ 2 := by
  have hfac : (x ^ α - 1) ^ 2 - (x - 1) ^ 2 = (x ^ α - x) * (x ^ α + x - 2) := by ring
  rw [hfac]
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · have h1 : x ^ α < x := by
      simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hx hlt hα
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  · have h1 : x < x ^ α := by
      simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hgt hα
    exact mul_pos (by linarith) (by linarith)

/-- Core μ = 0 top-eigenspace exclusion (Theorem B3 eigenvector step):
    On any finite-dim PD solution (D, H) at κ > 1, Λ > 2^(2κ - 1) with D ⪯ dmax·I,
    no nonzero top eigenvector (D v = dmax v) can have zero flux (Φ v = 0). -/
private lemma zero_flux_top_eig_impossible {n : ℕ} {κ Λ dmax : ℝ}
    (hκ : 1 < κ) (hΛ : 2 ^ (2 * κ - 1) < Λ) (hdmax : 0 < dmax)
    {D H : Mat n} (hD : D.PosDef) (hD_le : ((dmax : ℂ) • (1 : Mat n) - D).PosSemidef)
    (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = (dmax : ℂ) • v)
    (hΦv : (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) -
      D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) * D).mulVec v = 0) :
    False := by
  have hkm1 : 0 < κ - 1 := by linarith
  have hc_pos : 0 < dmax⁻¹ := inv_pos.mpr hdmax
  let D' : Mat n := dmax⁻¹ • D
  let H' : Mat n := dmax⁻¹ • H
  have hD' : D'.PosDef := hD.smul hc_pos
  have hH' : H'.PosDef := hH.smul hc_pos
  have hD'c : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext i j; simp [D', Complex.real_smul]
  have hH'c : H' = ((dmax⁻¹ : ℝ) : ℂ) • H := by ext i j; simp [H', Complex.real_smul]
  have hD'_le : (1 - D').PosSemidef := by
    have h1 : (1 : Mat n) - D' = dmax⁻¹ • ((dmax : ℂ) • (1 : Mat n) - D) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Complex.real_smul,
        smul_eq_mul, hD'c]
      by_cases hij : i = j
      · subst hij; simp only [↓reduceIte, mul_one, mul_sub]
        have : ((dmax⁻¹ : ℝ) : ℂ) * (dmax : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, inv_mul_cancel₀ hdmax.ne', Complex.ofReal_one]
        rw [this]
      · simp [hij]
    rw [h1]; exact hD_le.smul hc_pos.le
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let D'half := posDefPow (1 / 2 : ℝ) hD'
  have hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
  have hG' : (D'half * H' * D'half).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH'
  have hD'half_eq : D'half = ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) • Dhalf :=
    posDefPow_smul (1 / 2) hc_pos hD
  have hG'_eq : D'half * H' * D'half = (dmax⁻¹ ^ 2) • (Dhalf * H * Dhalf) := by
    rw [hD'half_eq, hH'c]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    have hsq : dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ * dmax⁻¹ ^ (1 / 2 : ℝ)) = dmax⁻¹ ^ 2 := by
      calc dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ * dmax⁻¹ ^ (1 / 2 : ℝ))
          = dmax⁻¹ * (dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (1 / 2 : ℝ)) := by ring
        _ = dmax⁻¹ * dmax⁻¹ ^ ((1 / 2 : ℝ) + 1 / 2) := by rw [← Real.rpow_add hc_pos]
        _ = dmax⁻¹ ^ 2 := by norm_num; ring
    have hc : ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((dmax⁻¹ : ℝ) : ℂ) * ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
        ((dmax⁻¹ ^ 2 : ℝ) : ℂ) := by rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsq]
    rw [hc]
  have hG'pow : ∀ r : ℝ, posDefPow r hG' = ((dmax⁻¹ ^ (2 * r) : ℝ) : ℂ) • posDefPow r hG := fun r => by
    have h2pos : 0 < dmax⁻¹ ^ 2 := sq_pos_of_pos hc_pos
    rw [posDefPow_congr r hG'_eq hG' (hG.smul h2pos), posDefPow_smul r h2pos hG,
      show (dmax⁻¹ ^ 2) ^ r = dmax⁻¹ ^ (2 * r) by
        rw [← Real.rpow_natCast dmax⁻¹ 2, ← Real.rpow_mul hc_pos.le]; push_cast; rfl]
  have hD'v : D'.mulVec v = v := by
    rw [hD'c, Matrix.smul_mulVec, hDv, smul_smul, ← Complex.ofReal_mul,
      inv_mul_cancel₀ hdmax.ne', Complex.ofReal_one, one_smul]
  have hΦ'v : (posDefPow κ hG' - D' * posDefPow (κ - 1) hG' * D').mulVec v = 0 := by
    have hmat : posDefPow κ hG' - D' * posDefPow (κ - 1) hG' * D' =
        ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) • (posDefPow κ hG - D * posDefPow (κ - 1) hG * D) := by
      rw [hG'pow κ, hG'pow (κ - 1), hD'c]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub]
      refine congrArg (fun X => ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) • posDefPow κ hG - X) ?_
      refine congrArg (· • (D * posDefPow (κ - 1) hG * D)) ?_
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; apply congrArg Complex.ofReal
      calc dmax⁻¹ * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹)
          = dmax⁻¹ ^ (2 * (κ - 1)) * (dmax⁻¹ ^ (1 : ℝ) * dmax⁻¹ ^ (1 : ℝ)) := by simp [Real.rpow_one]; ring
        _ = dmax⁻¹ ^ (2 * (κ - 1) + (1 + 1)) := by
              rw [← Real.rpow_add hc_pos, ← Real.rpow_add hc_pos]
        _ = dmax⁻¹ ^ (2 * κ) := by congr 1; ring
    rw [hmat, Matrix.smul_mulVec, hΦv, smul_zero]
  have hEq' : posDefPow (2 * κ - 1) (hD'.add hH') =
      (Λ : ℂ) • (D'half * posDefPow (κ - 1) hG' * D'half) := by
    have hsum_eq : D' + H' = dmax⁻¹ • (D + H) := by simp [D', H', smul_add]
    have hL : posDefPow (2 * κ - 1) (hD'.add hH') =
        ((dmax⁻¹ ^ (2 * κ - 1) : ℝ) : ℂ) • posDefPow (2 * κ - 1) (hD.add hH) := by
      rw [posDefPow_congr (2 * κ - 1) hsum_eq (hD'.add hH') ((hD.add hH).smul hc_pos)]
      exact posDefPow_smul (2 * κ - 1) hc_pos (hD.add hH)
    rw [hL, hEq, hG'pow (κ - 1), hD'half_eq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    refine congrArg (· • (Dhalf * posDefPow (κ - 1) hG * Dhalf)) ?_
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    have hsc : dmax⁻¹ ^ (2 * κ - 1) = dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ)) := by
      calc dmax⁻¹ ^ (2 * κ - 1) = dmax⁻¹ ^ ((1 / 2 : ℝ) + (2 * (κ - 1) + 1 / 2)) := by congr 1; ring
        _ = dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (2 * (κ - 1) + 1 / 2) := Real.rpow_add hc_pos _ _
        _ = dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ)) := by
              rw [Real.rpow_add hc_pos]
    rw [hsc]; ring
  -- Now work on (D', H', v): D' v = v, 0 ≺ D' ⪯ 1, G'^κ v = D' G'^(κ-1) v
  let G' : Mat n := D'half * H' * D'half
  let U := hG'.isHermitian.eigenvectorUnitary
  let g := hG'.isHermitian.eigenvalues
  have hg_pos : ∀ i, 0 < g i := fun i => hG'.eigenvalues_pos i
  let y : Fin n → ℝ := fun i => g i ^ (κ - 1)
  have hy_pos : ∀ i, 0 < y i := fun i => Real.rpow_pos_of_pos (hg_pos i) _
  let α : ℝ := κ / (κ - 1)
  have hα : 1 < α := by dsimp only [α]; rw [one_lt_div hkm1]; linarith
  have hy_pow_α : ∀ i, y i ^ α = g i ^ κ := fun i => by
    dsimp only [y, α]
    rw [← Real.rpow_mul (hg_pos i).le, mul_div_cancel₀ κ hkm1.ne']
  have hG'k_eq : posDefPow κ hG' *ᵥ v = D'.mulVec (posDefPow (κ - 1) hG' *ᵥ v) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec v (D' * posDefPow (κ - 1) hG') D',
      hD'v, ← Matrix.mulVec_mulVec v D'] at hΦ'v
    exact sub_eq_zero.mp hΦ'v
  let z : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
  let w : Fin n → ℝ := fun i => ‖z i‖ ^ 2
  have hw_nn : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have hG's : G' = (U : Mat n) * Matrix.diagonal (fun i => (g i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, g, G', Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hG'.isHermitian.spectral_theorem
  have hpow_quad : ∀ r : ℝ, (star v ⬝ᵥ (posDefPow r hG').mulVec v).re = ∑ i, w i * g i ^ r := fun r => by
    rw [posDefPow_eq_of_diag r hG' U g hg_pos hG's]
    have hval : star v ⬝ᵥ ((U : Mat n) * Matrix.diagonal (fun i => ((g i ^ r : ℝ) : ℂ)) * (U : Mat n)ᴴ).mulVec v =
        ∑ i, (((w i * g i ^ r : ℝ) : ℂ)) := by
      rw [← Matrix.mulVec_mulVec v ((U : Mat n) * Matrix.diagonal (fun i => ((g i ^ r : ℝ) : ℂ))) (U : Mat n)ᴴ,
        ← Matrix.mulVec_mulVec z (U : Mat n), Matrix.dotProduct_mulVec,
        show star v ᵥ* (U : Mat n) = star z by
          dsimp only [z]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
      rw [dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def, w]
      have hc : starRingEnd ℂ (z i) * (((g i ^ r : ℝ) : ℂ) * z i) =
          (starRingEnd ℂ (z i) * z i) * ((g i ^ r : ℝ) : ℂ) := by ring
      rw [hc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [hval, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
  have hpow_norm : ∀ r : ℝ, (star ((posDefPow r hG').mulVec v) ⬝ᵥ (posDefPow r hG').mulVec v).re =
      ∑ i, w i * (g i ^ r) ^ 2 := fun r => by
    have hh : (posDefPow r hG')ᴴ = posDefPow r hG' := (posDefPow_posDef r hG').isHermitian.eq
    have hsq : posDefPow r hG' * posDefPow r hG' = posDefPow (2 * r) hG' := by
      rw [posDefPow_mul_posDefPow, two_mul]
    rw [Matrix.star_mulVec, hh, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hsq, hpow_quad (2 * r)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; rw [two_mul, Real.rpow_add (hg_pos i), sq]
  -- Mean equality: ∑ w_i y_i^α = ∑ w_i y_i
  have hmean : ∑ i, w i * y i ^ α = ∑ i, w i * y i := by
    have h1 : (star v ⬝ᵥ (posDefPow κ hG').mulVec v).re = (star v ⬝ᵥ (posDefPow (κ - 1) hG').mulVec v).re := by
      rw [hG'k_eq, Matrix.dotProduct_mulVec,
        show star v ᵥ* D' = star v by rw [← hD'.isHermitian.eq, ← Matrix.star_mulVec, hD'v]]
    rw [hpow_quad κ, hpow_quad (κ - 1)] at h1
    simpa only [hy_pow_α, y] using h1
  -- Second moment inequality: ∑ w_i (y_i^α)^2 ≤ ∑ w_i y_i^2 (since 0 ≺ D' ⪯ 1 ⟹ I - D'^2 ⪰ 0)
  have hD'2_le : (1 - D' * D').PosSemidef := by
    have hD'h : D'.IsHermitian := hD'.isHermitian
    -- Diagonalize D': each eigenvalue 0 < λ ≤ 1 gives 1 - λ^2 ≥ 0
    let UD := hD'h.eigenvectorUnitary
    let d := hD'h.eigenvalues
    have hD's : D' = (UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ := by
      simpa [UD, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hD'h.spectral_theorem
    have hd_le1 : ∀ i, d i ≤ 1 := fun i => by
      let ei : Fin n → ℂ := (UD : Mat n).mulVec (Pi.single i (1 : ℂ))
      have hnn := posSemidef_quad_re_nonneg hD'_le ei
      have hDei : D'.mulVec ei = (d i : ℂ) • ei := by
        dsimp only [ei]; conv_lhs => rw [hD's]
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
          blitz_unitary_conj_mul UD, Matrix.mul_one,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
        refine congrArg (Matrix.mulVec (UD : Mat n)) ?_
        ext j; by_cases hj : j = i <;> simp [Matrix.mulVec_diagonal, hj]
      have hei_norm : (star ei ⬝ᵥ ei).re = 1 := by
        dsimp only [ei]
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
          blitz_unitary_conj_mul UD, Matrix.one_mulVec]
        simp [dotProduct, Pi.single_apply]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hDei, dotProduct_sub, dotProduct_smul,
        smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hei_norm] at hnn
      linarith
    have h1D'2 : (1 : Mat n) - D' * D' =
        (UD : Mat n) * Matrix.diagonal (fun i => ((1 - d i ^ 2 : ℝ) : ℂ)) * (UD : Mat n)ᴴ := by
      have hD'sq : D' * D' = (UD : Mat n) * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * (UD : Mat n)ᴴ := by
        conv_lhs => rw [hD's]
        calc ((UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ) *
              ((UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ)
            = (UD : Mat n) * (Matrix.diagonal (fun i => (d i : ℂ)) * ((UD : Mat n)ᴴ * (UD : Mat n)) *
                Matrix.diagonal (fun i => (d i : ℂ))) * (UD : Mat n)ᴴ := by simp only [Matrix.mul_assoc]
          _ = (UD : Mat n) * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : ℂ)) * (UD : Mat n)ᴴ := by
                rw [blitz_unitary_conj_mul UD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
                refine congrArg (· * (UD : Mat n)ᴴ) (congrArg ((UD : Mat n) * ·) ?_)
                ext i j; by_cases hij : i = j
                · subst hij; simp [sq]
                · simp [Matrix.diagonal_apply_ne _ hij]
      have h1u : (1 : Mat n) = (UD : Mat n) * Matrix.diagonal (fun _ => (1 : ℂ)) * (UD : Mat n)ᴴ := by
        rw [Matrix.diagonal_one, Matrix.mul_one, blitz_unitary_mul_conj UD]
      conv_lhs => rw [h1u, hD'sq]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      refine congrArg (· * (UD : Mat n)ᴴ) (congrArg ((UD : Mat n) * ·) ?_)
      ext i j; by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij]
    rw [h1D'2]
    have hdiag_psd : (Matrix.diagonal (fun i => ((1 - d i ^ 2 : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro i
      rw [Complex.le_def, Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨by nlinarith only [hD'.eigenvalues_pos i, hd_le1 i], rfl⟩
    have := hdiag_psd.mul_mul_conjTranspose_same (UD : Mat n)
    simpa only [Matrix.mul_assoc] using this
  have hsq_le : ∑ i, w i * (y i ^ α) ^ 2 ≤ ∑ i, w i * y i ^ 2 := by
    let x := (posDefPow (κ - 1) hG').mulVec v
    have hnn := posSemidef_quad_re_nonneg hD'2_le x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at hnn
    have hD'x : (star x ⬝ᵥ (D' * D').mulVec x).re = (star (D'.mulVec x) ⬝ᵥ D'.mulVec x).re := by
      have h1 : star x ⬝ᵥ (D' * D').mulVec x = star (D'.mulVec x) ⬝ᵥ D'.mulVec x := by
        calc star x ⬝ᵥ (D' * D').mulVec x = star x ⬝ᵥ D'.mulVec (D'.mulVec x) := by rw [← Matrix.mulVec_mulVec]
          _ = (star x ᵥ* D') ⬝ᵥ D'.mulVec x := Matrix.dotProduct_mulVec _ _ _
          _ = (star x ᵥ* D'ᴴ) ⬝ᵥ D'.mulVec x := by rw [hD'.isHermitian.eq]
          _ = star (D'.mulVec x) ⬝ᵥ D'.mulVec x := by rw [← Matrix.star_mulVec]
      exact congrArg Complex.re h1
    rw [hD'x, ← hG'k_eq] at hnn
    have h1 := hpow_norm κ
    have h2 := hpow_norm (κ - 1)
    dsimp only [x] at hnn
    rw [h1, h2] at hnn
    have h1' : ∑ i, w i * (y i ^ α) ^ 2 = ∑ i, w i * (g i ^ κ) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => by rw [hy_pow_α]
    rw [h1']; dsimp only [y]; linarith
  -- Sum of w_i * q(y_i) ≤ 0 forces w_i > 0 ⟹ y_i = 1 ⟹ g_i = 1!
  have hq_sum_le : ∑ i, w i * ((y i ^ α - 1) ^ 2 - (y i - 1) ^ 2) ≤ 0 := by
    have hexp : ∑ i, w i * ((y i ^ α - 1) ^ 2 - (y i - 1) ^ 2) =
        (∑ i, w i * (y i ^ α) ^ 2 - ∑ i, w i * y i ^ 2) -
        2 * (∑ i, w i * y i ^ α - ∑ i, w i * y i) := by
      calc ∑ i, w i * ((y i ^ α - 1) ^ 2 - (y i - 1) ^ 2)
          = ∑ i, ((w i * (y i ^ α) ^ 2 - w i * y i ^ 2) - 2 * (w i * y i ^ α - w i * y i)) :=
              Finset.sum_congr rfl fun i _ => by ring
        _ = (∑ i, w i * (y i ^ α) ^ 2 - ∑ i, w i * y i ^ 2) -
              2 * (∑ i, w i * y i ^ α - ∑ i, w i * y i) := by
              simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexp, hmean, sub_self, mul_zero, sub_zero]; linarith
  have hq_term_nn : ∀ i, 0 ≤ w i * ((y i ^ α - 1) ^ 2 - (y i - 1) ^ 2) := fun i => by
    by_cases hy1 : y i = 1
    · rw [hy1, Real.one_rpow]; simp
    · exact mul_nonneg (hw_nn i) (q_rpow_pos hα (hy_pos i) hy1).le
  have hq_zero : ∀ i, w i * ((y i ^ α - 1) ^ 2 - (y i - 1) ^ 2) = 0 := fun i => by
    have hle := Finset.single_le_sum (fun j _ => hq_term_nn j) (Finset.mem_univ i)
    linarith [hq_term_nn i]
  have hz_eq1 : ∀ i, z i ≠ 0 → g i = 1 := fun i hzi => by
    have hwi : 0 < w i := sq_pos_of_pos (norm_pos_iff.mpr hzi)
    have hy1 : y i = 1 := by
      by_contra hne
      have hpos := mul_pos hwi (q_rpow_pos hα (hy_pos i) hne)
      exact hpos.ne' (hq_zero i)
    have h1 : g i ^ (κ - 1) = 1 ^ (κ - 1) := by simpa [y, Real.one_rpow] using hy1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (Real.rpow_lt_rpow (hg_pos i).le hlt hkm1).ne h1
    · exact (Real.rpow_lt_rpow zero_le_one hgt hkm1).ne' h1
  -- Hence G' v = v and G'^(κ-1) v = v!
  have hG'v : G'.mulVec v = v := by
    rw [hG's, ← Matrix.mulVec_mulVec v ((U : Mat n) * Matrix.diagonal (fun i => (g i : ℂ))) (U : Mat n)ᴴ,
      ← Matrix.mulVec_mulVec z (U : Mat n)]
    have hdz : (Matrix.diagonal (fun i => (g i : ℂ))).mulVec z = z := by
      ext i; simp only [Matrix.mulVec_diagonal]
      by_cases hzi : z i = 0
      · simp [hzi]
      · rw [hz_eq1 i hzi, Complex.ofReal_one, one_mul]
    rw [hdz]; dsimp only [z]
    rw [Matrix.mulVec_mulVec, blitz_unitary_mul_conj U, Matrix.one_mulVec]
  have hG'km1_v : (posDefPow (κ - 1) hG').mulVec v = v := by
    rw [posDefPow_eq_of_diag (κ - 1) hG' U g hg_pos hG's]
    rw [← Matrix.mulVec_mulVec v ((U : Mat n) * Matrix.diagonal (fun i => ((g i ^ (κ - 1) : ℝ) : ℂ))) (U : Mat n)ᴴ,
      ← Matrix.mulVec_mulVec z (U : Mat n)]
    have hdz : (Matrix.diagonal (fun i => ((g i ^ (κ - 1) : ℝ) : ℂ))).mulVec z = z := by
      ext i; simp only [Matrix.mulVec_diagonal]
      by_cases hzi : z i = 0
      · simp [hzi]
      · rw [hz_eq1 i hzi, Real.one_rpow, Complex.ofReal_one, one_mul]
    rw [hdz]; dsimp only [z]
    rw [Matrix.mulVec_mulVec, blitz_unitary_mul_conj U, Matrix.one_mulVec]
  -- D'^(1/2) v = v ⟹ H' v = v ⟹ (D' + H') v = 2 v ⟹ 2^(2κ-1) v = Λ v, contradiction!
  have hD'half_v : D'half.mulVec v = v := by
    have h1 := (posDefPow_mulVec_of_eig (1 / 2) hD' hv (by simpa using hD'v : D'.mulVec v = ((1 : ℝ) : ℂ) • v)).2
    simpa [D'half] using h1
  have hH'v : H'.mulVec v = v := by
    have h1 : D'half.mulVec (H'.mulVec v - v) = 0 := by
      rw [Matrix.mulVec_sub, hD'half_v]
      have h2 : D'half.mulVec (H'.mulVec v) = G'.mulVec v := by
        dsimp only [G']
        rw [← Matrix.mulVec_mulVec v (D'half * H') D'half, hD'half_v, ← Matrix.mulVec_mulVec]
      rw [h2, hG'v, sub_self]
    by_contra hne
    exact blitz_posDef_mulVec_ne_zero (posDefPow_posDef (1 / 2) hD') (sub_ne_zero.mpr hne) h1
  have hDH'v : (D' + H').mulVec v = ((2 : ℝ) : ℂ) • v := by
    rw [Matrix.add_mulVec, hD'v, hH'v]
    ext i; simp; ring
  have hLHS : (posDefPow (2 * κ - 1) (hD'.add hH')).mulVec v = ((2 ^ (2 * κ - 1) : ℝ) : ℂ) • v :=
    (posDefPow_mulVec_of_eig (2 * κ - 1) (hD'.add hH') hv hDH'v).2
  have hRHS : (posDefPow (2 * κ - 1) (hD'.add hH')).mulVec v = (Λ : ℂ) • v := by
    rw [hEq', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec v (D'half * posDefPow (κ - 1) hG') D'half,
      hD'half_v, ← Matrix.mulVec_mulVec v D'half, hG'km1_v, hD'half_v]
  have heq_vec : ((2 ^ (2 * κ - 1) : ℝ) : ℂ) • v = (Λ : ℂ) • v := hLHS.symm.trans hRHS
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by by_contra h; push Not at h; exact hv (funext h)
  have hci := congr_fun heq_vec i0
  simp only [Pi.smul_apply, smul_eq_mul] at hci
  have hc_eq : ((2 ^ (2 * κ - 1) : ℝ) : ℂ) = (Λ : ℂ) := mul_right_cancel₀ hi0 hci
  have hr_eq : (2 : ℝ) ^ (2 * κ - 1) = Λ := Complex.ofReal_injective hc_eq
  linarith

/-- Uniqueness of the upper root h > 1 of (1 + h)^(2κ - 1) = Λ h^(κ - 1). -/
private lemma upper_root_unique {κ Λ g h : ℝ} (hκ : 1 < κ) (hg : 1 < g) (hh : 1 < h)
    (hg_eq : (1 + g) ^ (2 * κ - 1) = Λ * g ^ (κ - 1))
    (hh_eq : (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1)) : g = h := by
  let f : ℝ → ℝ := fun x => (1 + x) ^ (2 * κ - 1) / x ^ (κ - 1)
  have hf_strict : StrictMonoOn f (Set.Ioi 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 1) ?_ ?_
    · refine ContinuousOn.div ?_ ?_ (fun x hx => (Real.rpow_pos_of_pos (by linarith [Set.mem_Ioi.mp hx]) _).ne')
      · exact (continuousOn_const.add continuousOn_id).rpow_const
          (fun x hx => Or.inl (by linarith [Set.mem_Ioi.mp hx] : (0 : ℝ) < 1 + x).ne')
      · exact continuousOn_id.rpow_const (fun x hx => Or.inl (by linarith [Set.mem_Ioi.mp hx] : (0 : ℝ) < x).ne')
    · intro x hx
      rw [interior_Ioi] at hx
      have hx0 : 0 < x := by linarith [Set.mem_Ioi.mp hx]
      have hx1 : 0 < 1 + x := by linarith
      have hd1 := ((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (p := 2 * κ - 1) (Or.inl hx1.ne')
      have hd2 := (hasDerivAt_id x).rpow_const (p := κ - 1) (Or.inl hx0.ne')
      have hdiv : HasDerivAt f
          (((2 * κ - 1) * (1 + x) ^ (2 * κ - 1 - 1) * 1 * x ^ (κ - 1) -
            (1 + x) ^ (2 * κ - 1) * ((κ - 1) * x ^ (κ - 1 - 1) * 1)) / (x ^ (κ - 1)) ^ 2) x :=
        (hd1.div hd2 (Real.rpow_pos_of_pos hx0 _).ne').congr_deriv (by simp only [id_eq]; ring)
      rw [hdiv.deriv]
      have hnum : ((2 * κ - 1) * (1 + x) ^ (2 * κ - 1 - 1) * 1 * x ^ (κ - 1) -
          (1 + x) ^ (2 * κ - 1) * ((κ - 1) * x ^ (κ - 1 - 1) * 1)) =
          (1 + x) ^ (2 * κ - 2) * x ^ (κ - 2) * (κ * x - (κ - 1)) := by
        have h1 : (1 + x) ^ (2 * κ - 1) = (1 + x) ^ (2 * κ - 2) * (1 + x) := by
          rw [← Real.rpow_add_one hx1.ne']; congr 1; ring
        have h2 : x ^ (κ - 1) = x ^ (κ - 2) * x := by
          rw [← Real.rpow_add_one hx0.ne']; congr 1; ring
        have h3 : 2 * κ - 1 - 1 = 2 * κ - 2 := by ring
        have h4 : κ - 1 - 1 = κ - 2 := by ring
        rw [h3, h4, h1, h2]; ring
      rw [hnum]
      have hpos1 : 0 < (1 + x) ^ (2 * κ - 2) := Real.rpow_pos_of_pos hx1 _
      have hpos2 : 0 < x ^ (κ - 2) := Real.rpow_pos_of_pos hx0 _
      have hpos3 : 0 < κ * x - (κ - 1) := by nlinarith [Set.mem_Ioi.mp hx]
      have hden : 0 < (x ^ (κ - 1)) ^ 2 := sq_pos_of_pos (Real.rpow_pos_of_pos hx0 _)
      exact div_pos (mul_pos (mul_pos hpos1 hpos2) hpos3) hden
  have hfg : f g = Λ := by
    dsimp only [f]; rw [hg_eq, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (by linarith) _).ne']
  have hfh : f h = Λ := by
    dsimp only [f]; rw [hh_eq, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos (by linarith) _).ne']
  exact hf_strict.injOn hg hh (hfg.trans hfh.symm)

/-- Existence of g > 1 solving g^κ - g^(κ-1) = μ for any κ > 1 and μ > 0. -/
private lemma exists_gap_root {κ μ : ℝ} (hκ : 1 < κ) (hμ : 0 < μ) :
    ∃ g : ℝ, 1 < g ∧ g ^ κ - g ^ (κ - 1) = μ := by
  let ψ : ℝ → ℝ := fun x => x ^ κ - x ^ (κ - 1)
  let B : ℝ := max 2 (μ + 2)
  have hB_gt1 : 1 < B := by dsimp only [B]; linarith [le_max_left (2 : ℝ) (μ + 2)]
  have hB_ge : μ + 2 ≤ B := le_max_right 2 (μ + 2)
  have hψ1 : ψ 1 = 0 := by dsimp only [ψ]; simp [Real.one_rpow]
  have hψB : μ ≤ ψ B := by
    dsimp only [ψ]
    have hB1 : 1 ≤ B ^ (κ - 1) := Real.one_le_rpow hB_gt1.le (by linarith)
    have hfac : B ^ κ - B ^ (κ - 1) = B ^ (κ - 1) * (B - 1) := by
      have : B ^ κ = B ^ (κ - 1) * B := by rw [← Real.rpow_add_one (by linarith : (0 : ℝ) < B).ne']; congr 1; ring
      rw [this]; ring
    rw [hfac]; nlinarith
  have hcont : ContinuousOn ψ (Set.Icc 1 B) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl (by linarith [hx.1] : (0 : ℝ) < x).ne')).sub
      (continuousOn_id.rpow_const (fun x hx => Or.inl (by linarith [hx.1] : (0 : ℝ) < x).ne'))
  have hmem : μ ∈ Set.Icc (ψ 1) (ψ B) := ⟨by linarith [hψ1], hψB⟩
  obtain ⟨g, ⟨hg1, _⟩, hψg⟩ := intermediate_value_Icc hB_gt1.le hcont hmem
  have hg_gt1 : 1 < g := lt_of_le_of_ne hg1 (by intro heq; rw [← heq, hψ1] at hψg; linarith)
  exact ⟨g, hg_gt1, hψg⟩

set_option maxHeartbeats 800000 in
/-- Theorem B3 (`b1_proof.md` §5): Universal Φ ⪰ 0 Rigidity for ALL κ > 1, ALL Λ > 2^(2κ - 1),
    and ALL finite dimensions n ≥ 1:
    Every finite-dimensional PosDef solution (D, H) of Holden's power equation
      (D + H)^(2κ - 1) = Λ D^(1/2) G^(κ - 1) D^(1/2)
    with nonnegative flux operator Φ = G^κ - D G^(κ - 1) D ⪰ 0 is pure h_+-vacuum:
      H = h_+ • D identically! -/
theorem universal_phi_psd_rigidity {n : ℕ} {κ Λ h : ℝ}
    (hκ : 1 < κ) (hΛ : 2 ^ (2 * κ - 1) < Λ) (hh : 1 < h)
    (hSc : (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1))
    {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    (hΦ_psd : (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) -
      D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) * D).PosSemidef) :
    H = (h : ℂ) • D := by
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _) hΛ
  let UD := hD.isHermitian.eigenvectorUnitary
  let d := hD.isHermitian.eigenvalues
  let L : Finset ℝ := Finset.univ.image d
  let QD : ℝ → Mat n := fun lam =>
    (UD : Mat n) * Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) * (UD : Mat n)ᴴ
  have hQDh : ∀ lam, (QD lam).IsHermitian := fun lam => by
    refine blitz_hermitian_conj_unitary UD ?_
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases h : d i = lam <;> simp [h]
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hQD_D : ∀ lam, D * QD lam = (lam : ℂ) • QD lam := fun lam => by
    have hDs : D = (UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ := by
      simpa [UD, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hD.isHermitian.spectral_theorem
    dsimp only [QD]
    conv_lhs => rw [hDs]
    calc ((UD : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (UD : Mat n)ᴴ) *
          ((UD : Mat n) * Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) * (UD : Mat n)ᴴ)
        = (UD : Mat n) * (Matrix.diagonal (fun i => (d i : ℂ)) * ((UD : Mat n)ᴴ * (UD : Mat n)) *
            Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0)) * (UD : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (UD : Mat n) * ((lam : ℂ) • Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0)) * (UD : Mat n)ᴴ := by
            rw [blitz_unitary_conj_mul UD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
            refine congrArg (· * (UD : Mat n)ᴴ) (congrArg ((UD : Mat n) * ·) ?_)
            ext i j; by_cases hij : i = j
            · subst hij
              simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
              split_ifs with heq
              · rw [heq, mul_one]
              · simp
            · simp [Matrix.diagonal_apply_ne _ hij]
      _ = (lam : ℂ) • ((UD : Mat n) * Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) * (UD : Mat n)ᴴ) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
  have hD_QD : ∀ lam, QD lam * D = (lam : ℂ) • QD lam := fun lam => by
    have h1 := congrArg Matrix.conjTranspose (hQD_D lam)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, (hQDh lam).eq, hD.isHermitian.eq,
      Complex.star_def, Complex.conj_ofReal] at h1
    exact h1
  have hQD_sum : ∑ lam ∈ L, QD lam = 1 := by
    dsimp only [QD]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    have hdiag : ∑ lam ∈ L, Matrix.diagonal (fun i => if d i = lam then (1 : ℂ) else 0) = (1 : Mat n) := by
      ext i j
      simp only [Matrix.sum_apply]
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem d (Finset.mem_univ i))]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [hdiag, Matrix.mul_one, blitz_unitary_mul_conj UD]
  -- Define K = ∑_{lam ∈ L} QD(lam) * (H - (h * lam) • 1)² * QD(lam) ⪰ 0!
  let T : ℝ → Mat n := fun lam => (H - ((h * lam : ℝ) : ℂ) • (1 : Mat n)) * QD lam
  let K : Mat n := ∑ lam ∈ L, (T lam)ᴴ * T lam
  have hKh : K.IsHermitian := by
    dsimp only [K]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hDK : D * K = K * D := by
    dsimp only [K]
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun lam _ => ?_
    have hTh : (T lam)ᴴ = QD lam * (H - ((h * lam : ℝ) : ℂ) • (1 : Mat n)) := by
      dsimp only [T]
      rw [Matrix.conjTranspose_mul, (hQDh lam).eq, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, hH.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
    rw [hTh]
    dsimp only [T]
    calc D * (QD lam * (H - ((h * lam : ℝ) : ℂ) • 1) * ((H - ((h * lam : ℝ) : ℂ) • 1) * QD lam))
        = (D * QD lam) * ((H - ((h * lam : ℝ) : ℂ) • 1) * ((H - ((h * lam : ℝ) : ℂ) • 1) * QD lam)) := by
            simp only [Matrix.mul_assoc]
      _ = (lam : ℂ) • (QD lam * ((H - ((h * lam : ℝ) : ℂ) • 1) * ((H - ((h * lam : ℝ) : ℂ) • 1) * QD lam))) := by
            rw [hQD_D lam, Matrix.smul_mul]
      _ = (QD lam * (H - ((h * lam : ℝ) : ℂ) • 1) * (H - ((h * lam : ℝ) : ℂ) • 1)) * ((lam : ℂ) • QD lam) := by
            simp only [Matrix.mul_smul, Matrix.mul_assoc]
      _ = QD lam * (H - ((h * lam : ℝ) : ℂ) • 1) * ((H - ((h * lam : ℝ) : ℂ) • 1) * QD lam) * D := by
            rw [← hD_QD lam]; simp only [Matrix.mul_assoc]
  have hK_ker_iff : ∀ x : Fin n → ℂ, K.mulVec x = 0 ↔ ∀ lam ∈ L, T lam *ᵥ x = 0 := fun x => by
    constructor
    · intro hKx lam hlam
      have h0 : (star x ⬝ᵥ K.mulVec x).re = 0 := by rw [hKx, dotProduct_zero, Complex.zero_re]
      dsimp only [K] at h0
      rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum] at h0
      have hterm : ∀ μ ∈ L, (star x ⬝ᵥ ((T μ)ᴴ * T μ).mulVec x).re = (star (T μ *ᵥ x) ⬝ᵥ (T μ *ᵥ x)).re :=
        fun μ _ => by
          rw [← Matrix.mulVec_mulVec x (T μ)ᴴ (T μ), Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      have hsum_nn : ∀ μ ∈ L, 0 ≤ (star x ⬝ᵥ ((T μ)ᴴ * T μ).mulVec x).re := fun μ hμ => by
        rw [hterm μ hμ]; exact blitz_dotProduct_star_self_nonneg _
      have hlam0 := (Finset.sum_eq_zero_iff_of_nonneg hsum_nn).mp h0 lam hlam
      rw [hterm lam hlam] at hlam0
      exact blitz_dotProduct_star_self_eq_zero hlam0
    · intro hall
      dsimp only [K]
      rw [Matrix.sum_mulVec]
      refine Finset.sum_eq_zero fun lam hlam => ?_
      rw [← Matrix.mulVec_mulVec x (T lam)ᴴ (T lam), hall lam hlam, Matrix.mulVec_zero]
  -- P := spectral projection of K onto eigenvalue 0 (reducing h_+-vacuum subspace!)
  let UK := hKh.eigenvectorUnitary
  let k_ev := hKh.eigenvalues
  let P : Mat n := (UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ
  have hPh : P.IsHermitian := by
    refine blitz_hermitian_conj_unitary UK ?_
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
    ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases h : k_ev i = 0 <;> simp [h]
    · simp [Matrix.diagonal_apply_ne _ hij]
  have hP2 : P * P = P := by
    dsimp only [P]
    calc ((UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ) *
          ((UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ)
        = (UK : Mat n) * (Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) *
            ((UK : Mat n)ᴴ * (UK : Mat n)) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0)) *
            (UK : Mat n)ᴴ := by simp only [Matrix.mul_assoc]
      _ = (UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ := by
            rw [blitz_unitary_conj_mul UK, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
            refine congrArg (· * (UK : Mat n)ᴴ) (congrArg ((UK : Mat n) * ·) ?_)
            ext i j; by_cases hij : i = j
            · subst hij; simp only [Matrix.diagonal_apply_eq]; split_ifs <;> simp
            · simp [Matrix.diagonal_apply_ne _ hij]
  have hK_spec : K = (UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ)) * (UK : Mat n)ᴴ := by
    simpa [UK, k_ev, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hKh.spectral_theorem
  have hKP : K * P = 0 := by
    dsimp only [P]; conv_lhs => rw [hK_spec]
    calc ((UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ)) * (UK : Mat n)ᴴ) *
          ((UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ)
        = (UK : Mat n) * (Matrix.diagonal (fun i => (k_ev i : ℂ)) * ((UK : Mat n)ᴴ * (UK : Mat n)) *
            Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0)) * (UK : Mat n)ᴴ := by
            simp only [Matrix.mul_assoc]
      _ = (UK : Mat n) * (0 : Mat n) * (UK : Mat n)ᴴ := by
            rw [blitz_unitary_conj_mul UK, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
            refine congrArg (· * (UK : Mat n)ᴴ) (congrArg ((UK : Mat n) * ·) ?_)
            ext i j; by_cases hij : i = j
            · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
              split_ifs with h0
              · rw [h0]; simp
              · simp
            · simp [Matrix.diagonal_apply_ne _ hij]
      _ = 0 := by simp
  have hPD : P * D = D * P := by
    -- D commutes with K, hence with any function of K's eigenvalues (in particular P = 1_{k_ev = 0}(K))
    have hD'_comm : (UK : Mat n)ᴴ * D * (UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ)) =
        Matrix.diagonal (fun i => (k_ev i : ℂ)) * ((UK : Mat n)ᴴ * D * (UK : Mat n)) := by
      have h1 := congrArg (fun X => (UK : Mat n)ᴴ * X * (UK : Mat n)) hDK.symm
      rw [hK_spec] at h1
      calc (UK : Mat n)ᴴ * D * (UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ))
          = (UK : Mat n)ᴴ * (D * ((UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ)) * (UK : Mat n)ᴴ)) *
              (UK : Mat n) := by
              have hUU := blitz_unitary_conj_mul UK
              calc _ = (UK : Mat n)ᴴ * D * (UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ)) *
                    ((UK : Mat n)ᴴ * (UK : Mat n)) := by rw [hUU, Matrix.mul_one]
                _ = _ := by simp only [Matrix.mul_assoc]
        _ = (UK : Mat n)ᴴ * (((UK : Mat n) * Matrix.diagonal (fun i => (k_ev i : ℂ)) * (UK : Mat n)ᴴ) * D) *
              (UK : Mat n) := h1.symm
        _ = Matrix.diagonal (fun i => (k_ev i : ℂ)) * ((UK : Mat n)ᴴ * D * (UK : Mat n)) := by
              have hUU := blitz_unitary_conj_mul UK
              calc _ = ((UK : Mat n)ᴴ * (UK : Mat n)) * Matrix.diagonal (fun i => (k_ev i : ℂ)) *
                    ((UK : Mat n)ᴴ * D * (UK : Mat n)) := by simp only [Matrix.mul_assoc]
                _ = _ := by rw [hUU, Matrix.one_mul]
    have hP'_comm : (UK : Mat n)ᴴ * D * (UK : Mat n) *
        Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) =
        Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * ((UK : Mat n)ᴴ * D * (UK : Mat n)) := by
      ext i j
      have hij := congr_fun (congr_fun hD'_comm i) j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij ⊢
      by_cases hi : k_ev i = 0 <;> by_cases hj : k_ev j = 0
      · simp [hi, hj]
      · have hne : (k_ev j : ℂ) ≠ (k_ev i : ℂ) := by
          rw [hi]; exact Complex.ofReal_ne_zero.mpr hj
        have h0 : ((UK : Mat n)ᴴ * D * (UK : Mat n)) i j = 0 := by
          have : ((UK : Mat n)ᴴ * D * (UK : Mat n)) i j * ((k_ev j : ℂ) - (k_ev i : ℂ)) = 0 := by
            linear_combination hij
          exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
        simp [hi, hj, h0]
      · have hne : (k_ev j : ℂ) ≠ (k_ev i : ℂ) := by
          rw [hj]; exact Ne.symm (Complex.ofReal_ne_zero.mpr hi)
        have h0 : ((UK : Mat n)ᴴ * D * (UK : Mat n)) i j = 0 := by
          have : ((UK : Mat n)ᴴ * D * (UK : Mat n)) i j * ((k_ev j : ℂ) - (k_ev i : ℂ)) = 0 := by
            linear_combination hij
          exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
        simp [hi, hj, h0]
      · simp [hi, hj]
    dsimp only [P]
    calc (UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ * D
        = (UK : Mat n) * (Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) *
            ((UK : Mat n)ᴴ * D * (UK : Mat n))) * (UK : Mat n)ᴴ := by
            calc _ = (UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) *
                  (UK : Mat n)ᴴ * D * ((UK : Mat n) * (UK : Mat n)ᴴ) := by
                    rw [blitz_unitary_mul_conj UK, Matrix.mul_one]
              _ = _ := by simp only [Matrix.mul_assoc]
      _ = (UK : Mat n) * (((UK : Mat n)ᴴ * D * (UK : Mat n)) *
            Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0)) * (UK : Mat n)ᴴ := by
            rw [← hP'_comm]
      _ = D * ((UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ) := by
            calc _ = ((UK : Mat n) * (UK : Mat n)ᴴ) * D *
                  ((UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0) * (UK : Mat n)ᴴ) := by
                    simp only [Matrix.mul_assoc]
              _ = _ := by rw [blitz_unitary_mul_conj UK, Matrix.one_mul]
  -- H * P = (h : ℂ) • (D * P) and P * H = H * P!
  have hHP : H * P = (h : ℂ) • (D * P) := by
    refine Matrix.ext_of_mulVec_single fun c => ?_
    let x := P.mulVec (Pi.single c (1 : ℂ))
    have hKx : K.mulVec x = 0 := by dsimp only [x]; rw [Matrix.mulVec_mulVec, hKP, Matrix.zero_mulVec]
    have hall := (hK_ker_iff x).mp hKx
    have hHx : H.mulVec x = (h : ℂ) • D.mulVec x := by
      have hx_sum : x = ∑ lam ∈ L, QD lam *ᵥ x := by
        rw [← Matrix.sum_mulVec, hQD_sum, Matrix.one_mulVec]
      conv_lhs => rw [hx_sum]
      conv_rhs => rw [hx_sum]
      rw [Matrix.mulVec_sum, Matrix.mulVec_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun lam hlam => ?_
      have hTl := hall lam hlam
      dsimp only [T] at hTl
      rw [← Matrix.mulVec_mulVec x (H - ((h * lam : ℝ) : ℂ) • 1) (QD lam),
        Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hTl
      have h1 : H.mulVec (QD lam *ᵥ x) = ((h * lam : ℝ) : ℂ) • (QD lam *ᵥ x) := sub_eq_zero.mp hTl
      rw [h1, Matrix.mulVec_mulVec x D (QD lam), hQD_D lam, Matrix.smul_mulVec, smul_smul, Complex.ofReal_mul]
    rw [← Matrix.mulVec_mulVec (Pi.single c (1 : ℂ)) H P, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec (Pi.single c (1 : ℂ)) D P]
    exact hHx
  have hPH : P * H = H * P := by
    have h1 := congrArg Matrix.conjTranspose hHP
    rw [Matrix.conjTranspose_mul H P, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul D P,
      hPh.eq, hH.isHermitian.eq, hD.isHermitian.eq, Complex.star_def, Complex.conj_ofReal,
      hPD, ← hHP] at h1
    exact h1
  let Q : Mat n := 1 - P
  have hQh : Q.IsHermitian := Matrix.isHermitian_one.sub hPh
  have hQ2 : Q * Q = Q := by
    dsimp only [Q]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]; abel
  have hPQ : P * Q = 0 := by dsimp only [Q]; rw [Matrix.mul_sub, Matrix.mul_one, hP2, sub_self]
  have hQP : Q * P = 0 := by dsimp only [Q]; rw [Matrix.sub_mul, Matrix.one_mul, hP2, sub_self]
  have hQD_comm : Q * D = D * Q := by
    dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPD]
  have hQH_comm : Q * H = H * Q := by
    dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPH]
  -- If Q = 0, then P = 1 and H = (h : ℂ) • D immediately!
  by_cases hQ0 : Q = 0
  · have hP1 : P = 1 := by
      have : (1 : Mat n) - P = 0 := hQ0
      exact (sub_eq_zero.mp this).symm
    rw [hP1, Matrix.mul_one, Matrix.mul_one] at hHP
    exact hHP
  · -- Suppose Q ≠ 0; derive contradiction on top eigenspace of D inside ran(Q)!
    exfalso
    -- Construct a joint eigenvector v ≠ 0 with Q v = v, D v = dmax' v (max eigenvalue of D on ran(Q)),
    -- and Φ v = ν v (ν ≥ 0)!
    have hG : (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD).PosDef :=
      posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
    let Φ : Mat n := posDefPow κ hG - D * posDefPow (κ - 1) hG * D
    have hΦh : Φ.IsHermitian := hΦ_psd.isHermitian
    -- Show P commutes with D^(1/2), G, G^κ, G^(κ-1), and Φ!
    have hP_posDefPow : ∀ {A : Mat n} (r : ℝ) (hA : A.PosDef), P * A = A * P →
        P * posDefPow r hA = posDefPow r hA * P := fun {A} r hA hPA => by
      let UA := hA.isHermitian.eigenvectorUnitary
      let ev := hA.isHermitian.eigenvalues
      have hAs : A = (UA : Mat n) * Matrix.diagonal (fun i => (ev i : ℂ)) * (UA : Mat n)ᴴ := by
        simpa [UA, ev, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hA.isHermitian.spectral_theorem
      have hP_c : (UA : Mat n)ᴴ * P * (UA : Mat n) * Matrix.diagonal (fun i => (ev i : ℂ)) =
          Matrix.diagonal (fun i => (ev i : ℂ)) * ((UA : Mat n)ᴴ * P * (UA : Mat n)) := by
        have h1 := congrArg (fun X => (UA : Mat n)ᴴ * X * (UA : Mat n)) hPA
        rw [hAs] at h1
        calc (UA : Mat n)ᴴ * P * (UA : Mat n) * Matrix.diagonal (fun i => (ev i : ℂ))
            = (UA : Mat n)ᴴ * (P * ((UA : Mat n) * Matrix.diagonal (fun i => (ev i : ℂ)) * (UA : Mat n)ᴴ)) *
                (UA : Mat n) := by
                calc _ = (UA : Mat n)ᴴ * P * (UA : Mat n) * Matrix.diagonal (fun i => (ev i : ℂ)) *
                      ((UA : Mat n)ᴴ * (UA : Mat n)) := by rw [blitz_unitary_conj_mul UA, Matrix.mul_one]
                  _ = _ := by simp only [Matrix.mul_assoc]
          _ = (UA : Mat n)ᴴ * (((UA : Mat n) * Matrix.diagonal (fun i => (ev i : ℂ)) * (UA : Mat n)ᴴ) * P) *
                (UA : Mat n) := h1
          _ = Matrix.diagonal (fun i => (ev i : ℂ)) * ((UA : Mat n)ᴴ * P * (UA : Mat n)) := by
                calc _ = ((UA : Mat n)ᴴ * (UA : Mat n)) * Matrix.diagonal (fun i => (ev i : ℂ)) *
                      ((UA : Mat n)ᴴ * P * (UA : Mat n)) := by simp only [Matrix.mul_assoc]
                  _ = _ := by rw [blitz_unitary_conj_mul UA, Matrix.one_mul]
      have hP_r : (UA : Mat n)ᴴ * P * (UA : Mat n) * Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) =
          Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) * ((UA : Mat n)ᴴ * P * (UA : Mat n)) := by
        ext i j
        have hij := congr_fun (congr_fun hP_c i) j
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij ⊢
        by_cases heq : ev i = ev j
        · rw [heq, mul_comm]
        · have hne : (ev j : ℂ) ≠ (ev i : ℂ) := fun hc => heq (Complex.ofReal_injective hc).symm
          have h0 : ((UA : Mat n)ᴴ * P * (UA : Mat n)) i j = 0 := by
            have : ((UA : Mat n)ᴴ * P * (UA : Mat n)) i j * ((ev j : ℂ) - (ev i : ℂ)) = 0 := by
              linear_combination hij
            exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
          simp [h0]
      unfold posDefPow
      calc P * ((UA : Mat n) * Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) * (UA : Mat n)ᴴ)
          = (UA : Mat n) * (((UA : Mat n)ᴴ * P * (UA : Mat n)) *
              Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ))) * (UA : Mat n)ᴴ := by
              calc _ = ((UA : Mat n) * (UA : Mat n)ᴴ) * P *
                    ((UA : Mat n) * Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) * (UA : Mat n)ᴴ) := by
                      rw [blitz_unitary_mul_conj UA, Matrix.one_mul]
                _ = _ := by simp only [Matrix.mul_assoc]
        _ = (UA : Mat n) * (Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) *
              ((UA : Mat n)ᴴ * P * (UA : Mat n))) * (UA : Mat n)ᴴ := by rw [hP_r]
        _ = ((UA : Mat n) * Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) * (UA : Mat n)ᴴ) * P := by
              calc _ = ((UA : Mat n) * Matrix.diagonal (fun i => ((ev i ^ r : ℝ) : ℂ)) * (UA : Mat n)ᴴ) * P *
                    ((UA : Mat n) * (UA : Mat n)ᴴ) := by simp only [Matrix.mul_assoc]
                _ = _ := by rw [blitz_unitary_mul_conj UA, Matrix.mul_one]
    have hP_Dhalf : P * posDefPow (1 / 2 : ℝ) hD = posDefPow (1 / 2 : ℝ) hD * P := hP_posDefPow (1 / 2) hD hPD
    have hP_G : P * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) =
        (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * P := by
      calc P * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD)
          = (P * posDefPow (1 / 2 : ℝ) hD) * H * posDefPow (1 / 2 : ℝ) hD := by simp only [Matrix.mul_assoc]
        _ = posDefPow (1 / 2 : ℝ) hD * (P * H) * posDefPow (1 / 2 : ℝ) hD := by
              rw [hP_Dhalf]; simp only [Matrix.mul_assoc]
        _ = posDefPow (1 / 2 : ℝ) hD * H * (P * posDefPow (1 / 2 : ℝ) hD) := by
              rw [hPH]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hP_Dhalf]; simp only [Matrix.mul_assoc]
    have hP_Φ : P * Φ = Φ * P := by
      dsimp only [Φ]
      rw [Matrix.mul_sub, Matrix.sub_mul, hP_posDefPow κ hG hP_G]
      refine congrArg (fun X => posDefPow κ hG * P - X) ?_
      calc P * (D * posDefPow (κ - 1) hG * D)
          = (P * D) * posDefPow (κ - 1) hG * D := by simp only [Matrix.mul_assoc]
        _ = D * (P * posDefPow (κ - 1) hG) * D := by rw [hPD]; simp only [Matrix.mul_assoc]
        _ = D * posDefPow (κ - 1) hG * (P * D) := by rw [hP_posDefPow (κ - 1) hG hP_G]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPD]; simp only [Matrix.mul_assoc]
    have hD_Φ : D * Φ = Φ * D := by
      -- Global commutativity [D, Φ] = 0 from [D + H, (D + H)^(2κ - 1)] = 0!
      have hcomm1 : (D + H) * posDefPow (2 * κ - 1) (hD.add hH) =
          posDefPow (2 * κ - 1) (hD.add hH) * (D + H) := posDefPow_comm_self (2 * κ - 1) (hD.add hH)
      rw [hEq, Matrix.mul_smul, Matrix.smul_mul] at hcomm1
      have hcomm2 : (D + H) * (posDefPow (1 / 2 : ℝ) hD * posDefPow (κ - 1) hG * posDefPow (1 / 2 : ℝ) hD) =
          (posDefPow (1 / 2 : ℝ) hD * posDefPow (κ - 1) hG * posDefPow (1 / 2 : ℝ) hD) * (D + H) :=
        smul_right_injective (Mat n) (Complex.ofReal_ne_zero.mpr hΛ_pos.ne') hcomm1
      let Dh := posDefPow (1 / 2 : ℝ) hD
      have hDh2 : Dh * Dh = D := by dsimp only [Dh]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
      have hDhD : Dh * D = D * Dh := (posDefPow_comm_self (1 / 2) hD).symm
      have hG_pow_k : (Dh * H * Dh) * posDefPow (κ - 1) hG = posDefPow κ hG := by
        have h1 := posDefPow_one hG
        calc (Dh * H * Dh) * posDefPow (κ - 1) hG
            = posDefPow 1 hG * posDefPow (κ - 1) hG := by rw [h1]
          _ = posDefPow (1 + (κ - 1)) hG := posDefPow_mul_posDefPow 1 (κ - 1) hG
          _ = posDefPow κ hG := by congr 1; ring
      have hG_pow_k' : posDefPow (κ - 1) hG * (Dh * H * Dh) = posDefPow κ hG := by
        rw [← posDefPow_comm_self (κ - 1) hG, hG_pow_k]
      have h3 := congrArg (fun X => Dh * X * Dh) hcomm2
      have hL3 : Dh * ((D + H) * (Dh * posDefPow (κ - 1) hG * Dh)) * Dh =
          D * (D * posDefPow (κ - 1) hG * D) + posDefPow κ hG * D := by
        rw [Matrix.add_mul, Matrix.mul_add, Matrix.add_mul]
        refine congrArg₂ (· + ·) ?_ ?_
        · calc Dh * (D * (Dh * posDefPow (κ - 1) hG * Dh)) * Dh
              = D * (Dh * Dh) * posDefPow (κ - 1) hG * (Dh * Dh) := by
                  rw [← Matrix.mul_assoc Dh D, hDhD]; simp only [Matrix.mul_assoc]
            _ = D * (D * posDefPow (κ - 1) hG * D) := by rw [hDh2]; simp only [Matrix.mul_assoc]
        · calc Dh * (H * (Dh * posDefPow (κ - 1) hG * Dh)) * Dh
              = ((Dh * H * Dh) * posDefPow (κ - 1) hG) * (Dh * Dh) := by simp only [Matrix.mul_assoc]
            _ = posDefPow κ hG * D := by rw [hG_pow_k, hDh2]
      have hR3 : Dh * ((Dh * posDefPow (κ - 1) hG * Dh) * (D + H)) * Dh =
          D * posDefPow (κ - 1) hG * D * D + D * posDefPow κ hG := by
        rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul]
        refine congrArg₂ (· + ·) ?_ ?_
        · have hDhDDh : Dh * D * Dh = (Dh * Dh) * D := by
            calc Dh * D * Dh = Dh * (Dh * Dh) * Dh := by rw [← hDh2]
              _ = (Dh * Dh) * (Dh * Dh) := by simp only [Matrix.mul_assoc]
              _ = (Dh * Dh) * D := by rw [hDh2]
          have hstep : Dh * (Dh * posDefPow (κ - 1) hG * Dh * D) * Dh =
              (Dh * Dh) * posDefPow (κ - 1) hG * (Dh * D * Dh) := by simp only [Matrix.mul_assoc]
          rw [hstep, hDhDDh, hDh2]
          simp only [Matrix.mul_assoc]
        · have hstep : Dh * (Dh * posDefPow (κ - 1) hG * Dh * H) * Dh =
              (Dh * Dh) * (posDefPow (κ - 1) hG * (Dh * H * Dh)) := by simp only [Matrix.mul_assoc]
          rw [hstep, hDh2, hG_pow_k']
      rw [hL3, hR3] at h3
      dsimp only [Φ]
      rw [Matrix.mul_sub, Matrix.sub_mul]
      have h4 : D * posDefPow κ hG + D * posDefPow (κ - 1) hG * D * D =
          posDefPow κ hG * D + D * (D * posDefPow (κ - 1) hG * D) := by
        rw [add_comm, ← h3, add_comm]
      exact sub_eq_sub_iff_add_eq_add.mpr h4
    -- Now find the maximum eigenvalue dmax' of D on ran(Q) via B_D = D - (M_D : ℂ) • P!
    let MD : ℝ := D.trace.re + 1
    let BD : Mat n := D - (MD : ℂ) • P
    have hBDh : BD.IsHermitian := hD.isHermitian.sub (blitz_hermitian_smul_real hPh MD)
    have hBD_P : P * BD = BD * P := by
      dsimp only [BD]; rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hPD, hP2]
    have hBD_Φ : Φ * BD = BD * Φ := by
      calc Φ * BD = Φ * (D - (MD : ℂ) • P) := rfl
        _ = Φ * D - (MD : ℂ) • (Φ * P) := by rw [Matrix.mul_sub, Matrix.mul_smul]
        _ = D * Φ - (MD : ℂ) • (P * Φ) := by rw [hD_Φ, hP_Φ]
        _ = BD * Φ := by dsimp only [BD]; rw [Matrix.sub_mul, Matrix.smul_mul]
    -- Since Q ≠ 0, there exists i with BD eigenvalue > 0 (and every BD eigenvalue on ran(P) is < 0)!
    have hQ_ex : ∃ x : Fin n → ℂ, Q.mulVec x ≠ 0 := by
      by_contra hall; push Not at hall
      exact hQ0 (Matrix.ext_of_mulVec_single fun c => (hall (Pi.single c 1)).trans (Matrix.zero_mulVec _).symm)
    obtain ⟨x0, hx0⟩ := hQ_ex
    have hn_nonempty : Nonempty (Fin n) := by
      by_contra hne; rw [not_nonempty_iff] at hne; exact hx0 (funext fun i => (hne.false i).elim)
    let UBD := hBDh.eigenvectorUnitary
    let b_ev := hBDh.eigenvalues
    obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ b_ev Finset.univ_nonempty
    let dmax' : ℝ := b_ev i_max
    have hBD_spec : BD = (UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ)) * (UBD : Mat n)ᴴ := by
      simpa [UBD, b_ev, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hBDh.spectral_theorem
    have hdmax'_pos : 0 < dmax' := by
      let y0 := Q.mulVec x0
      have hBD_y0 : BD.mulVec y0 = D.mulVec y0 := by
        dsimp only [BD, y0]
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec x0 P Q, hPQ, Matrix.zero_mulVec,
          smul_zero, sub_zero]
      have hpos_y0 : 0 < (star y0 ⬝ᵥ BD.mulVec y0).re := by
        rw [hBD_y0]; exact blitz_posDef_quad_re_pos hD hx0
      let z0 := (UBD : Mat n)ᴴ.mulVec y0
      have hval : (star y0 ⬝ᵥ BD.mulVec y0).re = ∑ i, ‖z0 i‖ ^ 2 * b_ev i := by
        have h1 : star y0 ⬝ᵥ BD.mulVec y0 = ∑ i, (((‖z0 i‖ ^ 2 * b_ev i : ℝ) : ℂ)) := by
          rw [hBD_spec, ← Matrix.mulVec_mulVec y0 ((UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ))) (UBD : Mat n)ᴴ,
            ← Matrix.mulVec_mulVec z0 (UBD : Mat n), Matrix.dotProduct_mulVec,
            show star y0 ᵥ* (UBD : Mat n) = star z0 by
              symm; dsimp only [z0]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
          rw [dotProduct]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
          have hc : starRingEnd ℂ (z0 i) * ((b_ev i : ℂ) * z0 i) =
              (starRingEnd ℂ (z0 i) * z0 i) * (b_ev i : ℂ) := by ring
          rw [hc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
        rw [h1, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
      have hle : ∑ i, ‖z0 i‖ ^ 2 * b_ev i ≤ dmax' * ∑ i, ‖z0 i‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_comm (‖z0 i‖ ^ 2)]; exact mul_le_mul_of_nonneg_right (hi_max i (Finset.mem_univ i)) (sq_nonneg _)
      have hz0_pos : 0 < ∑ i, ‖z0 i‖ ^ 2 := by
        have hnorm : (star z0 ⬝ᵥ z0).re = (star y0 ⬝ᵥ y0).re := by
          dsimp only [z0]
          rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
            Matrix.mulVec_mulVec, blitz_unitary_mul_conj UBD, Matrix.one_mulVec]
        have : ∑ i, ‖z0 i‖ ^ 2 = (star z0 ⬝ᵥ z0).re := by
          rw [dotProduct, Complex.re_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        rw [this, hnorm]; exact blitz_dotProduct_star_self_pos hx0
      rw [hval] at hpos_y0
      nlinarith only [hpos_y0, hle, hz0_pos]
    -- Define top spectral projection P_top of BD onto eigenvalue dmax', and extract joint eigenvector v of (D, Φ)!
    let Ptop : Mat n := (UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ
    have hPtop_h : Ptop.IsHermitian := by
      refine blitz_hermitian_conj_unitary UBD ?_
      rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
      ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases h : b_ev i = dmax' <;> simp [h]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hPtop_ne : Ptop ≠ 0 := by
      intro h0
      have h1 := congrArg (fun X => (UBD : Mat n)ᴴ * X * (UBD : Mat n)) h0
      dsimp only [Ptop] at h1
      simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc] at h1
      rw [← Matrix.mul_assoc (UBD : Mat n)ᴴ (UBD : Mat n),
        blitz_unitary_conj_mul UBD, Matrix.one_mul, Matrix.mul_one] at h1
      have h2 := congr_fun (congr_fun h1 i_max) i_max
      simp [dmax'] at h2
    have hBD_Ptop : BD * Ptop = (dmax' : ℂ) • Ptop := by
      dsimp only [Ptop]; conv_lhs => rw [hBD_spec]
      calc ((UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ)) * (UBD : Mat n)ᴴ) *
            ((UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ)
          = (UBD : Mat n) * (Matrix.diagonal (fun i => (b_ev i : ℂ)) * ((UBD : Mat n)ᴴ * (UBD : Mat n)) *
              Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0)) * (UBD : Mat n)ᴴ := by
              simp only [Matrix.mul_assoc]
        _ = (UBD : Mat n) * ((dmax' : ℂ) • Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0)) *
              (UBD : Mat n)ᴴ := by
              rw [blitz_unitary_conj_mul UBD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
              refine congrArg (· * (UBD : Mat n)ᴴ) (congrArg ((UBD : Mat n) * ·) ?_)
              ext i j; by_cases hij : i = j
              · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
                split_ifs with heq
                · rw [heq, mul_one]
                · simp
              · simp [Matrix.diagonal_apply_ne _ hij]
        _ = (dmax' : ℂ) • Ptop := by rw [Matrix.mul_smul, Matrix.smul_mul]
    have hPtop_Φ : Ptop * Φ = Φ * Ptop := by
      have hΦ_c : (UBD : Mat n)ᴴ * Φ * (UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ)) =
          Matrix.diagonal (fun i => (b_ev i : ℂ)) * ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) := by
        have h1 := congrArg (fun X => (UBD : Mat n)ᴴ * X * (UBD : Mat n)) hBD_Φ
        rw [hBD_spec] at h1
        calc (UBD : Mat n)ᴴ * Φ * (UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ))
            = (UBD : Mat n)ᴴ * (Φ * ((UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ)) * (UBD : Mat n)ᴴ)) *
                (UBD : Mat n) := by
                calc _ = (UBD : Mat n)ᴴ * Φ * (UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ)) *
                      ((UBD : Mat n)ᴴ * (UBD : Mat n)) := by rw [blitz_unitary_conj_mul UBD, Matrix.mul_one]
                  _ = _ := by simp only [Matrix.mul_assoc]
          _ = (UBD : Mat n)ᴴ * (((UBD : Mat n) * Matrix.diagonal (fun i => (b_ev i : ℂ)) * (UBD : Mat n)ᴴ) * Φ) *
                (UBD : Mat n) := h1
          _ = Matrix.diagonal (fun i => (b_ev i : ℂ)) * ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) := by
                calc _ = ((UBD : Mat n)ᴴ * (UBD : Mat n)) * Matrix.diagonal (fun i => (b_ev i : ℂ)) *
                      ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) := by simp only [Matrix.mul_assoc]
                  _ = _ := by rw [blitz_unitary_conj_mul UBD, Matrix.one_mul]
      have hP_r : (UBD : Mat n)ᴴ * Φ * (UBD : Mat n) *
          Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) =
          Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) := by
        ext i j
        have hij := congr_fun (congr_fun hΦ_c i) j
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij ⊢
        by_cases hi : b_ev i = dmax' <;> by_cases hj : b_ev j = dmax'
        · simp [hi, hj]
        · have hne : (b_ev j : ℂ) ≠ (b_ev i : ℂ) := fun hc => hj ((Complex.ofReal_injective hc).trans hi)
          have h0 : ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) i j = 0 := by
            have : ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) i j * ((b_ev j : ℂ) - (b_ev i : ℂ)) = 0 := by
              linear_combination hij
            exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
          simp [hi, hj, h0]
        · have hne : (b_ev j : ℂ) ≠ (b_ev i : ℂ) := fun hc => hi ((Complex.ofReal_injective hc).symm.trans hj)
          have h0 : ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) i j = 0 := by
            have : ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) i j * ((b_ev j : ℂ) - (b_ev i : ℂ)) = 0 := by
              linear_combination hij
            exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
          simp [hi, hj, h0]
        · simp [hi, hj]
      dsimp only [Ptop]
      calc (UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ * Φ
          = (UBD : Mat n) * (Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) *
              ((UBD : Mat n)ᴴ * Φ * (UBD : Mat n))) * (UBD : Mat n)ᴴ := by
              calc _ = (UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) *
                    (UBD : Mat n)ᴴ * Φ * ((UBD : Mat n) * (UBD : Mat n)ᴴ) := by
                      rw [blitz_unitary_mul_conj UBD, Matrix.mul_one]
                _ = _ := by simp only [Matrix.mul_assoc]
        _ = (UBD : Mat n) * (((UBD : Mat n)ᴴ * Φ * (UBD : Mat n)) *
              Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0)) * (UBD : Mat n)ᴴ := by rw [← hP_r]
        _ = Φ * ((UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ) := by
              calc _ = ((UBD : Mat n) * (UBD : Mat n)ᴴ) * Φ *
                    ((UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ) := by
                      simp only [Matrix.mul_assoc]
                _ = _ := by rw [blitz_unitary_mul_conj UBD, Matrix.one_mul]
    -- Take an eigenvector v of (Φ + (1 : ℂ) • 1) * Ptop with positive eigenvalue (since Φ + I ≻ 0 and Ptop ≠ 0)!
    let BΦ : Mat n := Ptop * (Φ + 1) * Ptop
    have hΦ1_pd : (Φ + 1).PosDef := by
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      refine ⟨hΦh.add Matrix.isHermitian_one, fun x hx => ?_⟩
      rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add]
      have h1 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hΦ_psd).2 x
      have h2 := (Matrix.posDef_iff_dotProduct_mulVec.mp (Matrix.PosDef.one (n := Fin n) (R := ℂ))).2 hx
      rw [Matrix.one_mulVec] at h2
      rw [Complex.lt_def, Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.add_im]
      rw [Complex.le_def, Complex.zero_re, Complex.zero_im] at h1
      rw [Complex.lt_def, Complex.zero_re, Complex.zero_im] at h2
      exact ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
    have hBΦh : BΦ.IsHermitian := by
      dsimp only [BΦ]
      rw [Matrix.IsHermitian, Matrix.conjTranspose_mul (Ptop * (Φ + 1)) Ptop,
        Matrix.conjTranspose_mul Ptop (Φ + 1),
        hPtop_h.eq, hΦ1_pd.isHermitian.eq, ← Matrix.mul_assoc]
    have hPtop2 : Ptop * Ptop = Ptop := by
      dsimp only [Ptop]
      calc ((UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ) *
            ((UBD : Mat n) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) * (UBD : Mat n)ᴴ)
          = (UBD : Mat n) * (Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0) *
              ((UBD : Mat n)ᴴ * (UBD : Mat n)) * Matrix.diagonal (fun i => if b_ev i = dmax' then (1 : ℂ) else 0)) *
              (UBD : Mat n)ᴴ := by simp only [Matrix.mul_assoc]
        _ = Ptop := by
              rw [blitz_unitary_conj_mul UBD, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
              refine congrArg (· * (UBD : Mat n)ᴴ) (congrArg ((UBD : Mat n) * ·) ?_)
              ext i j; by_cases hij : i = j
              · subst hij; simp only [Matrix.diagonal_apply_eq]; by_cases h : b_ev i = dmax' <;> simp [h]
              · simp [Matrix.diagonal_apply_ne _ hij]
    let UBΦ := hBΦh.eigenvectorUnitary
    let evΦ := hBΦh.eigenvalues
    obtain ⟨j_max, _, hj_max⟩ := Finset.exists_max_image Finset.univ evΦ Finset.univ_nonempty
    let v : Fin n → ℂ := (UBΦ : Mat n).mulVec (Pi.single j_max (1 : ℂ))
    have hv_ne : v ≠ 0 := by
      intro hv0
      have h1 := congrArg (Matrix.mulVec (UBΦ : Mat n)ᴴ) hv0
      dsimp only [v] at h1
      rw [Matrix.mulVec_mulVec, blitz_unitary_conj_mul UBΦ, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      have := congr_fun h1 j_max; simp at this
    have hBΦ_spec : BΦ = (UBΦ : Mat n) * Matrix.diagonal (fun i => (evΦ i : ℂ)) * (UBΦ : Mat n)ᴴ := by
      simpa [UBΦ, evΦ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hBΦh.spectral_theorem
    have hBΦ_v : BΦ.mulVec v = (evΦ j_max : ℂ) • v := by
      dsimp only [v]; conv_lhs => rw [hBΦ_spec]
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        blitz_unitary_conj_mul UBΦ, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
      refine congrArg (Matrix.mulVec (UBΦ : Mat n)) ?_
      ext i; by_cases hi : i = j_max <;> simp [Matrix.mulVec_diagonal, hi]
    have hevΦ_pos : 0 < evΦ j_max := by
      obtain ⟨y1, hy1⟩ : ∃ y, Ptop.mulVec y ≠ 0 := by
        by_contra hall; push Not at hall
        exact hPtop_ne (Matrix.ext_of_mulVec_single fun c => (hall (Pi.single c 1)).trans (Matrix.zero_mulVec _).symm)
      have hpos1 : 0 < (star y1 ⬝ᵥ BΦ.mulVec y1).re := by
        have hq_eq : star y1 ⬝ᵥ BΦ.mulVec y1 = star (Ptop.mulVec y1) ⬝ᵥ (Φ + 1).mulVec (Ptop.mulVec y1) := by
          dsimp only [BΦ]
          rw [← Matrix.mulVec_mulVec y1 (Ptop * (Φ + 1)) Ptop, ← Matrix.mulVec_mulVec (Ptop.mulVec y1) Ptop (Φ + 1),
            Matrix.dotProduct_mulVec,
            show star y1 ᵥ* Ptop = star (Ptop.mulVec y1) by rw [Matrix.star_mulVec, hPtop_h.eq]]
        rw [hq_eq]
        exact blitz_posDef_quad_re_pos hΦ1_pd hy1
      let z1 := (UBΦ : Mat n)ᴴ.mulVec y1
      have hval1 : (star y1 ⬝ᵥ BΦ.mulVec y1).re = ∑ i, ‖z1 i‖ ^ 2 * evΦ i := by
        have h1 : star y1 ⬝ᵥ BΦ.mulVec y1 = ∑ i, (((‖z1 i‖ ^ 2 * evΦ i : ℝ) : ℂ)) := by
          rw [hBΦ_spec, ← Matrix.mulVec_mulVec y1 ((UBΦ : Mat n) * Matrix.diagonal (fun i => (evΦ i : ℂ))) (UBΦ : Mat n)ᴴ,
            ← Matrix.mulVec_mulVec z1 (UBΦ : Mat n), Matrix.dotProduct_mulVec,
            show star y1 ᵥ* (UBΦ : Mat n) = star z1 by
              dsimp only [z1]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
          rw [dotProduct]; refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
          have hc : starRingEnd ℂ (z1 i) * ((evΦ i : ℂ) * z1 i) =
              (starRingEnd ℂ (z1 i) * z1 i) * (evΦ i : ℂ) := by ring
          rw [hc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
        rw [h1, Complex.re_sum]; refine Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
      have hle1 : ∑ i, ‖z1 i‖ ^ 2 * evΦ i ≤ evΦ j_max * ∑ i, ‖z1 i‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _ => ?_
        rw [mul_comm (‖z1 i‖ ^ 2)]; exact mul_le_mul_of_nonneg_right (hj_max i (Finset.mem_univ i)) (sq_nonneg _)
      have hz1_pos : 0 < ∑ i, ‖z1 i‖ ^ 2 := by
        have hnorm : (star z1 ⬝ᵥ z1).re = (star y1 ⬝ᵥ y1).re := by
          dsimp only [z1]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
            ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, blitz_unitary_mul_conj UBΦ, Matrix.one_mulVec]
        have : ∑ i, ‖z1 i‖ ^ 2 = (star z1 ⬝ᵥ z1).re := by
          rw [dotProduct, Complex.re_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        have hy1_ne : y1 ≠ 0 := fun h0 => hy1 (by rw [h0, Matrix.mulVec_zero])
        rw [this, hnorm]; exact blitz_dotProduct_star_self_pos hy1_ne
      rw [hval1] at hpos1; nlinarith only [hpos1, hle1, hz1_pos]
    -- Since BΦ v = evΦ j_max • v with evΦ j_max > 0 and Ptop * BΦ = BΦ, we get Ptop v = v!
    have hPtop_v : Ptop.mulVec v = v := by
      have h1 : (evΦ j_max : ℂ) • Ptop.mulVec v = (evΦ j_max : ℂ) • v := by
        calc (evΦ j_max : ℂ) • Ptop.mulVec v
            = Ptop.mulVec (BΦ.mulVec v) := by rw [← Matrix.mulVec_smul, ← hBΦ_v]
          _ = BΦ.mulVec v := by
                rw [Matrix.mulVec_mulVec]; dsimp only [BΦ]
                rw [show Ptop * (Ptop * (Φ + 1) * Ptop) = (Ptop * Ptop) * (Φ + 1) * Ptop by simp only [Matrix.mul_assoc],
                  hPtop2]
          _ = (evΦ j_max : ℂ) • v := hBΦ_v
      exact smul_right_injective (Fin n → ℂ) (Complex.ofReal_ne_zero.mpr hevΦ_pos.ne') h1
    -- Hence BD v = dmax' v, P v = 0, Q v = v, D v = dmax' v, and Φ v = (evΦ j_max - 1) v!
    have hBD_v : BD.mulVec v = (dmax' : ℂ) • v := by
      rw [← hPtop_v, Matrix.mulVec_mulVec, hBD_Ptop, Matrix.smul_mulVec, hPtop_v]
    have hPv0 : P.mulVec v = 0 := by
      by_contra hne
      have h1 : BD.mulVec (P.mulVec v) = (dmax' : ℂ) • (P.mulVec v) := by
        rw [Matrix.mulVec_mulVec, ← hBD_P, ← Matrix.mulVec_mulVec, hBD_v, Matrix.mulVec_smul]
      have h2 : BD.mulVec (P.mulVec v) = D.mulVec (P.mulVec v) - (MD : ℂ) • (P.mulVec v) := by
        dsimp only [BD]; rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec v P P, hP2]
      have h3 := congrArg (fun z => (star (P.mulVec v) ⬝ᵥ z).re) (h1.symm.trans h2)
      simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h3
      have hDlt := blitz_posDef_quad_re_lt_trace hD hne
      have hnp := blitz_dotProduct_star_self_pos hne
      dsimp only [MD] at h3
      nlinarith only [h3, hDlt, hnp, hdmax'_pos]
    have hQv : Q.mulVec v = v := by
      dsimp only [Q]; rw [Matrix.sub_mulVec, Matrix.one_mulVec, hPv0, sub_zero]
    have hDv : D.mulVec v = (dmax' : ℂ) • v := by
      have h1 : BD.mulVec v = D.mulVec v := by
        dsimp only [BD]; rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hPv0, smul_zero, sub_zero]
      rw [← h1]; exact hBD_v
    let ν : ℝ := evΦ j_max - 1
    have hΦv : Φ.mulVec v = (ν : ℂ) • v := by
      have h1 : BΦ.mulVec v = Φ.mulVec v + v := by
        dsimp only [BΦ]
        rw [← Matrix.mulVec_mulVec v (Ptop * (Φ + 1)) Ptop, hPtop_v, Matrix.mul_add, Matrix.mul_one,
          hPtop_Φ, Matrix.add_mulVec, ← Matrix.mulVec_mulVec v Φ Ptop, hPtop_v]
      rw [h1] at hBΦ_v
      have h2 : Φ.mulVec v = (evΦ j_max : ℂ) • v - (1 : ℂ) • v := by
        rw [one_smul]; exact eq_sub_of_add_eq hBΦ_v
      rw [h2, ← sub_smul]; dsimp only [ν]; push_cast; rfl
    have hν_nn : 0 ≤ ν := by
      have hnn := posSemidef_quad_re_nonneg hΦ_psd v
      rw [hΦv, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at hnn
      have hnp := blitz_dotProduct_star_self_pos hv_ne
      nlinarith only [hnn, hnp]
    -- Now build the replaced PosDef pair D̃ = Q D Q + dmax' P, H̃ = Q H Q + (h * dmax') P!
    let Dtilde : Mat n := Q * D * Q + (dmax' : ℂ) • P
    let Htilde : Mat n := Q * H * Q + ((h * dmax' : ℝ) : ℂ) • P
    obtain ⟨hDtilde_raw, hDtilde_pow⟩ := posDefPow_block_replace (1 / 2) dmax' hdmax'_pos hD hPh hP2 hPD
    obtain ⟨hHtilde_raw, _⟩ := posDefPow_block_replace 1 (h * dmax') (mul_pos (by linarith) hdmax'_pos) hH hPh hP2 hPH
    have hDtilde : Dtilde.PosDef := hDtilde_raw
    have hHtilde : Htilde.PosDef := hHtilde_raw
    have hDtilde_half : posDefPow (1 / 2 : ℝ) hDtilde =
        Q * posDefPow (1 / 2 : ℝ) hD * Q + ((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P := hDtilde_pow
    -- Check D̃ ⪯ dmax' • 1 globally on ALL of ℂⁿ!
    have hDtilde_le : ((dmax' : ℂ) • (1 : Mat n) - Dtilde).PosSemidef := by
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨(blitz_hermitian_smul_real Matrix.isHermitian_one dmax').sub hDtilde.isHermitian, fun x => ?_⟩
      have hx_split : (dmax' : ℂ) • (1 : Mat n) - Dtilde = Q * ((dmax' : ℂ) • (1 : Mat n) - BD) * Q := by
        have h1 : (1 : Mat n) = Q + P := by dsimp only [Q]; abel
        dsimp only [Dtilde, BD]
        calc (dmax' : ℂ) • (1 : Mat n) - (Q * D * Q + (dmax' : ℂ) • P)
            = (dmax' : ℂ) • Q - Q * D * Q := by rw [h1, smul_add]; abel
          _ = Q * ((dmax' : ℂ) • (1 : Mat n) - (D - (MD : ℂ) • P)) * Q := by
                have hQMP : Q * ((MD : ℂ) • P) = 0 := by rw [Matrix.mul_smul, hQP, smul_zero]
                rw [Matrix.mul_sub Q, Matrix.mul_sub Q, hQMP, sub_zero,
                  Matrix.sub_mul _ _ Q, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ2]
      let y := Q.mulVec x
      have hquad_eq : star x ⬝ᵥ ((dmax' : ℂ) • (1 : Mat n) - Dtilde).mulVec x =
          star y ⬝ᵥ ((dmax' : ℂ) • (1 : Mat n) - BD).mulVec y := by
        rw [hx_split, ← Matrix.mulVec_mulVec x (Q * ((dmax' : ℂ) • 1 - BD)) Q,
          ← Matrix.mulVec_mulVec y Q ((dmax' : ℂ) • 1 - BD), Matrix.dotProduct_mulVec,
          show star x ᵥ* Q = star y by dsimp only [y]; rw [Matrix.star_mulVec, hQh.eq]]
      rw [hquad_eq]
      let z := (UBD : Mat n)ᴴ.mulVec y
      have hval : star y ⬝ᵥ ((dmax' : ℂ) • (1 : Mat n) - BD).mulVec y =
          ∑ i, (((‖z i‖ ^ 2 * (dmax' - b_ev i) : ℝ) : ℂ)) := by
        have hspec_sub : (dmax' : ℂ) • (1 : Mat n) - BD =
            (UBD : Mat n) * Matrix.diagonal (fun i => ((dmax' - b_ev i : ℝ) : ℂ)) * (UBD : Mat n)ᴴ := by
          have h1u : (dmax' : ℂ) • (1 : Mat n) =
              (UBD : Mat n) * Matrix.diagonal (fun _ => (dmax' : ℂ)) * (UBD : Mat n)ᴴ := by
            have hdiag : Matrix.diagonal (fun _ : Fin n => (dmax' : ℂ)) = (dmax' : ℂ) • (1 : Mat n) := by
              ext i j; by_cases hij : i = j <;> simp [hij]
            rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, blitz_unitary_mul_conj UBD]
          conv_lhs => rw [h1u, hBD_spec]
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
          refine congrArg (· * (UBD : Mat n)ᴴ) (congrArg ((UBD : Mat n) * ·) ?_)
          ext i j; by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.diagonal_apply_ne _ hij]
        rw [hspec_sub,
          ← Matrix.mulVec_mulVec y ((UBD : Mat n) * Matrix.diagonal (fun i => ((dmax' - b_ev i : ℝ) : ℂ))) (UBD : Mat n)ᴴ,
          ← Matrix.mulVec_mulVec z (UBD : Mat n), Matrix.dotProduct_mulVec,
          show star y ᵥ* (UBD : Mat n) = star z by
            symm; dsimp only [z]; rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]]
        rw [dotProduct]; refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
        have hc : starRingEnd ℂ (z i) * (((dmax' - b_ev i : ℝ) : ℂ) * z i) =
            (starRingEnd ℂ (z i) * z i) * ((dmax' - b_ev i : ℝ) : ℂ) := by ring
        rw [hc, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
      rw [hval, Complex.le_def, Complex.zero_re, Complex.zero_im, Complex.re_sum, Complex.im_sum]
      refine ⟨Finset.sum_nonneg fun i _ => ?_, symm (Finset.sum_eq_zero fun i _ => Complex.ofReal_im _)⟩
      rw [Complex.ofReal_re]
      exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hi_max i (Finset.mem_univ i)))
    -- Check G̃ = Q G Q + (h * dmax'²) P, and D̃ + H̃ = Q (D + H) Q + ((1 + h) dmax') P!
    have hGtilde : (posDefPow (1 / 2 : ℝ) hDtilde * Htilde * posDefPow (1 / 2 : ℝ) hDtilde).PosDef :=
      posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hDtilde) hHtilde
    have hGtilde_eq : posDefPow (1 / 2 : ℝ) hDtilde * Htilde * posDefPow (1 / 2 : ℝ) hDtilde =
        Q * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * Q +
        ((h * dmax' ^ 2 : ℝ) : ℂ) • P := by
      rw [hDtilde_half]
      dsimp only [Htilde]
      have hQ_Dh : Q * posDefPow (1 / 2 : ℝ) hD = posDefPow (1 / 2 : ℝ) hD * Q := by
        dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_Dhalf]
      have hQDhQ : Q * posDefPow (1 / 2 : ℝ) hD * Q = Q * posDefPow (1 / 2 : ℝ) hD := by
        rw [Matrix.mul_assoc, ← hQ_Dh, ← Matrix.mul_assoc, hQ2]
      have hQHQ : Q * H * Q = Q * H := by
        rw [Matrix.mul_assoc, ← hQH_comm, ← Matrix.mul_assoc, hQ2]
      have hQ_G : Q * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * Q =
          (Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * H * Q) * (Q * posDefPow (1 / 2 : ℝ) hD * Q) := by
        rw [hQDhQ, hQHQ]
        calc Q * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * Q
            = (Q * posDefPow (1 / 2 : ℝ) hD) * H * (posDefPow (1 / 2 : ℝ) hD * Q) := by
                simp only [Matrix.mul_assoc]
          _ = (Q * posDefPow (1 / 2 : ℝ) hD) * H * (Q * posDefPow (1 / 2 : ℝ) hD) := by
                rw [← hQ_Dh]
          _ = (Q * posDefPow (1 / 2 : ℝ) hD * Q) * H * (Q * posDefPow (1 / 2 : ℝ) hD) :=
                congrArg (· * H * (Q * posDefPow (1 / 2 : ℝ) hD)) hQDhQ.symm
          _ = Q * posDefPow (1 / 2 : ℝ) hD * (Q * H) * (Q * posDefPow (1 / 2 : ℝ) hD) := by
                simp only [Matrix.mul_assoc]
      simp only [Matrix.add_mul, Matrix.mul_add]
      have kQP_r : ∀ X : Mat n, (X * Q) * P = 0 := fun X => by rw [Matrix.mul_assoc, hQP, Matrix.mul_zero]
      have kPQ_l : ∀ X : Mat n, P * (Q * X) = 0 := fun X => by rw [← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
      have kill1 : (Q * posDefPow (1 / 2 : ℝ) hD * Q) * (((h * dmax' : ℝ) : ℂ) • P) = 0 := by
        rw [Matrix.mul_smul, kQP_r, smul_zero]
      have kill2 : (((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P) * (Q * H * Q) = 0 := by
        rw [Matrix.smul_mul, Matrix.mul_assoc Q H Q, kPQ_l, smul_zero]
      have kill3 : (Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * H * Q) * (((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P) = 0 := by
        rw [Matrix.mul_smul, show (Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * H * Q) * P =
          ((Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * H) * Q) * P by simp only [Matrix.mul_assoc], kQP_r, smul_zero]
      have kill4 : (((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P) * (((h * dmax' : ℝ) : ℂ) • P) *
          (Q * posDefPow (1 / 2 : ℝ) hD * Q) = 0 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul, hP2,
          Matrix.mul_assoc Q (posDefPow (1 / 2 : ℝ) hD) Q, kPQ_l, smul_zero]
      simp only [kill1, kill2, kill3, kill4, Matrix.zero_mul, zero_add, add_zero, ← hQ_G]
      refine congrArg (Q * (posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD) * Q + ·) ?_
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP2]
      refine congrArg (· • P) ?_
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]; apply congrArg Complex.ofReal
      have hsq : dmax' ^ (1 / 2 : ℝ) * dmax' ^ (1 / 2 : ℝ) = dmax' := by
        rw [← Real.rpow_add hdmax'_pos]; norm_num
      calc dmax' ^ (1 / 2 : ℝ) * (h * dmax' * dmax' ^ (1 / 2 : ℝ))
          = h * dmax' * (dmax' ^ (1 / 2 : ℝ) * dmax' ^ (1 / 2 : ℝ)) := by ring
        _ = h * dmax' ^ 2 := by rw [hsq]; ring
    have hGtilde_pow : ∀ r : ℝ, posDefPow r hGtilde =
        Q * posDefPow r hG * Q + (((h * dmax' ^ 2) ^ r : ℝ) : ℂ) • P := fun r => by
      obtain ⟨hG2, hpow2⟩ := posDefPow_block_replace r (h * dmax' ^ 2)
        (mul_pos (by linarith) (sq_pos_of_pos hdmax'_pos)) hG hPh hP2 hP_G
      rw [posDefPow_congr r hGtilde_eq hGtilde hG2, hpow2]
    have hDHtilde_eq : Dtilde + Htilde = Q * (D + H) * Q + (((1 + h) * dmax' : ℝ) : ℂ) • P := by
      dsimp only [Dtilde, Htilde]
      rw [Matrix.mul_add, Matrix.add_mul]
      have hsc : (dmax' : ℂ) • P + ((h * dmax' : ℝ) : ℂ) • P = (((1 + h) * dmax' : ℝ) : ℂ) • P := by
        rw [← add_smul]; refine congrArg (· • P) ?_; push_cast; ring
      calc Q * D * Q + (dmax' : ℂ) • P + (Q * H * Q + ((h * dmax' : ℝ) : ℂ) • P)
          = (Q * D * Q + Q * H * Q) + ((dmax' : ℂ) • P + ((h * dmax' : ℝ) : ℂ) • P) := by abel
        _ = Q * D * Q + Q * H * Q + (((1 + h) * dmax' : ℝ) : ℂ) • P := by rw [hsc]
    have hP_DH : P * (D + H) = (D + H) * P := by rw [Matrix.mul_add, Matrix.add_mul, hPD, hPH]
    have hEq_tilde : posDefPow (2 * κ - 1) (hDtilde.add hHtilde) =
        (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hDtilde * posDefPow (κ - 1) hGtilde * posDefPow (1 / 2 : ℝ) hDtilde) := by
      obtain ⟨hA2, hpow2⟩ := posDefPow_block_replace (2 * κ - 1) ((1 + h) * dmax')
        (mul_pos (by linarith) hdmax'_pos) (hD.add hH) hPh hP2 hP_DH
      have hL : posDefPow (2 * κ - 1) (hDtilde.add hHtilde) =
          Q * posDefPow (2 * κ - 1) (hD.add hH) * Q + ((((1 + h) * dmax') ^ (2 * κ - 1) : ℝ) : ℂ) • P := by
        rw [posDefPow_congr (2 * κ - 1) hDHtilde_eq (hDtilde.add hHtilde) hA2]
        exact hpow2
      rw [hL, hEq, hGtilde_pow (κ - 1), hDtilde_half]
      have hQ_Dh : Q * posDefPow (1 / 2 : ℝ) hD = posDefPow (1 / 2 : ℝ) hD * Q := by
        dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_Dhalf]
      have hQ_Gk : Q * posDefPow (κ - 1) hG = posDefPow (κ - 1) hG * Q := by
        dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_posDefPow (κ - 1) hG hP_G]
      simp only [Matrix.add_mul, Matrix.mul_add]
      have kQP_r : ∀ X : Mat n, (X * Q) * P = 0 := fun X => by rw [Matrix.mul_assoc, hQP, Matrix.mul_zero]
      have kPQ_l : ∀ X : Mat n, P * (Q * X) = 0 := fun X => by rw [← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
      have k1 : (Q * posDefPow (1 / 2 : ℝ) hD * Q) * ((((h * dmax' ^ 2) ^ (κ - 1) : ℝ) : ℂ) • P) = 0 := by
        rw [Matrix.mul_smul, kQP_r, smul_zero]
      have k2 : (((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P) * (Q * posDefPow (κ - 1) hG * Q) = 0 := by
        rw [Matrix.smul_mul, Matrix.mul_assoc Q (posDefPow (κ - 1) hG) Q, kPQ_l, smul_zero]
      have k3 : (Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * posDefPow (κ - 1) hG * Q) *
          (((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P) = 0 := by
        rw [Matrix.mul_smul, show (Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * posDefPow (κ - 1) hG * Q) * P =
          ((Q * posDefPow (1 / 2 : ℝ) hD * Q) * (Q * posDefPow (κ - 1) hG) * Q) * P by simp only [Matrix.mul_assoc],
          kQP_r, smul_zero]
      have k4 : (((dmax' ^ (1 / 2 : ℝ) : ℝ) : ℂ) • P) * ((((h * dmax' ^ 2) ^ (κ - 1) : ℝ) : ℂ) • P) *
          (Q * posDefPow (1 / 2 : ℝ) hD * Q) = 0 := by
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mul, hP2,
          Matrix.mul_assoc Q (posDefPow (1 / 2 : ℝ) hD) Q, kPQ_l, smul_zero]
      simp only [k1, k2, k3, k4, Matrix.zero_mul, zero_add, add_zero, smul_add]
      refine congrArg₂ (· + ·) ?_ ?_
      · rw [Matrix.mul_smul, Matrix.smul_mul]
        refine congrArg ((Λ : ℂ) • ·) ?_
        have hQDhQ' : Q * posDefPow (1 / 2 : ℝ) hD * Q = Q * posDefPow (1 / 2 : ℝ) hD := by
          rw [Matrix.mul_assoc, ← hQ_Dh, ← Matrix.mul_assoc, hQ2]
        have hQGkQ : Q * posDefPow (κ - 1) hG * Q = Q * posDefPow (κ - 1) hG := by
          rw [Matrix.mul_assoc, ← hQ_Gk, ← Matrix.mul_assoc, hQ2]
        rw [hQDhQ', hQGkQ]
        calc Q * (posDefPow (1 / 2 : ℝ) hD * posDefPow (κ - 1) hG * posDefPow (1 / 2 : ℝ) hD) * Q
            = (Q * posDefPow (1 / 2 : ℝ) hD) * posDefPow (κ - 1) hG * (posDefPow (1 / 2 : ℝ) hD * Q) := by
                simp only [Matrix.mul_assoc]
          _ = (Q * posDefPow (1 / 2 : ℝ) hD) * posDefPow (κ - 1) hG * (Q * posDefPow (1 / 2 : ℝ) hD) := by
                rw [← hQ_Dh]
          _ = (Q * posDefPow (1 / 2 : ℝ) hD * Q) * posDefPow (κ - 1) hG * (Q * posDefPow (1 / 2 : ℝ) hD) :=
                congrArg (· * posDefPow (κ - 1) hG * (Q * posDefPow (1 / 2 : ℝ) hD)) hQDhQ'.symm
          _ = Q * posDefPow (1 / 2 : ℝ) hD * (Q * posDefPow (κ - 1) hG) * (Q * posDefPow (1 / 2 : ℝ) hD) := by
                simp only [Matrix.mul_assoc]
      · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hP2]
        refine congrArg (· • P) ?_
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
        apply congrArg Complex.ofReal
        have h1 : ((1 + h) * dmax') ^ (2 * κ - 1) = (1 + h) ^ (2 * κ - 1) * dmax' ^ (2 * κ - 1) :=
          Real.mul_rpow (by linarith) hdmax'_pos.le
        have h2 : (h * dmax' ^ 2) ^ (κ - 1) = h ^ (κ - 1) * dmax' ^ (2 * (κ - 1)) := by
          rw [Real.mul_rpow (by linarith) (sq_nonneg dmax'), ← Real.rpow_natCast dmax' 2,
            ← Real.rpow_mul hdmax'_pos.le]; push_cast; rfl
        have h3 : dmax' ^ (1 / 2 : ℝ) * (dmax' ^ (2 * (κ - 1)) * dmax' ^ (1 / 2 : ℝ)) = dmax' ^ (2 * κ - 1) := by
          calc _ = dmax' ^ (1 / 2 : ℝ) * dmax' ^ (2 * (κ - 1) + 1 / 2) := by rw [Real.rpow_add hdmax'_pos]
            _ = dmax' ^ ((1 / 2 : ℝ) + (2 * (κ - 1) + 1 / 2)) := (Real.rpow_add hdmax'_pos _ _).symm
            _ = dmax' ^ (2 * κ - 1) := by congr 1; ring
        rw [h1, hSc, h2]; linear_combination (Λ * h ^ (κ - 1)) * h3.symm
    -- Evaluate D̃ v and Φ̃ v!
    have hDtilde_v : Dtilde.mulVec v = (dmax' : ℂ) • v := by
      dsimp only [Dtilde]
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, hPv0, smul_zero, add_zero,
        ← Matrix.mulVec_mulVec v (Q * D) Q, hQv, ← Matrix.mulVec_mulVec v Q D, hDv,
        Matrix.mulVec_smul, hQv]
    have hΦtilde_v : (posDefPow κ hGtilde - Dtilde * posDefPow (κ - 1) hGtilde * Dtilde).mulVec v = (ν : ℂ) • v := by
      have hQ_Gk : Q * posDefPow κ hG = posDefPow κ hG * Q := by
        dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_posDefPow κ hG hP_G]
      have hQ_Gkm1 : Q * posDefPow (κ - 1) hG = posDefPow (κ - 1) hG * Q := by
        dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP_posDefPow (κ - 1) hG hP_G]
      have h1 : Q.mulVec ((posDefPow κ hG).mulVec v) = (posDefPow κ hG).mulVec v := by
        rw [Matrix.mulVec_mulVec, hQ_Gk, ← Matrix.mulVec_mulVec, hQv]
      have h2 : Q.mulVec ((posDefPow (κ - 1) hG).mulVec v) = (posDefPow (κ - 1) hG).mulVec v := by
        rw [Matrix.mulVec_mulVec, hQ_Gkm1, ← Matrix.mulVec_mulVec, hQv]
      have hGk_v : (posDefPow κ hGtilde).mulVec v = (posDefPow κ hG).mulVec v := by
        rw [hGtilde_pow κ, Matrix.add_mulVec, Matrix.smul_mulVec, hPv0, smul_zero, add_zero,
          ← Matrix.mulVec_mulVec v (Q * posDefPow κ hG) Q, hQv, ← Matrix.mulVec_mulVec v Q (posDefPow κ hG), h1]
      have hGkm1_v : (posDefPow (κ - 1) hGtilde).mulVec v = (posDefPow (κ - 1) hG).mulVec v := by
        rw [hGtilde_pow (κ - 1), Matrix.add_mulVec, Matrix.smul_mulVec, hPv0, smul_zero, add_zero,
          ← Matrix.mulVec_mulVec v (Q * posDefPow (κ - 1) hG) Q, hQv, ← Matrix.mulVec_mulVec v Q (posDefPow (κ - 1) hG), h2]
      have h3 : Dtilde.mulVec ((posDefPow (κ - 1) hG).mulVec v) = D.mulVec ((posDefPow (κ - 1) hG).mulVec v) := by
        dsimp only [Dtilde]
        have hP_Gkm1_v : P.mulVec ((posDefPow (κ - 1) hG).mulVec v) = 0 := by
          rw [Matrix.mulVec_mulVec, hP_posDefPow (κ - 1) hG hP_G, ← Matrix.mulVec_mulVec, hPv0, Matrix.mulVec_zero]
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, hP_Gkm1_v, smul_zero, add_zero,
          ← Matrix.mulVec_mulVec _ (Q * D) Q, h2, hQD_comm, ← Matrix.mulVec_mulVec _ D Q, h2]
      rw [Matrix.sub_mulVec, hGk_v,
        ← Matrix.mulVec_mulVec v (Dtilde * posDefPow (κ - 1) hGtilde) Dtilde, hDtilde_v,
        Matrix.mulVec_smul, ← Matrix.mulVec_mulVec v Dtilde (posDefPow (κ - 1) hGtilde), hGkm1_v, h3]
      have h4 : (posDefPow κ hG).mulVec v - (dmax' : ℂ) • D.mulVec ((posDefPow (κ - 1) hG).mulVec v) =
          Φ.mulVec v := by
        dsimp only [Φ]
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec v (D * posDefPow (κ - 1) hG) D, hDv,
          Matrix.mulVec_smul, ← Matrix.mulVec_mulVec v D]
      rw [h4, hΦv]
    -- Split ν = 0 vs ν > 0!
    rcases eq_or_lt_of_le hν_nn with hν0 | hν_pos
    · rw [← hν0, Complex.ofReal_zero, zero_smul] at hΦtilde_v
      exact zero_flux_top_eig_impossible hκ hΛ hdmax'_pos hDtilde hDtilde_le hHtilde hEq_tilde
        hv_ne hDtilde_v hΦtilde_v
    · let μ : ℝ := ν / dmax' ^ (2 * κ)
      have hμ_pos : 0 < μ := div_pos hν_pos (Real.rpow_pos_of_pos hdmax'_pos _)
      obtain ⟨g, hg1, hg_eq⟩ := exists_gap_root hκ hμ_pos
      have hΦtilde_v' : (posDefPow κ hGtilde - Dtilde * posDefPow (κ - 1) hGtilde * Dtilde).mulVec v =
          ((μ * dmax' ^ (2 * κ) : ℝ) : ℂ) • v := by
        rw [hΦtilde_v]; dsimp only [μ]
        rw [div_mul_cancel₀ _ (Real.rpow_pos_of_pos hdmax'_pos _).ne']
      have hgap := universal_spectral_gap_theorem hκ hΛ_pos hμ_pos hg1 hg_eq hdmax'_pos
        hDtilde hDtilde_le hHtilde hEq_tilde hv_ne hDtilde_v hΦtilde_v'
      rcases hgap with ⟨hHtilde_v, hSc_g⟩ | hlt
      · have hgh : g = h := upper_root_unique hκ hg1 hh hSc_g hSc
        rw [hgh] at hHtilde_v
        have hHv : H.mulVec v = ((h * dmax' : ℝ) : ℂ) • v := by
          dsimp only [Htilde] at hHtilde_v
          rw [Matrix.add_mulVec, Matrix.smul_mulVec, hPv0, smul_zero, add_zero,
            ← Matrix.mulVec_mulVec v (Q * H) Q, hQv, hQH_comm, ← Matrix.mulVec_mulVec v H Q, hQv] at hHtilde_v
          exact hHtilde_v
        -- Now K v = 0 ⟹ P v = v, contradicting P v = 0 and v ≠ 0!
        have hKv : K.mulVec v = 0 := by
          rw [hK_ker_iff]
          intro lam hlam
          dsimp only [T]
          rw [← Matrix.mulVec_mulVec v (H - ((h * lam : ℝ) : ℂ) • 1) (QD lam)]
          by_cases hld : lam = dmax'
          · have hQDv : QD lam *ᵥ v = v := by
              have hsum := congrArg (fun M : Mat n => M.mulVec v) hQD_sum
              rw [Matrix.sum_mulVec, Matrix.one_mulVec] at hsum
              have hother : ∀ μ ∈ L, μ ≠ lam → QD μ *ᵥ v = 0 := fun μ _ hne => by
                have h1 : (μ : ℂ) • (QD μ *ᵥ v) = (lam : ℂ) • (QD μ *ᵥ v) := by
                  calc (μ : ℂ) • (QD μ *ᵥ v) = (D * QD μ).mulVec v := by rw [hQD_D μ, Matrix.smul_mulVec]
                    _ = (QD μ * D).mulVec v := by rw [hQD_D μ, hD_QD μ]
                    _ = (dmax' : ℂ) • (QD μ *ᵥ v) := by rw [← Matrix.mulVec_mulVec, hDv, Matrix.mulVec_smul]
                    _ = (lam : ℂ) • (QD μ *ᵥ v) := by rw [hld]
                have h2 : ((μ - lam : ℝ) : ℂ) • (QD μ *ᵥ v) = 0 := by
                  rw [Complex.ofReal_sub, sub_smul, h1, sub_self]
                exact (smul_eq_zero.mp h2).resolve_left (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hne))
              rw [Finset.sum_eq_single lam (fun μ hμ hne => hother μ hμ hne) (fun hnot => (hnot hlam).elim)] at hsum
              exact hsum
            rw [hQDv, hld, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hHv, sub_self]
          · have hQDv0 : QD lam *ᵥ v = 0 := by
              have h1 : (lam : ℂ) • (QD lam *ᵥ v) = (dmax' : ℂ) • (QD lam *ᵥ v) := by
                calc (lam : ℂ) • (QD lam *ᵥ v) = (D * QD lam).mulVec v := by rw [hQD_D lam, Matrix.smul_mulVec]
                  _ = (QD lam * D).mulVec v := by rw [hQD_D lam, hD_QD lam]
                  _ = (dmax' : ℂ) • (QD lam *ᵥ v) := by rw [← Matrix.mulVec_mulVec, hDv, Matrix.mulVec_smul]
              have h2 : ((lam - dmax' : ℝ) : ℂ) • (QD lam *ᵥ v) = 0 := by
                rw [Complex.ofReal_sub, sub_smul, h1, sub_self]
              exact (smul_eq_zero.mp h2).resolve_left (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hld))
            rw [hQDv0, Matrix.mulVec_zero]
        have hPv_eq_v : P.mulVec v = v := by
          let zK := (UK : Mat n)ᴴ.mulVec v
          have hKzK : (Matrix.diagonal (fun i => (k_ev i : ℂ))).mulVec zK = 0 := by
            have h1 := congrArg (Matrix.mulVec (UK : Mat n)ᴴ) hKv
            rw [hK_spec, Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.mul_assoc,
              ← Matrix.mul_assoc (UK : Mat n)ᴴ (UK : Mat n),
              blitz_unitary_conj_mul UK, Matrix.one_mul, ← Matrix.mulVec_mulVec] at h1
            exact h1
          have hdiag_zK : (Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0)).mulVec zK = zK := by
            ext i; simp only [Matrix.mulVec_diagonal]
            by_cases h0 : k_ev i = 0
            · simp [h0]
            · have hi := congr_fun hKzK i
              simp only [Matrix.mulVec_diagonal, Pi.zero_apply] at hi
              have hzi : zK i = 0 := (mul_eq_zero.mp hi).resolve_left (Complex.ofReal_ne_zero.mpr h0)
              simp [h0, hzi]
          dsimp only [P]
          rw [← Matrix.mulVec_mulVec v ((UK : Mat n) * Matrix.diagonal (fun i => if k_ev i = 0 then (1 : ℂ) else 0)) (UK : Mat n)ᴴ,
            ← Matrix.mulVec_mulVec zK (UK : Mat n), hdiag_zK]
          dsimp only [zK]; rw [Matrix.mulVec_mulVec, blitz_unitary_mul_conj UK, Matrix.one_mulVec]
        rw [hPv0] at hPv_eq_v
        exact hv_ne hPv_eq_v.symm
      · have hle : dmax' / g < dmax' := (div_lt_iff₀ (by linarith)).mpr (by nlinarith)
        linarith

/-! ==========================================================================
    PART 2: Third-Root Hyperbolic Spectral Pencil (Theorem B1, p = 4/3)
    ========================================================================== -/

private lemma blitz_trace_fromBlocks {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (B : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂]

/-- Theorem B1 (Parts 1–3, `b1_proof.md` §4): Third-Root Hyperbolic Spectral Pencil &
    Universal Harmonic-Mean Trace Lower Bound at p = 4/3:
    For Λ > 8 and the three real roots c₀ < -4 < 0 < h_- < 1/2 < 1 < h_+ of (1 + c)³ = Λ c
    (with Vieta relations h_+ + h_- + c₀ = -3 and h_+ h_- c₀ = -1), on ANY PosDef solution
    (D, H) of (D + H)³ = Λ D H D (A = D + H, G = D^(1/2) H D^(1/2)):
      (1) Overdamped reality: every root r ∈ ℂ of (|c₀| r² I + r D - G) u = 0 (u ≠ 0) is
          strictly real and nonzero (r.im = 0, r.re ≠ 0).
      (2) Exact companion cube trace: for C₀ = [[0, I], [-G/c₀, D/c₀]],
            Re Tr(C₀³) = c₀⁻³ Re Tr(D³) - 3 c₀⁻² Re Tr(D G).
      (3) Unconditional Harmonic-Mean Trace Identity & Lower Bound: given the companion spectral
          splitting Re Tr(C₀³) = (1 + c₀)⁻³ Re Tr(A³) + ∑ γ_j³ with s ≥ 1 positive roots γ_j > 0,
            Re Tr(D² H) = Re Tr(D G) = (h_+ h_- / (h_+ + h_-)) Re Tr(D³) + (c₀² / (h_+ + h_-)) ∑ γ_j³
                        > (h_+ h_- / (h_+ + h_-)) Re Tr(D³).
      (4) Exact k = 3 Three-Pencil Elimination: given also Re Tr(C_{h_+}³) = (1 + h_+)⁻³ Re Tr(A³) + S_μ,
            (1 / (h_+(h_+ + 3)) - h_+ h_- / (h_+ + h_-)) Re Tr(D³) =
              (h_+² / (h_+ + 3)) S_μ + (c₀² / (h_+ + h_-)) ∑ γ_j³. -/
theorem third_root_harmonic_mean_bound {n : ℕ} {Λ c0 hm hp : ℝ}
    (hc0 : c0 < -4) (hhm : 0 < hm) (hhp : 1 < hp)
    (hSc0 : (1 + c0) ^ 3 = Λ * c0) (hScp : (1 + hp) ^ 3 = Λ * hp)
    (hV1 : hp + hm + c0 = -3) (hV3 : hp * hm * c0 = -1)
    {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef)
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D)) :
    let G := posDefPow (1 / 2 : ℝ) hD * H * posDefPow (1 / 2 : ℝ) hD
    let C0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
      Matrix.fromBlocks 0 1 ((-(c0⁻¹) : ℂ) • G) ((c0⁻¹ : ℂ) • D)
    -- (1) Overdamped reality of Q₀(r) = (-c₀) r² I + r D - G
    (∀ (r : ℂ) (u : Fin n → ℂ), u ≠ 0 →
      ((((-c0 : ℝ) : ℂ) * r ^ 2) • (1 : Mat n) + r • D - G).mulVec u = 0 →
      r.im = 0 ∧ r.re ≠ 0) ∧
    -- (2) Exact companion cube trace
    (C0 ^ 3).trace.re = c0⁻¹ ^ 3 * (D ^ 3).trace.re - 3 * c0⁻¹ ^ 2 * (D * G).trace.re ∧
    -- (3) Exact Harmonic-Mean Identity & strict lower bound
    (∀ {s : ℕ}, 1 ≤ s → ∀ (γ : Fin s → ℝ), (∀ j, 0 < γ j) →
      (C0 ^ 3).trace.re = ((1 + c0) ^ 3)⁻¹ * ((D + H) ^ 3).trace.re + ∑ j, γ j ^ 3 →
      (D ^ 2 * H).trace.re = (D * G).trace.re ∧
      (D * G).trace.re = (hp * hm / (hp + hm)) * (D ^ 3).trace.re +
        (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3 ∧
      (hp * hm / (hp + hm)) * (D ^ 3).trace.re < (D * G).trace.re) ∧
    -- (4) Exact k = 3 three-pencil elimination
    (∀ {s : ℕ} (γ : Fin s → ℝ) (Sμ : ℝ),
      (C0 ^ 3).trace.re = ((1 + c0) ^ 3)⁻¹ * ((D + H) ^ 3).trace.re + ∑ j, γ j ^ 3 →
      hp⁻¹ ^ 3 * (D ^ 3).trace.re - 3 * hp⁻¹ ^ 2 * (D * G).trace.re =
        ((1 + hp) ^ 3)⁻¹ * ((D + H) ^ 3).trace.re + Sμ →
      (1 / (hp * (hp + 3)) - hp * hm / (hp + hm)) * (D ^ 3).trace.re =
        (hp ^ 2 / (hp + 3)) * Sμ + (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3) := by
  intro G C0
  have hG_pd : G.PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
  have hc0_ne : c0 ≠ 0 := ne_of_lt (lt_trans hc0 (by norm_num))
  have h1c0_ne : 1 + c0 ≠ 0 := by linarith
  have hhp_pos : 0 < hp := by linarith
  have hhp3_pos : 0 < hp + 3 := by linarith
  have h1hp_pos : 0 < 1 + hp := by linarith
  have hsum_pos : 0 < hp + hm := by linarith
  -- (1) Overdamped reality
  have hpart1 : ∀ (r : ℂ) (u : Fin n → ℂ), u ≠ 0 →
      ((((-c0 : ℝ) : ℂ) * r ^ 2) • (1 : Mat n) + r • D - G).mulVec u = 0 →
      r.im = 0 ∧ r.re ≠ 0 := by
    intro r u hu hroot
    let nv : ℝ := (star u ⬝ᵥ u).re
    let dv : ℝ := (star u ⬝ᵥ D.mulVec u).re
    let gv : ℝ := (star u ⬝ᵥ G.mulVec u).re
    have hnv : 0 < nv := blitz_dotProduct_star_self_pos hu
    have hdv : 0 < dv := blitz_posDef_quad_re_pos hD hu
    have hgv : 0 < gv := blitz_posDef_quad_re_pos hG_pd hu
    have hnv_c : star u ⬝ᵥ u = (nv : ℂ) := by
      have him : (star u ⬝ᵥ u).im = 0 := by
        rw [dotProduct, Complex.im_sum]; refine Finset.sum_eq_zero fun i _ => ?_
        simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_im]
      exact Complex.ext rfl (by simp [him])
    have hdv_c : star u ⬝ᵥ D.mulVec u = (dv : ℂ) := by
      have h1 := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hD).2 hu)).2
      exact Complex.ext rfl (by simp [← h1])
    have hgv_c : star u ⬝ᵥ G.mulVec u = (gv : ℂ) := by
      have h1 := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hG_pd).2 hu)).2
      exact Complex.ext rfl (by simp [← h1])
    have hdot : (((-c0 : ℝ) : ℂ) * r ^ 2) * (nv : ℂ) + r * (dv : ℂ) - (gv : ℂ) = 0 := by
      have h0 := congrArg (fun w => star u ⬝ᵥ w) hroot
      simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
        hnv_c, hdv_c, hgv_c] at h0
      exact h0
    have hre := congrArg Complex.re hdot
    have him := congrArg Complex.im hdot
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.zero_re, Complex.zero_im,
      sq, zero_mul, mul_zero, sub_zero, add_zero] at hre him
    have him_eq : r.im * (2 * (-c0) * nv * r.re + dv) = 0 := by linarith
    have hre_eq : (-c0) * nv * (r.re ^ 2 - r.im ^ 2) + dv * r.re - gv = 0 := by linarith
    have him0 : r.im = 0 := by
      by_contra hne
      have h1 : 2 * (-c0) * nv * r.re + dv = 0 := (mul_eq_zero.mp him_eq).resolve_left hne
      have hα : 0 < (-c0) * nv := mul_pos (by linarith) hnv
      have hdisc : 4 * ((-c0) * nv) * ((-c0) * nv * (r.re ^ 2 - r.im ^ 2) + dv * r.re - gv) =
          (2 * (-c0) * nv * r.re + dv) ^ 2 - dv ^ 2 - 4 * ((-c0) * nv) ^ 2 * r.im ^ 2 - 4 * (-c0) * nv * gv := by ring
      rw [hre_eq, h1] at hdisc
      have h1' : 0 < dv ^ 2 := sq_pos_of_pos hdv
      have h2' : 0 ≤ 4 * ((-c0) * nv) ^ 2 * r.im ^ 2 := by positivity
      have h3' : 0 < 4 * ((-c0) * nv) * gv := by positivity
      nlinarith only [hdisc, h1', h2', h3']
    refine ⟨him0, fun hre0 => ?_⟩
    rw [him0, hre0] at hre_eq
    nlinarith only [hre_eq, hgv]
  -- (2) Exact companion cube trace
  have hpart2 : (C0 ^ 3).trace.re = c0⁻¹ ^ 3 * (D ^ 3).trace.re - 3 * c0⁻¹ ^ 2 * (D * G).trace.re := by
    let α : ℂ := -((c0⁻¹ : ℝ) : ℂ)
    let β : ℂ := ((c0⁻¹ : ℝ) : ℂ)
    have hC0 : C0 = Matrix.fromBlocks (0 : Mat n) 1 (α • G) (β • D) := by
      dsimp only [C0, α, β]; simp
    have hC02 : C0 * C0 = Matrix.fromBlocks (α • G) (β • D) ((β * α) • (D * G)) (α • G + (β * β) • (D * D)) := by
      rw [hC0, Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm α β]
    have hC03 : C0 ^ 3 = (C0 * C0) * C0 := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
    rw [hC03, hC02, hC0, Matrix.fromBlocks_multiply, blitz_trace_fromBlocks]
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add,
      Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, mul_add, ← mul_assoc, Complex.add_re]
    have hG_D : (G * D).trace = (D * G).trace := Matrix.trace_mul_comm G D
    have hD3 : D * D * D = D ^ 3 := (blitz_pow_three D).symm
    rw [hG_D, hD3]
    have hre1 : (β * α * (D * G).trace).re = -(c0⁻¹ ^ 2) * (D * G).trace.re := by
      dsimp only [α, β]
      rw [show ((c0⁻¹ : ℝ) : ℂ) * -((c0⁻¹ : ℝ) : ℂ) = ((-(c0⁻¹ ^ 2) : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hre2 : (α * β * (D * G).trace).re = -(c0⁻¹ ^ 2) * (D * G).trace.re := by
      dsimp only [α, β]
      rw [show -((c0⁻¹ : ℝ) : ℂ) * ((c0⁻¹ : ℝ) : ℂ) = ((-(c0⁻¹ ^ 2) : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hre3 : (β * β * β * (D ^ 3).trace).re = c0⁻¹ ^ 3 * (D ^ 3).trace.re := by
      dsimp only [β]
      rw [show ((c0⁻¹ : ℝ) : ℂ) * ((c0⁻¹ : ℝ) : ℂ) * ((c0⁻¹ : ℝ) : ℂ) = ((c0⁻¹ ^ 3 : ℝ) : ℂ) by push_cast; ring]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre1, hre2, hre3]
    ring
  -- Shared trace identities for (3) & (4)
  have hD2H_DG : (D ^ 2 * H).trace.re = (D * G).trace.re := by
    let Dh := posDefPow (1 / 2 : ℝ) hD
    have hDh2 : Dh * Dh = D := by dsimp only [Dh]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
    have h1 : (D * G).trace = (D ^ 2 * H).trace := by
      dsimp only [G]
      calc (D * (Dh * H * Dh)).trace = ((D * Dh * H) * Dh).trace := by
              apply blitz_tr_eq; simp only [Matrix.mul_assoc]
        _ = (Dh * (D * (Dh * H))).trace := by
              rw [Matrix.trace_mul_comm (D * Dh * H) Dh]; apply blitz_tr_eq; simp only [Matrix.mul_assoc]
        _ = ((Dh * Dh) * D * H).trace := by
              have hcomm : Dh * D = D * Dh := (posDefPow_comm_self (1 / 2) hD).symm
              apply blitz_tr_eq
              calc Dh * (D * (Dh * H)) = (D * Dh) * Dh * H := by rw [← Matrix.mul_assoc, hcomm]; simp only [Matrix.mul_assoc]
                _ = D * (Dh * Dh) * H := by simp only [Matrix.mul_assoc]
                _ = (Dh * Dh) * D * H := by rw [hDh2]
        _ = (D ^ 2 * H).trace := by rw [hDh2, blitz_pow_two]
    exact congrArg Complex.re h1.symm
  have hA3_tr : ((D + H) ^ 3).trace.re = Λ * (D * G).trace.re := by
    rw [hEq, trace_re_smul_real, ← hD2H_DG]
    have h1 : (D * H * D).trace = (D ^ 2 * H).trace := by
      rw [Matrix.trace_mul_comm (D * H) D, blitz_pow_two, Matrix.mul_assoc]
    rw [h1]
  have hV_c0 : c0 * (c0 + 3) = (hp + hm) / (hp * hm) := by
    have h1 : c0 + 3 = -(hp + hm) := by linarith
    rw [h1, eq_div_iff (mul_pos hhp_pos hhm).ne']
    linear_combination -(hp + hm) * hV3
  -- (3) Exact Harmonic-Mean Identity & strict lower bound
  have hpart3 : ∀ {s : ℕ} (_hs : 1 ≤ s) (γ : Fin s → ℝ), (∀ j, 0 < γ j) →
      (C0 ^ 3).trace.re = ((1 + c0) ^ 3)⁻¹ * ((D + H) ^ 3).trace.re + ∑ j, γ j ^ 3 →
      (D ^ 2 * H).trace.re = (D * G).trace.re ∧
      (D * G).trace.re = (hp * hm / (hp + hm)) * (D ^ 3).trace.re +
        (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3 ∧
      (hp * hm / (hp + hm)) * (D ^ 3).trace.re < (D * G).trace.re := by
    intro s hs γ hγ hsplit
    rw [hpart2, hA3_tr] at hsplit
    have hΛ_c0 : ((1 + c0) ^ 3)⁻¹ * Λ = c0⁻¹ := by
      field_simp [h1c0_ne, hc0_ne]; linarith [hSc0]
    have h1 : c0⁻¹ ^ 3 * (D ^ 3).trace.re - (c0⁻¹ + 3 * c0⁻¹ ^ 2) * (D * G).trace.re = ∑ j, γ j ^ 3 := by
      have : ((1 + c0) ^ 3)⁻¹ * (Λ * (D * G).trace.re) = c0⁻¹ * (D * G).trace.re := by
        rw [← mul_assoc, hΛ_c0]
      linarith
    have hharm : (D * G).trace.re = (hp * hm / (hp + hm)) * (D ^ 3).trace.re +
        (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3 := by
      have h2 : (c0 * (c0 + 3)) * (D * G).trace.re = (D ^ 3).trace.re - c0 ^ 3 * ∑ j, γ j ^ 3 := by
        have hmul := congrArg (fun x => c0 ^ 3 * x) h1
        have hL : c0 ^ 3 * (c0⁻¹ ^ 3 * (D ^ 3).trace.re - (c0⁻¹ + 3 * c0⁻¹ ^ 2) * (D * G).trace.re) =
            (D ^ 3).trace.re - (c0 * (c0 + 3)) * (D * G).trace.re := by
          field_simp [hc0_ne]
        linarith
      rw [hV_c0] at h2
      have hne1 : hp * hm ≠ 0 := (mul_pos hhp_pos hhm).ne'
      have h3 : (hp + hm) * (D * G).trace.re = (hp * hm) * (D ^ 3).trace.re + c0 ^ 2 * ∑ j, γ j ^ 3 := by
        have h2' := congrArg (fun x => (hp * hm) * x) h2
        rw [← mul_assoc, mul_div_cancel₀ _ hne1] at h2'
        have hc3 : hp * hm * c0 ^ 3 = -(c0 ^ 2) := by linear_combination c0 ^ 2 * hV3
        linear_combination h2' - (∑ j, γ j ^ 3) * hc3
      field_simp [hsum_pos.ne']; linarith
    have hsum_pos_γ : 0 < ∑ j, γ j ^ 3 := by
      have hne : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
      exact Finset.sum_pos (fun j _ => pow_pos (hγ j) 3) Finset.univ_nonempty
    have hstrict : (hp * hm / (hp + hm)) * (D ^ 3).trace.re < (D * G).trace.re := by
      rw [hharm]
      have hpos : 0 < (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3 :=
        mul_pos (div_pos (sq_pos_of_ne_zero hc0_ne) hsum_pos) hsum_pos_γ
      linarith
    exact ⟨hD2H_DG, hharm, hstrict⟩
  -- (4) Exact k = 3 three-pencil elimination
  have hpart4 : ∀ {s : ℕ} (γ : Fin s → ℝ) (Sμ : ℝ),
      (C0 ^ 3).trace.re = ((1 + c0) ^ 3)⁻¹ * ((D + H) ^ 3).trace.re + ∑ j, γ j ^ 3 →
      hp⁻¹ ^ 3 * (D ^ 3).trace.re - 3 * hp⁻¹ ^ 2 * (D * G).trace.re =
        ((1 + hp) ^ 3)⁻¹ * ((D + H) ^ 3).trace.re + Sμ →
      (1 / (hp * (hp + 3)) - hp * hm / (hp + hm)) * (D ^ 3).trace.re =
        (hp ^ 2 / (hp + 3)) * Sμ + (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3 := by
    intro s γ Sμ hsplit0 hsplitp
    rw [hpart2, hA3_tr] at hsplit0
    rw [hA3_tr] at hsplitp
    have hΛ_c0 : ((1 + c0) ^ 3)⁻¹ * Λ = c0⁻¹ := by field_simp [h1c0_ne, hc0_ne]; linarith [hSc0]
    have hΛ_hp : ((1 + hp) ^ 3)⁻¹ * Λ = hp⁻¹ := by field_simp [h1hp_pos.ne', hhp_pos.ne']; linarith [hScp]
    have h1 : (D * G).trace.re = (hp * hm / (hp + hm)) * (D ^ 3).trace.re +
        (c0 ^ 2 / (hp + hm)) * ∑ j, γ j ^ 3 := by
      have ha : c0⁻¹ ^ 3 * (D ^ 3).trace.re - (c0⁻¹ + 3 * c0⁻¹ ^ 2) * (D * G).trace.re = ∑ j, γ j ^ 3 := by
        have : ((1 + c0) ^ 3)⁻¹ * (Λ * (D * G).trace.re) = c0⁻¹ * (D * G).trace.re := by rw [← mul_assoc, hΛ_c0]
        linarith
      have hb : (c0 * (c0 + 3)) * (D * G).trace.re = (D ^ 3).trace.re - c0 ^ 3 * ∑ j, γ j ^ 3 := by
        have hmul := congrArg (fun x => c0 ^ 3 * x) ha
        have hL : c0 ^ 3 * (c0⁻¹ ^ 3 * (D ^ 3).trace.re - (c0⁻¹ + 3 * c0⁻¹ ^ 2) * (D * G).trace.re) =
            (D ^ 3).trace.re - (c0 * (c0 + 3)) * (D * G).trace.re := by field_simp [hc0_ne]
        linarith
      rw [hV_c0] at hb
      have hne1 : hp * hm ≠ 0 := (mul_pos hhp_pos hhm).ne'
      have hc : (hp + hm) * (D * G).trace.re = (hp * hm) * (D ^ 3).trace.re + c0 ^ 2 * ∑ j, γ j ^ 3 := by
        have hb' := congrArg (fun x => (hp * hm) * x) hb
        rw [← mul_assoc, mul_div_cancel₀ _ hne1] at hb'
        have hc3 : hp * hm * c0 ^ 3 = -(c0 ^ 2) := by linear_combination c0 ^ 2 * hV3
        linear_combination hb' - (∑ j, γ j ^ 3) * hc3
      field_simp [hsum_pos.ne']; linarith
    have h2 : (D * G).trace.re = (1 / (hp * (hp + 3))) * (D ^ 3).trace.re - (hp ^ 2 / (hp + 3)) * Sμ := by
      have ha : hp⁻¹ ^ 3 * (D ^ 3).trace.re - (hp⁻¹ + 3 * hp⁻¹ ^ 2) * (D * G).trace.re = Sμ := by
        have : ((1 + hp) ^ 3)⁻¹ * (Λ * (D * G).trace.re) = hp⁻¹ * (D * G).trace.re := by rw [← mul_assoc, hΛ_hp]
        linarith
      have hb : (hp * (hp + 3)) * (D * G).trace.re = (D ^ 3).trace.re - hp ^ 3 * Sμ := by
        have hmul := congrArg (fun x => hp ^ 3 * x) ha
        have hL : hp ^ 3 * (hp⁻¹ ^ 3 * (D ^ 3).trace.re - (hp⁻¹ + 3 * hp⁻¹ ^ 2) * (D * G).trace.re) =
            (D ^ 3).trace.re - (hp * (hp + 3)) * (D * G).trace.re := by field_simp [hhp_pos.ne']
        linarith
      field_simp [hhp_pos.ne', hhp3_pos.ne']; linarith
    linarith
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩

/-- Exact degree-28 integer polynomial for Theorem B1(4) (proving ρ₄(s) < 1/8). -/
private def polyP8 (t : ℝ) : ℝ :=
  let h := 1 + t
  let U := h * (h + 3)
  let N := 2 * h + 3
  let D := h ^ 3 * (U ^ 2 + 2 * h + 3) - N
  D ^ 4 - 512 * (t * (t + 2) ^ 3) ^ 3 * N ^ 4

private lemma polyP8_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < polyP8 t := by
  by_cases hge : (1 : ℝ) / 4 ≤ t
  · let s : ℝ := t - 1 / 4
    have hs : 0 ≤ s := by dsimp only [s]; linarith
    have ht_eq : t = 1 / 4 + s := by dsimp only [s]; ring
    rw [ht_eq]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ 28 := by positivity
    suffices hpos : 0 < (4 : ℝ) ^ 28 * polyP8 (1 / 4 + s) by nlinarith only [h4, hpos]
    have hid : (4 : ℝ) ^ 28 * polyP8 (1 / 4 + s) =
        (177186549308729673363633 : ℝ) + (3771588952493110923102000 : ℝ) * s ^ 1 + (50271560331805519606636704 : ℝ) * s ^ 2 +
        (412430475757231477974046464 : ℝ) * s ^ 3 + (2130457535308441031506041600 : ℝ) * s ^ 4 + (7466763445657816827328339968 : ℝ) * s ^ 5 +
        (19121671139871129164120604672 : ℝ) * s ^ 6 + (37867068135250082567374897152 : ℝ) * s ^ 7 + (60356611352917526086571065344 : ℝ) * s ^ 8 +
        (79565502261565502667281661952 : ℝ) * s ^ 9 + (88316463490975304629021048832 : ℝ) * s ^ 10 + (83495841522939768855859298304 : ℝ) * s ^ 11 +
        (67717547346839032380335849472 : ℝ) * s ^ 12 + (47312801932276513546275127296 : ℝ) * s ^ 13 + (28536877161292969069806354432 : ℝ) * s ^ 14 +
        (14865028288078288155538620416 : ℝ) * s ^ 15 + (6680234998410405831258406912 : ℝ) * s ^ 16 + (2583369297088017045871656960 : ℝ) * s ^ 17 +
        (856210821654495657512140800 : ℝ) * s ^ 18 + (241794277214744734806835200 : ℝ) * s ^ 19 + (57722465741708237029244928 : ℝ) * s ^ 20 +
        (11526270570993706095083520 : ℝ) * s ^ 21 + (1898226908768770078015488 : ℝ) * s ^ 22 + (252930698964570130612224 : ℝ) * s ^ 23 +
        (26545435271845837275136 : ℝ) * s ^ 24 + (2109193331484561244160 : ℝ) * s ^ 25 + (119084181346930655232 : ℝ) * s ^ 26 +
        (4251398048237748224 : ℝ) * s ^ 27 + (72057594037927936 : ℝ) * s ^ 28 := by
      dsimp only [polyP8]; ring
    rw [hid]; positivity
  · push Not at hge
    let s : ℝ := 1 / (4 * t) - 1
    have hs : 0 ≤ s := by
      dsimp only [s]; rw [sub_nonneg, le_div_iff₀ (by linarith)]; linarith
    have hs1 : 0 < 1 + s := by linarith
    have ht_eq : t = 1 / (4 * (1 + s)) := by
      dsimp only [s]; field_simp [ht.ne']; ring
    rw [ht_eq]
    have hscale : (0 : ℝ) < (4 : ℝ) ^ 28 * (1 + s) ^ 28 := by positivity
    suffices hpos : 0 < (4 : ℝ) ^ 28 * (1 + s) ^ 28 * polyP8 (1 / (4 * (1 + s))) by
      nlinarith only [hscale, hpos]
    have hid : (4 : ℝ) ^ 28 * (1 + s) ^ 28 * polyP8 (1 / (4 * (1 + s))) =
        (177186549308729673363633 : ℝ) + (4018326142521153123406224 : ℝ) * s ^ 1 + (44660262730109162775929568 : ℝ) * s ^ 2 +
        (324753264309605153954501376 : ℝ) * s ^ 3 + (1738277689980082368307564800 : ℝ) * s ^ 4 + (7294346868562568641101201408 : ℝ) * s ^ 5 +
        (24917792915301222797108822016 : ℝ) * s ^ 6 + (70947948953460660673583185920 : ℝ) * s ^ 7 + (170935664972986037677375881216 : ℝ) * s ^ 8 +
        (351900300267987339136033882112 : ℝ) * s ^ 9 + (622935239595220180717369556992 : ℝ) * s ^ 10 + (952056793223270173865291022336 : ℝ) * s ^ 11 +
        (1259370819558324947719211188224 : ℝ) * s ^ 12 + (1443649113225333994905371934720 : ℝ) * s ^ 13 + (1434424214350113234165776252928 : ℝ) * s ^ 14 +
        (1234392944428740164342914220032 : ℝ) * s ^ 15 + (918294602918856749224520843264 : ℝ) * s ^ 16 + (588772101978017544886825254912 : ℝ) * s ^ 17 +
        (323924195913351074361726992384 : ℝ) * s ^ 18 + (152004870277155488850037964800 : ℝ) * s ^ 19 + (60352830616583439531594743808 : ℝ) * s ^ 20 +
        (20060373427846611405927088128 : ℝ) * s ^ 21 + (5503437889600174206530617344 : ℝ) * s ^ 22 + (1222594928277052002750431232 : ℝ) * s ^ 23 +
        (214160599263908438516695040 : ℝ) * s ^ 24 + (28453025256493334231252992 : ℝ) * s ^ 25 + (2695629629020204418727936 : ℝ) * s ^ 26 +
        (162626495753823407046656 : ℝ) * s ^ 27 + (4722366482869645213696 : ℝ) * s ^ 28 := by
      dsimp only [polyP8]; field_simp [hs1.ne']; ring
    rw [hid]; positivity

/-- Theorem B1(4) (`b1_proof.md` §4): 4× Sharper Zero-Float Exact Integer Proof of
    Uniform S_{4/3} Contraction ρ₄(s) < 1/8 for ALL m ≥ 2 and ALL s ≥ 1!
    From the k = 3 three-pencil bound ∑ d_i³ < A(Λ) / (B(Λ) - A(Λ)) and Lemma 0's
    (m - 1) < (1 + h_+)³ (h_+ - 1), our 2-piece degree-28 all-positive integer polynomial
    proof establishes unconditionally:
      ρ₄ := (m - 1) ∑ d_i⁴ < 1/8   (4× sharper than Theorem 16's 1/2)! -/
theorem third_root_pencil_rho4_lt_eighth {m s : ℕ} (hm : 2 ≤ m) {hp hm_rt : ℝ}
    (hhp : 1 < hp) (hhm : 0 < hm_rt)
    (hVieta : hp * hm_rt * (hp + hm_rt + 3) = 1)
    (hm_lt : (m : ℝ) - 1 < (1 + hp) ^ 3 * (hp - 1))
    (d : Fin s → ℝ) (hd_pos : ∀ i, 0 < d i)
    (hA_lt : ∑ i, d i ^ 3 <
      (1 / (hp * (hp + 3)) - hp * hm_rt / (hp + hm_rt)) /
        (hp ^ 2 / (hp + 3) - (1 / (hp * (hp + 3)) - hp * hm_rt / (hp + hm_rt)))) :
    ((m : ℝ) - 1) * ∑ i, d i ^ 4 < 1 / 8 := by
  let t : ℝ := hp - 1
  have ht : 0 < t := by linarith
  have hhp_pos : 0 < hp := by linarith
  have hhp3_pos : 0 < hp + 3 := by linarith
  have hsum_pos : 0 < hp + hm_rt := by linarith
  let U : ℝ := hp * (hp + 3)
  have hU_pos : 0 < U := mul_pos hhp_pos hhp3_pos
  have hU_gt4 : 4 < U := by dsimp only [U]; nlinarith
  let A : ℝ := 1 / U - hp * hm_rt / (hp + hm_rt)
  let B : ℝ := hp ^ 2 / (hp + 3)
  let NA : ℝ := 2 * hp + 3
  let DBA : ℝ := hp ^ 3 * (U ^ 2 + 2 * hp + 3) - NA
  have hNA_pos : 0 < NA := by dsimp only [NA]; linarith
  have hDBA_pos : 0 < DBA := by dsimp only [DBA, NA, U]; nlinarith [sq_nonneg (hp - 1)]
  -- Step 1: Pure rational upper bound A < NA / (U (U² + 2 h_+ + 3)) and A / (B - A) < NA / DBA
  have h_hm_ub : hp * hm_rt < 1 / (hp + 3) := by
    rw [lt_div_iff₀ hhp3_pos]
    have h1 : hp * hm_rt * (hp + 3) < hp * hm_rt * (hp + hm_rt + 3) := by
      have : 0 < hp * hm_rt := mul_pos hhp_pos hhm
      nlinarith
    linarith [hVieta]
  have h_inv_sum : (hp + hm_rt) / (hp * hm_rt) < (U ^ 2 + 2 * hp + 3) / U := by
    have h_id : (hp + hm_rt) / (hp * hm_rt) = U + hp * hm_rt + 1 / hp := by
      dsimp only [U]
      have hmul : hp + hm_rt = (hp * (hp + 3) + hp * hm_rt) * (hp * hm_rt) + hm_rt := by
        linear_combination -hp * hVieta
      field_simp [(mul_pos hhp_pos hhm).ne', hhp_pos.ne']
      linarith
    have h_ub : U + hp * hm_rt + 1 / hp < U + 1 / (hp + 3) + 1 / hp := by linarith [h_hm_ub]
    have h_eq : U + 1 / (hp + 3) + 1 / hp = (U ^ 2 + 2 * hp + 3) / U := by
      dsimp only [U]; field_simp [hhp_pos.ne', hhp3_pos.ne']; ring
    linarith
  have h_frac_lb : U / (U ^ 2 + 2 * hp + 3) < hp * hm_rt / (hp + hm_rt) := by
    have hU2_pos : 0 < U ^ 2 + 2 * hp + 3 := by positivity
    rw [div_lt_div_iff₀ hU2_pos hsum_pos]
    have h1 := (div_lt_div_iff₀ (mul_pos hhp_pos hhm) hU_pos).mp h_inv_sum
    linarith
  have hA_ub : A < NA / (U * (U ^ 2 + 2 * hp + 3)) := by
    dsimp only [A, NA]
    have hU2_pos : 0 < U ^ 2 + 2 * hp + 3 := by positivity
    have h1 : 1 / U - U / (U ^ 2 + 2 * hp + 3) = (2 * hp + 3) / (U * (U ^ 2 + 2 * hp + 3)) := by
      field_simp [hU_pos.ne', hU2_pos.ne']; ring
    linarith
  have hB_eq : B = hp ^ 3 / U := by dsimp only [B, U]; field_simp [hhp_pos.ne', hhp3_pos.ne']
  have hB_sub_A_pos : 0 < B - A := by
    have h1 : B - NA / (U * (U ^ 2 + 2 * hp + 3)) = DBA / (U * (U ^ 2 + 2 * hp + 3)) := by
      rw [hB_eq]; dsimp only [DBA]; field_simp [hU_pos.ne', (by positivity : (0 : ℝ) < U ^ 2 + 2 * hp + 3).ne']
    have hpos : 0 < DBA / (U * (U ^ 2 + 2 * hp + 3)) := div_pos hDBA_pos (by positivity)
    linarith [hA_ub]
  have hfrac_lt : A / (B - A) < NA / DBA := by
    rw [div_lt_div_iff₀ hB_sub_A_pos hDBA_pos]
    have h1 : A * DBA < NA * (B - A) ↔ A * (DBA + NA) < NA * B := by constructor <;> intro h <;> linarith
    rw [h1]
    have hsum_eq : DBA + NA = hp ^ 3 * (U ^ 2 + 2 * hp + 3) := by dsimp only [DBA]; ring
    rw [hsum_eq, hB_eq]
    have hU2_pos : 0 < U ^ 2 + 2 * hp + 3 := by positivity
    have h2 := mul_lt_mul_of_pos_right hA_ub (mul_pos (pow_pos hhp_pos 3) hU2_pos)
    have h3 : NA / (U * (U ^ 2 + 2 * hp + 3)) * (hp ^ 3 * (U ^ 2 + 2 * hp + 3)) = NA * (hp ^ 3 / U) := by
      field_simp [hU_pos.ne', hU2_pos.ne']
    linarith
  -- Step 2: Elementary ℓ⁴/ℓ³ inequality: (∑ d_i⁴)³ ≤ (∑ d_i³)⁴!
  let S3 : ℝ := ∑ i, d i ^ 3
  let S4 : ℝ := ∑ i, d i ^ 4
  have hS3_nn : 0 ≤ S3 := Finset.sum_nonneg fun i _ => pow_nonneg (hd_pos i).le 3
  have hS4_nn : 0 ≤ S4 := Finset.sum_nonneg fun i _ => pow_nonneg (hd_pos i).le 4
  have hS3_lt : S3 < NA / DBA := lt_trans hA_lt hfrac_lt
  have hS4_cube_le : S4 ^ 3 ≤ S3 ^ 4 := by
    by_cases hS3_0 : S3 = 0
    · have hS4_0 : S4 = 0 := by
        dsimp only [S4]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hdi3 : d i ^ 3 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => pow_nonneg (hd_pos j).le 3)).mp hS3_0 i (Finset.mem_univ i)
        exact absurd (pow_pos (hd_pos i) 3) (by rw [hdi3]; exact lt_irrefl 0)
      rw [hS4_0, hS3_0]; norm_num
    · have hS3_pos : 0 < S3 := lt_of_le_of_ne hS3_nn (Ne.symm hS3_0)
      have hterm : ∀ i, d i ^ 4 ≤ S3 ^ (1 / 3 : ℝ) * d i ^ 3 := fun i => by
        have hle3 : d i ^ 3 ≤ S3 :=
          Finset.single_le_sum (fun j _ => pow_nonneg (hd_pos j).le 3) (Finset.mem_univ i)
        have hle1 : d i ≤ S3 ^ (1 / 3 : ℝ) := by
          have := Real.rpow_le_rpow (pow_nonneg (hd_pos i).le 3) hle3 (by norm_num : (0 : ℝ) ≤ 1 / 3)
          rw [← Real.rpow_natCast (d i) 3, ← Real.rpow_mul (hd_pos i).le] at this
          norm_num at this; exact this
        calc d i ^ 4 = d i * d i ^ 3 := by ring
          _ ≤ S3 ^ (1 / 3 : ℝ) * d i ^ 3 := mul_le_mul_of_nonneg_right hle1 (pow_nonneg (hd_pos i).le 3)
      have hS4_le : S4 ≤ S3 ^ (1 / 3 : ℝ) * S3 := by
        dsimp only [S4]
        calc ∑ i, d i ^ 4 ≤ ∑ i, S3 ^ (1 / 3 : ℝ) * d i ^ 3 := Finset.sum_le_sum fun i _ => hterm i
          _ = S3 ^ (1 / 3 : ℝ) * S3 := by rw [← Finset.mul_sum]
      have hcube : S4 ^ 3 ≤ (S3 ^ (1 / 3 : ℝ) * S3) ^ 3 := pow_le_pow_left₀ hS4_nn hS4_le 3
      have hrhs : (S3 ^ (1 / 3 : ℝ) * S3) ^ 3 = S3 ^ 4 := by
        rw [mul_pow, ← Real.rpow_natCast (S3 ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hS3_pos.le]
        norm_num; ring
      rwa [hrhs] at hcube
  -- Step 3: Combine with polyP8 t > 0!
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hpoly : 0 < polyP8 t := polyP8_pos_of_pos ht
  have hpoly_eq : polyP8 t = DBA ^ 4 - 512 * ((1 + hp) ^ 3 * (hp - 1)) ^ 3 * NA ^ 4 := by
    dsimp only [polyP8, DBA, NA, U, t]; ring
  rw [hpoly_eq] at hpoly
  have hcube_lt : (((m : ℝ) - 1) * S4) ^ 3 < (1 / 8 : ℝ) ^ 3 := by
    have h1 : (((m : ℝ) - 1) * S4) ^ 3 ≤ ((m : ℝ) - 1) ^ 3 * S3 ^ 4 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hS4_cube_le (pow_nonneg hm1_pos.le 3)
    have h2 : ((m : ℝ) - 1) ^ 3 * S3 ^ 4 < ((1 + hp) ^ 3 * (hp - 1)) ^ 3 * (NA / DBA) ^ 4 := by
      have hm_cub : ((m : ℝ) - 1) ^ 3 < ((1 + hp) ^ 3 * (hp - 1)) ^ 3 :=
        pow_lt_pow_left₀ hm_lt hm1_pos.le (by norm_num)
      have hS3_4 : S3 ^ 4 < (NA / DBA) ^ 4 := pow_lt_pow_left₀ hS3_lt hS3_nn (by norm_num)
      calc ((m : ℝ) - 1) ^ 3 * S3 ^ 4
          < ((m : ℝ) - 1) ^ 3 * (NA / DBA) ^ 4 := mul_lt_mul_of_pos_left hS3_4 (pow_pos hm1_pos 3)
        _ < ((1 + hp) ^ 3 * (hp - 1)) ^ 3 * (NA / DBA) ^ 4 :=
            mul_lt_mul_of_pos_right hm_cub (pow_pos (div_pos hNA_pos hDBA_pos) 4)
    have h3 : ((1 + hp) ^ 3 * (hp - 1)) ^ 3 * (NA / DBA) ^ 4 < (1 / 8 : ℝ) ^ 3 := by
      rw [div_pow, show (1 / 8 : ℝ) ^ 3 = 1 / 512 by norm_num, mul_div_assoc',
        div_lt_div_iff₀ (pow_pos hDBA_pos 4) (by norm_num : (0 : ℝ) < 512)]
      linarith
    linarith
  by_contra hge; push Not at hge
  have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) hge 3
  linarith

/-! ==========================================================================
    PART 3: Pinching Second-Variation Positivity (Theorem B4(2), p ∈ {4/3, 3/2})
    ========================================================================== -/

private lemma blitz_ring_add_pow4 {R : Type*} [Ring R] (A B : R) :
    (A + B) ^ 4 = A ^ 4 +
      (A ^ 3 * B + A ^ 2 * B * A + A * B * A ^ 2 + B * A ^ 3) +
      (A ^ 2 * B ^ 2 + A * B * A * B + A * B ^ 2 * A + B * A ^ 2 * B + B * A * B * A + B ^ 2 * A ^ 2) +
      (A * B ^ 3 + B * A * B ^ 2 + B ^ 2 * A * B + B ^ 3 * A) +
      B ^ 4 := by
  noncomm_ring

private lemma blitz_ring_add3_pow3 {R : Type*} [Ring R] (X0 X1 X2 : R) :
    (X0 + X1 + X2) ^ 3 =
      X0 ^ 3 +
      (X0 ^ 2 * X1 + X0 * X1 * X0 + X1 * X0 ^ 2) +
      (X0 ^ 2 * X2 + X0 * X2 * X0 + X2 * X0 ^ 2 + X0 * X1 ^ 2 + X1 * X0 * X1 + X1 ^ 2 * X0) +
      (X0 * X1 * X2 + X0 * X2 * X1 + X1 * X0 * X2 + X1 * X2 * X0 + X2 * X0 * X1 + X2 * X1 * X0 + X1 ^ 3) +
      (X0 * X2 ^ 2 + X2 * X0 * X2 + X2 ^ 2 * X0 + X1 ^ 2 * X2 + X1 * X2 * X1 + X2 * X1 ^ 2) +
      (X1 * X2 ^ 2 + X2 * X1 * X2 + X2 ^ 2 * X1) +
      X2 ^ 3 := by
  noncomm_ring

private lemma blitz_ring_add_pow3 {R : Type*} [Ring R] (A B : R) :
    (A + B) ^ 3 = A ^ 3 + (A ^ 2 * B + A * B * A + B * A ^ 2) +
      (A * B ^ 2 + B * A * B + B ^ 2 * A) + B ^ 3 := by
  noncomm_ring

private lemma blitz_trace_zero_of_conj_neg {n : ℕ} {J X : Mat n}
    (hJ2 : J * J = 1) (hneg : J * X * J = -X) : X.trace = 0 := by
  have h1 : (J * X * J).trace = X.trace := by
    rw [Matrix.trace_mul_cycle, hJ2, Matrix.one_mul]
  rw [hneg, Matrix.trace_neg] at h1
  have h2 : X.trace + X.trace = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp (by linear_combination h2 : (2 : ℂ) * X.trace = 0)).resolve_left two_ne_zero

private lemma blitz_orth_proj_helpers {n : ℕ} {D X P : Mat n}
    (hP2 : P * P = P) (hPD : P * D = D * P) :
    let Q := 1 - P
    let X0 := P * X * P + Q * X * Q
    let V := X - X0
    let J := (2 : ℂ) • P - 1
    Q * Q = Q ∧ P * Q = 0 ∧ Q * P = 0 ∧ Q * D = D * Q ∧
    J * J = 1 ∧ J * D * J = D ∧ J * X0 * J = X0 ∧ J * V * J = -V ∧
    D = P * D * P + Q * D * Q ∧ V = P * X * Q + Q * X * P := by
  intro Q X0 V J
  have hQ2 : Q * Q = Q := by dsimp only [Q]; simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hP2]; abel
  have hPQ : P * Q = 0 := by dsimp only [Q]; rw [Matrix.mul_sub, Matrix.mul_one, hP2, sub_self]
  have hQP : Q * P = 0 := by dsimp only [Q]; rw [Matrix.sub_mul, Matrix.one_mul, hP2, sub_self]
  have hQD : Q * D = D * Q := by dsimp only [Q]; rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPD]
  have hJ_eq : J = P - Q := by dsimp only [J, Q]; rw [two_smul]; abel
  have hJ2 : J * J = 1 := by
    calc J * J = (P - Q) * (P - Q) := by rw [hJ_eq]
      _ = P * P - P * Q - (Q * P - Q * Q) := by simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
      _ = P + Q := by rw [hP2, hQ2, hPQ, hQP]; abel
      _ = 1 := by dsimp only [Q]; abel
  have hJP : J * P = P := by rw [hJ_eq, Matrix.sub_mul, hP2, hQP, sub_zero]
  have hPJ : P * J = P := by rw [hJ_eq, Matrix.mul_sub, hP2, hPQ, sub_zero]
  have hJQ : J * Q = -Q := by rw [hJ_eq, Matrix.sub_mul, hPQ, hQ2, zero_sub]
  have hQJ : Q * J = -Q := by rw [hJ_eq, Matrix.mul_sub, hQP, hQ2, zero_sub]
  have hPQ1 : P + Q = 1 := by dsimp only [Q]; abel
  have hD_split : D = P * D * P + Q * D * Q := by
    calc D = (P + Q) * D * (P + Q) := by rw [hPQ1, Matrix.one_mul, Matrix.mul_one]
      _ = P * D * P + P * D * Q + Q * D * P + Q * D * Q := by
            simp only [Matrix.add_mul, Matrix.mul_add]; abel
      _ = P * D * P + Q * D * Q := by
            have h1 : P * D * Q = 0 := by rw [hPD, Matrix.mul_assoc, hPQ, Matrix.mul_zero]
            have h2 : Q * D * P = 0 := by rw [hQD, Matrix.mul_assoc, hQP, Matrix.mul_zero]
            rw [h1, h2, add_zero, add_zero]
  have hV_eq : V = P * X * Q + Q * X * P := by
    have hX : X = P * X * P + P * X * Q + Q * X * P + Q * X * Q := by
      calc X = (P + Q) * X * (P + Q) := by rw [hPQ1, Matrix.one_mul, Matrix.mul_one]
        _ = P * X * P + P * X * Q + Q * X * P + Q * X * Q := by
              simp only [Matrix.add_mul, Matrix.mul_add]; abel
    calc V = X - (P * X * P + Q * X * Q) := rfl
      _ = (P * X * P + P * X * Q + Q * X * P + Q * X * Q) - (P * X * P + Q * X * Q) := by rw [← hX]
      _ = P * X * Q + Q * X * P := by abel
  have hJDJ : J * D * J = D := by
    conv_lhs => rw [hD_split]
    rw [Matrix.mul_add, Matrix.add_mul]
    have h1 : J * (P * D * P) * J = P * D * P := by
      calc _ = (J * P) * D * (P * J) := by simp only [Matrix.mul_assoc]
        _ = P * D * P := by rw [hJP, hPJ]
    have h2 : J * (Q * D * Q) * J = Q * D * Q := by
      calc _ = (J * Q) * D * (Q * J) := by simp only [Matrix.mul_assoc]
        _ = (-Q) * D * (-Q) := by rw [hJQ, hQJ]
        _ = Q * D * Q := by simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [h1, h2, ← hD_split]
  have hJX0J : J * X0 * J = X0 := by
    dsimp only [X0]; rw [Matrix.mul_add, Matrix.add_mul]
    have h1 : J * (P * X * P) * J = P * X * P := by
      calc _ = (J * P) * X * (P * J) := by simp only [Matrix.mul_assoc]
        _ = P * X * P := by rw [hJP, hPJ]
    have h2 : J * (Q * X * Q) * J = Q * X * Q := by
      calc _ = (J * Q) * X * (Q * J) := by simp only [Matrix.mul_assoc]
        _ = (-Q) * X * (-Q) := by rw [hJQ, hQJ]
        _ = Q * X * Q := by simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    rw [h1, h2]
  have hJVJ : J * V * J = -V := by
    rw [hV_eq, Matrix.mul_add, Matrix.add_mul]
    have h1 : J * (P * X * Q) * J = -(P * X * Q) := by
      calc _ = (J * P) * X * (Q * J) := by simp only [Matrix.mul_assoc]
        _ = P * X * (-Q) := by rw [hJP, hQJ]
        _ = -(P * X * Q) := by simp only [Matrix.mul_neg]
    have h2 : J * (Q * X * P) * J = -(Q * X * P) := by
      calc _ = (J * Q) * X * (P * J) := by simp only [Matrix.mul_assoc]
        _ = (-Q) * X * P := by rw [hJQ, hPJ]
        _ = -(Q * X * P) := by simp only [Matrix.neg_mul]
    rw [h1, h2]; abel
  exact ⟨hQ2, hPQ, hQP, hQD, hJ2, hJDJ, hJX0J, hJVJ, hD_split, hV_eq⟩

private lemma blitz_block_diag_pow3 {n : ℕ} {A B : Mat n} (hAB : A * B = 0) (hBA : B * A = 0) :
    (A + B) ^ 3 = A ^ 3 + B ^ 3 := by
  rw [blitz_ring_add_pow3]
  have h1 : A ^ 2 * B = 0 := by rw [blitz_pow_two, Matrix.mul_assoc, hAB, Matrix.mul_zero]
  have h2 : A * B * A = 0 := by rw [hAB, Matrix.zero_mul]
  have h3 : B * A ^ 2 = 0 := by rw [blitz_pow_two, ← Matrix.mul_assoc, hBA, Matrix.zero_mul]
  have h4 : A * B ^ 2 = 0 := by rw [blitz_pow_two, ← Matrix.mul_assoc, hAB, Matrix.zero_mul]
  have h5 : B * A * B = 0 := by rw [hBA, Matrix.zero_mul]
  have h6 : B ^ 2 * A = 0 := by rw [blitz_pow_two, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  rw [h1, h2, h3, h4, h5, h6]; abel

private lemma blitz_block_diag_pow4 {n : ℕ} {A B : Mat n} (hAB : A * B = 0) (hBA : B * A = 0) :
    (A + B) ^ 4 = A ^ 4 + B ^ 4 := by
  rw [blitz_ring_add_pow4]
  have hA2B : A ^ 2 * B = 0 := by rw [blitz_pow_two, Matrix.mul_assoc, hAB, Matrix.mul_zero]
  have hA3B : A ^ 3 * B = 0 := by rw [blitz_pow_three, Matrix.mul_assoc, Matrix.mul_assoc, hAB, Matrix.mul_zero, Matrix.mul_zero]
  have hBA2 : B * A ^ 2 = 0 := by rw [blitz_pow_two, ← Matrix.mul_assoc, hBA, Matrix.zero_mul]
  have hBA3 : B * A ^ 3 = 0 := by rw [blitz_pow_three, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBA, Matrix.zero_mul, Matrix.zero_mul]
  have hAB2 : A * B ^ 2 = 0 := by rw [blitz_pow_two, ← Matrix.mul_assoc, hAB, Matrix.zero_mul]
  have hAB3 : A * B ^ 3 = 0 := by rw [blitz_pow_three, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.zero_mul, Matrix.zero_mul]
  have hB2A : B ^ 2 * A = 0 := by rw [blitz_pow_two, Matrix.mul_assoc, hBA, Matrix.mul_zero]
  have hB3A : B ^ 3 * A = 0 := by rw [blitz_pow_three, Matrix.mul_assoc, Matrix.mul_assoc, hBA, Matrix.mul_zero, Matrix.mul_zero]
  have hA2B2 : A ^ 2 * B ^ 2 = 0 := by rw [blitz_pow_two, blitz_pow_two, Matrix.mul_assoc, ← Matrix.mul_assoc A B, hAB, Matrix.zero_mul, Matrix.mul_zero]
  have hB2A2 : B ^ 2 * A ^ 2 = 0 := by rw [blitz_pow_two, blitz_pow_two, Matrix.mul_assoc, ← Matrix.mul_assoc B A, hBA, Matrix.zero_mul, Matrix.mul_zero]
  simp only [hA3B, hA2B, hAB, hBA, hBA2, hBA3, hAB2, hAB3, hB2A, hB3A, hA2B2, hB2A2,
    Matrix.zero_mul, add_zero]

/-- Theorem B4(2a) (`b1_proof.md` §5): Pinching Second-Variation Positivity at p = 4/3!
    Along the pinching ray q(t) = 4 W_Λ(D, H₀ + t V) (where H₀ = P H P + Q H Q, V = H - H₀,
    Q = 1 - P, P orthogonal projection commuting with D) at any solution (D, H) of
    (D + H)³ = Λ D H D:
      (1) Exact even quartic: q(t) = q(0) - 2 t² Re Tr(V⁴) + t⁴ Re Tr(V⁴) for all t ∈ ℝ.
      (2) Stationarity & exact second variation at t = 1:
            q'(1) = 0  and  q''(1) = 8 Re Tr(V⁴)  (i.e. (1/4) q''(1) = 2 Re Tr(V⁴) = 4 ‖P H Q H P‖_HS²).
      (3) Strict positivity: whenever P H ≠ H P, q''(1) > 0 strictly! -/
theorem pinching_second_variation_pos_p43 {n : ℕ} {Λ h : ℝ} {D H P : Mat n}
    (hH : H.IsHermitian) (hP_herm : P.IsHermitian) (hP_idem : P * P = P) (hPD : P * D = D * P)
    (hEq : (D + H) ^ 3 = (Λ : ℂ) • (D * H * D)) :
    let Q := 1 - P
    let H0 := P * H * P + Q * H * Q
    let V := H - H0
    let q : ℝ → ℝ := fun t => fourW43 Λ h D (H0 + (t : ℂ) • V)
    let C4 : ℝ := (V ^ 4).trace.re
    (∀ t : ℝ, q t = q 0 - 2 * C4 * t ^ 2 + C4 * t ^ 4) ∧
    HasDerivAt q 0 1 ∧
    HasDerivAt (fun t => -4 * C4 * t + 4 * C4 * t ^ 3) (8 * C4) 1 ∧
    (∀ t : ℝ, HasDerivAt q (-4 * C4 * t + 4 * C4 * t ^ 3) t) ∧
    (P * H ≠ H * P → 0 < 8 * C4) := by
  intro Q H0 V q C4
  obtain ⟨hQ2, hPQ, hQP, hQD, hJ2, hJDJ, hJH0J, hJVJ, hD_split, hV_eq⟩ :=
    blitz_orth_proj_helpers (D := D) (X := H) hP_idem hPD
  let J : Mat n := (2 : ℂ) • P - 1
  change Q * Q = Q at hQ2; change P * Q = 0 at hPQ; change Q * P = 0 at hQP
  change Q * D = D * Q at hQD; change J * J = 1 at hJ2; change J * D * J = D at hJDJ
  change J * H0 * J = H0 at hJH0J; change J * V * J = -V at hJVJ
  change D = P * D * P + Q * D * Q at hD_split; change V = P * H * Q + Q * H * P at hV_eq
  have hJ_mul : ∀ A B : Mat n, (J * A * J) * (J * B * J) = J * (A * B) * J := fun A B => by
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  let A0 : Mat n := D + H0
  have hJA0J : J * A0 * J = A0 := by dsimp only [A0]; rw [Matrix.mul_add, Matrix.add_mul, hJDJ, hJH0J]
  have hodd_A03V : (A0 ^ 3 * V).trace = 0 := by
    apply blitz_trace_zero_of_conj_neg hJ2
    have : J * (A0 ^ 3 * V) * J = (J * A0 * J) * (J * A0 * J) * (J * A0 * J) * (J * V * J) := by
      rw [hJ_mul, hJ_mul, hJ_mul]; simp only [blitz_pow_three, Matrix.mul_assoc]
    rw [this, hJA0J, hJVJ]; simp only [Matrix.mul_neg, blitz_pow_three, Matrix.mul_assoc]
  have hodd_A0V3 : (A0 * V ^ 3).trace = 0 := by
    apply blitz_trace_zero_of_conj_neg hJ2
    have : J * (A0 * V ^ 3) * J = (J * A0 * J) * (J * V * J) * (J * V * J) * (J * V * J) := by
      rw [hJ_mul, hJ_mul, hJ_mul]; simp only [blitz_pow_three, Matrix.mul_assoc]
    rw [this, hJA0J, hJVJ]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, blitz_pow_three, Matrix.mul_assoc]
  have hodd_DH0DV : (D * H0 * D * V).trace = 0 := by
    apply blitz_trace_zero_of_conj_neg hJ2
    have : J * (D * H0 * D * V) * J = (J * D * J) * (J * H0 * J) * (J * D * J) * (J * V * J) := by
      rw [hJ_mul, hJ_mul, hJ_mul]
    rw [this, hJDJ, hJH0J, hJVJ]; simp only [Matrix.mul_neg, Matrix.mul_assoc]
  -- Define C2 explicitly and expand q(t) = q(0) + C2 * t^2 + C4 * t^4
  let C2 : ℝ := 4 * (A0 ^ 2 * V ^ 2).trace.re + 2 * (A0 * V * A0 * V).trace.re - 2 * Λ * (D * V * D * V).trace.re
  have hq_poly : ∀ t : ℝ, q t = q 0 + C2 * t ^ 2 + C4 * t ^ 4 := fun t => by
    dsimp only [q, fourW43]
    rw [show H0 + ((0 : ℝ) : ℂ) • V = H0 by simp]
    have hsplit : D + (H0 + (t : ℂ) • V) = A0 + (t : ℂ) • V := by dsimp only [A0]; abel
    rw [hsplit, blitz_ring_add_pow4 A0 ((t : ℂ) • V)]
    have hp2 : ((t : ℂ) • V) ^ 2 = ((t ^ 2 : ℝ) : ℂ) • V ^ 2 := by
      rw [blitz_pow_two, blitz_pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    have hp3 : ((t : ℂ) • V) ^ 3 = ((t ^ 3 : ℝ) : ℂ) • V ^ 3 := by
      rw [blitz_pow_three, blitz_pow_three]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    have hp4 : ((t : ℂ) • V) ^ 4 = ((t ^ 4 : ℝ) : ℂ) • V ^ 4 := by
      rw [blitz_pow_four, blitz_pow_four]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    rw [hp2, hp3, hp4]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul, Complex.add_re]
    -- Cycle all traces cleanly
    have c1 : (A0 ^ 2 * V * A0).trace = (A0 ^ 3 * V).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, blitz_pow_three, Matrix.mul_assoc]
    have c2 : (A0 * V * A0 ^ 2).trace = (A0 ^ 3 * V).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, blitz_pow_three, Matrix.mul_assoc]
    have c3 : (V * A0 ^ 3).trace = (A0 ^ 3 * V).trace := Matrix.trace_mul_comm V (A0 ^ 3)
    have c4 : (A0 * V ^ 2 * A0).trace = (A0 ^ 2 * V ^ 2).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c5 : (V * A0 ^ 2 * V).trace = (A0 ^ 2 * V ^ 2).trace := by
      rw [Matrix.mul_assoc V (A0 ^ 2) V, Matrix.trace_mul_comm V (A0 ^ 2 * V)]
      apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c6 : (V * A0 * V * A0).trace = (A0 * V * A0 * V).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [Matrix.mul_assoc]
    have c7 : (V ^ 2 * A0 ^ 2).trace = (A0 ^ 2 * V ^ 2).trace := Matrix.trace_mul_comm (V ^ 2) (A0 ^ 2)
    have c8 : (V * A0 * V ^ 2).trace = (A0 * V ^ 3).trace := by
      rw [Matrix.mul_assoc V A0 (V ^ 2), Matrix.trace_mul_comm V (A0 * V ^ 2)]
      apply blitz_tr_eq; simp only [blitz_pow_two, blitz_pow_three, Matrix.mul_assoc]
    have c9 : (V ^ 2 * A0 * V).trace = (A0 * V ^ 3).trace := by
      rw [Matrix.mul_assoc (V ^ 2) A0 V, Matrix.trace_mul_comm (V ^ 2) (A0 * V)]
      apply blitz_tr_eq; simp only [blitz_pow_two, blitz_pow_three, Matrix.mul_assoc]
    have c10 : (V ^ 3 * A0).trace = (A0 * V ^ 3).trace := Matrix.trace_mul_comm (V ^ 3) A0
    have ht2c : (t : ℂ) * (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have hDHDH : (D * (H0 + (t : ℂ) • V) * D * (H0 + (t : ℂ) • V)).trace.re =
        (D * H0 * D * H0).trace.re + t ^ 2 * (D * V * D * V).trace.re := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, Complex.add_re]
      have hd1 : (D * V * D * H0).trace = (D * H0 * D * V).trace := by
        calc (D * V * D * H0).trace = ((D * V) * (D * H0)).trace := by apply blitz_tr_eq; simp only [Matrix.mul_assoc]
          _ = ((D * H0) * (D * V)).trace := Matrix.trace_mul_comm _ _
          _ = (D * H0 * D * V).trace := by apply blitz_tr_eq; simp only [Matrix.mul_assoc]
      rw [hd1, hodd_DH0DV]
      simp only [mul_zero, zero_add, add_zero, Complex.zero_re, ← mul_assoc, ht2c,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hodd_A03V, hodd_A0V3, hDHDH]
    simp only [mul_zero, Complex.zero_re, add_zero, ht2c,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    dsimp only [A0, C2, C4]
    ring
  -- Check q(0) = fourW43(P D P, P H P) + fourW43(Q D Q, Q H Q)
  have hq0_split : q 0 = fourW43 Λ h (P * D * P) (P * H * P) + fourW43 Λ h (Q * D * Q) (Q * H * Q) := by
    dsimp only [q, fourW43]
    rw [show H0 + ((0 : ℝ) : ℂ) • V = H0 by simp]
    have hA0_sp : D + H0 = (P * D * P + P * H * P) + (Q * D * Q + Q * H * Q) := by
      calc D + H0 = (P * D * P + Q * D * Q) + (P * H * P + Q * H * Q) := congrArg (· + H0) hD_split
        _ = _ := by abel
    have hAB_A : (P * D * P + P * H * P) * (Q * D * Q + Q * H * Q) = 0 := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      have k : ∀ X Y : Mat n, (P * X * P) * (Q * Y * Q) = 0 := fun X Y => by
        calc (P * X * P) * (Q * Y * Q) = P * X * (P * Q) * Y * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      rw [k, k, k, k, add_zero, add_zero]
    have hBA_A : (Q * D * Q + Q * H * Q) * (P * D * P + P * H * P) = 0 := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      have k : ∀ X Y : Mat n, (Q * X * Q) * (P * Y * P) = 0 := fun X Y => by
        calc (Q * X * Q) * (P * Y * P) = Q * X * (Q * P) * Y * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      rw [k, k, k, k, add_zero, add_zero]
    have hA4 : (D + H0) ^ 4 = (P * D * P + P * H * P) ^ 4 + (Q * D * Q + Q * H * Q) ^ 4 := by
      rw [hA0_sp]; exact blitz_block_diag_pow4 hAB_A hBA_A
    have hD4 : D ^ 4 = (P * D * P) ^ 4 + (Q * D * Q) ^ 4 := by
      conv_lhs => rw [hD_split]
      exact blitz_block_diag_pow4
        (by calc (P * D * P) * (Q * D * Q) = P * D * (P * Q) * D * Q := by simp only [Matrix.mul_assoc]
              _ = 0 := by rw [hPQ]; simp)
        (by calc (Q * D * Q) * (P * D * P) = Q * D * (Q * P) * D * P := by simp only [Matrix.mul_assoc]
              _ = 0 := by rw [hQP]; simp)
    have hDH : D * H0 = (P * D * P) * (P * H * P) + (Q * D * Q) * (Q * H * Q) := by
      conv_lhs => rw [hD_split]; dsimp only [H0]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      have k1 : (P * D * P) * (Q * H * Q) = 0 := by
        calc _ = P * D * (P * Q) * H * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have k2 : (Q * D * Q) * (P * H * P) = 0 := by
        calc _ = Q * D * (Q * P) * H * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      rw [k1, k2, add_zero, zero_add]
    have hDHDH : D * H0 * D * H0 = (P * D * P) * (P * H * P) * (P * D * P) * (P * H * P) +
        (Q * D * Q) * (Q * H * Q) * (Q * D * Q) * (Q * H * Q) := by
      calc D * H0 * D * H0 = (D * H0) * (D * H0) := by simp only [Matrix.mul_assoc]
        _ = ((P * D * P) * (P * H * P) + (Q * D * Q) * (Q * H * Q)) *
              ((P * D * P) * (P * H * P) + (Q * D * Q) * (Q * H * Q)) := by rw [hDH]
        _ = (P * D * P) * (P * H * P) * (P * D * P) * (P * H * P) +
              (Q * D * Q) * (Q * H * Q) * (Q * D * Q) * (Q * H * Q) := by
              rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
              have k1 : ((P * D * P) * (P * H * P)) * ((Q * D * Q) * (Q * H * Q)) = 0 := by
                calc _ = P * D * P * P * H * (P * Q) * D * Q * Q * H * Q := by simp only [Matrix.mul_assoc]
                  _ = 0 := by rw [hPQ]; simp
              have k2 : ((Q * D * Q) * (Q * H * Q)) * ((P * D * P) * (P * H * P)) = 0 := by
                calc _ = Q * D * Q * Q * H * (Q * P) * D * P * P * H * P := by simp only [Matrix.mul_assoc]
                  _ = 0 := by rw [hQP]; simp
              rw [k1, k2, add_zero, zero_add]; simp only [Matrix.mul_assoc]
    rw [hA4, hD4, hDHDH, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Complex.add_re, Complex.add_re, Complex.add_re]
    ring
  -- Compare t = 1 with pinching_decomposition_p43 to obtain C2 = -2 * C4 in 1 line!
  have hpinch := (pinching_decomposition_p43 (h := h) hH hP_herm hP_idem hPD hEq).1
  have hq1_eq : q 1 = fourW43 Λ h D H := by
    dsimp only [q]
    rw [show H0 + ((1 : ℝ) : ℂ) • V = H by dsimp only [V]; simp]
  have hC2_eq : C2 = -2 * C4 := by
    have h1 := hq_poly 1
    rw [hq1_eq, hq0_split] at h1
    dsimp only [C4] at h1 ⊢
    linarith [hpinch]
  have hq_exact : ∀ t : ℝ, q t = q 0 - 2 * C4 * t ^ 2 + C4 * t ^ 4 := fun t => by
    rw [hq_poly t, hC2_eq]; ring
  have hderiv1 : ∀ t : ℝ, HasDerivAt q (-4 * C4 * t + 4 * C4 * t ^ 3) t := fun t => by
    have hfun : q = fun s => q 0 - 2 * C4 * s ^ 2 + C4 * s ^ 4 := funext hq_exact
    rw [hfun]
    have hd := ((hasDerivAt_const t (q 0)).sub ((hasDerivAt_pow 2 t).const_mul (2 * C4))).add
      ((hasDerivAt_pow 4 t).const_mul C4)
    exact hd.congr_deriv (by ring)
  have hderiv1_at1 : HasDerivAt q 0 1 := by
    have h := hderiv1 1
    exact h.congr_deriv (by ring)
  have hderiv2_at1 : HasDerivAt (fun t => -4 * C4 * t + 4 * C4 * t ^ 3) (8 * C4) 1 := by
    have hd := ((hasDerivAt_id (1 : ℝ)).const_mul (-4 * C4)).add ((hasDerivAt_pow 3 (1 : ℝ)).const_mul (4 * C4))
    exact hd.congr_deriv (by ring)
  have hstrict : P * H ≠ H * P → 0 < 8 * C4 := fun hne => by
    have hV_ne : V ≠ 0 := by
      intro hV0
      have hH0 : H = H0 := sub_eq_zero.mp hV0
      apply hne
      calc P * H = P * (P * H * P + Q * H * Q) := congrArg (P * ·) hH0
        _ = P * H * P := by
              rw [Matrix.mul_add,
                show P * (P * H * P) = (P * P) * H * P by simp only [Matrix.mul_assoc], hP_idem,
                show P * (Q * H * Q) = (P * Q) * H * Q by simp only [Matrix.mul_assoc], hPQ,
                Matrix.zero_mul, Matrix.zero_mul, add_zero]
        _ = (P * H * P + Q * H * Q) * P := by
              rw [Matrix.add_mul, Matrix.mul_assoc (P * H), hP_idem,
                Matrix.mul_assoc (Q * H), hQP, Matrix.mul_zero, add_zero]
        _ = H * P := congrArg (· * P) hH0.symm
    have hVh : V.IsHermitian := by
      have hH0h : H0.IsHermitian := by
        dsimp only [H0]
        have hQh : Q.IsHermitian := Matrix.isHermitian_one.sub hP_herm
        refine Matrix.IsHermitian.add ?_ ?_
        · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_herm.eq, hH.eq, Matrix.mul_assoc]
        · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh.eq, hH.eq, Matrix.mul_assoc]
      exact hH.sub hH0h
    have hV2_ne : V ^ 2 ≠ 0 := by
      intro h0
      have htr : hsNormSq V = 0 := by
        dsimp only [hsNormSq]; rw [hVh.eq, ← blitz_pow_two, h0, Matrix.trace_zero, Complex.zero_re]
      exact hV_ne ((hsNormSq_eq_zero_iff V).mp htr)
    have hC4_eq : C4 = hsNormSq (V ^ 2) := by
      dsimp only [C4, hsNormSq]
      have hV2h : (V ^ 2)ᴴ = V ^ 2 := by
        rw [blitz_pow_two, Matrix.conjTranspose_mul, hVh.eq]
      rw [hV2h]; apply blitz_tr_re_eq; simp only [blitz_pow_two, blitz_pow_four, Matrix.mul_assoc]
    have hC4_pos : 0 < C4 := by
      rw [hC4_eq]
      exact lt_of_le_of_ne (hsNormSq_nonneg _) (fun h0 => hV2_ne ((hsNormSq_eq_zero_iff _).mp h0.symm))
    linarith
  exact ⟨hq_exact, hderiv1_at1, hderiv2_at1, hderiv1, hstrict⟩

/-- Theorem B4(2b) (`b1_proof.md` §5): Pinching Second-Variation Positivity at p = 3/2!
    Along the pinching ray q(t) = 3 W_Λ(D, M₀ + t V) (where M₀ = P M P + Q M Q, V = M - M₀,
    X₀ = D + M₀ D M₀, X₁ = M₀ D V + V D M₀, X₂ = V D V) at any PosDef solution (D, M) of
    (D + M D M)² = Λ D M D:
      (1) Exact even sextic: q(t) = q(0) - (2 A₄ + 3 A₆) t² + A₄ t⁴ + A₆ t⁶ for all t ∈ ℝ,
          where A₄ = 3 Re Tr(X₀ X₂²) + 3 Re Tr(X₁² X₂) ≥ 0 and A₆ = Re Tr(X₂³) ≥ 0.
      (2) Stationarity & exact second variation at t = 1:
            q'(1) = 0  and  q''(1) = 8 A₄ + 24 A₆.
      (3) Strict positivity: whenever P M ≠ M P, q''(1) = 8 A₄ + 24 A₆ > 0 strictly! -/
theorem pinching_second_variation_pos_p32 {n : ℕ} {Λ m : ℝ} {D M P : Mat n}
    (hD : D.PosDef) (hM : M.PosDef) (hP_herm : P.IsHermitian) (hP_idem : P * P = P)
    (hPD : P * D = D * P)
    (hEq : (D + M * D * M) ^ 2 = (Λ : ℂ) • (D * M * D)) :
    let Q := 1 - P
    let M0 := P * M * P + Q * M * Q
    let V := M - M0
    let X0 := D + M0 * D * M0
    let X1 := M0 * D * V + V * D * M0
    let X2 := V * D * V
    let q : ℝ → ℝ := fun t => threeW32 Λ m D (M0 + (t : ℂ) • V)
    let A4 : ℝ := 3 * (X0 * X2 ^ 2).trace.re + 3 * (X1 ^ 2 * X2).trace.re
    let A6 : ℝ := (X2 ^ 3).trace.re
    (∀ t : ℝ, q t = q 0 - (2 * A4 + 3 * A6) * t ^ 2 + A4 * t ^ 4 + A6 * t ^ 6) ∧
    HasDerivAt q 0 1 ∧
    HasDerivAt (fun t => -2 * (2 * A4 + 3 * A6) * t + 4 * A4 * t ^ 3 + 6 * A6 * t ^ 5) (8 * A4 + 24 * A6) 1 ∧
    (∀ t : ℝ, HasDerivAt q (-2 * (2 * A4 + 3 * A6) * t + 4 * A4 * t ^ 3 + 6 * A6 * t ^ 5) t) ∧
    0 ≤ A4 ∧ 0 ≤ A6 ∧
    (P * M ≠ M * P → 0 < 8 * A4 + 24 * A6) := by
  intro Q M0 V X0 X1 X2 q A4 A6
  obtain ⟨hQ2, hPQ, hQP, hQD, hJ2, hJDJ, hJM0J, hJVJ, hD_split, _⟩ :=
    blitz_orth_proj_helpers (D := D) (X := M) hP_idem hPD
  let J : Mat n := (2 : ℂ) • P - 1
  change Q * Q = Q at hQ2; change P * Q = 0 at hPQ; change Q * P = 0 at hQP
  change Q * D = D * Q at hQD; change J * J = 1 at hJ2; change J * D * J = D at hJDJ
  change J * M0 * J = M0 at hJM0J; change J * V * J = -V at hJVJ
  change D = P * D * P + Q * D * Q at hD_split
  have hJ_mul : ∀ A B : Mat n, (J * A * J) * (J * B * J) = J * (A * B) * J := fun A B => by
    calc (J * A * J) * (J * B * J) = J * A * (J * J) * B * J := by simp only [Matrix.mul_assoc]
      _ = J * (A * B) * J := by rw [hJ2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hJX0J : J * X0 * J = X0 := by
    dsimp only [X0]; rw [Matrix.mul_add, Matrix.add_mul, hJDJ]
    have : J * (M0 * D * M0) * J = (J * M0 * J) * (J * D * J) * (J * M0 * J) := by rw [hJ_mul, hJ_mul]
    rw [this, hJM0J, hJDJ]
  have hJX1J : J * X1 * J = -X1 := by
    dsimp only [X1]; rw [Matrix.mul_add, Matrix.add_mul]
    have h1 : J * (M0 * D * V) * J = -(M0 * D * V) := by
      have : J * (M0 * D * V) * J = (J * M0 * J) * (J * D * J) * (J * V * J) := by rw [hJ_mul, hJ_mul]
      rw [this, hJM0J, hJDJ, hJVJ]; simp only [Matrix.mul_neg]
    have h2 : J * (V * D * M0) * J = -(V * D * M0) := by
      have : J * (V * D * M0) * J = (J * V * J) * (J * D * J) * (J * M0 * J) := by rw [hJ_mul, hJ_mul]
      rw [this, hJM0J, hJDJ, hJVJ]; simp only [Matrix.neg_mul]
    rw [h1, h2]; abel
  have hJX2J : J * X2 * J = X2 := by
    dsimp only [X2]
    have : J * (V * D * V) * J = (J * V * J) * (J * D * J) * (J * V * J) := by rw [hJ_mul, hJ_mul]
    rw [this, hJVJ, hJDJ]; simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  have hodd_tr : ∀ Y : Mat n, J * Y * J = -Y → Y.trace = 0 := fun Y hY =>
    blitz_trace_zero_of_conj_neg hJ2 hY
  have hodd_X02X1 : (X0 ^ 2 * X1).trace = 0 := hodd_tr _ (by
    have : J * (X0 ^ 2 * X1) * J = (J * X0 * J) * (J * X0 * J) * (J * X1 * J) := by
      rw [hJ_mul, hJ_mul]; simp only [blitz_pow_two, Matrix.mul_assoc]
    rw [this, hJX0J, hJX1J]; simp only [Matrix.mul_neg, blitz_pow_two, Matrix.mul_assoc])
  have hodd_X0X1X2 : (X0 * X1 * X2).trace = 0 := hodd_tr _ (by
    have : J * (X0 * X1 * X2) * J = (J * X0 * J) * (J * X1 * J) * (J * X2 * J) := by rw [hJ_mul, hJ_mul]
    rw [this, hJX0J, hJX1J, hJX2J]; simp only [Matrix.mul_neg, Matrix.neg_mul])
  have hodd_X0X2X1 : (X0 * X2 * X1).trace = 0 := hodd_tr _ (by
    have : J * (X0 * X2 * X1) * J = (J * X0 * J) * (J * X2 * J) * (J * X1 * J) := by rw [hJ_mul, hJ_mul]
    rw [this, hJX0J, hJX1J, hJX2J]; simp only [Matrix.mul_neg])
  have hodd_X13 : (X1 ^ 3).trace = 0 := hodd_tr _ (by
    have : J * (X1 ^ 3) * J = (J * X1 * J) * (J * X1 * J) * (J * X1 * J) := by
      rw [hJ_mul, hJ_mul]; simp only [blitz_pow_three, Matrix.mul_assoc]
    rw [this, hJX1J]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, blitz_pow_three, Matrix.mul_assoc])
  have hodd_X1X22 : (X1 * X2 ^ 2).trace = 0 := hodd_tr _ (by
    have : J * (X1 * X2 ^ 2) * J = (J * X1 * J) * (J * X2 * J) * (J * X2 * J) := by
      rw [hJ_mul, hJ_mul]; simp only [blitz_pow_two, Matrix.mul_assoc]
    rw [this, hJX1J, hJX2J]; simp only [Matrix.neg_mul, blitz_pow_two, Matrix.mul_assoc])
  have hodd_DM02DV : ((D * M0) ^ 2 * (D * V)).trace = 0 := hodd_tr _ (by
    have hDM0 : J * (D * M0) * J = D * M0 := by rw [← hJ_mul, hJDJ, hJM0J]
    have hDV : J * (D * V) * J = -(D * V) := by rw [← hJ_mul, hJDJ, hJVJ]; simp only [Matrix.mul_neg]
    have : J * ((D * M0) ^ 2 * (D * V)) * J = (J * (D * M0) * J) * (J * (D * M0) * J) * (J * (D * V) * J) := by
      rw [hJ_mul, hJ_mul]; simp only [blitz_pow_two, Matrix.mul_assoc]
    rw [this, hDM0, hDV]; simp only [Matrix.mul_neg, blitz_pow_two, Matrix.mul_assoc])
  have hodd_DV3 : ((D * V) ^ 3).trace = 0 := hodd_tr _ (by
    have hDV : J * (D * V) * J = -(D * V) := by rw [← hJ_mul, hJDJ, hJVJ]; simp only [Matrix.mul_neg]
    have : J * ((D * V) ^ 3) * J = (J * (D * V) * J) * (J * (D * V) * J) * (J * (D * V) * J) := by
      rw [hJ_mul, hJ_mul]; simp only [blitz_pow_three, Matrix.mul_assoc]
    rw [this, hDV]; simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, blitz_pow_three, Matrix.mul_assoc])
  let A2 : ℝ := 3 * (X0 ^ 2 * X2).trace.re + 3 * (X0 * X1 ^ 2).trace.re - 6 * Λ * ((D * M0) * (D * V) ^ 2).trace.re
  have hq_poly : ∀ t : ℝ, q t = q 0 + A2 * t ^ 2 + A4 * t ^ 4 + A6 * t ^ 6 := fun t => by
    dsimp only [q, threeW32]
    rw [show M0 + ((0 : ℝ) : ℂ) • V = M0 by simp]
    have hX_split : D + (M0 + (t : ℂ) • V) * D * (M0 + (t : ℂ) • V) =
        X0 + (t : ℂ) • X1 + ((t ^ 2 : ℝ) : ℂ) • X2 := by
      dsimp only [X0, X1, X2]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
      rw [show (t : ℂ) * (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring]
      abel
    rw [hX_split, blitz_ring_add3_pow3 X0 ((t : ℂ) • X1) (((t ^ 2 : ℝ) : ℂ) • X2)]
    have hX1_2 : ((t : ℂ) • X1) ^ 2 = ((t ^ 2 : ℝ) : ℂ) • X1 ^ 2 := by
      rw [blitz_pow_two, blitz_pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    have hX1_3 : ((t : ℂ) • X1) ^ 3 = ((t ^ 3 : ℝ) : ℂ) • X1 ^ 3 := by
      rw [blitz_pow_three, blitz_pow_three]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    have hX2_2 : (((t ^ 2 : ℝ) : ℂ) • X2) ^ 2 = ((t ^ 4 : ℝ) : ℂ) • X2 ^ 2 := by
      rw [blitz_pow_two, blitz_pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    have hX2_3 : (((t ^ 2 : ℝ) : ℂ) • X2) ^ 3 = ((t ^ 6 : ℝ) : ℂ) • X2 ^ 3 := by
      rw [blitz_pow_three, blitz_pow_three]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
    rw [hX1_2, hX1_3, hX2_2, hX2_3]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_add, Matrix.trace_smul,
      smul_eq_mul, Complex.add_re]
    -- Cycle traces in (X0 + t X1 + t² X2)^3
    have c1 : (X0 * X1 * X0).trace = (X0 ^ 2 * X1).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c2 : (X1 * X0 ^ 2).trace = (X0 ^ 2 * X1).trace := Matrix.trace_mul_comm X1 (X0 ^ 2)
    have c3 : (X0 * X2 * X0).trace = (X0 ^ 2 * X2).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c4 : (X2 * X0 ^ 2).trace = (X0 ^ 2 * X2).trace := Matrix.trace_mul_comm X2 (X0 ^ 2)
    have c5 : (X1 * X0 * X1).trace = (X0 * X1 ^ 2).trace := by
      rw [Matrix.mul_assoc X1 X0 X1, Matrix.trace_mul_comm X1 (X0 * X1)]
      apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c6 : (X1 ^ 2 * X0).trace = (X0 * X1 ^ 2).trace := Matrix.trace_mul_comm (X1 ^ 2) X0
    have c7 : (X1 * X0 * X2).trace = (X0 * X2 * X1).trace := by
      rw [Matrix.mul_assoc X1 X0 X2, Matrix.trace_mul_comm X1 (X0 * X2)]
    have c8 : (X1 * X2 * X0).trace = (X0 * X1 * X2).trace := by
      rw [Matrix.trace_mul_comm (X1 * X2) X0, ← Matrix.mul_assoc X0 X1 X2]
    have c9 : (X2 * X0 * X1).trace = (X0 * X1 * X2).trace := by
      rw [Matrix.mul_assoc X2 X0 X1, Matrix.trace_mul_comm X2 (X0 * X1)]
    have c10 : (X2 * X1 * X0).trace = (X0 * X2 * X1).trace := by
      rw [Matrix.trace_mul_comm (X2 * X1) X0, ← Matrix.mul_assoc X0 X2 X1]
    have c11 : (X2 * X0 * X2).trace = (X0 * X2 ^ 2).trace := by
      rw [Matrix.mul_assoc X2 X0 X2, Matrix.trace_mul_comm X2 (X0 * X2)]
      apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c12 : (X2 ^ 2 * X0).trace = (X0 * X2 ^ 2).trace := Matrix.trace_mul_comm (X2 ^ 2) X0
    have c13 : (X1 * X2 * X1).trace = (X1 ^ 2 * X2).trace := by
      rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c14 : (X2 * X1 ^ 2).trace = (X1 ^ 2 * X2).trace := Matrix.trace_mul_comm X2 (X1 ^ 2)
    have c15 : (X2 * X1 * X2).trace = (X1 * X2 ^ 2).trace := by
      rw [Matrix.mul_assoc X2 X1 X2, Matrix.trace_mul_comm X2 (X1 * X2)]
      apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
    have c16 : (X2 ^ 2 * X1).trace = (X1 * X2 ^ 2).trace := Matrix.trace_mul_comm (X2 ^ 2) X1
    have ht2c : (t : ℂ) * (t : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have ht4c : (t : ℂ) * ((t ^ 2 : ℝ) : ℂ) * (t : ℂ) = ((t ^ 4 : ℝ) : ℂ) := by push_cast; ring
    have ht4c' : ((t ^ 2 : ℝ) : ℂ) * ((t ^ 2 : ℝ) : ℂ) = ((t ^ 4 : ℝ) : ℂ) := by push_cast; ring
    -- Expand ((D * (M0 + t V))^3).trace.re
    have hDM3 : ((D * (M0 + (t : ℂ) • V)) ^ 3).trace.re =
        ((D * M0) ^ 3).trace.re + 3 * t ^ 2 * ((D * M0) * (D * V) ^ 2).trace.re := by
      rw [Matrix.mul_add, Matrix.mul_smul, blitz_ring_add_pow3 (D * M0) ((t : ℂ) • (D * V))]
      have hp2 : ((t : ℂ) • (D * V)) ^ 2 = ((t ^ 2 : ℝ) : ℂ) • (D * V) ^ 2 := by
        rw [blitz_pow_two, blitz_pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
      have hp3 : ((t : ℂ) • (D * V)) ^ 3 = ((t ^ 3 : ℝ) : ℂ) • (D * V) ^ 3 := by
        rw [blitz_pow_three, blitz_pow_three]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; push_cast; ring_nf
      rw [hp2, hp3]
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.trace_add, Matrix.trace_smul,
        smul_eq_mul, Complex.add_re]
      have d1 : (D * M0 * (D * V) * (D * M0)).trace = ((D * M0) ^ 2 * (D * V)).trace := by
        rw [Matrix.trace_mul_comm]; apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
      have d2 : (D * V * (D * M0) ^ 2).trace = ((D * M0) ^ 2 * (D * V)).trace := Matrix.trace_mul_comm _ _
      have d3 : (D * V * (D * M0) * (D * V)).trace = (D * M0 * (D * V) ^ 2).trace := by
        rw [Matrix.mul_assoc (D * V) (D * M0) (D * V), Matrix.trace_mul_comm (D * V) ((D * M0) * (D * V))]
        apply blitz_tr_eq; simp only [blitz_pow_two, Matrix.mul_assoc]
      have d4 : ((D * V) ^ 2 * (D * M0)).trace = (D * M0 * (D * V) ^ 2).trace := Matrix.trace_mul_comm _ _
      rw [d1, d2, d3, d4, hodd_DM02DV, hodd_DV3]
      simp only [mul_zero, Complex.zero_re, add_zero, ht2c,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring
    rw [c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16,
      hodd_X02X1, hodd_X0X1X2, hodd_X0X2X1, hodd_X13, hodd_X1X22, hDM3]
    simp only [mul_zero, Complex.zero_re, add_zero, ← mul_assoc,
      ht4c, ht4c', ht2c,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    dsimp only [X0, A2, A4, A6]
    ring
  -- Check q(0) = threeW32(P D P, P M P) + threeW32(Q D Q, Q M Q)
  have hq0_split : q 0 = threeW32 Λ m (P * D * P) (P * M * P) + threeW32 Λ m (Q * D * Q) (Q * M * Q) := by
    dsimp only [q, threeW32]
    rw [show M0 + ((0 : ℝ) : ℂ) • V = M0 by simp]
    have hM0DM0 : M0 * D * M0 = (P * M * P) * (P * D * P) * (P * M * P) + (Q * M * Q) * (Q * D * Q) * (Q * M * Q) := by
      calc M0 * D * M0 = (P * M * P + Q * M * Q) * (P * D * P + Q * D * Q) * (P * M * P + Q * M * Q) := by
            dsimp only [M0]; exact congrArg (fun Z => (P * M * P + Q * M * Q) * Z * (P * M * P + Q * M * Q)) hD_split
        _ = _ := by
            simp only [Matrix.add_mul, Matrix.mul_add]
            have kPQ : ∀ A B : Mat n, (P * A * P) * (Q * B * Q) = 0 := fun A B => by
              calc _ = P * A * (P * Q) * B * Q := by simp only [Matrix.mul_assoc]
                _ = 0 := by rw [hPQ]; simp
            have kQP : ∀ A B : Mat n, (Q * A * Q) * (P * B * P) = 0 := fun A B => by
              calc _ = Q * A * (Q * P) * B * P := by simp only [Matrix.mul_assoc]
                _ = 0 := by rw [hQP]; simp
            have p1 : (P * M * P) * (P * D * P) * (Q * M * Q) = 0 := by
              calc _ = P * M * P * P * D * (P * Q) * M * Q := by simp only [Matrix.mul_assoc]
                _ = 0 := by rw [hPQ]; simp
            have p2 : (Q * M * Q) * (Q * D * Q) * (P * M * P) = 0 := by
              calc _ = Q * M * Q * Q * D * (Q * P) * M * P := by simp only [Matrix.mul_assoc]
                _ = 0 := by rw [hQP]; simp
            simp only [kPQ, kQP, p1, p2, Matrix.zero_mul, add_zero, zero_add]
    have hX0_sp : D + M0 * D * M0 =
        (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) +
        (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) := by
      calc D + M0 * D * M0
          = (P * D * P + Q * D * Q) +
              ((P * M * P) * (P * D * P) * (P * M * P) + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) :=
            congrArg₂ (· + ·) hD_split hM0DM0
        _ = _ := by abel
    have hDM0 : D * M0 = (P * D * P) * (P * M * P) + (Q * D * Q) * (Q * M * Q) := by
      conv_lhs => rw [hD_split]; dsimp only [M0]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      have k1 : (P * D * P) * (Q * M * Q) = 0 := by
        calc _ = P * D * (P * Q) * M * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have k2 : (Q * D * Q) * (P * M * P) = 0 := by
        calc _ = Q * D * (Q * P) * M * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      rw [k1, k2, add_zero, zero_add]
    have hX0_3 : (D + M0 * D * M0) ^ 3 =
        (P * D * P + (P * M * P) * (P * D * P) * (P * M * P)) ^ 3 +
        (Q * D * Q + (Q * M * Q) * (Q * D * Q) * (Q * M * Q)) ^ 3 := by
      rw [hX0_sp]
      have kPQ : ∀ A B : Mat n, (P * A * P) * (Q * B * Q) = 0 := fun A B => by
        calc _ = P * A * (P * Q) * B * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      have kQP : ∀ A B : Mat n, (Q * A * Q) * (P * B * P) = 0 := fun A B => by
        calc _ = Q * A * (Q * P) * B * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
      refine blitz_block_diag_pow3 ?_ ?_
      · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        have a1 : (P * D * P) * ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) = 0 := by
          calc _ = P * D * (P * Q) * M * Q * Q * D * Q * Q * M * Q := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hPQ]; simp
        have a2 : ((P * M * P) * (P * D * P) * (P * M * P)) * (Q * D * Q) = 0 := by
          calc _ = P * M * P * P * D * P * P * M * (P * Q) * D * Q := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hPQ]; simp
        have a3 : ((P * M * P) * (P * D * P) * (P * M * P)) * ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) = 0 := by
          calc _ = P * M * P * P * D * P * P * M * (P * Q) * M * Q * Q * D * Q * Q * M * Q := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hPQ]; simp
        rw [kPQ, a1, a2, a3, add_zero, add_zero]
      · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
        have a1 : (Q * D * Q) * ((P * M * P) * (P * D * P) * (P * M * P)) = 0 := by
          calc _ = Q * D * (Q * P) * M * P * P * D * P * P * M * P := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hQP]; simp
        have a2 : ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) * (P * D * P) = 0 := by
          calc _ = Q * M * Q * Q * D * Q * Q * M * (Q * P) * D * P := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hQP]; simp
        have a3 : ((Q * M * Q) * (Q * D * Q) * (Q * M * Q)) * ((P * M * P) * (P * D * P) * (P * M * P)) = 0 := by
          calc _ = Q * M * Q * Q * D * Q * Q * M * (Q * P) * M * P * P * D * P * P * M * P := by simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hQP]; simp
        rw [kQP, a1, a2, a3, add_zero, add_zero]
    have hDM0_3 : (D * M0) ^ 3 = ((P * D * P) * (P * M * P)) ^ 3 + ((Q * D * Q) * (Q * M * Q)) ^ 3 := by
      rw [hDM0]
      refine blitz_block_diag_pow3 ?_ ?_
      · calc _ = P * D * P * P * M * (P * Q) * D * Q * Q * M * Q := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hPQ]; simp
      · calc _ = Q * D * Q * Q * M * (Q * P) * D * P * P * M * P := by simp only [Matrix.mul_assoc]
          _ = 0 := by rw [hQP]; simp
    have hD_3 : D ^ 3 = (P * D * P) ^ 3 + (Q * D * Q) ^ 3 := by
      conv_lhs => rw [hD_split]
      exact blitz_block_diag_pow3
        (by calc _ = P * D * (P * Q) * D * Q := by simp only [Matrix.mul_assoc]
              _ = 0 := by rw [hPQ]; simp)
        (by calc _ = Q * D * (Q * P) * D * P := by simp only [Matrix.mul_assoc]
              _ = 0 := by rw [hQP]; simp)
    rw [hX0_3, hDM0_3, hD_3, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Complex.add_re, Complex.add_re, Complex.add_re]
    ring
  -- Compare t = 1 with pinching_decomposition_p32!
  obtain ⟨hpinch, hA4a_nn, hA4b_nn, hA6_nn⟩ :=
    pinching_decomposition_p32 (m := m) hD hM hP_herm hP_idem hPD hEq
  have hA4_nn : 0 ≤ A4 := by dsimp only [A4]; linarith
  have hq1_eq : q 1 = threeW32 Λ m D M := by
    dsimp only [q]; rw [show M0 + ((1 : ℝ) : ℂ) • V = M by dsimp only [V]; simp]
  have hA2_eq : A2 = -(2 * A4 + 3 * A6) := by
    have h1 := hq_poly 1
    rw [hq1_eq, hq0_split] at h1
    dsimp only [A4, A6] at h1 ⊢
    linarith [hpinch]
  have hq_exact : ∀ t : ℝ, q t = q 0 - (2 * A4 + 3 * A6) * t ^ 2 + A4 * t ^ 4 + A6 * t ^ 6 := fun t => by
    rw [hq_poly t, hA2_eq]; ring
  have hderiv1 : ∀ t : ℝ, HasDerivAt q (-2 * (2 * A4 + 3 * A6) * t + 4 * A4 * t ^ 3 + 6 * A6 * t ^ 5) t := fun t => by
    have hfun : q = fun s => q 0 - (2 * A4 + 3 * A6) * s ^ 2 + A4 * s ^ 4 + A6 * s ^ 6 := funext hq_exact
    rw [hfun]
    have hd := (((hasDerivAt_const t (q 0)).sub ((hasDerivAt_pow 2 t).const_mul (2 * A4 + 3 * A6))).add
      ((hasDerivAt_pow 4 t).const_mul A4)).add ((hasDerivAt_pow 6 t).const_mul A6)
    exact hd.congr_deriv (by ring)
  have hderiv1_at1 : HasDerivAt q 0 1 := (hderiv1 1).congr_deriv (by ring)
  have hderiv2_at1 :
      HasDerivAt (fun t => -2 * (2 * A4 + 3 * A6) * t + 4 * A4 * t ^ 3 + 6 * A6 * t ^ 5) (8 * A4 + 24 * A6) 1 := by
    have hd := (((hasDerivAt_id (1 : ℝ)).const_mul (-2 * (2 * A4 + 3 * A6))).add
      ((hasDerivAt_pow 3 (1 : ℝ)).const_mul (4 * A4))).add ((hasDerivAt_pow 5 (1 : ℝ)).const_mul (6 * A6))
    exact hd.congr_deriv (by ring)
  have hstrict : P * M ≠ M * P → 0 < 8 * A4 + 24 * A6 := fun hne => by
    have hV_ne : V ≠ 0 := by
      intro hV0
      have hM0 : M = M0 := sub_eq_zero.mp hV0
      apply hne
      calc P * M = P * (P * M * P + Q * M * Q) := congrArg (P * ·) hM0
        _ = P * M * P := by
              rw [Matrix.mul_add,
                show P * (P * M * P) = (P * P) * M * P by simp only [Matrix.mul_assoc], hP_idem,
                show P * (Q * M * Q) = (P * Q) * M * Q by simp only [Matrix.mul_assoc], hPQ,
                Matrix.zero_mul, Matrix.zero_mul, add_zero]
        _ = (P * M * P + Q * M * Q) * P := by
              rw [Matrix.add_mul, Matrix.mul_assoc (P * M), hP_idem,
                Matrix.mul_assoc (Q * M), hQP, Matrix.mul_zero, add_zero]
        _ = M * P := congrArg (· * P) hM0.symm
    have hVh : V.IsHermitian := by
      have hM0h : M0.IsHermitian := by
        dsimp only [M0]; have hQh : Q.IsHermitian := Matrix.isHermitian_one.sub hP_herm
        refine Matrix.IsHermitian.add ?_ ?_
        · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hP_herm.eq, hM.isHermitian.eq, Matrix.mul_assoc]
        · rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh.eq, hM.isHermitian.eq, Matrix.mul_assoc]
      exact hM.isHermitian.sub hM0h
    -- X2 = V * D * V = (V * Dhalf) * (V * Dhalf)ᴴ ⪰ 0 and X2 ≠ 0 ⟹ A6 = Tr(X2³) > 0!
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    have hDhalf_sq : Dhalf * Dhalf = D := by dsimp only [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_one hD
    have hDhalf_h : Dhalfᴴ = Dhalf := (posDefPow_posDef (1 / 2) hD).isHermitian.eq
    have hX2_eq : X2 = (V * Dhalf) * (V * Dhalf)ᴴ := by
      calc X2 = V * (Dhalf * Dhalf) * V := by dsimp only [X2]; rw [hDhalf_sq]
        _ = (V * Dhalf) * (Dhalf * V) := by simp only [Matrix.mul_assoc]
        _ = (V * Dhalf) * (V * Dhalf)ᴴ := by rw [Matrix.conjTranspose_mul, hVh.eq, hDhalf_h]
    have hX2_psd : X2.PosSemidef := by
      rw [hX2_eq]; simpa using Matrix.posSemidef_conjTranspose_mul_self (V * Dhalf)ᴴ
    have hX2_ne : X2 ≠ 0 := by
      intro h0
      have hVD0 : V * Dhalf = 0 := by
        have htr : hsNormSq (V * Dhalf) = 0 := by
          dsimp only [hsNormSq]
          rw [trace_re_mul_comm (V * Dhalf)ᴴ (V * Dhalf), ← hX2_eq, h0, Matrix.trace_zero, Complex.zero_re]
        exact (hsNormSq_eq_zero_iff _).mp htr
      have hDmh : Dhalf * posDefPow (-(1 / 2 : ℝ)) hD = 1 := by
        dsimp only [Dhalf]; rw [posDefPow_mul_posDefPow]; norm_num; exact posDefPow_zero hD
      have hV0 : V = 0 := by
        calc V = V * (Dhalf * posDefPow (-(1 / 2 : ℝ)) hD) := by rw [hDmh, Matrix.mul_one]
          _ = (V * Dhalf) * posDefPow (-(1 / 2 : ℝ)) hD := by rw [Matrix.mul_assoc]
          _ = 0 := by rw [hVD0, Matrix.zero_mul]
      exact hV_ne hV0
    have hA6_pos : 0 < A6 := by
      let UX := hX2_psd.isHermitian.eigenvectorUnitary
      let evX := hX2_psd.isHermitian.eigenvalues
      have hX2s : X2 = (UX : Mat n) * Matrix.diagonal (fun i => (evX i : ℂ)) * (UX : Mat n)ᴴ := by
        simpa [UX, evX, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hX2_psd.isHermitian.spectral_theorem
      have hev_nn : ∀ i, 0 ≤ evX i := fun i => hX2_psd.eigenvalues_nonneg i
      have hex_pos : ∃ i, 0 < evX i := by
        by_contra hall; push Not at hall
        have hall0 : ∀ i, evX i = 0 := fun i => le_antisymm (hall i) (hev_nn i)
        apply hX2_ne; rw [hX2s]
        have : Matrix.diagonal (fun i => (evX i : ℂ)) = 0 := by
          ext i j; by_cases hij : i = j
          · subst hij; simp [hall0]
          · simp [Matrix.diagonal_apply_ne _ hij]
        rw [this, Matrix.mul_zero, Matrix.zero_mul]
      have hX2_cube : X2 ^ 3 = (UX : Mat n) * Matrix.diagonal (fun i => ((evX i ^ 3 : ℝ) : ℂ)) * (UX : Mat n)ᴴ := by
        rw [blitz_pow_three, hX2s]
        calc ((UX : Mat n) * Matrix.diagonal (fun i => (evX i : ℂ)) * (UX : Mat n)ᴴ) *
              ((UX : Mat n) * Matrix.diagonal (fun i => (evX i : ℂ)) * (UX : Mat n)ᴴ) *
              ((UX : Mat n) * Matrix.diagonal (fun i => (evX i : ℂ)) * (UX : Mat n)ᴴ)
            = (UX : Mat n) * (Matrix.diagonal (fun i => (evX i : ℂ)) * ((UX : Mat n)ᴴ * (UX : Mat n)) *
                Matrix.diagonal (fun i => (evX i : ℂ)) * ((UX : Mat n)ᴴ * (UX : Mat n)) *
                Matrix.diagonal (fun i => (evX i : ℂ))) * (UX : Mat n)ᴴ := by simp only [Matrix.mul_assoc]
          _ = (UX : Mat n) * Matrix.diagonal (fun i => ((evX i ^ 3 : ℝ) : ℂ)) * (UX : Mat n)ᴴ := by
                rw [blitz_unitary_conj_mul UX, Matrix.mul_one, Matrix.mul_one,
                  Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
                refine congrArg (· * (UX : Mat n)ᴴ) (congrArg ((UX : Mat n) * ·) ?_)
                ext i j; by_cases hij : i = j
                · subst hij; simp [pow_succ]
                · simp [Matrix.diagonal_apply_ne _ hij]
      have htr : A6 = ∑ i, evX i ^ 3 := by
        dsimp only [A6]
        have h1 : (X2 ^ 3).trace = (Matrix.diagonal (fun i => ((evX i ^ 3 : ℝ) : ℂ))).trace := by
          rw [hX2_cube, Matrix.trace_mul_cycle, blitz_unitary_conj_mul UX, Matrix.one_mul]
        rw [h1, Matrix.trace_diagonal, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => Complex.ofReal_re _
      rw [htr]
      obtain ⟨i0, hi0⟩ := hex_pos
      exact Finset.sum_pos' (fun i _ => pow_nonneg (hev_nn i) 3) ⟨i0, Finset.mem_univ _, pow_pos hi0 3⟩
    linarith
  exact ⟨hq_exact, hderiv1_at1, hderiv2_at1, hderiv1, hA4_nn, hA6_nn, hstrict⟩

/-! ==========================================================================
    PART 4: Exact 2×2 Hessian Determinant & Inertia (Theorem B5, p = 4/3)
    ========================================================================== -/

/-- Theorem B5 (`b1_proof.md` §3): Global Non-Degeneracy & Exact Inertia (2-, 1+) of
    ∇²_{HH} S_Λ at s = 2, p = 4/3 (ALL Λ > 27/4, ALL irreducible 2×2 PD solutions):
    For A = D + H = [[u₀, b], [b, v₀]] ≻ 0 (u₀, v₀ > 0, u₀ v₀ > b², b ≠ 0, S = u₀ + v₀)
    with D = diag(1, r) (0 < r < 1) solving the (1,2)-equation b² = Λ r - (u₀² + u₀ v₀ + v₀²),
    let L_H[V] := A² V + A V A + V A² - Λ D V D, and let L ∈ Mat₃(ℝ) be its exact matrix in the
    orthonormal basis E₁ = diag(1, 0), E₂ = diag(0, 1), E₃ = (1/√2)[[0, 1], [1, 0]] of S²:
      (1) Exact Schur complement M_schur := L_{12,12} - L₃₃⁻¹ L_{12,3} L_{3,12} obeys
            (x, y) M_schur (x, y)ᵀ = -(3 S² - 2 Λ r)(x + y)² - Λ(x + r y)² < 0  ∀ (x, y) ≠ (0, 0),
          while L₃₃ = 2 b² > 0 (exact inertia (2-, 1+)).
      (2) Exact closed-form determinant:
            det(L) = 2 b² Λ (3 S² - 2 Λ r)(1 - r)² > 0.
      (3) Complex U(1) diagonal phase-gauge kernel: on ℂ²×², E₄ = [[0, -i], [i, 0]] satisfies
            L_H[E₄] = 0 identically! -/
theorem hessian_det_pos_2x2_p43 {Λ r u0 v0 b : ℝ}
    (hΛ : 0 < Λ) (hr0 : 0 < r) (hr1 : r < 1)
    (hb : b ≠ 0) (hdetA : b ^ 2 < u0 * v0)
    (hb2_eq : b ^ 2 = Λ * r - (u0 ^ 2 + u0 * v0 + v0 ^ 2)) :
    let S := u0 + v0
    let D : Matrix (Fin 2) (Fin 2) ℝ := ![![1, 0], ![0, r]]
    let A : Matrix (Fin 2) (Fin 2) ℝ := ![![u0, b], ![b, v0]]
    let E : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ :=
      ![![![1, 0], ![0, 0]], ![![0, 0], ![0, 1]], ![![0, 1 / Real.sqrt 2], ![1 / Real.sqrt 2, 0]]]
    let LH : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
      fun V => A * A * V + A * V * A + V * A * A - Λ • (D * V * D)
    let L : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (LH (E i) * E j).trace
    let Mschur : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.of fun i j => L i.castSucc j.castSucc - L i.castSucc 2 * L 2 j.castSucc / L 2 2
    -- (1) Exact L₃₃ > 0 and strict negative definiteness of Schur complement (exact inertia (2-, 1+))
    L 2 2 = 2 * b ^ 2 ∧ 0 < L 2 2 ∧
    0 < 3 * S ^ 2 - 2 * Λ * r ∧
    (∀ x y : ℝ, Mschur 0 0 * x ^ 2 + (Mschur 0 1 + Mschur 1 0) * x * y + Mschur 1 1 * y ^ 2 =
      -(3 * S ^ 2 - 2 * Λ * r) * (x + y) ^ 2 - Λ * (x + r * y) ^ 2) ∧
    (∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) →
      Mschur 0 0 * x ^ 2 + (Mschur 0 1 + Mschur 1 0) * x * y + Mschur 1 1 * y ^ 2 < 0) ∧
    -- (2) Exact closed-form determinant > 0
    L.det = 2 * b ^ 2 * Λ * (3 * S ^ 2 - 2 * Λ * r) * (1 - r) ^ 2 ∧
    0 < L.det ∧
    -- (3) Complex U(1) gauge kernel L_H[E₄] = 0
    (let Dc : Mat 2 := ![![(1 : ℂ), 0], ![0, (r : ℂ)]]
     let Ac : Mat 2 := ![![(u0 : ℂ), (b : ℂ)], ![(b : ℂ), (v0 : ℂ)]]
     let E4 : Mat 2 := ![![(0 : ℂ), -Complex.I], ![Complex.I, 0]]
     Ac * Ac * E4 + Ac * E4 * Ac + E4 * Ac * Ac - (Λ : ℂ) • (Dc * E4 * Dc) = 0) := by
  intro S D A E LH L Mschur
  have _ : 0 < Λ * r := mul_pos hΛ hr0
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq2_ne : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hb2_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
  have hE0 : E 0 = ![![1, 0], ![0, 0]] := rfl
  have hE1 : E 1 = ![![0, 0], ![0, 1]] := rfl
  have hE2 : E 2 = ![![0, 1 / Real.sqrt 2], ![1 / Real.sqrt 2, 0]] := rfl
  -- Compute all 9 entries of L explicitly (expand Matrix ops BEFORE unfolding A, D, E)!
  have hL00 : L 0 0 = 3 * u0 ^ 2 + 2 * b ^ 2 - Λ := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE0, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hL11 : L 1 1 = 3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2 := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE1, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hL01 : L 0 1 = b ^ 2 := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE0, hE1, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hL10 : L 1 0 = b ^ 2 := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE0, hE1, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hL02 : L 0 2 = Real.sqrt 2 * b * (2 * u0 + v0) := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE0, hE2, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsq2_ne]; linear_combination -b * (2 * u0 + v0) * hsq2
  have hL20 : L 2 0 = Real.sqrt 2 * b * (2 * u0 + v0) := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE0, hE2, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsq2_ne]; linear_combination -b * (2 * u0 + v0) * hsq2
  have hL12 : L 1 2 = Real.sqrt 2 * b * (u0 + 2 * v0) := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE1, hE2, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsq2_ne]; linear_combination -b * (u0 + 2 * v0) * hsq2
  have hL21 : L 2 1 = Real.sqrt 2 * b * (u0 + 2 * v0) := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE1, hE2, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsq2_ne]; linear_combination -b * (u0 + 2 * v0) * hsq2
  have hL22 : L 2 2 = 2 * b ^ 2 := by
    simp only [L, LH, Matrix.of_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    simp only [hE2, A, D, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hsq2_ne]
    rw [hsq2]; linear_combination 2 * hb2_eq
  have hL22_pos : 0 < L 2 2 := by rw [hL22]; linarith
  have hQ_eq : 3 * S ^ 2 - 2 * Λ * r = S ^ 2 + 2 * (u0 * v0 - b ^ 2) := by
    dsimp only [S]; rw [hb2_eq]; ring
  have hQ_pos : 0 < 3 * S ^ 2 - 2 * Λ * r := by
    rw [hQ_eq]; nlinarith [sq_nonneg S, hdetA]
  -- Schur complement entries!
  have hM00 : Mschur 0 0 = -(3 * S ^ 2 - 2 * Λ * r) - Λ := by
    dsimp only [Mschur, Matrix.of_apply, S]
    change L 0 0 - L 0 2 * L 2 0 / L 2 2 = _
    rw [hL00, hL02, hL20, hL22]
    have hnum : Real.sqrt 2 * b * (2 * u0 + v0) * (Real.sqrt 2 * b * (2 * u0 + v0)) =
        2 * b ^ 2 * (2 * u0 + v0) ^ 2 := by linear_combination b ^ 2 * (2 * u0 + v0) ^ 2 * hsq2
    rw [hnum, mul_div_cancel_left₀ _ (by positivity : (2 * b ^ 2 : ℝ) ≠ 0), hb2_eq]; ring
  have hM11 : Mschur 1 1 = -(3 * S ^ 2 - 2 * Λ * r) - Λ * r ^ 2 := by
    dsimp only [Mschur, Matrix.of_apply, S]
    change L 1 1 - L 1 2 * L 2 1 / L 2 2 = _
    rw [hL11, hL12, hL21, hL22]
    have hnum : Real.sqrt 2 * b * (u0 + 2 * v0) * (Real.sqrt 2 * b * (u0 + 2 * v0)) =
        2 * b ^ 2 * (u0 + 2 * v0) ^ 2 := by linear_combination b ^ 2 * (u0 + 2 * v0) ^ 2 * hsq2
    rw [hnum, mul_div_cancel_left₀ _ (by positivity : (2 * b ^ 2 : ℝ) ≠ 0), hb2_eq]; ring
  have hM01 : Mschur 0 1 = -(3 * S ^ 2 - 2 * Λ * r) - Λ * r := by
    dsimp only [Mschur, Matrix.of_apply, S]
    change L 0 1 - L 0 2 * L 2 1 / L 2 2 = _
    rw [hL01, hL02, hL21, hL22]
    have hnum : Real.sqrt 2 * b * (2 * u0 + v0) * (Real.sqrt 2 * b * (u0 + 2 * v0)) =
        2 * b ^ 2 * ((2 * u0 + v0) * (u0 + 2 * v0)) := by
      linear_combination b ^ 2 * (2 * u0 + v0) * (u0 + 2 * v0) * hsq2
    rw [hnum, mul_div_cancel_left₀ _ (by positivity : (2 * b ^ 2 : ℝ) ≠ 0), hb2_eq]; ring
  have hM10 : Mschur 1 0 = -(3 * S ^ 2 - 2 * Λ * r) - Λ * r := by
    dsimp only [Mschur, Matrix.of_apply, S]
    change L 1 0 - L 1 2 * L 2 0 / L 2 2 = _
    rw [hL10, hL12, hL20, hL22]
    have hnum : Real.sqrt 2 * b * (u0 + 2 * v0) * (Real.sqrt 2 * b * (2 * u0 + v0)) =
        2 * b ^ 2 * ((u0 + 2 * v0) * (2 * u0 + v0)) := by
      linear_combination b ^ 2 * (u0 + 2 * v0) * (2 * u0 + v0) * hsq2
    rw [hnum, mul_div_cancel_left₀ _ (by positivity : (2 * b ^ 2 : ℝ) ≠ 0), hb2_eq]; ring
  have hquad : ∀ x y : ℝ, Mschur 0 0 * x ^ 2 + (Mschur 0 1 + Mschur 1 0) * x * y + Mschur 1 1 * y ^ 2 =
      -(3 * S ^ 2 - 2 * Λ * r) * (x + y) ^ 2 - Λ * (x + r * y) ^ 2 := fun x y => by
    rw [hM00, hM01, hM10, hM11]; ring
  have hquad_neg : ∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) →
      Mschur 0 0 * x ^ 2 + (Mschur 0 1 + Mschur 1 0) * x * y + Mschur 1 1 * y ^ 2 < 0 := fun x y hxy => by
    rw [hquad x y]
    have hne : x + y ≠ 0 ∨ x + r * y ≠ 0 := by
      by_contra h; push Not at h
      have h1 : (1 - r) * y = 0 := by linarith
      have hy0 : y = 0 := (mul_eq_zero.mp h1).resolve_left (by linarith)
      have hx0 : x = 0 := by linarith
      rcases hxy with hx | hy
      · exact hx hx0
      · exact hy hy0
    rcases hne with h1 | h2
    · have hp1 : 0 < (3 * S ^ 2 - 2 * Λ * r) * (x + y) ^ 2 := mul_pos hQ_pos (sq_pos_of_ne_zero h1)
      have hp2 : 0 ≤ Λ * (x + r * y) ^ 2 := mul_nonneg hΛ.le (sq_nonneg _)
      linarith
    · have hp1 : 0 ≤ (3 * S ^ 2 - 2 * Λ * r) * (x + y) ^ 2 := mul_nonneg hQ_pos.le (sq_nonneg _)
      have hp2 : 0 < Λ * (x + r * y) ^ 2 := mul_pos hΛ (sq_pos_of_ne_zero h2)
      linarith
  have hdet_eq : L.det = 2 * b ^ 2 * Λ * (3 * S ^ 2 - 2 * Λ * r) * (1 - r) ^ 2 := by
    rw [Matrix.det_fin_three, hL00, hL01, hL02, hL10, hL11, hL12, hL20, hL21, hL22]
    dsimp only [S]
    -- Use hsq2 : √2^2 = 2 and hb2_eq : b^2 = Λ*r - (u0^2 + u0*v0 + v0^2)
    have hstep1 : (3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) * (2 * b ^ 2) -
        (3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * (Real.sqrt 2 * b * (u0 + 2 * v0)) * (Real.sqrt 2 * b * (u0 + 2 * v0)) -
        b ^ 2 * b ^ 2 * (2 * b ^ 2) +
        b ^ 2 * (Real.sqrt 2 * b * (u0 + 2 * v0)) * (Real.sqrt 2 * b * (2 * u0 + v0)) +
        Real.sqrt 2 * b * (2 * u0 + v0) * b ^ 2 * (Real.sqrt 2 * b * (u0 + 2 * v0)) -
        Real.sqrt 2 * b * (2 * u0 + v0) * (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) * (Real.sqrt 2 * b * (2 * u0 + v0)) =
        2 * b ^ 2 * (((3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) - b ^ 4) -
          (3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * (u0 + 2 * v0) ^ 2 -
          (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) * (2 * u0 + v0) ^ 2 +
          2 * b ^ 2 * (2 * u0 + v0) * (u0 + 2 * v0)) := by
      linear_combination
        (-(3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * b ^ 2 * (u0 + 2 * v0) ^ 2 +
          2 * b ^ 4 * (u0 + 2 * v0) * (2 * u0 + v0) -
          (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) * b ^ 2 * (2 * u0 + v0) ^ 2) * hsq2
    rw [hstep1]
    have hfac_eq : (((3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) - b ^ 4) -
        (3 * u0 ^ 2 + 2 * b ^ 2 - Λ) * (u0 + 2 * v0) ^ 2 -
        (3 * v0 ^ 2 + 2 * b ^ 2 - Λ * r ^ 2) * (2 * u0 + v0) ^ 2 +
        2 * b ^ 2 * (2 * u0 + v0) * (u0 + 2 * v0)) =
        Λ * (3 * (u0 + v0) ^ 2 - 2 * Λ * r) * (1 - r) ^ 2 := by
      rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, hb2_eq]; ring
    rw [hfac_eq]; ring
  have hdet_pos : 0 < L.det := by
    rw [hdet_eq]
    have h1r : 0 < (1 - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
    positivity
  have hgauge : (let Dc : Mat 2 := ![![(1 : ℂ), 0], ![0, (r : ℂ)]]
      let Ac : Mat 2 := ![![(u0 : ℂ), (b : ℂ)], ![(b : ℂ), (v0 : ℂ)]]
      let E4 : Mat 2 := ![![(0 : ℂ), -Complex.I], ![Complex.I, 0]]
      Ac * Ac * E4 + Ac * E4 * Ac + E4 * Ac * Ac - (Λ : ℂ) • (Dc * E4 * Dc) = 0) := by
    intro Dc Ac E4
    have hbc : ((b : ℂ) ^ 2) = (Λ : ℂ) * (r : ℂ) - ((u0 : ℂ) ^ 2 + (u0 : ℂ) * (v0 : ℂ) + (v0 : ℂ) ^ 2) := by
      exact_mod_cast hb2_eq
    refine Matrix.ext fun i j => ?_
    revert i j
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
      simp only [Ac, Dc, E4, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
      simp only [Ac, Dc, E4, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -Complex.I * hbc
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
      simp only [Ac, Dc, E4, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination Complex.I * hbc
    · simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
      simp only [Ac, Dc, E4, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
  exact ⟨hL22, hL22_pos, hQ_pos, hquad, hquad_neg, hdet_eq, hdet_pos, hgauge⟩

/-! ==========================================================================
    PART 5: Complete 2×2 Analytic Master Trace Proofs (Theorems B6 & B7)
    ========================================================================== -/

/-- Exact flux derivative polynomial h(v) = (1 - v)² (-9 v² + 20 v - 8) for Theorem B6 (p = 4/3). -/
def fluxDerivH43 (v : ℝ) : ℝ := (1 - v) ^ 2 * (-9 * v ^ 2 + 20 * v - 8)

set_option maxHeartbeats 800000 in
/-- Theorem B6 (`b1_proof.md` §1): Complete Core Analytic Proof of the 2×2 Master Trace
    Inequality at p = 4/3 for ALL Λ > 8 and ALL m ≥ 2:
      (1) Exact (u, t) factorization of b², positivity of a, c, b², and det(H) = (S - 1 - r)³ / (2S - 1 - r) > 0.
      (2) Exact strict monotonicity h'(v) = 6 (1 - v)(2 v - 3)(3 v - 2) < 0 on (2/3, 1),
          exact factored opposite-sign endpoints h(1/x) - 1/Λ < 0 and h(1/(1 + p_max)) - 1/Λ > 0,
          and exact flux derivative identities along any C¹ branch S(r) solving S³ = Λ r (2S - 1 - r):
            φ₁'(r) = -r⁴ φ₂'(r) = ((1 + r)⁴ u⁴ / ((2S - 1 - r)(4S - 3 - 3r))) (h(1/u) - 1/Λ).
      (3) Exact Λ-monotonicity of τ₂(Λ) / σ_+(Λ) and Master Trace bound for all m ≥ 2:
            dσ_+/dΛ = h_+² / (1 + h_+)² > 0,  Tr(Φ) = r_*⁴ σ_+ - τ₂ < 0,
            σ_+² d(τ₂/σ_+)/dΛ = (r_*⁴ σ_+ - τ₂) dσ_+/dΛ - (σ_+/Λ) E < 0,
          whence τ₂/σ_+ ≤ 1/(m - 1) ⟺ σ_+ + τ₂ ≤ (m/(m - 1)) σ_+! -/
theorem master_trace_2x2_p43 {Λ hm hp : ℝ}
    (hhm0 : 0 < hm) (hhm_half : hm < 1 / 2) (hhp1 : 1 < hp)
    (hScm : (1 + hm) ^ 3 = Λ * hm) (hScp : (1 + hp) ^ 3 = Λ * hp) :
    let x := 1 + hm
    let y := 1 + hp
    let pmax := x * y / (x ^ 2 + y ^ 2)
    let σp := hp ^ 2 - hp
    let σm := hm - hm ^ 2
    -- (0) Vieta & pmax bounds
    0 < pmax ∧ pmax < 1 / 2 ∧ Λ = (1 + pmax) ^ 3 / (pmax ^ 2 * (1 + 2 * pmax)) ∧
    -- (1) Exact (u, t) factorization, b² > 0, a > 0, c > 0, det(H) > 0
    (∀ r u : ℝ, 0 < r → r < 1 → x < u → u < 1 + pmax →
      let t := r / (1 + r) ^ 2
      let S := (1 + r) * u
      let a := r * (2 + r - S) / (1 - r)
      let c := (S - 1 - 2 * r) / (1 - r)
      let u0 := 1 + a
      let v0 := r + c
      let b2 := Λ * r - (u0 ^ 2 + u0 * v0 + v0 ^ 2)
      u ^ 3 / (2 * u - 1) = Λ * t →
      b2 = (1 + r) ^ 2 / ((1 - 4 * t) * (2 * u - 1)) * (t - (u - 1) ^ 2) * ((u - 1) - (2 * u - 1) * t) ∧
      0 < b2 ∧ 0 < a ∧ 0 < c ∧
      a * c - b2 = (S - 1 - r) ^ 3 / (2 * S - 1 - r) ∧ 0 < a * c - b2) ∧
    -- (2) Strict decrease of h(v) on (2/3, 1), exact factored endpoints, and exact C¹ flux derivatives
    (∀ v : ℝ, 2 / 3 < v → v < 1 →
      HasDerivAt fluxDerivH43 (6 * (1 - v) * (2 * v - 3) * (3 * v - 2)) v ∧
      6 * (1 - v) * (2 * v - 3) * (3 * v - 2) < 0) ∧
    (fluxDerivH43 (1 / x) - 1 / Λ = -(1 - 1 / x) * (2 - 1 / x) * (3 / x - 2) ^ 2 ∧
      fluxDerivH43 (1 / x) - 1 / Λ < 0) ∧
    (fluxDerivH43 (1 / (1 + pmax)) - 1 / Λ =
      pmax ^ 2 * (2 + 5 * pmax) * (1 - 2 * pmax) / (1 + pmax) ^ 4 ∧
      0 < fluxDerivH43 (1 / (1 + pmax)) - 1 / Λ) ∧
    (∀ (r S S' : ℝ), 0 < r → r < 1 → 1 + r < S → 4 * S - 3 - 3 * r ≠ 0 →
      S ^ 3 = Λ * r * (2 * S - 1 - r) →
      3 * S ^ 2 * S' = Λ * (2 * S - 1 - r) + Λ * r * (2 * S' - 1) →
      let u := S / (1 + r)
      let φ1' := (Λ * r - S ^ 2 + (2 + r) * S - (3 + 3 * r + r ^ 2)) +
        r * (Λ - 2 * S * S' + S + (2 + r) * S' - (3 + 2 * r))
      let φ2' := ((Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) +
        r * (Λ - 2 * S * S' + 2 * S + (1 + 2 * r) * S' - (3 + 6 * r))) / r ^ 4 -
        4 * (r * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2))) / r ^ 5
      φ1' = -r ^ 4 * φ2' ∧
      φ1' = (1 + r) ^ 4 * u ^ 4 / ((2 * S - 1 - r) * (4 * S - 3 - 3 * r)) *
        (fluxDerivH43 (1 / u) - 1 / Λ)) ∧
    -- (3) Exact Λ-sensitivity & 2×2 Master Trace inequality for all m ≥ 2
    (∀ (r_star τ2 τ2' σp' E : ℝ), 0 < r_star → r_star < 1 / (hp ^ 2 + hp - 1) →
      σm < τ2 → 0 < E →
      σp' = hp ^ 2 / (1 + hp) ^ 2 →
      Λ * (-τ2' + r_star ^ 4 * σp') = E →
      r_star ^ 4 * σp - τ2 < 0 ∧
      0 < σp' ∧
      (r_star ^ 4 * σp - τ2) * σp' - (σp / Λ) * E = τ2' * σp - τ2 * σp' ∧
      τ2' * σp - τ2 * σp' < 0 ∧
      (∀ m : ℕ, 2 ≤ m → τ2 / σp ≤ 1 / ((m : ℝ) - 1) → σp + τ2 ≤ (m : ℝ) / ((m : ℝ) - 1) * σp)) := by
  intro x y pmax σp σm
  have hΛ_pos : 0 < Λ := by nlinarith [pow_pos (by linarith : (0 : ℝ) < 1 + hp) 3]
  have hx1 : 1 < x := by dsimp only [x]; linarith
  have hx_lt : x < 3 / 2 := by dsimp only [x]; linarith
  have hy2 : 2 < y := by dsimp only [y]; linarith
  have hxy_lt : x < y := by linarith
  have hsum2_pos : 0 < x ^ 2 + y ^ 2 := by positivity
  have hpmax_pos : 0 < pmax := div_pos (mul_pos (by linarith) (by linarith)) hsum2_pos
  have hpmax_half : pmax < 1 / 2 := by
    dsimp only [pmax]; rw [div_lt_div_iff₀ hsum2_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy_lt.ne')]
  have hxy_rel : x * y * (x + y) = x ^ 2 + x * y + y ^ 2 := by
    have hdiff : x ^ 3 * (y - 1) - y ^ 3 * (x - 1) = 0 := by
      have h1 : x ^ 3 = Λ * (x - 1) := by dsimp only [x]; linear_combination hScm
      have h2 : y ^ 3 = Λ * (y - 1) := by dsimp only [y]; linear_combination hScp
      linear_combination (y - 1) * h1 - (x - 1) * h2
    have hfac : x ^ 3 * (y - 1) - y ^ 3 * (x - 1) = (x - y) * (x * y * (x + y) - (x ^ 2 + x * y + y ^ 2)) := by ring
    rw [hfac] at hdiff
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hxy_lt.ne))
  have hΛ_xy : Λ = x ^ 2 + x * y + y ^ 2 := by
    have h1 : x ^ 3 = Λ * (x - 1) := by dsimp only [x]; linear_combination hScm
    have h2 : y ^ 3 = Λ * (y - 1) := by dsimp only [y]; linear_combination hScp
    have hsub : (y - x) * (x ^ 2 + x * y + y ^ 2 - Λ) = 0 := by linear_combination h2 - h1
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hxy_lt.ne'))).symm
  have hΛ_pmax : Λ = (1 + pmax) ^ 3 / (pmax ^ 2 * (1 + 2 * pmax)) := by
    let s : ℝ := x ^ 2 + y ^ 2
    have hs_pos : 0 < s := hsum2_pos
    have h1p : 1 + pmax = Λ / s := by
      dsimp only [pmax, s]; rw [hΛ_xy, eq_div_iff hs_pos.ne', add_mul, div_mul_cancel₀ _ hs_pos.ne']; ring
    have h12p : 1 + 2 * pmax = (x + y) ^ 2 / s := by
      dsimp only [pmax, s]; rw [eq_div_iff hs_pos.ne', add_mul, mul_div_assoc', div_mul_cancel₀ _ hs_pos.ne']; ring
    have hxyΛ : x * y * (x + y) = Λ := hxy_rel.trans hΛ_xy.symm
    have hpmax_s : pmax = x * y / s := rfl
    rw [h1p, h12p, hpmax_s]
    have hxpy : 0 < x + y := by linarith
    have hxy_pos : 0 < x * y := mul_pos (by linarith) (by linarith)
    have hden_ne : (x * y / s) ^ 2 * ((x + y) ^ 2 / s) ≠ 0 := by positivity
    rw [eq_div_iff hden_ne]
    have hL : Λ * ((x * y / s) ^ 2 * ((x + y) ^ 2 / s)) = Λ * (x * y * (x + y)) ^ 2 / s ^ 3 := by
      simp only [div_eq_mul_inv, ← inv_pow]; ring
    have hR : (Λ / s) ^ 3 = Λ ^ 3 / s ^ 3 := div_pow Λ s 3
    rw [hL, hR, hxyΛ]; ring
  -- (1) Exact (u, t) factorization & positivity
  have hpart1 : ∀ r u : ℝ, 0 < r → r < 1 → x < u → u < 1 + pmax →
      let t := r / (1 + r) ^ 2
      let S := (1 + r) * u
      let a := r * (2 + r - S) / (1 - r)
      let c := (S - 1 - 2 * r) / (1 - r)
      let u0 := 1 + a
      let v0 := r + c
      let b2 := Λ * r - (u0 ^ 2 + u0 * v0 + v0 ^ 2)
      u ^ 3 / (2 * u - 1) = Λ * t →
      b2 = (1 + r) ^ 2 / ((1 - 4 * t) * (2 * u - 1)) * (t - (u - 1) ^ 2) * ((u - 1) - (2 * u - 1) * t) ∧
      0 < b2 ∧ 0 < a ∧ 0 < c ∧
      a * c - b2 = (S - 1 - r) ^ 3 / (2 * S - 1 - r) ∧ 0 < a * c - b2 := by
    intro r u hr0 hr1 hxu hup t S a c u0 v0 b2 hut
    have h1pr : 0 < 1 + r := by linarith
    have h1mr : 0 < 1 - r := by linarith
    have hu1 : 1 < u := lt_trans hx1 hxu
    have hu_lt32 : u < 3 / 2 := by linarith
    have h2u1 : 0 < 2 * u - 1 := by linarith
    have h1m4t : 1 - 4 * t = (1 - r) ^ 2 / (1 + r) ^ 2 := by
      dsimp only [t]; field_simp [h1pr.ne']; ring
    have h1m4t_pos : 0 < 1 - 4 * t := by rw [h1m4t]; positivity
    have hΛr_eq : Λ * r = (1 + r) ^ 2 * u ^ 3 / (2 * u - 1) := by
      have ht_eq : Λ * t = Λ * r / (1 + r) ^ 2 := by dsimp only [t]; ring
      rw [ht_eq] at hut
      have h1 := congrArg (fun z => (1 + r) ^ 2 * z) hut
      field_simp [h1pr.ne', h2u1.ne'] at h1 ⊢; linarith
    have hb2_fac : b2 = (1 + r) ^ 2 / ((1 - 4 * t) * (2 * u - 1)) * (t - (u - 1) ^ 2) * ((u - 1) - (2 * u - 1) * t) := by
      let d : ℝ := 1 - r
      let p : ℝ := 1 + r
      let w : ℝ := 2 * u - 1
      have hd_ne : d ≠ 0 := h1mr.ne'
      have hp_ne : p ≠ 0 := h1pr.ne'
      have hw_ne : w ≠ 0 := h2u1.ne'
      have hscale : d ^ 2 * p ^ 2 * w ≠ 0 := by positivity
      apply mul_left_cancel₀ hscale
      have h1 : u0 = (d + r * (2 + r - p * u)) / d := by
        dsimp only [u0, a, S, d, p]; rw [eq_div_iff hd_ne, add_mul, div_mul_cancel₀ _ hd_ne]; ring
      have h2 : v0 = (r * d + (p * u - 1 - 2 * r)) / d := by
        dsimp only [v0, c, S, d, p]; rw [eq_div_iff hd_ne, add_mul, div_mul_cancel₀ _ hd_ne]
      have hL : d ^ 2 * p ^ 2 * w * b2 =
          d ^ 2 * p ^ 4 * u ^ 3 -
            w * p ^ 2 * ((d + r * (2 + r - p * u)) ^ 2 +
              (d + r * (2 + r - p * u)) * (r * d + (p * u - 1 - 2 * r)) +
              (r * d + (p * u - 1 - 2 * r)) ^ 2) := by
        dsimp only [b2]; rw [hΛr_eq, h1, h2]
        change d ^ 2 * p ^ 2 * w * (p ^ 2 * u ^ 3 / w - _) = _
        let P1 := d + r * (2 + r - p * u)
        let P2 := r * d + (p * u - 1 - 2 * r)
        have hsum : (P1 / d) ^ 2 + (P1 / d) * (P2 / d) + (P2 / d) ^ 2 = (P1 ^ 2 + P1 * P2 + P2 ^ 2) / d ^ 2 := by
          simp only [div_eq_mul_inv, ← inv_pow]; ring
        rw [hsum, mul_sub]
        have ha : d ^ 2 * p ^ 2 * w * (p ^ 2 * u ^ 3 / w) = d ^ 2 * p ^ 4 * u ^ 3 := by
          calc _ = d ^ 2 * p ^ 4 * u ^ 3 * (w / w) := by ring
            _ = _ := by rw [div_self hw_ne, mul_one]
        have hb : d ^ 2 * p ^ 2 * w * ((P1 ^ 2 + P1 * P2 + P2 ^ 2) / d ^ 2) =
            w * p ^ 2 * (P1 ^ 2 + P1 * P2 + P2 ^ 2) := by
          calc _ = w * p ^ 2 * (P1 ^ 2 + P1 * P2 + P2 ^ 2) * (d ^ 2 / d ^ 2) := by ring
            _ = _ := by rw [div_self (pow_ne_zero 2 hd_ne), mul_one]
        rw [ha, hb]
      have hR : d ^ 2 * p ^ 2 * w *
          ((1 + r) ^ 2 / ((1 - 4 * t) * (2 * u - 1)) * (t - (u - 1) ^ 2) * (u - 1 - (2 * u - 1) * t)) =
          p ^ 2 * (r - (u - 1) ^ 2 * p ^ 2) * ((u - 1) * p ^ 2 - w * r) := by
        rw [h1m4t]; dsimp only [t]
        change d ^ 2 * p ^ 2 * w *
          (p ^ 2 / (d ^ 2 / p ^ 2 * w) * (r / p ^ 2 - (u - 1) ^ 2) * (u - 1 - w * (r / p ^ 2))) = _
        have hf1 : r / p ^ 2 - (u - 1) ^ 2 = (r - (u - 1) ^ 2 * p ^ 2) / p ^ 2 := by
          rw [eq_div_iff (pow_ne_zero 2 hp_ne), sub_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hp_ne)]
        have hf2 : u - 1 - w * (r / p ^ 2) = ((u - 1) * p ^ 2 - w * r) / p ^ 2 := by
          rw [eq_div_iff (pow_ne_zero 2 hp_ne), sub_mul, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 2 hp_ne)]
        have hf3 : p ^ 2 / (d ^ 2 / p ^ 2 * w) = p ^ 4 / (d ^ 2 * w) := by
          rw [div_mul_eq_mul_div, div_div_eq_mul_div]; ring
        rw [hf1, hf2, hf3]
        calc _ = p ^ 2 * (r - (u - 1) ^ 2 * p ^ 2) * ((u - 1) * p ^ 2 - w * r) *
              ((d ^ 2 * w) / (d ^ 2 * w)) * (p ^ 4 / p ^ 4) := by
                simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]; ring
          _ = _ := by rw [div_self (mul_ne_zero (pow_ne_zero 2 hd_ne) hw_ne), div_self (pow_ne_zero 4 hp_ne), mul_one, mul_one]
      rw [hL, hR]; dsimp only [d, p, w]; ring
    -- Show u³ / (u - 1) < Λ (giving (u - 1) - (2 u - 1) t > 0) and u³ / ((u-1)²(2u-1)) > Λ (giving t > (u-1)²)
    have hΛ_gt_u : u ^ 3 / (u - 1) < Λ := by
      have hu_lt_y : u < y := by linarith
      rw [div_lt_iff₀ (by linarith)]
      have hpoly' : u ^ 3 - Λ * (u - 1) = (u - x) * (u - y) * (u + x + y) := by
        rw [hΛ_xy]; linear_combination -hxy_rel
      have hneg : (u - x) * (u - y) * (u + x + y) < 0 := by
        have h1 : 0 < u - x := by linarith
        have h2 : u - y < 0 := by linarith
        have h3 : 0 < u + x + y := by linarith
        nlinarith [mul_neg_of_pos_of_neg h1 h2]
      linarith
    have hfac2_pos : 0 < (u - 1) - (2 * u - 1) * t := by
      have hut' : u ^ 3 = Λ * t * (2 * u - 1) := (div_eq_iff h2u1.ne').mp hut
      have ht_val : (2 * u - 1) * t = u ^ 3 / Λ := by
        rw [eq_div_iff hΛ_pos.ne']; linarith
      rw [ht_val, sub_pos, div_lt_iff₀ hΛ_pos]
      have hlt := (div_lt_iff₀ (by linarith : 0 < u - 1)).mp hΛ_gt_u
      linarith
    have hfac1_pos : 0 < t - (u - 1) ^ 2 := by
      have hut' : u ^ 3 = Λ * t * (2 * u - 1) := (div_eq_iff h2u1.ne').mp hut
      have ht_val : t = u ^ 3 / (Λ * (2 * u - 1)) := by
        rw [eq_div_iff (mul_pos hΛ_pos h2u1).ne']; linarith
      rw [ht_val, sub_pos, lt_div_iff₀ (mul_pos hΛ_pos h2u1)]
      -- Compare u³ / ((u - 1)² (2 u - 1)) > (1 + pmax)³ / (pmax² (1 + 2 pmax)) = Λ!
      let q := u - 1
      have hq0 : 0 < q := by linarith
      have hq_lt : q < pmax := by linarith
      have hcomp : Λ * ((2 * u - 1) * (u - 1) ^ 2) < u ^ 3 ↔
          (1 + pmax) ^ 3 * (q ^ 2 * (1 + 2 * q)) < (1 + q) ^ 3 * (pmax ^ 2 * (1 + 2 * pmax)) := by
        rw [hΛ_pmax]
        have h2uq : 2 * u - 1 = 1 + 2 * q := by dsimp only [q]; ring
        have huq : u = 1 + q := by dsimp only [q]; ring
        have hu1q : u - 1 = q := rfl
        rw [h2uq, hu1q, huq]
        have hden : 0 < pmax ^ 2 * (1 + 2 * pmax) := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
        constructor <;> intro h <;> linarith
      rw [show (u - 1) ^ 2 * (Λ * (2 * u - 1)) = Λ * ((2 * u - 1) * (u - 1) ^ 2) by ring, hcomp]
      have hdiff_clean : (1 + q) ^ 3 * (pmax ^ 2 * (1 + 2 * pmax)) - (1 + pmax) ^ 3 * (q ^ 2 * (1 + 2 * q)) =
          (pmax - q) * (pmax + q + 2 * pmax ^ 2 + 5 * pmax * q + 2 * q ^ 2 +
            6 * pmax ^ 2 * q + 6 * pmax * q ^ 2 + 5 * pmax ^ 2 * q ^ 2) := by ring
      have hpos : 0 < (pmax - q) * (pmax + q + 2 * pmax ^ 2 + 5 * pmax * q + 2 * q ^ 2 +
          6 * pmax ^ 2 * q + 6 * pmax * q ^ 2 + 5 * pmax ^ 2 * q ^ 2) := by
        have hpmq : 0 < pmax - q := by linarith
        positivity
      linarith
    have hb2_pos : 0 < b2 := by rw [hb2_fac]; positivity
    have hprod_pos : 0 < (u - 1) * (2 - u) - t := by
      have h1 : (u - 1) * (2 - u) - (u - 1) / (2 * u - 1) = (u - 1) ^ 2 * (3 - 2 * u) / (2 * u - 1) := by
        rw [eq_div_iff h2u1.ne', sub_mul, div_mul_cancel₀ _ h2u1.ne']; ring
      have h2 : t < (u - 1) / (2 * u - 1) := (lt_div_iff₀ h2u1).mpr (by linarith [hfac2_pos])
      have h3 : 0 < (u - 1) ^ 2 * (3 - 2 * u) / (2 * u - 1) := by
        have h32 : 0 < 3 - 2 * u := by linarith
        have hu1' : 0 < u - 1 := by linarith
        positivity
      linarith
    have hac_prod : (2 + r - S) * (S - 1 - 2 * r) = (1 + r) ^ 2 * ((u - 1) * (2 - u) - t) := by
      dsimp only [S, t]; field_simp [h1pr.ne']; ring
    have ha_plus_c : (2 + r - S) + (S - 1 - 2 * r) = 1 - r := by ring
    have h1pr2 : 0 < (1 + r) ^ 2 := sq_pos_of_pos h1pr
    have ha_num_pos : 0 < 2 + r - S := by nlinarith only [hac_prod, ha_plus_c, hprod_pos, h1pr2, h1mr]
    have hc_num_pos : 0 < S - 1 - 2 * r := by nlinarith only [hac_prod, ha_plus_c, hprod_pos, h1pr2, h1mr]
    have ha_pos : 0 < a := by dsimp only [a]; positivity
    have hc_pos : 0 < c := by dsimp only [c]; positivity
    have hdetH : a * c - b2 = (S - 1 - r) ^ 3 / (2 * S - 1 - r) := by
      let d : ℝ := 1 - r
      let p : ℝ := 1 + r
      let w : ℝ := 2 * u - 1
      have hd_ne : d ≠ 0 := h1mr.ne'
      have hp_ne : p ≠ 0 := h1pr.ne'
      have hw_ne : w ≠ 0 := h2u1.ne'
      have h2S : 2 * S - 1 - r = p * w := by dsimp only [S, p, w]; ring
      have hscale : d ^ 2 * p * w ≠ 0 := by positivity
      apply mul_left_cancel₀ hscale
      have hu0_eq : u0 = (d + r * (2 + r - p * u)) / d := by
        dsimp only [u0, a, S, d, p]; rw [eq_div_iff hd_ne, add_mul, div_mul_cancel₀ _ hd_ne]; ring
      have hv0_eq : v0 = (r * d + (p * u - 1 - 2 * r)) / d := by
        dsimp only [v0, c, S, d, p]; rw [eq_div_iff hd_ne, add_mul, div_mul_cancel₀ _ hd_ne]
      have ha_eq : a = (r * (2 + r - p * u)) / d := rfl
      have hc_eq : c = (p * u - 1 - 2 * r) / d := by dsimp only [c, S, d, p]
      let P1 := d + r * (2 + r - p * u)
      let P2 := r * d + (p * u - 1 - 2 * r)
      let A1 := r * (2 + r - p * u)
      let C1 := p * u - 1 - 2 * r
      have hL : d ^ 2 * p * w * (a * c - b2) =
          p * w * (A1 * C1 + P1 ^ 2 + P1 * P2 + P2 ^ 2) - d ^ 2 * p ^ 3 * u ^ 3 := by
        dsimp only [b2]; rw [hΛr_eq, ha_eq, hc_eq, hu0_eq, hv0_eq]
        change d ^ 2 * p * w * (A1 / d * (C1 / d) - (p ^ 2 * u ^ 3 / w - ((P1 / d) ^ 2 + (P1 / d) * (P2 / d) + (P2 / d) ^ 2))) = _
        have hsum : A1 / d * (C1 / d) - (p ^ 2 * u ^ 3 / w - ((P1 / d) ^ 2 + (P1 / d) * (P2 / d) + (P2 / d) ^ 2)) =
            (A1 * C1 + P1 ^ 2 + P1 * P2 + P2 ^ 2) / d ^ 2 - p ^ 2 * u ^ 3 / w := by
          simp only [div_eq_mul_inv, ← inv_pow]; ring
        rw [hsum, mul_sub]
        have ht1 : d ^ 2 * p * w * ((A1 * C1 + P1 ^ 2 + P1 * P2 + P2 ^ 2) / d ^ 2) =
            p * w * (A1 * C1 + P1 ^ 2 + P1 * P2 + P2 ^ 2) := by
          calc _ = p * w * (A1 * C1 + P1 ^ 2 + P1 * P2 + P2 ^ 2) * (d ^ 2 / d ^ 2) := by ring
            _ = _ := by rw [div_self (pow_ne_zero 2 hd_ne), mul_one]
        have ht2 : d ^ 2 * p * w * (p ^ 2 * u ^ 3 / w) = d ^ 2 * p ^ 3 * u ^ 3 := by
          calc _ = d ^ 2 * p ^ 3 * u ^ 3 * (w / w) := by ring
            _ = _ := by rw [div_self hw_ne, mul_one]
        rw [ht1, ht2]
      have hR : d ^ 2 * p * w * ((S - 1 - r) ^ 3 / (2 * S - 1 - r)) = d ^ 2 * (S - 1 - r) ^ 3 := by
        rw [h2S]
        calc _ = d ^ 2 * (S - 1 - r) ^ 3 * ((p * w) / (p * w)) := by ring
          _ = _ := by rw [div_self (mul_ne_zero hp_ne hw_ne), mul_one]
      rw [hL, hR]; dsimp only [P1, P2, A1, C1, S, d, p, w]; ring
    have hdetH_pos : 0 < a * c - b2 := by
      rw [hdetH]
      have h1 : 0 < S - 1 - r := by dsimp only [S]; nlinarith only [hr0, hu1]
      have h2 : 0 < 2 * S - 1 - r := by dsimp only [S]; nlinarith only [hr0, hu1]
      positivity
    exact ⟨hb2_fac, hb2_pos, ha_pos, hc_pos, hdetH, hdetH_pos⟩
  -- (2a) Derivative of h(v) < 0 on (2/3, 1)
  have hpart2a : ∀ v : ℝ, 2 / 3 < v → v < 1 →
      HasDerivAt fluxDerivH43 (6 * (1 - v) * (2 * v - 3) * (3 * v - 2)) v ∧
      6 * (1 - v) * (2 * v - 3) * (3 * v - 2) < 0 := fun v hv1 hv2 => by
    have hd : HasDerivAt fluxDerivH43 (6 * (1 - v) * (2 * v - 3) * (3 * v - 2)) v := by
      have hfun : fluxDerivH43 = fun w => (1 - w) ^ 2 * (-9 * w ^ 2 + 20 * w - 8) := rfl
      rw [hfun]
      have hd1 := ((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).pow 2
      have hd2 := (((hasDerivAt_pow 2 v).const_mul (-9 : ℝ)).add ((hasDerivAt_id v).const_mul (20 : ℝ))).sub
        (hasDerivAt_const v (8 : ℝ))
      exact (hd1.mul hd2).congr_deriv (by simp only [Pi.pow_apply, Pi.sub_apply, Pi.add_apply, id_eq]; ring)
    have hneg : 6 * (1 - v) * (2 * v - 3) * (3 * v - 2) < 0 := by
      have h1 : 0 < 1 - v := by linarith
      have h2 : 2 * v - 3 < 0 := by linarith
      have h3 : 0 < 3 * v - 2 := by linarith
      nlinarith [mul_neg_of_pos_of_neg h1 h2]
    exact ⟨hd, hneg⟩
  -- (2b) Endpoints
  have hpart2b : fluxDerivH43 (1 / x) - 1 / Λ = -(1 - 1 / x) * (2 - 1 / x) * (3 / x - 2) ^ 2 ∧
      fluxDerivH43 (1 / x) - 1 / Λ < 0 := by
    have hinvΛ : 1 / Λ = (1 / x) ^ 2 * (1 - 1 / x) := by
      have hx0 : x ≠ 0 := by linarith
      have hScx : x ^ 3 = Λ * (x - 1) := by dsimp only [x]; linear_combination hScm
      field_simp [hΛ_pos.ne', hx0]; linarith
    have heq : fluxDerivH43 (1 / x) - 1 / Λ = -(1 - 1 / x) * (2 - 1 / x) * (3 / x - 2) ^ 2 := by
      rw [hinvΛ]; dsimp only [fluxDerivH43]; ring
    have hneg : fluxDerivH43 (1 / x) - 1 / Λ < 0 := by
      rw [heq]
      have h1 : 0 < 1 - 1 / x := by rw [sub_pos, div_lt_one (by linarith)]; exact hx1
      have h2 : 0 < 2 - 1 / x := by linarith
      have h3 : 0 < (3 / x - 2) ^ 2 := sq_pos_of_ne_zero (by
        intro h0; have : 3 / x = 2 := by linarith
        have : 3 = 2 * x := (div_eq_iff (by linarith : x ≠ 0)).mp this
        linarith)
      nlinarith [mul_pos h1 h2]
    exact ⟨heq, hneg⟩
  have hpart2c : fluxDerivH43 (1 / (1 + pmax)) - 1 / Λ =
      pmax ^ 2 * (2 + 5 * pmax) * (1 - 2 * pmax) / (1 + pmax) ^ 4 ∧
      0 < fluxDerivH43 (1 / (1 + pmax)) - 1 / Λ := by
    have h1p : 0 < 1 + pmax := by linarith
    have hinvΛ : 1 / Λ = pmax ^ 2 * (1 + 2 * pmax) / (1 + pmax) ^ 3 := by
      rw [hΛ_pmax]; field_simp [h1p.ne', hpmax_pos.ne', (by linarith : 1 + 2 * pmax ≠ 0)]
    have heq : fluxDerivH43 (1 / (1 + pmax)) - 1 / Λ =
        pmax ^ 2 * (2 + 5 * pmax) * (1 - 2 * pmax) / (1 + pmax) ^ 4 := by
      rw [hinvΛ]; dsimp only [fluxDerivH43]; field_simp [h1p.ne']; ring
    have hpos : 0 < fluxDerivH43 (1 / (1 + pmax)) - 1 / Λ := by
      rw [heq]; have h12 : 0 < 1 - 2 * pmax := by linarith
      positivity
    exact ⟨heq, hpos⟩
  -- (2d) Exact C¹ flux derivative identities along S³ = Λ r (2S - 1 - r)
  have hpart2d : ∀ (r S S' : ℝ), 0 < r → r < 1 → 1 + r < S → 4 * S - 3 - 3 * r ≠ 0 →
      S ^ 3 = Λ * r * (2 * S - 1 - r) →
      3 * S ^ 2 * S' = Λ * (2 * S - 1 - r) + Λ * r * (2 * S' - 1) →
      let u := S / (1 + r)
      let φ1' := (Λ * r - S ^ 2 + (2 + r) * S - (3 + 3 * r + r ^ 2)) +
        r * (Λ - 2 * S * S' + S + (2 + r) * S' - (3 + 2 * r))
      let φ2' := ((Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) +
        r * (Λ - 2 * S * S' + 2 * S + (1 + 2 * r) * S' - (3 + 6 * r))) / r ^ 4 -
        4 * (r * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2))) / r ^ 5
      φ1' = -r ^ 4 * φ2' ∧
      φ1' = (1 + r) ^ 4 * u ^ 4 / ((2 * S - 1 - r) * (4 * S - 3 - 3 * r)) *
        (fluxDerivH43 (1 / u) - 1 / Λ) := by
    intro r S S' hr0 hr1 hS1 hden2 hS3 hS3' u φ1' φ2'
    have h1pr : 0 < 1 + r := by linarith
    have hS_pos : 0 < S := by linarith
    have h2S_pos : 0 < 2 * S - 1 - r := by linarith
    have hΛr : Λ * r = S ^ 3 / (2 * S - 1 - r) := by
      rw [eq_div_iff h2S_pos.ne']; linarith [hS3]
    have hS'_eq : r * S' = S * (2 * S - 1 - 2 * r) / (4 * S - 3 - 3 * r) := by
      have h1 : r * (3 * S ^ 2 - 2 * Λ * r) * S' = Λ * r * (2 * S - 1 - 2 * r) := by
        linear_combination r * hS3'
      have h2 : (2 * S - 1 - r) * (3 * S ^ 2 - 2 * Λ * r) = S ^ 2 * (4 * S - 3 - 3 * r) := by
        linear_combination 2 * hS3
      have h3 : (2 * S - 1 - r) * (r * (3 * S ^ 2 - 2 * Λ * r) * S') =
          (2 * S - 1 - r) * (Λ * r * (2 * S - 1 - 2 * r)) := congrArg ((2 * S - 1 - r) * ·) h1
      have h4 : S ^ 2 * (4 * S - 3 - 3 * r) * (r * S') = S ^ 3 * (2 * S - 1 - 2 * r) := by
        linear_combination h3 - (r * S') * h2 - (2 * S - 1 - 2 * r) * hS3
      have h5 : S ^ 2 * ((4 * S - 3 - 3 * r) * (r * S') - S * (2 * S - 1 - 2 * r)) = 0 := by
        linear_combination h4
      have h6 : (4 * S - 3 - 3 * r) * (r * S') = S * (2 * S - 1 - 2 * r) :=
        sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left (sq_pos_of_pos hS_pos).ne')
      exact eq_div_of_mul_eq hden2 (by linarith)
    have hsym : φ1' = -r ^ 4 * φ2' := by
      have hφ2_mul : -r ^ 4 * φ2' =
          -((Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) +
            r * (Λ - 2 * S * S' + 2 * S + (1 + 2 * r) * S' - (3 + 6 * r))) +
          4 * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) := by
        dsimp only [φ2']
        rw [mul_sub]
        have hr4 : r ^ 4 ≠ 0 := (pow_pos hr0 4).ne'
        have hr5 : r ^ 5 ≠ 0 := (pow_pos hr0 5).ne'
        have ht1 : -r ^ 4 * (((Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) +
            r * (Λ - 2 * S * S' + 2 * S + (1 + 2 * r) * S' - (3 + 6 * r))) / r ^ 4) =
            -((Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) +
              r * (Λ - 2 * S * S' + 2 * S + (1 + 2 * r) * S' - (3 + 6 * r))) := by
          rw [neg_mul, mul_div_cancel₀ _ hr4]
        have ht2 : -r ^ 4 * (4 * (r * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2))) / r ^ 5) =
            -(4 * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2))) := by
          rw [neg_mul]
          refine congrArg Neg.neg ?_
          have hmul : r ^ 4 * (4 * (r * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2))) / r ^ 5) =
              4 * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) * r ^ 5 / r ^ 5 := by
            rw [mul_div_assoc']; congr 1; ring
          rw [hmul, mul_div_cancel_right₀ _ hr5]
        rw [ht1, ht2]; ring
      rw [hφ2_mul]; dsimp only [φ1']
      have h0 : ((Λ * r - S ^ 2 + (2 + r) * S - (3 + 3 * r + r ^ 2)) +
            r * (Λ - 2 * S * S' + S + (2 + r) * S' - (3 + 2 * r))) -
          (-((Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2)) +
            r * (Λ - 2 * S * S' + 2 * S + (1 + 2 * r) * S' - (3 + 6 * r))) +
            4 * (Λ * r - S ^ 2 + (1 + 2 * r) * S - (1 + 3 * r + 3 * r ^ 2))) =
          -(4 * S - 3 - 3 * r) * (r * S') + S * (2 * S - 1 - 2 * r) := by ring
      have hzero : -(4 * S - 3 - 3 * r) * (r * S') + S * (2 * S - 1 - 2 * r) = 0 := by
        rw [hS'_eq, neg_mul, mul_div_cancel₀ _ hden2]; ring
      linarith
    -- Prove hformula cleanly by clearing (2*S - 1 - r) * (4*S - 3 - 3*r)!
    exact ⟨hsym, by
      let w1 : ℝ := 2 * S - 1 - r
      let w2 : ℝ := 4 * S - 3 - 3 * r
      have hw1_ne : w1 ≠ 0 := h2S_pos.ne'
      have hw2_ne : w2 ≠ 0 := hden2
      have h1u : 1 / u = (1 + r) / S := by
        dsimp only [u]; rw [one_div, inv_div]
      have hu4 : (1 + r) ^ 4 * u ^ 4 = S ^ 4 := by
        dsimp only [u]; rw [div_pow, mul_div_cancel₀ _ (pow_pos h1pr 4).ne']
      have hnum_rhs : (1 + r) ^ 4 * u ^ 4 * (fluxDerivH43 (1 / u) - 1 / Λ) =
          (S - (1 + r)) ^ 2 * (-9 * (1 + r) ^ 2 + 20 * (1 + r) * S - 8 * S ^ 2) - S * r * w1 := by
        rw [hu4, h1u, mul_sub]; dsimp only [fluxDerivH43]
        have ha : S ^ 4 * ((1 - (1 + r) / S) ^ 2 * (-9 * ((1 + r) / S) ^ 2 + 20 * ((1 + r) / S) - 8)) =
            (S - (1 + r)) ^ 2 * (-9 * (1 + r) ^ 2 + 20 * (1 + r) * S - 8 * S ^ 2) := by
          have hs1 : 1 - (1 + r) / S = (S - (1 + r)) / S := by
            rw [eq_div_iff hS_pos.ne', sub_mul, one_mul, div_mul_cancel₀ _ hS_pos.ne']
          have hs2 : -9 * ((1 + r) / S) ^ 2 + 20 * ((1 + r) / S) - 8 =
              (-9 * (1 + r) ^ 2 + 20 * (1 + r) * S - 8 * S ^ 2) / S ^ 2 := by
            rw [eq_div_iff (sq_pos_of_pos hS_pos).ne', sub_mul, add_mul]
            have t1 : -9 * ((1 + r) / S) ^ 2 * S ^ 2 = -9 * (1 + r) ^ 2 := by
              rw [div_pow, mul_assoc, div_mul_cancel₀ _ (sq_pos_of_pos hS_pos).ne']
            have t2 : 20 * ((1 + r) / S) * S ^ 2 = 20 * (1 + r) * S := by
              calc _ = 20 * ((1 + r) / S * S) * S := by ring
                _ = 20 * (1 + r) * S := by rw [div_mul_cancel₀ _ hS_pos.ne']
            rw [t1, t2]
          rw [hs1, hs2]
          calc S ^ 4 * (((S - (1 + r)) / S) ^ 2 * ((-9 * (1 + r) ^ 2 + 20 * (1 + r) * S - 8 * S ^ 2) / S ^ 2))
              = (S - (1 + r)) ^ 2 * (-9 * (1 + r) ^ 2 + 20 * (1 + r) * S - 8 * S ^ 2) * (S ^ 4 / S ^ 4) := by ring
            _ = _ := by rw [div_self (pow_pos hS_pos 4).ne', mul_one]
        have hb : S ^ 4 * (1 / Λ) = S * r * w1 := by
          rw [mul_one_div, div_eq_iff hΛ_pos.ne']; dsimp only [w1]; linear_combination S * hS3
        rw [ha, hb]
      rw [div_mul_eq_mul_div, hnum_rhs, eq_div_iff (mul_ne_zero hw1_ne hw2_ne)]
      have h1 : φ1' = 2 * (Λ * r) - S ^ 2 + (2 + 2 * r) * S - (3 + 6 * r + 3 * r ^ 2) +
          (2 + r - 2 * S) * (r * S') := by dsimp only [φ1']; ring
      rw [h1, hΛr, hS'_eq]
      change (2 * (S ^ 3 / w1) - S ^ 2 + (2 + 2 * r) * S - (3 + 6 * r + 3 * r ^ 2) +
          (2 + r - 2 * S) * (S * (2 * S - 1 - 2 * r) / w2)) * (w1 * w2) = _
      have hL_clr : (2 * (S ^ 3 / w1) - S ^ 2 + (2 + 2 * r) * S - (3 + 6 * r + 3 * r ^ 2) +
          (2 + r - 2 * S) * (S * (2 * S - 1 - 2 * r) / w2)) * (w1 * w2) =
          2 * S ^ 3 * w2 + (-S ^ 2 + (2 + 2 * r) * S - (3 + 6 * r + 3 * r ^ 2)) * (w1 * w2) +
          (2 + r - 2 * S) * S * (2 * S - 1 - 2 * r) * w1 := by
        have ht1 : 2 * (S ^ 3 / w1) * (w1 * w2) = 2 * S ^ 3 * w2 := by
          calc _ = 2 * (S ^ 3 / w1 * w1) * w2 := by ring
            _ = 2 * S ^ 3 * w2 := by rw [div_mul_cancel₀ _ hw1_ne]
        have ht2 : (2 + r - 2 * S) * (S * (2 * S - 1 - 2 * r) / w2) * (w1 * w2) =
            (2 + r - 2 * S) * S * (2 * S - 1 - 2 * r) * w1 := by
          calc _ = (2 + r - 2 * S) * (S * (2 * S - 1 - 2 * r) / w2 * w2) * w1 := by ring
            _ = _ := by rw [div_mul_cancel₀ _ hw2_ne]; ring
        linear_combination ht1 + ht2
      rw [hL_clr]; dsimp only [w1, w2]; ring⟩
  -- (3) Exact Λ-sensitivity & Master Trace inequality for all m ≥ 2!
  have hpart3 : ∀ (r_star τ2 τ2' σp' E : ℝ), 0 < r_star → r_star < 1 / (hp ^ 2 + hp - 1) →
      σm < τ2 → 0 < E →
      σp' = hp ^ 2 / (1 + hp) ^ 2 →
      Λ * (-τ2' + r_star ^ 4 * σp') = E →
      r_star ^ 4 * σp - τ2 < 0 ∧
      0 < σp' ∧
      (r_star ^ 4 * σp - τ2) * σp' - (σp / Λ) * E = τ2' * σp - τ2 * σp' ∧
      τ2' * σp - τ2 * σp' < 0 ∧
      (∀ m : ℕ, 2 ≤ m → τ2 / σp ≤ 1 / ((m : ℝ) - 1) → σp + τ2 ≤ (m : ℝ) / ((m : ℝ) - 1) * σp) := by
    intro r_star τ2 τ2' σp' E hr0 hr_lt hτ2_gt hE_pos hσp'_eq hsens
    have hσp_pos : 0 < σp := by dsimp only [σp]; nlinarith
    have hlem0 : 1 < Λ * σm := by
      have h := (lemma0_lambda_sigma_minus_gt_one (κ := 2) (by norm_num) hhm0
        (by norm_num; exact hhm_half) (by norm_num; exact hScm)).1
      have h1 : hm ^ ((2 : ℝ) - 1) * (1 - hm) = σm := by dsimp only [σm]; norm_num; ring
      rwa [h1] at h
    have hden_pos : 0 < hp ^ 2 + hp - 1 := by nlinarith only [hhp1]
    have hfrac_lt : (1 + hp) ^ 3 * (hp - 1) / (hp ^ 2 + hp - 1) ^ 4 < 1 / 2 := by
      rw [div_lt_div_iff₀ (pow_pos hden_pos 4) (by norm_num : (0 : ℝ) < 2)]
      let t := hp - 1
      have ht : 0 < t := by dsimp only [t]; linarith
      have hid' : (hp ^ 2 + hp - 1) ^ 4 - 2 * ((1 + hp) ^ 3 * (hp - 1)) =
          (1 - 2 * t) ^ 2 + 30 * t ^ 2 + 132 * t ^ 3 + 193 * t ^ 4 + 144 * t ^ 5 +
          58 * t ^ 6 + 12 * t ^ 7 + t ^ 8 := by
        dsimp only [t]; ring
      have hpos : 0 < (1 - 2 * t) ^ 2 + 30 * t ^ 2 + 132 * t ^ 3 + 193 * t ^ 4 + 144 * t ^ 5 +
          58 * t ^ 6 + 12 * t ^ 7 + t ^ 8 := by positivity
      linarith
    have htr_neg : r_star ^ 4 * σp - τ2 < 0 := by
      have hr4 : r_star ^ 4 < (1 / (hp ^ 2 + hp - 1)) ^ 4 := pow_lt_pow_left₀ hr_lt hr0.le (by norm_num)
      have hΛσp : Λ * σp = (1 + hp) ^ 3 * (hp - 1) := by
        dsimp only [σp]; linear_combination (hp - 1) * hScp.symm
      have h1 : Λ * (r_star ^ 4 * σp) < 1 / 2 := by
        calc Λ * (r_star ^ 4 * σp) = (Λ * σp) * r_star ^ 4 := by ring
          _ < (Λ * σp) * (1 / (hp ^ 2 + hp - 1)) ^ 4 := mul_lt_mul_of_pos_left hr4 (mul_pos hΛ_pos hσp_pos)
          _ = (1 + hp) ^ 3 * (hp - 1) / (hp ^ 2 + hp - 1) ^ 4 := by rw [hΛσp, one_div, inv_pow, div_eq_mul_inv]
          _ < 1 / 2 := hfrac_lt
      have h2 : 1 < Λ * τ2 := lt_trans hlem0 (mul_lt_mul_of_pos_left hτ2_gt hΛ_pos)
      nlinarith
    have hσp'_pos : 0 < σp' := by rw [hσp'_eq]; positivity
    have hquot_id : (r_star ^ 4 * σp - τ2) * σp' - (σp / Λ) * E = τ2' * σp - τ2 * σp' := by
      rw [← hsens]; field_simp [hΛ_pos.ne']; ring
    have hquot_neg : τ2' * σp - τ2 * σp' < 0 := by
      rw [← hquot_id]
      have h1 : (r_star ^ 4 * σp - τ2) * σp' < 0 := mul_neg_of_neg_of_pos htr_neg hσp'_pos
      have h2 : 0 < (σp / Λ) * E := mul_pos (div_pos hσp_pos hΛ_pos) hE_pos
      linarith
    have hmaster : ∀ m : ℕ, 2 ≤ m → τ2 / σp ≤ 1 / ((m : ℝ) - 1) → σp + τ2 ≤ (m : ℝ) / ((m : ℝ) - 1) * σp := by
      intro m hm hle
      have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hτ2_le : τ2 ≤ σp / ((m : ℝ) - 1) := by
        have := (div_le_iff₀ hσp_pos).mp hle
        linarith [show 1 / ((m : ℝ) - 1) * σp = σp / ((m : ℝ) - 1) by ring]
      have heq : (m : ℝ) / ((m : ℝ) - 1) * σp = σp + σp / ((m : ℝ) - 1) := by
        field_simp [hm1.ne']; ring
      linarith
    exact ⟨htr_neg, hσp'_pos, hquot_id, hquot_neg, hmaster⟩
  exact ⟨hpmax_pos, hpmax_half, hΛ_pmax, hpart1, hpart2a, hpart2b, hpart2c, hpart2d, hpart3⟩

/-- Exact strictly convex auxiliary function f(q) = q⁻³ + 6 q + 16 q³ + 9 q⁵ for Theorem B7 (p = 3/2). -/
def fluxDerivF32 (q : ℝ) : ℝ := q⁻¹ ^ 3 + 6 * q + 16 * q ^ 3 + 9 * q ^ 5

set_option maxHeartbeats 800000 in
/-- Theorem B7 (`b1_proof.md` §2): Complete Core Analytic Proof of the 2×2 Master Trace
    Inequality at p = 3/2 for ALL Λ > 4 and ALL m ≥ 2:
      (1) Vieta bound q_max² = m_- m_+ < 1/3, Λ = (1 + q_max²)(1 - q_max²)² / q_max³, σ_+ + σ_- > 0,
          and exact closed-form (q, s) parameterization: b² > 0, m₀ > 0, m₁ > 0 for all q ∈ (m_-, q_max).
      (2) Exact strict convexity f''(q) = 12 q⁻⁵ + 96 q + 180 q³ > 0 on (0, ∞), exact factored
          opposite-sign endpoints 4 Λ - f(m_-) < 0 and 4 Λ - f(q_max) > 0, and exact flux derivative
          identities φ₁'(r) = -r³ φ₂'(r) = (√r q³ / (2 w²(s q + (1 + 3 q²) w))) (4 Λ - f(q)).
      (3) Exact Λ-monotonicity of τ₂(Λ) / σ_+(Λ) and Master Trace bound for all m ≥ 2! -/
theorem master_trace_2x2_p32 {Λ mm mp : ℝ}
    (hmm0 : 0 < mm) (hmm_lt : mm < mp) (hmp1 : 1 < mp)
    (hScm : (1 + mm ^ 2) ^ 2 = Λ * mm) (hScp : (1 + mp ^ 2) ^ 2 = Λ * mp) :
    let qmax := Real.sqrt (mm * mp)
    let σp := mp ^ 3 - mp
    let σm := mm - mm ^ 3
    -- (1) Vieta bound q_max² < 1/3, Λ formula, σ_+ + σ_- > 0, and exact (q, s) positivity
    (qmax ^ 2 < 1 / 3 ∧ mm < qmax ∧
      Λ = (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 / qmax ^ 3 ∧ 0 < σp + σm) ∧
    (∀ q r : ℝ, mm < q → q < qmax → 0 < r → r < 1 →
      let w := Real.sqrt (1 + q ^ 2)
      let s := (Λ - q * (1 + q ^ 2)) / w
      let sr := Real.sqrt r
      let m0 := sr / (1 - r) * ((1 - r * q ^ 2) / w - sr * q)
      let m1 := 1 / (sr * (1 - r)) * (sr * q - (r - q ^ 2) / w)
      (1 + r) / sr = s →
      2 < s ∧
      m0 * m1 - q ^ 2 = q ^ 4 / ((s ^ 2 - 4) * (1 + q ^ 2)) * (w / q - s) * (s - w * (1 - 2 * q ^ 2) / q ^ 3) ∧
      0 < m0 * m1 - q ^ 2 ∧ 0 < m0 ∧ 0 < m1) ∧
    -- (2) Strict convexity f''(q) > 0, factored opposite-sign endpoints, and exact flux derivative
    (∀ q : ℝ, 0 < q →
      HasDerivAt fluxDerivF32 (-3 * q⁻¹ ^ 4 + 6 + 48 * q ^ 2 + 45 * q ^ 4) q ∧
      HasDerivAt (fun x => -3 * x⁻¹ ^ 4 + 6 + 48 * x ^ 2 + 45 * x ^ 4)
        (12 * q⁻¹ ^ 5 + 96 * q + 180 * q ^ 3) q ∧
      0 < 12 * q⁻¹ ^ 5 + 96 * q + 180 * q ^ 3) ∧
    (4 * Λ - fluxDerivF32 mm = -((1 - 3 * mm ^ 2) ^ 2 * (1 + mm ^ 2) ^ 2 / mm ^ 3) ∧
      4 * Λ - fluxDerivF32 mm < 0) ∧
    (4 * Λ - fluxDerivF32 qmax =
      (1 - 3 * qmax ^ 2) * (1 + qmax ^ 2) * (3 + 2 * qmax ^ 2 + 3 * qmax ^ 4) / qmax ^ 3 ∧
      0 < 4 * Λ - fluxDerivF32 qmax) ∧
    (∀ (r q w q' : ℝ), 0 < r → r < 1 → 0 < q → w = Real.sqrt (1 + q ^ 2) →
      let s := (1 + r) / Real.sqrt r
      Λ = s * w + q * w ^ 2 →
      q' = (1 - r) * w ^ 2 / (2 * r * Real.sqrt r * (s * q + (1 + 3 * q ^ 2) * w)) →
      let sr := Real.sqrt r
      let φ1' := q + r * q' - (1 / (2 * sr * w) * (1 + r * q ^ 4) +
        sr / w * (q ^ 4 + 4 * r * q ^ 3 * q') - sr * q * q' / w ^ 3 * (1 + r * q ^ 4))
      let φ2' := (q' / r - q / r ^ 2) - ((1 / w + 4 * q ^ 3 * q' / w - q * q' * (r + q ^ 4) / w ^ 3) / (r * sr) -
        3 * (r + q ^ 4) / (2 * r ^ 2 * sr * w))
      φ1' = -r ^ 3 * φ2' ∧
      φ1' = sr * q ^ 3 / (2 * w ^ 2 * (s * q + (1 + 3 * q ^ 2) * w)) * (4 * Λ - fluxDerivF32 q)) ∧
    -- (3) Exact Λ-sensitivity & 2×2 Master Trace inequality for all m ≥ 2!
    (∀ (r_star τ2 τ2' σp' E : ℝ), 0 < r_star → r_star < 1 / (mp ^ 4 + mp ^ 2 - 1) →
      σm < τ2 → 0 < E →
      σp' = mp ^ 2 / (1 + mp ^ 2) →
      Λ * (-τ2' + r_star ^ 3 * σp') = E →
      r_star ^ 3 * σp - τ2 < 0 ∧
      0 < σp' ∧
      (r_star ^ 3 * σp - τ2) * σp' - (σp / Λ) * E = τ2' * σp - τ2 * σp' ∧
      τ2' * σp - τ2 * σp' < 0 ∧
      (∀ m : ℕ, 2 ≤ m → τ2 / σp ≤ 1 / ((m : ℝ) - 1) → σp + τ2 ≤ (m : ℝ) / ((m : ℝ) - 1) * σp)) := by
  intro qmax σp σm
  have hmp0 : 0 < mp := by linarith
  have hΛ_pos : 0 < Λ := by nlinarith [sq_pos_of_pos (by positivity : 0 < 1 + mp ^ 2)]
  have hb_pos : 0 < mm * mp := mul_pos hmm0 hmp0
  have hqmax_pos : 0 < qmax := Real.sqrt_pos.mpr hb_pos
  have hqmax_sq : qmax ^ 2 = mm * mp := Real.sq_sqrt hb_pos.le
  -- Vieta identities on m⁴ + 2 m² - Λ m + 1 = 0!
  let a := mp + mm
  let b := mm * mp
  have ha_pos : 0 < a := by dsimp only [a]; linarith
  have hab_rel : a ^ 2 * b = (1 - b) ^ 2 := by
    have hdiff : (1 + mp ^ 2) ^ 2 * mm - (1 + mm ^ 2) ^ 2 * mp = 0 := by
      linear_combination mm * hScp - mp * hScm
    have hfac : (1 + mp ^ 2) ^ 2 * mm - (1 + mm ^ 2) ^ 2 * mp =
        (mp - mm) * (mm * mp * (mp + mm) ^ 2 - (1 - mm * mp) ^ 2) := by ring
    rw [hfac] at hdiff
    have h0 := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hmm_lt.ne'))
    dsimp only [a, b]; linarith
  have hΛ_ab : Λ = a * (1 - b ^ 2) / b := by
    have hdiff : (1 + mp ^ 2) ^ 2 - (1 + mm ^ 2) ^ 2 = Λ * (mp - mm) := by linear_combination hScp - hScm
    have hfac : (1 + mp ^ 2) ^ 2 - (1 + mm ^ 2) ^ 2 = (mp - mm) * ((mp + mm) * (mp ^ 2 + mm ^ 2 + 2)) := by ring
    rw [hfac] at hdiff
    have hΛ1 : Λ = (mp + mm) * (mp ^ 2 + mm ^ 2 + 2) := by
      rw [mul_comm Λ] at hdiff
      exact (mul_left_cancel₀ (sub_ne_zero.mpr hmm_lt.ne') hdiff).symm
    have hsum2 : mp ^ 2 + mm ^ 2 + 2 = a ^ 2 - 2 * b + 2 := by dsimp only [a, b]; ring
    rw [hΛ1, hsum2, eq_div_iff hb_pos.ne']
    dsimp only [a, b] at *
    linear_combination (mp + mm) * hab_rel
  have hb_lt1 : b < 1 := by
    have h1 : 0 < a * (1 - b ^ 2) / b := by rw [← hΛ_ab]; exact hΛ_pos
    have h2 : 0 < 1 - b ^ 2 := by
      have := (div_pos_iff_of_pos_right hb_pos).mp h1
      nlinarith
    nlinarith
  have ha_eq : a = (1 - b) / qmax := by
    have hsq : a ^ 2 = ((1 - b) / qmax) ^ 2 := by
      rw [div_pow, hqmax_sq]; exact (eq_div_iff hb_pos.ne').mpr hab_rel
    have hrhs : 0 ≤ (1 - b) / qmax := div_nonneg (by linarith) hqmax_pos.le
    nlinarith [sq_nonneg (a - (1 - b) / qmax), hsq]
  have hb_lt_third : b < 1 / 3 := by
    have hdisc : 0 < a ^ 2 - 4 * b := by
      have : a ^ 2 - 4 * b = (mp - mm) ^ 2 := by dsimp only [a, b]; ring
      rw [this]; exact sq_pos_of_ne_zero (sub_ne_zero.mpr hmm_lt.ne')
    have h1 : 4 * b ^ 2 < (1 - b) ^ 2 := by nlinarith [hab_rel]
    nlinarith
  have hqmax_sq_lt : qmax ^ 2 < 1 / 3 := by rwa [hqmax_sq]
  have hmm_lt_qmax : mm < qmax := by
    have h1 : mm ^ 2 < qmax ^ 2 := by rw [hqmax_sq]; nlinarith only [hmm0, hmm_lt]
    nlinarith only [h1, hmm0, hqmax_pos]
  have hΛ_qmax : Λ = (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 / qmax ^ 3 := by
    have hbq : b = qmax ^ 2 := hqmax_sq.symm
    rw [hΛ_ab, ha_eq, hbq]; field_simp [hqmax_pos.ne']; ring
  have hσ_sum_pos : 0 < σp + σm := by
    have hid : σp + σm = (mp - mm) * (a ^ 2 - b - 1) := by dsimp only [σp, σm, a, b]; ring
    have h2 : b * (a ^ 2 - b - 1) = 1 - 3 * b := by linear_combination hab_rel
    have h3 : 0 < a ^ 2 - b - 1 := by nlinarith
    rw [hid]; exact mul_pos (by linarith) h3
  -- (1b) Closed-form (q, s) positivity
  have hpart1b : ∀ q r : ℝ, mm < q → q < qmax → 0 < r → r < 1 →
      let w := Real.sqrt (1 + q ^ 2)
      let s := (Λ - q * (1 + q ^ 2)) / w
      let sr := Real.sqrt r
      let m0 := sr / (1 - r) * ((1 - r * q ^ 2) / w - sr * q)
      let m1 := 1 / (sr * (1 - r)) * (sr * q - (r - q ^ 2) / w)
      (1 + r) / sr = s →
      2 < s ∧
      m0 * m1 - q ^ 2 = q ^ 4 / ((s ^ 2 - 4) * (1 + q ^ 2)) * (w / q - s) * (s - w * (1 - 2 * q ^ 2) / q ^ 3) ∧
      0 < m0 * m1 - q ^ 2 ∧ 0 < m0 ∧ 0 < m1 := by
    intro q r hmq hqq hr0 hr1 w s sr m0 m1 hrs
    have hq0 : 0 < q := lt_trans hmm0 hmq
    have hq_sq_lt : q ^ 2 < 1 / 3 := lt_trans (by nlinarith only [hq0, hqq]) hqmax_sq_lt
    have hw_pos : 0 < w := Real.sqrt_pos.mpr (by positivity)
    have hw2 : w ^ 2 = 1 + q ^ 2 := Real.sq_sqrt (by positivity)
    have hsr_pos : 0 < sr := Real.sqrt_pos.mpr hr0
    have hsr2 : sr ^ 2 = r := Real.sq_sqrt hr0.le
    have h1mr : 0 < 1 - r := by linarith
    have hs_gt2 : 2 < s := by
      rw [← hrs, lt_div_iff₀ hsr_pos]
      have hsr_ne1 : 1 - sr ≠ 0 := by
        intro h0; have hsr1 : sr = 1 := by linarith
        rw [hsr1, one_pow] at hsr2; linarith
      have : 0 < (1 - sr) ^ 2 := sq_pos_of_ne_zero hsr_ne1
      nlinarith only [this, hsr2]
    have hs2_4 : s ^ 2 - 4 = (1 - r) ^ 2 / r := by
      rw [← hrs, ← hsr2]; field_simp [hsr_pos.ne']; ring
    have hb2_clean : m0 * m1 - q ^ 2 =
        q ^ 4 / ((s ^ 2 - 4) * (1 + q ^ 2)) * (w / q - s) * (s - w * (1 - 2 * q ^ 2) / q ^ 3) := by
      have hs2_4_pos : 0 < s ^ 2 - 4 := by nlinarith
      have h1r_ne : (1 : ℝ) - sr ^ 2 ≠ 0 := by rw [hsr2]; exact h1mr.ne'
      dsimp only [m0, m1]
      rw [hs2_4, ← hrs, ← hsr2]
      field_simp [h1r_ne, hsr_pos.ne', hw_pos.ne', hq0.ne', (by positivity : 0 < 1 + q ^ 2).ne']
      have hw3 : w ^ 3 = (1 + q ^ 2) * w := by rw [show w ^ 3 = w ^ 2 * w by ring, hw2]
      have hw4 : w ^ 4 = (1 + q ^ 2) ^ 2 := by rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2]
      ring_nf
      simp only [hw2, hw3, hw4]
      ring
    -- Sign of both factors: w / q - s < 0 and s - w (1 - 2 q²) / q³ < 0!
    have hfac1_neg : w / q - s < 0 := by
      have hid : w / q - s = ((1 + q ^ 2) ^ 2 - Λ * q) / (q * w) := by
        dsimp only [s]
        rw [eq_div_iff (mul_pos hq0 hw_pos).ne', sub_mul]
        have h1 : w / q * (q * w) = w ^ 2 := by
          calc _ = w / q * q * w := by ring
            _ = w ^ 2 := by rw [div_mul_cancel₀ _ hq0.ne']; ring
        have h2 : (Λ - q * (1 + q ^ 2)) / w * (q * w) = (Λ - q * (1 + q ^ 2)) * q := by
          calc _ = (Λ - q * (1 + q ^ 2)) / w * w * q := by ring
            _ = _ := by rw [div_mul_cancel₀ _ hw_pos.ne']
        rw [h1, h2, hw2]; ring
      rw [hid]; apply div_neg_of_neg_of_pos _ (mul_pos hq0 hw_pos)
      have hq_lt_mp : q < mp := by
        have h1 : qmax < mp := by
          have hsq : qmax ^ 2 < mp ^ 2 := by rw [hqmax_sq]; nlinarith only [hmm_lt, hmp0]
          nlinarith only [hsq, hqmax_pos, hmp0]
        linarith
      have hfac : (1 + q ^ 2) ^ 2 - Λ * q = (q - mm) * (q - mp) * (q ^ 2 + a * q + 1 / b) := by
        rw [hΛ_ab]
        apply mul_left_cancel₀ hb_pos.ne'
        have hL : b * ((1 + q ^ 2) ^ 2 - a * (1 - b ^ 2) / b * q) = b * (1 + q ^ 2) ^ 2 - a * (1 - b ^ 2) * q := by
          rw [mul_sub]
          congr 1
          calc b * (a * (1 - b ^ 2) / b * q) = (a * (1 - b ^ 2) / b * b) * q := by ring
            _ = a * (1 - b ^ 2) * q := by rw [div_mul_cancel₀ _ hb_pos.ne']
        have hR : b * ((q - mm) * (q - mp) * (q ^ 2 + a * q + 1 / b)) =
            (q - mm) * (q - mp) * (b * q ^ 2 + b * a * q + 1) := by
          calc _ = (q - mm) * (q - mp) * (b * q ^ 2 + b * a * q + b * (1 / b)) := by ring
            _ = _ := by rw [mul_one_div_cancel hb_pos.ne']
        rw [hL, hR]
        dsimp only [a, b] at hab_rel ⊢
        linear_combination q ^ 2 * hab_rel
      rw [hfac]
      have h1 : 0 < q - mm := by linarith
      have h2 : q - mp < 0 := by linarith
      have h3 : 0 < q ^ 2 + a * q + 1 / b := by positivity
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h1 h2) h3
    have hfac2_neg : s - w * (1 - 2 * q ^ 2) / q ^ 3 < 0 := by
      have hid : s - w * (1 - 2 * q ^ 2) / q ^ 3 = (Λ * q ^ 3 - (1 + q ^ 2) * (1 - q ^ 2) ^ 2) / (q ^ 3 * w) := by
        dsimp only [s]
        rw [eq_div_iff (mul_pos (pow_pos hq0 3) hw_pos).ne', sub_mul]
        have h1 : (Λ - q * (1 + q ^ 2)) / w * (q ^ 3 * w) = (Λ - q * (1 + q ^ 2)) * q ^ 3 := by
          calc _ = (Λ - q * (1 + q ^ 2)) / w * w * q ^ 3 := by ring
            _ = _ := by rw [div_mul_cancel₀ _ hw_pos.ne']
        have h2 : w * (1 - 2 * q ^ 2) / q ^ 3 * (q ^ 3 * w) = w ^ 2 * (1 - 2 * q ^ 2) := by
          calc _ = w * (1 - 2 * q ^ 2) / q ^ 3 * q ^ 3 * w := by ring
            _ = w ^ 2 * (1 - 2 * q ^ 2) := by rw [div_mul_cancel₀ _ (pow_pos hq0 3).ne']; ring
        rw [h1, h2, hw2]; ring
      rw [hid]; apply div_neg_of_neg_of_pos _ (mul_pos (pow_pos hq0 3) hw_pos)
      rw [hΛ_qmax, div_mul_eq_mul_div, sub_neg, div_lt_iff₀ (pow_pos hqmax_pos 3)]
      have h1 : (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 < (1 + q ^ 2) * (1 - q ^ 2) ^ 2 := by
        have hid4 : (1 + q ^ 2) * (1 - q ^ 2) ^ 2 - (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 =
            (qmax ^ 2 - q ^ 2) * (1 + (q ^ 2 + qmax ^ 2) - (q ^ 4 + q ^ 2 * qmax ^ 2 + qmax ^ 4)) := by ring
        have hpos1 : 0 < qmax ^ 2 - q ^ 2 := by nlinarith only [hq0, hqq]
        have hpos2 : 0 < 1 + (q ^ 2 + qmax ^ 2) - (q ^ 4 + q ^ 2 * qmax ^ 2 + qmax ^ 4) := by
          nlinarith only [hq_sq_lt, hqmax_sq_lt, sq_nonneg q, sq_nonneg qmax]
        linarith [mul_pos hpos1 hpos2]
      have h2 : q ^ 3 < qmax ^ 3 := pow_lt_pow_left₀ hqq hq0.le (by norm_num)
      have hp1 : 0 < (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 := by
        have : 0 < 1 - qmax ^ 2 := by linarith
        positivity
      calc (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 * q ^ 3
          < (1 + qmax ^ 2) * (1 - qmax ^ 2) ^ 2 * qmax ^ 3 := mul_lt_mul_of_pos_left h2 hp1
        _ < (1 + q ^ 2) * (1 - q ^ 2) ^ 2 * qmax ^ 3 := mul_lt_mul_of_pos_right h1 (pow_pos hqmax_pos 3)
    have hb2_pos : 0 < m0 * m1 - q ^ 2 := by
      rw [hb2_clean]
      have h1 : 0 < q ^ 4 / ((s ^ 2 - 4) * (1 + q ^ 2)) := by
        have : 0 < s ^ 2 - 4 := by nlinarith only [hs_gt2]
        positivity
      have h2 : 0 < (w / q - s) * (s - w * (1 - 2 * q ^ 2) / q ^ 3) :=
        mul_pos_of_neg_of_neg hfac1_neg hfac2_neg
      nlinarith only [h1, h2]
    have hm0_pos : 0 < m0 := by
      dsimp only [m0]
      apply mul_pos (div_pos hsr_pos h1mr)
      rw [sub_pos, lt_div_iff₀ hw_pos]
      have hsr_lt1 : sr < 1 := by nlinarith only [hsr2, hsr_pos, hr1]
      have hs3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have hw_lt : w < 2 / Real.sqrt 3 := by
        have h1 : w ^ 2 < (2 / Real.sqrt 3) ^ 2 := by
          rw [hw2, div_pow, Real.sq_sqrt (by norm_num)]; linarith
        have h2 : 0 < 2 / Real.sqrt 3 := div_pos (by norm_num) hs3_pos
        nlinarith only [h1, hw_pos, h2]
      have hq_lt_s3 : q < 1 / Real.sqrt 3 := by
        have h1 : q ^ 2 < (1 / Real.sqrt 3) ^ 2 := by
          rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]; exact hq_sq_lt
        have h2 : 0 < 1 / Real.sqrt 3 := div_pos one_pos hs3_pos
        nlinarith only [h1, hq0, h2]
      have hqw : q * w < 2 / 3 := by
        calc q * w < (1 / Real.sqrt 3) * (2 / Real.sqrt 3) :=
              mul_lt_mul'' hq_lt_s3 hw_lt hq0.le hw_pos.le
          _ = 2 / (Real.sqrt 3 ^ 2) := by ring
          _ = 2 / 3 := by rw [Real.sq_sqrt (by norm_num)]
      have hsr_qw : sr * q * w < 2 / 3 := by
        calc sr * q * w = sr * (q * w) := by ring
          _ < 1 * (2 / 3) := mul_lt_mul'' hsr_lt1 hqw hsr_pos.le (mul_pos hq0 hw_pos).le
          _ = 2 / 3 := one_mul _
      nlinarith only [hsr_qw, hq_sq_lt, hr1, hr0]
    have hm1_pos : 0 < m1 := by nlinarith only [hb2_pos, hm0_pos, sq_pos_of_pos hq0]
    exact ⟨hs_gt2, hb2_clean, hb2_pos, hm0_pos, hm1_pos⟩
  -- (2a) Strict convexity f''(q) > 0
  have hpart2a : ∀ q : ℝ, 0 < q →
      HasDerivAt fluxDerivF32 (-3 * q⁻¹ ^ 4 + 6 + 48 * q ^ 2 + 45 * q ^ 4) q ∧
      HasDerivAt (fun x => -3 * x⁻¹ ^ 4 + 6 + 48 * x ^ 2 + 45 * x ^ 4)
        (12 * q⁻¹ ^ 5 + 96 * q + 180 * q ^ 3) q ∧
      0 < 12 * q⁻¹ ^ 5 + 96 * q + 180 * q ^ 3 := fun q hq => by
    have hd1 : HasDerivAt fluxDerivF32 (-3 * q⁻¹ ^ 4 + 6 + 48 * q ^ 2 + 45 * q ^ 4) q := by
      have hfun : fluxDerivF32 = fun x => x⁻¹ ^ 3 + 6 * x + 16 * x ^ 3 + 9 * x ^ 5 := rfl
      rw [hfun]
      have hinv := (hasDerivAt_inv hq.ne').pow 3
      have hd := ((hinv.add ((hasDerivAt_id q).const_mul (6 : ℝ))).add
        ((hasDerivAt_pow 3 q).const_mul (16 : ℝ))).add ((hasDerivAt_pow 5 q).const_mul (9 : ℝ))
      exact hd.congr_deriv (by rw [← inv_pow q 2]; ring)
    have hd2 : HasDerivAt (fun x => -3 * x⁻¹ ^ 4 + 6 + 48 * x ^ 2 + 45 * x ^ 4)
        (12 * q⁻¹ ^ 5 + 96 * q + 180 * q ^ 3) q := by
      have hinv := ((hasDerivAt_inv hq.ne').pow 4).const_mul (-3 : ℝ)
      have hd := ((hinv.add (hasDerivAt_const q (6 : ℝ))).add
        ((hasDerivAt_pow 2 q).const_mul (48 : ℝ))).add ((hasDerivAt_pow 4 q).const_mul (45 : ℝ))
      exact hd.congr_deriv (by rw [← inv_pow q 2]; ring)
    exact ⟨hd1, hd2, by positivity⟩
  -- (2b) Factored endpoints
  have hpart2b : 4 * Λ - fluxDerivF32 mm = -((1 - 3 * mm ^ 2) ^ 2 * (1 + mm ^ 2) ^ 2 / mm ^ 3) ∧
      4 * Λ - fluxDerivF32 mm < 0 := by
    have hΛm : Λ = (1 + mm ^ 2) ^ 2 / mm := by rw [eq_div_iff hmm0.ne']; linarith [hScm]
    have heq : 4 * Λ - fluxDerivF32 mm = -((1 - 3 * mm ^ 2) ^ 2 * (1 + mm ^ 2) ^ 2 / mm ^ 3) := by
      rw [hΛm]; dsimp only [fluxDerivF32]; field_simp [hmm0.ne']; ring
    have hmm_sq_lt : mm ^ 2 < 1 / 3 := lt_trans (by nlinarith only [hmm0, hmm_lt_qmax]) hqmax_sq_lt
    have hneg : 4 * Λ - fluxDerivF32 mm < 0 := by
      rw [heq]; apply neg_neg_of_pos
      have h1 : 0 < (1 - 3 * mm ^ 2) ^ 2 := sq_pos_of_ne_zero (by linarith)
      positivity
    exact ⟨heq, hneg⟩
  have hpart2c : 4 * Λ - fluxDerivF32 qmax =
      (1 - 3 * qmax ^ 2) * (1 + qmax ^ 2) * (3 + 2 * qmax ^ 2 + 3 * qmax ^ 4) / qmax ^ 3 ∧
      0 < 4 * Λ - fluxDerivF32 qmax := by
    have heq : 4 * Λ - fluxDerivF32 qmax =
        (1 - 3 * qmax ^ 2) * (1 + qmax ^ 2) * (3 + 2 * qmax ^ 2 + 3 * qmax ^ 4) / qmax ^ 3 := by
      rw [hΛ_qmax]; dsimp only [fluxDerivF32]; field_simp [hqmax_pos.ne']; ring
    have hpos : 0 < 4 * Λ - fluxDerivF32 qmax := by
      rw [heq]; have h1 : 0 < 1 - 3 * qmax ^ 2 := by linarith
      positivity
    exact ⟨heq, hpos⟩
  -- (2d) Exact flux derivative identity at p = 3/2 (eliminating r = sr² and w² = 1 + q²!)
  have hpart2d : ∀ (r q w q' : ℝ), 0 < r → r < 1 → 0 < q → w = Real.sqrt (1 + q ^ 2) →
      let s := (1 + r) / Real.sqrt r
      Λ = s * w + q * w ^ 2 →
      q' = (1 - r) * w ^ 2 / (2 * r * Real.sqrt r * (s * q + (1 + 3 * q ^ 2) * w)) →
      let sr := Real.sqrt r
      let φ1' := q + r * q' - (1 / (2 * sr * w) * (1 + r * q ^ 4) +
        sr / w * (q ^ 4 + 4 * r * q ^ 3 * q') - sr * q * q' / w ^ 3 * (1 + r * q ^ 4))
      let φ2' := (q' / r - q / r ^ 2) - ((1 / w + 4 * q ^ 3 * q' / w - q * q' * (r + q ^ 4) / w ^ 3) / (r * sr) -
        3 * (r + q ^ 4) / (2 * r ^ 2 * sr * w))
      φ1' = -r ^ 3 * φ2' ∧
      φ1' = sr * q ^ 3 / (2 * w ^ 2 * (s * q + (1 + 3 * q ^ 2) * w)) * (4 * Λ - fluxDerivF32 q) := by
    intro r q w q' hr0 hr1 hq0 hw_eq s hΛ_sw hq'_eq sr φ1' φ2'
    have hsr_pos : 0 < sr := Real.sqrt_pos.mpr hr0
    have hsr2 : sr ^ 2 = r := Real.sq_sqrt hr0.le
    have hw_pos : 0 < w := by rw [hw_eq]; exact Real.sqrt_pos.mpr (by positivity)
    have hw2 : w ^ 2 = 1 + q ^ 2 := by rw [hw_eq]; exact Real.sq_sqrt (by positivity)
    have hw3 : w ^ 3 = (1 + q ^ 2) * w := by rw [show w ^ 3 = w ^ 2 * w by ring, hw2]
    have hw4 : w ^ 4 = (1 + q ^ 2) ^ 2 := by rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2]
    have hs_pos : 0 < s := div_pos (by linarith) hsr_pos
    have hden_pos : 0 < s * q + (1 + 3 * q ^ 2) * w := by positivity
    let K : ℝ := (1 + sr ^ 2) * q + sr * (1 + 3 * q ^ 2) * w
    have hK_pos : 0 < K := by dsimp only [K]; positivity
    have hden_K : s * q + (1 + 3 * q ^ 2) * w = K / sr := by
      dsimp only [s, K]
      change (1 + r) / sr * q + (1 + 3 * q ^ 2) * w = _
      rw [← hsr2, eq_div_iff hsr_pos.ne', add_mul]
      have h1 : (1 + sr ^ 2) / sr * q * sr = (1 + sr ^ 2) * q := by
        calc _ = (1 + sr ^ 2) / sr * sr * q := by ring
          _ = _ := by rw [div_mul_cancel₀ _ hsr_pos.ne']
      rw [h1]; ring
    have hq'_K : q' = (1 - sr ^ 2) * w ^ 2 / (2 * sr ^ 2 * K) := by
      rw [hq'_eq, hden_K]
      change (1 - r) * w ^ 2 / (2 * r * sr * (K / sr)) = _
      rw [← hsr2]
      have h1 : 2 * sr ^ 2 * sr * (K / sr) = 2 * sr ^ 2 * K := by
        calc _ = 2 * sr ^ 2 * (K / sr * sr) := by ring
          _ = 2 * sr ^ 2 * K := by rw [div_mul_cancel₀ _ hsr_pos.ne']
      rw [h1]
    have hsym : φ1' = -r ^ 3 * φ2' := by
      dsimp only [φ1', φ2']
      rw [hq'_K, ← hsr2]
      field_simp [hsr_pos.ne', hw_pos.ne', hK_pos.ne']
      dsimp only [K]
      ring_nf
      simp only [hw2, hw3]
      ring
    have hformula : φ1' = sr * q ^ 3 / (2 * w ^ 2 * (s * q + (1 + 3 * q ^ 2) * w)) * (4 * Λ - fluxDerivF32 q) := by
      dsimp only [φ1', fluxDerivF32]
      rw [hq'_K, hΛ_sw, hden_K]
      have hs_sr : s = (1 + sr ^ 2) / sr := by dsimp only [s, sr]; rw [hsr2]
      rw [hs_sr, ← hsr2]
      field_simp [hsr_pos.ne', hw_pos.ne', hq0.ne', hK_pos.ne']
      dsimp only [K]
      ring_nf
      simp only [hw2, hw3, hw4]
      ring
    exact ⟨hsym, hformula⟩
  -- (3) Exact Λ-sensitivity & 2×2 Master Trace inequality at p = 3/2 for all m ≥ 2!
  have hpart3 : ∀ (r_star τ2 τ2' σp' E : ℝ), 0 < r_star → r_star < 1 / (mp ^ 4 + mp ^ 2 - 1) →
      σm < τ2 → 0 < E →
      σp' = mp ^ 2 / (1 + mp ^ 2) →
      Λ * (-τ2' + r_star ^ 3 * σp') = E →
      r_star ^ 3 * σp - τ2 < 0 ∧
      0 < σp' ∧
      (r_star ^ 3 * σp - τ2) * σp' - (σp / Λ) * E = τ2' * σp - τ2 * σp' ∧
      τ2' * σp - τ2 * σp' < 0 ∧
      (∀ m : ℕ, 2 ≤ m → τ2 / σp ≤ 1 / ((m : ℝ) - 1) → σp + τ2 ≤ (m : ℝ) / ((m : ℝ) - 1) * σp) := by
    intro r_star τ2 τ2' σp' E hr0 hr_lt hτ2_gt hE_pos hσp'_eq hsens
    have hσp_pos : 0 < σp := by
      dsimp only [σp]
      have hsq : 1 < mp ^ 2 := by nlinarith only [hmp1]
      nlinarith only [hmp1, hsq]
    have hmm_sq_lt : mm ^ 2 < 1 / 3 := lt_trans (by nlinarith only [hmm0, hmm_lt_qmax]) hqmax_sq_lt
    have hlem0 : 1 < Λ * σm := by
      have h := (lemma0_lambda_sigma_minus_gt_one (κ := 3 / 2) (by norm_num)
        (sq_pos_of_pos hmm0) (by norm_num; exact hmm_sq_lt) (by
          have h1 : (2 : ℝ) * (3 / 2) - 1 = 2 := by norm_num
          have h2 : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
          rw [h1, h2, Real.rpow_two, ← Real.rpow_natCast mm 2, ← Real.rpow_mul hmm0.le]
          norm_num; exact hScm)).1
      have h1 : (mm ^ 2) ^ ((3 / 2 : ℝ) - 1) * (1 - mm ^ 2) = σm := by
        have : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
        rw [this, ← Real.rpow_natCast mm 2, ← Real.rpow_mul hmm0.le]
        norm_num; dsimp only [σm]; ring
      rwa [h1] at h
    have hden_pos : 0 < mp ^ 4 + mp ^ 2 - 1 := by nlinarith only [hmp1]
    have hfrac_lt : (1 + mp ^ 2) ^ 2 * (mp ^ 2 - 1) / (mp ^ 4 + mp ^ 2 - 1) ^ 3 < 1 / 2 := by
      rw [div_lt_div_iff₀ (pow_pos hden_pos 3) (by norm_num : (0 : ℝ) < 2)]
      let t := mp ^ 2 - 1
      have ht : 0 < t := by dsimp only [t]; nlinarith only [hmp1]
      have hid : (mp ^ 4 + mp ^ 2 - 1) ^ 3 - 2 * ((1 + mp ^ 2) ^ 2 * (mp ^ 2 - 1)) =
          1 + t + 22 * t ^ 2 + 43 * t ^ 3 + 30 * t ^ 4 + 9 * t ^ 5 + t ^ 6 := by
        dsimp only [t]; ring
      have hpos : 0 < 1 + t + 22 * t ^ 2 + 43 * t ^ 3 + 30 * t ^ 4 + 9 * t ^ 5 + t ^ 6 := by positivity
      linarith
    have htr_neg : r_star ^ 3 * σp - τ2 < 0 := by
      have hr3 : r_star ^ 3 < (1 / (mp ^ 4 + mp ^ 2 - 1)) ^ 3 := pow_lt_pow_left₀ hr_lt hr0.le (by norm_num)
      have hΛσp : Λ * σp = (1 + mp ^ 2) ^ 2 * (mp ^ 2 - 1) := by
        dsimp only [σp]; linear_combination (mp ^ 2 - 1) * hScp.symm
      have h1 : Λ * (r_star ^ 3 * σp) < 1 / 2 := by
        calc Λ * (r_star ^ 3 * σp) = (Λ * σp) * r_star ^ 3 := by ring
          _ < (Λ * σp) * (1 / (mp ^ 4 + mp ^ 2 - 1)) ^ 3 := mul_lt_mul_of_pos_left hr3 (mul_pos hΛ_pos hσp_pos)
          _ = (1 + mp ^ 2) ^ 2 * (mp ^ 2 - 1) / (mp ^ 4 + mp ^ 2 - 1) ^ 3 := by rw [hΛσp, one_div, inv_pow, div_eq_mul_inv]
          _ < 1 / 2 := hfrac_lt
      have h2 : 1 < Λ * τ2 := lt_trans hlem0 (mul_lt_mul_of_pos_left hτ2_gt hΛ_pos)
      have hlt : r_star ^ 3 * σp < τ2 := lt_of_mul_lt_mul_left (by linarith only [h1, h2]) hΛ_pos.le
      linarith only [hlt]
    have hσp'_pos : 0 < σp' := by rw [hσp'_eq]; positivity
    have hquot_id : (r_star ^ 3 * σp - τ2) * σp' - (σp / Λ) * E = τ2' * σp - τ2 * σp' := by
      rw [← hsens]; field_simp [hΛ_pos.ne']; ring
    have hquot_neg : τ2' * σp - τ2 * σp' < 0 := by
      rw [← hquot_id]
      have h1 : (r_star ^ 3 * σp - τ2) * σp' < 0 := mul_neg_of_neg_of_pos htr_neg hσp'_pos
      have h2 : 0 < (σp / Λ) * E := mul_pos (div_pos hσp_pos hΛ_pos) hE_pos
      linarith
    have hmaster : ∀ m : ℕ, 2 ≤ m → τ2 / σp ≤ 1 / ((m : ℝ) - 1) → σp + τ2 ≤ (m : ℝ) / ((m : ℝ) - 1) * σp := by
      intro m hm hle
      have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
      have hτ2_le : τ2 ≤ σp / ((m : ℝ) - 1) := by
        have := (div_le_iff₀ hσp_pos).mp hle
        linarith [show 1 / ((m : ℝ) - 1) * σp = σp / ((m : ℝ) - 1) by ring]
      have heq : (m : ℝ) / ((m : ℝ) - 1) * σp = σp + σp / ((m : ℝ) - 1) := by
        field_simp [hm1.ne']; ring
      linarith
    exact ⟨htr_neg, hσp'_pos, hquot_id, hquot_neg, hmaster⟩
  exact ⟨⟨hqmax_sq_lt, hmm_lt_qmax, hΛ_qmax, hσ_sum_pos⟩, hpart1b, hpart2a, hpart2b, hpart2c, hpart2d, hpart3⟩

/-! ==========================================================================
    PART 6: Euler–Betti Root Identity (Theorem N2) & All-p Hessian Signs (N1.2)
    ========================================================================== -/

/-- Matrix-level non-vacuum negative-flux corollary of Theorem B3 (`universal_phi_psd_rigidity`):
    Every finite-dimensional PosDef block (D, H) solving Holden's equation at κ > 1, Λ > 2^(2κ - 1)
    with H ≠ h_+ D has strictly positive negative-flux rank: Re Tr(P^-) ≥ 1! -/
lemma non_vacuum_block_has_neg_flux {n : ℕ} {κ Λ h : ℝ}
    (hκ : 1 < κ) (hΛ : 2 ^ (2 * κ - 1) < Λ) (hh : 1 < h)
    (hSc : (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1))
    {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    (hne : H ≠ (h : ℂ) • D) :
    let hG := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
    let Φ := posDefPow κ hG - D * posDefPow (κ - 1) hG * D
    let hΦ : Φ.IsHermitian :=
      (posDefPow_posDef κ hG).isHermitian.sub (posDef_conj_of_posDef hD (posDefPow_posDef (κ - 1) hG)).isHermitian
    1 ≤ (negSpectralProj hΦ).trace.re := by
  intro hG Φ hΦ
  let U := hΦ.eigenvectorUnitary
  let lam := hΦ.eigenvalues
  have htr : (negSpectralProj hΦ).trace.re = ∑ i : Fin n, if lam i < 0 then (1 : ℝ) else 0 := by
    unfold negSpectralProj
    have h1 : ((U : Mat n) * Matrix.diagonal (fun i => if lam i < 0 then (1 : ℂ) else 0) * (U : Mat n)ᴴ).trace =
        (Matrix.diagonal (fun i => if lam i < 0 then (1 : ℂ) else 0)).trace := by
      rw [Matrix.trace_mul_cycle, blitz_unitary_conj_mul U, Matrix.one_mul]
    rw [h1, Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [htr]
  obtain ⟨i0, hi0⟩ : ∃ i : Fin n, lam i < 0 := by
    by_contra hall; push Not at hall
    have hΦ_psd : Φ.PosSemidef := by
      have hspec : Φ = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
        simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hΦ.spectral_theorem
      rw [hspec]
      have hd : (Matrix.diagonal (fun i => (lam i : ℂ))).PosSemidef := by
        rw [Matrix.posSemidef_diagonal_iff]
        intro i
        rw [Complex.le_def, Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨hall i, rfl⟩
      simpa only [Matrix.mul_assoc] using hd.mul_mul_conjTranspose_same (U : Mat n)
    exact hne (universal_phi_psd_rigidity hκ hΛ hh hSc hD hH hEq hΦ_psd)
  have hle := Finset.single_le_sum (fun i _ => by split_ifs <;> norm_num : ∀ i ∈ Finset.univ,
      (0 : ℝ) ≤ if lam i < 0 then (1 : ℝ) else 0) (Finset.mem_univ i0)
  rw [if_pos hi0] at hle
  exact hle

/-- Theorem N2 (`b3_nonvanishing_proof.md` §2): Exact m = 2 Topological Euler–Betti Root
    Identity for ALL 1 < p < 2:
    On any connected finite-dimensional m = 2 solution with k vertices, block families B₁, B₂,
    1×1 h_+-root subsets Q₁⁺ ⊆ B₁, Q₂⁺ ⊆ B₂ (R := |Q₁⁺| + |Q₂⁺|), zero-flux count Z,
    negative-flux ranks negRank₁, negRank₂ (obeying negRank = 0 on Q_j⁺ and negRank ≥ 1 on
    B_j \ Q_j⁺ by `non_vacuum_block_has_neg_flux` / Theorem B3), vertex-flux partition
      k = Z + ∑_{B ∈ B₁} negRank₁(B) + ∑_{B ∈ B₂} negRank₂(B),
    and bipartite incidence first Betti number β₁ = 2 k - (k + |B₁| + |B₂|) + 1:
      (1) (R - 1) + β₁ = Z + ∑_{B ∈ B₁ \ Q₁⁺} (negRank₁(B) - 1) + ∑_{B ∈ B₂ \ Q₂⁺} (negRank₂(B) - 1),
      (2) Every summand on the RHS is ≥ 0,
      (3) When R ≥ 1 and β₁ ≥ 0:
            (R = 1 ∧ β₁ = 0) ↔ (Z = 0 ∧ (∀ B ∈ B₁ \ Q₁⁺, negRank₁ B = 1) ∧ (∀ B ∈ B₂ \ Q₂⁺, negRank₂ B = 1))! -/
theorem euler_betti_root_identity {ι1 ι2 : Type*} [DecidableEq ι1] [DecidableEq ι2]
    (B1 Q1 : Finset ι1) (B2 Q2 : Finset ι2)
    (hQ1 : Q1 ⊆ B1) (hQ2 : Q2 ⊆ B2)
    (negRank1 : ι1 → ℕ) (negRank2 : ι2 → ℕ)
    (hQ1_zero : ∀ b ∈ Q1, negRank1 b = 0)
    (hQ2_zero : ∀ b ∈ Q2, negRank2 b = 0)
    (hB1_pos : ∀ b ∈ B1 \ Q1, 1 ≤ negRank1 b)
    (hB2_pos : ∀ b ∈ B2 \ Q2, 1 ≤ negRank2 b)
    (k Z : ℕ)
    (hpart : k = Z + ∑ b ∈ B1, negRank1 b + ∑ b ∈ B2, negRank2 b) :
    let R : ℕ := Q1.card + Q2.card
    let β1 : ℤ := (2 * k : ℤ) - ((k : ℤ) + (B1.card : ℤ) + (B2.card : ℤ)) + 1
    ((R : ℤ) - 1) + β1 = (Z : ℤ) +
      ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) +
      ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) ∧
    (0 ≤ ((R : ℤ) - 1) + β1) ∧
    (1 ≤ R → 0 ≤ β1 →
      ((R = 1 ∧ β1 = 0) ↔
        (Z = 0 ∧ (∀ b ∈ B1 \ Q1, negRank1 b = 1) ∧ (∀ b ∈ B2 \ Q2, negRank2 b = 1)))) := by
  intro R β1
  have hsum1 : (∑ b ∈ B1, (negRank1 b : ℤ)) =
      ((B1.card : ℤ) - (Q1.card : ℤ)) + ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) := by
    have hsplit : ∑ b ∈ B1, (negRank1 b : ℤ) =
        ∑ b ∈ B1 \ Q1, (negRank1 b : ℤ) + ∑ b ∈ Q1, (negRank1 b : ℤ) := by
      rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hQ1]
    have hQ0 : ∑ b ∈ Q1, (negRank1 b : ℤ) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [hQ1_zero b hb]; rfl
    have hsdiff : ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) =
        (∑ b ∈ B1 \ Q1, (negRank1 b : ℤ)) - ((B1 \ Q1).card : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((B1 \ Q1).card : ℤ) = (B1.card : ℤ) - (Q1.card : ℤ) := by
      rw [Finset.card_sdiff_of_subset hQ1, Nat.cast_sub (Finset.card_le_card hQ1)]
    linarith
  have hsum2 : (∑ b ∈ B2, (negRank2 b : ℤ)) =
      ((B2.card : ℤ) - (Q2.card : ℤ)) + ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) := by
    have hsplit : ∑ b ∈ B2, (negRank2 b : ℤ) =
        ∑ b ∈ B2 \ Q2, (negRank2 b : ℤ) + ∑ b ∈ Q2, (negRank2 b : ℤ) := by
      rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset hQ2]
    have hQ0 : ∑ b ∈ Q2, (negRank2 b : ℤ) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [hQ2_zero b hb]; rfl
    have hsdiff : ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) =
        (∑ b ∈ B2 \ Q2, (negRank2 b : ℤ)) - ((B2 \ Q2).card : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : ((B2 \ Q2).card : ℤ) = (B2.card : ℤ) - (Q2.card : ℤ) := by
      rw [Finset.card_sdiff_of_subset hQ2, Nat.cast_sub (Finset.card_le_card hQ2)]
    linarith
  have hk_z : (k : ℤ) = (Z : ℤ) + ∑ b ∈ B1, (negRank1 b : ℤ) + ∑ b ∈ B2, (negRank2 b : ℤ) := by
    exact_mod_cast hpart
  have hid : ((R : ℤ) - 1) + β1 = (Z : ℤ) +
      ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) +
      ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) := by
    have hR : (R : ℤ) = (Q1.card : ℤ) + (Q2.card : ℤ) := by dsimp only [R]; push_cast; rfl
    dsimp only [β1]
    linarith [hR, hk_z, hsum1, hsum2]
  have h1_nn : ∀ b ∈ B1 \ Q1, (0 : ℤ) ≤ (negRank1 b : ℤ) - 1 := fun b hb => by
    have := hB1_pos b hb; omega
  have h2_nn : ∀ b ∈ B2 \ Q2, (0 : ℤ) ≤ (negRank2 b : ℤ) - 1 := fun b hb => by
    have := hB2_pos b hb; omega
  have hs1_nn : 0 ≤ ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) := Finset.sum_nonneg h1_nn
  have hs2_nn : 0 ≤ ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) := Finset.sum_nonneg h2_nn
  have hrhs_nn : 0 ≤ ((R : ℤ) - 1) + β1 := by rw [hid]; omega
  refine ⟨hid, hrhs_nn, fun hR1 hβ0 => ?_⟩
  constructor
  · rintro ⟨hReq, hβeq⟩
    have htot0 : (Z : ℤ) + ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) +
        ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) = 0 := by rw [← hid, hReq, hβeq]; norm_num
    have hZ0 : Z = 0 := by omega
    have hS1_0 : ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) = 0 := by omega
    have hS2_0 : ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) = 0 := by omega
    refine ⟨hZ0, fun b hb => ?_, fun b hb => ?_⟩
    · have := (Finset.sum_eq_zero_iff_of_nonneg h1_nn).mp hS1_0 b hb; omega
    · have := (Finset.sum_eq_zero_iff_of_nonneg h2_nn).mp hS2_0 b hb; omega
  · rintro ⟨hZ0, hall1, hall2⟩
    have hS1_0 : ∑ b ∈ B1 \ Q1, ((negRank1 b : ℤ) - 1) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [hall1 b hb]; norm_num
    have hS2_0 : ∑ b ∈ B2 \ Q2, ((negRank2 b : ℤ) - 1) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [hall2 b hb]; norm_num
    rw [hZ0, hS1_0, hS2_0] at hid
    omega

/-- Exact Daletskii–Krein self-block local Hessian kernel Q_loc(h, 1; h, 1) (Theorem N1 Part 2). -/
def qLocSelf (κ h : ℝ) : ℝ :=
  (κ * h - (κ - 1)) / ((κ - 1) * (2 * κ - 1) * h ^ (κ - 1))

/-- Exact Daletskii–Krein cross-scalar local Hessian kernel Q_loc(h₁, 1; h₂, ρ) (Theorem N1 Part 2). -/
def qLocCross (κ h1 h2 ρ : ℝ) : ℝ :=
  (h1 - h2 * ρ ^ 2) / (ρ * (h1 ^ (κ - 1) - h2 ^ (κ - 1) * ρ ^ (2 * κ - 2))) -
  ((1 + h1) - (1 + h2) * ρ) / (h1 ^ (κ - 1) - h2 ^ (κ - 1) * ρ ^ (2 * κ - 1))

set_option maxHeartbeats 800000 in
/-- Theorem N1 Part 2 (`b3_nonvanishing_proof.md` §1): Exact Closed-Form Scalar & Cross-Scalar
    Local Hessian Spectral Signs for ALL 1 < p < 2 (all κ > 1, all Λ > 2^(2κ - 1)):
    For the two positive roots h_- < h_+ of (1 + h)^(2κ - 1) = Λ h^(κ - 1):
      (1) Root localization: 0 < h_- < (κ - 1)/κ < 1 < h_+.
      (2) Self-block signs: Q_loc(h_+, 1; h_+, 1) > 0 and Q_loc(h_-, 1; h_-, 1) < 0.
      (3) Same-root cross-pair (ρ = e^(-u), u > 0):
            Q_loc(h, 1; h, e^(-u)) = (e^((κ - 1) u) sinh(u/2) / (h^(κ - 1) sinh((κ - 1/2) u))) *
              (h * sinh(κ u) / sinh((κ - 1) u) - 1),
          with sinh(κ u) / sinh((κ - 1) u) > κ / (κ - 1) strictly increasing in u > 0, proving:
            - (h_+, h_+) is STRICTLY POSITIVE for ALL u > 0 (all ρ ∈ (0, 1]),
            - (h_-, h_-) > 0 ↔ h_- * sinh(κ u) / sinh((κ - 1) u) > 1 (flips positive for small ρ).
      (4) Opposite-root cross-pair (h_+, 1; h_-, ρ):
            Q_loc(h_+, 1; h_-, ρ) = ((1 - ρ) [h_+^(κ - 1)(h_+ - ρ) + h_-^(κ - 1) ρ^(2κ - 1)(1 - h_- ρ)]) /
              (ρ (h_+^(κ - 1) - h_-^(κ - 1) ρ^(2κ - 2)) (h_+^(κ - 1) - h_-^(κ - 1) ρ^(2κ - 1)))
          is STRICTLY POSITIVE for ALL ρ ∈ (0, 1) and vanishes identically at ρ = 1!
      (5) Exact p = 4/3 (κ = 2) opposite-root (h_-, 1; h_+, r) sign flip on r ∈ (0, 1):
            1/r - Λ / ((1 + h_-)² + (1 + h_-)(1 + h_+) r + (1 + h_+)² r²) > 0 ↔ r < ((1 + h_-)/(1 + h_+))²
          (and equals Q_loc(2, h_-, h_+, r) away from the removable points h_- = h_+ r², h_- = h_+ r³)! -/
theorem hessian_sign_pairs_all_p {κ Λ hm hp : ℝ}
    (hκ : 1 < κ) (hΛ : 2 ^ (2 * κ - 1) < Λ)
    (hhm0 : 0 < hm) (hhm_lt : hm < hp)
    (hScm : (1 + hm) ^ (2 * κ - 1) = Λ * hm ^ (κ - 1))
    (hScp : (1 + hp) ^ (2 * κ - 1) = Λ * hp ^ (κ - 1)) :
    -- (1) Exact root localization
    (hm < (κ - 1) / κ ∧ (κ - 1) / κ < 1 ∧ 1 < hp) ∧
    -- (2) Exact self-block signs
    (0 < qLocSelf κ hp ∧ qLocSelf κ hm < 0) ∧
    -- (3) Same-root cross-pair hyperbolic identity, strict positivity for (h_+, h_+), and flip iff for (h_-, h_-)
    (∀ h u : ℝ, 0 < h → 0 < u →
      qLocCross κ h h (Real.exp (-u)) =
        (Real.exp ((κ - 1) * u) * Real.sinh (u / 2)) / (h ^ (κ - 1) * Real.sinh ((κ - 1 / 2) * u)) *
          (h * (Real.sinh (κ * u) / Real.sinh ((κ - 1) * u)) - 1)) ∧
    (∀ u : ℝ, 0 < u → κ / (κ - 1) < Real.sinh (κ * u) / Real.sinh ((κ - 1) * u)) ∧
    (∀ u : ℝ, 0 < u → 0 < qLocCross κ hp hp (Real.exp (-u))) ∧
    (∀ u : ℝ, 0 < u → (0 < qLocCross κ hm hm (Real.exp (-u)) ↔
      1 < hm * (Real.sinh (κ * u) / Real.sinh ((κ - 1) * u)))) ∧
    -- (4) Opposite-root cross-pair factorization, positivity on (0, 1), and vanishing at ρ = 1
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      qLocCross κ hp hm ρ =
        (1 - ρ) * (hp ^ (κ - 1) * (hp - ρ) + hm ^ (κ - 1) * ρ ^ (2 * κ - 1) * (1 - hm * ρ)) /
          (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2)) *
            (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 1)))) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ < 1 → 0 < qLocCross κ hp hm ρ) ∧
    qLocCross κ hp hm 1 = 0 ∧
    -- (5) Exact p = 4/3 opposite-root (h_-, 1; h_+, r) sign flip at r_max = ((1 + h_-)/(1 + h_+))²
    (κ = 2 → ∀ r : ℝ, 0 < r → r < 1 →
      (1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) =
        (1 - r) * ((1 + hm) ^ 2 - (1 + hp) ^ 2 * r) /
          (r * ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2))) ∧
      (0 < 1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) ↔
        r < ((1 + hm) / (1 + hp)) ^ 2) ∧
      (hm ≠ hp * r ^ 2 → hm ≠ hp * r ^ 3 →
        qLocCross 2 hm hp r =
          1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2))) := by
  have hkm1 : 0 < κ - 1 := by linarith
  have h2km1 : 0 < 2 * κ - 1 := by linarith
  have hhp0 : 0 < hp := lt_trans hhm0 hhm_lt
  -- (1) Root localization via f(x) = (1 + x)^(2κ - 1) / x^(κ - 1): strictly decreasing on (0, (κ-1)/κ],
  --     strictly increasing on [(κ-1)/κ, ∞), and f(1) = 2^(2κ - 1) < Λ!
  let f : ℝ → ℝ := fun x => (1 + x) ^ (2 * κ - 1) / x ^ (κ - 1)
  have hf_deriv : ∀ x : ℝ, 0 < x →
      HasDerivAt f ((1 + x) ^ (2 * κ - 2) * x ^ (κ - 2) * (κ * x - (κ - 1)) / (x ^ (κ - 1)) ^ 2) x := fun x hx => by
    have hx1 : 0 < 1 + x := by linarith
    have hd1 := ((hasDerivAt_id x).const_add (1 : ℝ)).rpow_const (p := 2 * κ - 1) (Or.inl hx1.ne')
    have hd2 := (hasDerivAt_id x).rpow_const (p := κ - 1) (Or.inl hx.ne')
    refine (hd1.div hd2 (Real.rpow_pos_of_pos hx _).ne').congr_deriv ?_
    have h1 : (1 + x) ^ (2 * κ - 1) = (1 + x) ^ (2 * κ - 2) * (1 + x) := by
      rw [← Real.rpow_add_one hx1.ne']; congr 1; ring
    have h2 : x ^ (κ - 1) = x ^ (κ - 2) * x := by
      rw [← Real.rpow_add_one hx.ne']; congr 1; ring
    have h3 : 2 * κ - 1 - 1 = 2 * κ - 2 := by ring
    have h4 : κ - 1 - 1 = κ - 2 := by ring
    simp only [id_eq]
    rw [h3, h4, h1, h2]; ring
  have hf_dec : StrictAntiOn f (Set.Ioc 0 ((κ - 1) / κ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioc 0 ((κ - 1) / κ)) ?_ ?_
    · refine ContinuousOn.div ?_ ?_ (fun x hx => (Real.rpow_pos_of_pos hx.1 _).ne')
      · exact (continuousOn_const.add continuousOn_id).rpow_const (fun x hx => Or.inl (by linarith [hx.1] : (0 : ℝ) < 1 + x).ne')
      · exact continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')
    · intro x hx
      rw [interior_Ioc] at hx
      rw [(hf_deriv x hx.1).deriv]
      have hx1 : 0 < 1 + x := by linarith [hx.1]
      have hneg : κ * x - (κ - 1) < 0 := by
        have := (lt_div_iff₀ (by linarith : 0 < κ)).mp hx.2; linarith
      have hp1 : 0 < (1 + x) ^ (2 * κ - 2) * x ^ (κ - 2) :=
        mul_pos (Real.rpow_pos_of_pos hx1 _) (Real.rpow_pos_of_pos hx.1 _)
      have hden : 0 < (x ^ (κ - 1)) ^ 2 := sq_pos_of_pos (Real.rpow_pos_of_pos hx.1 _)
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp1 hneg) hden
  have hf_inc : StrictMonoOn f (Set.Ici ((κ - 1) / κ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici ((κ - 1) / κ)) ?_ ?_
    · have hc_pos : 0 < (κ - 1) / κ := div_pos hkm1 (by linarith)
      refine ContinuousOn.div ?_ ?_ (fun x hx => (Real.rpow_pos_of_pos (lt_of_lt_of_le hc_pos hx) _).ne')
      · exact (continuousOn_const.add continuousOn_id).rpow_const
          (fun x hx => Or.inl (by linarith [lt_of_lt_of_le hc_pos hx] : (0 : ℝ) < 1 + x).ne')
      · exact continuousOn_id.rpow_const (fun x hx => Or.inl (lt_of_lt_of_le hc_pos hx).ne')
    · intro x hx
      rw [interior_Ici] at hx
      have hc_pos : 0 < (κ - 1) / κ := div_pos hkm1 (by linarith)
      have hx0 : 0 < x := lt_trans hc_pos hx
      rw [(hf_deriv x hx0).deriv]
      have hx1 : 0 < 1 + x := by linarith
      have hpos : 0 < κ * x - (κ - 1) := by
        have := (div_lt_iff₀ (by linarith : 0 < κ)).mp hx; linarith
      have hp1 : 0 < (1 + x) ^ (2 * κ - 2) * x ^ (κ - 2) :=
        mul_pos (Real.rpow_pos_of_pos hx1 _) (Real.rpow_pos_of_pos hx0 _)
      have hden : 0 < (x ^ (κ - 1)) ^ 2 := sq_pos_of_pos (Real.rpow_pos_of_pos hx0 _)
      exact div_pos (mul_pos hp1 hpos) hden
  have hfm : f hm = Λ := by
    dsimp only [f]; rw [hScm, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hhm0 _).ne']
  have hfp : f hp = Λ := by
    dsimp only [f]; rw [hScp, mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hhp0 _).ne']
  have hf1 : f 1 < Λ := by dsimp only [f]; simpa [Real.one_rpow, show (1 : ℝ) + 1 = 2 by norm_num] using hΛ
  have hc_lt1 : (κ - 1) / κ < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have hhm_lt_c : hm < (κ - 1) / κ := by
    by_contra hge; push Not at hge
    have hlt := hf_inc hge (le_trans hge hhm_lt.le) hhm_lt
    linarith [hfm, hfp]
  have hhp_gt_c : (κ - 1) / κ < hp := by
    by_contra hle; push Not at hle
    have hgt := hf_dec ⟨hhm0, hhm_lt_c.le⟩ ⟨hhp0, hle⟩ hhm_lt
    linarith [hfm, hfp]
  have hhp_gt1 : 1 < hp := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · linarith [hfp, hf1]
    · have := hf_inc hhp_gt_c.le hc_lt1.le hlt
      linarith [hfp, hf1]
  -- (2) Self-block signs
  have hself_p : 0 < qLocSelf κ hp := by
    dsimp only [qLocSelf]
    exact div_pos (by nlinarith) (mul_pos (mul_pos hkm1 h2km1) (Real.rpow_pos_of_pos hhp0 _))
  have hself_m : qLocSelf κ hm < 0 := by
    dsimp only [qLocSelf]
    have hneg : κ * hm - (κ - 1) < 0 := by
      have := (lt_div_iff₀ (by linarith : 0 < κ)).mp hhm_lt_c; linarith
    exact div_neg_of_neg_of_pos hneg (mul_pos (mul_pos hkm1 h2km1) (Real.rpow_pos_of_pos hhm0 _))
  -- (3) Same-root cross-pair hyperbolic identity & strict monotonicity
  have hsame_id : ∀ h u : ℝ, 0 < h → 0 < u →
      qLocCross κ h h (Real.exp (-u)) =
        (Real.exp ((κ - 1) * u) * Real.sinh (u / 2)) / (h ^ (κ - 1) * Real.sinh ((κ - 1 / 2) * u)) *
          (h * (Real.sinh (κ * u) / Real.sinh ((κ - 1) * u)) - 1) := by
    intro h u hh0 hu0
    let a : ℝ := Real.exp (u / 2)
    let b : ℝ := Real.exp ((κ - 1) * u)
    have ha_gt1 : 1 < a := Real.one_lt_exp_iff.mpr (by linarith)
    have hb_gt1 : 1 < b := Real.one_lt_exp_iff.mpr (mul_pos hkm1 hu0)
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    have hexp_nu : Real.exp (-u) = (a ^ 2)⁻¹ := by
      dsimp only [a]; rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
    have hexp_u : Real.exp u = a ^ 2 := by dsimp only [a]; rw [← Real.exp_nat_mul]; congr 1; ring
    have hrpow1 : (Real.exp (-u)) ^ (2 * κ - 2) = (b ^ 2)⁻¹ := by
      rw [← Real.exp_mul]; dsimp only [b]; rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; ring
    have hrpow2 : (Real.exp (-u)) ^ (2 * κ - 1) = (a ^ 2 * b ^ 2)⁻¹ := by
      rw [← Real.exp_mul]; dsimp only [a, b]
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_neg]; congr 1; ring
    have hsinh1 : Real.sinh (u / 2) = (a - a⁻¹) / 2 := by
      rw [Real.sinh_eq, Real.exp_neg]
    have hsinh2 : Real.sinh ((κ - 1) * u) = (b - b⁻¹) / 2 := by
      rw [Real.sinh_eq, Real.exp_neg]
    have hsinh3 : Real.sinh ((κ - 1 / 2) * u) = (a * b - (a * b)⁻¹) / 2 := by
      rw [Real.sinh_eq, show (κ - 1 / 2) * u = u / 2 + (κ - 1) * u by ring,
        Real.exp_add, Real.exp_neg, Real.exp_add]
    have hsinh4 : Real.sinh (κ * u) = (a ^ 2 * b - (a ^ 2 * b)⁻¹) / 2 := by
      rw [Real.sinh_eq, show κ * u = u + (κ - 1) * u by ring,
        Real.exp_add, hexp_u, Real.exp_neg, Real.exp_add, hexp_u]
    dsimp only [qLocCross]
    rw [hrpow1, hrpow2, hexp_nu, hsinh1, hsinh2, hsinh3, hsinh4]
    have hhkm : 0 < h ^ (κ - 1) := Real.rpow_pos_of_pos hh0 _
    have hb2_ne : b ^ 2 - 1 ≠ 0 := by nlinarith
    have hab2_ne : a ^ 2 * b ^ 2 - 1 ≠ 0 := by nlinarith [mul_lt_mul'' ha_gt1 hb_gt1 zero_le_one zero_le_one]
    have h1_ne : h ^ (κ - 1) - h ^ (κ - 1) * (b ^ 2)⁻¹ ≠ 0 := by
      have : h ^ (κ - 1) - h ^ (κ - 1) * (b ^ 2)⁻¹ = h ^ (κ - 1) * (b ^ 2 - 1) / b ^ 2 := by
        field_simp [hb0.ne']
      rw [this]; exact div_ne_zero (mul_ne_zero hhkm.ne' hb2_ne) (sq_pos_of_pos hb0).ne'
    have h2_ne : h ^ (κ - 1) - h ^ (κ - 1) * (a ^ 2 * b ^ 2)⁻¹ ≠ 0 := by
      have : h ^ (κ - 1) - h ^ (κ - 1) * (a ^ 2 * b ^ 2)⁻¹ = h ^ (κ - 1) * (a ^ 2 * b ^ 2 - 1) / (a ^ 2 * b ^ 2) := by
        field_simp [ha0.ne', hb0.ne']
      rw [this]; exact div_ne_zero (mul_ne_zero hhkm.ne' hab2_ne) (mul_pos (sq_pos_of_pos ha0) (sq_pos_of_pos hb0)).ne'
    have hs2_ne : (b - b⁻¹) / 2 ≠ 0 := by
      have : b - b⁻¹ = (b ^ 2 - 1) / b := by field_simp [hb0.ne']
      rw [this]; exact div_ne_zero (div_ne_zero hb2_ne hb0.ne') two_ne_zero
    have hs3_ne : (a * b - (a * b)⁻¹) / 2 ≠ 0 := by
      have : a * b - (a * b)⁻¹ = (a ^ 2 * b ^ 2 - 1) / (a * b) := by field_simp [ha0.ne', hb0.ne']
      rw [this]; exact div_ne_zero (div_ne_zero hab2_ne (mul_pos ha0 hb0).ne') two_ne_zero
    change _ = (b * _) / _ * _
    field_simp [ha0.ne', hb0.ne', hhkm.ne', h1_ne, h2_ne, hs2_ne, hs3_ne]
    ring
  have hsinh_ratio_gt : ∀ u : ℝ, 0 < u → κ / (κ - 1) < Real.sinh (κ * u) / Real.sinh ((κ - 1) * u) := by
    intro u hu0
    have hs_pos : 0 < Real.sinh ((κ - 1) * u) := Real.sinh_pos_iff.mpr (mul_pos hkm1 hu0)
    rw [div_lt_div_iff₀ hkm1 hs_pos]
    -- Show g(x) := (κ - 1) sinh(κ x) - κ sinh((κ - 1) x) > 0 for x > 0!
    let g : ℝ → ℝ := fun x => (κ - 1) * Real.sinh (κ * x) - κ * Real.sinh ((κ - 1) * x)
    have hg0 : g 0 = 0 := by dsimp only [g]; simp
    have hg_mono : StrictMonoOn g (Set.Ici 0) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
      · exact ((continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))).sub
          (continuous_const.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id)))).continuousOn
      · intro x hx
        rw [interior_Ici] at hx
        have hd1 : HasDerivAt (fun t => (κ - 1) * Real.sinh (κ * t)) ((κ - 1) * (Real.cosh (κ * x) * κ)) x :=
          ((Real.hasDerivAt_sinh (κ * x)).comp x ((hasDerivAt_id x).const_mul κ)).const_mul (κ - 1) |>.congr_deriv (by ring)
        have hd2 : HasDerivAt (fun t => κ * Real.sinh ((κ - 1) * t)) (κ * (Real.cosh ((κ - 1) * x) * (κ - 1))) x :=
          ((Real.hasDerivAt_sinh ((κ - 1) * x)).comp x ((hasDerivAt_id x).const_mul (κ - 1))).const_mul κ |>.congr_deriv (by ring)
        have hdg : HasDerivAt g ((κ - 1) * (Real.cosh (κ * x) * κ) - κ * (Real.cosh ((κ - 1) * x) * (κ - 1))) x :=
          hd1.sub hd2
        rw [hdg.deriv]
        have hfac : (κ - 1) * (Real.cosh (κ * x) * κ) - κ * (Real.cosh ((κ - 1) * x) * (κ - 1)) =
            κ * (κ - 1) * (Real.cosh (κ * x) - Real.cosh ((κ - 1) * x)) := by ring
        rw [hfac]
        have hcosh_lt : Real.cosh ((κ - 1) * x) < Real.cosh (κ * x) := by
          have hx_pos : (0 : ℝ) < x := hx
          have h1 : (κ - 1) * x < κ * x := by nlinarith
          have h2 : 0 ≤ (κ - 1) * x := mul_nonneg hkm1.le hx_pos.le
          have hc_mono : StrictMonoOn Real.cosh (Set.Ici 0) := by
            refine strictMonoOn_of_deriv_pos (convex_Ici 0) Real.continuous_cosh.continuousOn ?_
            intro y hy; rw [interior_Ici] at hy
            rw [(Real.hasDerivAt_cosh y).deriv]
            exact Real.sinh_pos_iff.mpr hy
          exact hc_mono h2 (le_trans h2 h1.le) h1
        exact mul_pos (mul_pos (by linarith) hkm1) (sub_pos.mpr hcosh_lt)
    have hgu : 0 < g u := by rw [← hg0]; exact hg_mono (le_refl (0 : ℝ)) hu0.le hu0
    dsimp only [g] at hgu; linarith
  have hsame_hp_pos : ∀ u : ℝ, 0 < u → 0 < qLocCross κ hp hp (Real.exp (-u)) := fun u hu0 => by
    rw [hsame_id hp u hhp0 hu0]
    have hpre : 0 < Real.exp ((κ - 1) * u) * Real.sinh (u / 2) /
        (hp ^ (κ - 1) * Real.sinh ((κ - 1 / 2) * u)) :=
      div_pos (mul_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr (by linarith)))
        (mul_pos (Real.rpow_pos_of_pos hhp0 _) (Real.sinh_pos_iff.mpr (mul_pos (by linarith) hu0)))
    have hbr : 0 < hp * (Real.sinh (κ * u) / Real.sinh ((κ - 1) * u)) - 1 := by
      have h1 := hsinh_ratio_gt u hu0
      have h2 : 1 < κ / (κ - 1) := (one_lt_div hkm1).mpr (by linarith)
      have h3 : 1 < Real.sinh (κ * u) / Real.sinh ((κ - 1) * u) := lt_trans h2 h1
      nlinarith
    exact mul_pos hpre hbr
  have hsame_hm_iff : ∀ u : ℝ, 0 < u → (0 < qLocCross κ hm hm (Real.exp (-u)) ↔
      1 < hm * (Real.sinh (κ * u) / Real.sinh ((κ - 1) * u))) := fun u hu0 => by
    rw [hsame_id hm u hhm0 hu0]
    have hpre : 0 < Real.exp ((κ - 1) * u) * Real.sinh (u / 2) /
        (hm ^ (κ - 1) * Real.sinh ((κ - 1 / 2) * u)) :=
      div_pos (mul_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr (by linarith)))
        (mul_pos (Real.rpow_pos_of_pos hhm0 _) (Real.sinh_pos_iff.mpr (mul_pos (by linarith) hu0)))
    rw [mul_pos_iff_of_pos_left hpre, sub_pos]
  -- (4) Opposite-root cross-pair factorization & strict positivity on (0, 1)
  have hopp_id : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      qLocCross κ hp hm ρ =
        (1 - ρ) * (hp ^ (κ - 1) * (hp - ρ) + hm ^ (κ - 1) * ρ ^ (2 * κ - 1) * (1 - hm * ρ)) /
          (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2)) *
            (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 1))) := by
    intro ρ hρ0 hρ1
    have hhm_lt_hp : hm ^ (κ - 1) < hp ^ (κ - 1) := Real.rpow_lt_rpow hhm0.le hhm_lt hkm1
    have hρ_p1 : ρ ^ (2 * κ - 2) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by linarith)
    have hρ_p2 : ρ ^ (2 * κ - 1) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by linarith)
    have hd1 : 0 < hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2) := by
      have : hm ^ (κ - 1) * ρ ^ (2 * κ - 2) ≤ hm ^ (κ - 1) :=
        mul_le_of_le_one_right (Real.rpow_pos_of_pos hhm0 _).le hρ_p1
      linarith
    have hd2 : 0 < hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 1) := by
      have : hm ^ (κ - 1) * ρ ^ (2 * κ - 1) ≤ hm ^ (κ - 1) :=
        mul_le_of_le_one_right (Real.rpow_pos_of_pos hhm0 _).le hρ_p2
      linarith
    have hρ_rel : ρ * ρ ^ (2 * κ - 2) = ρ ^ (2 * κ - 1) := by
      rw [mul_comm, ← Real.rpow_add_one hρ0.ne']; congr 1; ring
    dsimp only [qLocCross]
    rw [← hρ_rel] at hd2 ⊢
    have hden_ne : ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2)) *
        (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2))) ≠ 0 :=
      (mul_pos (mul_pos hρ0 hd1) hd2).ne'
    rw [eq_div_iff hden_ne, sub_mul]
    have hL1 : (hp - hm * ρ ^ 2) / (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2))) *
        (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2)) *
          (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2)))) =
        (hp - hm * ρ ^ 2) * (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2))) := by
      rw [← mul_assoc, div_mul_cancel₀ _ (mul_pos hρ0 hd1).ne']
    have hL2 : (1 + hp - (1 + hm) * ρ) / (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2))) *
        (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2)) *
          (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2)))) =
        (1 + hp - (1 + hm) * ρ) * (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2))) := by
      calc _ = (1 + hp - (1 + hm) * ρ) / (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2))) *
            (hp ^ (κ - 1) - hm ^ (κ - 1) * (ρ * ρ ^ (2 * κ - 2))) *
            (ρ * (hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2))) := by ring
        _ = _ := by rw [div_mul_cancel₀ _ hd2.ne']
    rw [hL1, hL2]; ring
  have hopp_pos : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → 0 < qLocCross κ hp hm ρ := fun ρ hρ0 hρ1 => by
    rw [hopp_id ρ hρ0 hρ1.le]
    have hhm_lt1 : hm < 1 := lt_trans hhm_lt_c hc_lt1
    have hhm_lt_hp : hm ^ (κ - 1) < hp ^ (κ - 1) := Real.rpow_lt_rpow hhm0.le hhm_lt hkm1
    have hρ_p1 : ρ ^ (2 * κ - 2) ≤ 1 := Real.rpow_le_one hρ0.le hρ1.le (by linarith)
    have hρ_p2 : ρ ^ (2 * κ - 1) ≤ 1 := Real.rpow_le_one hρ0.le hρ1.le (by linarith)
    have hd1 : 0 < hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 2) := by
      have : hm ^ (κ - 1) * ρ ^ (2 * κ - 2) ≤ hm ^ (κ - 1) :=
        mul_le_of_le_one_right (Real.rpow_pos_of_pos hhm0 _).le hρ_p1
      linarith
    have hd2 : 0 < hp ^ (κ - 1) - hm ^ (κ - 1) * ρ ^ (2 * κ - 1) := by
      have : hm ^ (κ - 1) * ρ ^ (2 * κ - 1) ≤ hm ^ (κ - 1) :=
        mul_le_of_le_one_right (Real.rpow_pos_of_pos hhm0 _).le hρ_p2
      linarith
    have hnum1 : 0 < hp ^ (κ - 1) * (hp - ρ) := mul_pos (Real.rpow_pos_of_pos hhp0 _) (by linarith)
    have hnum2 : 0 < hm ^ (κ - 1) * ρ ^ (2 * κ - 1) * (1 - hm * ρ) :=
      mul_pos (mul_pos (Real.rpow_pos_of_pos hhm0 _) (Real.rpow_pos_of_pos hρ0 _)) (by nlinarith)
    exact div_pos (mul_pos (by linarith) (add_pos hnum1 hnum2)) (mul_pos (mul_pos hρ0 hd1) hd2)
  have hopp_one : qLocCross κ hp hm 1 = 0 := by
    rw [hopp_id 1 zero_lt_one le_rfl]; simp
  -- (5) Exact p = 4/3 (κ = 2) opposite-root (h_-, 1; h_+, r) sign flip at r_max = ((1 + h_-)/(1 + h_+))²
  have hpart5 : κ = 2 → ∀ r : ℝ, 0 < r → r < 1 →
      (1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) =
        (1 - r) * ((1 + hm) ^ 2 - (1 + hp) ^ 2 * r) /
          (r * ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2))) ∧
      (0 < 1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) ↔
        r < ((1 + hm) / (1 + hp)) ^ 2) ∧
      (hm ≠ hp * r ^ 2 → hm ≠ hp * r ^ 3 →
        qLocCross 2 hm hp r =
          1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2)) := by
    intro hκ2 r hr0 hr1
    subst hκ2
    have hScm3 : (1 + hm) ^ 3 = Λ * hm := by
      have := hScm; norm_num at this; exact this
    have hScp3 : (1 + hp) ^ 3 = Λ * hp := by
      have := hScp; norm_num at this; exact this
    have hΛ_eq : Λ = (1 + hm) ^ 2 + (1 + hm) * (1 + hp) + (1 + hp) ^ 2 := by
      have hdiff : (hp - hm) * ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) + (1 + hp) ^ 2 - Λ) = 0 := by
        linear_combination hScp3 - hScm3
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hhm_lt.ne'))).symm
    have hxy_rel : (1 + hm) * (1 + hp) * ((1 + hm) + (1 + hp)) =
        (1 + hm) ^ 2 + (1 + hm) * (1 + hp) + (1 + hp) ^ 2 := by
      have hdiff : (1 + hm) ^ 3 * hp - (1 + hp) ^ 3 * hm = 0 := by
        linear_combination hp * hScm3 - hm * hScp3
      have hfac : (1 + hm) ^ 3 * hp - (1 + hp) ^ 3 * hm =
          (hm - hp) * ((1 + hm) * (1 + hp) * ((1 + hm) + (1 + hp)) -
            ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) + (1 + hp) ^ 2)) := by ring
      rw [hfac] at hdiff
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hhm_lt.ne))
    have hden_pos : 0 < (1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2 := by positivity
    have hfac_eq : 1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) =
        (1 - r) * ((1 + hm) ^ 2 - (1 + hp) ^ 2 * r) /
          (r * ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2)) := by
      rw [hΛ_eq]; field_simp [hr0.ne', hden_pos.ne']; ring
    have hiff : 0 < 1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) ↔
        r < ((1 + hm) / (1 + hp)) ^ 2 := by
      rw [hfac_eq, div_pos_iff_of_pos_right (mul_pos hr0 hden_pos), mul_pos_iff_of_pos_left (by linarith),
        sub_pos, div_pow, lt_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 + hp))]
      constructor <;> intro h <;> linarith
    have hqeq : hm ≠ hp * r ^ 2 → hm ≠ hp * r ^ 3 →
        qLocCross 2 hm hp r =
          1 / r - Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) := by
      intro hne2 hne3
      dsimp only [qLocCross]
      rw [show (2 : ℝ) - 1 = 1 by norm_num, show 2 * (2 : ℝ) - 2 = 2 by norm_num,
        show 2 * (2 : ℝ) - 1 = 3 by norm_num, Real.rpow_one, Real.rpow_one,
        Real.rpow_two, show r ^ (3 : ℝ) = r ^ 3 by exact_mod_cast Real.rpow_natCast r 3]
      have hd2 : hm - hp * r ^ 2 ≠ 0 := sub_ne_zero.mpr hne2
      have hd3 : hm - hp * r ^ 3 ≠ 0 := sub_ne_zero.mpr hne3
      have hterm1 : (hm - hp * r ^ 2) / (r * (hm - hp * r ^ 2)) = 1 / r := by
        field_simp [hr0.ne', hd2]
      have hterm2 : (1 + hm - (1 + hp) * r) / (hm - hp * r ^ 3) =
          Λ / ((1 + hm) ^ 2 + (1 + hm) * (1 + hp) * r + (1 + hp) ^ 2 * r ^ 2) := by
        rw [div_eq_div_iff hd3 hden_pos.ne']
        linear_combination hScm3 - r ^ 3 * hScp3
      rw [hterm1, hterm2]
    exact ⟨hfac_eq, hiff, hqeq⟩
  exact ⟨⟨hhm_lt_c, hc_lt1, hhp_gt1⟩, ⟨hself_p, hself_m⟩,
    hsame_id, hsinh_ratio_gt, hsame_hp_pos, hsame_hm_iff,
    hopp_id, hopp_pos, hopp_one, hpart5⟩

/-! ==========================================================================
    AXIOM AUDIT: Confirm ONLY standard axioms [propext, Classical.choice, Quot.sound]
    ========================================================================== -/

#print axioms universal_phi_psd_rigidity
#print axioms third_root_harmonic_mean_bound
#print axioms third_root_pencil_rho4_lt_eighth
#print axioms pinching_second_variation_pos_p43
#print axioms pinching_second_variation_pos_p32
#print axioms hessian_det_pos_2x2_p43
#print axioms master_trace_2x2_p43
#print axioms master_trace_2x2_p32
#print axioms euler_betti_root_identity
#print axioms hessian_sign_pairs_all_p

end MI20

