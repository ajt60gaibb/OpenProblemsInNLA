/-
  MI20/Theorem9_10_CommutatorAndQuadraticBound.lean
  =================================================
  Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Purpose:     Complete Mathlib-grounded, zero-sorry Lean 4.33.1 formalization of:
                 - Theorem 9(a) (`universal_commutator_identity`, `universal_commutator_theorem`):
                   Exact commutator miracle for Holden's positive power system at every κ > 1,
                   proving [D, G_j^κ - D G_j^(κ-1) D] = 0 for every summand j individually.
                 - Theorem 9(b) (`power_variance_lemma`):
                   Elementary power-variance inequality (with exact equality characterization):
                   E[X^α] ≥ E[X] ⟹ Var(X^α) ≥ Var(X) for all X > 0 and α > 1.
                 - Theorem 9(c) (`top_eigenspace_spectral_dichotomy`):
                   Every nonnegative eigenvalue of Φ_j on the top eigenspace E_max = ker(D - d_max I)
                   equals +σ_+(Λ) = h_+(Λ)^(κ-1)(h_+(Λ) - 1) with decoupled eigenvector H_j v = h_+ d_max v.
                 - Theorem 10 (`universal_algebraic_upper_bound`, `universal_bound_p43_m2`,
                   `universal_bound_p32_m2`, `universal_quadratic_log_bound`):
                   Universal pure-algebraic upper bound for all 1 < p < 2 and all m ≥ 2:
                     h_+(Λ)^(κ-1) (h_+(Λ) - 1) ≤ (m - 1) (κ - 1)^(κ - 1) / κ^κ,
                   including the closed-form radical caps Λ ≤ (13 + 16√2)/4 < 891/100 (p = 4/3, m = 2),
                   Λ ≤ 49√3/18 < 472/100 (p = 3/2, m = 2), and the first dimension-free non-asymptotic
                   quadratic upper bound log C_{p,m}(∞) ≤ ((m^2 - 1) / (2 p^2)) (p - 1)^2 solving Open Question 2.
-/

import MI20.Theorem5_PSDReduction
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ==========================================================================
    PART 1: Positive-Definite Congruence, Scaling, and Eigenvector Helpers
    ========================================================================== -/

lemma posDef_mulVec_ne_zero {n : ℕ} {A : Mat n} (hA : A.PosDef) {x : Fin n → ℂ} (hx : x ≠ 0) :
    A.mulVec x ≠ 0 := by
  intro h0
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 hx
  rw [h0, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

lemma posDef_conj_of_posDef {n : ℕ} {A B : Mat n} (hA : A.PosDef) (hB : B.PosDef) :
    (A * B * A).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hHerm : (A * B * A).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hA.isHermitian.eq, hB.isHermitian.eq, Matrix.mul_assoc]
  refine ⟨hHerm, fun x hx => ?_⟩
  have hAx : A.mulVec x ≠ 0 := posDef_mulVec_ne_zero hA hx
  have hquad : star x ⬝ᵥ (A * B * A).mulVec x = star (A.mulVec x) ⬝ᵥ B.mulVec (A.mulVec x) := by
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have hst : star x ᵥ* A = star (A.mulVec x) := by
      rw [Matrix.star_mulVec, hA.isHermitian.eq]
    rw [hst]
  rw [hquad]
  exact (Matrix.posDef_iff_dotProduct_mulVec.mp hB).2 hAx

lemma posDef_mul_left_cancel {n : ℕ} {A X Y : Mat n} (hA : A.PosDef) (h : A * X = A * Y) :
    X = Y := by
  have hinv : A * posDefPow (-1) hA = 1 := by
    calc A * posDefPow (-1) hA
        = posDefPow 1 hA * posDefPow (-1) hA := by rw [posDefPow_one]
      _ = posDefPow (1 + (-1)) hA := posDefPow_mul_posDefPow 1 (-1) hA
      _ = 1 := by norm_num; exact posDefPow_zero hA
  have hinvL : posDefPow (-1) hA * A = 1 := by
    calc posDefPow (-1) hA * A
        = posDefPow (-1) hA * posDefPow 1 hA := by rw [posDefPow_one]
      _ = posDefPow (-1 + 1) hA := posDefPow_mul_posDefPow (-1) 1 hA
      _ = 1 := by norm_num; exact posDefPow_zero hA
  calc X = 1 * X := (Matrix.one_mul X).symm
    _ = (posDefPow (-1) hA * A) * X := by rw [hinvL]
    _ = posDefPow (-1) hA * (A * X) := Matrix.mul_assoc _ _ _
    _ = posDefPow (-1) hA * (A * Y) := by rw [h]
    _ = (posDefPow (-1) hA * A) * Y := (Matrix.mul_assoc _ _ _).symm
    _ = Y := by rw [hinvL, Matrix.one_mul]

lemma posDef_mul_right_cancel {n : ℕ} {A X Y : Mat n} (hA : A.PosDef) (h : X * A = Y * A) :
    X = Y := by
  have hinv : A * posDefPow (-1) hA = 1 := by
    calc A * posDefPow (-1) hA
        = posDefPow 1 hA * posDefPow (-1) hA := by rw [posDefPow_one]
      _ = posDefPow (1 + (-1)) hA := posDefPow_mul_posDefPow 1 (-1) hA
      _ = 1 := by norm_num; exact posDefPow_zero hA
  calc X = X * 1 := (Matrix.mul_one X).symm
    _ = X * (A * posDefPow (-1) hA) := by rw [hinv]
    _ = (X * A) * posDefPow (-1) hA := (Matrix.mul_assoc _ _ _).symm
    _ = (Y * A) * posDefPow (-1) hA := by rw [h]
    _ = Y * (A * posDefPow (-1) hA) := Matrix.mul_assoc _ _ _
    _ = Y := by rw [hinv, Matrix.mul_one]

lemma posDefPow_comm_self {n : ℕ} (r : ℝ) {T : Mat n} (hT : T.PosDef) :
    T * posDefPow r hT = posDefPow r hT * T := by
  calc T * posDefPow r hT
      = posDefPow 1 hT * posDefPow r hT := by rw [posDefPow_one]
    _ = posDefPow (1 + r) hT := posDefPow_mul_posDefPow 1 r hT
    _ = posDefPow (r + 1) hT := by rw [add_comm]
    _ = posDefPow r hT * posDefPow 1 hT := (posDefPow_mul_posDefPow r 1 hT).symm
    _ = posDefPow r hT * T := by rw [posDefPow_one]

lemma posDefPow_smul {n : ℕ} (r : ℝ) {c : ℝ} (hc : 0 < c) {T : Mat n} (hT : T.PosDef) :
    posDefPow r (hT.smul hc) = ((c ^ r : ℝ) : ℂ) • posDefPow r hT := by
  let U := hT.isHermitian.eigenvectorUnitary
  let lam := hT.isHermitian.eigenvalues
  have hT_eq : T = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hT.isHermitian.spectral_theorem
  have hcT_eq : c • T =
      (U : Mat n) * Matrix.diagonal (fun i => ((c * lam i : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
    have hsm : c • T = ((c : ℝ) : ℂ) • T := by ext i j; simp [Complex.real_smul]
    rw [hsm, hT_eq, ← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 1; congr 1; ext i j
    by_cases hij : i = j
    · subst hij; simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  rw [posDefPow_eq_of_diag r (hT.smul hc) U (fun i => c * lam i)
    (fun i => mul_pos hc (hT.eigenvalues_pos i)) hcT_eq]
  unfold posDefPow
  rw [← Matrix.smul_mul, ← Matrix.mul_smul]
  congr 1; congr 1; ext i j
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, ← Complex.ofReal_mul]
    congr 1
    exact Real.mul_rpow hc.le (hT.eigenvalues_pos i).le
  · simp [Matrix.diagonal, hij]

lemma posDefPow_mulVec_of_eig {n : ℕ} (r : ℝ) {T : Mat n} (hT : T.PosDef)
    {v : Fin n → ℂ} (hv : v ≠ 0) {μ : ℝ} (heig : T.mulVec v = (μ : ℂ) • v) :
    0 < μ ∧ (posDefPow r hT).mulVec v = ((μ ^ r : ℝ) : ℂ) • v := by
  have hμ : 0 < μ := by
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hT).2 hv
    rw [heig, dotProduct_smul, smul_eq_mul] at hpos
    have hvv : 0 < (star v ⬝ᵥ v).re := by
      rw [dotProduct, Complex.re_sum]
      have hnn : ∀ i, 0 ≤ (star (v i) * v i).re := fun i => by
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        exact sq_nonneg _
      obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
        by_contra hall; push Not at hall; exact hv (funext hall)
      refine Finset.sum_pos' (fun i _ => hnn i) ⟨i0, Finset.mem_univ _, ?_⟩
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_pos_of_pos (norm_pos_iff.mpr hi0)
    have hre : 0 < ((μ : ℂ) * (star v ⬝ᵥ v)).re := by
      have := Complex.lt_def.mp hpos; exact this.1
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    exact pos_of_mul_pos_left hre hvv.le
  refine ⟨hμ, ?_⟩
  let U := hT.isHermitian.eigenvectorUnitary
  let lam := hT.isHermitian.eigenvalues
  let y : Fin n → ℂ := (U : Mat n)ᴴ.mulVec v
  have hT_eq : T = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hT.isHermitian.spectral_theorem
  have hdiag_y : (Matrix.diagonal (fun i => (lam i : ℂ))).mulVec y = (μ : ℂ) • y := by
    have h1 := congrArg (Matrix.mulVec (U : Mat n)ᴴ) heig
    rw [hT_eq] at h1
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at h1
    rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U,
      Matrix.one_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
    exact h1
  have hcomp : ∀ i : Fin n, y i ≠ 0 → lam i = μ := by
    intro i hyi
    have hi := congr_fun hdiag_y i
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hi
    have hsub : ((lam i : ℂ) - (μ : ℂ)) * y i = 0 := by linear_combination hi
    exact Complex.ofReal_injective (sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hyi))
  have hpow_y : (Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ))).mulVec y =
      ((μ ^ r : ℝ) : ℂ) • y := by
    ext i
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hyi : y i = 0
    · simp [hyi]
    · rw [hcomp i hyi]
  unfold posDefPow
  change ((U : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ)) * (U : Mat n)ᴴ).mulVec v = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (U : Mat n).mulVec ((Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ))).mulVec y) = _
  rw [hpow_y, Matrix.mulVec_smul]
  simp only [y, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec]

/-! ==========================================================================
    PART 2: Theorem 9(a) — Universal Commutator Identity and Theorem
    ========================================================================== -/

/-- Exact 2-line commutator identity (Theorem 9a, identity form):
    For every n ≥ 1, every real κ, and every pair of positive-definite matrices D, H ∈ Mat n,
    setting G := D^(1/2) H D^(1/2) and Φ := G^κ - D G^(κ-1) D:
      D^(1/2) [D + H, D^(1/2) G^(κ-1) D^(1/2)] D^(1/2) = -[D, Φ]. -/
theorem universal_commutator_identity {n : ℕ} {κ : ℝ} {D H : Mat n}
    (hD : D.PosDef) (hH : H.PosDef) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
    let Gkm1 := posDefPow (κ - 1) hG
    let Gk := posDefPow κ hG
    let Phi := Gk - D * Gkm1 * D
    let Rhs := Dhalf * Gkm1 * Dhalf
    Dhalf * ((D + H) * Rhs - Rhs * (D + H)) * Dhalf = -(D * Phi - Phi * D) := by
  intro Dhalf hG Gkm1 Gk Phi Rhs
  have hDhalf_sq : Dhalf * Dhalf = D := by
    dsimp [Dhalf]
    rw [posDefPow_mul_posDefPow]
    norm_num
    exact posDefPow_one hD
  have hDhalf_D_Dhalf : Dhalf * D * Dhalf = D * D := by
    calc Dhalf * D * Dhalf
        = Dhalf * (Dhalf * Dhalf) * Dhalf := by rw [hDhalf_sq]
      _ = (Dhalf * Dhalf) * (Dhalf * Dhalf) := by simp only [Matrix.mul_assoc]
      _ = D * D := by rw [hDhalf_sq]
  have hG_Gkm1 : (Dhalf * H * Dhalf) * Gkm1 = Gk := by
    calc (Dhalf * H * Dhalf) * Gkm1
        = posDefPow 1 hG * posDefPow (κ - 1) hG := by rw [posDefPow_one]
      _ = posDefPow (1 + (κ - 1)) hG := posDefPow_mul_posDefPow 1 (κ - 1) hG
      _ = Gk := by dsimp [Gk]; congr 1; ring
  have hGkm1_G : Gkm1 * (Dhalf * H * Dhalf) = Gk := by
    calc Gkm1 * (Dhalf * H * Dhalf)
        = posDefPow (κ - 1) hG * posDefPow 1 hG := by rw [posDefPow_one]
      _ = posDefPow ((κ - 1) + 1) hG := posDefPow_mul_posDefPow (κ - 1) 1 hG
      _ = Gk := by dsimp [Gk]; congr 1; ring
  have hL1 : Dhalf * ((D + H) * Rhs) * Dhalf = D * (D * Gkm1 * D) + Gk * D := by
    dsimp [Rhs]
    calc Dhalf * ((D + H) * (Dhalf * Gkm1 * Dhalf)) * Dhalf
        = (Dhalf * (D + H) * Dhalf) * Gkm1 * (Dhalf * Dhalf) := by simp only [Matrix.mul_assoc]
      _ = (Dhalf * D * Dhalf + Dhalf * H * Dhalf) * Gkm1 * D := by
            rw [hDhalf_sq, Matrix.mul_add, Matrix.add_mul]
      _ = (D * D + Dhalf * H * Dhalf) * Gkm1 * D := by rw [hDhalf_D_Dhalf]
      _ = (D * D) * Gkm1 * D + ((Dhalf * H * Dhalf) * Gkm1) * D := by
            rw [Matrix.add_mul, Matrix.add_mul]
      _ = D * (D * Gkm1 * D) + Gk * D := by rw [hG_Gkm1]; simp only [Matrix.mul_assoc]
  have hL2 : Dhalf * (Rhs * (D + H)) * Dhalf = (D * Gkm1 * D) * D + D * Gk := by
    dsimp [Rhs]
    calc Dhalf * ((Dhalf * Gkm1 * Dhalf) * (D + H)) * Dhalf
        = (Dhalf * Dhalf) * Gkm1 * (Dhalf * (D + H) * Dhalf) := by simp only [Matrix.mul_assoc]
      _ = D * Gkm1 * (Dhalf * D * Dhalf + Dhalf * H * Dhalf) := by
            rw [hDhalf_sq, Matrix.mul_add, Matrix.add_mul]
      _ = D * Gkm1 * (D * D + Dhalf * H * Dhalf) := by rw [hDhalf_D_Dhalf]
      _ = D * Gkm1 * (D * D) + D * (Gkm1 * (Dhalf * H * Dhalf)) := by
            rw [Matrix.mul_add]; congr 1; exact Matrix.mul_assoc _ _ _
      _ = (D * Gkm1 * D) * D + D * Gk := by rw [hGkm1_G]; simp only [Matrix.mul_assoc]
  rw [Matrix.mul_sub, Matrix.sub_mul, hL1, hL2]
  dsimp [Phi]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- Universal Commutator Theorem (Theorem 9a):
    Every solution (D, H) of Holden's positive power equation
      (D + H)^(2κ - 1) = Λ D^(1/2) G^(κ - 1) D^(1/2)   (Λ > 0)
    automatically satisfies [D, Φ] = 0, i.e., D * Φ = Φ * D! -/
theorem universal_commutator_theorem {n : ℕ} {κ Λ : ℝ} (hΛ : 0 < Λ) {D H : Mat n}
    (hD : D.PosDef) (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD)) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
    let Phi := posDefPow κ hG - D * posDefPow (κ - 1) hG * D
    D * Phi = Phi * D := by
  intro Dhalf hG Phi
  let Rhs := Dhalf * posDefPow (κ - 1) hG * Dhalf
  have hcomm_pow : (D + H) * posDefPow (2 * κ - 1) (hD.add hH) =
      posDefPow (2 * κ - 1) (hD.add hH) * (D + H) :=
    posDefPow_comm_self (2 * κ - 1) (hD.add hH)
  rw [hEq, Matrix.mul_smul, Matrix.smul_mul] at hcomm_pow
  have hΛc : (Λ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΛ.ne'
  have hcomm_Rhs : (D + H) * Rhs = Rhs * (D + H) := smul_right_injective (Mat n) hΛc hcomm_pow
  have hid := universal_commutator_identity (κ := κ) hD hH
  dsimp only at hid
  change Dhalf * ((D + H) * Rhs - Rhs * (D + H)) * Dhalf = -(D * Phi - Phi * D) at hid
  rw [hcomm_Rhs, sub_self, Matrix.mul_zero, Matrix.zero_mul] at hid
  exact sub_eq_zero.mp (neg_eq_zero.mp hid.symm)

/-! ==========================================================================
    PART 3: Theorem 9(b) — Elementary Power-Variance Lemma
    ========================================================================== -/

private lemma rpow_sub_id_strictMono_Ici {α a b : ℝ} (hα : 1 < α) (ha : 1 ≤ a) (hab : a < b) :
    a ^ α - a < b ^ α - b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  set t : ℝ := b / a
  have ht1 : 1 < t := (one_lt_div ha0).mpr hab
  have ht_rpow : t < t ^ α := by
    simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt ht1 hα
  have ha_pow : a ≤ a ^ α := by
    simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ha hα.le
  have hba : b ^ α = a ^ α * t ^ α := by
    rw [← Real.mul_rpow ha0.le (by linarith : 0 ≤ t)]
    dsimp [t]; rw [mul_div_cancel₀ b ha0.ne']
  have h1 : a ^ α * (t - 1) < a ^ α * (t ^ α - 1) :=
    mul_lt_mul_of_pos_left (by linarith) (Real.rpow_pos_of_pos ha0 α)
  have h2 : a * (t - 1) ≤ a ^ α * (t - 1) :=
    mul_le_mul_of_nonneg_right ha_pow (by linarith)
  have h3 : a * (t - 1) = b - a := by dsimp [t]; field_simp [ha0.ne']
  linarith

/-- Power-Variance Lemma (Theorem 9b):
    For any finite probability distribution (w_i ≥ 0, ∑ w_i = 1) on strictly positive values x_i > 0
    and any exponent α > 1, if E[X^α] ≥ E[X] then Var(X^α) ≥ Var(X), with equality if and only if
    X is constant on the support {i : w_i > 0}. -/
theorem power_variance_lemma {n : ℕ} {w x : Fin n → ℝ} {α : ℝ}
    (hα : 1 < α) (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i : Fin n, w i = 1)
    (hx : ∀ i, 0 < x i) (hmean : ∑ i : Fin n, w i * x i ≤ ∑ i : Fin n, w i * (x i) ^ α) :
    (∑ i : Fin n, w i * (x i) ^ 2 - (∑ i : Fin n, w i * x i) ^ 2 ≤
      ∑ i : Fin n, w i * ((x i) ^ α) ^ 2 - (∑ i : Fin n, w i * (x i) ^ α) ^ 2) ∧
    (∑ i : Fin n, w i * (x i) ^ 2 - (∑ i : Fin n, w i * x i) ^ 2 =
      ∑ i : Fin n, w i * ((x i) ^ α) ^ 2 - (∑ i : Fin n, w i * (x i) ^ α) ^ 2 →
      ∀ i j : Fin n, 0 < w i → 0 < w j → x i = x j) := by
  let y : Fin n → ℝ := fun i => (x i) ^ α
  let mx : ℝ := ∑ i : Fin n, w i * x i
  let my : ℝ := ∑ i : Fin n, w i * y i
  let s : ℝ := my + mx
  -- Exact algebraic identity: Var(Y) - Var(X) = ∑ w_i (y_i - x_i) (y_i + x_i - s)
  have hdiff : (∑ i : Fin n, w i * (y i) ^ 2 - my ^ 2) -
      (∑ i : Fin n, w i * (x i) ^ 2 - mx ^ 2) =
      ∑ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) := by
    have hexp : ∀ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) =
        w i * (y i) ^ 2 - w i * (x i) ^ 2 - s * (w i * y i - w i * x i) := fun i => by ring
    simp_rw [hexp]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    dsimp [s, my, mx]; ring
  have hs_zero : ∑ i : Fin n, w i * (y i + x i - s) = 0 := by
    have h1 : ∀ i : Fin n, w i * (y i + x i - s) = w i * y i + w i * x i - s * w i := fun i => by ring
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hw_sum, mul_one]
    dsimp [s, my, mx]; ring
  by_cases hs2 : s ≤ 2
  · -- Case 1: s ≤ 2. Use (y - x)(y + x - s) = (y - x)(y + x - 2) + (2 - s)(y - x).
    have hpt : ∀ i : Fin n, 0 ≤ w i * ((y i - x i) * (y i + x i - 2)) := by
      intro i
      refine mul_nonneg (hw i) ?_
      by_cases hxi : 1 ≤ x i
      · have hyi : x i ≤ y i := by
          simpa [y, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hxi hα.le
        exact mul_nonneg (by linarith) (by linarith)
      · push Not at hxi
        have hyi : y i < x i := by
          simpa [y, Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt (hx i) hxi hα
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hdecomp : ∑ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) =
        (∑ i : Fin n, w i * ((y i - x i) * (y i + x i - 2))) + (2 - s) * (my - mx) := by
      have h1 : ∀ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) =
          w i * ((y i - x i) * (y i + x i - 2)) + (2 - s) * (w i * y i - w i * x i) := fun i => by ring
      simp_rw [h1]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    have hge : 0 ≤ ∑ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) := by
      rw [hdecomp]
      exact add_nonneg (Finset.sum_nonneg fun i _ => hpt i)
        (mul_nonneg (by linarith) (by dsimp [my, mx, y]; linarith))
    refine ⟨by linarith, fun heq i j hwi hwj => ?_⟩
    have hsum0 : ∑ k : Fin n, w k * ((y k - x k) * (y k + x k - 2)) = 0 := by
      have h0 : ∑ k : Fin n, w k * ((y k - x k) * (y k + x k - s)) = 0 := by linarith
      rw [hdecomp] at h0
      have h2 : 0 ≤ (2 - s) * (my - mx) := mul_nonneg (by linarith) (by dsimp [my, mx, y]; linarith)
      have h1 : 0 ≤ ∑ k : Fin n, w k * ((y k - x k) * (y k + x k - 2)) :=
        Finset.sum_nonneg fun k _ => hpt k
      linarith
    have hEq1 : ∀ k : Fin n, 0 < w k → x k = 1 := by
      intro k hwk
      have hterm0 : w k * ((y k - x k) * (y k + x k - 2)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hpt r).mp hsum0 k (Finset.mem_univ k)
      have hprod0 : (y k - x k) * (y k + x k - 2) = 0 := (mul_eq_zero.mp hterm0).resolve_left hwk.ne'
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hyk : y k < x k := by
          simpa [y, Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt (hx k) hlt hα
        have : 0 < (y k - x k) * (y k + x k - 2) :=
          mul_pos_of_neg_of_neg (by linarith) (by linarith)
        linarith
      · have hyk : x k < y k := by
          simpa [y, Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hgt hα
        have : 0 < (y k - x k) * (y k + x k - 2) := mul_pos (by linarith) (by linarith)
        linarith
    rw [hEq1 i hwi, hEq1 j hwj]
  · -- Case 2: s > 2. Pick x0 > 1 with x0^α + x0 = s via IVT and set c0 = x0^α - x0 > 0.
    push Not at hs2
    let f : ℝ → ℝ := fun t => t ^ α + t
    have hf_cont : ContinuousOn f (Set.Icc 1 (max s 2)) :=
      ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ α)).add continuous_id).continuousOn
    have hf1 : f 1 = 2 := by dsimp [f]; norm_num
    have hfM : s ≤ f (max s 2) := by
      dsimp [f]
      have h1 : 0 ≤ (max s 2) ^ α := Real.rpow_nonneg (by linarith [le_max_right s 2]) α
      linarith [le_max_left s 2]
    have hmem : s ∈ Set.Icc (f 1) (f (max s 2)) := ⟨by linarith, hfM⟩
    obtain ⟨x0, hx0_mem, hx0_eq⟩ :=
      intermediate_value_Icc (by linarith [le_max_right s 2] : (1 : ℝ) ≤ max s 2) hf_cont hmem
    have hx0_gt1 : 1 < x0 := by
      rcases eq_or_lt_of_le hx0_mem.1 with h1 | hgt
      · exfalso; rw [← h1, hf1] at hx0_eq; linarith
      · exact hgt
    let c0 : ℝ := x0 ^ α - x0
    have hc0_pos : 0 < c0 := by
      have : x0 < x0 ^ α := by
        simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hx0_gt1 hα
      dsimp [c0]; linarith
    have hpt_pos : ∀ t : ℝ, 0 < t → t ≠ x0 → 0 < (t ^ α - t - c0) * (t ^ α + t - s) := by
      intro t ht hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs_lt : t ^ α + t < s := by
          rw [← hx0_eq]; dsimp [f]
          have : t ^ α < x0 ^ α := Real.rpow_lt_rpow ht.le hlt (by linarith)
          linarith
        have hc_lt : t ^ α - t < c0 := by
          by_cases ht1 : 1 ≤ t
          · exact rpow_sub_id_strictMono_Ici hα ht1 hlt
          · push Not at ht1
            have : t ^ α < t := by
              simpa [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt ht ht1 hα
            linarith
        exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
      · have hs_gt : s < t ^ α + t := by
          rw [← hx0_eq]; dsimp [f]
          have : x0 ^ α < t ^ α := Real.rpow_lt_rpow (by linarith) hgt (by linarith)
          linarith
        have hc_gt : c0 < t ^ α - t := rpow_sub_id_strictMono_Ici hα hx0_gt1.le hgt
        exact mul_pos (by linarith) (by linarith)
    have hpt : ∀ i : Fin n, 0 ≤ w i * ((y i - x i - c0) * (y i + x i - s)) := by
      intro i
      refine mul_nonneg (hw i) ?_
      by_cases hxi : x i = x0
      · rw [show y i = x0 ^ α by dsimp [y]; rw [hxi], hxi]; dsimp [c0]; ring_nf; exact le_rfl
      · exact (hpt_pos (x i) (hx i) hxi).le
    have hshift : ∑ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) =
        ∑ i : Fin n, w i * ((y i - x i - c0) * (y i + x i - s)) := by
      have h1 : ∀ i : Fin n, w i * ((y i - x i - c0) * (y i + x i - s)) =
          w i * ((y i - x i) * (y i + x i - s)) - c0 * (w i * (y i + x i - s)) := fun i => by ring
      simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, hs_zero, mul_zero, sub_zero]
    have hge : 0 ≤ ∑ i : Fin n, w i * ((y i - x i) * (y i + x i - s)) := by
      rw [hshift]; exact Finset.sum_nonneg fun i _ => hpt i
    refine ⟨by linarith, fun heq i j hwi hwj => ?_⟩
    have hsum0 : ∑ k : Fin n, w k * ((y k - x k - c0) * (y k + x k - s)) = 0 := by linarith
    have hEqx0 : ∀ k : Fin n, 0 < w k → x k = x0 := by
      intro k hwk
      have hterm0 : w k * ((y k - x k - c0) * (y k + x k - s)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun r _ => hpt r).mp hsum0 k (Finset.mem_univ k)
      have hprod0 : (y k - x k - c0) * (y k + x k - s) = 0 :=
        (mul_eq_zero.mp hterm0).resolve_left hwk.ne'
      by_contra hne
      have := hpt_pos (x k) (hx k) hne
      dsimp [y] at hprod0
      linarith
    rw [hEqx0 i hwi, hEqx0 j hwj]

/-! ==========================================================================
    PART 4: Theorem 9(c) — Top-Eigenspace Spectral Dichotomy
    ========================================================================== -/

private lemma norm_sq_mulVec_le_of_le_one {n : ℕ} {D : Mat n} (hD : D.PosDef)
    (hD_le : (1 - D).PosSemidef) (u : Fin n → ℂ) :
    (star (D.mulVec u) ⬝ᵥ D.mulVec u).re ≤ (star u ⬝ᵥ u).re := by
  let U := hD.isHermitian.eigenvectorUnitary
  let lam := hD.isHermitian.eigenvalues
  have hlam_le : ∀ i : Fin n, lam i ≤ 1 := by
    intro i
    let vi : Fin n → ℂ := (hD.isHermitian.eigenvectorBasis i).ofLp
    have hmul : D.mulVec vi = (lam i : ℂ) • vi := hD.isHermitian.mulVec_eigenvectorBasis i
    have hnn := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hD_le).2 vi
    have hnorm : star vi ⬝ᵥ vi = 1 := by
      have hin := orthonormal_iff_ite.mp hD.isHermitian.eigenvectorBasis.orthonormal i i
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hin
      simpa [vi] using hin
    have hq : star vi ⬝ᵥ (1 - D).mulVec vi = ((1 - lam i : ℝ) : ℂ) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hmul, dotProduct_sub,
        dotProduct_smul, smul_eq_mul, hnorm, mul_one]
      push_cast; ring
    rw [hq] at hnn
    have hre : 0 ≤ (1 - lam i : ℝ) := by simpa using (Complex.le_def.mp hnn).1
    linarith
  have hD_eq : D = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
    simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hD.isHermitian.spectral_theorem
  let y : Fin n → ℂ := (U : Mat n)ᴴ.mulVec u
  have hLHS : (star (D.mulVec u) ⬝ᵥ D.mulVec u).re = ∑ i : Fin n, (lam i) ^ 2 * ‖y i‖ ^ 2 := by
    have hDu : D.mulVec u = (U : Mat n).mulVec ((Matrix.diagonal (fun i => (lam i : ℂ))).mulVec y) := by
      rw [hD_eq]; simp only [y, ← Matrix.mulVec_mulVec]
    rw [hDu, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    have hUstar : (star ((Matrix.diagonal (fun i => (lam i : ℂ))).mulVec y) ᵥ* (U : Mat n)ᴴ) ᵥ* (U : Mat n) =
        star ((Matrix.diagonal (fun i => (lam i : ℂ))).mulVec y) := by
      rw [Matrix.vecMul_vecMul, unitary_conjTranspose_mul_self U, Matrix.vecMul_one]
    rw [hUstar, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, star_mul', Complex.star_def, Complex.conj_ofReal]
    have h1 : (lam i : ℂ) * starRingEnd ℂ (y i) * ((lam i : ℂ) * y i) =
        ((lam i) ^ 2 : ℝ) * (starRingEnd ℂ (y i) * y i) := by push_cast; ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hRHS : (star u ⬝ᵥ u).re = ∑ i : Fin n, ‖y i‖ ^ 2 := by
    have hu : u = (U : Mat n).mulVec y := by
      simp only [y, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec]
    conv_lhs => rw [hu]
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self U, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hLHS, hRHS]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 : 0 < lam i := hD.eigenvalues_pos i
  have h1 : lam i ≤ 1 := hlam_le i
  have hsq : (lam i) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg ‖y i‖]

/-- Universal Top-Eigenspace Spectral Dichotomy (Theorem 9c):
    Assume 0 ≺ D ⪯ I, H ≻ 0, κ > 1, Λ > 0 satisfy Holden's power equation
      (D + H)^(2κ - 1) = Λ D^(1/2) G^(κ - 1) D^(1/2).
    If a nonzero vector v ∈ E_max (D v = v) is an eigenvector of Φ = G^κ - D G^(κ-1) D
    with NONNEGATIVE eigenvalue μ ≥ 0, then v is a completely decoupled common eigenvector
    of D, G, and H with H v = h v, h ≥ 1, (1 + h)^(2κ - 1) = Λ h^(κ - 1), and μ = h^(κ - 1)(h - 1). -/
theorem top_eigenspace_spectral_dichotomy {n : ℕ} {κ Λ μ : ℝ}
    (hκ : 1 < κ) (_hΛ : 0 < Λ) (hμ : 0 ≤ μ)
    {D H : Mat n} (hD : D.PosDef) (hD_le : (1 - D).PosSemidef) (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = v)
    (hPhiv : (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) -
      D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) * D).mulVec v =
      (μ : ℂ) • v) :
    ∃ h : ℝ, 1 ≤ h ∧ H.mulVec v = (h : ℂ) • v ∧
      (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧ μ = h ^ (κ - 1) * (h - 1) := by
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
  let G := Dhalf * H * Dhalf
  let Gkm1 := posDefPow (κ - 1) hG
  let Gk := posDefPow κ hG
  -- Normalize v to unit norm
  have hv_norm_pos : 0 < (star v ⬝ᵥ v).re := by
    rw [dotProduct, Complex.re_sum]
    have hnn : ∀ i, 0 ≤ (star (v i) * v i).re := fun i => by
      rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg _
    obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by by_contra hall; push Not at hall; exact hv (funext hall)
    refine Finset.sum_pos' (fun i _ => hnn i) ⟨i0, Finset.mem_univ _, ?_⟩
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hi0)
  let nv : ℝ := Real.sqrt (star v ⬝ᵥ v).re
  have hnv : 0 < nv := Real.sqrt_pos.mpr hv_norm_pos
  let u : Fin n → ℂ := ((nv⁻¹ : ℝ) : ℂ) • v
  have hDu : D.mulVec u = u := by dsimp [u]; rw [Matrix.mulVec_smul, hDv]
  have hPhiu : (Gk - D * Gkm1 * D).mulVec u = (μ : ℂ) • u := by
    change (Gk - D * Gkm1 * D).mulVec (((nv⁻¹ : ℝ) : ℂ) • v) = (μ : ℂ) • (((nv⁻¹ : ℝ) : ℂ) • v)
    rw [Matrix.mulVec_smul, hPhiv, smul_comm]
  have hu_norm : (star u ⬝ᵥ u).re = 1 := by
    have hst : star u = ((nv⁻¹ : ℝ) : ℂ) • star v := by
      ext i; simp [u]
    rw [hst]
    change (((nv⁻¹ : ℝ) : ℂ) • star v ⬝ᵥ ((nv⁻¹ : ℝ) : ℂ) • v).re = 1
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hmul : ((nv⁻¹ : ℝ) : ℂ) * (((nv⁻¹ : ℝ) : ℂ) * (star v ⬝ᵥ v)) =
        (((nv⁻¹ * nv⁻¹ : ℝ) : ℂ)) * (star v ⬝ᵥ v) := by push_cast; ring
    rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hsq : nv * nv = (star v ⬝ᵥ v).re := Real.mul_self_sqrt hv_norm_pos.le
    field_simp [hnv.ne']
    linarith
  -- Expand u in the eigenbasis of G
  let UG := hG.isHermitian.eigenvectorUnitary
  let lam := hG.isHermitian.eigenvalues
  let z : Fin n → ℂ := (UG : Mat n)ᴴ.mulVec u
  let w : Fin n → ℝ := fun i => ‖z i‖ ^ 2
  let x : Fin n → ℝ := fun i => (lam i) ^ (κ - 1)
  let α : ℝ := κ / (κ - 1)
  have hkm1 : 0 < κ - 1 := by linarith
  have hα : 1 < α := by dsimp [α]; rw [one_lt_div hkm1]; linarith
  have hw_nn : ∀ i, 0 ≤ w i := fun i => sq_nonneg _
  have hx_pos : ∀ i, 0 < x i := fun i => Real.rpow_pos_of_pos (hG.eigenvalues_pos i) _
  have hxa : ∀ i, (x i) ^ α = (lam i) ^ κ := fun i => by
    dsimp [x, α]
    rw [← Real.rpow_mul (hG.eigenvalues_pos i).le]
    congr 1; field_simp [hkm1.ne']
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
  -- Key relation from Φ u = μ u and D u = u:
  --   D (Gkm1 u) = (Gk - μ I) u!
  have hDGkm1 : D.mulVec (Gkm1.mulVec u) = Gk.mulVec u - (μ : ℂ) • u := by
    have hmul3 : (D * Gkm1 * D).mulVec u = D.mulVec (Gkm1.mulVec u) := by
      calc (D * Gkm1 * D).mulVec u
          = (D * Gkm1).mulVec (D.mulVec u) := (Matrix.mulVec_mulVec u (D * Gkm1) D).symm
        _ = (D * Gkm1).mulVec u := by rw [hDu]
        _ = D.mulVec (Gkm1.mulVec u) := (Matrix.mulVec_mulVec u D Gkm1).symm
    have h1 := hPhiu
    rw [Matrix.sub_mulVec, hmul3] at h1
    ext i; have hi := congr_fun h1 i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    linear_combination -hi
  -- Helper: quadratic form of posDefPow r hG at u is ∑ w_i (lam i)^r
  have hquad_G : ∀ r : ℝ, (star u ⬝ᵥ (posDefPow r hG).mulVec u).re = ∑ i : Fin n, w i * (lam i) ^ r := by
    intro r
    unfold posDefPow
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (star u ⬝ᵥ (UG : Mat n).mulVec ((Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ))).mulVec z)).re = _
    rw [Matrix.dotProduct_mulVec]
    have hst : star u ᵥ* (UG : Mat n) = star z := by
      simp only [z, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [hst, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have h1 : starRingEnd ℂ (z i) * ((((lam i) ^ r : ℝ) : ℂ) * z i) =
        (((lam i) ^ r : ℝ) : ℂ) * (starRingEnd ℂ (z i) * z i) := by ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  -- Compute μ = E[X^α] - E[X] ≥ 0
  have hμ_eq : μ = (∑ i : Fin n, w i * (x i) ^ α) - (∑ i : Fin n, w i * x i) := by
    have h1 : (star u ⬝ᵥ (Gk - D * Gkm1 * D).mulVec u).re = μ := by
      rw [hPhiu, dotProduct_smul, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hu_norm, mul_one]
    have h2 : (star u ⬝ᵥ (Gk - D * Gkm1 * D).mulVec u).re =
        (star u ⬝ᵥ Gk.mulVec u).re - (star u ⬝ᵥ Gkm1.mulVec u).re := by
      have hmul3 : (D * Gkm1 * D).mulVec u = D.mulVec (Gkm1.mulVec u) := by
        calc (D * Gkm1 * D).mulVec u
            = (D * Gkm1).mulVec (D.mulVec u) := (Matrix.mulVec_mulVec u (D * Gkm1) D).symm
          _ = (D * Gkm1).mulVec u := by rw [hDu]
          _ = D.mulVec (Gkm1.mulVec u) := (Matrix.mulVec_mulVec u D Gkm1).symm
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hmul3]
      congr 2
      rw [Matrix.dotProduct_mulVec]
      have hst : star u ᵥ* D = star u := by
        calc star u ᵥ* D = star (D.mulVec u) := by rw [Matrix.star_mulVec, hD.isHermitian.eq]
          _ = star u := by rw [hDu]
      rw [hst]
    rw [← h1, h2, hquad_G κ, hquad_G (κ - 1)]
    simp_rw [hxa]; rfl
  have hmean : ∑ i : Fin n, w i * x i ≤ ∑ i : Fin n, w i * (x i) ^ α := by linarith
  -- Compute ‖(Gk - μ I) u‖^2 = ‖D Gkm1 u‖^2 ≤ ‖Gkm1 u‖^2
  have hnorm_ineq : (star (Gk.mulVec u - (μ : ℂ) • u) ⬝ᵥ (Gk.mulVec u - (μ : ℂ) • u)).re ≤
      (star (Gkm1.mulVec u) ⬝ᵥ Gkm1.mulVec u).re := by
    rw [← hDGkm1]
    exact norm_sq_mulVec_le_of_le_one hD hD_le (Gkm1.mulVec u)
  -- Express both norms in the eigenbasis of G
  have hLHS_norm : (star (Gk.mulVec u - (μ : ℂ) • u) ⬝ᵥ (Gk.mulVec u - (μ : ℂ) • u)).re =
      ∑ i : Fin n, w i * ((x i) ^ α - μ) ^ 2 := by
    have hvec : Gk.mulVec u - (μ : ℂ) • u =
        (UG : Mat n).mulVec (fun i => ((((x i) ^ α - μ : ℝ) : ℂ)) * z i) := by
      have hu : u = (UG : Mat n).mulVec z := by
        simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UG, Matrix.one_mulVec]
      have hGku : Gk.mulVec u = (UG : Mat n).mulVec (fun i => (((lam i) ^ κ : ℝ) : ℂ) * z i) := by
        change ((UG : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ κ : ℝ) : ℂ)) * (UG : Mat n)ᴴ).mulVec u = _
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        congr 1; ext i; simp [z, Matrix.mulVec_diagonal]
      rw [hGku]; conv_lhs => rw [hu]
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
      congr 1; ext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hxa i]; push_cast; ring
    rw [hvec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UG, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    have h1 : ((((x i) ^ α - μ : ℝ) : ℂ) * starRingEnd ℂ (z i)) *
        ((((x i) ^ α - μ : ℝ) : ℂ) * z i) =
        ((((x i) ^ α - μ) ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (z i) * z i) := by push_cast; ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  have hRHS_norm : (star (Gkm1.mulVec u) ⬝ᵥ Gkm1.mulVec u).re = ∑ i : Fin n, w i * (x i) ^ 2 := by
    have hGkm1u : Gkm1.mulVec u = (UG : Mat n).mulVec (fun i => ((x i : ℝ) : ℂ) * z i) := by
      change ((UG : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ (κ - 1) : ℝ) : ℂ)) * (UG : Mat n)ᴴ).mulVec u = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1; ext i; simp [z, x, Matrix.mulVec_diagonal]
    rw [hGkm1u, Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UG, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [w, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal]
    have h1 : (((x i : ℝ) : ℂ) * starRingEnd ℂ (z i)) * (((x i : ℝ) : ℂ) * z i) =
        (((x i) ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ (z i) * z i) := by push_cast; ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  -- Expand LHS = Var(X^α) + (E[X])^2 and RHS = Var(X) + (E[X])^2
  have hLHS_var : ∑ i : Fin n, w i * ((x i) ^ α - μ) ^ 2 =
      (∑ i : Fin n, w i * ((x i) ^ α) ^ 2 - (∑ i : Fin n, w i * (x i) ^ α) ^ 2) +
      (∑ i : Fin n, w i * x i) ^ 2 := by
    have hexp : ∀ i : Fin n, w i * ((x i) ^ α - μ) ^ 2 =
        w i * ((x i) ^ α) ^ 2 - 2 * μ * (w i * (x i) ^ α) + μ ^ 2 * w i := fun i => by ring
    simp_rw [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw_sum, mul_one]
    rw [hμ_eq]; ring
  have hvar_le : ∑ i : Fin n, w i * ((x i) ^ α) ^ 2 - (∑ i : Fin n, w i * (x i) ^ α) ^ 2 ≤
      ∑ i : Fin n, w i * (x i) ^ 2 - (∑ i : Fin n, w i * x i) ^ 2 := by
    linarith [hnorm_ineq, hLHS_norm, hRHS_norm, hLHS_var]
  -- Apply Power-Variance Lemma!
  obtain ⟨hvar_ge, hvar_eq⟩ := power_variance_lemma hα hw_nn hw_sum hx_pos hmean
  have hconst := hvar_eq (le_antisymm hvar_ge hvar_le)
  -- Pick any index i0 with w i0 > 0; then every active i has lam i = lam i0 =: h!
  obtain ⟨i0, hi0_pos⟩ : ∃ i0 : Fin n, 0 < w i0 := by
    by_contra hall; push Not at hall
    have : ∑ i : Fin n, w i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hall i) (hw_nn i)
    linarith
  let h : ℝ := lam i0
  have hh_pos : 0 < h := hG.eigenvalues_pos i0
  have hlam_eq : ∀ i : Fin n, z i ≠ 0 → lam i = h := by
    intro i hzi
    have hwi : 0 < w i := sq_pos_of_pos (norm_pos_iff.mpr hzi)
    have hxi : x i = x i0 := hconst i i0 hwi hi0_pos
    have h1 : ((lam i) ^ (κ - 1)) ^ (κ - 1)⁻¹ = ((lam i0) ^ (κ - 1)) ^ (κ - 1)⁻¹ :=
      congrArg (fun t => t ^ (κ - 1)⁻¹) hxi
    rw [← Real.rpow_mul (hG.eigenvalues_pos i).le, ← Real.rpow_mul (hG.eigenvalues_pos i0).le,
      mul_inv_cancel₀ hkm1.ne', Real.rpow_one, Real.rpow_one] at h1
    exact h1
  -- Therefore G u = h u, hence G v = h v!
  have hGu : G.mulVec u = (h : ℂ) • u := by
    have hG_eq : G = (UG : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (UG : Mat n)ᴴ := by
      simpa [UG, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hG.isHermitian.spectral_theorem
    have hdiag_z : (Matrix.diagonal (fun i => (lam i : ℂ))).mulVec z = (h : ℂ) • z := by
      ext i; simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hzi : z i = 0
      · simp [hzi]
      · rw [hlam_eq i hzi]
    rw [hG_eq, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    change (UG : Mat n).mulVec ((Matrix.diagonal (fun i => (lam i : ℂ))).mulVec z) = _
    rw [hdiag_z, Matrix.mulVec_smul]
    simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UG, Matrix.one_mulVec]
  have hGv : G.mulVec v = (h : ℂ) • v := by
    have h1 := congrArg (fun a => ((nv : ℝ) : ℂ) • a) hGu
    have hnv_u : ((nv : ℝ) : ℂ) • u = v := by
      dsimp [u]; rw [smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
    rw [← Matrix.mulVec_smul, hnv_u, smul_comm, hnv_u] at h1
    exact h1
  -- Since D v = v, Dhalf v = v, so H v = Dhalf^{-1} G Dhalf^{-1} v = h v!
  have hDhalf_v : Dhalf.mulVec v = v := by
    have := (posDefPow_mulVec_of_eig (1 / 2) hD hv (μ := 1) (by simpa using hDv)).2
    simpa [Dhalf] using this
  have hHv : H.mulVec v = (h : ℂ) • v := by
    have h1 : Dhalf.mulVec (H.mulVec v) = Dhalf.mulVec ((h : ℂ) • v) := by
      rw [Matrix.mulVec_smul, hDhalf_v, ← hGv]
      dsimp [G]; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDhalf_v]
    have h0 : Dhalf.mulVec (H.mulVec v - (h : ℂ) • v) = 0 := by rw [Matrix.mulVec_sub, h1, sub_self]
    by_contra hne
    exact posDef_mulVec_ne_zero (posDefPow_posDef (1 / 2) hD) (sub_ne_zero.mpr hne) h0
  -- Plug v into (D + H)^(2κ-1) v = Λ Dhalf G^(κ-1) Dhalf v!
  have hDHv : (D + H).mulVec v = ((1 + h : ℝ) : ℂ) • v := by
    rw [Matrix.add_mulVec, hDv, hHv]; ext i; simp; ring
  have hLHS_eig := (posDefPow_mulVec_of_eig (2 * κ - 1) (hD.add hH) hv hDHv).2
  have hGkm1_v := (posDefPow_mulVec_of_eig (κ - 1) hG hv hGv).2
  have hGk_v := (posDefPow_mulVec_of_eig κ hG hv hGv).2
  have hEq_v := congrArg (fun M : Mat n => M.mulVec v) hEq
  rw [hLHS_eig, Matrix.smul_mulVec] at hEq_v
  have hRHS_v : (Dhalf * Gkm1 * Dhalf).mulVec v = ((h ^ (κ - 1) : ℝ) : ℂ) • v := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDhalf_v, hGkm1_v, Matrix.mulVec_smul, hDhalf_v]
  change (((1 + h) ^ (2 * κ - 1) : ℝ) : ℂ) • v = (Λ : ℂ) • (Dhalf * Gkm1 * Dhalf).mulVec v at hEq_v
  rw [hRHS_v, smul_smul] at hEq_v
  have hscalar_eq : (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) := by
    obtain ⟨i1, hi1⟩ : ∃ i, v i ≠ 0 := by by_contra hall; push Not at hall; exact hv (funext hall)
    have hi := congr_fun hEq_v i1
    simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul] at hi
    exact Complex.ofReal_injective (mul_right_cancel₀ hi1 hi)
  -- Compute μ = h^(κ - 1) * (h - 1), and deduce 1 ≤ h since μ ≥ 0!
  have hμ_val : μ = h ^ (κ - 1) * (h - 1) := by
    have hPhiv' : (Gk - D * Gkm1 * D).mulVec v = ((h ^ κ - h ^ (κ - 1) : ℝ) : ℂ) • v := by
      have hmul3 : (D * Gkm1 * D).mulVec v = D.mulVec (Gkm1.mulVec v) := by
        calc (D * Gkm1 * D).mulVec v
            = (D * Gkm1).mulVec (D.mulVec v) := (Matrix.mulVec_mulVec v (D * Gkm1) D).symm
          _ = (D * Gkm1).mulVec v := by rw [hDv]
          _ = D.mulVec (Gkm1.mulVec v) := (Matrix.mulVec_mulVec v D Gkm1).symm
      rw [Matrix.sub_mulVec, hGk_v, hmul3, hGkm1_v, Matrix.mulVec_smul, hDv]
      ext i; simp; ring
    have hcmp : (μ : ℂ) • v = ((h ^ κ - h ^ (κ - 1) : ℝ) : ℂ) • v := by rw [← hPhiv, hPhiv']
    obtain ⟨i1, hi1⟩ : ∃ i, v i ≠ 0 := by by_contra hall; push Not at hall; exact hv (funext hall)
    have h1 : μ = h ^ κ - h ^ (κ - 1) :=
      Complex.ofReal_injective (mul_right_cancel₀ hi1 (congr_fun hcmp i1))
    have h2 : h ^ κ = h ^ (κ - 1) * h := by
      calc h ^ κ = h ^ ((κ - 1) + 1) := by congr 1; ring
        _ = h ^ (κ - 1) * h ^ (1 : ℝ) := Real.rpow_add hh_pos (κ - 1) 1
        _ = h ^ (κ - 1) * h := by rw [Real.rpow_one]
    linarith
  have hh_ge1 : 1 ≤ h := by
    have hpow_pos : 0 < h ^ (κ - 1) := Real.rpow_pos_of_pos hh_pos _
    nlinarith
  exact ⟨h, hh_ge1, hHv, hscalar_eq, hμ_val⟩

/-! ==========================================================================
    PART 5: Theorem 10 — Universal Pure-Algebraic Upper Bound & Corollaries
    ========================================================================== -/

/-- One-line weighted AM–GM / Young lower bound on x^κ - x^(κ-1) for all x > 0 and κ > 1:
      x^κ - x^(κ - 1) ≥ -(κ - 1)^(κ - 1) / κ^κ. -/
theorem rpow_sub_rpow_ge_neg_ck {κ x : ℝ} (hκ : 1 < κ) (hx : 0 < x) :
    -((κ - 1) ^ (κ - 1) / κ ^ κ) ≤ x ^ κ - x ^ (κ - 1) := by
  have hκ0 : 0 < κ := by linarith
  have hkm1 : 0 < κ - 1 := by linarith
  have hw1 : 0 ≤ (κ - 1) / κ := div_nonneg hkm1.le hκ0.le
  have hw2 : 0 ≤ 1 / κ := div_nonneg zero_le_one hκ0.le
  have hwsum : (κ - 1) / κ + 1 / κ = 1 := by field_simp [hκ0.ne']; ring
  let a : ℝ := κ / (κ - 1) * x ^ κ
  let b : ℝ := ((κ - 1) / κ) ^ (κ - 1)
  have ha0 : 0 ≤ a := mul_nonneg (div_nonneg hκ0.le hkm1.le) (Real.rpow_nonneg hx.le κ)
  have hb0 : 0 ≤ b := Real.rpow_nonneg (div_nonneg hkm1.le hκ0.le) _
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ha0 hb0 hwsum
  have hLHS : a ^ ((κ - 1) / κ) * b ^ (1 / κ) = x ^ (κ - 1) := by
    dsimp [a, b]
    rw [Real.mul_rpow (div_nonneg hκ0.le hkm1.le) (Real.rpow_nonneg hx.le κ),
      ← Real.rpow_mul hx.le, ← Real.rpow_mul (div_nonneg hkm1.le hκ0.le)]
    have hexp1 : κ * ((κ - 1) / κ) = κ - 1 := by field_simp [hκ0.ne']
    have hexp2 : (κ - 1) * (1 / κ) = (κ - 1) / κ := by ring
    rw [hexp1, hexp2]
    have hcancel : (κ / (κ - 1)) ^ ((κ - 1) / κ) * ((κ - 1) / κ) ^ ((κ - 1) / κ) = 1 := by
      rw [← Real.mul_rpow (div_nonneg hκ0.le hkm1.le) (div_nonneg hkm1.le hκ0.le)]
      have : κ / (κ - 1) * ((κ - 1) / κ) = 1 := by field_simp [hκ0.ne', hkm1.ne']
      rw [this, Real.one_rpow]
    calc (κ / (κ - 1)) ^ ((κ - 1) / κ) * x ^ (κ - 1) * ((κ - 1) / κ) ^ ((κ - 1) / κ)
        = ((κ / (κ - 1)) ^ ((κ - 1) / κ) * ((κ - 1) / κ) ^ ((κ - 1) / κ)) * x ^ (κ - 1) := by ring
      _ = x ^ (κ - 1) := by rw [hcancel, one_mul]
  have hRHS : (κ - 1) / κ * a + 1 / κ * b = x ^ κ + (κ - 1) ^ (κ - 1) / κ ^ κ := by
    dsimp [a, b]
    have h1 : (κ - 1) / κ * (κ / (κ - 1) * x ^ κ) = x ^ κ := by field_simp [hκ0.ne', hkm1.ne']
    have h2 : 1 / κ * ((κ - 1) / κ) ^ (κ - 1) = (κ - 1) ^ (κ - 1) / κ ^ κ := by
      rw [Real.div_rpow hkm1.le hκ0.le]
      have hkp : κ * κ ^ (κ - 1) = κ ^ κ := by
        calc κ * κ ^ (κ - 1) = κ ^ (1 : ℝ) * κ ^ (κ - 1) := by rw [Real.rpow_one]
          _ = κ ^ (1 + (κ - 1)) := (Real.rpow_add hκ0 1 (κ - 1)).symm
          _ = κ ^ κ := by congr 1; ring
      field_simp [hκ0.ne', (Real.rpow_pos_of_pos hκ0 (κ - 1)).ne']
      exact hkp.symm
    rw [h1, h2]
  linarith

/-- Universal Pure-Algebraic Upper Bound (Theorem 10):
    For EVERY finite-dimensional positive-definite solution (D, H_1, ..., H_m) of Holden's
    power system with m ≥ 2, κ > 1, and Λ > 2^(2κ - 1), there exists h > 1 solving
    (1 + h)^(2κ - 1) = Λ h^(κ - 1) and satisfying:
      h^(κ - 1) * (h - 1) ≤ (m - 1) * (κ - 1)^(κ - 1) / κ^κ. -/
theorem universal_algebraic_upper_bound {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n)
    {κ Λ : ℝ} (hκ : 1 < κ) (hΛ : 2 ^ (2 * κ - 1) < Λ)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j : Fin m,
      posDefPow (2 * κ - 1) (hD.add (hH j)) =
        (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
          posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
          posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
        D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0) :
    ∃ h : ℝ, 1 < h ∧ (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      h ^ (κ - 1) * (h - 1) ≤ ((m : ℝ) - 1) * ((κ - 1) ^ (κ - 1) / κ ^ κ) := by
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos zero_lt_two _) hΛ
  -- Step 1: Rescale (D, H_j) by d_max^{-1} so 0 ≺ D' ⪯ I and ker(D' - I) ≠ {0}.
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ hD.isHermitian.eigenvalues Finset.univ_nonempty
  let dmax : ℝ := hD.isHermitian.eigenvalues i_max
  have hdmax : 0 < dmax := hD.eigenvalues_pos i_max
  have hc_pos : 0 < dmax⁻¹ := inv_pos.mpr hdmax
  let D' : Mat n := dmax⁻¹ • D
  let H' : Fin m → Mat n := fun j => dmax⁻¹ • H j
  have hD' : D'.PosDef := hD.smul hc_pos
  have hH' : ∀ j, (H' j).PosDef := fun j => (hH j).smul hc_pos
  -- Verify 1 - D' is PSD
  have hD'_le : (1 - D').PosSemidef := by
    let U := hD.isHermitian.eigenvectorUnitary
    let lam := hD.isHermitian.eigenvalues
    have hD_eq : D = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
      simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hD.isHermitian.spectral_theorem
    have h1D' : 1 - D' = (U : Mat n) * Matrix.diagonal (fun i => ((1 - dmax⁻¹ * lam i : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
      have h1 : (1 : Mat n) = (U : Mat n) * Matrix.diagonal (fun _ => (1 : ℂ)) * (U : Mat n)ᴴ := by
        simp [Matrix.diagonal_one, unitary_mul_conjTranspose_self]
      have hD'_eq : D' = (U : Mat n) * Matrix.diagonal (fun i => ((dmax⁻¹ * lam i : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
        have hsm : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
        rw [hsm, hD_eq, ← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 1; congr 1; ext a b; by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
      rw [h1, hD'_eq, ← Matrix.sub_mul, ← Matrix.mul_sub]
      congr 1; congr 1; ext a b; by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
    rw [h1D']
    have hdiag_psd : (Matrix.diagonal (fun i => ((1 - dmax⁻¹ * lam i : ℝ) : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i
      have hle : lam i ≤ dmax := hi_max i (Finset.mem_univ i)
      have hnn : 0 ≤ 1 - dmax⁻¹ * lam i := by
        have : dmax⁻¹ * lam i ≤ 1 := by rw [inv_mul_le_iff₀ hdmax]; linarith
        linarith
      exact_mod_cast hnn
    simpa using hdiag_psd.mul_mul_conjTranspose_same (U : Mat n)
  -- Verify rescaled equations hold for (D', H')!
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let D'half := posDefPow (1 / 2 : ℝ) hD'
  have hD'half_eq : D'half = ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) • Dhalf := posDefPow_smul (1 / 2) hc_pos hD
  let hG : ∀ j, (Dhalf * H j * Dhalf).PosDef := fun j =>
    posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)
  let hG' : ∀ j, (D'half * H' j * D'half).PosDef := fun j =>
    posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') (hH' j)
  have hG'_eq : ∀ j, D'half * H' j * D'half = (dmax⁻¹ ^ (2 : ℕ)) • (Dhalf * H j * Dhalf) := by
    intro j
    have hHj : H' j = ((dmax⁻¹ : ℝ) : ℂ) • H j := by
      ext a b; simp only [H', Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    rw [hD'half_eq, hHj]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hsq : dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (1 / 2 : ℝ) = dmax⁻¹ := by
      rw [← Real.rpow_add hc_pos]; norm_num
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    have hsc : ((dmax⁻¹ : ℝ) : ℂ) * (((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
        (((dmax⁻¹ ^ (2 : ℕ) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsq, sq]
    linear_combination (Dhalf * H j * Dhalf) a b * hsc
  have hG'pow_eq : ∀ j (r : ℝ),
      posDefPow r (hG' j) = (((dmax⁻¹ ^ (2 * r) : ℝ) : ℂ)) • posDefPow r (hG j) := by
    intro j r
    have hc2 : 0 < dmax⁻¹ ^ (2 : ℕ) := pow_pos hc_pos 2
    have hsame : posDefPow r (hG' j) = posDefPow r ((hG j).smul hc2) := by
      let U0 := (hG j).isHermitian.eigenvectorUnitary
      let lam0 := (hG j).isHermitian.eigenvalues
      have h0 : Dhalf * H j * Dhalf =
          (U0 : Mat n) * Matrix.diagonal (fun i => (lam0 i : ℂ)) * (U0 : Mat n)ᴴ := by
        simpa [U0, lam0, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using (hG j).isHermitian.spectral_theorem
      have h1 : D'half * H' j * D'half =
          (U0 : Mat n) * Matrix.diagonal (fun i => ((dmax⁻¹ ^ (2 : ℕ) * lam0 i : ℝ) : ℂ)) * (U0 : Mat n)ᴴ := by
        rw [hG'_eq j]
        have hsm : (dmax⁻¹ ^ (2 : ℕ)) • (Dhalf * H j * Dhalf) =
            ((dmax⁻¹ ^ (2 : ℕ) : ℝ) : ℂ) • (Dhalf * H j * Dhalf) := by ext a b; simp [Complex.real_smul]
        rw [hsm, h0, ← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 1; congr 1; ext a b; by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
      rw [posDefPow_eq_of_diag r (hG' j) U0 (fun i => dmax⁻¹ ^ (2 : ℕ) * lam0 i)
        (fun i => mul_pos hc2 ((hG j).eigenvalues_pos i)) h1,
        posDefPow_eq_of_diag r ((hG j).smul hc2) U0 (fun i => dmax⁻¹ ^ (2 : ℕ) * lam0 i)
        (fun i => mul_pos hc2 ((hG j).eigenvalues_pos i)) (by rw [← hG'_eq j]; exact h1)]
    rw [hsame, posDefPow_smul r hc2 (hG j)]
    congr 1; congr 1
    rw [← Real.rpow_natCast dmax⁻¹ 2, ← Real.rpow_mul hc_pos.le]; norm_num
  have hEq1' : ∀ j : Fin m,
      posDefPow (2 * κ - 1) (hD'.add (hH' j)) =
        (Λ : ℂ) • (D'half * posDefPow (κ - 1) (hG' j) * D'half) := by
    intro j
    have hadd_eq : D' + H' j = dmax⁻¹ • (D + H j) := by ext a b; simp [D', H', smul_add]
    have hLHS : posDefPow (2 * κ - 1) (hD'.add (hH' j)) =
        ((dmax⁻¹ ^ (2 * κ - 1) : ℝ) : ℂ) • posDefPow (2 * κ - 1) (hD.add (hH j)) := by
      let U0 := (hD.add (hH j)).isHermitian.eigenvectorUnitary
      let lam0 := (hD.add (hH j)).isHermitian.eigenvalues
      have h0 : D + H j = (U0 : Mat n) * Matrix.diagonal (fun i => (lam0 i : ℂ)) * (U0 : Mat n)ᴴ := by
        simpa [U0, lam0, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using (hD.add (hH j)).isHermitian.spectral_theorem
      have h1 : D' + H' j =
          (U0 : Mat n) * Matrix.diagonal (fun i => ((dmax⁻¹ * lam0 i : ℝ) : ℂ)) * (U0 : Mat n)ᴴ := by
        rw [hadd_eq]
        have hsm : dmax⁻¹ • (D + H j) = ((dmax⁻¹ : ℝ) : ℂ) • (D + H j) := by
          ext a b; simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
        rw [hsm, h0, ← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 1; congr 1; ext a b; by_cases hab : a = b <;> simp [Matrix.diagonal, hab]
      rw [posDefPow_eq_of_diag (2 * κ - 1) (hD'.add (hH' j)) U0 (fun i => dmax⁻¹ * lam0 i)
        (fun i => mul_pos hc_pos ((hD.add (hH j)).eigenvalues_pos i)) h1,
        ← posDefPow_smul (2 * κ - 1) hc_pos (hD.add (hH j)),
        posDefPow_eq_of_diag (2 * κ - 1) ((hD.add (hH j)).smul hc_pos) U0 (fun i => dmax⁻¹ * lam0 i)
        (fun i => mul_pos hc_pos ((hD.add (hH j)).eigenvalues_pos i)) (by rw [← hadd_eq]; exact h1)]
    rw [hLHS, hEq1 j, hG'pow_eq j (κ - 1), hD'half_eq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hexp : dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ)) =
        dmax⁻¹ ^ (2 * κ - 1) := by
      calc dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ))
          = (dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (1 / 2 : ℝ)) * dmax⁻¹ ^ (2 * (κ - 1)) := by ring
        _ = dmax⁻¹ ^ ((1 / 2 : ℝ) + (1 / 2 : ℝ)) * dmax⁻¹ ^ (2 * (κ - 1)) := by rw [Real.rpow_add hc_pos]
        _ = dmax⁻¹ ^ (((1 / 2 : ℝ) + (1 / 2 : ℝ)) + 2 * (κ - 1)) := (Real.rpow_add hc_pos _ _).symm
        _ = dmax⁻¹ ^ (2 * κ - 1) := by congr 1; ring
    rw [← hexp]; ring
  let Phi' : Fin m → Mat n := fun j => posDefPow κ (hG' j) - D' * posDefPow (κ - 1) (hG' j) * D'
  have hPhi'_eq : ∀ j, Phi' j = ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) •
      (posDefPow κ (hG j) - D * posDefPow (κ - 1) (hG j) * D) := by
    intro j
    dsimp [Phi']
    have hD'c : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by
      ext a b; simp only [D', Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    have hterm2 : D' * posDefPow (κ - 1) (hG' j) * D' =
        ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) • (D * posDefPow (κ - 1) (hG j) * D) := by
      rw [hD'c, hG'pow_eq j (κ - 1)]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hsc_r : dmax⁻¹ * (dmax⁻¹ * dmax⁻¹ ^ (2 * (κ - 1))) = dmax⁻¹ ^ (2 * κ) := by
        calc dmax⁻¹ * (dmax⁻¹ * dmax⁻¹ ^ (2 * (κ - 1)))
            = (dmax⁻¹ ^ (1 : ℝ) * dmax⁻¹ ^ (1 : ℝ)) * dmax⁻¹ ^ (2 * (κ - 1)) := by rw [Real.rpow_one]; ring
          _ = dmax⁻¹ ^ ((1 : ℝ) + 1) * dmax⁻¹ ^ (2 * (κ - 1)) := by rw [Real.rpow_add hc_pos]
          _ = dmax⁻¹ ^ (((1 : ℝ) + 1) + 2 * (κ - 1)) := (Real.rpow_add hc_pos _ _).symm
          _ = dmax⁻¹ ^ (2 * κ) := by congr 1; ring
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul]
      have hsc_c : ((dmax⁻¹ : ℝ) : ℂ) * (((dmax⁻¹ : ℝ) : ℂ) * ((dmax⁻¹ ^ (2 * (κ - 1)) : ℝ) : ℂ)) =
          ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsc_r]
      linear_combination (D * posDefPow (κ - 1) (hG j) * D) a b * hsc_c
    rw [hG'pow_eq j κ, hterm2, ← smul_sub]
    ext a b; simp [Complex.real_smul]
  have hEq2' : ∑ j : Fin m, Phi' j = 0 := by
    simp_rw [hPhi'_eq, ← Finset.smul_sum, hEq2, smul_zero]
  -- Step 2: By Theorem 9(a), each Phi' j commutes with D', hence preserves E_max = ker(D' - I).
  have hPhi'_herm : ∀ j, (Phi' j).IsHermitian := by
    intro j
    dsimp [Phi']
    have h1 := (posDefPow_posDef κ (hG' j)).isHermitian
    have h2 := (posDef_conj_of_posDef hD' (posDefPow_posDef (κ - 1) (hG' j))).isHermitian
    exact h1.sub h2
  have hPhi'_comm : ∀ j, D' * Phi' j = Phi' j * D' := fun j =>
    universal_commutator_theorem hΛ_pos hD' (hH' j) (hEq1' j)
  -- Pick any nonzero vector u0 in E_max = ker(D' - I) (the i_max eigenvector of D!)
  let u0 : Fin n → ℂ := (hD.isHermitian.eigenvectorBasis i_max).ofLp
  have hu0_ne : u0 ≠ 0 := by
    intro h0
    have hin := orthonormal_iff_ite.mp hD.isHermitian.eigenvectorBasis.orthonormal i_max i_max
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hin
    have : star u0 ⬝ᵥ u0 = 1 := by simpa [u0] using hin
    rw [h0, dotProduct_zero] at this
    exact zero_ne_one this
  have hDu0 : D'.mulVec u0 = u0 := by
    have h1 : D.mulVec u0 = (dmax : ℂ) • u0 := hD.isHermitian.mulVec_eigenvectorBasis i_max
    have hsm : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
    rw [hsm, Matrix.smul_mulVec, h1, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hdmax.ne',
      Complex.ofReal_one, one_smul]
  -- Since ∑_j <u0, Phi' j u0> = 0, some j0 has Re <u0, Phi' j0 u0> ≥ 0!
  have hsum_q : ∑ j : Fin m, (star u0 ⬝ᵥ (Phi' j).mulVec u0).re = 0 := by
    rw [← Complex.re_sum, ← dotProduct_sum]
    have hvec : ∑ j : Fin m, (Phi' j).mulVec u0 = (∑ j : Fin m, Phi' j).mulVec u0 := by
      ext i; simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => by rw [Matrix.sum_apply, Finset.sum_mul]
    rw [hvec, hEq2', Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
  obtain ⟨j0, hj0_ge⟩ : ∃ j0 : Fin m, 0 ≤ (star u0 ⬝ᵥ (Phi' j0).mulVec u0).re := by
    by_contra hall; push Not at hall
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    have hlt : ∑ j : Fin m, (star u0 ⬝ᵥ (Phi' j).mulVec u0).re < 0 :=
      Finset.sum_neg (fun j _ => hall j) Finset.univ_nonempty
    linarith
  -- Step 3: Diagonalize Phi' j0 inside the invariant eigenspace E_max = ker(D' - I)!
  -- Even simpler: since D' and Phi' j0 are commuting Hermitian matrices, project u0 onto
  -- the eigenbasis of Phi' j0! Every nonzero component e_k of u0 in the eigenbasis of Phi' j0
  -- ALSO satisfies D' e_k = e_k (wait: D' preserves each eigenspace of Phi' j0, so projecting
  -- onto the spectral component of Phi' j0 with eigenvalue μ_k ≥ 0 directly yields a nonzero
  -- simultaneous eigenvector v with D' v = v and (Phi' j0) v = μ v, μ ≥ 0!!).
  let UΦ := (hPhi'_herm j0).eigenvectorUnitary
  let mu := (hPhi'_herm j0).eigenvalues
  let c : Fin n → ℂ := (UΦ : Mat n)ᴴ.mulVec u0
  have hq_exp : (star u0 ⬝ᵥ (Phi' j0).mulVec u0).re = ∑ k : Fin n, mu k * ‖c k‖ ^ 2 := by
    have hEqΦ : Phi' j0 = (UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)) * (UΦ : Mat n)ᴴ := by
      simpa [UΦ, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using (hPhi'_herm j0).spectral_theorem
    rw [hEqΦ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hst : star u0 ᵥ* (UΦ : Mat n) = star c := by
      simp only [c, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [hst, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have h1 : starRingEnd ℂ (c k) * ((mu k : ℂ) * c k) = (mu k : ℂ) * (starRingEnd ℂ (c k) * c k) := by ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  obtain ⟨k0, hk0_c, hk0_mu⟩ : ∃ k0 : Fin n, c k0 ≠ 0 ∧ 0 ≤ mu k0 := by
    by_contra hall; push Not at hall
    have hle : ∀ k : Fin n, mu k * ‖c k‖ ^ 2 ≤ 0 := fun k => by
      by_cases hck : c k = 0
      · simp [hck]
      · exact mul_nonpos_of_nonpos_of_nonneg (hall k hck).le (sq_nonneg _)
    -- Check that at least one c k ≠ 0 (since u0 ≠ 0), so sum < 0!
    obtain ⟨k1, hk1⟩ : ∃ k1 : Fin n, c k1 ≠ 0 := by
      by_contra hzero; push Not at hzero
      have hc0 : c = 0 := funext hzero
      have h1 := congrArg (Matrix.mulVec (UΦ : Mat n)) hc0
      simp only [c, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UΦ, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact hu0_ne h1
    have hlt : ∑ k : Fin n, mu k * ‖c k‖ ^ 2 < 0 := by
      calc ∑ k : Fin n, mu k * ‖c k‖ ^ 2
          = mu k1 * ‖c k1‖ ^ 2 + ∑ k ∈ Finset.univ.erase k1, mu k * ‖c k‖ ^ 2 :=
            (Finset.add_sum_erase _ _ (Finset.mem_univ k1)).symm
        _ < 0 + 0 := add_lt_add_of_lt_of_le
            (mul_neg_of_neg_of_pos (hall k1 hk1) (sq_pos_of_pos (norm_pos_iff.mpr hk1)))
            (Finset.sum_nonpos fun k _ => hle k)
        _ = 0 := add_zero 0
    linarith
  -- Construct the exact spectral projection v := P_{mu k0}(Phi' j0) u0!
  -- v is nonzero (its k0-th UΦ-coordinate is c k0 ≠ 0), satisfies (Phi' j0) v = (mu k0) v,
  -- AND since D' commutes with Phi' j0, D' commutes with P_{mu k0}(Phi' j0), so D' v = v!!
  let projDiag : Mat n := Matrix.diagonal (fun k => if mu k = mu k0 then (1 : ℂ) else 0)
  let P0 : Mat n := (UΦ : Mat n) * projDiag * (UΦ : Mat n)ᴴ
  let v : Fin n → ℂ := P0.mulVec u0
  have hv_ne : v ≠ 0 := by
    intro h0
    have h1 := congr_fun (congrArg (Matrix.mulVec (UΦ : Mat n)ᴴ) h0) k0
    dsimp [v, P0] at h1
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_zero, Pi.zero_apply] at h1
    rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ,
      Matrix.one_mul, ← Matrix.mulVec_mulVec] at h1
    change (projDiag.mulVec c) k0 = 0 at h1
    simp [projDiag, Matrix.mulVec_diagonal] at h1
    exact hk0_c h1
  have hPhi_v : (Phi' j0).mulVec v = (mu k0 : ℂ) • v := by
    have hEqΦ : Phi' j0 = (UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)) * (UΦ : Mat n)ᴴ := by
      simpa [UΦ, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using (hPhi'_herm j0).spectral_theorem
    have hmulP : Phi' j0 * P0 = (mu k0 : ℂ) • P0 := by
      dsimp [P0]; rw [hEqΦ]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hdiag_eq : Matrix.diagonal (fun i => (mu i : ℂ) * if mu i = mu k0 then (1 : ℂ) else 0) =
          (mu k0 : ℂ) • projDiag := by
        ext a b; by_cases hab : a = b
        · subst hab; by_cases hmu : mu a = mu k0 <;> simp [Matrix.diagonal, projDiag, hmu]
        · simp [Matrix.diagonal, projDiag, hab]
      rw [hdiag_eq, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
      ext a b; simp [Complex.real_smul]
    dsimp [v]; rw [Matrix.mulVec_mulVec, hmulP, Matrix.smul_mulVec]
    ext a; simp [Complex.real_smul]
  have hDP0 : D' * P0 = P0 * D' := by
    -- In the UΦ basis, M := UΦᴴ D' UΦ commutes with diag(mu), hence M_{ab} = 0 whenever mu a ≠ mu b,
    -- hence M commutes with projDiag = diag(1_{mu = mu k0})!
    let M : Mat n := (UΦ : Mat n)ᴴ * D' * (UΦ : Mat n)
    have hEqΦ : Phi' j0 = (UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)) * (UΦ : Mat n)ᴴ := by
      simpa [UΦ, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using (hPhi'_herm j0).spectral_theorem
    have hMcomm : M * Matrix.diagonal (fun k => (mu k : ℂ)) =
        Matrix.diagonal (fun k => (mu k : ℂ)) * M := by
      have h1 : (UΦ : Mat n)ᴴ * (D' * Phi' j0) * (UΦ : Mat n) =
          (UΦ : Mat n)ᴴ * (Phi' j0 * D') * (UΦ : Mat n) := by rw [hPhi'_comm j0]
      rw [hEqΦ] at h1
      simp only [Matrix.mul_assoc] at h1
      rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ,
        Matrix.one_mul, Matrix.mul_one] at h1
      have hL : (UΦ : Mat n)ᴴ * (D' * ((UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)))) =
          M * Matrix.diagonal (fun k => (mu k : ℂ)) := by dsimp [M]; simp only [Matrix.mul_assoc]
      have hR : Matrix.diagonal (fun k => (mu k : ℂ)) * ((UΦ : Mat n)ᴴ * (D' * (UΦ : Mat n))) =
          Matrix.diagonal (fun k => (mu k : ℂ)) * M := by dsimp [M]; simp only [Matrix.mul_assoc]
      rw [hL, hR] at h1; exact h1
    have hMproj : M * projDiag = projDiag * M := by
      ext a b
      simp only [projDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases h1 : mu a = mu k0 <;> by_cases h2 : mu b = mu k0
      · simp [h1, h2]
      · have hne : mu a ≠ mu b := by intro h; exact h2 (h ▸ h1)
        have hab := congr_fun (congr_fun hMcomm a) b
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab
        have hM0 : M a b = 0 := by
          have : M a b * ((mu b : ℂ) - (mu a : ℂ)) = 0 := by linear_combination hab
          have hsub_ne : (mu b : ℂ) - (mu a : ℂ) ≠ 0 := by
            rw [← Complex.ofReal_sub]; exact mt Complex.ofReal_eq_zero.mp (sub_ne_zero.mpr (Ne.symm hne))
          exact (mul_eq_zero.mp this).resolve_right hsub_ne
        simp [h1, h2, hM0]
      · have hne : mu a ≠ mu b := by intro h; exact h1 (h.symm ▸ h2)
        have hab := congr_fun (congr_fun hMcomm a) b
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab
        have hM0 : M a b = 0 := by
          have : M a b * ((mu b : ℂ) - (mu a : ℂ)) = 0 := by linear_combination hab
          have hsub_ne : (mu b : ℂ) - (mu a : ℂ) ≠ 0 := by
            rw [← Complex.ofReal_sub]; exact mt Complex.ofReal_eq_zero.mp (sub_ne_zero.mpr (Ne.symm hne))
          exact (mul_eq_zero.mp this).resolve_right hsub_ne
        simp [h1, h2, hM0]
      · simp [h1, h2]
    have hD'_back : D' = (UΦ : Mat n) * M * (UΦ : Mat n)ᴴ := by
      dsimp [M]; simp only [Matrix.mul_assoc]
      rw [unitary_mul_conjTranspose_self UΦ, Matrix.mul_one, ← Matrix.mul_assoc (UΦ : Mat n),
        unitary_mul_conjTranspose_self UΦ, Matrix.one_mul]
    rw [hD'_back]; dsimp [P0]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ, Matrix.one_mul,
      ← Matrix.mul_assoc M projDiag, hMproj, Matrix.mul_assoc,
      ← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ, Matrix.one_mul]
  have hDv : D'.mulVec v = v := by
    dsimp [v]; rw [Matrix.mulVec_mulVec, hDP0, ← Matrix.mulVec_mulVec, hDu0]
  -- Step 4: Apply Theorem 9(c) (Top-Eigenspace Spectral Dichotomy) to (D', H' j0, v, mu k0)!
  obtain ⟨h, hh_ge1, _, hscalar, hmu_eq⟩ :=
    top_eigenspace_spectral_dichotomy hκ hΛ_pos hk0_mu hD' hD'_le (hH' j0) (hEq1' j0) hv_ne hDv hPhi_v
  have hh_gt1 : 1 < h := by
    rcases eq_or_lt_of_le hh_ge1 with rfl | hgt
    · exfalso; rw [Real.one_rpow, mul_one] at hscalar; norm_num at hscalar; linarith
    · exact hgt
  -- Step 5: Bound <v, Phi' j v> ≥ -c_κ * ‖v‖^2 for EVERY j ≠ j0, and sum ∑_j <v, Phi' j v> = 0!
  have hv_norm_pos : 0 < (star v ⬝ᵥ v).re := by
    rw [dotProduct, Complex.re_sum]
    have hnn : ∀ i, 0 ≤ (star (v i) * v i).re := fun i => by
      rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg _
    obtain ⟨i1, hi1⟩ : ∃ i, v i ≠ 0 := by by_contra hall; push Not at hall; exact hv_ne (funext hall)
    refine Finset.sum_pos' (fun i _ => hnn i) ⟨i1, Finset.mem_univ _, ?_⟩
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hi1)
  let ck : ℝ := (κ - 1) ^ (κ - 1) / κ ^ κ
  have hother : ∀ j : Fin m, -ck * (star v ⬝ᵥ v).re ≤ (star v ⬝ᵥ (Phi' j).mulVec v).re := by
    intro j
    let UGj := (hG' j).isHermitian.eigenvectorUnitary
    let lamj := (hG' j).isHermitian.eigenvalues
    let zj : Fin n → ℂ := (UGj : Mat n)ᴴ.mulVec v
    have hquad_j : ∀ r : ℝ,
        (star v ⬝ᵥ (posDefPow r (hG' j)).mulVec v).re = ∑ i : Fin n, ‖zj i‖ ^ 2 * (lamj i) ^ r := by
      intro r
      unfold posDefPow
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      have hst : star v ᵥ* (UGj : Mat n) = star zj := by
        simp only [zj, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
      rw [hst, dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
      have h1 : starRingEnd ℂ (zj i) * ((((lamj i) ^ r : ℝ) : ℂ) * zj i) =
          (((lamj i) ^ r : ℝ) : ℂ) * (starRingEnd ℂ (zj i) * zj i) := by ring
      rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
    have hv_sum : (star v ⬝ᵥ v).re = ∑ i : Fin n, ‖zj i‖ ^ 2 := by
      have hv_back : v = (UGj : Mat n).mulVec zj := by
        simp only [zj, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UGj, Matrix.one_mulVec]
      conv_lhs => rw [hv_back]
      rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
        unitary_conjTranspose_mul_self UGj, Matrix.vecMul_one, dotProduct, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    have hsplit : (star v ⬝ᵥ (Phi' j).mulVec v).re =
        ∑ i : Fin n, ‖zj i‖ ^ 2 * ((lamj i) ^ κ - (lamj i) ^ (κ - 1)) := by
      dsimp [Phi']
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
      have hDkill : (star v ⬝ᵥ (D' * posDefPow (κ - 1) (hG' j) * D').mulVec v).re =
          (star v ⬝ᵥ (posDefPow (κ - 1) (hG' j)).mulVec v).re := by
        have hmul3 : (D' * posDefPow (κ - 1) (hG' j) * D').mulVec v = D'.mulVec ((posDefPow (κ - 1) (hG' j)).mulVec v) := by
          calc (D' * posDefPow (κ - 1) (hG' j) * D').mulVec v
              = (D' * posDefPow (κ - 1) (hG' j)).mulVec (D'.mulVec v) := (Matrix.mulVec_mulVec v _ D').symm
            _ = (D' * posDefPow (κ - 1) (hG' j)).mulVec v := by rw [hDv]
            _ = D'.mulVec ((posDefPow (κ - 1) (hG' j)).mulVec v) := (Matrix.mulVec_mulVec v D' _).symm
        rw [hmul3, Matrix.dotProduct_mulVec]
        have hst : star v ᵥ* D' = star v := by
          have h1 : star v ᵥ* D'ᴴ = star (D'.mulVec v) := (Matrix.star_mulVec D' v).symm
          rw [hD'.isHermitian.eq, hDv] at h1
          exact h1
        rw [hst]
      rw [hDkill, hquad_j κ, hquad_j (κ - 1), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hv_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpt := rpow_sub_rpow_ge_neg_ck hκ ((hG' j).eigenvalues_pos i)
    nlinarith [sq_nonneg ‖zj i‖]
  have hsum_v : ∑ j : Fin m, (star v ⬝ᵥ (Phi' j).mulVec v).re = 0 := by
    rw [← Complex.re_sum, ← dotProduct_sum]
    have hvec : ∑ j : Fin m, (Phi' j).mulVec v = (∑ j : Fin m, Phi' j).mulVec v := by
      ext i; simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun x _ => by rw [Matrix.sum_apply, Finset.sum_mul]
    rw [hvec, hEq2', Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
  have hj0_val : (star v ⬝ᵥ (Phi' j0).mulVec v).re = mu k0 * (star v ⬝ᵥ v).re := by
    rw [hPhi_v, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsum_split : (star v ⬝ᵥ (Phi' j0).mulVec v).re +
      ∑ j ∈ Finset.univ.erase j0, (star v ⬝ᵥ (Phi' j).mulVec v).re = 0 := by
    rw [Finset.add_sum_erase Finset.univ (fun j => (star v ⬝ᵥ (Phi' j).mulVec v).re) (Finset.mem_univ j0)]
    exact hsum_v
  have hrest_ge : -(((m : ℝ) - 1) * ck) * (star v ⬝ᵥ v).re ≤
      ∑ j ∈ Finset.univ.erase j0, (star v ⬝ᵥ (Phi' j).mulVec v).re := by
    calc -(((m : ℝ) - 1) * ck) * (star v ⬝ᵥ v).re
        = ((Finset.univ.erase j0).card : ℝ) * (-ck * (star v ⬝ᵥ v).re) := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
            have hm1 : 1 ≤ m := by omega
            rw [Nat.cast_sub hm1, Nat.cast_one]; ring
      _ = ∑ _j ∈ Finset.univ.erase j0, (-ck * (star v ⬝ᵥ v).re) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.univ.erase j0, (star v ⬝ᵥ (Phi' j).mulVec v).re :=
            Finset.sum_le_sum fun j _ => hother j
  have hmu_le : mu k0 ≤ ((m : ℝ) - 1) * ck := by nlinarith
  exact ⟨h, hh_gt1, hscalar, by linarith⟩

/-! ==========================================================================
    PART 6: Closed-Form Radical Caps (p = 4/3, p = 3/2) & Quadratic p → 1⁺ Law
    ========================================================================== -/

/-- Closed-form Corollary (p = 4/3, m = 2, κ = 2):
    Theorem 10 yields the exact radical cap Λ ≤ (13 + 16√2)/4 < 891/100! -/
theorem universal_bound_p43_m2 {Λ h : ℝ} (hh : 1 < h)
    (hscalar : (1 + h) ^ (3 : ℝ) = Λ * h ^ (1 : ℝ))
    (hbound : h ^ (1 : ℝ) * (h - 1) ≤ (1 : ℝ) * ((1 : ℝ) ^ (1 : ℝ) / (2 : ℝ) ^ (2 : ℝ))) :
    Λ ≤ (13 + 16 * Real.sqrt 2) / 4 ∧ Λ < 891 / 100 := by
  have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr zero_lt_two
  have hsq2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt zero_le_two
  rw [Real.rpow_one, Real.one_rpow, show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at hbound
  have hh_quad : h ^ 2 - h ≤ 1 / 4 := by nlinarith
  have hh_le : h ≤ (1 + Real.sqrt 2) / 2 := by
    have h1 : (2 * h - 1) ^ 2 ≤ 2 := by nlinarith
    have h2 : 2 * h - 1 ≤ Real.sqrt 2 := by nlinarith [Real.sq_sqrt zero_le_two]
    linarith
  have hcub : (1 + h) ^ (3 : ℝ) = (1 + h) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (1 + h) 3
  rw [hcub, Real.rpow_one] at hscalar
  have hLam_eq : Λ = (1 + h) ^ 3 / h := by field_simp [(by linarith : h ≠ 0)]; linarith
  -- (1 + h)^3 / h is increasing on h ≥ 1: check difference with h_max = (1 + √2)/2!
  let h0 : ℝ := (1 + Real.sqrt 2) / 2
  have hh0_gt : 1 < h0 := by dsimp [h0]; nlinarith
  have hmono : (1 + h) ^ 3 / h ≤ (1 + h0) ^ 3 / h0 := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hfac2 : (1 + h0) ^ 3 * h - (1 + h) ^ 3 * h0 =
        (h0 - h) * (h * h0 * (h0 + h + 3) - 1) := by ring
    have hh_le0 : h ≤ h0 := hh_le
    have hhh0 : 1 < h * h0 := by nlinarith
    have hpos : 0 < h * h0 * (h0 + h + 3) - 1 := by nlinarith
    have hprod : 0 ≤ (h0 - h) * (h * h0 * (h0 + h + 3) - 1) := mul_nonneg (by linarith) hpos.le
    linarith
  have hval : (1 + h0) ^ 3 / h0 = (13 + 16 * Real.sqrt 2) / 4 := by
    dsimp [h0]
    field_simp [(by linarith : 1 + Real.sqrt 2 ≠ 0)]
    nlinarith [hsq2_sq]
  have hLam_le : Λ ≤ (13 + 16 * Real.sqrt 2) / 4 := by linarith
  have hLam_lt : Λ < 891 / 100 := by
    have : 16 * Real.sqrt 2 < 2264 / 100 := by nlinarith [hsq2_sq]
    linarith
  exact ⟨hLam_le, hLam_lt⟩

/-- Closed-form Corollary (p = 3/2, m = 2, κ = 3/2):
    Theorem 10 yields the exact radical cap Λ ≤ 49√3/18 < 472/100! -/
theorem universal_bound_p32_m2 {Λ h : ℝ} (hh : 1 < h)
    (hscalar : (1 + h) ^ (2 : ℝ) = Λ * h ^ (1 / 2 : ℝ))
    (hbound : h ^ (1 / 2 : ℝ) * (h - 1) ≤ (1 : ℝ) * ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) / (3 / 2 : ℝ) ^ (3 / 2 : ℝ))) :
    Λ ≤ 49 * Real.sqrt 3 / 18 ∧ Λ < 472 / 100 := by
  have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsq3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set m : ℝ := Real.sqrt h
  have hm_gt1 : 1 < m := by
    have : (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    rw [this]; exact Real.sqrt_lt_sqrt zero_le_one hh
  have hm_sq : m ^ 2 = h := Real.sq_sqrt (by linarith)
  have hhr : h ^ (1 / 2 : ℝ) = m := (Real.sqrt_eq_rpow h).symm
  have hck : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / (3 / 2 : ℝ) ^ (3 / 2 : ℝ) = 2 / (3 * Real.sqrt 3) := by
    have h1 : (3 / 2 : ℝ) ^ (3 / 2 : ℝ) = (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
      calc (3 / 2 : ℝ) ^ (3 / 2 : ℝ) = (3 / 2 : ℝ) ^ ((1 : ℝ) + 1 / 2) := by norm_num
        _ = (3 / 2 : ℝ) ^ (1 : ℝ) * (3 / 2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_add (by norm_num) 1 (1 / 2)
        _ = (3 / 2 : ℝ) * (3 / 2 : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    have h2 : (3 / 2 : ℝ) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
    rw [h1, h2, ← Real.sqrt_eq_rpow 3]
    have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    field_simp [hhalf_pos.ne', hsq3.ne']
  rw [hhr, hck, one_mul, ← hm_sq] at hbound
  let m0 : ℝ := 2 / Real.sqrt 3
  have hm0_gt1 : 1 < m0 := by dsimp [m0]; rw [one_lt_div hsq3]; nlinarith [hsq3_sq]
  have hm0_val : m0 * (m0 ^ 2 - 1) = 2 / (3 * Real.sqrt 3) := by
    dsimp [m0]; field_simp [hsq3.ne']; nlinarith [hsq3_sq]
  have hm_le : m ≤ m0 := by
    by_contra hgt; push Not at hgt
    have : m0 * (m0 ^ 2 - 1) < m * (m ^ 2 - 1) := by
      have hfac : m * (m ^ 2 - 1) - m0 * (m0 ^ 2 - 1) = (m - m0) * (m ^ 2 + m * m0 + m0 ^ 2 - 1) := by ring
      have hpos : 0 < m ^ 2 + m * m0 + m0 ^ 2 - 1 := by nlinarith
      have hprod : 0 < (m - m0) * (m ^ 2 + m * m0 + m0 ^ 2 - 1) := mul_pos (by linarith) hpos
      linarith
    linarith
  have hsq_rpow : (1 + h) ^ (2 : ℝ) = (1 + h) ^ (2 : ℕ) := by exact_mod_cast Real.rpow_natCast (1 + h) 2
  rw [hsq_rpow, hhr, ← hm_sq] at hscalar
  have hLam_eq : Λ = (1 + m ^ 2) ^ 2 / m := by field_simp [(by linarith : m ≠ 0)]; linarith
  have hmono : (1 + m ^ 2) ^ 2 / m ≤ (1 + m0 ^ 2) ^ 2 / m0 := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have hfac : (1 + m0 ^ 2) ^ 2 * m - (1 + m ^ 2) ^ 2 * m0 =
        (m0 - m) * (m * m0 * (m0 ^ 2 + m * m0 + m ^ 2 + 2) - 1) := by ring
    have hmm0 : 1 < m * m0 := by nlinarith
    have hbig : 1 < m0 ^ 2 + m * m0 + m ^ 2 + 2 := by nlinarith
    have hpos : 0 < m * m0 * (m0 ^ 2 + m * m0 + m ^ 2 + 2) - 1 := by nlinarith
    have hprod : 0 ≤ (m0 - m) * (m * m0 * (m0 ^ 2 + m * m0 + m ^ 2 + 2) - 1) := mul_nonneg (by linarith) hpos.le
    linarith
  have hval : (1 + m0 ^ 2) ^ 2 / m0 = 49 * Real.sqrt 3 / 18 := by
    dsimp [m0]; field_simp [hsq3.ne']; nlinarith [hsq3_sq]
  have hLam_le : Λ ≤ 49 * Real.sqrt 3 / 18 := by linarith
  have hLam_lt : Λ < 472 / 100 := by
    have : 49 * Real.sqrt 3 < 472 * 18 / 100 := by nlinarith [hsq3_sq]
    linarith
  exact ⟨hLam_le, hLam_lt⟩

/-- Dimension-Free Non-Asymptotic Quadratic Upper Bound (Solving Open Question 2 for ALL 1 < p < 2, m ≥ 2):
    From Theorem 10, setting κ = p / (2(p - 1)) > 1 and C = (Λ / 2^(2κ - 1))^(1/(2κ)), we obtain:
      log C ≤ ((m^2 - 1) / (2 p^2)) * (p - 1)^2,
    hence C ≤ exp(((m^2 - 1) / (2 p^2)) * (p - 1)^2) for every 1 < p < 2 and every m ≥ 2! -/
theorem universal_quadratic_log_bound {m : ℕ} (hm : 2 ≤ m) {p Λ h : ℝ}
    (hp1 : 1 < p) (hp2 : p < 2) (hΛ : 0 < Λ) (hh : 1 < h)
    (hscalar : (1 + h) ^ (2 * (p / (2 * (p - 1))) - 1) = Λ * h ^ (p / (2 * (p - 1)) - 1))
    (hbound : h ^ (p / (2 * (p - 1)) - 1) * (h - 1) ≤
      ((m : ℝ) - 1) * ((p / (2 * (p - 1)) - 1) ^ (p / (2 * (p - 1)) - 1) /
        (p / (2 * (p - 1))) ^ (p / (2 * (p - 1))))) :
    let κ : ℝ := p / (2 * (p - 1))
    Real.log ((Λ / 2 ^ (2 * κ - 1)) ^ (1 / (2 * κ))) ≤ ((m : ℝ) ^ 2 - 1) / (2 * p ^ 2) * (p - 1) ^ 2 := by
  intro κ
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have hκ : 1 < κ := by dsimp [κ]; rw [one_lt_div (by linarith)]; linarith
  have hκ0 : 0 < κ := by linarith
  have hkm1 : 0 < κ - 1 := by linarith
  -- Step 1: Bound δ := h - 1 ≤ (m - 1) / κ!
  have hck_le : (κ - 1) ^ (κ - 1) / κ ^ κ ≤ 1 / κ := by
    have h1 : (κ - 1) ^ (κ - 1) ≤ κ ^ (κ - 1) :=
      Real.rpow_le_rpow hkm1.le (by linarith) hkm1.le
    have hkp : κ ^ κ = κ * κ ^ (κ - 1) := by
      calc κ ^ κ = κ ^ ((1 : ℝ) + (κ - 1)) := by congr 1; ring
        _ = κ ^ (1 : ℝ) * κ ^ (κ - 1) := Real.rpow_add hκ0 1 (κ - 1)
        _ = κ * κ ^ (κ - 1) := by rw [Real.rpow_one]
    rw [hkp, div_le_div_iff₀ (mul_pos hκ0 (Real.rpow_pos_of_pos hκ0 _)) hκ0]
    nlinarith
  have hhp_ge1 : 1 ≤ h ^ (κ - 1) := Real.one_le_rpow hh.le hkm1.le
  let δ : ℝ := h - 1
  have hδ0 : 0 < δ := by dsimp [δ]; linarith
  have hδ_le : δ ≤ ((m : ℝ) - 1) / κ := by
    have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h1 : δ ≤ h ^ (κ - 1) * δ := by nlinarith
    have h2 : ((m : ℝ) - 1) * ((κ - 1) ^ (κ - 1) / κ ^ κ) ≤ ((m : ℝ) - 1) * (1 / κ) :=
      mul_le_mul_of_nonneg_left hck_le hm1
    have h3 : ((m : ℝ) - 1) * (1 / κ) = ((m : ℝ) - 1) / κ := by ring
    dsimp [δ] at h1 ⊢; linarith
  -- Step 2: Exact identity Λ / 2^(2κ - 1) = ((1 + δ/2)^2 / (1 + δ))^(κ - 1) * (1 + δ/2)
  have hquot : Λ / 2 ^ (2 * κ - 1) =
      (1 + δ ^ 2 / (4 * (1 + δ))) ^ (κ - 1) * (1 + δ / 2) := by
    have h1h : 1 + h = 2 * (1 + δ / 2) := by dsimp [δ]; ring
    have h2p_ne : (2 : ℝ) ^ (2 * κ - 1) ≠ 0 := (Real.rpow_pos_of_pos zero_lt_two _).ne'
    have hh_ne : h ^ (κ - 1) ≠ 0 := (Real.rpow_pos_of_pos (by linarith : 0 < h) _).ne'
    have hLam : Λ / 2 ^ (2 * κ - 1) = (1 + δ / 2) ^ (2 * κ - 1) / (1 + δ) ^ (κ - 1) := by
      have hL1 : Λ = (1 + h) ^ (2 * κ - 1) / h ^ (κ - 1) := by field_simp [hh_ne]; linarith
      rw [hL1, h1h, Real.mul_rpow zero_le_two (by linarith : 0 ≤ 1 + δ / 2)]
      have hhd : h = 1 + δ := by dsimp [δ]; ring
      rw [hhd]; field_simp [h2p_ne, hh_ne]
    rw [hLam]
    have hsplit : (1 + δ / 2) ^ (2 * κ - 1) = ((1 + δ / 2) ^ (2 : ℝ)) ^ (κ - 1) * (1 + δ / 2) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ 1 + δ / 2)]
      calc (1 + δ / 2) ^ (2 * κ - 1)
          = (1 + δ / 2) ^ (2 * (κ - 1) + 1) := by congr 1; ring
        _ = (1 + δ / 2) ^ (2 * (κ - 1)) * (1 + δ / 2) ^ (1 : ℝ) := Real.rpow_add (by linarith) _ _
        _ = (1 + δ / 2) ^ (2 * (κ - 1)) * (1 + δ / 2) := by rw [Real.rpow_one]
    have hsq2 : (1 + δ / 2) ^ (2 : ℝ) / (1 + δ) = 1 + δ ^ 2 / (4 * (1 + δ)) := by
      have : (1 + δ / 2) ^ (2 : ℝ) = (1 + δ / 2) ^ (2 : ℕ) := by
        exact_mod_cast Real.rpow_natCast (1 + δ / 2) 2
      rw [this]; field_simp [(by linarith : 1 + δ ≠ 0)]; ring
    rw [hsplit, mul_div_right_comm, ← Real.div_rpow (Real.rpow_nonneg (by linarith) _) (by linarith), hsq2]
  -- Step 3: Apply log(1 + u) ≤ u to both factors!
  have hpos1 : 0 < 1 + δ ^ 2 / (4 * (1 + δ)) := by positivity
  have hpos2 : 0 < 1 + δ / 2 := by linarith
  have hlog : Real.log ((Λ / 2 ^ (2 * κ - 1)) ^ (1 / (2 * κ))) =
      ((κ - 1) / (2 * κ)) * Real.log (1 + δ ^ 2 / (4 * (1 + δ))) +
      (1 / (2 * κ)) * Real.log (1 + δ / 2) := by
    rw [Real.log_rpow (div_pos hΛ (Real.rpow_pos_of_pos zero_lt_two _)), hquot,
      Real.log_mul (Real.rpow_pos_of_pos hpos1 _).ne' hpos2.ne',
      Real.log_rpow hpos1]
    ring
  rw [hlog]
  have hlog1 : Real.log (1 + δ ^ 2 / (4 * (1 + δ))) ≤ δ ^ 2 / 4 := by
    calc Real.log (1 + δ ^ 2 / (4 * (1 + δ)))
        ≤ δ ^ 2 / (4 * (1 + δ)) := by linarith [Real.log_le_sub_one_of_pos hpos1]
      _ ≤ δ ^ 2 / 4 := by
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith [sq_nonneg δ]
  have hlog2 : Real.log (1 + δ / 2) ≤ δ / 2 := by linarith [Real.log_le_sub_one_of_pos hpos2]
  have hcoef1 : (κ - 1) / (2 * κ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) zero_lt_two]; linarith
  have hterm1 : (κ - 1) / (2 * κ) * Real.log (1 + δ ^ 2 / (4 * (1 + δ))) ≤ δ ^ 2 / 8 := by
    calc (κ - 1) / (2 * κ) * Real.log (1 + δ ^ 2 / (4 * (1 + δ)))
        ≤ (κ - 1) / (2 * κ) * (δ ^ 2 / 4) := mul_le_mul_of_nonneg_left hlog1 (by positivity)
      _ ≤ (1 / 2) * (δ ^ 2 / 4) := mul_le_mul_of_nonneg_right hcoef1 (by positivity)
      _ = δ ^ 2 / 8 := by ring
  have hterm2 : 1 / (2 * κ) * Real.log (1 + δ / 2) ≤ δ / (4 * κ) := by
    calc 1 / (2 * κ) * Real.log (1 + δ / 2)
        ≤ 1 / (2 * κ) * (δ / 2) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = δ / (4 * κ) := by ring
  have hδsq : δ ^ 2 ≤ (((m : ℝ) - 1) / κ) ^ 2 := by
    nlinarith [hδ0, hδ_le]
  have hsum_bound : δ ^ 2 / 8 + δ / (4 * κ) ≤ ((m : ℝ) ^ 2 - 1) / (8 * κ ^ 2) := by
    have h1 : δ ^ 2 / 8 ≤ ((m : ℝ) - 1) ^ 2 / (8 * κ ^ 2) := by
      have : (((m : ℝ) - 1) / κ) ^ 2 / 8 = ((m : ℝ) - 1) ^ 2 / (8 * κ ^ 2) := by ring
      linarith
    have h2 : δ / (4 * κ) ≤ ((m : ℝ) - 1) / (4 * κ ^ 2) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      have : δ * (4 * κ ^ 2) ≤ ((m : ℝ) - 1) / κ * (4 * κ ^ 2) :=
        mul_le_mul_of_nonneg_right hδ_le (by positivity)
      have hsimp : ((m : ℝ) - 1) / κ * (4 * κ ^ 2) = ((m : ℝ) - 1) * (4 * κ) := by
        field_simp [hκ0.ne']
      linarith
    have h3 : ((m : ℝ) - 1) ^ 2 / (8 * κ ^ 2) + ((m : ℝ) - 1) / (4 * κ ^ 2) =
        ((m : ℝ) ^ 2 - 1) / (8 * κ ^ 2) := by field_simp [hκ0.ne']; ring
    linarith
  have hκ_subst : ((m : ℝ) ^ 2 - 1) / (8 * κ ^ 2) = ((m : ℝ) ^ 2 - 1) / (2 * p ^ 2) * (p - 1) ^ 2 := by
    dsimp [κ]; field_simp [hp0.ne', hpm1.ne']; ring
  linarith

end MI20
