/-
  MI20/Theorem10B_SharpUniversalAndSuperexp.lean
  ==============================================
  Author:      Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Purpose:     Complete Mathlib-grounded, zero-sorry Lean 4.33.1 formalization of:
                 - Theorem 10A (`universal_sharp_one_line_bound`, `sharp_one_line_cap_p43_m2`,
                   `sharp_one_line_cap_p32_m2`, `sharp_one_line_p2_limit_frobenius`):
                   Sharp 1-line universal pure-algebraic bound for ALL 1 < p < 2 and ALL m ≥ 2:
                     (1 + h)^(2κ - 1) * (h - 1) ≤ (m - 1) * (2κ - 1)^(2κ - 1) / κ^(2κ),
                   strictly dominating Theorem 10 everywhere, exact at p → 2⁻ (recovering
                   Qiu's / Tang–Zhang's Frobenius constant √((1 + √m)/2) for every m ≥ 2),
                   and giving Λ < 872/100 (p = 4/3) and Λ < 451/100 (p = 3/2, beating Holden!).
                 - Theorem 10B (`universal_two_function_bound`, `two_function_regime1_bound`,
                   `two_function_regime2_bound`, `two_function_cap_p32_m2`, `two_function_cap_p43_m2`,
                   `superexponential_p2_collapse_bound`):
                   Coupled two-function elementary bound for ALL 1 < p < 2 and ALL m ≥ 2,
                   yielding closed-form complete-square caps Λ < 447/100 (p = 3/2, 9× tighter than
                   Holden with zero SDP) and Λ < 866/100 (p = 4/3), plus the explicit B = 1/(2 - p)
                   super-exponential collapse law as p → 2⁻.
                 - Theorem 10C (`bessel_two_line_identity_p43`):
                   Exact 2-line pure-algebraic Bessel identity ‖(D + H) H v‖² = 1 + 2a + s₂ - Λ P
                   and Bessel/Cauchy–Schwarz system at p = 4/3 for ALL m ≥ 2 (NO D ≤ I, NO [D, Φ] = 0,
                   NO SDP!).
-/

import MI20.Theorem9_10_CommutatorAndQuadraticBound

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ==========================================================================
    PART 0: Clean Complex Dot-Product & Spectral Quadratic Helpers
    ========================================================================== -/

private lemma dotProduct_star_self_im {n : ℕ} (x : Fin n → ℂ) : (star x ⬝ᵥ x).im = 0 := by
  rw [dotProduct, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_im]

private lemma dotProduct_star_comm {n : ℕ} (x y : Fin n → ℂ) :
    star x ⬝ᵥ y = starRingEnd ℂ (star y ⬝ᵥ x) := by
  rw [dotProduct, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

private lemma herm_dotProduct_mulVec_im {n : ℕ} {A : Mat n} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ A.mulVec x).im = 0 := by
  have h1 : star x ⬝ᵥ A.mulVec x = starRingEnd ℂ (star x ⬝ᵥ A.mulVec x) := by
    calc star x ⬝ᵥ A.mulVec x
        = starRingEnd ℂ (star (A.mulVec x) ⬝ᵥ x) := dotProduct_star_comm x (A.mulVec x)
      _ = starRingEnd ℂ ((star x ᵥ* Aᴴ) ⬝ᵥ x) := by rw [← Matrix.star_mulVec]
      _ = starRingEnd ℂ ((star x ᵥ* A) ⬝ᵥ x) := by rw [hA.eq]
      _ = starRingEnd ℂ (star x ⬝ᵥ A.mulVec x) := by rw [Matrix.dotProduct_mulVec]
  have him := congrArg Complex.im h1
  rw [Complex.conj_im] at him
  linarith

private lemma quad_posDefPow_spec {n : ℕ} {T : Mat n} (hT : T.PosDef) (w : Fin n → ℂ) :
    let U := hT.isHermitian.eigenvectorUnitary
    let lam := hT.isHermitian.eigenvalues
    let z : Fin n → ℂ := (U : Mat n)ᴴ.mulVec w
    (star w ⬝ᵥ w).re = ∑ i : Fin n, ‖z i‖ ^ 2 ∧
    (∀ r : ℝ, (star w ⬝ᵥ (posDefPow r hT).mulVec w).re = ∑ i : Fin n, ‖z i‖ ^ 2 * (lam i) ^ r) ∧
    (w ≠ 0 → 0 < (star w ⬝ᵥ w).re) := by
  intro U lam z
  have hnorm : (star w ⬝ᵥ w).re = ∑ i : Fin n, ‖z i‖ ^ 2 := by
    have hw_back : w = (U : Mat n).mulVec z := by
      simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec]
    conv_lhs => rw [hw_back]
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self U, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  refine ⟨hnorm, fun r => ?_, fun hw_ne => ?_⟩
  · unfold posDefPow
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hst : star w ᵥ* (U : Mat n) = star z := by
      simp only [z, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    change (star w ᵥ* (U : Mat n) ⬝ᵥ (Matrix.diagonal fun i => (((lam i) ^ r : ℝ) : ℂ)).mulVec z).re = _
    rw [hst, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have h1 : starRingEnd ℂ (z i) * ((((lam i) ^ r : ℝ) : ℂ) * z i) =
        (((lam i) ^ r : ℝ) : ℂ) * (starRingEnd ℂ (z i) * z i) := by ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
  · rw [hnorm]
    obtain ⟨i0, hi0⟩ : ∃ i, z i ≠ 0 := by
      by_contra hz; push Not at hz
      have hz0 : z = 0 := funext hz
      have h1 := congrArg (Matrix.mulVec (U : Mat n)) hz0
      simp only [z, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact hw_ne h1
    exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hi0)⟩

/-! ==========================================================================
    PART 1: Five-Line Weighted AM-GM Scalar Lemmas (Zero Derivatives!)
    ========================================================================== -/

/-- Weighted AM-GM bound for Theorem 10A:
    For all κ > 1 and z > 0, z^(2κ - 1) * (2 - z) ≤ (2κ - 1)^(2κ - 1) / κ^(2κ). -/
lemma rpow_mul_two_sub_le {κ z : ℝ} (hκ : 1 < κ) (hz : 0 < z) :
    z ^ (2 * κ - 1) * (2 - z) ≤ (2 * κ - 1) ^ (2 * κ - 1) / κ ^ (2 * κ) := by
  have h2k : 0 < 2 * κ := by linarith
  have h2km1 : 0 < 2 * κ - 1 := by linarith
  have hκ0 : 0 < κ := by linarith
  have hrhs_nonneg : 0 ≤ (2 * κ - 1) ^ (2 * κ - 1) / κ ^ (2 * κ) := by positivity
  by_cases hz2 : 2 ≤ z
  · have hle0 : z ^ (2 * κ - 1) * (2 - z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hz.le _) (by linarith)
    linarith
  · push Not at hz2
    have h2sub : 0 < 2 - z := by linarith
    have hw1 : 0 ≤ (2 * κ - 1) / (2 * κ) := by positivity
    have hw2 : 0 ≤ 1 / (2 * κ) := by positivity
    have hwsum : (2 * κ - 1) / (2 * κ) + 1 / (2 * κ) = 1 := by field_simp [h2k.ne']; ring
    have ha : 0 ≤ z / (2 * κ - 1) := by positivity
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ha h2sub.le hwsum
    have hrhs_simp : (2 * κ - 1) / (2 * κ) * (z / (2 * κ - 1)) + 1 / (2 * κ) * (2 - z) = 1 / κ := by
      field_simp [h2k.ne', h2km1.ne', hκ0.ne']; ring
    rw [hrhs_simp] at hamgm
    have hpow := Real.rpow_le_rpow (by positivity) hamgm h2k.le
    rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg h2sub.le _),
        ← Real.rpow_mul ha, ← Real.rpow_mul h2sub.le] at hpow
    have he1 : (2 * κ - 1) / (2 * κ) * (2 * κ) = 2 * κ - 1 := div_mul_cancel₀ _ h2k.ne'
    have he2 : 1 / (2 * κ) * (2 * κ) = 1 := div_mul_cancel₀ _ h2k.ne'
    rw [he1, he2, Real.rpow_one, Real.div_rpow hz.le h2km1.le,
        Real.div_rpow zero_le_one hκ0.le, Real.one_rpow] at hpow
    have hden_pos : 0 < (2 * κ - 1) ^ (2 * κ - 1) := Real.rpow_pos_of_pos h2km1 _
    have hmul := mul_le_mul_of_nonneg_right hpow hden_pos.le
    have hL : z ^ (2 * κ - 1) / (2 * κ - 1) ^ (2 * κ - 1) * (2 - z) * (2 * κ - 1) ^ (2 * κ - 1) =
        z ^ (2 * κ - 1) * (2 - z) := by field_simp [hden_pos.ne']
    have hR : 1 / κ ^ (2 * κ) * (2 * κ - 1) ^ (2 * κ - 1) =
        (2 * κ - 1) ^ (2 * κ - 1) / κ ^ (2 * κ) := by ring
    linarith

/-- Weighted AM-GM bound for Theorem 10B (F_Z ≤ 0):
    For all κ > 1, B > 0, and z > 0:
      z^(2κ - 1) * (B - z) ≤ ((2κ - 2)^(2κ - 2) / (2κ - 1)^(2κ - 1)) * B^(2κ - 1) * z. -/
lemma rpow_FZ_le_zero {κ B z : ℝ} (hκ : 1 < κ) (hB : 0 < B) (hz : 0 < z) :
    z ^ (2 * κ - 1) * (B - z) ≤
      ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1) * z := by
  have h2km2 : 0 < 2 * κ - 2 := by linarith
  have h2km1 : 0 < 2 * κ - 1 := by linarith
  have hrhs_nn : 0 ≤ ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1) * z := by
    exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg h2km2.le _) (Real.rpow_nonneg h2km1.le _))
      (Real.rpow_nonneg hB.le _)) hz.le
  by_cases hzB : B ≤ z
  · have hle0 : z ^ (2 * κ - 1) * (B - z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hz.le _) (by linarith)
    linarith
  · push Not at hzB
    have hBsub : 0 < B - z := by linarith
    have hw1 : 0 ≤ (2 * κ - 2) / (2 * κ - 1) := div_nonneg h2km2.le h2km1.le
    have hw2 : 0 ≤ 1 / (2 * κ - 1) := div_nonneg zero_le_one h2km1.le
    have hwsum : (2 * κ - 2) / (2 * κ - 1) + 1 / (2 * κ - 1) = 1 := by
      field_simp [h2km1.ne']; ring
    have ha : 0 ≤ z / (2 * κ - 2) := div_nonneg hz.le h2km2.le
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ha hBsub.le hwsum
    have hrhs_simp : (2 * κ - 2) / (2 * κ - 1) * (z / (2 * κ - 2)) + 1 / (2 * κ - 1) * (B - z) =
        B / (2 * κ - 1) := by
      have h1 : (2 * κ - 2) / (2 * κ - 1) * (z / (2 * κ - 2)) = z / (2 * κ - 1) := by
        rw [div_mul_div_comm, mul_comm (2 * κ - 2) z, mul_div_mul_right _ _ h2km2.ne']
      rw [h1]; ring
    rw [hrhs_simp] at hamgm
    have hlhs_nn : 0 ≤ (z / (2 * κ - 2)) ^ ((2 * κ - 2) / (2 * κ - 1)) * (B - z) ^ (1 / (2 * κ - 1)) :=
      mul_nonneg (Real.rpow_nonneg ha _) (Real.rpow_nonneg hBsub.le _)
    have hpow := Real.rpow_le_rpow hlhs_nn hamgm h2km1.le
    rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hBsub.le _),
        ← Real.rpow_mul ha, ← Real.rpow_mul hBsub.le] at hpow
    have he1 : (2 * κ - 2) / (2 * κ - 1) * (2 * κ - 1) = 2 * κ - 2 := div_mul_cancel₀ _ h2km1.ne'
    have he2 : 1 / (2 * κ - 1) * (2 * κ - 1) = 1 := div_mul_cancel₀ _ h2km1.ne'
    rw [he1, he2, Real.rpow_one, Real.div_rpow hz.le h2km2.le, Real.div_rpow hB.le h2km1.le] at hpow
    have hden_pos : 0 < (2 * κ - 2) ^ (2 * κ - 2) := Real.rpow_pos_of_pos h2km2 _
    have hmul := mul_le_mul_of_nonneg_right hpow (mul_nonneg hden_pos.le hz.le)
    have hsplit_z : z ^ (2 * κ - 1) = z ^ (2 * κ - 2) * z := by
      calc z ^ (2 * κ - 1) = z ^ ((2 * κ - 2) + 1) := by congr 1; ring
        _ = z ^ (2 * κ - 2) * z ^ (1 : ℝ) := Real.rpow_add hz _ _
        _ = z ^ (2 * κ - 2) * z := by rw [Real.rpow_one]
    have hL : z ^ (2 * κ - 2) / (2 * κ - 2) ^ (2 * κ - 2) * (B - z) * ((2 * κ - 2) ^ (2 * κ - 2) * z) =
        z ^ (2 * κ - 1) * (B - z) := by
      rw [hsplit_z]
      calc z ^ (2 * κ - 2) / (2 * κ - 2) ^ (2 * κ - 2) * (B - z) * ((2 * κ - 2) ^ (2 * κ - 2) * z)
          = (z ^ (2 * κ - 2) / (2 * κ - 2) ^ (2 * κ - 2) * (2 * κ - 2) ^ (2 * κ - 2)) * z * (B - z) := by ring
        _ = z ^ (2 * κ - 2) * z * (B - z) := by rw [div_mul_cancel₀ _ hden_pos.ne']
    have hR : B ^ (2 * κ - 1) / (2 * κ - 1) ^ (2 * κ - 1) * ((2 * κ - 2) ^ (2 * κ - 2) * z) =
        ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1) * z := by ring
    linarith

/-- Weighted AM-GM bound for Theorem 10B Regime I (1 < κ < 2):
    For all α > 0, γ > 0, x > 0:
      α * x - γ * x^κ ≤ ((κ - 1) * (2 - κ)^((2 - κ)/(κ - 1)) * α^(1/(κ - 1)) * γ^(-(2 - κ)/(κ - 1))) * x^(κ - 1). -/
lemma rpow_FX_regime1_le {κ α γ x : ℝ} (hκ1 : 1 < κ) (hκ2 : κ < 2)
    (hα : 0 < α) (hγ : 0 < γ) (hx : 0 < x) :
    α * x - γ * x ^ κ ≤
      ((κ - 1) * (2 - κ) ^ ((2 - κ) / (κ - 1)) * α ^ (1 / (κ - 1)) *
        γ ^ (-(2 - κ) / (κ - 1))) * x ^ (κ - 1) := by
  have hkm1 : 0 < κ - 1 := by linarith
  have h2mk : 0 < 2 - κ := by linarith
  set C : ℝ := (κ - 1) * (2 - κ) ^ ((2 - κ) / (κ - 1)) * α ^ (1 / (κ - 1)) * γ ^ (-(2 - κ) / (κ - 1))
  have hC_pos : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (mul_pos hkm1 (Real.rpow_pos_of_pos h2mk _))
      (Real.rpow_pos_of_pos hα _)) (Real.rpow_pos_of_pos hγ _)
  have hw1 : 0 ≤ 2 - κ := h2mk.le
  have hw2 : 0 ≤ κ - 1 := hkm1.le
  have hwsum : (2 - κ) + (κ - 1) = 1 := by ring
  have ha : 0 ≤ γ * x / (2 - κ) := div_nonneg (mul_nonneg hγ.le hx.le) h2mk.le
  have hb : 0 ≤ C / (κ - 1) := div_nonneg hC_pos.le hkm1.le
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ha hb hwsum
  have hR : (2 - κ) * (γ * x / (2 - κ)) + (κ - 1) * (C / (κ - 1)) = γ * x + C := by
    field_simp [h2mk.ne', hkm1.ne']
  rw [hR] at hamgm
  have hL : (γ * x / (2 - κ)) ^ (2 - κ) * (C / (κ - 1)) ^ (κ - 1) = α * x ^ (2 - κ) := by
    have hCdiv : C / (κ - 1) =
        (2 - κ) ^ ((2 - κ) / (κ - 1)) * α ^ (1 / (κ - 1)) * γ ^ (-(2 - κ) / (κ - 1)) := by
      dsimp [C]; field_simp [hkm1.ne']
    rw [hCdiv, Real.div_rpow (mul_nonneg hγ.le hx.le) h2mk.le, Real.mul_rpow hγ.le hx.le,
        Real.mul_rpow (mul_nonneg (Real.rpow_nonneg h2mk.le _) (Real.rpow_nonneg hα.le _))
          (Real.rpow_nonneg hγ.le _),
        Real.mul_rpow (Real.rpow_nonneg h2mk.le _) (Real.rpow_nonneg hα.le _),
        ← Real.rpow_mul h2mk.le, ← Real.rpow_mul hα.le, ← Real.rpow_mul hγ.le]
    have he1 : (2 - κ) / (κ - 1) * (κ - 1) = 2 - κ := div_mul_cancel₀ _ hkm1.ne'
    have he2 : 1 / (κ - 1) * (κ - 1) = 1 := div_mul_cancel₀ _ hkm1.ne'
    have he3 : -(2 - κ) / (κ - 1) * (κ - 1) = -(2 - κ) := div_mul_cancel₀ _ hkm1.ne'
    rw [he1, he2, he3, Real.rpow_one, Real.rpow_neg hγ.le]
    have hγp_ne : γ ^ (2 - κ) ≠ 0 := (Real.rpow_pos_of_pos hγ _).ne'
    have h2p_ne : (2 - κ) ^ (2 - κ) ≠ 0 := (Real.rpow_pos_of_pos h2mk _).ne'
    field_simp [hγp_ne, h2p_ne]
  rw [hL] at hamgm
  have hxk_pos : 0 < x ^ (κ - 1) := Real.rpow_pos_of_pos hx _
  have hmul := mul_le_mul_of_nonneg_right hamgm hxk_pos.le
  have h1 : x ^ (2 - κ) * x ^ (κ - 1) = x := by
    rw [← Real.rpow_add hx]
    have hexp : (2 - κ) + (κ - 1) = 1 := by ring
    rw [hexp, Real.rpow_one]
  have h2 : x * x ^ (κ - 1) = x ^ κ := by
    calc x * x ^ (κ - 1) = x ^ (1 : ℝ) * x ^ (κ - 1) := by rw [Real.rpow_one]
      _ = x ^ (1 + (κ - 1)) := (Real.rpow_add hx _ _).symm
      _ = x ^ κ := by congr 1; ring
  have hL2 : α * x ^ (2 - κ) * x ^ (κ - 1) = α * x := by rw [mul_assoc, h1]
  have hR2 : (γ * x + C) * x ^ (κ - 1) = γ * x ^ κ + C * x ^ (κ - 1) := by
    rw [add_mul, mul_assoc, h2]
  linarith

/-- Weighted AM-GM bound for Theorem 10B Regime II (κ > 2):
    For all α > 0, M > 0, x > 0:
      α * x - M * x^(κ - 1) ≤ ((κ - 2) / (κ - 1)) * (α^(κ - 1) / ((κ - 1) * M))^(1 / (κ - 2)). -/
lemma rpow_FX_regime2_le {κ α M x : ℝ} (hκ2 : 2 < κ) (hα : 0 < α) (hM : 0 < M) (hx : 0 < x) :
    α * x - M * x ^ (κ - 1) ≤
      ((κ - 2) / (κ - 1)) * (α ^ (κ - 1) / ((κ - 1) * M)) ^ (1 / (κ - 2)) := by
  have hkm1 : 0 < κ - 1 := by linarith
  have hkm2 : 0 < κ - 2 := by linarith
  set C : ℝ := ((κ - 2) / (κ - 1)) * (α ^ (κ - 1) / ((κ - 1) * M)) ^ (1 / (κ - 2))
  have hw1 : 0 ≤ 1 / (κ - 1) := by positivity
  have hw2 : 0 ≤ (κ - 2) / (κ - 1) := by positivity
  have hwsum : 1 / (κ - 1) + (κ - 2) / (κ - 1) = 1 := by field_simp [hkm1.ne']; ring
  have ha : 0 ≤ (κ - 1) * M * x ^ (κ - 1) := by positivity
  have hb : 0 ≤ (κ - 1) / (κ - 2) * C := by positivity
  have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 ha hb hwsum
  have hR : 1 / (κ - 1) * ((κ - 1) * M * x ^ (κ - 1)) +
      (κ - 2) / (κ - 1) * ((κ - 1) / (κ - 2) * C) = M * x ^ (κ - 1) + C := by
    field_simp [hkm1.ne', hkm2.ne']
  rw [hR] at hamgm
  have hL : ((κ - 1) * M * x ^ (κ - 1)) ^ (1 / (κ - 1)) *
      ((κ - 1) / (κ - 2) * C) ^ ((κ - 2) / (κ - 1)) = α * x := by
    have hCsimp : (κ - 1) / (κ - 2) * C = (α ^ (κ - 1) / ((κ - 1) * M)) ^ (1 / (κ - 2)) := by
      dsimp [C]; field_simp [hkm1.ne', hkm2.ne']
    rw [hCsimp, Real.mul_rpow (by positivity) (Real.rpow_nonneg hx.le _),
        ← Real.rpow_mul hx.le, ← Real.rpow_mul (by positivity)]
    have he1 : (κ - 1) * (1 / (κ - 1)) = 1 := mul_one_div_cancel hkm1.ne'
    have he2 : 1 / (κ - 2) * ((κ - 2) / (κ - 1)) = 1 / (κ - 1) := by field_simp [hkm1.ne', hkm2.ne']
    rw [he1, he2, Real.rpow_one, Real.div_rpow (Real.rpow_nonneg hα.le _) (by positivity),
        ← Real.rpow_mul hα.le, he1, Real.rpow_one]
    have hMp_ne : ((κ - 1) * M) ^ (1 / (κ - 1)) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
    field_simp [hMp_ne]
  linarith

/-! ==========================================================================
    PART 2: Core Spectral Identity Linking A = D + H and G = D^(1/2) H D^(1/2)
    ========================================================================== -/

lemma spectral_identities_A_and_G {n : ℕ} {κ Λ : ℝ}
    {D H : Mat n} (hD : D.PosDef) (hH : H.PosDef)
    (hEq : posDefPow (2 * κ - 1) (hD.add hH) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH) *
        posDefPow (1 / 2 : ℝ) hD))
    {v : Fin n → ℂ} (hv : v ≠ 0) (hDv : D.mulVec v = v) :
    let Dhalf := posDefPow (1 / 2 : ℝ) hD
    let hG : (Dhalf * H * Dhalf).PosDef := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) hH
    let hA : (D + H).PosDef := hD.add hH
    let Phi := posDefPow κ hG - D * posDefPow (κ - 1) hG * D
    (star v ⬝ᵥ (D + H).mulVec v).re = (star v ⬝ᵥ v).re + (star v ⬝ᵥ (Dhalf * H * Dhalf).mulVec v).re ∧
    (star v ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec v).re =
      Λ * (star v ⬝ᵥ (posDefPow (κ - 1) hG).mulVec v).re ∧
    (star v ⬝ᵥ (posDefPow (2 * κ) hA).mulVec v).re =
      Λ * ((star v ⬝ᵥ (posDefPow (κ - 1) hG).mulVec v).re + (star v ⬝ᵥ (posDefPow κ hG).mulVec v).re) ∧
    (2 * (star v ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec v).re -
        (star v ⬝ᵥ (posDefPow (2 * κ) hA).mulVec v).re) =
      -Λ * (star v ⬝ᵥ Phi.mulVec v).re := by
  intro Dhalf hG hA Phi
  have hDv1 : D.mulVec v = (1 : ℂ) • v := by simpa using hDv
  have hDhalf_v : Dhalf.mulVec v = v := by
    have h := (posDefPow_mulVec_of_eig (1 / 2 : ℝ) hD hv hDv1).2
    simpa [Dhalf, Real.one_rpow] using h
  have hstar_Dhalf : star v ᵥ* Dhalf = star v := by
    have h1 : star v ᵥ* Dhalfᴴ = star (Dhalf.mulVec v) := (Matrix.star_mulVec Dhalf v).symm
    rw [(posDefPow_posDef (1 / 2) hD).isHermitian.eq, hDhalf_v] at h1
    exact h1
  have hstar_D : star v ᵥ* D = star v := by
    have h1 : star v ᵥ* Dᴴ = star (D.mulVec v) := (Matrix.star_mulVec D v).symm
    rw [hD.isHermitian.eq, hDv] at h1
    exact h1
  have hId1 : (star v ⬝ᵥ (D + H).mulVec v).re =
      (star v ⬝ᵥ v).re + (star v ⬝ᵥ (Dhalf * H * Dhalf).mulVec v).re := by
    have hGv : star v ⬝ᵥ (Dhalf * H * Dhalf).mulVec v = star v ⬝ᵥ H.mulVec v := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDhalf_v,
        Matrix.dotProduct_mulVec, hstar_Dhalf]
    rw [hGv, Matrix.add_mulVec, dotProduct_add, hDv, Complex.add_re]
  have hId2 : (star v ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec v).re =
      Λ * (star v ⬝ᵥ (posDefPow (κ - 1) hG).mulVec v).re := by
    rw [hEq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDhalf_v,
      Matrix.dotProduct_mulVec, hstar_Dhalf,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hA2k : posDefPow (2 * κ) hA = posDefPow (2 * κ - 1) hA * (D + H) := by
    calc posDefPow (2 * κ) hA
        = posDefPow ((2 * κ - 1) + 1) hA := by congr 1; ring
      _ = posDefPow (2 * κ - 1) hA * posDefPow 1 hA := (posDefPow_mul_posDefPow (2 * κ - 1) 1 hA).symm
      _ = posDefPow (2 * κ - 1) hA * (D + H) := by rw [posDefPow_one]
  have hA2km1_Hv : (star v ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec (H.mulVec v)).re =
      Λ * (star v ⬝ᵥ (posDefPow κ hG).mulVec v).re := by
    have hG_pow : posDefPow (κ - 1) hG * (Dhalf * H * Dhalf) = posDefPow κ hG := by
      calc posDefPow (κ - 1) hG * (Dhalf * H * Dhalf)
          = posDefPow (κ - 1) hG * posDefPow 1 hG := by rw [posDefPow_one]
        _ = posDefPow ((κ - 1) + 1) hG := posDefPow_mul_posDefPow (κ - 1) 1 hG
        _ = posDefPow κ hG := by congr 1; ring
    have hstep : (Dhalf * posDefPow (κ - 1) hG * Dhalf).mulVec (H.mulVec v) =
        Dhalf.mulVec ((posDefPow κ hG).mulVec v) := by
      calc (Dhalf * posDefPow (κ - 1) hG * Dhalf).mulVec (H.mulVec v)
          = (Dhalf * posDefPow (κ - 1) hG * Dhalf * H).mulVec v := by rw [Matrix.mulVec_mulVec]
        _ = (Dhalf * posDefPow (κ - 1) hG * Dhalf * H).mulVec (Dhalf.mulVec v) := by rw [hDhalf_v]
        _ = (Dhalf * (posDefPow (κ - 1) hG * (Dhalf * H * Dhalf))).mulVec v := by
              rw [Matrix.mulVec_mulVec]; simp only [Matrix.mul_assoc]
        _ = (Dhalf * posDefPow κ hG).mulVec v := by rw [hG_pow]
        _ = Dhalf.mulVec ((posDefPow κ hG).mulVec v) := (Matrix.mulVec_mulVec v _ _).symm
    rw [hEq, Matrix.smul_mulVec, hstep, dotProduct_smul, smul_eq_mul,
      Matrix.dotProduct_mulVec, hstar_Dhalf,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hId3 : (star v ⬝ᵥ (posDefPow (2 * κ) hA).mulVec v).re =
      Λ * ((star v ⬝ᵥ (posDefPow (κ - 1) hG).mulVec v).re + (star v ⬝ᵥ (posDefPow κ hG).mulVec v).re) := by
    rw [hA2k, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.mulVec_add, hDv, dotProduct_add,
      Complex.add_re, hId2, hA2km1_Hv]
    ring
  have hPhi_q : (star v ⬝ᵥ Phi.mulVec v).re =
      (star v ⬝ᵥ (posDefPow κ hG).mulVec v).re - (star v ⬝ᵥ (posDefPow (κ - 1) hG).mulVec v).re := by
    dsimp [Phi]
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    have hDk : (star v ⬝ᵥ (D * posDefPow (κ - 1) hG * D).mulVec v).re =
        (star v ⬝ᵥ (posDefPow (κ - 1) hG).mulVec v).re := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDv,
        Matrix.dotProduct_mulVec, hstar_D]
    rw [hDk]
  refine ⟨hId1, hId2, hId3, ?_⟩
  rw [hId2, hId3, hPhi_q]; ring

/-! ==========================================================================
    PART 3: Top-Eigenspace Negative-Flux State Extraction (All m ≥ 2)
    ========================================================================== -/

theorem exists_negative_flux_eigenvector {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {κ Λ : ℝ}
    (hκ : 1 < κ) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0) :
    ∃ (D' H' : Mat n) (hD' : D'.PosDef) (hH' : H'.PosDef) (h P : ℝ) (w : Fin n → ℂ),
      1 < h ∧
      (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1) ≤ P ∧
      posDefPow (2 * κ - 1) (hD'.add hH') =
        (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD' *
          posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH') *
          posDefPow (1 / 2 : ℝ) hD') ∧
      w ≠ 0 ∧
      D'.mulVec w = w ∧
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH') -
       D' * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH') * D').mulVec w =
        ((-P : ℝ) : ℂ) • w := by
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos zero_lt_two _) hΛ
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let evalsD := hD.isHermitian.eigenvalues
  obtain ⟨i_max, _, hi_max⟩ := Finset.exists_max_image Finset.univ evalsD Finset.univ_nonempty
  set dmax : ℝ := evalsD i_max
  have hdmax : 0 < dmax := hD.eigenvalues_pos i_max
  have hc_pos : 0 < dmax⁻¹ := inv_pos.mpr hdmax
  let D' : Mat n := dmax⁻¹ • D
  let H' : Fin m → Mat n := fun j => dmax⁻¹ • H j
  have hD' : D'.PosDef := hD.smul hc_pos
  have hH' : ∀ j, (H' j).PosDef := fun j => (hH j).smul hc_pos
  have hD'_le : (1 - D').PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨Matrix.isHermitian_one.sub hD'.isHermitian, fun x => ?_⟩
    have hre_nonneg : 0 ≤ (star x ⬝ᵥ (1 - D').mulVec x).re := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re]
      let UD := hD.isHermitian.eigenvectorUnitary
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
      have hxx : (star x ⬝ᵥ x).re = ∑ i : Fin n, ‖y i‖ ^ 2 := (quad_posDefPow_spec hD x).1
      rw [hD'x, hxx, sub_nonneg]
      refine Finset.sum_le_sum fun i _ => ?_
      have hle1 : dmax⁻¹ * evalsD i ≤ 1 := by
        rw [inv_mul_le_iff₀ hdmax, mul_one]; exact hi_max i (Finset.mem_univ i)
      nlinarith [sq_nonneg ‖y i‖]
    rw [Complex.le_def]
    exact ⟨hre_nonneg, (herm_dotProduct_mulVec_im (Matrix.isHermitian_one.sub hD'.isHermitian) x).symm⟩
  let Dhalf := posDefPow (1 / 2 : ℝ) hD
  let D'half := posDefPow (1 / 2 : ℝ) hD'
  let hG : ∀ j, (Dhalf * H j * Dhalf).PosDef := fun j =>
    posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)
  let hG' : ∀ j, (D'half * H' j * D'half).PosDef := fun j =>
    posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') (hH' j)
  have hD'half_eq : D'half = ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) • Dhalf := posDefPow_smul (1 / 2) hc_pos hD
  have hG'_eq : ∀ j, D'half * H' j * D'half = (dmax⁻¹ ^ (2 : ℝ)) • (Dhalf * H j * Dhalf) := by
    intro j
    rw [hD'half_eq]
    have hHj : H' j = ((dmax⁻¹ : ℝ) : ℂ) • H j := by ext a b; simp [H', Complex.real_smul]
    rw [hHj]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have hsc : dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ * dmax⁻¹ ^ (1 / 2 : ℝ)) = dmax⁻¹ ^ (2 : ℝ) := by
      calc dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ * dmax⁻¹ ^ (1 / 2 : ℝ))
          = (dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (1 / 2 : ℝ)) * dmax⁻¹ ^ (1 : ℝ) := by rw [Real.rpow_one]; ring
        _ = dmax⁻¹ ^ ((1 / 2 : ℝ) + 1 / 2) * dmax⁻¹ ^ (1 : ℝ) := by rw [Real.rpow_add hc_pos]
        _ = dmax⁻¹ ^ (((1 / 2 : ℝ) + 1 / 2) + 1) := (Real.rpow_add hc_pos _ _).symm
        _ = dmax⁻¹ ^ (2 : ℝ) := by congr 1; norm_num
    ext a b
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
    have hsc_c : ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (((dmax⁻¹ : ℝ) : ℂ) * ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) = ((dmax⁻¹ ^ (2 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsc]
    linear_combination (Dhalf * H j * Dhalf) a b * hsc_c
  have hG'pow_eq : ∀ j (r : ℝ), posDefPow r (hG' j) =
      ((dmax⁻¹ ^ (2 * r) : ℝ) : ℂ) • posDefPow r (hG j) := by
    intro j r
    have h2pos : 0 < dmax⁻¹ ^ (2 : ℝ) := Real.rpow_pos_of_pos hc_pos 2
    have hsm := posDefPow_smul r h2pos (hG j)
    have hG'eq : D'half * H' j * D'half = (dmax⁻¹ ^ (2 : ℝ)) • (Dhalf * H j * Dhalf) := hG'_eq j
    have heq : posDefPow r (hG' j) = posDefPow r ((hG j).smul h2pos) := by
      let U := ((hG j).smul h2pos).isHermitian.eigenvectorUnitary
      let lam := ((hG j).smul h2pos).isHermitian.eigenvalues
      have hspec : D'half * H' j * D'half =
          (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
        rw [hG'eq]
        simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using ((hG j).smul h2pos).isHermitian.spectral_theorem
      exact posDefPow_eq_of_diag r (hG' j) U lam (fun i => ((hG j).smul h2pos).eigenvalues_pos i) hspec
    rw [heq, hsm, ← Real.rpow_mul hc_pos.le]
  have hEq1' : ∀ j, posDefPow (2 * κ - 1) (hD'.add (hH' j)) =
      (Λ : ℂ) • (D'half * posDefPow (κ - 1) (hG' j) * D'half) := by
    intro j
    have hsum_eq : D' + H' j = dmax⁻¹ • (D + H j) := by simp [D', H', smul_add]
    have hL : posDefPow (2 * κ - 1) (hD'.add (hH' j)) =
        ((dmax⁻¹ ^ (2 * κ - 1) : ℝ) : ℂ) • posDefPow (2 * κ - 1) (hD.add (hH j)) := by
      have hsm := posDefPow_smul (2 * κ - 1) hc_pos (hD.add (hH j))
      let U := ((hD.add (hH j)).smul hc_pos).isHermitian.eigenvectorUnitary
      let lam := ((hD.add (hH j)).smul hc_pos).isHermitian.eigenvalues
      have hspec : D' + H' j = (U : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U : Mat n)ᴴ := by
        rw [hsum_eq]
        simpa [U, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using ((hD.add (hH j)).smul hc_pos).isHermitian.spectral_theorem
      have heq1 : posDefPow (2 * κ - 1) (hD'.add (hH' j)) =
          posDefPow (2 * κ - 1) ((hD.add (hH j)).smul hc_pos) :=
        posDefPow_eq_of_diag (2 * κ - 1) (hD'.add (hH' j)) U lam
          (fun i => ((hD.add (hH j)).smul hc_pos).eigenvalues_pos i) hspec
      rw [heq1, hsm]
    rw [hL, hEq1 j, hG'pow_eq j (κ - 1)]
    have hR : D'half * (((dmax⁻¹ ^ (2 * (κ - 1)) : ℝ) : ℂ) • posDefPow (κ - 1) (hG j)) * D'half =
        ((dmax⁻¹ ^ (2 * κ - 1) : ℝ) : ℂ) • (Dhalf * posDefPow (κ - 1) (hG j) * Dhalf) := by
      rw [hD'half_eq]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hsc_r : dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ)) =
          dmax⁻¹ ^ (2 * κ - 1) := by
        calc dmax⁻¹ ^ (1 / 2 : ℝ) * (dmax⁻¹ ^ (2 * (κ - 1)) * dmax⁻¹ ^ (1 / 2 : ℝ))
            = (dmax⁻¹ ^ (1 / 2 : ℝ) * dmax⁻¹ ^ (1 / 2 : ℝ)) * dmax⁻¹ ^ (2 * (κ - 1)) := by ring
          _ = dmax⁻¹ ^ ((1 / 2 : ℝ) + 1 / 2) * dmax⁻¹ ^ (2 * (κ - 1)) := by rw [Real.rpow_add hc_pos]
          _ = dmax⁻¹ ^ (((1 / 2 : ℝ) + 1 / 2) + 2 * (κ - 1)) := (Real.rpow_add hc_pos _ _).symm
          _ = dmax⁻¹ ^ (2 * κ - 1) := by congr 1; ring
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul]
      have hsc_c : ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (((dmax⁻¹ ^ (2 * (κ - 1)) : ℝ) : ℂ) * ((dmax⁻¹ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
          ((dmax⁻¹ ^ (2 * κ - 1) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsc_r]
      linear_combination (Dhalf * posDefPow (κ - 1) (hG j) * Dhalf) a b * hsc_c
    rw [hR, smul_comm]
  let Phi' : Fin m → Mat n := fun j => posDefPow κ (hG' j) - D' * posDefPow (κ - 1) (hG' j) * D'
  have hPhi'_eq : ∀ j, Phi' j = (dmax⁻¹ ^ (2 * κ)) •
      (posDefPow κ (hG j) - D * posDefPow (κ - 1) (hG j) * D) := by
    intro j; dsimp [Phi']
    have hD'c : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
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
      ext a b; simp only [Matrix.smul_apply, smul_eq_mul]
      have hsc_c : ((dmax⁻¹ : ℝ) : ℂ) * (((dmax⁻¹ : ℝ) : ℂ) * ((dmax⁻¹ ^ (2 * (κ - 1)) : ℝ) : ℂ)) =
          ((dmax⁻¹ ^ (2 * κ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hsc_r]
      linear_combination (D * posDefPow (κ - 1) (hG j) * D) a b * hsc_c
    rw [hG'pow_eq j κ, hterm2, ← smul_sub]
    ext a b; simp [Complex.real_smul]
  have hEq2' : ∑ j : Fin m, Phi' j = 0 := by
    simp_rw [hPhi'_eq, ← Finset.smul_sum, hEq2, smul_zero]
  have hPhi'_herm : ∀ j, (Phi' j).IsHermitian := fun j =>
    (posDefPow_posDef κ (hG' j)).isHermitian.sub
      (posDef_conj_of_posDef hD' (posDefPow_posDef (κ - 1) (hG' j))).isHermitian
  have hPhi'_comm : ∀ j, D' * Phi' j = Phi' j * D' := fun j =>
    universal_commutator_theorem hΛ_pos hD' (hH' j) (hEq1' j)
  have hspec_proj : ∀ (j : Fin m) (u : Fin n → ℂ), u ≠ 0 → D'.mulVec u = u →
      ∀ (k0 : Fin n), ((hPhi'_herm j).eigenvectorUnitary : Mat n)ᴴ.mulVec u k0 ≠ 0 →
      ∃ w : Fin n → ℂ, w ≠ 0 ∧ D'.mulVec w = w ∧
        (Phi' j).mulVec w = ((hPhi'_herm j).eigenvalues k0 : ℂ) • w := by
    intro j u _ hDu k0 hk0_c
    let UΦ := (hPhi'_herm j).eigenvectorUnitary
    let mu := (hPhi'_herm j).eigenvalues
    let projDiag : Mat n := Matrix.diagonal (fun k => if mu k = mu k0 then (1 : ℂ) else 0)
    let P0 : Mat n := (UΦ : Mat n) * projDiag * (UΦ : Mat n)ᴴ
    let w : Fin n → ℂ := P0.mulVec u
    have hw_ne : w ≠ 0 := by
      intro h0
      have h1 := congr_fun (congrArg (Matrix.mulVec (UΦ : Mat n)ᴴ) h0) k0
      dsimp [w, P0] at h1
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mulVec_zero, Pi.zero_apply] at h1
      rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ,
        Matrix.one_mul, ← Matrix.mulVec_mulVec] at h1
      simp [projDiag, Matrix.mulVec_diagonal] at h1
      exact hk0_c h1
    have hEqΦ : Phi' j = (UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)) * (UΦ : Mat n)ᴴ := by
      simpa [UΦ, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using (hPhi'_herm j).spectral_theorem
    have hPhi_w : (Phi' j).mulVec w = (mu k0 : ℂ) • w := by
      have hmulP : Phi' j * P0 = (mu k0 : ℂ) • P0 := by
        dsimp [P0]; rw [hEqΦ]; simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ,
          Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
        have hdiag_eq : Matrix.diagonal (fun i => (mu i : ℂ) * if mu i = mu k0 then (1 : ℂ) else 0) =
            (mu k0 : ℂ) • projDiag := by
          ext a b; by_cases hab : a = b
          · subst hab; by_cases hmu : mu a = mu k0 <;> simp [Matrix.diagonal, projDiag, hmu]
          · simp [Matrix.diagonal, projDiag, hab]
        rw [hdiag_eq, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
        ext a b; simp [Complex.real_smul]
      dsimp [w]; rw [Matrix.mulVec_mulVec, hmulP, Matrix.smul_mulVec]
      ext a; simp [Complex.real_smul]
    have hDP0 : D' * P0 = P0 * D' := by
      let M : Mat n := (UΦ : Mat n)ᴴ * D' * (UΦ : Mat n)
      have hMcomm : M * Matrix.diagonal (fun k => (mu k : ℂ)) =
          Matrix.diagonal (fun k => (mu k : ℂ)) * M := by
        have h1 : (UΦ : Mat n)ᴴ * (D' * Phi' j) * (UΦ : Mat n) =
            (UΦ : Mat n)ᴴ * (Phi' j * D') * (UΦ : Mat n) := by rw [hPhi'_comm j]
        rw [hEqΦ] at h1; simp only [Matrix.mul_assoc] at h1
        rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ,
          Matrix.one_mul, Matrix.mul_one] at h1
        have hL : (UΦ : Mat n)ᴴ * (D' * ((UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)))) =
            M * Matrix.diagonal (fun k => (mu k : ℂ)) := by dsimp [M]; simp only [Matrix.mul_assoc]
        have hR : Matrix.diagonal (fun k => (mu k : ℂ)) * ((UΦ : Mat n)ᴴ * (D' * (UΦ : Mat n))) =
            Matrix.diagonal (fun k => (mu k : ℂ)) * M := by dsimp [M]; simp only [Matrix.mul_assoc]
        rw [hL, hR] at h1; exact h1
      have hMproj : M * projDiag = projDiag * M := by
        ext a b; simp only [projDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
        by_cases h1 : mu a = mu k0 <;> by_cases h2 : mu b = mu k0
        · simp [h1, h2]
        · have hne : mu a ≠ mu b := fun h => h2 (h ▸ h1)
          have hab := congr_fun (congr_fun hMcomm a) b
          simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hab
          have hM0 : M a b = 0 := by
            have : M a b * ((mu b : ℂ) - (mu a : ℂ)) = 0 := by linear_combination hab
            have hsub_ne : (mu b : ℂ) - (mu a : ℂ) ≠ 0 := by
              rw [← Complex.ofReal_sub]; exact mt Complex.ofReal_eq_zero.mp (sub_ne_zero.mpr (Ne.symm hne))
            exact (mul_eq_zero.mp this).resolve_right hsub_ne
          simp [h1, h2, hM0]
        · have hne : mu a ≠ mu b := fun h => h1 (h.symm ▸ h2)
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
      rw [hD'_back]; dsimp [P0]; simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ, Matrix.one_mul,
        ← Matrix.mul_assoc M projDiag, hMproj, Matrix.mul_assoc,
        ← Matrix.mul_assoc (UΦ : Mat n)ᴴ (UΦ : Mat n), unitary_conjTranspose_mul_self UΦ, Matrix.one_mul]
    have hDw : D'.mulVec w = w := by
      dsimp [w]; rw [Matrix.mulVec_mulVec, hDP0, ← Matrix.mulVec_mulVec, hDu]
    exact ⟨w, hw_ne, hDw, hPhi_w⟩
  let u0 : Fin n → ℂ := (hD.isHermitian.eigenvectorBasis i_max).ofLp
  have hu0_ne : u0 ≠ 0 := by
    intro h0
    have hin := orthonormal_iff_ite.mp hD.isHermitian.eigenvectorBasis.orthonormal i_max i_max
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hin
    have : star u0 ⬝ᵥ u0 = 1 := by simpa [u0] using hin
    rw [h0, dotProduct_zero] at this; exact zero_ne_one this
  have hDu0 : D'.mulVec u0 = u0 := by
    have h1 : D.mulVec u0 = (dmax : ℂ) • u0 := hD.isHermitian.mulVec_eigenvectorBasis i_max
    have hsm : D' = ((dmax⁻¹ : ℝ) : ℂ) • D := by ext a b; simp [D', Complex.real_smul]
    rw [hsm, Matrix.smul_mulVec, h1, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hdmax.ne',
      Complex.ofReal_one, one_smul]
  have hsum_q : ∀ x : Fin n → ℂ, ∑ j : Fin m, (star x ⬝ᵥ (Phi' j).mulVec x).re = 0 := by
    intro x
    rw [← Complex.re_sum, ← dotProduct_sum]
    have hvec : ∑ j : Fin m, (Phi' j).mulVec x = (∑ j : Fin m, Phi' j).mulVec x := by
      ext i; simp only [Finset.sum_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ => by rw [Matrix.sum_apply, Finset.sum_mul]
    rw [hvec, hEq2', Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
  obtain ⟨j0, hj0_ge⟩ : ∃ j0 : Fin m, 0 ≤ (star u0 ⬝ᵥ (Phi' j0).mulVec u0).re := by
    by_contra hall; push Not at hall
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    have hlt := Finset.sum_neg (fun j _ => hall j) Finset.univ_nonempty
    linarith [hsum_q u0]
  have hq_spec : ∀ (j : Fin m) (x : Fin n → ℂ),
      (star x ⬝ᵥ (Phi' j).mulVec x).re =
        ∑ k : Fin n, (hPhi'_herm j).eigenvalues k *
          ‖(((hPhi'_herm j).eigenvectorUnitary : Mat n)ᴴ.mulVec x) k‖ ^ 2 := by
    intro j x
    let UΦ := (hPhi'_herm j).eigenvectorUnitary
    let mu := (hPhi'_herm j).eigenvalues
    let c := (UΦ : Mat n)ᴴ.mulVec x
    have hEqΦ : Phi' j = (UΦ : Mat n) * Matrix.diagonal (fun k => (mu k : ℂ)) * (UΦ : Mat n)ᴴ := by
      simpa [UΦ, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using (hPhi'_herm j).spectral_theorem
    conv_lhs => rw [hEqΦ]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    have hst : star x ᵥ* (UΦ : Mat n) = star c := by
      simp only [c, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    change (star x ᵥ* (UΦ : Mat n) ⬝ᵥ (Matrix.diagonal fun k => (mu k : ℂ)).mulVec c).re = _
    rw [hst, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.star_apply, Matrix.mulVec_diagonal, Complex.star_def]
    have h1 : starRingEnd ℂ (c k) * ((mu k : ℂ) * c k) = (mu k : ℂ) * (starRingEnd ℂ (c k) * c k) := by ring
    rw [h1, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnorm_spec : ∀ (j : Fin m) (x : Fin n → ℂ),
      (star x ⬝ᵥ x).re = ∑ k : Fin n, ‖(((hPhi'_herm j).eigenvectorUnitary : Mat n)ᴴ.mulVec x) k‖ ^ 2 := by
    intro j x
    let UΦ := (hPhi'_herm j).eigenvectorUnitary
    let c := (UΦ : Mat n)ᴴ.mulVec x
    have hx_back : x = (UΦ : Mat n).mulVec c := by
      simp only [c, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UΦ, Matrix.one_mulVec]
    conv_lhs => rw [hx_back]
    rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.vecMul_vecMul,
      unitary_conjTranspose_mul_self UΦ, Matrix.vecMul_one, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    rfl
  obtain ⟨k0, hk0_c, hk0_mu⟩ : ∃ k0 : Fin n,
      (((hPhi'_herm j0).eigenvectorUnitary : Mat n)ᴴ.mulVec u0) k0 ≠ 0 ∧
      0 ≤ (hPhi'_herm j0).eigenvalues k0 := by
    by_contra hall; push Not at hall
    let UΦ := (hPhi'_herm j0).eigenvectorUnitary
    let c := (UΦ : Mat n)ᴴ.mulVec u0
    obtain ⟨k1, hk1⟩ : ∃ k1 : Fin n, c k1 ≠ 0 := by
      by_contra hz; push Not at hz
      have hc0 : c = 0 := funext hz
      have h1 := congrArg (Matrix.mulVec (UΦ : Mat n)) hc0
      simp only [c, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UΦ, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact hu0_ne h1
    have hle : ∀ k, (hPhi'_herm j0).eigenvalues k * ‖c k‖ ^ 2 ≤ 0 := fun k => by
      by_cases hck : c k = 0
      · simp [hck]
      · exact mul_nonpos_of_nonpos_of_nonneg (hall k hck).le (sq_nonneg _)
    have hlt : ∑ k : Fin n, (hPhi'_herm j0).eigenvalues k * ‖c k‖ ^ 2 < 0 := by
      calc ∑ k : Fin n, (hPhi'_herm j0).eigenvalues k * ‖c k‖ ^ 2
          = (hPhi'_herm j0).eigenvalues k1 * ‖c k1‖ ^ 2 +
            ∑ k ∈ Finset.univ.erase k1, (hPhi'_herm j0).eigenvalues k * ‖c k‖ ^ 2 :=
            (Finset.add_sum_erase _ _ (Finset.mem_univ k1)).symm
        _ < 0 + 0 := add_lt_add_of_lt_of_le
            (mul_neg_of_neg_of_pos (hall k1 hk1) (sq_pos_of_pos (norm_pos_iff.mpr hk1)))
            (Finset.sum_nonpos fun k _ => hle k)
        _ = 0 := add_zero 0
    linarith [hq_spec j0 u0]
  obtain ⟨v, hv_ne, hDv, hPhi0_v⟩ := hspec_proj j0 u0 hu0_ne hDu0 k0 hk0_c
  obtain ⟨h, hh_ge1, _, hscalar, hmu_eq⟩ :=
    top_eigenspace_spectral_dichotomy hκ hΛ_pos hk0_mu hD' hD'_le (hH' j0) (hEq1' j0) hv_ne hDv hPhi0_v
  have hh_gt1 : 1 < h := by
    rcases eq_or_lt_of_le hh_ge1 with rfl | hgt
    · exfalso; rw [Real.one_rpow, mul_one] at hscalar; norm_num at hscalar; linarith
    · exact hgt
  set σ : ℝ := h ^ (κ - 1) * (h - 1)
  have hv_norm_pos : 0 < (star v ⬝ᵥ v).re := (quad_posDefPow_spec hD' v).2.2 hv_ne
  have hj0_val : (star v ⬝ᵥ (Phi' j0).mulVec v).re = σ * (star v ⬝ᵥ v).re := by
    rw [hPhi0_v, hmu_eq, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hsum_erase : ∑ j ∈ Finset.univ.erase j0, (star v ⬝ᵥ (Phi' j).mulVec v).re =
      -σ * (star v ⬝ᵥ v).re := by
    have h1 := Finset.add_sum_erase Finset.univ (fun j => (star v ⬝ᵥ (Phi' j).mulVec v).re) (Finset.mem_univ j0)
    linarith [hsum_q v, hj0_val]
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hcard_erase : ((Finset.univ.erase j0).card : ℝ) = (m : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]
    have hm1 : 1 ≤ m := by omega
    rw [Nat.cast_sub hm1, Nat.cast_one]
  obtain ⟨j1, _, hj1_le⟩ : ∃ j1 ∈ Finset.univ.erase j0,
      (star v ⬝ᵥ (Phi' j1).mulVec v).re ≤ -(σ / ((m : ℝ) - 1)) * (star v ⬝ᵥ v).re := by
    by_contra hall; push Not at hall
    have hne : (Finset.univ.erase j0).Nonempty := by
      have hc : 0 < (Finset.univ.erase j0).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ j0), Finset.card_univ, Fintype.card_fin]; omega
      exact Finset.card_pos.mp hc
    have hgt : ∑ j ∈ Finset.univ.erase j0, (-(σ / ((m : ℝ) - 1)) * (star v ⬝ᵥ v).re) <
        ∑ j ∈ Finset.univ.erase j0, (star v ⬝ᵥ (Phi' j).mulVec v).re :=
      Finset.sum_lt_sum_of_nonempty hne fun j hj => hall j hj
    rw [Finset.sum_const, nsmul_eq_mul, hcard_erase] at hgt
    have hsimp : ((m : ℝ) - 1) * (-(σ / ((m : ℝ) - 1)) * (star v ⬝ᵥ v).re) = -σ * (star v ⬝ᵥ v).re := by
      field_simp [hm1_pos.ne']
    linarith
  obtain ⟨k1, hk1_c, hk1_mu⟩ : ∃ k1 : Fin n,
      (((hPhi'_herm j1).eigenvectorUnitary : Mat n)ᴴ.mulVec v) k1 ≠ 0 ∧
      (hPhi'_herm j1).eigenvalues k1 ≤ -(σ / ((m : ℝ) - 1)) := by
    by_contra hall; push Not at hall
    let UΦ := (hPhi'_herm j1).eigenvectorUnitary
    let c := (UΦ : Mat n)ᴴ.mulVec v
    obtain ⟨k2, hk2⟩ : ∃ k2 : Fin n, c k2 ≠ 0 := by
      by_contra hz; push Not at hz
      have hc0 : c = 0 := funext hz
      have h1 := congrArg (Matrix.mulVec (UΦ : Mat n)) hc0
      simp only [c, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self UΦ, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact hv_ne h1
    have hge : ∀ k, -(σ / ((m : ℝ) - 1)) * ‖c k‖ ^ 2 ≤ (hPhi'_herm j1).eigenvalues k * ‖c k‖ ^ 2 := fun k => by
      by_cases hck : c k = 0
      · simp [hck]
      · exact mul_le_mul_of_nonneg_right (hall k hck).le (sq_nonneg _)
    have hgt : ∑ k : Fin n, -(σ / ((m : ℝ) - 1)) * ‖c k‖ ^ 2 <
        ∑ k : Fin n, (hPhi'_herm j1).eigenvalues k * ‖c k‖ ^ 2 := by
      have hadd := Finset.add_sum_erase Finset.univ
        (fun k => (hPhi'_herm j1).eigenvalues k * ‖c k‖ ^ 2) (Finset.mem_univ k2)
      calc ∑ k : Fin n, -(σ / ((m : ℝ) - 1)) * ‖c k‖ ^ 2
          = -(σ / ((m : ℝ) - 1)) * ‖c k2‖ ^ 2 +
            ∑ k ∈ Finset.univ.erase k2, -(σ / ((m : ℝ) - 1)) * ‖c k‖ ^ 2 :=
            (Finset.add_sum_erase _ _ (Finset.mem_univ k2)).symm
        _ < (hPhi'_herm j1).eigenvalues k2 * ‖c k2‖ ^ 2 +
            ∑ k ∈ Finset.univ.erase k2, (hPhi'_herm j1).eigenvalues k * ‖c k‖ ^ 2 :=
            add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_right (hall k2 hk2) (sq_pos_of_pos (norm_pos_iff.mpr hk2)))
              (Finset.sum_le_sum fun k _ => hge k)
        _ = ∑ k : Fin n, (hPhi'_herm j1).eigenvalues k * ‖c k‖ ^ 2 := hadd
    rw [← Finset.mul_sum, ← hnorm_spec j1 v, ← hq_spec j1 v] at hgt
    linarith
  obtain ⟨w, hw_ne, hDw, hPhi1_w⟩ := hspec_proj j1 v hv_ne hDv k1 hk1_c
  set P : ℝ := -(hPhi'_herm j1).eigenvalues k1
  refine ⟨D', H' j1, hD', hH' j1, h, P, w, hh_gt1, hscalar, ?_, hEq1' j1, hw_ne, hDw, ?_⟩
  · dsimp [P, σ]; linarith
  · have hneg : (-P : ℝ) = (hPhi'_herm j1).eigenvalues k1 := by dsimp [P]; ring
    rw [hneg]; exact hPhi1_w

/-! ==========================================================================
    PART 4: Theorem 10A — Sharp 1-Line Universal Upper Bound (ALL 1<p<2, m≥2)
    ========================================================================== -/

theorem universal_sharp_one_line_bound {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {κ Λ : ℝ}
    (hκ : 1 < κ) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0) :
    ∃ h : ℝ, 1 < h ∧ (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      (1 + h) ^ (2 * κ - 1) * (h - 1) ≤
        ((m : ℝ) - 1) * ((2 * κ - 1) ^ (2 * κ - 1) / κ ^ (2 * κ)) := by
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos zero_lt_two _) hΛ
  obtain ⟨D', H', hD', hH', h, P, w, hh_gt1, hscalar, hP_ge, hEq1', hw_ne, hDw, hPhi_w⟩ :=
    exists_negative_flux_eigenvector hn hm hκ hΛ hD hH hEq1 hEq2
  let hA := hD'.add hH'
  have hid := (spectral_identities_A_and_G hD' hH' hEq1' hw_ne hDw).2.2.2
  obtain ⟨hw_sum, hquad_A, hw_pos_fn⟩ := quad_posDefPow_spec hA w
  have hw_pos : 0 < (star w ⬝ᵥ w).re := hw_pos_fn hw_ne
  let zA := (hA.isHermitian.eigenvectorUnitary : Mat n)ᴴ.mulVec w
  let lamA := hA.isHermitian.eigenvalues
  have hPhi_re : (star w ⬝ᵥ
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH') -
       D' * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH') * D').mulVec w).re =
      -P * (star w ⬝ᵥ w).re := by
    rw [hPhi_w, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hLP_eq : Λ * P * (star w ⬝ᵥ w).re =
      ∑ i : Fin n, ‖zA i‖ ^ 2 * ((lamA i) ^ (2 * κ - 1) * (2 - lamA i)) := by
    have h1 : 2 * (star w ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec w).re -
        (star w ⬝ᵥ (posDefPow (2 * κ) hA).mulVec w).re = Λ * P * (star w ⬝ᵥ w).re := by
      rw [hid, hPhi_re]; ring
    rw [← h1, hquad_A (2 * κ - 1), hquad_A (2 * κ), Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hpow2k : (lamA i) ^ (2 * κ) = (lamA i) ^ (2 * κ - 1) * lamA i := by
      calc (lamA i) ^ (2 * κ) = (lamA i) ^ ((2 * κ - 1) + 1) := by congr 1; ring
        _ = (lamA i) ^ (2 * κ - 1) * (lamA i) ^ (1 : ℝ) := Real.rpow_add (hA.eigenvalues_pos i) _ _
        _ = (lamA i) ^ (2 * κ - 1) * lamA i := by rw [Real.rpow_one]
    rw [hpow2k]; ring
  set M_rhs : ℝ := (2 * κ - 1) ^ (2 * κ - 1) / κ ^ (2 * κ)
  have hLP_le : Λ * P * (star w ⬝ᵥ w).re ≤ M_rhs * (star w ⬝ᵥ w).re := by
    rw [hLP_eq, hw_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpt := rpow_mul_two_sub_le hκ (hA.eigenvalues_pos i)
    nlinarith [sq_nonneg ‖zA i‖]
  have hLP : Λ * P ≤ M_rhs := by nlinarith
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hL_sig : Λ * (h ^ (κ - 1) * (h - 1)) ≤ ((m : ℝ) - 1) * M_rhs := by
    have h1 : Λ * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) ≤ M_rhs := by
      calc Λ * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) ≤ Λ * P :=
            mul_le_mul_of_nonneg_left hP_ge hΛ_pos.le
        _ ≤ M_rhs := hLP
    have h2 : Λ * (h ^ (κ - 1) * (h - 1)) = ((m : ℝ) - 1) * (Λ * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1))) := by
      field_simp [hm1_pos.ne']
    nlinarith
  have hcancel : (1 + h) ^ (2 * κ - 1) * (h - 1) = Λ * (h ^ (κ - 1) * (h - 1)) := by
    rw [hscalar]; ring
  exact ⟨h, hh_gt1, hscalar, by linarith⟩

theorem sharp_one_line_cap_p43_m2 {Λ h : ℝ} (hh : 1 < h)
    (hscalar : (1 + h) ^ (3 : ℝ) = Λ * h ^ (1 : ℝ))
    (hbound : (1 + h) ^ (3 : ℝ) * (h - 1) ≤ (1 : ℝ) * ((3 : ℝ) ^ (3 : ℝ) / (2 : ℝ) ^ (4 : ℝ))) :
    Λ < 872 / 100 := by
  have hcub : (1 + h) ^ (3 : ℝ) = (1 + h) ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast (1 + h) 3
  rw [hcub, Real.rpow_one] at hscalar
  rw [hcub] at hbound
  have hval_rhs : (1 : ℝ) * ((3 : ℝ) ^ (3 : ℝ) / (2 : ℝ) ^ (4 : ℝ)) = 27 / 16 := by norm_num
  rw [hval_rhs] at hbound
  have hh_lt : h < 1167 / 1000 := by
    by_contra hge; push Not at hge
    have h1 : (1 + (1167 / 1000 : ℝ)) ^ 3 * (1167 / 1000 - 1) ≤ (1 + h) ^ 3 * (h - 1) := by
      nlinarith [sq_nonneg (h - 1167 / 1000)]
    norm_num at h1; linarith
  have hLam_eq : Λ = (1 + h) ^ 3 / h := by field_simp [(by linarith : h ≠ 0)]; linarith
  rw [hLam_eq, div_lt_iff₀ (by linarith)]
  have hdiff : (872 / 100 : ℝ) * h - (1 + h) ^ 3 =
      ((872 / 100 : ℝ) * (1167 / 1000) - (1 + 1167 / 1000) ^ 3) +
      (1167 / 1000 - h) * (h ^ 2 + (1167 / 1000 + 3) * h + ((1167 / 1000) ^ 2 + 3 * (1167 / 1000) + 3) - 872 / 100) := by
    ring
  have hrem : 0 < h ^ 2 + (1167 / 1000 + 3) * h + ((1167 / 1000) ^ 2 + 3 * (1167 / 1000) + 3) - 872 / 100 := by
    nlinarith
  have hbase : (0 : ℝ) < (872 / 100 : ℝ) * (1167 / 1000) - (1 + 1167 / 1000) ^ 3 := by norm_num
  nlinarith

theorem sharp_one_line_cap_p32_m2 {Λ h : ℝ} (hh : 1 < h)
    (hscalar : (1 + h) ^ (2 : ℝ) = Λ * h ^ (1 / 2 : ℝ))
    (hbound : (1 + h) ^ (2 : ℝ) * (h - 1) ≤ (1 : ℝ) * ((2 : ℝ) ^ (2 : ℝ) / (3 / 2 : ℝ) ^ (3 : ℝ))) :
    Λ < 451 / 100 := by
  have hsq : (1 + h) ^ (2 : ℝ) = (1 + h) ^ (2 : ℕ) := by exact_mod_cast Real.rpow_natCast (1 + h) 2
  rw [hsq] at hscalar hbound
  have hval_rhs : (1 : ℝ) * ((2 : ℝ) ^ (2 : ℝ) / (3 / 2 : ℝ) ^ (3 : ℝ)) = 32 / 27 := by norm_num
  rw [hval_rhs] at hbound
  have hh_lt : h < 1238 / 1000 := by
    by_contra hge; push Not at hge
    have h1 : (1 + (1238 / 1000 : ℝ)) ^ 2 * (1238 / 1000 - 1) ≤ (1 + h) ^ 2 * (h - 1) := by nlinarith
    norm_num at h1; linarith
  have hhr : h ^ (1 / 2 : ℝ) = Real.sqrt h := (Real.sqrt_eq_rpow h).symm
  rw [hhr] at hscalar
  have hsq_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
  have hΛ_pos : 0 < Λ := by nlinarith
  have hsq_eq : Λ ^ 2 * h = (1 + h) ^ 4 := by
    have h1 : (Λ * Real.sqrt h) ^ 2 = ((1 + h) ^ 2) ^ 2 := by rw [← hscalar]
    have h2 : (Λ * Real.sqrt h) ^ 2 = Λ ^ 2 * h := by rw [mul_pow, Real.sq_sqrt (by linarith)]
    linarith [h1, h2]
  have hmono : (1 + h) ^ 4 * (1238 / 1000 : ℝ) < (1 + 1238 / 1000 : ℝ) ^ 4 * h := by
    set b : ℝ := 1238 / 1000
    have hfac : (1 + b) ^ 4 * h - (1 + h) ^ 4 * b =
        (b - h) * (b * h * (b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6) - 1) := by ring
    have hb_gt : 0 < b - h := sub_pos.mpr hh_lt
    have hbh : 1 < b * h := by dsimp [b]; nlinarith
    have hbig : 6 < b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6 := by dsimp [b]; nlinarith
    have hpos : 0 < b * h * (b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6) - 1 := by nlinarith
    have hprod : 0 < (b - h) * (b * h * (b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6) - 1) :=
      mul_pos hb_gt hpos
    linarith
  have htop : (1 + (1238 / 1000 : ℝ)) ^ 4 < (451 / 100 : ℝ) ^ 2 * (1238 / 1000 : ℝ) := by norm_num
  have hΛsq_lt : Λ ^ 2 < (451 / 100 : ℝ) ^ 2 := by
    have h1 : Λ ^ 2 * h * (1238 / 1000 : ℝ) < (451 / 100 : ℝ) ^ 2 * (1238 / 1000 : ℝ) * h := by
      nlinarith
    nlinarith
  nlinarith

theorem sharp_one_line_p2_limit_frobenius {m : ℕ} (hm : 2 ≤ m) {h : ℝ} (hh : 1 ≤ h)
    (hbound : (1 + h) * (h - 1) ≤ (m : ℝ) - 1) :
    Real.sqrt ((1 + h) / 2) ≤ Real.sqrt ((1 + Real.sqrt (m : ℝ)) / 2) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hh_sq : h ^ 2 ≤ (m : ℝ) := by nlinarith
  have hh_le : h ≤ Real.sqrt (m : ℝ) := by
    nlinarith [Real.sq_sqrt hm0, Real.sqrt_nonneg (m : ℝ)]
  exact Real.sqrt_le_sqrt (by linarith)

/-! ==========================================================================
    PART 5: Theorem 10B — Coupled Two-Function Bound & Super-Exponential p → 2⁻ Law
    ========================================================================== -/

theorem universal_two_function_bound {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {κ Λ : ℝ}
    (hκ : 1 < κ) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0)
    {α β γ cZ cX : ℝ} (hγ : 0 ≤ γ)
    (hFZ : ∀ z : ℝ, 0 < z → z ^ (2 * κ - 1) * (2 - β - z) - α * z ≤ cZ)
    (hFX : ∀ x : ℝ, 0 < x → (β * Λ + γ) * x ^ (κ - 1) - γ * x ^ κ + α * x ≤ cX) :
    ∃ h : ℝ, 1 < h ∧ (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      (Λ + γ) * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) - α ≤ cZ + cX := by
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos zero_lt_two _) hΛ
  obtain ⟨D', H', hD', hH', h, P, w, hh_gt1, hscalar, hP_ge, hEq1', hw_ne, hDw, hPhi_w⟩ :=
    exists_negative_flux_eigenvector hn hm hκ hΛ hD hH hEq1 hEq2
  let hA := hD'.add hH'
  let hG := posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD') hH'
  obtain ⟨hId1, hId2, hId3, _⟩ := spectral_identities_A_and_G hD' hH' hEq1' hw_ne hDw
  obtain ⟨hw_A, hquad_A, hw_pos_fn⟩ := quad_posDefPow_spec hA w
  obtain ⟨hw_G, hquad_G, _⟩ := quad_posDefPow_spec hG w
  have hw_pos : 0 < (star w ⬝ᵥ w).re := hw_pos_fn hw_ne
  let zA := (hA.isHermitian.eigenvectorUnitary : Mat n)ᴴ.mulVec w
  let lamA := hA.isHermitian.eigenvalues
  let zG := (hG.isHermitian.eigenvectorUnitary : Mat n)ᴴ.mulVec w
  let lamG := hG.isHermitian.eigenvalues
  have hboundZ : (2 - β) * (star w ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec w).re -
      (star w ⬝ᵥ (posDefPow (2 * κ) hA).mulVec w).re -
      α * (star w ⬝ᵥ (D' + H').mulVec w).re ≤ cZ * (star w ⬝ᵥ w).re := by
    have hA1 : (star w ⬝ᵥ (D' + H').mulVec w).re = ∑ i : Fin n, ‖zA i‖ ^ 2 * lamA i := by
      have h1 := hquad_A 1
      rw [posDefPow_one hA] at h1
      exact h1.trans (Finset.sum_congr rfl fun i _ => by rw [Real.rpow_one])
    rw [hquad_A (2 * κ - 1), hquad_A (2 * κ), hA1, hw_A,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpow2k : (lamA i) ^ (2 * κ) = (lamA i) ^ (2 * κ - 1) * lamA i := by
      calc (lamA i) ^ (2 * κ) = (lamA i) ^ ((2 * κ - 1) + 1) := by congr 1; ring
        _ = (lamA i) ^ (2 * κ - 1) * (lamA i) ^ (1 : ℝ) := Real.rpow_add (hA.eigenvalues_pos i) _ _
        _ = (lamA i) ^ (2 * κ - 1) * lamA i := by rw [Real.rpow_one]
    have hpt := hFZ (lamA i) (hA.eigenvalues_pos i)
    rw [hpow2k]; nlinarith [sq_nonneg ‖zA i‖]
  have hboundX : (β * Λ + γ) * (star w ⬝ᵥ (posDefPow (κ - 1) hG).mulVec w).re -
      γ * (star w ⬝ᵥ (posDefPow κ hG).mulVec w).re +
      α * (star w ⬝ᵥ (posDefPow (1 / 2 : ℝ) hD' * H' * posDefPow (1 / 2 : ℝ) hD').mulVec w).re ≤
      cX * (star w ⬝ᵥ w).re := by
    have hG1 : (star w ⬝ᵥ (posDefPow (1 / 2 : ℝ) hD' * H' * posDefPow (1 / 2 : ℝ) hD').mulVec w).re =
        ∑ i : Fin n, ‖zG i‖ ^ 2 * lamG i := by
      have h1 := hquad_G 1
      rw [posDefPow_one hG] at h1
      exact h1.trans (Finset.sum_congr rfl fun i _ => by rw [Real.rpow_one])
    rw [hquad_G (κ - 1), hquad_G κ, hG1, hw_G,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpt := hFX (lamG i) (hG.eigenvalues_pos i)
    nlinarith [sq_nonneg ‖zG i‖]
  have hPhi_re : (star w ⬝ᵥ (posDefPow κ hG - D' * posDefPow (κ - 1) hG * D').mulVec w).re =
      -P * (star w ⬝ᵥ w).re := by
    rw [hPhi_w, dotProduct_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hPhi_diff : (star w ⬝ᵥ (posDefPow (κ - 1) hG).mulVec w).re -
      (star w ⬝ᵥ (posDefPow κ hG).mulVec w).re = P * (star w ⬝ᵥ w).re := by
    have hDk : (star w ⬝ᵥ (D' * posDefPow (κ - 1) hG * D').mulVec w).re =
        (star w ⬝ᵥ (posDefPow (κ - 1) hG).mulVec w).re := by
      have hst : star w ᵥ* D' = star w := by
        have h1 : star w ᵥ* D'ᴴ = star (D'.mulVec w) := (Matrix.star_mulVec D' w).symm
        rw [hD'.isHermitian.eq, hDw] at h1; exact h1
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDw,
        Matrix.dotProduct_mulVec, hst]
    have hsub : (star w ⬝ᵥ (posDefPow κ hG - D' * posDefPow (κ - 1) hG * D').mulVec w).re =
        (star w ⬝ᵥ (posDefPow κ hG).mulVec w).re - (star w ⬝ᵥ (posDefPow (κ - 1) hG).mulVec w).re := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, hDk]
    linarith
  -- Abstract scalar expectations to avoid any kernel unfolding!
  set eW : ℝ := (star w ⬝ᵥ w).re
  set eA1 : ℝ := (star w ⬝ᵥ (D' + H').mulVec w).re
  set eG1 : ℝ := (star w ⬝ᵥ (posDefPow (1 / 2 : ℝ) hD' * H' * posDefPow (1 / 2 : ℝ) hD').mulVec w).re
  set eAkm : ℝ := (star w ⬝ᵥ (posDefPow (2 * κ - 1) hA).mulVec w).re
  set eAk : ℝ := (star w ⬝ᵥ (posDefPow (2 * κ) hA).mulVec w).re
  set eGkm : ℝ := (star w ⬝ᵥ (posDefPow (κ - 1) hG).mulVec w).re
  set eGk : ℝ := (star w ⬝ᵥ (posDefPow κ hG).mulVec w).re
  have hsum_exact :
      ((2 - β) * eAkm - eAk - α * eA1) + ((β * Λ + γ) * eGkm - γ * eGk + α * eG1) =
      ((Λ + γ) * P - α) * eW := by
    have h1 : eA1 = eW + eG1 := hId1
    have h2 : eAkm = Λ * eGkm := hId2
    have h3 : eAk = Λ * (eGkm + eGk) := hId3
    have h4 : eGkm - eGk = P * eW := hPhi_diff
    rw [h1, h2, h3]; linear_combination (Λ + γ) * h4
  have hcomb : ((Λ + γ) * P - α) * eW ≤ (cZ + cX) * eW := by
    have hz : (2 - β) * eAkm - eAk - α * eA1 ≤ cZ * eW := hboundZ
    have hx : (β * Λ + γ) * eGkm - γ * eGk + α * eG1 ≤ cX * eW := hboundX
    linarith
  have hmain : (Λ + γ) * P - α ≤ cZ + cX := by nlinarith
  have hmonoP : (Λ + γ) * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) ≤ (Λ + γ) * P :=
    mul_le_mul_of_nonneg_left hP_ge (by linarith)
  exact ⟨h, hh_gt1, hscalar, by linarith⟩

theorem two_function_regime1_bound {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {κ Λ B γ : ℝ}
    (hκ1 : 1 < κ) (hκ2 : κ < 2) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ)
    (hB : 2 < B) (hγ : 0 < γ)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0)
    (hcond : γ + (κ - 1) * (2 - κ) ^ ((2 - κ) / (κ - 1)) *
        (((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1)) ^ (1 / (κ - 1)) *
        γ ^ (-(2 - κ) / (κ - 1)) ≤ (B - 2) * Λ) :
    ∃ h : ℝ, 1 < h ∧ (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      (Λ + γ) * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) ≤
        ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1) := by
  set α : ℝ := ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1)
  have hα_pos : 0 < α := by
    have h1 : 0 < 2 * κ - 2 := by linarith
    have h2 : 0 < 2 * κ - 1 := by linarith
    have h3 : 0 < B := by linarith
    exact mul_pos (div_pos (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos h2 _))
      (Real.rpow_pos_of_pos h3 _)
  obtain ⟨h, hh, hsc, hbd⟩ := universal_two_function_bound hn hm hκ1 hΛ hD hH hEq1 hEq2
    (α := α) (β := 2 - B) (γ := γ) (cZ := 0) (cX := 0) hγ.le
    (fun z hz => by
      have h1 := rpow_FZ_le_zero hκ1 (by linarith : 0 < B) hz
      have h2 : 2 - (2 - B) - z = B - z := by ring
      rw [h2]; dsimp [α]; linarith)
    (fun x hx => by
      have h1 := rpow_FX_regime1_le hκ1 hκ2 hα_pos hγ hx
      have hxk_nn : 0 ≤ x ^ (κ - 1) := Real.rpow_nonneg hx.le _
      have h2 : ((2 - B) * Λ + γ) + (κ - 1) * (2 - κ) ^ ((2 - κ) / (κ - 1)) *
          α ^ (1 / (κ - 1)) * γ ^ (-(2 - κ) / (κ - 1)) ≤ 0 := by linarith
      have h3 := mul_nonpos_of_nonpos_of_nonneg h2 hxk_nn
      linarith)
  exact ⟨h, hh, hsc, by linarith⟩

theorem two_function_regime2_bound {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {κ Λ B : ℝ}
    (hκ2 : 2 < κ) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ) (hB : 2 < B)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0) :
    let α : ℝ := ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1)
    ∃ h : ℝ, 1 < h ∧ (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      Λ * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) ≤
        α + ((κ - 2) / (κ - 1)) * (α ^ (κ - 1) / ((κ - 1) * ((B - 2) * Λ))) ^ (1 / (κ - 2)) := by
  intro α
  have hκ1 : 1 < κ := by linarith
  have hΛ_pos : 0 < Λ := lt_trans (Real.rpow_pos_of_pos zero_lt_two _) hΛ
  have hα_pos : 0 < α := by
    have h1 : 0 < 2 * κ - 2 := by linarith
    have h2 : 0 < 2 * κ - 1 := by linarith
    have h3 : 0 < B := by linarith
    exact mul_pos (div_pos (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos h2 _))
      (Real.rpow_pos_of_pos h3 _)
  have hM_pos : 0 < (B - 2) * Λ := mul_pos (by linarith) hΛ_pos
  set cX : ℝ := ((κ - 2) / (κ - 1)) * (α ^ (κ - 1) / ((κ - 1) * ((B - 2) * Λ))) ^ (1 / (κ - 2))
  obtain ⟨h, hh, hsc, hbd⟩ := universal_two_function_bound hn hm hκ1 hΛ hD hH hEq1 hEq2
    (α := α) (β := 2 - B) (γ := 0) (cZ := 0) (cX := cX) le_rfl
    (fun z hz => by
      have h1 := rpow_FZ_le_zero hκ1 (by linarith : 0 < B) hz
      have h2 : 2 - (2 - B) - z = B - z := by ring
      rw [h2]; dsimp [α]; linarith)
    (fun x hx => by
      have h1 := rpow_FX_regime2_le hκ2 hα_pos hM_pos hx
      have h2 : ((2 - B) * Λ + 0) * x ^ (κ - 1) - 0 * x ^ κ + α * x =
          α * x - ((B - 2) * Λ) * x ^ (κ - 1) := by ring
      rw [h2]; exact h1)
  exact ⟨h, hh, hsc, by linarith⟩

theorem superexponential_p2_collapse_bound {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) {κ Λ γ : ℝ}
    (hκ1 : 1 < κ) (hκ32 : κ < 3 / 2) (hΛ : (2 : ℝ) ^ (2 * κ - 1) < Λ) (hγ : 0 < γ)
    {D : Mat n} (hD : D.PosDef) {H : Fin m → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * κ - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin m,
      (posDefPow κ (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow (κ - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0)
    (hcond : γ + (κ - 1) * (2 - κ) ^ ((2 - κ) / (κ - 1)) *
        (1 / (2 * κ - 2)) ^ (1 / (κ - 1)) * γ ^ (-(2 - κ) / (κ - 1)) ≤
        ((3 - 2 * κ) / (2 * κ - 2)) * Λ) :
    ∃ h : ℝ, 1 < h ∧ (1 + h) ^ (2 * κ - 1) = Λ * h ^ (κ - 1) ∧
      (Λ + γ) * (h ^ (κ - 1) * (h - 1) / ((m : ℝ) - 1)) ≤ 1 / (2 * κ - 2) := by
  have hκ2 : κ < 2 := by linarith
  have h2km2 : 0 < 2 * κ - 2 := by linarith
  have h2km1 : 0 < 2 * κ - 1 := by linarith
  set B : ℝ := (2 * κ - 1) / (2 * κ - 2)
  have hB_gt2 : 2 < B := by dsimp [B]; rw [lt_div_iff₀ h2km2]; linarith
  have hBsub2 : B - 2 = (3 - 2 * κ) / (2 * κ - 2) := by
    dsimp [B]
    rw [eq_div_iff h2km2.ne', sub_mul, div_mul_cancel₀ _ h2km2.ne']; ring
  have hα_simp : ((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1) =
      1 / (2 * κ - 2) := by
    dsimp [B]
    rw [Real.div_rpow h2km1.le h2km2.le]
    have hsplit : (2 * κ - 2) ^ (2 * κ - 1) = (2 * κ - 2) ^ (2 * κ - 2) * (2 * κ - 2) := by
      calc (2 * κ - 2) ^ (2 * κ - 1) = (2 * κ - 2) ^ ((2 * κ - 2) + 1) := by congr 1; ring
        _ = (2 * κ - 2) ^ (2 * κ - 2) * (2 * κ - 2) ^ (1 : ℝ) := Real.rpow_add h2km2 _ _
        _ = (2 * κ - 2) ^ (2 * κ - 2) * (2 * κ - 2) := by rw [Real.rpow_one]
    rw [hsplit]
    have hne1 : (2 * κ - 1) ^ (2 * κ - 1) ≠ 0 := (Real.rpow_pos_of_pos h2km1 _).ne'
    have hne2 : (2 * κ - 2) ^ (2 * κ - 2) ≠ 0 := (Real.rpow_pos_of_pos h2km2 _).ne'
    rw [div_mul_div_comm, eq_div_iff h2km2.ne', div_mul_eq_mul_div,
      div_eq_iff (mul_ne_zero hne1 (mul_ne_zero hne2 h2km2.ne'))]
    ring
  have hcond' : γ + (κ - 1) * (2 - κ) ^ ((2 - κ) / (κ - 1)) *
      (((2 * κ - 2) ^ (2 * κ - 2) / (2 * κ - 1) ^ (2 * κ - 1)) * B ^ (2 * κ - 1)) ^ (1 / (κ - 1)) *
      γ ^ (-(2 - κ) / (κ - 1)) ≤ (B - 2) * Λ := by
    rw [hα_simp, hBsub2]; exact hcond
  obtain ⟨h, hh, hsc, hbd⟩ :=
    two_function_regime1_bound hn hm hκ1 hκ2 hΛ hB_gt2 hγ hD hH hEq1 hEq2 hcond'
  rw [hα_simp] at hbd
  exact ⟨h, hh, hsc, hbd⟩

theorem two_function_cap_p32_m2 {n : ℕ} (hn : 1 ≤ n) {Λ : ℝ}
    (hΛ : (2 : ℝ) ^ (2 * (3 / 2 : ℝ) - 1) < Λ)
    {D : Mat n} (hD : D.PosDef) {H : Fin 2 → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * (3 / 2 : ℝ) - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow ((3 / 2 : ℝ) - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin 2,
      (posDefPow (3 / 2 : ℝ) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow ((3 / 2 : ℝ) - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0) :
    Λ < 447 / 100 := by
  by_contra hge; push Not at hge
  set B : ℝ := 61 / 25
  set α : ℝ := B ^ 2 / 4
  set γ : ℝ := 8 / 5
  have hFZ : ∀ z : ℝ, 0 < z → z ^ (2 * (3 / 2 : ℝ) - 1) * (2 - (2 - B) - z) - α * z ≤ 0 := by
    intro z hz
    have h2 : (2 * (3 / 2 : ℝ) - 1) = (2 : ℕ) := by norm_num
    rw [h2, Real.rpow_natCast]
    have hid : z ^ 2 * (2 - (2 - B) - z) - α * z = -z * (z - B / 2) ^ 2 := by dsimp [α]; ring
    rw [hid]
    nlinarith [sq_nonneg (z - B / 2)]
  have hFX : ∀ x : ℝ, 0 < x →
      ((2 - B) * Λ + γ) * x ^ ((3 / 2 : ℝ) - 1) - γ * x ^ (3 / 2 : ℝ) + α * x ≤ 0 := by
    intro x hx
    set u : ℝ := Real.sqrt x
    have hu : 0 < u := Real.sqrt_pos.mpr hx
    have hu2 : u ^ 2 = x := Real.sq_sqrt hx.le
    have hxh : x ^ ((3 / 2 : ℝ) - 1) = u := by
      have : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
      rw [this, ← Real.sqrt_eq_rpow]
    have hx32 : x ^ (3 / 2 : ℝ) = u ^ 3 := by
      calc x ^ (3 / 2 : ℝ) = x ^ ((1 : ℝ) + 1 / 2) := by norm_num
        _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := Real.rpow_add hx _ _
        _ = x * u := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
        _ = u ^ 3 := by rw [← hu2]; ring
    rw [hxh, hx32, ← hu2]
    have hquad_coef : (2 - B) * Λ + γ + α ^ 2 / (4 * γ) ≤ 0 := by
      dsimp [B, α, γ]; linarith
    have hid : ((2 - B) * Λ + γ) * u - γ * u ^ 3 + α * u ^ 2 =
        u * (-γ * (u - α / (2 * γ)) ^ 2 + ((2 - B) * Λ + γ + α ^ 2 / (4 * γ))) := by
      dsimp [γ]; ring
    rw [hid]
    have hneg : -γ * (u - α / (2 * γ)) ^ 2 + ((2 - B) * Λ + γ + α ^ 2 / (4 * γ)) ≤ 0 := by
      have : 0 ≤ γ * (u - α / (2 * γ)) ^ 2 := mul_nonneg (by dsimp [γ]; norm_num) (sq_nonneg _)
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hu.le hneg
  obtain ⟨h, hh, hsc, hbd⟩ := universal_two_function_bound hn (by norm_num : 2 ≤ 2)
    (by norm_num : (1 : ℝ) < 3 / 2) hΛ hD hH hEq1 hEq2 (by dsimp [γ]; norm_num : 0 ≤ γ) hFZ hFX
  have hsq : (1 + h) ^ (2 * (3 / 2 : ℝ) - 1) = (1 + h) ^ 2 := by
    have : 2 * (3 / 2 : ℝ) - 1 = (2 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]
  have hhr : h ^ ((3 / 2 : ℝ) - 1) = Real.sqrt h := by
    have : (3 / 2 : ℝ) - 1 = 1 / 2 := by norm_num
    rw [this, ← Real.sqrt_eq_rpow]
  rw [hsq, hhr] at hsc
  rw [hhr] at hbd
  have hsh_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr (by linarith)
  have hsh_sq : Real.sqrt h ^ 2 = h := Real.sq_sqrt (by linarith)
  have hh_gt2 : 1223 / 1000 < h := by
    by_contra hle; push Not at hle
    have h4eq : Λ ^ 2 * h = (1 + h) ^ 4 := by
      have h1 : (Λ * Real.sqrt h) ^ 2 = ((1 + h) ^ 2) ^ 2 := by rw [← hsc]
      rw [mul_pow, hsh_sq] at h1; linarith
    have hmono : (1 + h) ^ 4 * (1223 / 1000 : ℝ) ≤ (1 + 1223 / 1000 : ℝ) ^ 4 * h := by
      set b : ℝ := 1223 / 1000
      have hfac : (1 + b) ^ 4 * h - (1 + h) ^ 4 * b =
          (b - h) * (b * h * (b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6) - 1) := by ring
      have hb_nn : 0 ≤ b - h := sub_nonneg.mpr hle
      have hbh : 1 < b * h := by dsimp [b]; nlinarith
      have hbig : 6 < b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6 := by dsimp [b]; nlinarith
      have hpos : 0 < b * h * (b ^ 2 + b * h + h ^ 2 + 4 * b + 4 * h + 6) - 1 := by nlinarith
      have hprod := mul_nonneg hb_nn hpos.le
      linarith
    have hnum : (1 + (1223 / 1000 : ℝ)) ^ 4 < (447 / 100 : ℝ) ^ 2 * (1223 / 1000 : ℝ) := by norm_num
    have hΛsq : (447 / 100 : ℝ) ^ 2 ≤ Λ ^ 2 := by nlinarith
    have hfin : (447 / 100 : ℝ) ^ 2 * h * (1223 / 1000 : ℝ) ≤ (1 + 1223 / 1000 : ℝ) ^ 4 * h := by nlinarith
    nlinarith
  have hsh_gt2 : 1105 / 1000 < Real.sqrt h := by nlinarith [hsh_sq]
  have hdiv1 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hdiv1, div_one] at hbd
  have hcontra : α < (Λ + γ) * (Real.sqrt h * (h - 1)) := by
    dsimp [B, α, γ]
    have h1 : (1105 / 1000 : ℝ) * (1223 / 1000 - 1) < Real.sqrt h * (h - 1) := by nlinarith
    nlinarith
  linarith

theorem two_function_cap_p43_m2 {n : ℕ} (hn : 1 ≤ n) {Λ : ℝ}
    (hΛ : (2 : ℝ) ^ (2 * (2 : ℝ) - 1) < Λ)
    {D : Mat n} (hD : D.PosDef) {H : Fin 2 → Mat n} (hH : ∀ j, (H j).PosDef)
    (hEq1 : ∀ j, posDefPow (2 * (2 : ℝ) - 1) (hD.add (hH j)) =
      (Λ : ℂ) • (posDefPow (1 / 2 : ℝ) hD *
        posDefPow ((2 : ℝ) - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) *
        posDefPow (1 / 2 : ℝ) hD))
    (hEq2 : ∑ j : Fin 2,
      (posDefPow (2 : ℝ) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) -
       D * posDefPow ((2 : ℝ) - 1) (posDef_conj_of_posDef (posDefPow_posDef (1 / 2) hD) (hH j)) * D) = 0) :
    Λ < 866 / 100 := by
  by_contra hge; push Not at hge
  set B : ℝ := 109 / 50
  set α : ℝ := (4 / 27 : ℝ) * B ^ 3
  have hFZ : ∀ z : ℝ, 0 < z → z ^ (2 * (2 : ℝ) - 1) * (2 - (2 - B) - z) - α * z ≤ 0 := by
    intro z hz
    have h3 : (2 * (2 : ℝ) - 1) = (3 : ℕ) := by norm_num
    rw [h3, Real.rpow_natCast]
    have hid : z ^ 3 * (2 - (2 - B) - z) - α * z =
        -z * (z - 2 * B / 3) ^ 2 * (z + B / 3) := by dsimp [α]; ring
    rw [hid]
    have hpos : 0 ≤ z * (z - 2 * B / 3) ^ 2 * (z + B / 3) := by
      have : 0 < B := by dsimp [B]; norm_num
      positivity
    linarith
  have hFX : ∀ x : ℝ, 0 < x →
      ((2 - B) * Λ + 0) * x ^ ((2 : ℝ) - 1) - 0 * x ^ (2 : ℝ) + α * x ≤ 0 := by
    intro x hx
    have h1 : ((2 : ℝ) - 1) = 1 := by norm_num
    rw [h1, Real.rpow_one]
    have hcoef : (2 - B) * Λ + α ≤ 0 := by dsimp [B, α]; linarith
    nlinarith
  obtain ⟨h, hh, hsc, hbd⟩ := universal_two_function_bound hn (by norm_num : 2 ≤ 2)
    (by norm_num : (1 : ℝ) < 2) hΛ hD hH hEq1 hEq2 le_rfl hFZ hFX
  have h3 : (2 * (2 : ℝ) - 1) = (3 : ℕ) := by norm_num
  have h1 : ((2 : ℝ) - 1) = 1 := by norm_num
  rw [h3, Real.rpow_natCast, h1, Real.rpow_one] at hsc
  rw [h1, Real.rpow_one] at hbd
  have hh_gt : 11538 / 10000 < h := by
    by_contra hle; push Not at hle
    have hmono : (1 + h) ^ 3 * (11538 / 10000 : ℝ) ≤ (1 + 11538 / 10000 : ℝ) ^ 3 * h := by
      set b : ℝ := 11538 / 10000
      have hfac : (1 + b) ^ 3 * h - (1 + h) ^ 3 * b = (b - h) * (h * b * (b + h + 3) - 1) := by ring
      have hb_nn : 0 ≤ b - h := sub_nonneg.mpr hle
      have hhb : 1 < h * b := by dsimp [b]; nlinarith
      have hbig : 3 < b + h + 3 := by dsimp [b]; nlinarith
      have hpos : 0 < h * b * (b + h + 3) - 1 := by nlinarith
      have hprod := mul_nonneg hb_nn hpos.le
      linarith
    have hnum : (1 + (11538 / 10000 : ℝ)) ^ 3 < (866 / 100 : ℝ) * (11538 / 10000 : ℝ) := by norm_num
    have hfin : (866 / 100 : ℝ) * h * (11538 / 10000 : ℝ) ≤ (1 + 11538 / 10000 : ℝ) ^ 3 * h := by nlinarith
    nlinarith
  have hdiv1 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
  rw [hdiv1, div_one, add_zero] at hbd
  have hcontra : α < Λ * (h * (h - 1)) := by
    dsimp [B, α]
    have h1 : (11538 / 10000 : ℝ) * (11538 / 10000 - 1) < h * (h - 1) := by nlinarith
    nlinarith
  linarith

/-! ==========================================================================
    PART 6: Theorem 10C — Exact 2-Line Pure-Algebraic Bessel Bound at p = 4/3
    ========================================================================== -/

theorem bessel_two_line_identity_p43 {n : ℕ} {Λ P : ℝ} {D H : Mat n}
    (hD : D.PosDef) (hH : H.PosDef)
    (hEq : (D + H) * (D + H) * (D + H) = (Λ : ℂ) • (D * H * D))
    {v : Fin n → ℂ} (hv_unit : (star v ⬝ᵥ v).re = 1) (hDv : D.mulVec v = v)
    (hPhi : (H * D * H - D * H * D).mulVec v = ((-P : ℝ) : ℂ) • v) :
    let u := H.mulVec v
    let a := (star v ⬝ᵥ u).re
    let s2 := (star u ⬝ᵥ u).re
    0 < a ∧ a ^ 2 ≤ s2 ∧
    (star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u).re = 1 + 2 * a + s2 - Λ * P ∧
    s2 ^ 2 ≤ a * ((Λ - 4) * a - 2 * s2 - 1 + P) ∧
    ((Λ - 3) * a - a ^ 2 - 1 - (2 + a) * s2) ^ 2 ≤
      (s2 - a ^ 2) * (1 + 2 * a + s2 - Λ * P - (a + s2) ^ 2) := by
  intro u a s2
  have hv_ne : v ≠ 0 := by intro h0; rw [h0, dotProduct_zero, Complex.zero_re] at hv_unit; norm_num at hv_unit
  have hv_c : star v ⬝ᵥ v = 1 := Complex.ext hv_unit (by simpa using dotProduct_star_self_im v)
  have hstar_D : star v ᵥ* D = star v := by
    have h1 : star v ᵥ* Dᴴ = star (D.mulVec v) := (Matrix.star_mulVec D v).symm
    rw [hD.isHermitian.eq, hDv] at h1; exact h1
  have hstar_H : star v ᵥ* H = star u := by
    have h1 : star v ᵥ* Hᴴ = star (H.mulVec v) := (Matrix.star_mulVec H v).symm
    rw [hH.isHermitian.eq] at h1; exact h1
  have hstar_DH : star v ᵥ* (D + H) = star v + star u := by
    rw [Matrix.vecMul_add, hstar_D, hstar_H]
  have ha_pos : 0 < a := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 hv_ne)).1
  have ha_c : star v ⬝ᵥ u = (a : ℂ) :=
    Complex.ext rfl (by simpa using herm_dotProduct_mulVec_im hH.isHermitian v)
  have huv_c : star u ⬝ᵥ v = (a : ℂ) := by
    rw [dotProduct_star_comm u v, ha_c, Complex.conj_ofReal]
  have hs2_c : star u ⬝ᵥ u = (s2 : ℂ) := Complex.ext rfl (by simpa using dotProduct_star_self_im u)
  -- Helper for expanding star (x - (c : ℂ) • y)
  have hstar_sub_smul : ∀ (x y : Fin n → ℂ) (c : ℝ),
      star (x - (c : ℂ) • y) = star x - (c : ℂ) • star y := by
    intro x y c; ext i; simp
  have huDu : (star u ⬝ᵥ D.mulVec u).re = a - P := by
    have h1 : star v ⬝ᵥ (H * D * H - D * H * D).mulVec v = ((-P : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
      rw [hPhi, dotProduct_smul, smul_eq_mul]
    rw [hv_c, mul_one, Matrix.sub_mulVec, dotProduct_sub] at h1
    have hterm1 : star v ⬝ᵥ (H * D * H).mulVec v = star u ⬝ᵥ D.mulVec u := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, hstar_H]
    have hterm2 : star v ⬝ᵥ (D * H * D).mulVec v = star v ⬝ᵥ u := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDv,
        Matrix.dotProduct_mulVec, hstar_D]
    rw [hterm1, hterm2] at h1
    have hre := congrArg Complex.re h1
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    linarith
  set s3 : ℝ := (star u ⬝ᵥ H.mulVec u).re
  have hEQ1 : s3 = (Λ - 4) * a - 2 * s2 - 1 + P := by
    have h1 : star v ⬝ᵥ ((D + H) * (D + H) * (D + H)).mulVec v =
        (Λ : ℂ) * (star v ⬝ᵥ (D * H * D).mulVec v) := by
      rw [hEq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hR : star v ⬝ᵥ (D * H * D).mulVec v = star v ⬝ᵥ u := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDv,
        Matrix.dotProduct_mulVec, hstar_D]
    have hL : star v ⬝ᵥ ((D + H) * (D + H) * (D + H)).mulVec v =
        star v ⬝ᵥ v + (3 : ℂ) * (star v ⬝ᵥ u) + (2 : ℂ) * (star u ⬝ᵥ u) +
        star u ⬝ᵥ D.mulVec u + star u ⬝ᵥ H.mulVec u := by
      have hDHv : (D + H).mulVec v = v + u := by rw [Matrix.add_mulVec, hDv]
      calc star v ⬝ᵥ ((D + H) * (D + H) * (D + H)).mulVec v
          = (star v ᵥ* (D + H)) ⬝ᵥ ((D + H).mulVec ((D + H).mulVec v)) := by
              rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                Matrix.dotProduct_mulVec]
        _ = (star v + star u) ⬝ᵥ ((D + H).mulVec (v + u)) := by rw [hstar_DH, hDHv]
        _ = (star v + star u) ⬝ᵥ (v + u + D.mulVec u + H.mulVec u) := by
              rw [Matrix.mulVec_add, hDHv, Matrix.add_mulVec]; congr 1; abel
        _ = star v ⬝ᵥ v + star v ⬝ᵥ u + star v ⬝ᵥ D.mulVec u + star v ⬝ᵥ H.mulVec u +
            (star u ⬝ᵥ v + star u ⬝ᵥ u + star u ⬝ᵥ D.mulVec u + star u ⬝ᵥ H.mulVec u) := by
              simp only [add_dotProduct, dotProduct_add]; abel
        _ = star v ⬝ᵥ v + (3 : ℂ) * (star v ⬝ᵥ u) + (2 : ℂ) * (star u ⬝ᵥ u) +
            star u ⬝ᵥ D.mulVec u + star u ⬝ᵥ H.mulVec u := by
              have hvDu : star v ⬝ᵥ D.mulVec u = star v ⬝ᵥ u := by rw [Matrix.dotProduct_mulVec, hstar_D]
              have hvHu : star v ⬝ᵥ H.mulVec u = star u ⬝ᵥ u := by rw [Matrix.dotProduct_mulVec, hstar_H]
              rw [hvDu, hvHu, huv_c, ha_c]; ring
    rw [hL, hR] at h1
    have hre := congrArg Complex.re h1
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero] at hre
    linarith [hv_unit, huDu]
  have hnorm_DHu : (star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u).re = 1 + 2 * a + s2 - Λ * P := by
    have h1 : star v ⬝ᵥ ((D + H) * (D + H) * (D + H)).mulVec u =
        (Λ : ℂ) * (star v ⬝ᵥ (D * H * D).mulVec u) := by
      rw [hEq, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hR : star v ⬝ᵥ (D * H * D).mulVec u = star u ⬝ᵥ D.mulVec u := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, hstar_D, Matrix.dotProduct_mulVec, hstar_H]
    have hL : star v ⬝ᵥ ((D + H) * (D + H) * (D + H)).mulVec u =
        star v ⬝ᵥ u + star u ⬝ᵥ u + star u ⬝ᵥ D.mulVec u + star u ⬝ᵥ H.mulVec u +
        star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u := by
      have hstar_DH_u : star u ᵥ* (D + H) = star ((D + H).mulVec u) := by
        have h1 := (Matrix.star_mulVec (D + H) u).symm
        rw [(hD.add hH).isHermitian.eq] at h1; exact h1
      calc star v ⬝ᵥ ((D + H) * (D + H) * (D + H)).mulVec u
          = (star v ᵥ* (D + H)) ⬝ᵥ ((D + H).mulVec ((D + H).mulVec u)) := by
              rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
                Matrix.dotProduct_mulVec]
        _ = (star v + star u) ⬝ᵥ ((D + H).mulVec ((D + H).mulVec u)) := by rw [hstar_DH]
        _ = (star v ᵥ* (D + H)) ⬝ᵥ (D + H).mulVec u + (star u ᵥ* (D + H)) ⬝ᵥ (D + H).mulVec u := by
              rw [add_dotProduct, Matrix.dotProduct_mulVec]; congr 1; exact Matrix.dotProduct_mulVec _ _ _
        _ = (star v + star u) ⬝ᵥ (D.mulVec u + H.mulVec u) +
            star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u := by
              rw [hstar_DH, hstar_DH_u, Matrix.add_mulVec]
        _ = star v ⬝ᵥ D.mulVec u + star v ⬝ᵥ H.mulVec u +
            star u ⬝ᵥ D.mulVec u + star u ⬝ᵥ H.mulVec u +
            star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u := by
              simp only [add_dotProduct, dotProduct_add]; abel
        _ = star v ⬝ᵥ u + star u ⬝ᵥ u + star u ⬝ᵥ D.mulVec u + star u ⬝ᵥ H.mulVec u +
            star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u := by
              have hvDu : star v ⬝ᵥ D.mulVec u = star v ⬝ᵥ u := by rw [Matrix.dotProduct_mulVec, hstar_D]
              have hvHu : star v ⬝ᵥ H.mulVec u = star u ⬝ᵥ u := by rw [Matrix.dotProduct_mulVec, hstar_H]
              rw [hvDu, hvHu]
    rw [hL, hR] at h1
    have hre := congrArg Complex.re h1
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    change a + s2 + (star u ⬝ᵥ D.mulVec u).re + s3 + (star ((D + H).mulVec u) ⬝ᵥ (D + H).mulVec u).re =
      Λ * (star u ⬝ᵥ D.mulVec u).re at hre
    rw [huDu, hEQ1] at hre
    linarith
  have hCS1 : a ^ 2 ≤ s2 := by
    let b : Fin n → ℂ := u - (a : ℂ) • v
    have hnn : 0 ≤ (star b ⬝ᵥ b).re := by
      rw [dotProduct, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg _
    have hexp : (star b ⬝ᵥ b).re = s2 - a ^ 2 := by
      change (star (u - (a : ℂ) • v) ⬝ᵥ (u - (a : ℂ) • v)).re = s2 - a ^ 2
      rw [hstar_sub_smul u v a, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ha_c, huv_c, hv_c, hs2_c]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_one]; ring
    linarith
  have hCS2 : s2 ^ 2 ≤ a * s3 := by
    let x : Fin n → ℂ := u - ((s2 / a : ℝ) : ℂ) • v
    have hnn : 0 ≤ (star x ⬝ᵥ H.mulVec x).re := by
      by_cases hx0 : x = 0
      · rw [hx0, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re]
      · exact ((Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp hH).2 hx0)).1).le
    have hexp : (star x ⬝ᵥ H.mulVec x).re = s3 - s2 ^ 2 / a := by
      change (star (u - ((s2 / a : ℝ) : ℂ) • v) ⬝ᵥ H.mulVec (u - ((s2 / a : ℝ) : ℂ) • v)).re = s3 - s2 ^ 2 / a
      rw [hstar_sub_smul u v (s2 / a), Matrix.mulVec_sub, Matrix.mulVec_smul,
        sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      have huHv : star u ⬝ᵥ H.mulVec v = (s2 : ℂ) := hs2_c
      have hvHu : star v ⬝ᵥ H.mulVec u = (s2 : ℂ) := by rw [Matrix.dotProduct_mulVec, hstar_H, hs2_c]
      rw [huHv, hvHu, ha_c]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      field_simp [ha_pos.ne']; ring
    have hle : s2 ^ 2 / a ≤ s3 := by linarith
    have hmul := (div_le_iff₀ ha_pos).mp hle
    linarith
  have hBessel : ((Λ - 3) * a - a ^ 2 - 1 - (2 + a) * s2) ^ 2 ≤
      (s2 - a ^ 2) * (1 + 2 * a + s2 - Λ * P - (a + s2) ^ 2) := by
    let y : Fin n → ℂ := (D + H).mulVec u
    let b : Fin n → ℂ := u - (a : ℂ) • v
    have hvy : star v ⬝ᵥ y = ((a + s2 : ℝ) : ℂ) := by
      dsimp [y]
      rw [Matrix.add_mulVec, dotProduct_add]
      have h1 : star v ⬝ᵥ D.mulVec u = (a : ℂ) := by rw [Matrix.dotProduct_mulVec, hstar_D, ha_c]
      have h2 : star v ⬝ᵥ H.mulVec u = (s2 : ℂ) := by rw [Matrix.dotProduct_mulVec, hstar_H, hs2_c]
      rw [h1, h2]; push_cast; ring
    have hyv : star y ⬝ᵥ v = ((a + s2 : ℝ) : ℂ) := by
      rw [dotProduct_star_comm y v, hvy, Complex.conj_ofReal]
    have huy_re : (star u ⬝ᵥ y).re = a - P + s3 := by
      dsimp [y]; rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, huDu]
    have hby_re : (star b ⬝ᵥ y).re = (Λ - 3) * a - a ^ 2 - 1 - (2 + a) * s2 := by
      change (star (u - (a : ℂ) • v) ⬝ᵥ y).re = _
      rw [hstar_sub_smul u v a, sub_dotProduct, smul_dotProduct, smul_eq_mul, hvy, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
        zero_mul, sub_zero, huy_re, hEQ1]
      ring
    set cb : ℝ := (star b ⬝ᵥ y).re
    set d : ℝ := s2 - a ^ 2
    have hvb : star v ⬝ᵥ b = 0 := by
      change star v ⬝ᵥ (u - (a : ℂ) • v) = 0
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ha_c, hv_c, mul_one, sub_self]
    have hbv : star b ⬝ᵥ v = 0 := by
      rw [dotProduct_star_comm b v, hvb, map_zero]
    have hbb : (star b ⬝ᵥ b).re = d := by
      change (star (u - (a : ℂ) • v) ⬝ᵥ (u - (a : ℂ) • v)).re = d
      rw [hstar_sub_smul u v a, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ha_c, huv_c, hv_c, hs2_c]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_one]; dsimp [d]; ring
    let z1 : Fin n → ℂ := y - ((a + s2 : ℝ) : ℂ) • v
    have hz1z1 : (star z1 ⬝ᵥ z1).re = 1 + 2 * a + s2 - Λ * P - (a + s2) ^ 2 := by
      change (star (y - ((a + s2 : ℝ) : ℂ) • v) ⬝ᵥ (y - ((a + s2 : ℝ) : ℂ) • v)).re = _
      rw [hstar_sub_smul y v (a + s2), sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hvy, hyv, hv_c]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, mul_one]
      rw [hnorm_DHu]; ring
    have hbz1_re : (star b ⬝ᵥ z1).re = cb := by
      change (star b ⬝ᵥ (y - ((a + s2 : ℝ) : ℂ) • v)).re = cb
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hbv, mul_zero, sub_zero]
    have hz1b_re : (star z1 ⬝ᵥ b).re = cb := by
      have h1 := congrArg Complex.re (dotProduct_star_comm z1 b)
      rw [Complex.conj_re] at h1; rw [h1, hbz1_re]
    let w0 : Fin n → ℂ := ((d : ℝ) : ℂ) • z1 - ((cb : ℝ) : ℂ) • b
    have hnn : 0 ≤ (star w0 ⬝ᵥ w0).re := by
      rw [dotProduct, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg _
    have hw0_exp : (star w0 ⬝ᵥ w0).re = d * (d * (star z1 ⬝ᵥ z1).re - cb ^ 2) := by
      have hsw : star w0 = ((d : ℝ) : ℂ) • star z1 - ((cb : ℝ) : ℂ) • star b := by
        dsimp [w0]; ext i; simp
      change (star w0 ⬝ᵥ (((d : ℝ) : ℂ) • z1 - ((cb : ℝ) : ℂ) • b)).re = _
      rw [hsw, sub_dotProduct, dotProduct_sub, dotProduct_sub,
        smul_dotProduct, smul_dotProduct, smul_dotProduct, smul_dotProduct,
        dotProduct_smul, dotProduct_smul, dotProduct_smul, dotProduct_smul]
      simp only [smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [hbb, hbz1_re, hz1b_re]; ring
    rw [hw0_exp, hz1z1] at hnn
    have hgoal_cb : cb ^ 2 ≤ d * (1 + 2 * a + s2 - Λ * P - (a + s2) ^ 2) := by
      by_cases hd0 : d = 0
      · have hb0 : b = 0 := by
          by_contra hne
          have hpos : 0 < (star b ⬝ᵥ b).re := by
            rw [dotProduct, Complex.re_sum]
            obtain ⟨i0, hi0⟩ : ∃ i, b i ≠ 0 := by by_contra h; push Not at h; exact hne (funext h)
            refine Finset.sum_pos' (fun i _ => ?_) ⟨i0, Finset.mem_univ _, ?_⟩
            · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
              exact sq_nonneg _
            · simp only [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
              exact sq_pos_of_pos (norm_pos_iff.mpr hi0)
          linarith [hbb, hd0]
        have hcb0 : cb = 0 := by dsimp [cb]; rw [hb0, star_zero, zero_dotProduct, Complex.zero_re]
        rw [hcb0, hd0]; norm_num
      · have hd_pos : 0 < d := lt_of_le_of_ne (by dsimp [d]; linarith) (Ne.symm hd0)
        nlinarith
    rw [← hby_re]; exact hgoal_cb
  exact ⟨ha_pos, hCS1, hnorm_DHu, by rw [← hEQ1]; exact hCS2, hBessel⟩

end MI20
