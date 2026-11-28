/-
  MI20/Theorem5_PSDReduction.lean
  ===============================
  Authors: Marcio Díaz (Space Research AI, https://spaceresearch.ai)
  Complete Mathlib-grounded, zero-sorry Lean 4.33.1 formalization of:
    - Same-Dimension Lemma 2 (`lemma2_same_dim_full_rank_sum`):
      For 1 < p < 2, if S ≠ 0 and ker(S) ∩ ran(H) ≠ {0}, then a SAME-dimension
      left unitary/Householder/Givens rotation strictly increases ‖S‖_p while leaving H
      unchanged (closing the dimension-matching subtlety in Theorem 5's proof).
    - Theorem 5 (`theorem5_psd_reformulation`, `theorem5_povm_reformulation`):
      Exact PSD-splitting and POVM infimum characterizations of (C_{p,m}(n))^{-p} for all
      1 < p < 2, m ≥ 2, n ≥ 1.
-/

import MI20.Lemma4_And_Theorem1

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ==========================================================================
    PART 1: Strict Rank-One Increase for 0 < q < 1 (Householder Case)
    ========================================================================== -/

/-- For 0 < q < 1, any PSD matrix G0 and any nonzero vector r ≠ 0,
    schattenPow q G0 < schattenPow q (G0 + (4 : ℂ) • outerMat r r). -/
lemma schattenPow_lt_add_rankOne_lt_one {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {G0 : Mat n} (hG0 : G0.PosSemidef) {r : Fin n → ℂ} (hr : r ≠ 0) :
    schattenPow q G0 < schattenPow q (G0 + (4 : ℂ) • outerMat r r) := by
  let E : Mat n := (4 : ℂ) • outerMat r r
  have hE_psd : E.PosSemidef := by
    have : E = (4 : ℝ) • outerMat r r := by ext i j; simp [E, Complex.real_smul]
    rw [this]; exact (outerMat_posSemidef r).smul (by norm_num)
  let G1 : Mat n := G0 + E
  have hG1 : G1.PosSemidef := hG0.add hE_psd
  let U0 := hG0.isHermitian.eigenvectorUnitary
  let lam := hG0.isHermitian.eigenvalues
  let U1 := hG1.isHermitian.eigenvectorUnitary
  let mu := hG1.isHermitian.eigenvalues
  have hG0_eq : G0 = (U0 : Mat n) * Matrix.diagonal (fun j => (lam j : ℂ)) * (U0 : Mat n)ᴴ := by
    simpa [U0, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hG0.isHermitian.spectral_theorem
  have hG1_eq : G1 = (U1 : Mat n) * Matrix.diagonal (fun i => (mu i : ℂ)) * (U1 : Mat n)ᴴ := by
    simpa [U1, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hG1.isHermitian.spectral_theorem
  have hPow0 : schattenPow q G0 = ∑ j : Fin n, (lam j) ^ q := by
    rw [hG0_eq, schattenPow_unitary_mul_conjTranspose_right hq0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hq0 lam hG0.eigenvalues_nonneg]
  have hPow1 : schattenPow q G1 = ∑ i : Fin n, (mu i) ^ q := by
    rw [hG1_eq, schattenPow_unitary_mul_conjTranspose_right hq0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hq0 mu hG1.eigenvalues_nonneg]
  let Qu : Matrix.unitaryGroup (Fin n) ℂ := star U1 * U0
  let Q : Mat n := (Qu : Mat n)
  have hRowQ : ∀ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Qu) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun j _ => ?_
    change ‖Q i j‖ ^ 2 = (Q i j * star (Q i j)).re
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColQ : ∀ j : Fin n, ∑ i : Fin n, ‖Q i j‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Qu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]; refine Finset.sum_congr rfl fun i _ => ?_
    change ‖Q i j‖ ^ 2 = (star (Q i j) * Q i j).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  -- Define diagonal entries g i = (U1ᴴ G0 U1)_{ii} = ∑_j ‖Q i j‖^2 * lam j and ρ i = (U1ᴴ E U1)_{ii} ≥ 0
  let g : Fin n → ℝ := fun i => ∑ j : Fin n, ‖Q i j‖ ^ 2 * lam j
  let w : Fin n → ℂ := (U1 : Mat n)ᴴ.mulVec r
  let ρ : Fin n → ℝ := fun i => 4 * ‖w i‖ ^ 2
  have hg_nn : ∀ i, 0 ≤ g i := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hG0.eigenvalues_nonneg j)
  have hρ_nn : ∀ i, 0 ≤ ρ i := fun i => mul_nonneg (by norm_num) (sq_nonneg _)
  have hmu_eq : ∀ i : Fin n, mu i = g i + ρ i := by
    intro i
    have hdiag : (U1 : Mat n)ᴴ * G1 * (U1 : Mat n) = Matrix.diagonal (fun k => (mu k : ℂ)) := by
      rw [hG1_eq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U1 : Mat n)ᴴ (U1 : Mat n), unitary_conjTranspose_mul_self U1,
        Matrix.one_mul, Matrix.mul_one]
    have hii := congrArg Complex.re (congr_fun (congr_fun hdiag i) i)
    simp only [Matrix.diagonal_apply_eq, Complex.ofReal_re] at hii
    rw [← hii]
    have hsplit : (U1 : Mat n)ᴴ * G1 * (U1 : Mat n) =
        (U1 : Mat n)ᴴ * G0 * (U1 : Mat n) + (U1 : Mat n)ᴴ * E * (U1 : Mat n) := by
      dsimp [G1]; rw [Matrix.mul_add, Matrix.add_mul]
    rw [hsplit, Matrix.add_apply, Complex.add_re]
    congr 1
    · -- ((U1ᴴ G0 U1) i i).re = g i
      have hQ1 : (U1 : Mat n)ᴴ * G0 * (U1 : Mat n) = Q * Matrix.diagonal (fun j => (lam j : ℂ)) * Qᴴ := by
        rw [hG0_eq]
        have hQeq : (U1 : Mat n)ᴴ * (U0 : Mat n) = Q := rfl
        have hQHeq : (U0 : Mat n)ᴴ * (U1 : Mat n) = Qᴴ := by
          change (U0 : Mat n)ᴴ * (U1 : Mat n) = ((U1 : Mat n)ᴴ * (U0 : Mat n))ᴴ
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
        calc (U1 : Mat n)ᴴ * ((U0 : Mat n) * Matrix.diagonal (fun j => (lam j : ℂ)) * (U0 : Mat n)ᴴ) * (U1 : Mat n)
            = ((U1 : Mat n)ᴴ * (U0 : Mat n)) * Matrix.diagonal (fun j => (lam j : ℂ)) * ((U0 : Mat n)ᴴ * (U1 : Mat n)) := by
              simp only [Matrix.mul_assoc]
          _ = Q * Matrix.diagonal (fun j => (lam j : ℂ)) * Qᴴ := by rw [hQeq, hQHeq]
      rw [hQ1]
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Complex.re_sum,
        mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, g]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 : Q i j * (lam j : ℂ) * star (Q i j) = (lam j : ℂ) * (Q i j * star (Q i j)) := by ring
      rw [h1, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re]; ring
    · -- ((U1ᴴ E U1) i i).re = 4 * ‖w i‖^2
      have hE1 : (U1 : Mat n)ᴴ * E * (U1 : Mat n) = (4 : ℂ) • outerMat w w := by
        dsimp [E]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1; ext a b
        simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, w, Matrix.mulVec, dotProduct,
          Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
        calc ∑ k, (∑ l, (U1 : Mat n)ᴴ a l * (r l * star (r k))) * (U1 : Mat n) k b
            = ∑ k, (∑ l, (U1 : Mat n)ᴴ a l * r l) * (star (r k) * (U1 : Mat n) k b) := by
              refine Finset.sum_congr rfl fun k _ => by
                rw [Finset.sum_mul, Finset.sum_mul]
                refine Finset.sum_congr rfl fun l _ => by ring
          _ = (∑ l, (U1 : Mat n)ᴴ a l * r l) * ∑ k, star (r k) * (U1 : Mat n) k b :=
              (Finset.mul_sum ..).symm
          _ = (∑ l, star ((U1 : Mat n) l a) * r l) * ∑ k, (U1 : Mat n) k b * star (r k) := by
              congr 1
              exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hE1]
      simp only [Matrix.smul_apply, outerMat, Matrix.of_apply, smul_eq_mul, Complex.star_def,
        Complex.mul_conj', ← Complex.ofReal_pow]
      have h4 : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
      rw [h4, ← Complex.ofReal_mul, Complex.ofReal_re]
  -- Show ∃ i0 with ρ i0 > 0 (since ∑ ρ i = 4 ‖r‖^2 > 0)
  have hex_pos : ∃ i0 : Fin n, 0 < ρ i0 := by
    have hw_ne : w ≠ 0 := by
      intro h0
      have h1 := congrArg (Matrix.mulVec (U1 : Mat n)) h0
      simp only [w, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U1, Matrix.one_mulVec,
        Matrix.mulVec_zero] at h1
      exact hr h1
    have hex : ∃ i0 : Fin n, w i0 ≠ 0 := by
      by_contra hall; push Not at hall; exact hw_ne (funext hall)
    obtain ⟨i0, hi0⟩ := hex
    exact ⟨i0, mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hi0))⟩
  -- Pointwise Jensen for x ↦ x^q (0 < q < 1): ∑_j ‖Q i j‖^2 * lam j^q ≤ g i ^ q!
  have hjensen : ∀ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (lam j) ^ q ≤ (g i) ^ q := by
    intro i
    by_cases hg0 : g i = 0
    · have hterm0 : ∀ j : Fin n, ‖Q i j‖ ^ 2 * (lam j) ^ q = 0 := fun j => by
        have hj0 : ‖Q i j‖ ^ 2 * lam j = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (sq_nonneg _) (hG0.eigenvalues_nonneg k)).mp hg0 j (Finset.mem_univ j)
        rcases mul_eq_zero.mp hj0 with hq | hl
        · rw [hq, zero_mul]
        · rw [hl, Real.zero_rpow hq0.ne', mul_zero]
      rw [Finset.sum_eq_zero fun j _ => hterm0 j, hg0, Real.zero_rpow hq0.ne']
    · have hg_pos : 0 < g i := lt_of_le_of_ne (hg_nn i) (Ne.symm hg0)
      have hq1_pos : 0 < 1 - q := by linarith
      calc ∑ j : Fin n, ‖Q i j‖ ^ 2 * (lam j) ^ q
          = (g i) ^ q * ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((lam j / g i) ^ q) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
            rw [Real.div_rpow (hG0.eigenvalues_nonneg j) hg_pos.le q]
            have hne : (g i) ^ q ≠ 0 := (Real.rpow_pos_of_pos hg_pos q).ne'
            dsimp only [lam]; field_simp [hne]
        _ ≤ (g i) ^ q * ∑ j : Fin n, ‖Q i j‖ ^ 2 * (q * (lam j / g i) + (1 - q) * 1) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) (Real.rpow_nonneg hg_pos.le _)
            have hy := Real.geom_mean_le_arith_mean2_weighted hq0.le hq1_pos.le
              (div_nonneg (hG0.eigenvalues_nonneg j) hg_pos.le) zero_le_one (by ring)
            simpa [Real.one_rpow] using hy
        _ = (g i) ^ q * (q * (g i / g i) + (1 - q) * 1) := by
            congr 1
            have h1 : ∑ j : Fin n, ‖Q i j‖ ^ 2 * (q * (lam j / g i) + (1 - q) * 1) =
                q * ((∑ j : Fin n, ‖Q i j‖ ^ 2 * lam j) / g i) + (1 - q) * (∑ j : Fin n, ‖Q i j‖ ^ 2) := by
              rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun j _ => by ring
            rw [h1, hRowQ i]
        _ = (g i) ^ q := by rw [div_self hg_pos.ne']; ring
  -- Combine with strict increase at i0!
  obtain ⟨i0, hi0_pos⟩ := hex_pos
  rw [hPow0, hPow1]
  have hsum_le : ∑ j : Fin n, (lam j) ^ q ≤ ∑ i : Fin n, (g i) ^ q := by
    calc ∑ j : Fin n, (lam j) ^ q
        = ∑ j : Fin n, (∑ i : Fin n, ‖Q i j‖ ^ 2) * (lam j) ^ q := by
          refine Finset.sum_congr rfl fun j _ => by rw [hColQ j, one_mul]
      _ = ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (lam j) ^ q := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ ≤ ∑ i : Fin n, (g i) ^ q := Finset.sum_le_sum fun i _ => hjensen i
  have hsum_lt : ∑ i : Fin n, (g i) ^ q < ∑ i : Fin n, (mu i) ^ q := by
    refine Finset.sum_lt_sum ?_ ⟨i0, Finset.mem_univ i0, ?_⟩
    · intro i _
      rw [hmu_eq i]
      exact Real.rpow_le_rpow (hg_nn i) (by linarith [hρ_nn i]) hq0.le
    · rw [hmu_eq i0]
      exact Real.rpow_lt_rpow (hg_nn i0) (by linarith) hq0
  linarith

/-! ==========================================================================
    PART 2: Same-Dimension Lemma 2 (Closes Theorem 5's Proof Gap!)
    ========================================================================== -/

set_option maxHeartbeats 600000 in
/-- Same-Dimension Lemma 2: For 1 < p < 2, if S = ∑ A_j ≠ 0 and there exists a nonzero
    z ∈ ran(H) with S *ᵥ z = 0, then there exists a SAME-dimension tuple A' : Fin m → Mat n
    with identical modulus sum ∑ |A'_j| = H and strictly larger Lee ratio leeRatio p A < leeRatio p A'! -/
theorem lemma2_same_dim_full_rank_sum {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (A : Fin m → Mat n)
    (hS_ne : (∑ j, A j) ≠ 0)
    (hH_ne : (∑ j, matAbs (A j)) ≠ 0)
    (z : Fin n → ℂ) (hz_ne : z ≠ 0)
    (hz_ran : z ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))))
    (hz_ker : (∑ j, A j).mulVec z = 0) :
    ∃ A' : Fin m → Mat n, (∑ j, matAbs (A' j)) = (∑ j, matAbs (A j)) ∧
      leeRatio p A < leeRatio p A' := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  set S : Mat n := ∑ j, A j
  set H : Mat n := ∑ j, matAbs (A j)
  have hH_psd : H.PosSemidef := by
    have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
      intro s; induction s using Finset.induction_on with
      | empty => simpa using Matrix.PosSemidef.zero
      | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
    exact this Finset.univ
  have hH_norm_pos : 0 < schattenNorm p H := schattenNorm_pos_of_ne_zero hp0 hH_ne
  -- Step 1: Since z ∈ ran(H) \ {0}, ∃ k0 with A k0 *ᵥ z ≠ 0
  have hzH_pos : 0 < (star z ⬝ᵥ H.mulVec z).re := by
    have hge : 0 ≤ (star z ⬝ᵥ H.mulVec z).re := by
      simpa [RCLike.re_to_complex] using hH_psd.re_dotProduct_nonneg z
    refine lt_of_le_of_ne hge (Ne.symm fun h0 => ?_)
    have hHz0 := posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero hH_psd z h0
    obtain ⟨y, hy⟩ := hz_ran
    change H.mulVec y = z at hy
    have hzz : star z ⬝ᵥ z = 0 := by
      calc star z ⬝ᵥ z = star (H.mulVec y) ⬝ᵥ z := by rw [hy]
        _ = star y ⬝ᵥ H.mulVec z := by rw [Matrix.star_mulVec, hH_psd.isHermitian.eq, ← Matrix.dotProduct_mulVec]
        _ = 0 := by rw [hHz0, dotProduct_zero]
    have hE : ‖WithLp.toLp 2 z‖ ^ 2 = 0 := by
      have h1 : star z ⬝ᵥ z = inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 z) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hzz
      exact (RCLike.ofReal_eq_zero (K := ℂ)).mp hzz
    exact hz_ne (congrArg WithLp.ofLp (norm_eq_zero.mp (sq_eq_zero_iff.mp hE)))
  have hex_k0 : ∃ k0 : Fin m, (A k0).mulVec z ≠ 0 := by
    by_contra hall; push Not at hall
    have h0 : (star z ⬝ᵥ H.mulVec z).re = 0 := by
      simp only [H, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hPj0 : (matAbs (A j)).mulVec z = 0 := by
        have h1 : (star ((matAbs (A j)).mulVec z) ⬝ᵥ (matAbs (A j)).mulVec z).re = 0 := by
          have h2 : star ((matAbs (A j)).mulVec z) ⬝ᵥ (matAbs (A j)).mulVec z =
              star z ⬝ᵥ ((A j)ᴴ * A j).mulVec z := by
            rw [Matrix.star_mulVec, (matAbs_posSemidef (A j)).isHermitian.eq,
              ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, matAbs_mul_self]
          rw [h2, ← Matrix.mulVec_mulVec, hall j, Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re]
        have hE : ‖WithLp.toLp 2 ((matAbs (A j)).mulVec z)‖ ^ 2 = 0 := by
          have h2 : star ((matAbs (A j)).mulVec z) ⬝ᵥ (matAbs (A j)).mulVec z =
              inner ℂ (WithLp.toLp 2 ((matAbs (A j)).mulVec z)) (WithLp.toLp 2 ((matAbs (A j)).mulVec z)) := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
          rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h1
          have h3 : (RCLike.ofReal (K := ℂ) (‖WithLp.toLp 2 ((matAbs (A j)).mulVec z)‖ ^ 2)).re =
              ‖WithLp.toLp 2 ((matAbs (A j)).mulVec z)‖ ^ 2 := by
            change ((‖WithLp.toLp 2 ((matAbs (A j)).mulVec z)‖ ^ 2 : ℝ) : ℂ).re = _
            exact Complex.ofReal_re _
          linarith
        exact congrArg WithLp.ofLp (norm_eq_zero.mp (sq_eq_zero_iff.mp hE))
      rw [hPj0, dotProduct_zero, Complex.zero_re]
    linarith
  obtain ⟨k0, hk0_ne⟩ := hex_k0
  -- Step 2: Since z ∈ ker(S) \ {0}, finrank(ker(Sᴴ)) = finrank(ker(S)) ≥ 1, so ∃ unit e ∈ ker(Sᴴ)!
  have hkerS_pos : 0 < Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin Sᴴ)) := by
    rw [finrank_ker_conjTranspose_eq S]
    have hbot_lt : (⊥ : Submodule ℂ (Fin n → ℂ)) < LinearMap.ker (Matrix.mulVecLin S) := by
      refine lt_of_le_of_ne bot_le fun h0 => ?_
      have hz_mem : z ∈ LinearMap.ker (Matrix.mulVecLin S) := hz_ker
      rw [← h0, Submodule.mem_bot] at hz_mem
      exact hz_ne hz_mem
    have := Submodule.finrank_lt_finrank_of_lt hbot_lt
    simpa using this
  -- Case split: either ∃ e ∈ ker(Sᴴ) with (A k0)ᴴ *ᵥ e ≠ 0 (Householder reflection!),
  -- or ∀ e ∈ ker(Sᴴ), (A k0)ᴴ *ᵥ e = 0 (2D Givens rotation in span{wHat, e} ⊆ ℂ^n!).
  by_cases hCase1 : ∃ e0 : Fin n → ℂ, Sᴴ.mulVec e0 = 0 ∧ (A k0)ᴴ.mulVec e0 ≠ 0
  · -- Case 1: Householder reflection Q = I - 2 e eᴴ ∈ U(n) gives S'ᴴ S' = Sᴴ S + 4 r rᴴ!
    obtain ⟨e0, he0_S, he0_A⟩ := hCase1
    have he0_ne : e0 ≠ 0 := fun h0 => he0_A (by rw [h0, Matrix.mulVec_zero])
    let e0E : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 e0
    have he0_norm_pos : 0 < ‖e0E‖ := norm_pos_iff.mpr fun h0 => he0_ne (congrArg WithLp.ofLp h0)
    let e : Fin n → ℂ := ((‖e0E‖⁻¹ : ℝ) : ℂ) • e0
    have he_unit : star e ⬝ᵥ e = 1 := by
      have h1 : star e0 ⬝ᵥ e0 = ((‖e0E‖ ^ 2 : ℝ) : ℂ) := by
        have h2 : star e0 ⬝ᵥ e0 = inner ℂ e0E e0E := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
      simp only [e, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
        Complex.conj_ofReal, h1]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      exact_mod_cast (by field_simp [he0_norm_pos.ne'] : ‖e0E‖⁻¹ * (‖e0E‖⁻¹ * ‖e0E‖ ^ 2) = 1)
    have he_S : Sᴴ.mulVec e = 0 := by simp [e, Matrix.mulVec_smul, he0_S]
    let r : Fin n → ℂ := (A k0)ᴴ.mulVec e
    have hr_ne : r ≠ 0 := by
      simp only [r, e, Matrix.mulVec_smul]
      intro h0
      rcases smul_eq_zero.mp h0 with hc | hv
      · exact (Complex.ofReal_ne_zero.mpr (inv_ne_zero he0_norm_pos.ne')) hc
      · exact he0_A hv
    let Q_mat : Mat n := 1 - (2 : ℂ) • outerMat e e
    have hQ_herm : Q_matᴴ = Q_mat := by
      simp only [Q_mat, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
        (outerMat_posSemidef e).isHermitian.eq, Complex.star_def, map_ofNat]
    have hQ_unit : Q_mat ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hQ_herm]
      have hout_sq : outerMat e e * outerMat e e = outerMat e e := by
        ext i j; simp only [Matrix.mul_apply, outerMat, Matrix.of_apply]
        have : ∑ k, e i * star (e k) * (e k * star (e j)) = e i * star (e j) * (star e ⬝ᵥ e) := by
          simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, he_unit, mul_one]
      simp only [Q_mat, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.smul_mul, Matrix.mul_smul, hout_sq]
      ext i j; simp; ring
    let Q : Matrix.unitaryGroup (Fin n) ℂ := ⟨Q_mat, hQ_unit⟩
    let A' : Fin m → Mat n := Function.update A k0 ((Q : Mat n) * A k0)
    have hH' : ∑ j, matAbs (A' j) = H := by
      have hfun : (fun j => matAbs (A' j)) = fun j => matAbs (A j) := by
        ext j a b; by_cases hjk : j = k0
        · subst hjk
          have : A' j = (Q : Mat n) * A j := by simp [A']
          rw [this, matAbs_unitary_mul]
        · simp [A', hjk]
      rw [hfun]
    have hS' : ∑ j, A' j = S - (2 : ℂ) • outerMat e r := by
      have h1 := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ k0) A ((Q : Mat n) * A k0)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      have h2 := Finset.add_sum_erase Finset.univ A (Finset.mem_univ k0)
      have hQA : (Q : Mat n) * A k0 = A k0 - (2 : ℂ) • outerMat e r := by
        change (1 - (2 : ℂ) • outerMat e e) * A k0 = A k0 - (2 : ℂ) • outerMat e r
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
        congr 2; ext i j
        simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, r, Matrix.mulVec, dotProduct,
          Matrix.conjTranspose_apply, star_sum, star_mul', star_star, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [h1, hQA]
      change A k0 - (2 : ℂ) • outerMat e r + ∑ j ∈ Finset.univ.erase k0, A j = (∑ x, A x) - (2 : ℂ) • outerMat e r
      rw [← h2]; abel
    have hGram' : (∑ j, A' j)ᴴ * (∑ j, A' j) = Sᴴ * S + (4 : ℂ) • outerMat r r := by
      rw [hS', Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Complex.star_def, map_ofNat]
      have houtH : (outerMat e r)ᴴ = outerMat r e := by
        ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul',
          star_star]; ring
      rw [houtH, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      have hc1 : Sᴴ * outerMat e r = 0 := by
        ext i j
        have hi := congr_fun he_S i
        simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, Matrix.mulVec, dotProduct,
          Pi.zero_apply, Matrix.zero_apply] at hi ⊢
        have : ∑ k, Sᴴ i k * (e k * star (r j)) = (∑ k, Sᴴ i k * e k) * star (r j) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, hi, zero_mul]
      have hc2 : outerMat r e * S = 0 := by
        have := congrArg Matrix.conjTranspose hc1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, houtH,
          Matrix.conjTranspose_zero] at this
        exact this
      have hsq : outerMat r e * outerMat e r = outerMat r r := by
        ext i j; simp only [Matrix.mul_apply, outerMat, Matrix.of_apply]
        have : ∑ k, r i * star (e k) * (e k * star (r j)) = r i * star (r j) * (star e ⬝ᵥ e) := by
          simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, he_unit, mul_one]
      rw [Matrix.mul_smul, hc1, smul_zero, Matrix.smul_mul, hc2, smul_zero,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq]
      ext i j
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
        smul_eq_mul, sub_zero, zero_sub]; ring
    have hPow_lt : schattenPow p S < schattenPow p (∑ j, A' j) := by
      rw [← schattenPow_gram hp0 S, ← schattenPow_gram hp0 (∑ j, A' j), hGram']
      exact schattenPow_lt_add_rankOne_lt_one hq0 hq1 (Matrix.posSemidef_conjTranspose_mul_self S) hr_ne
    have hNorm_lt : schattenNorm p S < schattenNorm p (∑ j, A' j) := by
      unfold schattenNorm
      exact Real.rpow_lt_rpow (schattenPow_nonneg p S) hPow_lt (one_div_pos.mpr hp0)
    refine ⟨A', hH', ?_⟩
    unfold leeRatio; rw [hH']
    exact div_lt_div_of_pos_right hNorm_lt hH_norm_pos
  · -- Case 2: ∀ e0 ∈ ker(Sᴴ), (A k0)ᴴ *ᵥ e0 = 0!
    -- Pick unit e ∈ ker(Sᴴ); then e ⊥ wHat = (A k0 *ᵥ z) / ‖A k0 *ᵥ z‖, so 2D Givens rotation
    -- in span{wHat, e} ⊆ ℂ^n yields the EXACT SAME Gram matrix M(η) as Lemma 2 in dimension n!
    push Not at hCase1
    have hex_e0 : ∃ e0 : Fin n → ℂ, e0 ≠ 0 ∧ Sᴴ.mulVec e0 = 0 := by
      have hne_bot : LinearMap.ker (Matrix.mulVecLin Sᴴ) ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hkerS_pos; omega
      obtain ⟨e0, he0_mem, he0_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
      exact ⟨e0, he0_ne, he0_mem⟩
    obtain ⟨e0, he0_ne, he0_S⟩ := hex_e0
    let e0E : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 e0
    have he0_norm_pos : 0 < ‖e0E‖ := norm_pos_iff.mpr fun h0 => he0_ne (congrArg WithLp.ofLp h0)
    let e : Fin n → ℂ := ((‖e0E‖⁻¹ : ℝ) : ℂ) • e0
    have he_unit : star e ⬝ᵥ e = 1 := by
      have h1 : star e0 ⬝ᵥ e0 = ((‖e0E‖ ^ 2 : ℝ) : ℂ) := by
        have h2 : star e0 ⬝ᵥ e0 = inner ℂ e0E e0E := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
      simp only [e, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
        Complex.conj_ofReal, h1]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      exact_mod_cast (by field_simp [he0_norm_pos.ne'] : ‖e0E‖⁻¹ * (‖e0E‖⁻¹ * ‖e0E‖ ^ 2) = 1)
    have he_S : Sᴴ.mulVec e = 0 := by simp [e, Matrix.mulVec_smul, he0_S]
    have he_Ak0 : (A k0)ᴴ.mulVec e = 0 := hCase1 e he_S
    -- Build wHat = (A k0 *ᵥ z) / ‖A k0 *ᵥ z‖ and verify e ⊥ wHat!
    let wE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 ((A k0).mulVec z)
    have hwE_ne : wE ≠ 0 := fun h0 => hk0_ne (congrArg WithLp.ofLp h0)
    have hwnorm_pos : 0 < ‖wE‖ := norm_pos_iff.mpr hwE_ne
    let what : Fin n → ℂ := ((‖wE‖⁻¹ : ℝ) : ℂ) • (A k0).mulVec z
    have hwhat_unit : star what ⬝ᵥ what = 1 := by
      have h1 : star ((A k0).mulVec z) ⬝ᵥ (A k0).mulVec z = ((‖wE‖ ^ 2 : ℝ) : ℂ) := by
        have h2 : star ((A k0).mulVec z) ⬝ᵥ (A k0).mulVec z = inner ℂ wE wE := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
      simp only [what, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def,
        Complex.conj_ofReal, h1]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      exact_mod_cast (by field_simp [hwnorm_pos.ne'] : ‖wE‖⁻¹ * (‖wE‖⁻¹ * ‖wE‖ ^ 2) = 1)
    have he_what : star e ⬝ᵥ what = 0 := by
      simp only [what, dotProduct_smul, smul_eq_mul]
      have h1 : star e ⬝ᵥ (A k0).mulVec z = star ((A k0)ᴴ.mulVec e) ⬝ᵥ z := by
        rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec]
      rw [h1, he_Ak0, star_zero, zero_dotProduct, mul_zero]
    have hwhat_e : star what ⬝ᵥ e = 0 := by
      have h1 : star (star e ⬝ᵥ what) = star what ⬝ᵥ e := by
        simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
        refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
      rw [← h1, he_what, star_zero]
    -- Re-use the EXACT same M(η) strict inequality from lemma2_full_rank_sum by noting that
    -- for ANY η ∈ (0, 1], the 2D Givens rotation R(η) ∈ U(n) on span{what, e} satisfies:
    --   (S(η))ᴴ * S(η) = M(η) where M(η) = Sᴴ S - η (r qᴴ + q rᴴ - 2 r rᴴ)!
    -- Wait: we can invoke the SAME rank-2 square completion directly or prove ∃ η ∈ (0, 1] with
    -- schattenPow (p/2) M(η) > schattenPow (p/2) (Sᴴ S)!
    -- EVEN SIMPLER: Look! For ANY A' constructed in lemma2_full_rank_sum? No, lemma2_full_rank_sum
    -- uses padZero (n+1) where e = e_{n+1}. Here we have e ∈ ℂ^n with e ⊥ what, eᴴ S = 0, eᴴ A k0 = 0!
    -- Check that R(η) := 1 + ((1 - η) - 1) • (outerMat what what + outerMat e e) +
    --                    s • (outerMat e what - outerMat what e) with s = √(1 - (1 - η)^2)
    -- is unitary in U(n) and gives (S_R(η))ᴴ * S_R(η) = M(η), and padZero (S_R(η)) has the
    -- EXACT SAME singular values as S_tilde(η) in lemma2_full_rank_sum!!
    -- WAIT A SECOND! Even cleaner: use a unitary W ∈ U(n+1) mapping (e, 0) ↔ (0, 1) and fixing
    -- everything in {e}ᗮ ⊂ ℂ^n!!
    -- CHECK THAT!!
    -- Define the involutive permutation/swap unitary W ∈ U(n+1) swapping (e, 0) and e_{n+1}!!
    -- Then W * (padZero (A j)) = padZero (A j) for EVERY j (since eᴴ A k0 = 0 AND eᴴ S = 0?
    -- Wait: eᴴ A j might NOT be 0 for j ≠ k0, only eᴴ S = 0 and eᴴ A k0 = 0!)
    -- So we only apply W to S_tilde: wait — we only need S_R(η)ᴴ S_R(η) = M(η), AND
    -- let's verify that `schattenPow (p/2) (Sᴴ S) < schattenPow (p/2) M(η)` is ALREADY proved
    -- via a 1-line call to `lemma2_full_rank_sum` applied to the 2-tuple `(A k0, S - A k0)`?
    -- NO, `|S - A k0|` differs from `∑_{j ≠ k0} |A j|`.
    -- Instead, let's check directly: for `Ã` in `lemma2_full_rank_sum`, `S_tilde(η)` is obtained
    -- by rotating ONLY `A k0` in `span{(what, 0), e_{n+1}}`, which gives `M(η)`!
    -- Wait: `lemma2_full_rank_sum` didn't expose `M(η)` separately, so let's do the 3-line
    -- Givens construction directly via `lemma2_full_rank_sum`? NO! Look at `W` again!
    -- Let `A_pair : Fin 2 → Mat n := ![A k0, S - A k0]`!
    -- WAIT A SECOND!! Check `A_pair`? No, we don't know `z ∈ ran(|A k0| + |S - A k0|)`?
    -- YES WE DO!! Because `A k0 *ᵥ z ≠ 0`, so `zᴴ |A k0| z > 0`, so `zᴴ (|A k0| + |S - A k0|) z > 0`!
    -- Wait: `z` might have a component in `ker(|A k0| + |S - A k0|)` — wait: `A_pair` STILL has
    -- `A0 = A k0`, `A1 = S - A k0`, `A0 + A1 = S`!
    -- WAIT A SECOND!! If we apply `W` (swap `e` and `e_{n+1}`) to `S_tilde`? No, `lemma2_full_rank_sum`
    -- gives an EXISTENTIAL `A' : Fin m → Mat (n+1)`, it doesn't return `η`.
    -- So let's just write the clean 40-line `M(η)` bound right here (Wait: we ALREADY have
    -- `schattenPow_add_kernel_rankOne` and `schattenPow_mono_of_posSemidef_lt_one` imported from
    -- `MI20.Lemma2_LeftRotation`!! So the `M(η)` strict inequality is literally 60 lines using
    -- those exact imported lemmas!!).
    let G0 : Mat n := Sᴴ * S
    have hG0 : G0.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self S
    let r : Fin n → ℂ := (A k0)ᴴ.mulVec what
    let qv : Fin n → ℂ := Sᴴ.mulVec what
    let Vp : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := LinearMap.range (Matrix.toEuclideanLin G0)
    let rE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 r
    let r1E : EuclideanSpace ℂ (Fin n) := Vp.starProjection rE
    let r0E : EuclideanSpace ℂ (Fin n) := rE - r1E
    let r1 : Fin n → ℂ := r1E.ofLp
    let r0 : Fin n → ℂ := r0E.ofLp
    have hr_split : r = r1 + r0 := by ext i; simp [r1, r0, r0E, rE]
    have hr0_kerG0 : G0.mulVec r0 = 0 := by
      have hr0_orth : r0E ∈ Vpᗮ := Submodule.sub_starProjection_mem_orthogonal rE
      have h1 : ∀ y : EuclideanSpace ℂ (Fin n), inner ℂ (Matrix.toEuclideanLin G0 y) r0E = 0 := fun y =>
        Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ y) hr0_orth
      have h2 : Matrix.toEuclideanLin G0 r0E = 0 := by
        apply ext_inner_left ℂ; intro y
        have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
        rw [inner_zero_right, ← hadj, LinearMap.adjoint_inner_right, h1 y]
      exact congrArg WithLp.ofLp h2
    have hr0_ne : r0 ≠ 0 := by
      have hz_orth : WithLp.toLp 2 z ∈ Vpᗮ := by
        rw [Submodule.mem_orthogonal]
        rintro _ ⟨y, rfl⟩
        have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
        rw [← LinearMap.adjoint_inner_right, hadj]
        have hG0z : Matrix.toEuclideanLin G0 (WithLp.toLp 2 z) = 0 := by
          apply WithLp.ofLp_injective 2
          change (Sᴴ * S).mulVec z = 0
          rw [← Matrix.mulVec_mulVec, hz_ker, Matrix.mulVec_zero]
        rw [hG0z, inner_zero_right]
      have hr1_z : inner ℂ r1E (WithLp.toLp 2 z) = 0 :=
        Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem Vp rE) hz_orth
      have hr_z : inner ℂ rE (WithLp.toLp 2 z) = (‖wE‖ : ℂ) := by
        have h1 : rE = (Matrix.toEuclideanLin (A k0)).adjoint (WithLp.toLp 2 what) := by
          apply WithLp.ofLp_injective 2
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; rfl
        rw [h1, LinearMap.adjoint_inner_left]
        change inner ℂ (WithLp.toLp 2 what) wE = (‖wE‖ : ℂ)
        have hwhatE : WithLp.toLp 2 what = ((‖wE‖⁻¹ : ℝ) : ℂ) • wE := by
          apply WithLp.ofLp_injective 2; rfl
        rw [hwhatE, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
        have hcast : ((‖wE‖ ^ 2 : ℝ) : ℂ) = RCLike.ofReal (‖wE‖ ^ 2) := rfl
        rw [← hcast, ← Complex.ofReal_mul]; congr 1; field_simp [hwnorm_pos.ne']
      have hr0_z : inner ℂ r0E (WithLp.toLp 2 z) = (‖wE‖ : ℂ) := by
        simp only [r0E, inner_sub_left, hr_z, hr1_z, sub_zero]
      intro h0
      have : r0E = 0 := WithLp.ofLp_injective 2 h0
      rw [this, inner_zero_left] at hr0_z
      exact (Complex.ofReal_ne_zero.mpr hwnorm_pos.ne') hr0_z.symm
    have hqv_Vp : WithLp.toLp 2 qv ∈ Vp := by
      have hVpp : Vp = (Vpᗮ)ᗮ := (Submodule.orthogonal_orthogonal Vp).symm
      rw [hVpp, Submodule.mem_orthogonal]
      intro x hx
      have hG0x : G0.mulVec x.ofLp = 0 := by
        have h1 : ∀ y : EuclideanSpace ℂ (Fin n), inner ℂ (Matrix.toEuclideanLin G0 y) x = 0 := fun y =>
          Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ y) hx
        have h2 : Matrix.toEuclideanLin G0 x = 0 := by
          apply ext_inner_left ℂ; intro y
          have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
            rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
          rw [inner_zero_right, ← hadj, LinearMap.adjoint_inner_right, h1 y]
        exact congrArg WithLp.ofLp h2
      have hSx : S.mulVec x.ofLp = 0 := by
        have hsq : (star (S.mulVec x.ofLp) ⬝ᵥ S.mulVec x.ofLp).re = 0 := by
          have h1 : star (S.mulVec x.ofLp) ⬝ᵥ S.mulVec x.ofLp = star x.ofLp ⬝ᵥ G0.mulVec x.ofLp := by
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
          rw [h1, hG0x, dotProduct_zero, Complex.zero_re]
        have hE : ‖WithLp.toLp 2 (S.mulVec x.ofLp)‖ ^ 2 = 0 := by
          have h1 : star (S.mulVec x.ofLp) ⬝ᵥ S.mulVec x.ofLp =
              inner ℂ (WithLp.toLp 2 (S.mulVec x.ofLp)) (WithLp.toLp 2 (S.mulVec x.ofLp)) := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
          rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hsq
          have h2 : (RCLike.ofReal (K := ℂ) (‖WithLp.toLp 2 (S.mulVec x.ofLp)‖ ^ 2)).re =
              ‖WithLp.toLp 2 (S.mulVec x.ofLp)‖ ^ 2 := by
            change ((‖WithLp.toLp 2 (S.mulVec x.ofLp)‖ ^ 2 : ℝ) : ℂ).re = _
            exact Complex.ofReal_re _
          linarith
        exact congrArg WithLp.ofLp (norm_eq_zero.mp (sq_eq_zero_iff.mp hE))
      have h1 : WithLp.toLp 2 qv = (Matrix.toEuclideanLin S).adjoint (WithLp.toLp 2 what) := by
        apply WithLp.ofLp_injective 2
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; rfl
      rw [h1, LinearMap.adjoint_inner_right]
      have hSxE : Matrix.toEuclideanLin S x = 0 := WithLp.ofLp_injective 2 hSx
      rw [hSxE, inner_zero_left]
    -- Spectral gap of G0 on Vp (exact same 20-line argument as Lemma 2)
    let lam := hG0.isHermitian.eigenvalues
    let Spos : Finset (Fin n) := Finset.univ.filter (fun i => lam i ≠ 0)
    have hSpos_ne : Spos.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hG0_zero : G0 = 0 := by
        have hspec := hG0.isHermitian.spectral_theorem
        have h0 : Matrix.diagonal (RCLike.ofReal ∘ lam) = (0 : Mat n) := by
          ext i j; by_cases hij : i = j
          · subst hij
            have hi : lam i = 0 := by
              by_contra hne
              have : i ∈ Spos := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
              rw [hempty] at this; exact Finset.notMem_empty i this
            simp [hi]
          · simp [Matrix.diagonal, hij]
        rw [hspec, h0, map_zero]
      have htr : (G0.trace).re = 0 := by rw [hG0_zero, Matrix.trace_zero, Complex.zero_re]
      have hpos : 0 < (G0.trace).re := by
        have h1 : (G0.trace).re = schattenPow 2 S := by
          rw [← schattenPow_gram (by norm_num : (0 : ℝ) < 2) S]
          norm_num only
          have hG0_eq : G0 = (hG0.isHermitian.eigenvectorUnitary : Mat n) *
              Matrix.diagonal (fun i => (lam i : ℂ)) * (hG0.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
            simpa [lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
              using hG0.isHermitian.spectral_theorem
          change (G0.trace).re = schattenPow 1 G0
          rw [hG0_eq, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self, Matrix.one_mul,
            Matrix.trace_diagonal, Complex.re_sum, schattenPow_unitary_mul_conjTranspose_right zero_le_one,
            schattenPow_unitary_mul_left, schattenPow_diagonal zero_lt_one lam hG0.eigenvalues_nonneg]
          simp [Real.rpow_one]
        rw [h1, ← schattenNorm_rpow (by norm_num : (0 : ℝ) < 2) S]
        exact Real.rpow_pos_of_pos (schattenNorm_pos_of_ne_zero (by norm_num : (0 : ℝ) < 2) hS_ne) 2
      linarith
    let lamMin : ℝ := (Spos.image lam).min' (hSpos_ne.image lam)
    have hlamMin_pos : 0 < lamMin := by
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (Finset.min'_mem (Spos.image lam) (hSpos_ne.image lam))
      dsimp only [lamMin]; rw [← heq]
      exact lt_of_le_of_ne (hG0.eigenvalues_nonneg i) (Ne.symm (Finset.mem_filter.mp hi).2)
    have hG0_lb : ∀ x : Fin n → ℂ, lamMin * ‖Vp.starProjection (WithLp.toLp 2 x)‖ ^ 2 ≤
        (star x ⬝ᵥ G0.mulVec x).re := by
      intro x
      let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
      let b := hG0.isHermitian.eigenvectorBasis
      have hquad : (star x ⬝ᵥ G0.mulVec x).re = ∑ i : Fin n, lam i * ‖inner ℂ (b i) xE‖ ^ 2 := by
        have h1 : star x ⬝ᵥ G0.mulVec x = inner ℂ xE (Matrix.toEuclideanLin G0 xE) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
        rw [h1]
        have hexp : xE = ∑ i : Fin n, inner ℂ (b i) xE • b i := (b.sum_repr' xE).symm
        have hGx : Matrix.toEuclideanLin G0 xE = ∑ i : Fin n, (lam i : ℂ) • (inner ℂ (b i) xE • b i) := by
          conv_lhs => rw [hexp]
          rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul]
          have hbi : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
            apply WithLp.ofLp_injective 2
            simpa [b, lam, Complex.real_smul] using hG0.isHermitian.mulVec_eigenvectorBasis i
          rw [hbi, smul_comm]
        rw [hGx, inner_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_smul_right, inner_smul_right]
        have hbi_x : inner ℂ xE (b i) = (starRingEnd ℂ) (inner ℂ (b i) xE) := (inner_conj_symm _ _).symm
        rw [hbi_x, show (lam i : ℂ) * (inner ℂ (b i) xE * (starRingEnd ℂ) (inner ℂ (b i) xE)) =
            (lam i : ℂ) * ((starRingEnd ℂ) (inner ℂ (b i) xE) * inner ℂ (b i) xE) by ring,
          Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      have hproj_sq : ‖Vp.starProjection xE‖ ^ 2 = ∑ i ∈ Spos, ‖inner ℂ (b i) xE‖ ^ 2 := by
        have hparseval : ‖Vp.starProjection xE‖ ^ 2 = ∑ i : Fin n, ‖inner ℂ (b i) (Vp.starProjection xE)‖ ^ 2 :=
          (b.sum_sq_norm_inner_right (Vp.starProjection xE)).symm
        rw [hparseval, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => lam i ≠ 0)]
        have hzero : ∑ i ∈ Finset.univ.filter (fun i => ¬ lam i ≠ 0), ‖inner ℂ (b i) (Vp.starProjection xE)‖ ^ 2 = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hli : lam i = 0 := not_not.mp (Finset.mem_filter.mp hi).2
          have hbi_orth : b i ∈ Vpᗮ := by
            rw [Submodule.mem_orthogonal]; rintro _ ⟨y, rfl⟩
            have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
              rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
            rw [← LinearMap.adjoint_inner_right, hadj]
            have hbi0 : Matrix.toEuclideanLin G0 (b i) = 0 := by
              apply WithLp.ofLp_injective 2
              simpa [b, lam, hli] using hG0.isHermitian.mulVec_eigenvectorBasis i
            rw [hbi0, inner_zero_right]
          rw [Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem Vp xE) hbi_orth,
            norm_zero, sq, zero_mul]
        rw [hzero, add_zero]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hbi_Vp : b i ∈ Vp := by
          have hli : lam i ≠ 0 := (Finset.mem_filter.mp hi).2
          refine ⟨((lam i)⁻¹ : ℂ) • b i, ?_⟩
          rw [map_smul]
          have hbi : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
            apply WithLp.ofLp_injective 2
            simpa [b, lam, Complex.real_smul] using hG0.isHermitian.mulVec_eigenvectorBasis i
          rw [hbi, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hli), one_smul]
        have hinner : inner ℂ (b i) (Vp.starProjection xE) = inner ℂ (b i) xE := by
          have h0 : inner ℂ (b i) (xE - Vp.starProjection xE) = 0 :=
            Submodule.inner_right_of_mem_orthogonal hbi_Vp (Submodule.sub_starProjection_mem_orthogonal xE)
          rw [inner_sub_right] at h0; exact (sub_eq_zero.mp h0).symm
        rw [hinner]
      rw [hquad, hproj_sq, Finset.mul_sum]
      calc ∑ i ∈ Spos, lamMin * ‖inner ℂ (b i) xE‖ ^ 2
          ≤ ∑ i ∈ Spos, lam i * ‖inner ℂ (b i) xE‖ ^ 2 := by
            refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            exact Finset.min'_le _ _ (Finset.mem_image_of_mem lam hi)
        _ ≤ ∑ i : Fin n, lam i * ‖inner ℂ (b i) xE‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun i _ _ => mul_nonneg (hG0.eigenvalues_nonneg i) (sq_nonneg _)
    -- Rank-2 square completion on M(η) = G0 - η (qv rᴴ + r qvᴴ - 2 r rᴴ):
    let v1 : Fin n → ℂ := qv - (2 : ℂ) • r1
    let v1E : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v1
    have hv1_Vp : v1E ∈ Vp := by
      have : v1E = WithLp.toLp 2 qv - (2 : ℂ) • r1E := by apply WithLp.ofLp_injective 2; rfl
      rw [this]; exact Vp.sub_mem hqv_Vp (Vp.smul_mem 2 (Submodule.starProjection_apply_mem Vp rE))
    let β : ℝ := (2 * ‖v1E‖ ^ 2 + (1 / 2) * ‖WithLp.toLp 2 qv‖ ^ 2 + 1) / lamMin
    have hβ_pos : 0 < β := div_pos (by positivity) hlamMin_pos
    let r0_sq : ℝ := ∑ i, ‖r0 i‖ ^ 2
    have hr0_sq_pos : 0 < r0_sq := by
      have h1 : r0_sq = ‖r0E‖ ^ 2 := by
        have h2 : star r0 ⬝ᵥ r0 = inner ℂ r0E r0E := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        have hre := congrArg Complex.re h2
        rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hre
        have hre2 : (RCLike.ofReal (K := ℂ) (‖r0E‖ ^ 2)).re = ‖r0E‖ ^ 2 := by
          change ((‖r0E‖ ^ 2 : ℝ) : ℂ).re = _; exact Complex.ofReal_re _
        rw [hre2] at hre
        rw [← hre]; simp only [r0_sq, dotProduct, Pi.star_apply, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      rw [h1]; exact sq_pos_of_pos (norm_pos_iff.mpr fun h0 => hr0_ne (congrArg WithLp.ofLp h0))
    let M : ℝ → Mat n := fun η =>
      G0 - (η : ℂ) • (outerMat qv r + outerMat r qv - (2 : ℂ) • outerMat r r)
    have hM_ge : ∀ η : ℝ, 0 ≤ η →
        (M η - (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0)).PosSemidef := by
      intro η hη
      have hHerm : (M η - (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0)).IsHermitian := by
        have hM_herm : (M η).IsHermitian := by
          rw [Matrix.IsHermitian]; dsimp [M]
          have h1 : (outerMat qv r)ᴴ = outerMat r qv := by
            ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
          have h2 : (outerMat r qv)ᴴ = outerMat qv r := by
            ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
          simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
            hG0.isHermitian.eq, (outerMat_posSemidef r).isHermitian.eq, h1, h2,
            star_trivial, Complex.star_def, map_ofNat]
          rw [add_comm (outerMat r qv)]
        rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, hM_herm.eq, Matrix.conjTranspose_add,
          Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
          Complex.conj_ofReal, hG0.isHermitian.eq, (outerMat_posSemidef r0).isHermitian.eq]
      rw [Matrix.posSemidef_iff_dotProduct_mulVec]
      refine ⟨hHerm, fun x => ?_⟩
      rw [Complex.nonneg_iff]
      refine ⟨?_, (isHermitian_im_dotProduct_mulVec_self hHerm x).symm⟩
      -- Same exact square-completion bound:
      -- Re(xᴴ (M(η) - (1-βη)G0 - η r0 r0ᴴ) x) = η * (β Re(xᴴ G0 x) + Re(xᴴ(2r1r1ᴴ - qv r1ᴴ - r1 qvᴴ + r0 r0ᴴ - qv r0ᴴ - r0 qvᴴ + 2 r1 r0ᴴ + 2 r0 r1ᴴ)x))
      let a1 : ℂ := star r1 ⬝ᵥ x
      let a0 : ℂ := star r0 ⬝ᵥ x
      let aq : ℂ := star qv ⬝ᵥ x
      let av : ℂ := star v1 ⬝ᵥ x
      have hav : av = aq - 2 * a1 := by
        simp only [av, aq, a1, v1, star_sub, star_smul, sub_dotProduct, smul_dotProduct,
          Complex.star_def, map_ofNat, smul_eq_mul]
      have hconj_dot : ∀ u : Fin n → ℂ, star x ⬝ᵥ u = (starRingEnd ℂ) (star u ⬝ᵥ x) := fun u => by
        simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Complex.star_def,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
        refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
      have hquad_id : (star x ⬝ᵥ (M η - (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0)).mulVec x).re =
          η * (β * (star x ⬝ᵥ G0.mulVec x).re +
            (2 * ‖a1‖ ^ 2 - (star aq * a1 + star a1 * aq).re + ‖a0‖ ^ 2 - (star av * a0 + star a0 * av).re)) := by
        have hstep1 : M η - (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) =
            (η : ℂ) • ((β : ℂ) • G0 + ((2 : ℂ) • outerMat r r - outerMat qv r - outerMat r qv - outerMat r0 r0)) := by
          dsimp [M]; ext i j; simp; ring
        rw [hstep1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        congr 1
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, Complex.add_re,
          smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        congr 1
        rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
          dotProduct_sub, dotProduct_sub, dotProduct_sub, dotProduct_smul, smul_eq_mul,
          outerMat_quad, outerMat_quad, outerMat_quad, outerMat_quad]
        have har : star r ⬝ᵥ x = a1 + a0 := by
          simp only [a1, a0, hr_split, star_add, add_dotProduct]
        have hxr : star x ⬝ᵥ r = star (a1 + a0) := by rw [← har]; exact hconj_dot r
        have hxq : star x ⬝ᵥ qv = star aq := hconj_dot qv
        have hxr0 : star x ⬝ᵥ r0 = star a0 := hconj_dot r0
        rw [har, hxr, hxq, hxr0]
        have hnorm_sq : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
          rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        have hcore : ((2 : ℂ) * (star (a1 + a0) * (a1 + a0)) - star aq * (a1 + a0) -
              star (a1 + a0) * aq - star a0 * a0).re =
            (2 * (star a1 * a1).re - (star aq * a1 + star a1 * aq).re +
              (star a0 * a0).re - (star av * a0 + star a0 * av).re) := by
          have heq : (2 : ℂ) * (star (a1 + a0) * (a1 + a0)) - star aq * (a1 + a0) -
                star (a1 + a0) * aq - star a0 * a0 =
              (2 : ℂ) * (star a1 * a1) - (star aq * a1 + star a1 * aq) +
                (star a0 * a0) - (star av * a0 + star a0 * av) := by
            rw [hav]; simp only [star_add, star_sub, star_mul', Complex.star_def, map_ofNat]; ring
          rw [heq]; simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
            Complex.im_ofNat]; ring
        rw [hcore, hnorm_sq a1, hnorm_sq a0]
      rw [hquad_id]
      refine mul_nonneg hη ?_
      -- Bound the bracketed term ≥ 0 via Cauchy-Schwarz on Vp!
      let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
      let xP : EuclideanSpace ℂ (Fin n) := Vp.starProjection xE
      have hdot_le : ∀ w : EuclideanSpace ℂ (Fin n), w ∈ Vp → ‖star w.ofLp ⬝ᵥ x‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖xP‖ ^ 2 := by
        intro w hw
        have h1 : star w.ofLp ⬝ᵥ x = inner ℂ w xE := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        have h2 : inner ℂ w xE = inner ℂ w xP := by
          have h0 : inner ℂ w (xE - xP) = 0 :=
            Submodule.inner_right_of_mem_orthogonal hw (Submodule.sub_starProjection_mem_orthogonal xE)
          rw [inner_sub_right] at h0; exact sub_eq_zero.mp h0
        rw [h1, h2]
        simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) w xP) 2
      have h1_le : ‖av‖ ^ 2 ≤ ‖v1E‖ ^ 2 * ‖xP‖ ^ 2 := hdot_le v1E hv1_Vp
      have h2_le : ‖aq‖ ^ 2 ≤ ‖WithLp.toLp 2 qv‖ ^ 2 * ‖xP‖ ^ 2 := hdot_le (WithLp.toLp 2 qv) hqv_Vp
      -- Complete the square in ‖a1‖ and ‖a0‖!
      have hcross1 : (star aq * a1 + star a1 * aq).re ≤ 2 * ‖a1‖ ^ 2 + (1 / 2) * ‖aq‖ ^ 2 := by
        have hnn : 0 ≤ (star (aq - 2 * a1) * (aq - 2 * a1)).re := by
          rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg _
        have hexp : (star (aq - 2 * a1) * (aq - 2 * a1)).re =
            ‖aq‖ ^ 2 + 4 * ‖a1‖ ^ 2 - 2 * (star aq * a1 + star a1 * aq).re := by
          have heq : star (aq - 2 * a1) * (aq - 2 * a1) =
              star aq * aq + 4 * (star a1 * a1) - 2 * (star aq * a1 + star a1 * aq) := by
            simp only [star_sub, star_mul', Complex.star_def, map_ofNat]; ring
          rw [heq, Complex.sub_re, Complex.add_re]
          have h4 : ((4 : ℂ) * (star a1 * a1)).re = 4 * (star a1 * a1).re := by
            rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; ring
          have h2 : ((2 : ℂ) * (star aq * a1 + star a1 * aq)).re = 2 * (star aq * a1 + star a1 * aq).re := by
            rw [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]; ring
          have hna : (star aq * aq).re = ‖aq‖ ^ 2 := by
            rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          have hn1 : (star a1 * a1).re = ‖a1‖ ^ 2 := by
            rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          rw [h4, h2, hna, hn1]
        linarith
      have hcross2 : (star av * a0 + star a0 * av).re ≤ ‖a0‖ ^ 2 + ‖av‖ ^ 2 := by
        have hnn : 0 ≤ (star (av - a0) * (av - a0)).re := by
          rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]; exact sq_nonneg _
        have hexp : (star (av - a0) * (av - a0)).re =
            ‖av‖ ^ 2 + ‖a0‖ ^ 2 - (star av * a0 + star a0 * av).re := by
          have heq : star (av - a0) * (av - a0) =
              star av * av + star a0 * a0 - (star av * a0 + star a0 * av) := by
            simp only [star_sub]; ring
          rw [heq, Complex.sub_re, Complex.add_re]
          have hnv : (star av * av).re = ‖av‖ ^ 2 := by
            rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          have hn0 : (star a0 * a0).re = ‖a0‖ ^ 2 := by
            rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
          rw [hnv, hn0]
        linarith
      have hβG : (2 * ‖v1E‖ ^ 2 + (1 / 2) * ‖WithLp.toLp 2 qv‖ ^ 2 + 1) * ‖xP‖ ^ 2 ≤
          β * (star x ⬝ᵥ G0.mulVec x).re := by
        have h1 := mul_le_mul_of_nonneg_left (hG0_lb x) hβ_pos.le
        have h2 : β * lamMin = 2 * ‖v1E‖ ^ 2 + (1 / 2) * ‖WithLp.toLp 2 qv‖ ^ 2 + 1 :=
          div_mul_cancel₀ _ hlamMin_pos.ne'
        nlinarith
      nlinarith [sq_nonneg ‖xP‖, sq_nonneg ‖v1E‖]
    -- Choose η ∈ (0, min(1, 1/(2β))] small enough that (1 - β η)^q * P0 + η^q * r0_sq^q > P0!
    let P0 : ℝ := schattenPow (p / 2) G0
    have hP0_pos : 0 < P0 := by
      have : P0 = schattenPow p S := schattenPow_gram hp0 S
      rw [this, ← schattenNorm_rpow hp0 S]
      exact Real.rpow_pos_of_pos (schattenNorm_pos_of_ne_zero hp0 hS_ne) p
    let c_thr : ℝ := r0_sq ^ (p / 2) / (2 * β * P0)
    have hcthr_pos : 0 < c_thr := div_pos (Real.rpow_pos_of_pos hr0_sq_pos _) (by positivity)
    let η : ℝ := min (min (1 / 2) (1 / (2 * β))) ((c_thr / 2) ^ ((1 - p / 2)⁻¹))
    have hη_pos : 0 < η := lt_min (lt_min (by norm_num) (div_pos one_pos (by positivity)))
      (Real.rpow_pos_of_pos (half_pos hcthr_pos) _)
    have hη_le_half : η ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hβη_le_half : β * η ≤ 1 / 2 := by
      have h1 : η ≤ 1 / (2 * β) := (min_le_left _ _).trans (min_le_right _ _)
      calc β * η ≤ β * (1 / (2 * β)) := mul_le_mul_of_nonneg_left h1 hβ_pos.le
        _ = 1 / 2 := by field_simp [hβ_pos.ne']
    -- Build 2D Givens rotation R ∈ U(n) in span{what, e} ⊆ ℂ^n with c = 1 - η, s = √(1 - (1-η)^2)!
    let cR : ℝ := 1 - η
    let sR : ℝ := Real.sqrt (1 - cR ^ 2)
    have hcsR : cR ^ 2 + sR ^ 2 = 1 := by
      have h1 : 0 ≤ 1 - cR ^ 2 := by dsimp [cR]; nlinarith
      simp [sR, Real.sq_sqrt h1]
    have h2η : (cR - 1) ^ 2 + sR ^ 2 = 2 * η := by
      have h1 : (1 - η - 1) ^ 2 + sR ^ 2 = (1 - η) ^ 2 + sR ^ 2 - 1 + 2 * η := by ring
      dsimp only [cR] at hcsR ⊢; linarith only [h1, hcsR]
    let R_mat : Mat n := 1 + ((cR - 1 : ℝ) : ℂ) • (outerMat what what + outerMat e e) +
      (sR : ℂ) • (outerMat e what - outerMat what e)
    -- Verify R_mat is unitary!
    have hout_mul : ∀ u1 v1 u2 v2 : Fin n → ℂ,
        outerMat u1 v1 * outerMat u2 v2 = (star v1 ⬝ᵥ u2) • outerMat u1 v2 := by
      intro u1 v1 u2 v2; ext i j
      simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
        dotProduct, Pi.star_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
    have hR_unit : R_mat ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      have hRH : R_matᴴ = 1 + ((cR - 1 : ℝ) : ℂ) • (outerMat what what + outerMat e e) +
          (sR : ℂ) • (outerMat what e - outerMat e what) := by
        dsimp [R_mat]
        rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
          Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
          Matrix.conjTranspose_sub, (outerMat_posSemidef what).isHermitian.eq,
          (outerMat_posSemidef e).isHermitian.eq, star_trivial, star_trivial]
        have h1 : (outerMat e what)ᴴ = outerMat what e := by
          ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
        have h2 : (outerMat what e)ᴴ = outerMat e what := by
          ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
        rw [h1, h2]
      rw [hRH]
      set P1 := outerMat what what
      set P2 := outerMat e e
      set E12 := outerMat what e
      set E21 := outerMat e what
      have hP1P1 : P1 * P1 = P1 := by rw [hout_mul, hwhat_unit, one_smul]
      have hP2P2 : P2 * P2 = P2 := by rw [hout_mul, he_unit, one_smul]
      have hP1P2 : P1 * P2 = 0 := by rw [hout_mul, hwhat_e, zero_smul]
      have hP2P1 : P2 * P1 = 0 := by rw [hout_mul, he_what, zero_smul]
      have hP1E21 : P1 * E21 = 0 := by rw [hout_mul, hwhat_e, zero_smul]
      have hP1E12 : P1 * E12 = E12 := by rw [hout_mul, hwhat_unit, one_smul]
      have hP2E21 : P2 * E21 = E21 := by rw [hout_mul, he_unit, one_smul]
      have hP2E12 : P2 * E12 = 0 := by rw [hout_mul, he_what, zero_smul]
      have hE12P1 : E12 * P1 = 0 := by rw [hout_mul, he_what, zero_smul]
      have hE12P2 : E12 * P2 = E12 := by rw [hout_mul, he_unit, one_smul]
      have hE21P1 : E21 * P1 = E21 := by rw [hout_mul, hwhat_unit, one_smul]
      have hE21P2 : E21 * P2 = 0 := by rw [hout_mul, hwhat_e, zero_smul]
      have hE12E21 : E12 * E21 = P1 := by rw [hout_mul, he_unit, one_smul]
      have hE21E12 : E21 * E12 = P2 := by rw [hout_mul, hwhat_unit, one_smul]
      have hE12E12 : E12 * E12 = 0 := by rw [hout_mul, he_what, zero_smul]
      have hE21E21 : E21 * E21 = 0 := by rw [hout_mul, hwhat_e, zero_smul]
      set a : ℂ := ((cR - 1 : ℝ) : ℂ)
      set b : ℂ := (sR : ℂ)
      have hcoef : (2 : ℂ) * a + a * a + b * b = 0 := by
        have hreal : 2 * (cR - 1) + (cR - 1) * (cR - 1) + sR * sR = 0 := by
          have hid : 2 * (cR - 1) + (cR - 1) * (cR - 1) + sR * sR = cR ^ 2 + sR ^ 2 - 1 := by ring
          linarith only [hid, hcsR]
        have hcast : (2 : ℂ) * a + a * a + b * b = ((2 * (cR - 1) + (cR - 1) * (cR - 1) + sR * sR : ℝ) : ℂ) := by
          dsimp [a, b]; push_cast; ring
        rw [hcast, hreal, Complex.ofReal_zero]
      have hexp : (1 + a • (P1 + P2) + b • (E12 - E21)) * (1 + a • (P1 + P2) + b • (E21 - E12)) =
          1 + ((2 : ℂ) * a + a * a + b * b) • (P1 + P2) := by
        have h1 : (P1 + P2) * (P1 + P2) = P1 + P2 := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP1P1, hP1P2, hP2P1, hP2P2]; abel
        have h2 : (P1 + P2) * (E21 - E12) = E21 - E12 := by
          rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, hP1E21, hP1E12, hP2E21, hP2E12]; abel
        have h3 : (E12 - E21) * (P1 + P2) = E12 - E21 := by
          rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, hE12P1, hE12P2, hE21P1, hE21P2]; abel
        have h4 : (E12 - E21) * (E21 - E12) = P1 + P2 := by
          rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hE12E21, hE12E12, hE21E21, hE21E12]; abel
        have hm1 : (a • (P1 + P2)) * (1 + a • (P1 + P2) + b • (E21 - E12)) =
            a • (P1 + P2) + (a * a) • (P1 + P2) + (a * b) • (E21 - E12) := by
          rw [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
            Matrix.mul_smul, h1, h2, smul_add, smul_add, smul_smul, smul_smul]
        have hm2 : (b • (E12 - E21)) * (1 + a • (P1 + P2) + b • (E21 - E12)) =
            b • (E12 - E21) + (b * a) • (E12 - E21) + (b * b) • (P1 + P2) := by
          rw [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
            Matrix.mul_smul, h3, h4, smul_add, smul_add, smul_smul, smul_smul]
        calc (1 + a • (P1 + P2) + b • (E12 - E21)) * (1 + a • (P1 + P2) + b • (E21 - E12))
            = 1 * (1 + a • (P1 + P2) + b • (E21 - E12)) +
              (a • (P1 + P2)) * (1 + a • (P1 + P2) + b • (E21 - E12)) +
              (b • (E12 - E21)) * (1 + a • (P1 + P2) + b • (E21 - E12)) := by
                rw [Matrix.add_mul, Matrix.add_mul]
          _ = 1 + a • (P1 + P2) + b • (E21 - E12) +
              (a • (P1 + P2) + (a * a) • (P1 + P2) + (a * b) • (E21 - E12)) +
              (b • (E12 - E21) + (b * a) • (E12 - E21) + (b * b) • (P1 + P2)) := by
                rw [Matrix.one_mul, hm1, hm2]
          _ = 1 + ((2 : ℂ) * a + a * a + b * b) • (P1 + P2) := by
                ext i j; simp; ring
      rw [hexp, hcoef, zero_smul, add_zero]
    let R : Matrix.unitaryGroup (Fin n) ℂ := ⟨R_mat, hR_unit⟩
    let A' : Fin m → Mat n := Function.update A k0 ((R : Mat n) * A k0)
    have hH' : ∑ j, matAbs (A' j) = H := by
      have hfun : (fun j => matAbs (A' j)) = fun j => matAbs (A j) := by
        ext j a b; by_cases hjk : j = k0
        · subst hjk
          have : A' j = (R : Mat n) * A j := by simp [A']
          rw [this, matAbs_unitary_mul]
        · simp [A', hjk]
      rw [hfun]
    -- Verify S' = S + ((cR - 1) what + sR e) rᴴ and S'ᴴ S' = M(η)!
    have hS' : ∑ j, A' j = S + ((cR - 1 : ℝ) : ℂ) • outerMat what r + (sR : ℂ) • outerMat e r := by
      have h1 := Finset.sum_update_of_mem (s := Finset.univ) (Finset.mem_univ k0) A ((R : Mat n) * A k0)
      rw [Finset.sdiff_singleton_eq_erase] at h1
      have h2 := Finset.add_sum_erase Finset.univ A (Finset.mem_univ k0)
      have hRA : (R : Mat n) * A k0 = A k0 + ((cR - 1 : ℝ) : ℂ) • outerMat what r + (sR : ℂ) • outerMat e r := by
        change (1 + ((cR - 1 : ℝ) : ℂ) • (outerMat what what + outerMat e e) +
          (sR : ℂ) • (outerMat e what - outerMat what e)) * A k0 = _
        have hou_A : ∀ u v : Fin n → ℂ, outerMat u v * A k0 = outerMat u ((A k0)ᴴ.mulVec v) := by
          intro u v; ext i j
          simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, Matrix.mulVec, dotProduct,
            Matrix.conjTranspose_apply, star_sum, star_mul', star_star, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => by ring
        have h0_e : outerMat what e * A k0 = 0 := by rw [hou_A, he_Ak0]; ext i j; simp [outerMat]
        have h0_ee : outerMat e e * A k0 = 0 := by rw [hou_A, he_Ak0]; ext i j; simp [outerMat]
        rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.add_mul, Matrix.sub_mul, h0_ee, add_zero, h0_e, sub_zero, hou_A, hou_A]
      dsimp only [S]; rw [h1, hRA, ← h2]; abel
    have hGram' : (∑ j, A' j)ᴴ * (∑ j, A' j) = M η := by
      rw [hS', Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
      have h1 : (outerMat what r)ᴴ = outerMat r what := by
        ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
      have h2 : (outerMat e r)ᴴ = outerMat r e := by
        ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
      rw [h1, h2]
      have hSe : Sᴴ * outerMat e r = 0 := by
        ext i j; have hi := congr_fun he_S i
        simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, Matrix.mulVec, dotProduct,
          Pi.zero_apply, Matrix.zero_apply] at hi ⊢
        have : ∑ k, Sᴴ i k * (e k * star (r j)) = (∑ k, Sᴴ i k * e k) * star (r j) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
        rw [this, hi, zero_mul]
      have heS : outerMat r e * S = 0 := by
        have := congrArg Matrix.conjTranspose hSe
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h2, Matrix.conjTranspose_zero] at this
        exact this
      have hSw : Sᴴ * outerMat what r = outerMat qv r := by
        ext i j; simp only [Matrix.mul_apply, outerMat, Matrix.of_apply, qv, Matrix.mulVec, dotProduct]
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
      have hwS : outerMat r what * S = outerMat r qv := by
        have := congrArg Matrix.conjTranspose hSw
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h1] at this
        have h3 : (outerMat qv r)ᴴ = outerMat r qv := by
          ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
        rwa [h3] at this
      have hww : outerMat r what * outerMat what r = outerMat r r := by rw [hout_mul, hwhat_unit, one_smul]
      have hee : outerMat r e * outerMat e r = outerMat r r := by rw [hout_mul, he_unit, one_smul]
      have hwe : outerMat r what * outerMat e r = 0 := by rw [hout_mul, hwhat_e, zero_smul]
      have hew : outerMat r e * outerMat what r = 0 := by rw [hout_mul, he_what, zero_smul]
      set a : ℂ := ((cR - 1 : ℝ) : ℂ)
      set b : ℂ := (sR : ℂ)
      have ha_eq : a = -((η : ℝ) : ℂ) := by dsimp [a, cR]; push_cast; ring
      have hab_eq : a * a + b * b = ((2 * η : ℝ) : ℂ) := by
        have h2η' : (cR - 1) * (cR - 1) + sR * sR = 2 * η := by simpa only [sq] using h2η
        dsimp [a, b]; exact_mod_cast h2η'
      calc (Sᴴ + a • outerMat r what + b • outerMat r e) * (S + a • outerMat what r + b • outerMat e r)
          = Sᴴ * (S + a • outerMat what r + b • outerMat e r) +
            (a • outerMat r what) * (S + a • outerMat what r + b • outerMat e r) +
            (b • outerMat r e) * (S + a • outerMat what r + b • outerMat e r) := by
              rw [Matrix.add_mul, Matrix.add_mul]
        _ = (Sᴴ * S + a • outerMat qv r + 0) +
            (a • outerMat r qv + (a * a) • outerMat r r + 0) +
            (0 + 0 + (b * b) • outerMat r r) := by
              simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
                hSw, hSe, hwS, hww, hwe, heS, hew, hee, smul_zero]
        _ = M η := by
              dsimp [M]; rw [ha_eq] at hab_eq ⊢
              ext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
                Complex.real_smul, add_zero, zero_add]
              have h1 : (-(η : ℂ)) * (-(η : ℂ)) + b * b = (2 : ℂ) * (η : ℂ) := by
                simpa using hab_eq
              linear_combination (outerMat r r i j) * h1
    -- Finally, compare schattenPow (p/2) (M η) ≥ (1 - β η)^(p/2) P0 + η^(p/2) r0_sq^(p/2) > P0!
    have hLow_psd : (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0).PosSemidef := by
      have h1 : ((1 - β * η : ℝ) : ℂ) • G0 = (1 - β * η) • G0 := by ext i j; simp [Complex.real_smul]
      have h2 : (η : ℂ) • outerMat r0 r0 = η • outerMat r0 r0 := by ext i j; simp [Complex.real_smul]
      rw [h1, h2]; exact (hG0.smul (by linarith)).add ((outerMat_posSemidef r0).smul hη_pos.le)
    have hM_psd : (M η).PosSemidef := by
      have : M η = (M η - (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0)) +
          (((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) := by abel
      rw [this]; exact (hM_ge η hη_pos.le).add hLow_psd
    have hmono := schattenPow_mono_of_posSemidef_lt_one hq0 hq1 hLow_psd hM_psd (hM_ge η hη_pos.le)
    have hadd := schattenPow_add_kernel_rankOne hq0 hG0 (by linarith : 0 ≤ 1 - β * η) hη_pos.le r0 hr0_ne hr0_kerG0
    have h1m_ge : 1 - 2 * β * η ≤ (1 - β * η) ^ (p / 2) := by
      have h0 : 0 ≤ 1 - β * η := by linarith
      have hle1 : 1 - β * η ≤ 1 := by linarith [mul_pos hβ_pos hη_pos]
      have hpow_ge : 1 - β * η ≤ (1 - β * η) ^ (p / 2) := by
        calc 1 - β * η = (1 - β * η) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (1 - β * η) ^ (p / 2) := Real.rpow_le_rpow_of_exponent_ge' h0 hle1 hq0.le hq1.le
      linarith [mul_pos hβ_pos hη_pos]
    have hη_gain : 2 * β * P0 * η < η ^ (p / 2) * r0_sq ^ (p / 2) := by
      have h1 : η ^ (1 - p / 2) ≤ c_thr / 2 := by
        calc η ^ (1 - p / 2) ≤ ((c_thr / 2) ^ (1 - p / 2)⁻¹) ^ (1 - p / 2) :=
              Real.rpow_le_rpow hη_pos.le (min_le_right _ _) (by linarith)
          _ = c_thr / 2 := by
              rw [← Real.rpow_mul (half_pos hcthr_pos).le, inv_mul_cancel₀ (by linarith), Real.rpow_one]
      have h2 : η = η ^ (p / 2) * η ^ (1 - p / 2) := by
        rw [← Real.rpow_add hη_pos]; norm_num
      have h3 : 2 * β * P0 * η ≤ 2 * β * P0 * (η ^ (p / 2) * (c_thr / 2)) := by
        conv_lhs => rw [h2]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hη_pos.le _)) (by positivity)
      have h4 : 2 * β * P0 * (η ^ (p / 2) * (c_thr / 2)) = (1 / 2) * (η ^ (p / 2) * r0_sq ^ (p / 2)) := by
        dsimp [c_thr]; field_simp [hβ_pos.ne', hP0_pos.ne']
      linarith [mul_pos (Real.rpow_pos_of_pos hη_pos (p / 2)) (Real.rpow_pos_of_pos hr0_sq_pos (p / 2))]
    have hPow_lt : schattenPow p S < schattenPow p (∑ j, A' j) := by
      rw [← schattenPow_gram hp0 S, ← schattenPow_gram hp0 (∑ j, A' j), hGram']
      change P0 < schattenPow (p / 2) (M η)
      rw [hadd] at hmono
      change (1 - β * η) ^ (p / 2) * P0 + (η * r0_sq) ^ (p / 2) ≤ schattenPow (p / 2) (M η) at hmono
      rw [Real.mul_rpow hη_pos.le hr0_sq_pos.le] at hmono
      have hlin : P0 < (1 - β * η) ^ (p / 2) * P0 + η ^ (p / 2) * r0_sq ^ (p / 2) := by
        nlinarith [mul_le_mul_of_nonneg_right h1m_ge hP0_pos.le]
      linarith
    have hNorm_lt : schattenNorm p S < schattenNorm p (∑ j, A' j) := by
      unfold schattenNorm
      exact Real.rpow_lt_rpow (schattenPow_nonneg p S) hPow_lt (one_div_pos.mpr hp0)
    refine ⟨A', hH', ?_⟩
    unfold leeRatio; rw [hH']
    exact div_lt_div_of_pos_right hNorm_lt hH_norm_pos

/-! ==========================================================================
    PART 3: Theorem 5 — Exact PSD-Splitting & POVM Reformulation (1 < p < 2)
    ========================================================================== -/

/-- Negative real power T^(-α) of a strictly positive definite matrix T ≻ 0 via spectral basis. -/
def posDefPow {n : ℕ} (r : ℝ) {T : Mat n} (hT : T.PosDef) : Mat n :=
  (hT.isHermitian.eigenvectorUnitary : Mat n) *
    Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ)) *
    (hT.isHermitian.eigenvectorUnitary : Mat n)ᴴ

lemma posDefPow_posDef {n : ℕ} (r : ℝ) {T : Mat n} (hT : T.PosDef) :
    (posDefPow r hT).PosDef := by
  unfold posDefPow
  have hd : (Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ))).PosDef := by
    rw [Matrix.posDef_diagonal_iff]; intro i
    exact_mod_cast Real.rpow_pos_of_pos (hT.eigenvalues_pos i) r
  -- U * D * Uᴴ is PosDef since U is invertible (unitary)
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  have hHerm : ((hT.isHermitian.eigenvectorUnitary : Mat n) *
      Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ)) *
      (hT.isHermitian.eigenvectorUnitary : Mat n)ᴴ).IsHermitian := by
    simpa using (hd.posSemidef.mul_mul_conjTranspose_same (hT.isHermitian.eigenvectorUnitary : Mat n)).isHermitian
  refine ⟨hHerm, fun x hx => ?_⟩
  let U := hT.isHermitian.eigenvectorUnitary
  let y : Fin n → ℂ := (U : Mat n)ᴴ.mulVec x
  have hy_ne : y ≠ 0 := by
    intro h0
    have h1 := congrArg (Matrix.mulVec (U : Mat n)) h0
    simp only [y, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self U, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
    exact hx h1
  have hquad : star x ⬝ᵥ ((U : Mat n) * Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ)) *
        (U : Mat n)ᴴ).mulVec x =
      star y ⬝ᵥ (Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ))).mulVec y := by
    simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    have : (star x) ᵥ* (U : Mat n) = star y := by
      simp only [y, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
    rw [this]
  rw [hquad]
  exact (Matrix.posDef_iff_dotProduct_mulVec.mp hd).2 hy_ne

lemma posDefPow_mul_posDefPow {n : ℕ} (r s : ℝ) {T : Mat n} (hT : T.PosDef) :
    posDefPow r hT * posDefPow s hT = posDefPow (r + s) hT := by
  let U := hT.isHermitian.eigenvectorUnitary
  let lam := hT.isHermitian.eigenvalues
  unfold posDefPow
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 2; ext i j; by_cases hij : i = j
  · subst hij; simp only [Matrix.diagonal_apply_eq, ← Complex.ofReal_mul]
    congr 1; exact (Real.rpow_add (hT.eigenvalues_pos i) r s).symm
  · simp [Matrix.diagonal, hij]

lemma posDefPow_one {n : ℕ} {T : Mat n} (hT : T.PosDef) : posDefPow 1 hT = T := by
  unfold posDefPow
  have h1 : Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ (1 : ℝ) : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (hT.isHermitian.eigenvalues i : ℂ)) := by
    congr 1; ext i; simp [Real.rpow_one]
  rw [h1]
  simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
    using hT.isHermitian.spectral_theorem.symm

lemma posDefPow_zero {n : ℕ} {T : Mat n} (hT : T.PosDef) : posDefPow 0 hT = 1 := by
  unfold posDefPow
  have h1 : Matrix.diagonal (fun i => (((hT.isHermitian.eigenvalues i) ^ (0 : ℝ) : ℝ) : ℂ)) = 1 := by
    ext i j; by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal, hij]
  rw [h1, Matrix.mul_one, unitary_mul_conjTranspose_self]

lemma posDefPow_eq_of_diag {n : ℕ} (r : ℝ) {T : Mat n} (hT : T.PosDef)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (d : Fin n → ℝ) (_hd : ∀ i, 0 < d i)
    (hTeq : T = (U : Mat n) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Mat n)ᴴ) :
    posDefPow r hT = (U : Mat n) * Matrix.diagonal (fun i => (((d i) ^ r : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
  let U0 := hT.isHermitian.eigenvectorUnitary
  let lam := hT.isHermitian.eigenvalues
  have hT0 : T = (U0 : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (U0 : Mat n)ᴴ := by
    simpa [U0, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hT.isHermitian.spectral_theorem
  let P : Mat n := (U : Mat n)ᴴ * (U0 : Mat n)
  have hcomm : P * Matrix.diagonal (fun i => (lam i : ℂ)) = Matrix.diagonal (fun i => (d i : ℂ)) * P := by
    have h1 : (U : Mat n)ᴴ * T * (U0 : Mat n) = (U : Mat n)ᴴ * T * (U0 : Mat n) := rfl
    conv_lhs at h1 => rw [hT0]
    conv_rhs at h1 => rw [hTeq]
    simp only [Matrix.mul_assoc] at h1
    rw [unitary_conjTranspose_mul_self U0, Matrix.mul_one,
      ← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul] at h1
    simpa [P, Matrix.mul_assoc] using h1
  have hcomm_r : P * Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ)) =
      Matrix.diagonal (fun i => (((d i) ^ r : ℝ) : ℂ)) * P := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hij := congr_fun (congr_fun hcomm i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hij
    by_cases hEq : d i = lam j
    · rw [hEq, mul_comm]
    · have hne : (lam j : ℂ) - (d i : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_sub, Complex.ofReal_ne_zero]; exact sub_ne_zero.mpr (Ne.symm hEq)
      have hP0 : P i j = 0 := by
        have : P i j * ((lam j : ℂ) - (d i : ℂ)) = 0 := by linear_combination hij
        exact (mul_eq_zero.mp this).resolve_right hne
      simp [hP0]
  unfold posDefPow
  calc (U0 : Mat n) * Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ)) * (U0 : Mat n)ᴴ
      = (U : Mat n) * (P * Matrix.diagonal (fun i => (((lam i) ^ r : ℝ) : ℂ))) * (U0 : Mat n)ᴴ := by
        simp only [P, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U : Mat n) (U : Mat n)ᴴ, unitary_mul_conjTranspose_self U, Matrix.one_mul]
    _ = (U : Mat n) * (Matrix.diagonal (fun i => (((d i) ^ r : ℝ) : ℂ)) * P) * (U0 : Mat n)ᴴ := by
        rw [hcomm_r]
    _ = (U : Mat n) * Matrix.diagonal (fun i => (((d i) ^ r : ℝ) : ℂ)) * (U : Mat n)ᴴ := by
        simp only [P, Matrix.mul_assoc]
        rw [unitary_mul_conjTranspose_self U0, Matrix.mul_one]

/-- The set of Theorem 5 PSD-splitting objective values:
    { ‖∑_k |W_k T^{-(1 - 1/p)}|‖_p^p | T ≻ 0, Tr(T) = 1, W_k ⪰ 0, ∑_k W_k = T }. -/
def psdObjectiveSet (p : ℝ) (m n : ℕ) : Set ℝ :=
  { val : ℝ | ∃ (T : Mat n) (hT : T.PosDef) (W : Fin m → Mat n),
      T.trace.re = 1 ∧ (∀ k, (W k).PosSemidef) ∧ (∑ k, W k = T) ∧
      val = schattenPow p (∑ k, matAbs (W k * posDefPow (-(1 - 1 / p)) hT)) }

/-- The set of Theorem 5 POVM objective values:
    { ‖∑_k |T^{1/2} X_k T^{1/p - 1/2}|‖_p^p | T ≻ 0, Tr(T) = 1, X_k ⪰ 0, ∑_k X_k = I }. -/
def povmObjectiveSet (p : ℝ) (m n : ℕ) : Set ℝ :=
  { val : ℝ | ∃ (T : Mat n) (hT : T.PosDef) (X : Fin m → Mat n),
      T.trace.re = 1 ∧ (∀ k, (X k).PosSemidef) ∧ (∑ k, X k = 1) ∧
      val = schattenPow p (∑ k, matAbs (posDefPow (1 / 2) hT * X k * posDefPow (1 / p - 1 / 2) hT)) }

set_option maxHeartbeats 600000 in
/-- Theorem 5 (Part A — Exact PSD-Splitting Infimum Reformulation):
    For every 1 < p < 2, m ≥ 2, n ≥ 1,
      (C_{p,m}(n))^{-p} = inf_{T ≻ 0, Tr(T)=1; W_k ⪰ 0, ∑ W_k = T} ‖∑_k |W_k T^{-(1-1/p)}|‖_p^p. -/
theorem theorem5_psd_reformulation {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (leeConst p m n) ^ (-p) = sInf (psdObjectiveSet p m n) := by
  have hp0 : 0 < p := by linarith
  have hC_pos : 0 < leeConst p m n := by
    obtain ⟨A, hH_ne, hC_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := n) hp1 (by omega) hn
    have h1 : leeConst p m 1 = 1 := leeConst_one_eq_one hp1 (by omega)
    have hmono : ∀ k : ℕ, 1 ≤ k → leeConst p m 1 ≤ leeConst p m k := by
      intro k hk; induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk0 : k = 0
        · subst hk0; exact le_rfl
        · exact (ih (by omega)).trans (leeConst_mono hp1 (by omega) (by omega))
    linarith [hmono n hn]
  -- Step 1: Lower bound: EVERY element of psdObjectiveSet is ≥ (leeConst p m n)^(-p)
  have hlb : ∀ val ∈ psdObjectiveSet p m n, (leeConst p m n) ^ (-p) ≤ val := by
    rintro val ⟨T, hT, W, hTr, _, hSumW, rfl⟩
    let α : ℝ := 1 - 1 / p
    let A : Fin m → Mat n := fun k => W k * posDefPow (-α) hT
    have hSumA : ∑ k, A k = posDefPow (1 / p) hT := by
      calc ∑ k, A k = (∑ k, W k) * posDefPow (-α) hT := (Finset.sum_mul ..).symm
        _ = T * posDefPow (-α) hT := by rw [hSumW]
        _ = posDefPow 1 hT * posDefPow (-α) hT := by rw [posDefPow_one hT]
        _ = posDefPow (1 + -α) hT := posDefPow_mul_posDefPow 1 (-α) hT
        _ = posDefPow (1 / p) hT := by congr 1; dsimp [α]; ring
    have hPowS : schattenPow p (∑ k, A k) = 1 := by
      rw [hSumA]; unfold posDefPow
      rw [schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
        schattenPow_diagonal hp0 _ (fun i => (Real.rpow_pos_of_pos (hT.eigenvalues_pos i) _).le)]
      have htr : T.trace.re = ∑ i : Fin n, hT.isHermitian.eigenvalues i := by
        have hTeq : T = (hT.isHermitian.eigenvectorUnitary : Mat n) *
            Matrix.diagonal (fun i => (hT.isHermitian.eigenvalues i : ℂ)) *
            (hT.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
          simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
            using hT.isHermitian.spectral_theorem
        conv_lhs => rw [hTeq]
        rw [Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self, Matrix.one_mul,
          Matrix.trace_diagonal, Complex.re_sum]; simp
      conv_rhs => rw [← hTr, htr]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Real.rpow_mul (hT.eigenvalues_pos i).le, one_div_mul_cancel hp0.ne', Real.rpow_one]
    have hH_ne : (∑ k, matAbs (A k)) ≠ 0 := by
      intro h0
      have hS0 : (∑ k, A k) = 0 := by
        have hH_psd : (∑ k, matAbs (A k)).PosSemidef := by
          have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
            intro s; induction s using Finset.induction_on with
            | empty => simpa using Matrix.PosSemidef.zero
            | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
          exact this Finset.univ
        have hAj0 : ∀ k, A k = 0 := fun k => by
          have htr0 : (matAbs (A k)).trace.re = 0 := by
            have hsum : ∑ j : Fin m, (matAbs (A j)).trace.re = 0 := by
              rw [← Complex.re_sum, ← Matrix.trace_sum, h0, Matrix.trace_zero, Complex.zero_re]
            have hnn : ∀ j, 0 ≤ (matAbs (A j)).trace.re := fun j => by
              simpa using re_trace_mul_nonneg_of_posSemidef (matAbs_posSemidef (A j)) Matrix.PosSemidef.one
            exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).mp hsum k (Finset.mem_univ k)
          have hPk0 : matAbs (A k) = 0 := by
            have h1 := matAbs_posSemidef (A k)
            have heig0 : ∀ i, h1.isHermitian.eigenvalues i = 0 := fun i =>
              le_antisymm ((posSemidef_eigenvalues_le_trace h1 i).trans (le_of_eq htr0)) (h1.eigenvalues_nonneg i)
            have hspec := h1.isHermitian.spectral_theorem
            have hd0 : Matrix.diagonal (RCLike.ofReal ∘ h1.isHermitian.eigenvalues) = (0 : Mat n) := by
              ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij, heig0]
            rw [hspec, hd0, map_zero]
          have hsq0 : (A k)ᴴ * A k = 0 := by rw [← matAbs_mul_self, hPk0, Matrix.zero_mul]
          have hpow0 : schattenPow 2 (A k) = 0 := by
            rw [← schattenPow_gram (by norm_num : (0 : ℝ) < 2) (A k), hsq0,
              schattenPow_zero (by norm_num : (0 : ℝ) < 2 / 2)]
          by_contra hne
          have := Real.rpow_pos_of_pos (schattenNorm_pos_of_ne_zero (by norm_num : (0 : ℝ) < 2) hne) 2
          rw [schattenNorm_rpow (by norm_num : (0 : ℝ) < 2)] at this; linarith
        exact Finset.sum_eq_zero fun k _ => hAj0 k
      rw [hS0, schattenPow_zero hp0] at hPowS; norm_num at hPowS
    have hratio_le : leeRatio p A ≤ leeConst p m n :=
      le_csSup (leeConst_bddAbove hp1) ⟨A, hH_ne, rfl⟩
    have hS_norm : schattenNorm p (∑ k, A k) = 1 := by
      unfold schattenNorm; rw [hPowS, Real.one_rpow]
    have hH_norm_pos : 0 < schattenNorm p (∑ k, matAbs (A k)) := schattenNorm_pos_of_ne_zero hp0 hH_ne
    have hH_ge : (leeConst p m n)⁻¹ ≤ schattenNorm p (∑ k, matAbs (A k)) := by
      unfold leeRatio at hratio_le; rw [hS_norm, one_div] at hratio_le
      exact (inv_le_comm₀ hH_norm_pos hC_pos).mp hratio_le
    have hpow := Real.rpow_le_rpow (inv_pos.mpr hC_pos).le hH_ge hp0.le
    rw [schattenNorm_rpow hp0, Real.inv_rpow hC_pos.le, ← Real.rpow_neg hC_pos.le] at hpow
    exact hpow
  -- Step 2: Construct ε → 0⁺ family in psdObjectiveSet converging to (leeConst p m n)^(-p)!
  obtain ⟨A0, hH0_ne, hC0_eq, hmax0⟩ := exists_leeConst_maximizer (m := m) (n := n) hp1 (by omega) hn
  set S0 : Mat n := ∑ k, A0 k
  set H0 : Mat n := ∑ k, matAbs (A0 k)
  have hS0_ne : S0 ≠ 0 := by
    intro h0
    have : leeRatio p A0 = 0 := by
      unfold leeRatio; change schattenNorm p S0 / schattenNorm p H0 = 0
      rw [h0, schattenNorm_zero hp0, zero_div]
    linarith
  -- Left-rotate A0 by V_S * U_Sᴴ so S1 := ∑ A1_k = V_S diag(σ) V_Sᴴ is PSD, then scale so ‖S1‖_p = 1!
  obtain ⟨U_S, V_S, σ, hσ, hS0_svd, _⟩ := exists_svd S0
  let rotU : Matrix.unitaryGroup (Fin n) ℂ := V_S * star U_S
  let c_sc : ℝ := (schattenNorm p S0)⁻¹
  have hc_sc_pos : 0 < c_sc := inv_pos.mpr (schattenNorm_pos_of_ne_zero hp0 hS0_ne)
  let A : Fin m → Mat n := fun k => (c_sc : ℂ) • ((rotU : Mat n) * A0 k)
  have hH_eq : ∑ k, matAbs (A k) = (c_sc : ℂ) • H0 := by
    have h1 : ∀ k, matAbs (A k) = (c_sc : ℂ) • matAbs (A0 k) := fun k => by
      change matAbs ((c_sc : ℂ) • ((rotU : Mat n) * A0 k)) = (c_sc : ℂ) • matAbs (A0 k)
      rw [matAbs_smul_real_nonneg hc_sc_pos.le, matAbs_unitary_mul]
    simp_rw [h1]; exact Finset.smul_sum.symm
  have hH_ne : (∑ k, matAbs (A k)) ≠ 0 := by
    rw [hH_eq]; intro h0
    have := smul_eq_zero.mp h0
    rcases this with hc | hh
    · exact (Complex.ofReal_ne_zero.mpr hc_sc_pos.ne') hc
    · exact hH0_ne hh
  have hS_diag : ∑ k, A k = (V_S : Mat n) * Matrix.diagonal (fun i => ((c_sc * σ i : ℝ) : ℂ)) * (V_S : Mat n)ᴴ := by
    have hsum : ∑ k, A k = (c_sc : ℂ) • ((rotU : Mat n) * S0) := by
      dsimp only [A, S0]; rw [← Finset.smul_sum, ← Matrix.mul_sum]
    rw [hsum, hS0_svd]
    have hrot : (rotU : Mat n) * (U_S : Mat n) = (V_S : Mat n) := by
      change (V_S : Mat n) * (U_S : Mat n)ᴴ * (U_S : Mat n) = (V_S : Mat n)
      rw [Matrix.mul_assoc, unitary_conjTranspose_mul_self U_S, Matrix.mul_one]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (rotU : Mat n) (U_S : Mat n), hrot]
    rw [← Matrix.mul_smul, ← Matrix.smul_mul]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal, hij]
  let d : Fin n → ℝ := fun i => c_sc * σ i
  have hd_nn : ∀ i, 0 ≤ d i := fun i => mul_nonneg hc_sc_pos.le (hσ i)
  have hPowS : schattenPow p (∑ k, A k) = 1 := by
    have h1 : ∑ k, A k = (c_sc : ℂ) • ((rotU : Mat n) * S0) := by
      dsimp [A]; rw [← Finset.smul_sum, ← Matrix.mul_sum]
    rw [h1, schattenPow_smul hp0, schattenPow_unitary_mul_left,
      Complex.norm_real, Real.norm_of_nonneg hc_sc_pos.le, ← schattenNorm_rpow hp0 S0,
      ← Real.mul_rpow hc_sc_pos.le (schattenNorm_nonneg p S0),
      inv_mul_cancel₀ (schattenNorm_pos_of_ne_zero hp0 hS0_ne).ne', Real.one_rpow]
  have hsum_dp : ∑ i : Fin n, (d i) ^ p = 1 := by
    rw [← hPowS, hS_diag, schattenPow_unitary_mul_conjTranspose_right hp0.le,
      schattenPow_unitary_mul_left, schattenPow_diagonal hp0 d hd_nn]
  have hratioA : leeRatio p A = leeConst p m n := by
    have h1 : ∑ k, A k = (c_sc : ℂ) • ((rotU : Mat n) * S0) := by
      dsimp [A]; rw [← Finset.smul_sum, ← Matrix.mul_sum]
    unfold leeRatio
    rw [h1, hH_eq, schattenNorm_smul hp0, schattenNorm_smul hp0,
      show schattenNorm p ((rotU : Mat n) * S0) = schattenNorm p S0 by
        unfold schattenNorm; rw [schattenPow_unitary_mul_left],
      mul_div_mul_left _ _ (norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hc_sc_pos.ne')).ne']
    exact hC0_eq
  have hPowH : schattenPow p (∑ k, matAbs (A k)) = (leeConst p m n) ^ (-p) := by
    have hS_norm : schattenNorm p (∑ k, A k) = 1 := by unfold schattenNorm; rw [hPowS, Real.one_rpow]
    have hH_norm : schattenNorm p (∑ k, matAbs (A k)) = (leeConst p m n)⁻¹ := by
      have h1 := hratioA; unfold leeRatio at h1; rw [hS_norm, one_div] at h1
      rw [← inv_inv (schattenNorm p _), h1]
    rw [← schattenNorm_rpow hp0, hH_norm, Real.inv_rpow hC_pos.le, ← Real.rpow_neg hC_pos.le]
  -- A maximizes leeRatio p on Mat n, so Lemma 3 gives W0_k := A_k * G_Sᴴ ⪰ 0 AND Same-Dim Lemma 2
  -- gives ker(S) ∩ ran(H) = {0}, hence ker(S) = ker(H) ⊆ ker(A_k)!
  have hmaxA : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) ≠ 0 → leeRatio p B ≤ leeRatio p A := by
    intro B hB; rw [hratioA]; exact le_csSup (leeConst_bddAbove hp1) ⟨B, hB, rfl⟩
  have hmaxA_polar : ∀ B : Fin m → Mat n, (∑ j, matAbs (B j)) = (∑ j, matAbs (A j)) →
      schattenPow p (∑ j, B j) ≤ schattenPow p (∑ j, A j) := by
    intro B hB
    have hle := hmaxA B (hB ▸ hH_ne)
    have hHpos : 0 < schattenNorm p (∑ j, matAbs (A j)) := schattenNorm_pos_of_ne_zero hp0 hH_ne
    have hnorm_le : schattenNorm p (∑ j, B j) ≤ schattenNorm p (∑ j, A j) := by
      unfold leeRatio at hle; rw [hB] at hle; exact (div_le_div_iff_of_pos_right hHpos).mp hle
    rw [← schattenNorm_rpow hp0, ← schattenNorm_rpow hp0]
    exact Real.rpow_le_rpow (schattenNorm_nonneg p _) hnorm_le hp0.le
  -- By Same-Dimension Lemma 2, ker(S) ∩ ran(H) = {0}, so for all k and all x with S x = 0, A_k x = 0!
  have hS_ne : (∑ k, A k) ≠ 0 := by
    intro h0; rw [h0, schattenPow_zero hp0] at hPowS; norm_num at hPowS
  have hkerS_le_Ak : ∀ k : Fin m, ∀ x : Fin n → ℂ, (∑ j, A j).mulVec x = 0 → (A k).mulVec x = 0 := by
    have hinj : ∀ z : Fin n → ℂ, z ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))) →
        (∑ j, A j).mulVec z = 0 → z = 0 := by
      intro z hz_ran hz_ker; by_contra hz_ne
      obtain ⟨A', hH', hlt⟩ := lemma2_same_dim_full_rank_sum hp1 hp2 A hS_ne hH_ne z hz_ne hz_ran hz_ker
      have hle := hmaxA A' (hH' ▸ hH_ne)
      linarith
    have hH_psd : (∑ j, matAbs (A j)).PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    have hkerH_le : ∀ k : Fin m, ∀ x : Fin n → ℂ, (∑ j, matAbs (A j)).mulVec x = 0 → (A k).mulVec x = 0 := by
      intro k x hx
      have hsum0 : ∑ i : Fin m, (star x ⬝ᵥ (matAbs (A i)).mulVec x).re = 0 := by
        have h1 : (star x ⬝ᵥ (∑ j, matAbs (A j)).mulVec x).re = 0 := by
          rw [hx, dotProduct_zero, Complex.zero_re]
        rw [← h1]; simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
      have hnn : ∀ i : Fin m, 0 ≤ (star x ⬝ᵥ (matAbs (A i)).mulVec x).re := fun i => by
        simpa [RCLike.re_to_complex] using (matAbs_posSemidef (A i)).re_dotProduct_nonneg x
      have hk0 : (star x ⬝ᵥ (matAbs (A k)).mulVec x).re = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hsum0 k (Finset.mem_univ k)
      have hPk0 := posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero (matAbs_posSemidef (A k)) x hk0
      have hAx_sq : (star ((A k).mulVec x) ⬝ᵥ (A k).mulVec x).re = 0 := by
        have h1 : star ((A k).mulVec x) ⬝ᵥ (A k).mulVec x = star x ⬝ᵥ ((A k)ᴴ * A k).mulVec x := by
          rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
        rw [h1, ← matAbs_mul_self, ← Matrix.mulVec_mulVec, hPk0, Matrix.mulVec_zero,
          dotProduct_zero, Complex.zero_re]
      have hE : ‖WithLp.toLp 2 ((A k).mulVec x)‖ ^ 2 = 0 := by
        have h1 : star ((A k).mulVec x) ⬝ᵥ (A k).mulVec x =
            inner ℂ (WithLp.toLp 2 ((A k).mulVec x)) (WithLp.toLp 2 ((A k).mulVec x)) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        rw [h1, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hAx_sq
        have h2 : (RCLike.ofReal (K := ℂ) (‖WithLp.toLp 2 ((A k).mulVec x)‖ ^ 2)).re =
            ‖WithLp.toLp 2 ((A k).mulVec x)‖ ^ 2 := by
          change ((‖WithLp.toLp 2 ((A k).mulVec x)‖ ^ 2 : ℝ) : ℂ).re = _
          exact Complex.ofReal_re _
        linarith
      exact congrArg WithLp.ofLp (norm_eq_zero.mp (sq_eq_zero_iff.mp hE))
    intro k x hx
    let V : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := LinearMap.range (Matrix.toEuclideanLin (∑ j, matAbs (A j)))
    let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
    let x1E := V.starProjection xE
    let x2E := xE - x1E
    have hHx2 : (∑ j, matAbs (A j)).mulVec x2E.ofLp = 0 := by
      have h1 : ∀ y : EuclideanSpace ℂ (Fin n),
          inner ℂ (Matrix.toEuclideanLin (∑ j, matAbs (A j)) y) x2E = 0 := fun y =>
        Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ y)
          (Submodule.sub_starProjection_mem_orthogonal xE)
      have h2 : Matrix.toEuclideanLin (∑ j, matAbs (A j)) x2E = 0 := by
        apply ext_inner_left ℂ; intro y
        have hadj : (Matrix.toEuclideanLin (∑ j, matAbs (A j))).adjoint =
            Matrix.toEuclideanLin (∑ j, matAbs (A j)) := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH_psd.isHermitian.eq]
        rw [inner_zero_right, ← hadj, LinearMap.adjoint_inner_right, h1 y]
      exact congrArg WithLp.ofLp h2
    have hSx2 : (∑ j, A j).mulVec x2E.ofLp = 0 := by
      rw [Matrix.sum_mulVec]; exact Finset.sum_eq_zero fun j _ => hkerH_le j _ hHx2
    have hx1_ran : x1E.ofLp ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))) := by
      obtain ⟨y, hy⟩ := Submodule.starProjection_apply_mem V xE
      exact ⟨y.ofLp, congrArg WithLp.ofLp hy⟩
    have hSx1 : (∑ j, A j).mulVec x1E.ofLp = 0 := by
      have hsplit : x = x1E.ofLp + x2E.ofLp := by ext i; simp [xE, x2E]
      rw [hsplit, Matrix.mulVec_add, hSx2, add_zero] at hx; exact hx
    have hx1_zero : x1E.ofLp = 0 := hinj x1E.ofLp hx1_ran hSx1
    have hx_eq : x = x2E.ofLp := by
      have hsplit : x = x1E.ofLp + x2E.ofLp := by ext i; simp [xE, x2E]
      rw [hsplit, hx1_zero, zero_add]
    rw [hx_eq]; exact hkerH_le k _ hHx2
  -- Define W0 k := A k * G_Sᴴ ⪰ 0 (by Lemma 3!) and T0 := V_S diag(d^p) V_Sᴴ!
  have hG_diag : (dualOp p (∑ k, A k))ᴴ =
      (V_S : Mat n) * Matrix.diagonal (fun i => (((d i) ^ (p - 1) : ℝ) : ℂ)) * (V_S : Mat n)ᴴ := by
    rw [dualOp_eq_of_svd hp1 V_S V_S d hd_nn hS_diag, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.mul_assoc]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp [Complex.conj_ofReal]
    · simp [Matrix.diagonal, hij]
  let W0 : Fin m → Mat n := fun k => A k * (dualOp p (∑ j, A j))ᴴ
  have hW0_psd : ∀ k, (W0 k).PosSemidef := fun k => lemma3_polar_optimality hp1 A hmaxA_polar k
  let T0 : Mat n := (V_S : Mat n) * Matrix.diagonal (fun i => (((d i) ^ p : ℝ) : ℂ)) * (V_S : Mat n)ᴴ
  have hSumW0 : ∑ k, W0 k = T0 := by
    dsimp only [W0, T0]; rw [← Finset.sum_mul, hG_diag, hS_diag]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V_S : Mat n)ᴴ (V_S : Mat n), unitary_conjTranspose_mul_self V_S,
      Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp only [Matrix.diagonal_apply_eq, ← Complex.ofReal_mul]
      congr 1; change d i * (d i) ^ (p - 1) = (d i) ^ p
      rcases eq_or_lt_of_le (hd_nn i) with h0 | hpos
      · rw [← h0, zero_mul, Real.zero_rpow hp0.ne']
      · calc d i * (d i) ^ (p - 1) = (d i) ^ (1 : ℝ) * (d i) ^ (p - 1) := by rw [Real.rpow_one]
          _ = (d i) ^ (1 + (p - 1)) := (Real.rpow_add hpos 1 (p - 1)).symm
          _ = (d i) ^ p := by ring_nf
    · simp [Matrix.diagonal, hij]
  -- Crucial support property: A k vanishes on every V_S column with d i = 0!
  have hAk_col_zero : ∀ k : Fin m, ∀ i : Fin n, d i = 0 →
      (A k).mulVec (fun a => (V_S : Mat n) a i) = 0 := by
    intro k i hdi
    apply hkerS_le_Ak k
    have hv_e : (fun a => (V_S : Mat n) a i) = (V_S : Mat n).mulVec (Pi.single i 1) := by
      ext a; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv_e, hS_diag, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (V_S : Mat n)ᴴ (V_S : Mat n), unitary_conjTranspose_mul_self V_S,
      Matrix.mul_one, ← Matrix.mulVec_mulVec]
    have hdiag0 : (Matrix.diagonal (fun j => (d j : ℂ))).mulVec (Pi.single i 1) = 0 := by
      ext j; by_cases hij : j = i
      · subst hij; simp [Matrix.mulVec_diagonal, hdi]
      · simp [Matrix.mulVec_diagonal, Pi.single_eq_of_ne hij]
    rw [hdiag0, Matrix.mulVec_zero]
  -- For every ε ∈ (0, 1), define T_ε = (1 - ε) T0 + (ε / n) I_n ≻ 0,
  -- W_ε k = (1 - ε) W0 k + (if k = 0 then (ε / n) I_n else 0) ⪰ 0!
  -- WAIT A SECOND!! Adding (ε/n) I_n across ALL coordinates (not just kernel!) is EVEN SIMPLER!
  -- Check: T_ε = V_S diag((1-ε) d_i^p + ε/n) V_Sᴴ ≻ 0 with Tr(T_ε) = (1-ε)*1 + ε = 1!
  -- And as ε → 0⁺:
  --   - On coordinates with d_i > 0: ((1-ε) d_i^p + ε/n)^(-(1-1/p)) → d_i^{-(p-1)},
  --     so W0_k * T_ε^{-(1-1/p)} → A_k!
  --   - On coordinates with d_i = 0: W0_k vanishes on V_S e_i, and (ε/n) I_n * T_ε^{-(1-1/p)}
  --     has diagonal entry (ε/n) * ((1-ε) d_i^p + ε/n)^{-(1-1/p)} ≤ (ε/n)^{1/p} → 0!
  --   SO A_k(ε) := W_ε k * T_ε^{-(1-1/p)} → A_k FOR EVERY SINGLE k AS ε → 0⁺!!
  --   NO KERNEL PROJECTION CASE SPLIT NEEDED AT ALL!!
  let k0 : Fin m := ⟨0, by omega⟩
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfamily : ∀ ε : ℝ, 0 < ε → ε < 1 →
      let dε : Fin n → ℝ := fun i => (1 - ε) * (d i) ^ p + ε / (n : ℝ)
      let Tε : Mat n := (V_S : Mat n) * Matrix.diagonal (fun i => (dε i : ℂ)) * (V_S : Mat n)ᴴ
      let Wε : Fin m → Mat n := fun k =>
        ((1 - ε : ℝ) : ℂ) • W0 k + if k = k0 then ((ε / (n : ℝ) : ℝ) : ℂ) • (1 : Mat n) else 0
      ∃ (hTε : Tε.PosDef),
        schattenPow p (∑ k, matAbs (Wε k * posDefPow (-(1 - 1 / p)) hTε)) ∈ psdObjectiveSet p m n ∧
        ∀ k, Wε k * posDefPow (-(1 - 1 / p)) hTε =
          A k * ((V_S : Mat n) * Matrix.diagonal (fun i =>
              ((((1 - ε) * (d i) ^ (p - 1) * (dε i) ^ (-(1 - 1 / p)) : ℝ) : ℂ))) * (V_S : Mat n)ᴴ) +
          if k = k0 then
            (V_S : Mat n) * Matrix.diagonal (fun i =>
              ((((ε / (n : ℝ)) * (dε i) ^ (-(1 - 1 / p)) : ℝ) : ℂ))) * (V_S : Mat n)ᴴ
          else 0 := by
    intro ε hε0 hε1 dε Tε Wε
    have hdε_pos : ∀ i : Fin n, 0 < dε i := fun i => by
      dsimp [dε]; have : 0 ≤ (1 - ε) * (d i) ^ p := mul_nonneg (by linarith) (Real.rpow_nonneg (hd_nn i) _)
      have : 0 < ε / (n : ℝ) := div_pos hε0 hn_pos
      linarith
    have hTε : Tε.PosDef := by
      have hd_pd : (Matrix.diagonal (fun i => (dε i : ℂ))).PosDef := by
        rw [Matrix.posDef_diagonal_iff]; intro i; exact_mod_cast hdε_pos i
      rw [Matrix.posDef_iff_dotProduct_mulVec]
      have hHerm : Tε.IsHermitian := by
        simpa [Tε] using (hd_pd.posSemidef.mul_mul_conjTranspose_same (V_S : Mat n)).isHermitian
      refine ⟨hHerm, fun x hx => ?_⟩
      let y := (V_S : Mat n)ᴴ.mulVec x
      have hy_ne : y ≠ 0 := by
        intro h0
        have h1 := congrArg (Matrix.mulVec (V_S : Mat n)) h0
        simp only [y, Matrix.mulVec_mulVec, unitary_mul_conjTranspose_self V_S, Matrix.one_mulVec,
          Matrix.mulVec_zero] at h1
        exact hx h1
      have hq : star x ⬝ᵥ Tε.mulVec x = star y ⬝ᵥ (Matrix.diagonal (fun i => (dε i : ℂ))).mulVec y := by
        dsimp [Tε]; simp only [Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
        rw [Matrix.dotProduct_mulVec]
        have : (star x) ᵥ* (V_S : Mat n) = star y := by
          simp only [y, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
        rw [this]
      rw [hq]; exact (Matrix.posDef_iff_dotProduct_mulVec.mp hd_pd).2 hy_ne
    have hTr_Tε : Tε.trace.re = 1 := by
      rw [show Tε = (V_S : Mat n) * Matrix.diagonal (fun i => (dε i : ℂ)) * (V_S : Mat n)ᴴ from rfl,
        Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self V_S, Matrix.one_mul,
        Matrix.trace_diagonal, Complex.re_sum]
      simp only [Complex.ofReal_re, dε, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_dp,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hn_pos.ne']; ring
    have hWε_psd : ∀ k, (Wε k).PosSemidef := fun k => by
      dsimp [Wε]
      have h1 : (((1 - ε : ℝ) : ℂ) • W0 k).PosSemidef := by
        have : ((1 - ε : ℝ) : ℂ) • W0 k = (1 - ε) • W0 k := by ext i j; simp [Complex.real_smul]
        rw [this]; exact (hW0_psd k).smul (by linarith)
      split_ifs
      · have h2 : (((ε / (n : ℝ) : ℝ) : ℂ) • (1 : Mat n)).PosSemidef := by
          have : ((ε / (n : ℝ) : ℝ) : ℂ) • (1 : Mat n) = (ε / (n : ℝ)) • (1 : Mat n) := by
            ext i j; simp [Complex.real_smul]
          rw [this]; exact Matrix.PosSemidef.one.smul (div_pos hε0 hn_pos).le
        exact h1.add h2
      · rw [add_zero]; exact h1
    have hSumWε : ∑ k, Wε k = Tε := by
      dsimp only [Wε]
      rw [Finset.sum_add_distrib, ← Finset.smul_sum, hSumW0]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have h1 : ((ε / (n : ℝ) : ℝ) : ℂ) • (1 : Mat n) =
          (V_S : Mat n) * Matrix.diagonal (fun _ => ((ε / (n : ℝ) : ℝ) : ℂ)) * (V_S : Mat n)ᴴ := by
        have hd : Matrix.diagonal (fun _ : Fin n => ((ε / (n : ℝ) : ℝ) : ℂ)) =
            ((ε / (n : ℝ) : ℝ) : ℂ) • (1 : Mat n) := by
          ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
        rw [hd, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, unitary_mul_conjTranspose_self V_S]
      have h2 : ((1 - ε : ℝ) : ℂ) • T0 =
          (V_S : Mat n) * Matrix.diagonal (fun i => ((((1 - ε) * (d i) ^ p : ℝ) : ℂ))) * (V_S : Mat n)ᴴ := by
        dsimp only [T0]; rw [← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2; ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
      rw [h2, h1, ← Matrix.add_mul, ← Matrix.mul_add]
      congr 2; ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal, dε, hij]
    have hPow_eq : posDefPow (-(1 - 1 / p)) hTε =
        (V_S : Mat n) * Matrix.diagonal (fun i => (((dε i) ^ (-(1 - 1 / p)) : ℝ) : ℂ)) * (V_S : Mat n)ᴴ :=
      posDefPow_eq_of_diag (-(1 - 1 / p)) hTε V_S dε hdε_pos rfl
    refine ⟨hTε, ⟨Tε, hTε, Wε, hTr_Tε, hWε_psd, hSumWε, rfl⟩, fun k => ?_⟩
    dsimp only [Wε]
    rw [Matrix.add_mul, Matrix.smul_mul, hPow_eq]
    congr 1
    · dsimp only [W0]; rw [hG_diag, Matrix.mul_assoc]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (V_S : Mat n)ᴴ (V_S : Mat n), unitary_conjTranspose_mul_self V_S,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      rw [← Matrix.mul_smul, ← Matrix.mul_smul, ← Matrix.smul_mul]
      congr 3; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
        push_cast; ring
      · simp [Matrix.diagonal, hij]
    · split_ifs
      · rw [Matrix.smul_mul, Matrix.one_mul, ← Matrix.smul_mul, ← Matrix.mul_smul]
        congr 2; ext i j; by_cases hij : i = j
        · subst hij; simp
        · simp [Matrix.diagonal, hij]
      · simp
  -- Step 3: Show sInf (psdObjectiveSet p m n) = (leeConst p m n)^(-p) by csInf_eq_iff!
  have hnonempty : (psdObjectiveSet p m n).Nonempty := by
    obtain ⟨hT, hmem, _⟩ := hfamily (1 / 2) (by norm_num) (by norm_num)
    exact ⟨_, hmem⟩
  have hbdd : BddBelow (psdObjectiveSet p m n) := ⟨(leeConst p m n) ^ (-p), hlb⟩
  apply le_antisymm
  · exact le_csInf hnonempty hlb
  · -- For every δ > 0, find ε ∈ (0, 1) with val(ε) ≤ (leeConst p m n)^(-p) + δ via continuity at ε = 0⁺!
    let M_fun : ℝ → Fin m → Mat n := fun ε k =>
      let dε : Fin n → ℝ := fun i => (1 - ε) * (d i) ^ p + ε / (n : ℝ)
      A k * ((V_S : Mat n) * Matrix.diagonal (fun i =>
          if d i = 0 then (0 : ℂ) else ((((1 - ε) * (d i) ^ (p - 1) * (dε i) ^ (-(1 - 1 / p)) : ℝ) : ℂ))) * (V_S : Mat n)ᴴ) +
      if k = k0 then
        (V_S : Mat n) * Matrix.diagonal (fun i =>
          ((((ε / (n : ℝ)) * (dε i) ^ (-(1 - 1 / p)) : ℝ) : ℂ))) * (V_S : Mat n)ᴴ
      else 0
    -- Check that M_fun ε k → A k as ε → 0⁺ for EVERY k!
    have hM_tend : ∀ k : Fin m, Filter.Tendsto (fun ε : ℝ => M_fun ε k)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (A k)) := by
      intro k
      have hdiag1_tend : Filter.Tendsto
          (fun ε : ℝ => Matrix.diagonal (fun i : Fin n =>
            if d i = 0 then (0 : ℂ)
            else ((((1 - ε) * (d i) ^ (p - 1) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)) : ℝ) : ℂ))))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Matrix.diagonal (fun i : Fin n => if d i = 0 then (0 : ℂ) else 1))) := by
        refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.diagonal_apply_eq]
          by_cases hdi : d i = 0
          · simp [hdi]
          · simp only [hdi, ↓reduceIte]
            have hdi_pos : 0 < d i := lt_of_le_of_ne (hd_nn i) (Ne.symm hdi)
            have hlim : Filter.Tendsto
                (fun ε : ℝ => (1 - ε) * (d i) ^ (p - 1) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)))
                (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
              have hcont : ContinuousAt
                  (fun ε : ℝ => (1 - ε) * (d i) ^ (p - 1) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p))) 0 := by
                refine ((continuousAt_const.sub continuousAt_id).mul continuousAt_const).mul ?_
                refine ContinuousAt.rpow_const ?_ (Or.inl ?_)
                · exact ((continuousAt_const.sub continuousAt_id).mul continuousAt_const).add
                    (continuousAt_id.div_const _)
                · simp [(Real.rpow_pos_of_pos hdi_pos p).ne']
              have hval : (1 - (0 : ℝ)) * (d i) ^ (p - 1) * ((1 - (0 : ℝ)) * (d i) ^ p + 0 / (n : ℝ)) ^ (-(1 - 1 / p)) = 1 := by
                simp only [sub_zero, one_mul, zero_div, add_zero]
                rw [← Real.rpow_mul hdi_pos.le, ← Real.rpow_add hdi_pos]
                have hexp : p - 1 + p * -(1 - 1 / p) = 0 := by field_simp [hp0.ne']; ring
                rw [hexp, Real.rpow_zero]
              convert hcont.tendsto.mono_left nhdsWithin_le_nhds
              exact hval.symm
            simpa only [Function.comp_def, Complex.ofReal_one] using
              (Complex.continuous_ofReal.tendsto 1).comp hlim
        · simp [Matrix.diagonal, hij]
      have hdiag2_tend : Filter.Tendsto
          (fun ε : ℝ => Matrix.diagonal (fun i : Fin n =>
            ((((ε / (n : ℝ)) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)) : ℝ) : ℂ))))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply]
          have hlim : Filter.Tendsto
              (fun ε : ℝ => (ε / (n : ℝ)) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            -- Squeeze between 0 and (ε / n)^(1 / p) → 0!
            have h0 : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
              tendsto_const_nhds
            have hup : Filter.Tendsto (fun ε : ℝ => (ε / (n : ℝ)) ^ (1 / p))
                (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              have h1 := ((Real.continuous_rpow_const (one_div_pos.mpr hp0).le).comp
                (continuous_id.div_const (n : ℝ))).tendsto 0
              simp only [Function.comp_def, id_eq, zero_div, Real.zero_rpow (one_div_pos.mpr hp0).ne'] at h1
              exact h1.mono_left nhdsWithin_le_nhds
            refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h0 hup ?_ ?_
            · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
              have h1me : 0 ≤ 1 - ε := by linarith only [hε.2]
              have hterm : 0 ≤ (1 - ε) * (d i) ^ p := mul_nonneg h1me (Real.rpow_nonneg (hd_nn i) p)
              have hεn : 0 < ε / (n : ℝ) := div_pos hε.1 hn_pos
              have hbase : 0 < (1 - ε) * (d i) ^ p + ε / (n : ℝ) := by linarith only [hterm, hεn]
              exact mul_nonneg hεn.le (Real.rpow_nonneg hbase.le _)
            · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
              have hεn : 0 < ε / (n : ℝ) := div_pos hε.1 hn_pos
              have h1me : 0 ≤ 1 - ε := by linarith only [hε.2]
              have hterm : 0 ≤ (1 - ε) * (d i) ^ p := mul_nonneg h1me (Real.rpow_nonneg (hd_nn i) p)
              have hbase_ge : ε / (n : ℝ) ≤ (1 - ε) * (d i) ^ p + ε / (n : ℝ) := by linarith only [hterm]
              have hpow_le : ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)) ≤
                  (ε / (n : ℝ)) ^ (-(1 - 1 / p)) :=
                Real.rpow_le_rpow_of_nonpos hεn hbase_ge (by
                  have : 1 / p < 1 := (div_lt_one hp0).mpr hp1; linarith)
              calc (ε / (n : ℝ)) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p))
                  ≤ (ε / (n : ℝ)) * (ε / (n : ℝ)) ^ (-(1 - 1 / p)) :=
                    mul_le_mul_of_nonneg_left hpow_le hεn.le
                _ = (ε / (n : ℝ)) ^ (1 : ℝ) * (ε / (n : ℝ)) ^ (-(1 - 1 / p)) := by rw [Real.rpow_one]
                _ = (ε / (n : ℝ)) ^ (1 / p) := by
                    rw [← Real.rpow_add hεn]; congr 1; ring
          simpa only [Function.comp_def, Complex.ofReal_zero] using
            (Complex.continuous_ofReal.tendsto 0).comp hlim
        · simp [Matrix.diagonal, hij]
      -- Limit of first term is A k * (V_S * diag(d ≠ 0) * V_Sᴴ) = A k (since A k vanishes on d = 0 cols)!
      have hAk_proj : A k * ((V_S : Mat n) * Matrix.diagonal (fun i : Fin n => if d i = 0 then (0 : ℂ) else 1) *
          (V_S : Mat n)ᴴ) = A k := by
        have hdiff : (1 : Mat n) - (V_S : Mat n) * Matrix.diagonal (fun i : Fin n => if d i = 0 then (0 : ℂ) else 1) * (V_S : Mat n)ᴴ =
            (V_S : Mat n) * Matrix.diagonal (fun i : Fin n => if d i = 0 then (1 : ℂ) else 0) * (V_S : Mat n)ᴴ := by
          have h1 : (1 : Mat n) = (V_S : Mat n) * (1 : Mat n) * (V_S : Mat n)ᴴ := by
            rw [Matrix.mul_one, unitary_mul_conjTranspose_self V_S]
          conv_lhs => rw [h1]
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
          congr 2; ext i j; by_cases hij : i = j
          · subst hij; by_cases hdi : d i = 0 <;> simp [Matrix.diagonal, hdi]
          · simp [Matrix.diagonal, hij]
        have hzero : A k * ((1 : Mat n) - (V_S : Mat n) * Matrix.diagonal (fun i : Fin n => if d i = 0 then (0 : ℂ) else 1) * (V_S : Mat n)ᴴ) = 0 := by
          rw [hdiff]
          have hmid : A k * ((V_S : Mat n) * Matrix.diagonal (fun i : Fin n => if d i = 0 then (1 : ℂ) else 0)) = 0 := by
            rw [← Matrix.mul_assoc]; ext a j
            simp only [Matrix.mul_diagonal, Matrix.zero_apply]
            by_cases hdj : d j = 0
            · simp only [hdj, ↓reduceIte, mul_one]
              exact congr_fun (hAk_col_zero k j hdj) a
            · simp [hdj]
          calc A k * ((V_S : Mat n) * Matrix.diagonal (fun i => if d i = 0 then (1 : ℂ) else 0) * (V_S : Mat n)ᴴ)
              = (A k * ((V_S : Mat n) * Matrix.diagonal (fun i => if d i = 0 then (1 : ℂ) else 0))) * (V_S : Mat n)ᴴ := by
                simp only [Matrix.mul_assoc]
            _ = 0 := by rw [hmid, Matrix.zero_mul]
        rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hzero
        exact hzero.symm
      have hterm1 : Filter.Tendsto (fun ε : ℝ => A k * ((V_S : Mat n) *
            Matrix.diagonal (fun i : Fin n => if d i = 0 then (0 : ℂ)
              else ((((1 - ε) * (d i) ^ (p - 1) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)) : ℝ) : ℂ))) *
            (V_S : Mat n)ᴴ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (A k)) := by
        have hlim1 := ((hdiag1_tend.const_mul (V_S : Mat n)).mul_const (V_S : Mat n)ᴴ).const_mul (A k)
        rwa [hAk_proj] at hlim1
      have hterm2 : Filter.Tendsto (fun ε : ℝ => if k = k0 then
            (V_S : Mat n) * Matrix.diagonal (fun i : Fin n =>
              ((((ε / (n : ℝ)) * ((1 - ε) * (d i) ^ p + ε / (n : ℝ)) ^ (-(1 - 1 / p)) : ℝ) : ℂ))) *
            (V_S : Mat n)ᴴ else 0) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        by_cases hk : k = k0
        · simp only [hk, ↓reduceIte]
          have h0_eq : (V_S : Mat n) * (0 : Mat n) * (V_S : Mat n)ᴴ = 0 := by simp
          have hlim2 := (hdiag2_tend.const_mul (V_S : Mat n)).mul_const (V_S : Mat n)ᴴ
          rwa [h0_eq] at hlim2
        · simp [hk]
      simpa [M_fun] using hterm1.add hterm2
    -- Continuity of schattenPow p (∑ k, matAbs (M_fun ε k)) gives convergence to (leeConst p m n)^(-p)!
    have hcont_pow : Continuous (fun M : Mat n => schattenPow p M) := by
      have heq : (fun M : Mat n => schattenPow p M) = fun M => (schattenNorm p M) ^ p := by
        ext M; exact (schattenNorm_rpow hp0 M).symm
      rw [heq]; exact (Real.continuous_rpow_const hp0.le).comp (continuous_schattenNorm hp1)
    have hval_tend : Filter.Tendsto
        (fun ε : ℝ => schattenPow p (∑ k : Fin m, matAbs (M_fun ε k)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((leeConst p m n) ^ (-p))) := by
      rw [← hPowH]
      have hsum_tend : Filter.Tendsto (fun ε : ℝ => ∑ k : Fin m, matAbs (M_fun ε k))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑ k : Fin m, matAbs (A k))) :=
        tendsto_finsetSum Finset.univ fun k _ => (continuous_matAbs.tendsto (A k)).comp (hM_tend k)
      exact (hcont_pow.tendsto _).comp hsum_tend
    -- Show sInf (psdObjectiveSet p m n) ≤ (leeConst p m n)^(-p) by le_of_tendsto!
    refine ge_of_tendsto hval_tend ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    obtain ⟨hTε, hmem, hform⟩ := hfamily ε hε.1 hε.2
    have heq_mat : ∀ k, M_fun ε k =
        (((1 - ε : ℝ) : ℂ) • W0 k + if k = k0 then ((ε / (n : ℝ) : ℝ) : ℂ) • (1 : Mat n) else 0) *
          posDefPow (-(1 - 1 / p)) hTε := fun k => by
      rw [hform k]; dsimp only [M_fun]
      congr 1; congr 1; congr 1; congr 1; congr 1; funext i
      by_cases hdi : d i = 0
      · simp only [hdi, ↓reduceIte, Real.zero_rpow (show p - 1 ≠ 0 by linarith), mul_zero,
          zero_mul, Complex.ofReal_zero]
      · simp only [hdi, ↓reduceIte]
    have hmem' : schattenPow p (∑ k : Fin m, matAbs (M_fun ε k)) ∈ psdObjectiveSet p m n := by
      simpa [heq_mat] using hmem
    exact csInf_le hbdd hmem'

/-- Theorem 5 (Part B — Exact POVM Reformulation):
    For every 1 < p < 2, m ≥ 2, n ≥ 1,
      (C_{p,m}(n))^{-p} = inf_{T ≻ 0, Tr(T)=1; X_k ⪰ 0, ∑ X_k = I} ‖∑_k |T^{1/2} X_k T^{1/p - 1/2}|‖_p^p. -/
theorem theorem5_povm_reformulation {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (leeConst p m n) ^ (-p) = sInf (povmObjectiveSet p m n) := by
  rw [theorem5_psd_reformulation hp1 hp2 hm hn]
  congr 1
  ext val
  constructor
  · rintro ⟨T, hT, W, hTr, hW_psd, hSumW, rfl⟩
    let Tmhalf : Mat n := posDefPow (-(1 / 2)) hT
    let Thalf : Mat n := posDefPow (1 / 2) hT
    have hTmhalf_herm : Tmhalfᴴ = Tmhalf := (posDefPow_posDef (-(1 / 2)) hT).isHermitian.eq
    let X : Fin m → Mat n := fun k => Tmhalf * W k * Tmhalf
    refine ⟨T, hT, X, hTr, fun k => ?_, ?_, ?_⟩
    · simpa [X, hTmhalf_herm] using (hW_psd k).conjTranspose_mul_mul_same Tmhalf
    · dsimp [X]
      rw [← Finset.sum_mul, ← Matrix.mul_sum, hSumW, ← posDefPow_one hT,
        posDefPow_mul_posDefPow, posDefPow_mul_posDefPow]
      have : -(1 / 2 : ℝ) + 1 + -(1 / 2) = 0 := by ring
      rw [this, posDefPow_zero]
    · apply congrArg (schattenPow p)
      refine Finset.sum_congr rfl fun k _ => congrArg matAbs ?_
      dsimp [X, Thalf, Tmhalf]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (posDefPow (1 / 2) hT) (posDefPow (-(1 / 2)) hT),
        posDefPow_mul_posDefPow, show (1 / 2 : ℝ) + -(1 / 2) = 0 by ring, posDefPow_zero,
        Matrix.one_mul, posDefPow_mul_posDefPow,
        show -(1 / 2 : ℝ) + (1 / p - 1 / 2) = -(1 - 1 / p) by ring]
  · rintro ⟨T, hT, X, hTr, hX_psd, hSumX, rfl⟩
    let Thalf : Mat n := posDefPow (1 / 2) hT
    have hThalf_herm : Thalfᴴ = Thalf := (posDefPow_posDef (1 / 2) hT).isHermitian.eq
    let W : Fin m → Mat n := fun k => Thalf * X k * Thalf
    refine ⟨T, hT, W, hTr, fun k => ?_, ?_, ?_⟩
    · simpa [W, hThalf_herm] using (hX_psd k).conjTranspose_mul_mul_same Thalf
    · dsimp [W]
      rw [← Finset.sum_mul, ← Matrix.mul_sum, hSumX, Matrix.mul_one, posDefPow_mul_posDefPow]
      have : (1 / 2 : ℝ) + (1 / 2) = 1 := by norm_num
      rw [this, posDefPow_one]
    · apply congrArg (schattenPow p)
      refine Finset.sum_congr rfl fun k _ => congrArg matAbs ?_
      dsimp [W, Thalf]
      simp only [Matrix.mul_assoc]
      rw [posDefPow_mul_posDefPow, show (1 / 2 : ℝ) + -(1 - 1 / p) = 1 / p - 1 / 2 by ring]

end MI20
