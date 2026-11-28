/-
  MI20/Lemma2_LeftRotation.lean
  =============================
  Author: Marcio Díaz (Space Research AI, https://spaceresearch.ai, marcio.diaz@gmail.com)
  Sublinear operator monotonicity (0 < q < 1) and Lemma 2 (full-rank sum via isometric left-rotation).
-/

import MI20.ExistenceAndPadding

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ### Elementary Helpers: Schatten Power of Gram Matrix & PSD Monotonicity for 0 < q < 1 -/

/-- Schatten p-power of A equals Schatten (p/2)-power of Aᴴ * A for all p > 0. -/
lemma schattenPow_gram {n : ℕ} {p : ℝ} (hp : 0 < p) (A : Mat n) :
    schattenPow (p / 2) (Aᴴ * A) = schattenPow p A := by
  obtain ⟨U, V, σ, hσ_nn, hSVD, hPow⟩ := exists_svd A
  have hD : (Matrix.diagonal (fun i => (σ i : ℂ)))ᴴ = Matrix.diagonal (fun i => (σ i : ℂ)) := by
    ext i j; by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hgram : Aᴴ * A = (V : Mat n) * Matrix.diagonal (fun i => (((σ i) ^ 2 : ℝ) : ℂ)) * (V : Mat n)ᴴ := by
    rw [hSVD]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hD, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Mat n)ᴴ (U : Mat n), unitary_conjTranspose_mul_self U, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp [sq]
    · simp [Matrix.diagonal, hij]
  have hp2 : 0 < p / 2 := half_pos hp
  rw [hgram, schattenPow_unitary_mul_conjTranspose_right hp2.le, schattenPow_unitary_mul_left,
    schattenPow_diagonal hp2 (fun i => (σ i) ^ 2) (fun i => sq_nonneg _), hPow p hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Real.rpow_two, ← Real.rpow_mul (hσ_nn i)]
  congr 1; ring

/-- Elementary PSD monotonicity of Schatten q-power for 0 < q < 1:
    0 ⪯ X ⪯ Y implies schattenPow q X ≤ schattenPow q Y.
    Proved directly via doubly-stochastic Parseval + Young's inequality (no Courant-Fischer!). -/
theorem schattenPow_mono_of_posSemidef_lt_one {n : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {X Y : Mat n} (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : (Y - X).PosSemidef) :
    schattenPow q X ≤ schattenPow q Y := by
  let Ux := hX.isHermitian.eigenvectorUnitary
  let lam := hX.isHermitian.eigenvalues
  let Uy := hY.isHermitian.eigenvectorUnitary
  let mu := hY.isHermitian.eigenvalues
  have hlam_nn : ∀ i, 0 ≤ lam i := hX.eigenvalues_nonneg
  have hmu_nn : ∀ j, 0 ≤ mu j := hY.eigenvalues_nonneg
  have hX_eq : X = (Ux : Mat n) * Matrix.diagonal (fun i => (lam i : ℂ)) * (Ux : Mat n)ᴴ := by
    simpa [Ux, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hX.isHermitian.spectral_theorem
  have hY_eq : Y = (Uy : Mat n) * Matrix.diagonal (fun j => (mu j : ℂ)) * (Uy : Mat n)ᴴ := by
    simpa [Uy, mu, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hY.isHermitian.spectral_theorem
  have hPowX : schattenPow q X = ∑ i : Fin n, (lam i) ^ q := by
    rw [hX_eq, schattenPow_unitary_mul_conjTranspose_right hq0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hq0 lam hlam_nn]
  have hPowY : schattenPow q Y = ∑ j : Fin n, (mu j) ^ q := by
    rw [hY_eq, schattenPow_unitary_mul_conjTranspose_right hq0.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hq0 mu hmu_nn]
  -- Define pseudo-inverse power G := Uy * diag(if mu j = 0 then 0 else (mu j)^(q-1)) * Uyᴴ ⪰ 0
  let gval : Fin n → ℝ := fun j => if mu j = 0 then 0 else (mu j) ^ (q - 1)
  have hgval_nn : ∀ j, 0 ≤ gval j := fun j => by
    dsimp [gval]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (hmu_nn j) _
  let G : Mat n := (Uy : Mat n) * Matrix.diagonal (fun j => (gval j : ℂ)) * (Uy : Mat n)ᴴ
  have hG_psd : G.PosSemidef := by
    have hd : (Matrix.diagonal (fun j => (gval j : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro j; exact_mod_cast hgval_nn j
    simpa [G] using hd.mul_mul_conjTranspose_same (Uy : Mat n)
  -- Since G ⪰ 0 and Y - X ⪰ 0, Re Tr(G * X) ≤ Re Tr(G * Y) = ∑ (mu j)^q
  have hTr_le : (G * X).trace.re ≤ (G * Y).trace.re := by
    have hnn := re_trace_mul_nonneg_of_posSemidef hG_psd hXY
    rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hnn
    linarith
  have hTrGY : (G * Y).trace.re = ∑ j : Fin n, (mu j) ^ q := by
    have hprod : G * Y = (Uy : Mat n) * Matrix.diagonal (fun j => (((mu j) ^ q : ℝ) : ℂ)) * (Uy : Mat n)ᴴ := by
      simp only [G]; conv_lhs => rw [hY_eq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Uy : Mat n)ᴴ (Uy : Mat n), unitary_conjTranspose_mul_self Uy,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp only [Matrix.diagonal_apply_eq, ← Complex.ofReal_mul]; congr 1
        dsimp [gval]; by_cases h0 : mu i = 0
        · simp [h0, Real.zero_rpow hq0.ne']
        · simp only [h0, ↓reduceIte]
          have hpos : 0 < mu i := lt_of_le_of_ne (hmu_nn i) (Ne.symm h0)
          rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
      · simp [Matrix.diagonal, hij]
    rw [hprod, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self Uy, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]
    simp
  -- Let Q := Uyᴴ * Ux (unitary), so Re Tr(G * X) = ∑ j, ∑ i, ‖Q j i‖^2 * gval j * lam i
  let Qu : Matrix.unitaryGroup (Fin n) ℂ := star Uy * Ux
  let Q : Mat n := (Qu : Mat n)
  have hTrGX : (G * X).trace.re = ∑ j : Fin n, ∑ i : Fin n, ‖Q j i‖ ^ 2 * (gval j * lam i) := by
    have hQeq : (Uy : Mat n)ᴴ * (Ux : Mat n) = Q := rfl
    have hQHeq : (Ux : Mat n)ᴴ * (Uy : Mat n) = Qᴴ := by
      change (Ux : Mat n)ᴴ * (Uy : Mat n) = ((Uy : Mat n)ᴴ * (Ux : Mat n))ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    set DG : Mat n := Matrix.diagonal (fun j => (gval j : ℂ))
    set DL : Mat n := Matrix.diagonal (fun i => (lam i : ℂ))
    have hprod : (G * X).trace = ((DG * Q) * (DL * Qᴴ)).trace := by
      have hG_eq : G = (Uy : Mat n) * DG * (Uy : Mat n)ᴴ := rfl
      calc (G * X).trace
          = ((Uy : Mat n) * (DG * ((Uy : Mat n)ᴴ * (Ux : Mat n)) * DL * (Ux : Mat n)ᴴ)).trace := by
              rw [hG_eq, hX_eq]; congr 1; simp only [Matrix.mul_assoc]
        _ = ((DG * Q * DL * (Ux : Mat n)ᴴ) * (Uy : Mat n)).trace := by
              rw [hQeq, Matrix.trace_mul_comm (Uy : Mat n)]
        _ = ((DG * Q) * (DL * ((Ux : Mat n)ᴴ * (Uy : Mat n)))).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DG * Q) * (DL * Qᴴ)).trace := by rw [hQHeq]
    rw [hprod, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, DG, DL, Matrix.diagonal_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Matrix.conjTranspose_apply]
    have hmul : ((gval j : ℂ) * Q j i * ((lam i : ℂ) * star (Q j i))) =
        (((gval j * lam i : ℝ) : ℂ) * (Q j i * star (Q j i))) := by push_cast; ring
    rw [hmul, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  have hRowQ : ∀ j : Fin n, ∑ i : Fin n, ‖Q j i‖ ^ 2 = 1 := by
    intro j
    have hU := congr_fun (congr_fun (unitary_mul_conjTranspose_self Qu) j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ‖Q j i‖ ^ 2 = (Q j i * star (Q j i)).re
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hColQ : ∀ i : Fin n, ∑ j : Fin n, ‖Q j i‖ ^ 2 = 1 := by
    intro i
    have hU := congr_fun (congr_fun (unitary_conjTranspose_mul_self Qu) i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at hU
    have hre := congrArg Complex.re hU
    simp only [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ‖Q j i‖ ^ 2 = (star (Q j i) * Q j i).re
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  -- Key kernel property: if mu j = 0 and lam i ≠ 0, then Q j i = 0!
  have hkerQ : ∀ j i : Fin n, mu j = 0 → lam i ≠ 0 → Q j i = 0 := by
    intro j i hmu0 hlam0
    -- w_j := column j of Uy satisfies Y w_j = 0 ⇒ X w_j = 0 ⇒ (Uxᴴ * X * Uy) i j = 0 ⇒ lam i * star(Q j i) = 0!
    let w : Fin n → ℂ := fun a => (Uy : Mat n) a j
    have hYw : Y.mulVec w = 0 := by
      have h1 : Y.mulVec w = (hY.isHermitian.eigenvectorBasis j |> Matrix.toEuclideanLin Y).ofLp := by
        ext a; simp [w, Uy, Matrix.IsHermitian.eigenvectorUnitary_apply, Matrix.toLpLin_apply,
          Matrix.toEuclideanLin]
      rw [h1]
      have h2 := hY.isHermitian.mulVec_eigenvectorBasis j
      change (Y.mulVec (hY.isHermitian.eigenvectorBasis j).ofLp) = _ at h2
      have h3 : (Matrix.toEuclideanLin Y (hY.isHermitian.eigenvectorBasis j)).ofLp =
          Y.mulVec (hY.isHermitian.eigenvectorBasis j).ofLp := rfl
      rw [h3, h2]
      change mu j • (hY.isHermitian.eigenvectorBasis j).ofLp = 0
      rw [hmu0, zero_smul]
    have hXw : X.mulVec w = 0 := by
      have h0 : (star w ⬝ᵥ Y.mulVec w).re = 0 := by rw [hYw, dotProduct_zero, Complex.zero_re]
      have hnn : 0 ≤ (star w ⬝ᵥ (Y - X).mulVec w).re := by
        simpa [RCLike.re_to_complex] using hXY.re_dotProduct_nonneg w
      rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at hnn
      have hge : 0 ≤ (star w ⬝ᵥ X.mulVec w).re := by
        simpa [RCLike.re_to_complex] using hX.re_dotProduct_nonneg w
      exact posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero hX w (by linarith)
    -- Now compute (Uxᴴ * (X * w)) i = 0, while Uxᴴ * X = diag(lam) * Uxᴴ gives lam i * (Uxᴴ * w) i = lam i * star(Q j i)!
    have hmul0 : ((Ux : Mat n)ᴴ.mulVec (X.mulVec w)) i = 0 := by rw [hXw, Matrix.mulVec_zero]; rfl
    have hmul_val : ((Ux : Mat n)ᴴ.mulVec (X.mulVec w)) i = (lam i : ℂ) * star (Q j i) := by
      rw [Matrix.mulVec_mulVec]
      have hprod : (Ux : Mat n)ᴴ * X = Matrix.diagonal (fun r => (lam r : ℂ)) * (Ux : Mat n)ᴴ := by
        rw [hX_eq]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Ux : Mat n)ᴴ (Ux : Mat n), unitary_conjTranspose_mul_self Ux, Matrix.one_mul]
      rw [hprod, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
      congr 1
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, w]
      have hq : Q j i = ∑ a : Fin n, star ((Uy : Mat n) a j) * (Ux : Mat n) a i := by
        change ((Uy : Mat n)ᴴ * (Ux : Mat n)) j i = _
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [hq, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_mul', star_star, mul_comm]
    rw [hmul_val] at hmul0
    have hstar0 : star (Q j i) = 0 :=
      (mul_eq_zero.mp hmul0).resolve_left (Complex.ofReal_ne_zero.mpr hlam0)
    simpa using congrArg star hstar0
  -- Pointwise Young bound: ‖Q j i‖^2 * (lam i)^q ≤ ‖Q j i‖^2 * (q * (gval j * lam i) + (1 - q) * (mu j)^q)
  have hterm : ∀ j i : Fin n,
      ‖Q j i‖ ^ 2 * (lam i) ^ q ≤
        ‖Q j i‖ ^ 2 * (q * (gval j * lam i) + (1 - q) * (mu j) ^ q) := by
    intro j i
    by_cases hlam0 : lam i = 0
    · rw [hlam0, Real.zero_rpow hq0.ne', mul_zero]
      exact mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg hq0.le (mul_nonneg (hgval_nn j) le_rfl))
        (mul_nonneg (by linarith) (Real.rpow_nonneg (hmu_nn j) q)))
    · by_cases hmu0 : mu j = 0
      · rw [hkerQ j i hmu0 hlam0]; simp
      · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have hmu_pos : 0 < mu j := lt_of_le_of_ne (hmu_nn j) (Ne.symm hmu0)
        have hlam_pos : 0 < lam i := lt_of_le_of_ne (hlam_nn i) (Ne.symm hlam0)
        have hg_eq : gval j = (mu j) ^ (q - 1) := by simp [gval, hmu0]
        rw [hg_eq]
        have hY := Real.geom_mean_le_arith_mean2_weighted hq0.le (by linarith : 0 ≤ 1 - q)
          (mul_nonneg (Real.rpow_nonneg hmu_pos.le (q - 1)) hlam_pos.le)
          (Real.rpow_nonneg hmu_pos.le q) (by ring)
        have hlhs : ((mu j) ^ (q - 1) * lam i) ^ q * ((mu j) ^ q) ^ (1 - q) = (lam i) ^ q := by
          rw [Real.mul_rpow (Real.rpow_nonneg hmu_pos.le _) hlam_pos.le,
            ← Real.rpow_mul hmu_pos.le, ← Real.rpow_mul hmu_pos.le]
          rw [mul_comm (((mu j) ^ ((q - 1) * q))) ((lam i) ^ q), mul_assoc,
            ← Real.rpow_add hmu_pos]
          have hexp : (q - 1) * q + q * (1 - q) = 0 := by ring
          rw [hexp, Real.rpow_zero, mul_one]
        rwa [hlhs] at hY
  rw [hPowX, hPowY]
  have hsum_le : ∑ i : Fin n, (lam i) ^ q ≤ q * (G * X).trace.re + (1 - q) * ∑ j : Fin n, (mu j) ^ q := by
    calc ∑ i : Fin n, (lam i) ^ q
        = ∑ i : Fin n, (∑ j : Fin n, ‖Q j i‖ ^ 2) * (lam i) ^ q := by
            refine Finset.sum_congr rfl fun i _ => by rw [hColQ i, one_mul]
      _ = ∑ j : Fin n, ∑ i : Fin n, ‖Q j i‖ ^ 2 * (lam i) ^ q := by
            simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ ≤ ∑ j : Fin n, ∑ i : Fin n, ‖Q j i‖ ^ 2 * (q * (gval j * lam i) + (1 - q) * (mu j) ^ q) :=
            Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hterm j i
      _ = (∑ j : Fin n, ∑ i : Fin n, q * (‖Q j i‖ ^ 2 * (gval j * lam i))) +
          (∑ j : Fin n, ∑ i : Fin n, ‖Q j i‖ ^ 2 * ((1 - q) * (mu j) ^ q)) := by
            simp_rw [mul_add, Finset.sum_add_distrib]
            congr 1; refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = q * (G * X).trace.re + (1 - q) * ∑ j : Fin n, (mu j) ^ q := by
            rw [hTrGX]
            congr 1
            · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum ..).symm
            · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
              rw [← Finset.sum_mul, hRowQ j, one_mul]
  nlinarith

/-! ### Rank-One Matrix Helper & Spectral Evaluation of (1 - β η) G₀ + η r₀ r₀ᴴ -/

/-- Outer product u * vᴴ as a matrix. -/
def outerMat {n : ℕ} (u v : Fin n → ℂ) : Mat n :=
  Matrix.of fun i j => u i * star (v j)

lemma outerMat_posSemidef {n : ℕ} (v : Fin n → ℂ) : (outerMat v v).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j; simp [outerMat, Matrix.conjTranspose_apply, mul_comm]
  · have hq : star x ⬝ᵥ (outerMat v v).mulVec x =
        star (star v ⬝ᵥ x) * (star v ⬝ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec, outerMat, Matrix.of_apply, Pi.star_apply,
        star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hq, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]
    exact_mod_cast sq_nonneg ‖star v ⬝ᵥ x‖

lemma outerMat_quad {n : ℕ} (u v x : Fin n → ℂ) :
    star x ⬝ᵥ (outerMat u v).mulVec x = (star x ⬝ᵥ u) * (star v ⬝ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec, outerMat, Matrix.of_apply, Pi.star_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Exact Schatten q-power of orthogonal sum c • G₀ + η • (r₀ r₀ᴴ) when G₀ ⪰ 0, r₀ ∈ ker(G₀), r₀ ≠ 0. -/
lemma schattenPow_add_kernel_rankOne {n : ℕ} {q : ℝ} (hq : 0 < q)
    {G0 : Mat n} (hG0 : G0.PosSemidef)
    {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η)
    (r0 : Fin n → ℂ) (hr0_ne : r0 ≠ 0) (hr0_ker : G0.mulVec r0 = 0) :
    schattenPow q ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) =
      c ^ q * schattenPow q G0 + (η * (∑ i : Fin n, ‖r0 i‖ ^ 2)) ^ q := by
  let b := hG0.isHermitian.eigenvectorBasis
  let lam := hG0.isHermitian.eigenvalues
  have hlam_nn : ∀ i, 0 ≤ lam i := hG0.eigenvalues_nonneg
  let Spos : Finset (Fin n) := Finset.univ.filter fun i => lam i ≠ 0
  let Szero : Finset (Fin n) := Finset.univ.filter fun i => lam i = 0
  have hPowG0 : schattenPow q G0 = ∑ i ∈ Spos, (lam i) ^ q := by
    have hG0_eq : G0 = (hG0.isHermitian.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => (lam i : ℂ)) * (hG0.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
      simpa [lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
        using hG0.isHermitian.spectral_theorem
    rw [hG0_eq, schattenPow_unitary_mul_conjTranspose_right hq.le, schattenPow_unitary_mul_left,
      schattenPow_diagonal hq lam hlam_nn]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => ?_
    have h0 : lam i = 0 := by simpa [Spos] using hi
    rw [h0, Real.zero_rpow hq.ne']
  -- Since r0 ∈ ker(G0) and r0 ≠ 0, Szero must be nonempty (otherwise G0 is injective)
  have hSzero_ne : Szero.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ i : Fin n, lam i ≠ 0 := by
      intro i hi
      have : i ∈ Szero := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hemp] at this; exact Finset.notMem_empty i this
    have hr0_0 : r0 = 0 := by
      let rE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 r0
      have hrep : ∀ i : Fin n, inner ℂ (b i) rE = 0 := by
        intro i
        have h1 : inner ℂ (Matrix.toEuclideanLin G0 (b i)) rE = 0 := by
          have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
            rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
          rw [← LinearMap.adjoint_inner_right, hadj]
          have : Matrix.toEuclideanLin G0 rE = 0 := WithLp.ofLp_injective 2 hr0_ker
          rw [this, inner_zero_right]
        have heig : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
          apply WithLp.ofLp_injective 2
          simpa [b, lam, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using hG0.isHermitian.mulVec_eigenvectorBasis i
        rw [heig, inner_smul_left, Complex.conj_ofReal] at h1
        exact (mul_eq_zero.mp h1).resolve_left (Complex.ofReal_ne_zero.mpr (hall i))
      have : rE = 0 := by
        rw [← b.sum_repr' rE]
        refine Finset.sum_eq_zero fun i _ => by rw [hrep i, zero_smul]
      exact congrArg WithLp.ofLp this
    exact hr0_ne hr0_0
  obtain ⟨i0, hi0_mem⟩ := hSzero_ne
  have hi0_lam : lam i0 = 0 := (Finset.mem_filter.mp hi0_mem).2
  -- Build unit vector rhat := r0 / ‖r0‖ ∈ ker(G0)
  let rE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 r0
  have hrE_ne : rE ≠ 0 := fun h => hr0_ne (congrArg WithLp.ofLp h)
  have hnorm_sq : ‖rE‖ ^ 2 = ∑ i : Fin n, ‖r0 i‖ ^ 2 := by
    simpa [rE, EuclideanSpace.norm_eq] using Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg ‖r0 i‖)
  have hrnorm_pos : 0 < ‖rE‖ := norm_pos_iff.mpr hrE_ne
  let rhat : EuclideanSpace ℂ (Fin n) := ((‖rE‖⁻¹ : ℝ) : ℂ) • rE
  have hrhat_norm : ‖rhat‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hrnorm_pos.le),
      inv_mul_cancel₀ hrnorm_pos.ne']
  -- rhat is orthogonal to every b i with i ∈ Spos
  have hrhat_orth : ∀ i ∈ Spos, inner ℂ (b i) rhat = 0 := by
    intro i hi
    have hlam_ne : lam i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hG0r : Matrix.toEuclideanLin G0 rhat = 0 := by
      apply WithLp.ofLp_injective 2
      change G0.mulVec (((‖rE‖⁻¹ : ℝ) : ℂ) • r0) = 0
      rw [Matrix.mulVec_smul, hr0_ker, smul_zero]
    have h1 : inner ℂ (Matrix.toEuclideanLin G0 (b i)) rhat = 0 := by
      have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
      rw [← LinearMap.adjoint_inner_right, hadj, hG0r, inner_zero_right]
    have heig : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
      apply WithLp.ofLp_injective 2
      simpa [b, lam, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using hG0.isHermitian.mulVec_eigenvectorBasis i
    rw [heig, inner_smul_left, Complex.conj_ofReal] at h1
    exact (mul_eq_zero.mp h1).resolve_left (Complex.ofReal_ne_zero.mpr hlam_ne)
  -- Index set S1 := insert i0 Spos; define orthonormal family v0 on S1 and extend on Srest := univ \ S1
  have hi0_not_Spos : i0 ∉ Spos := by simp [Spos, hi0_lam]
  let S1 : Finset (Fin n) := insert i0 Spos
  let Srest : Finset (Fin n) := Finset.univ \ S1
  let v0 : S1 → EuclideanSpace ℂ (Fin n) := fun i =>
    if hi : (i : Fin n) ∈ Spos then b i else rhat
  have hv0_orth : Orthonormal ℂ v0 := by
    rw [orthonormal_iff_ite]
    intro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [v0, Subtype.mk.injEq]
    by_cases hip : i ∈ Spos <;> by_cases hjp : j ∈ Spos
    · simp only [hip, hjp, ↓reduceDIte]
      exact orthonormal_iff_ite.mp b.orthonormal i j
    · have hij : i ≠ j := fun h => hjp (h ▸ hip)
      simp only [hip, hjp, ↓reduceDIte, hij, ↓reduceIte]
      exact hrhat_orth i hip
    · have hij : i ≠ j := fun h => hip (h.symm ▸ hjp)
      simp only [hip, hjp, ↓reduceDIte, hij, ↓reduceIte]
      rw [← inner_conj_symm, hrhat_orth j hjp, map_zero]
    · have hi' : i = i0 := (Finset.mem_insert.mp hi).resolve_right hip
      have hj' : j = i0 := (Finset.mem_insert.mp hj).resolve_right hjp
      subst hi'; subst hj'
      simp only [hip, ↓reduceDIte, ↓reduceIte, inner_self_eq_norm_sq_to_K, hrhat_norm]; norm_num
  let W : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Submodule.span ℂ (Set.range v0)
  let bWperp := stdOrthonormalBasis ℂ Wᗮ
  have hcardW : Module.finrank ℂ W = S1.card := by
    have hli : LinearIndependent ℂ v0 := hv0_orth.linearIndependent
    rw [finrank_span_eq_card hli, Fintype.card_coe]
  have hcardPerp : Module.finrank ℂ Wᗮ = Srest.card := by
    have hsum := Submodule.finrank_add_finrank_orthogonal W
    rw [finrank_euclideanSpace_fin, hcardW] at hsum
    have hcs : S1.card + Srest.card = n := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S1)
      simpa [Srest, add_comm] using this
    omega
  let ePerp : Srest ≃ Fin (Module.finrank ℂ Wᗮ) := Fintype.equivOfCardEq (by simp [hcardPerp])
  let uVec : Fin n → EuclideanSpace ℂ (Fin n) := fun i =>
    if hi : i ∈ S1 then v0 ⟨i, hi⟩ else (bWperp (ePerp ⟨i, by simp [Srest, hi]⟩) : EuclideanSpace ℂ (Fin n))
  have hu_orth : Orthonormal ℂ uVec := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : i ∈ S1 <;> by_cases hj : j ∈ S1
    · simp only [uVec, hi, hj, ↓reduceDIte]
      have := orthonormal_iff_ite.mp hv0_orth ⟨i, hi⟩ ⟨j, hj⟩
      simpa using this
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp only [uVec, hi, hj, ↓reduceDIte, hij, ↓reduceIte]
      have h1 : v0 ⟨i, hi⟩ ∈ W := Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
      have h2 : (bWperp (ePerp ⟨j, by simp [Srest, hj]⟩) : EuclideanSpace ℂ (Fin n)) ∈ Wᗮ := Submodule.coe_mem _
      exact Submodule.inner_right_of_mem_orthogonal h1 h2
    · have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp only [uVec, hi, hj, ↓reduceDIte, hij, ↓reduceIte]
      have h1 : v0 ⟨j, hj⟩ ∈ W := Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      have h2 : (bWperp (ePerp ⟨i, by simp [Srest, hi]⟩) : EuclideanSpace ℂ (Fin n)) ∈ Wᗮ := Submodule.coe_mem _
      exact Submodule.inner_left_of_mem_orthogonal h1 h2
    · simp only [uVec, hi, hj, ↓reduceDIte]
      have h1 := orthonormal_iff_ite.mp bWperp.orthonormal (ePerp ⟨i, by simp [Srest, hi]⟩) (ePerp ⟨j, by simp [Srest, hj]⟩)
      have h2 : (ePerp ⟨i, by simp [Srest, hi]⟩ = ePerp ⟨j, by simp [Srest, hj]⟩) ↔ i = j := by
        simp [ePerp.apply_eq_iff_eq]
      simpa [h2] using h1
  let Umat : Mat n := Matrix.of fun a k => (uVec k).ofLp a
  have hU_mem : Umat ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Umat, Matrix.of_apply, Matrix.one_apply]
    have hinner := orthonormal_iff_ite.mp hu_orth i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [dotProduct, mul_comm, eq_comm] using hinner
  let U : Matrix.unitaryGroup (Fin n) ℂ := ⟨Umat, hU_mem⟩
  -- Define target eigenvalues d : Fin n → ℝ
  let d : Fin n → ℝ := fun k =>
    if k ∈ Spos then c * lam k else if k = i0 then η * ‖rE‖ ^ 2 else 0
  have hd_nn : ∀ k, 0 ≤ d k := fun k => by
    dsimp [d]; split_ifs
    · exact mul_nonneg hc (hlam_nn k)
    · exact mul_nonneg hη (sq_nonneg _)
    · exact le_rfl
  -- Verify ((c • G0 + η • r0 r0ᴴ) *ᵥ uVec k) = d k • uVec k for all k!
  have hAct : ∀ k : Fin n,
      Matrix.toEuclideanLin ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) (uVec k) = (d k : ℂ) • uVec k := by
    intro k
    have houter_act : ∀ x : EuclideanSpace ℂ (Fin n),
        Matrix.toEuclideanLin (outerMat r0 r0) x = (inner ℂ rE x) • rE := by
      intro x
      apply WithLp.ofLp_injective 2
      ext a
      change ((outerMat r0 r0).mulVec x.ofLp) a = (inner ℂ rE x) * r0 a
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      simp [rE, outerMat, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    have hG0_orth : ∀ x : EuclideanSpace ℂ (Fin n), x ∈ Wᗮ → Matrix.toEuclideanLin G0 x = 0 := by
      intro x hx
      rw [← b.sum_repr' (Matrix.toEuclideanLin G0 x)]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : inner ℂ (b i) (Matrix.toEuclideanLin G0 x) = (lam i : ℂ) * inner ℂ (b i) x := by
        have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
        rw [← LinearMap.adjoint_inner_left, hadj]
        have heig : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
          apply WithLp.ofLp_injective 2
          simpa [b, lam, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using hG0.isHermitian.mulVec_eigenvectorBasis i
        rw [heig, inner_smul_left, Complex.conj_ofReal]
      rw [h1]
      by_cases hip : i ∈ Spos
      · have hbiW : b i ∈ W := by
          have : b i = v0 ⟨i, Finset.mem_insert_of_mem hip⟩ := by simp [v0, hip]
          rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
        rw [Submodule.inner_right_of_mem_orthogonal hbiW hx, mul_zero, zero_smul]
      · have h0 : lam i = 0 := by simpa [Spos] using hip
        rw [h0]; simp
    have hsplit : Matrix.toEuclideanLin ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) (uVec k) =
        (c : ℂ) • Matrix.toEuclideanLin G0 (uVec k) + (η : ℂ) • Matrix.toEuclideanLin (outerMat r0 r0) (uVec k) := by
      rw [map_add, map_smul, map_smul]
      rfl
    rw [hsplit, houter_act]
    by_cases hkp : k ∈ Spos
    · have hk1 : k ∈ S1 := Finset.mem_insert_of_mem hkp
      have hu : uVec k = b k := by simp [uVec, hk1, v0, hkp]
      rw [hu]
      have hG0b : Matrix.toEuclideanLin G0 (b k) = (lam k : ℂ) • b k := by
        apply WithLp.ofLp_injective 2
        simpa [b, lam, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using hG0.isHermitian.mulVec_eigenvectorBasis k
      have hrEb : inner ℂ rE (b k) = 0 := by
        have h1 : rE = ((‖rE‖ : ℝ) : ℂ) • rhat := by
          simp only [rhat, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hrnorm_pos.ne',
            Complex.ofReal_one, one_smul]
        rw [h1, inner_smul_left, ← inner_conj_symm, hrhat_orth k hkp, map_zero, mul_zero]
      rw [hG0b, hrEb, zero_smul, smul_zero, add_zero, smul_smul]
      simp [d, hkp]
    · by_cases hki0 : k = i0
      · rw [hki0]
        have hk1 : i0 ∈ S1 := Finset.mem_insert_self i0 Spos
        have hu : uVec i0 = rhat := by simp [uVec, hk1, v0, hi0_not_Spos]
        rw [hu]
        have hG0r : Matrix.toEuclideanLin G0 rhat = 0 := by
          apply WithLp.ofLp_injective 2
          change G0.mulVec (((‖rE‖⁻¹ : ℝ) : ℂ) • r0) = 0
          rw [Matrix.mulVec_smul, hr0_ker, smul_zero]
        have hrr : inner ℂ rE rhat = (‖rE‖ : ℂ) := by
          simp only [rhat, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
          have hcast : ((‖rE‖ ^ 2 : ℝ) : ℂ) = RCLike.ofReal (‖rE‖ ^ 2) := rfl
          rw [← hcast, ← Complex.ofReal_mul]; congr 1; field_simp [hrnorm_pos.ne']
        have hre : rE = (‖rE‖ : ℂ) • rhat := by
          simp only [rhat, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hrnorm_pos.ne',
            Complex.ofReal_one, one_smul]
        rw [hG0r, smul_zero, zero_add, hrr]
        conv_lhs => arg 2; arg 2; rw [hre]
        rw [smul_smul, smul_smul]
        simp only [d, hi0_not_Spos, ↓reduceIte, Complex.ofReal_mul, sq, mul_assoc]
      · have hk1 : k ∉ S1 := by simp [S1, hkp, hki0]
        have huWperp : uVec k ∈ Wᗮ := by simp [uVec, hk1]
        have hrEW : rE ∈ W := by
          have hrhatW : rhat ∈ W := by
            have : rhat = v0 ⟨i0, Finset.mem_insert_self i0 Spos⟩ := by simp [v0, hi0_not_Spos]
            rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
          have hre : rE = (‖rE‖ : ℂ) • rhat := by
            simp only [rhat, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hrnorm_pos.ne',
              Complex.ofReal_one, one_smul]
          rw [hre]; exact W.smul_mem _ hrhatW
        rw [hG0_orth (uVec k) huWperp, Submodule.inner_right_of_mem_orthogonal hrEW huWperp]
        simp [d, hkp, hki0]
  -- Deduce M = U * diag(d) * Uᴴ
  have hMatEq : (c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0 =
      (U : Mat n) * Matrix.diagonal (fun k => (d k : ℂ)) * (U : Mat n)ᴴ := by
    -- Check equality by multiplying both sides on the right by U (invertible since U * Uᴴ = 1)
    have hmul : ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) * (U : Mat n) =
        (U : Mat n) * Matrix.diagonal (fun k => (d k : ℂ)) := by
      ext a k
      have hcol : (((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) * (U : Mat n)) a k =
          (Matrix.toEuclideanLin ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) (uVec k)).ofLp a := by
        simp [Matrix.mul_apply, Matrix.toLpLin_apply, Matrix.toEuclideanLin, Matrix.mulVec,
          dotProduct, U, Umat, add_mul, Finset.sum_add_distrib, mul_assoc]
      rw [hcol, hAct k]
      simp [Matrix.mul_diagonal, U, Umat, mul_comm]
    calc (c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0
        = ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) * ((U : Mat n) * (U : Mat n)ᴴ) := by
            rw [unitary_mul_conjTranspose_self U, Matrix.mul_one]
      _ = ((c : ℂ) • G0 + (η : ℂ) • outerMat r0 r0) * (U : Mat n) * (U : Mat n)ᴴ := by
            rw [Matrix.mul_assoc]
      _ = (U : Mat n) * Matrix.diagonal (fun k => (d k : ℂ)) * (U : Mat n)ᴴ := by rw [hmul]
  rw [hMatEq, schattenPow_unitary_mul_conjTranspose_right hq.le, schattenPow_unitary_mul_left,
    schattenPow_diagonal hq d hd_nn, hPowG0, ← hnorm_sq]
  -- Split ∑ k, (d k)^q over Spos, {i0}, and rest
  have hsplit1 : ∑ k : Fin n, (d k) ^ q = ∑ k ∈ S1, (d k) ^ q := by
    symm; refine Finset.sum_subset (Finset.subset_univ S1) fun k _ hk => ?_
    have hkp : k ∉ Spos := fun h => hk (Finset.mem_insert_of_mem h)
    have hki0 : k ≠ i0 := fun h => hk (h ▸ Finset.mem_insert_self i0 Spos)
    simp [d, hkp, hki0, Real.zero_rpow hq.ne']
  rw [hsplit1, Finset.sum_insert hi0_not_Spos]
  have hi0_term : (d i0) ^ q = (η * ‖rE‖ ^ 2) ^ q := by simp [d, hi0_not_Spos]
  have hSpos_term : ∑ k ∈ Spos, (d k) ^ q = c ^ q * ∑ k ∈ Spos, (lam k) ^ q := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [d, hk, ↓reduceIte, Real.mul_rpow hc (hlam_nn k)]
  rw [hi0_term, hSpos_term, add_comm]

/-! ### Lemma 2: Left-Rotation Strict Improvement (Full-Rank Sum) -/

/-- Lemma 2 (Left-Rotation Strict Improvement): For 1 < p < 2, if S = ∑ A_j ≠ 0 and
    there exists a nonzero z ∈ ran(H) with S *ᵥ z = 0, then there exists an (n+1)-dimensional
    tuple Ã with strictly larger Lee ratio leeRatio p A < leeRatio p Ã. -/
theorem lemma2_full_rank_sum {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (A : Fin m → Mat n)
    (hS_ne : (∑ j, A j) ≠ 0)
    (hH_ne : (∑ j, matAbs (A j)) ≠ 0)
    (z : Fin n → ℂ) (hz_ne : z ≠ 0)
    (hz_ran : z ∈ LinearMap.range (Matrix.mulVecLin (∑ j, matAbs (A j))))
    (hz_ker : (∑ j, A j).mulVec z = 0) :
    ∃ A' : Fin m → Mat (n + 1), (∑ j, matAbs (A' j)) ≠ 0 ∧ leeRatio p A < leeRatio p A' := by
  have hp0 : 0 < p := by linarith
  set S : Mat n := ∑ j, A j
  set H : Mat n := ∑ j, matAbs (A j)
  have hH_psd : H.PosSemidef := by
    have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
      intro s; induction s using Finset.induction_on with
      | empty => simpa using Matrix.PosSemidef.zero
      | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
    exact this Finset.univ
  -- Step 1: z ∈ ran(H) \ {0} implies zᴴ H z > 0, so ∃ k0 with A k0 *ᵥ z ≠ 0!
  have hzH_pos : 0 < (star z ⬝ᵥ H.mulVec z).re := by
    have hge : 0 ≤ (star z ⬝ᵥ H.mulVec z).re := by
      simpa [RCLike.re_to_complex] using hH_psd.re_dotProduct_nonneg z
    refine lt_of_le_of_ne hge (Ne.symm fun h0 => ?_)
    have hHz0 : H.mulVec z = 0 := posSemidef_mulVec_eq_zero_of_re_dotProduct_eq_zero hH_psd z h0
    obtain ⟨y, hy⟩ := hz_ran
    have hy' : H.mulVec y = z := hy
    have hnorm : inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 z) = 0 := by
      have h1 : WithLp.toLp 2 z = Matrix.toEuclideanLin H (WithLp.toLp 2 y) :=
        WithLp.ofLp_injective 2 hy'.symm
      rw [h1]
      have hadj : (Matrix.toEuclideanLin H).adjoint = Matrix.toEuclideanLin H := by
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH_psd.isHermitian.eq]
      rw [← LinearMap.adjoint_inner_right, hadj, ← h1]
      have : Matrix.toEuclideanLin H (WithLp.toLp 2 z) = 0 := WithLp.ofLp_injective 2 hHz0
      rw [this, inner_zero_right]
    exact hz_ne (congrArg WithLp.ofLp (inner_self_eq_zero.mp hnorm))
  have hk0_ex : ∃ k0 : Fin m, (A k0).mulVec z ≠ 0 := by
    by_contra hall; push Not at hall
    have hzero : (star z ⬝ᵥ H.mulVec z).re = 0 := by
      have hH_sum : H.mulVec z = ∑ j : Fin m, (matAbs (A j)).mulVec z := by
        ext i; simp only [H, Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
        exact Finset.sum_comm
      have hPz0 : ∀ j : Fin m, (matAbs (A j)).mulVec z = 0 := by
        intro j
        have hsq : ((A j)ᴴ * A j).mulVec z = 0 := by
          rw [← Matrix.mulVec_mulVec, hall j, Matrix.mulVec_zero]
        have hdot : (star z ⬝ᵥ (matAbs (A j) * matAbs (A j)).mulVec z).re = 0 := by
          rw [matAbs_mul_self, hsq, dotProduct_zero, Complex.zero_re]
        have hPz_sq : (matAbs (A j)).mulVec ((matAbs (A j)).mulVec z) = 0 := by
          rw [Matrix.mulVec_mulVec, matAbs_mul_self]; exact hsq
        have hin : inner ℂ (Matrix.toEuclideanLin (matAbs (A j)) (WithLp.toLp 2 z))
            (Matrix.toEuclideanLin (matAbs (A j)) (WithLp.toLp 2 z)) = 0 := by
          have hadj : (Matrix.toEuclideanLin (matAbs (A j))).adjoint = Matrix.toEuclideanLin (matAbs (A j)) := by
            rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, (matAbs_isHermitian (A j)).eq]
          rw [← LinearMap.adjoint_inner_right, hadj]
          have : Matrix.toEuclideanLin (matAbs (A j)) (Matrix.toEuclideanLin (matAbs (A j)) (WithLp.toLp 2 z)) = 0 :=
            WithLp.ofLp_injective 2 hPz_sq
          rw [this, inner_zero_right]
        exact congrArg WithLp.ofLp (inner_self_eq_zero.mp hin)
      rw [hH_sum, Finset.sum_eq_zero (fun j _ => hPz0 j), dotProduct_zero, Complex.zero_re]
    linarith
  obtain ⟨k0, hk0_ne⟩ := hk0_ex
  -- Define unit vector w := (A k0 *ᵥ z) / ‖A k0 *ᵥ z‖ in ℂⁿ
  let wE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 ((A k0).mulVec z)
  have hwE_ne : wE ≠ 0 := fun h => hk0_ne (congrArg WithLp.ofLp h)
  have hwnorm_pos : 0 < ‖wE‖ := norm_pos_iff.mpr hwE_ne
  let whatE : EuclideanSpace ℂ (Fin n) := ((‖wE‖⁻¹ : ℝ) : ℂ) • wE
  let what : Fin n → ℂ := whatE.ofLp
  have hwhat_unit : star what ⬝ᵥ what = 1 := by
    have h1 : inner ℂ whatE whatE = 1 := by
      rw [inner_self_eq_norm_sq_to_K, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr hwnorm_pos.le), inv_mul_cancel₀ hwnorm_pos.ne']
      norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h1
    exact h1
  -- Set G0 := Sᴴ * S, r := (A k0)ᴴ *ᵥ what, q := Sᴴ *ᵥ what
  let G0 : Mat n := Sᴴ * S
  have hG0 : G0.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self S
  let r : Fin n → ℂ := (A k0)ᴴ.mulVec what
  let qv : Fin n → ℂ := Sᴴ.mulVec what
  -- Orthogonal decomposition of r into V_+ := ran(G0) and V_+ᗮ = ker(G0) = ker(S)
  let Vp : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := LinearMap.range (Matrix.toEuclideanLin G0)
  let rE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 r
  let r1E : EuclideanSpace ℂ (Fin n) := Vp.starProjection rE
  let r0E : EuclideanSpace ℂ (Fin n) := rE - r1E
  let r1 : Fin n → ℂ := r1E.ofLp
  let r0 : Fin n → ℂ := r0E.ofLp
  have hr_split : r = r1 + r0 := by change rE.ofLp = r1E.ofLp + (rE - r1E).ofLp; simp
  have hr0_kerG0 : G0.mulVec r0 = 0 := by
    have horth : r0E ∈ Vpᗮ := Submodule.sub_starProjection_mem_orthogonal rE
    have h2 : inner ℂ (Matrix.toEuclideanLin G0 r0E) (Matrix.toEuclideanLin G0 r0E) = 0 := by
      have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
      rw [← LinearMap.adjoint_inner_right, hadj]
      have hmem : Matrix.toEuclideanLin G0 (Matrix.toEuclideanLin G0 r0E) ∈ Vp := ⟨_, rfl⟩
      exact Submodule.inner_left_of_mem_orthogonal hmem horth
    exact congrArg WithLp.ofLp (inner_self_eq_zero.mp h2)
  -- Show r0 ≠ 0 because ⟨r0, z⟩ = ⟨r, z⟩ = ⟨what, A k0 z⟩ = ‖wE‖ > 0!
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
      have h1 : rE = (Matrix.toEuclideanLin (A k0)).adjoint whatE := by
        apply WithLp.ofLp_injective 2
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; rfl
      rw [h1, LinearMap.adjoint_inner_left]
      change inner ℂ whatE wE = (‖wE‖ : ℂ)
      simp only [whatE, inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K,
        ← RCLike.ofReal_pow]
      have hcast : ((‖wE‖ ^ 2 : ℝ) : ℂ) = RCLike.ofReal (‖wE‖ ^ 2) := rfl
      rw [← hcast, ← Complex.ofReal_mul]; congr 1; field_simp [hwnorm_pos.ne']
    have hr0_z : inner ℂ r0E (WithLp.toLp 2 z) = (‖wE‖ : ℂ) := by
      simp only [r0E, inner_sub_left, hr_z, hr1_z, sub_zero]
    intro h0
    have : r0E = 0 := WithLp.ofLp_injective 2 h0
    rw [this, inner_zero_left] at hr0_z
    exact (Complex.ofReal_ne_zero.mpr hwnorm_pos.ne') hr0_z.symm
  -- Show qv ∈ Vp (since qv = Sᴴ *ᵥ what is orthogonal to ker(G0) = ker(S))
  have hqv_Vp : WithLp.toLp 2 qv ∈ Vp := by
    have hVpp : Vp = (Vpᗮ)ᗮ := (Submodule.orthogonal_orthogonal Vp).symm
    rw [hVpp, Submodule.mem_orthogonal]
    intro x hx
    have hG0x : G0.mulVec x.ofLp = 0 := by
      have h2 : inner ℂ (Matrix.toEuclideanLin G0 x) (Matrix.toEuclideanLin G0 x) = 0 := by
        have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
        rw [← LinearMap.adjoint_inner_right, hadj]
        have hmem : Matrix.toEuclideanLin G0 (Matrix.toEuclideanLin G0 x) ∈ Vp := ⟨_, rfl⟩
        exact Submodule.inner_left_of_mem_orthogonal hmem hx
      exact congrArg WithLp.ofLp (inner_self_eq_zero.mp h2)
    have hSx : Matrix.toEuclideanLin S x = 0 := by
      have h2 : inner ℂ (Matrix.toEuclideanLin S x) (Matrix.toEuclideanLin S x) = 0 := by
        rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply, ← toEuclideanLin_gram]
        have : Matrix.toEuclideanLin G0 x = 0 := WithLp.ofLp_injective 2 hG0x
        rw [this, inner_zero_right]
      exact inner_self_eq_zero.mp h2
    have hq_adj : WithLp.toLp 2 qv = (Matrix.toEuclideanLin S).adjoint whatE := by
      apply WithLp.ofLp_injective 2
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]; rfl
    rw [hq_adj, LinearMap.adjoint_inner_right, hSx, inner_zero_left]
  -- Define v1 := r1 - (1/2) • qv ∈ Vp, and B1 := 2 v1 v1ᴴ + (1/2) qv qvᴴ
  let v1E : EuclideanSpace ℂ (Fin n) := r1E - ((1 / 2 : ℝ) : ℂ) • WithLp.toLp 2 qv
  let v1 : Fin n → ℂ := v1E.ofLp
  have hv1_Vp : v1E ∈ Vp := Vp.sub_mem (Submodule.starProjection_apply_mem Vp rE) (Vp.smul_mem _ hqv_Vp)
  -- Find β > 0 such that β • G0 - (2 • outerMat v1 v1 + (1/2) • outerMat qv qv) is PosSemidef!
  have hbeta : ∃ β : ℝ, 0 < β ∧
      ((β : ℂ) • G0 - ((2 : ℂ) • outerMat v1 v1 + ((1 / 2 : ℝ) : ℂ) • outerMat qv qv)).PosSemidef := by
    let b := hG0.isHermitian.eigenvectorBasis
    let lam := hG0.isHermitian.eigenvalues
    let Spos : Finset (Fin n) := Finset.univ.filter fun i => lam i ≠ 0
    have hSpos_ne : Spos.Nonempty := by
      by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have hG0_0 : G0 = 0 := by
        have hG0_eq : G0 = (hG0.isHermitian.eigenvectorUnitary : Mat n) *
            Matrix.diagonal (fun i => (lam i : ℂ)) * (hG0.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
          simpa [lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
            using hG0.isHermitian.spectral_theorem
        have hD0 : Matrix.diagonal (fun i => (lam i : ℂ)) = 0 := by
          ext i j; by_cases hij : i = j
          · subst hij
            have h0 : lam i = 0 := by
              by_contra hne
              have : i ∈ Spos := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
              rw [hemp] at this; exact Finset.notMem_empty i this
            simp [h0]
          · simp [Matrix.diagonal, hij]
        rw [hG0_eq, hD0, Matrix.mul_zero, Matrix.zero_mul]
      apply hS_ne
      have hpow : schattenPow (p / 2) G0 = 0 := by rw [hG0_0, schattenPow_zero (half_pos hp0)]
      rw [schattenPow_gram hp0 S] at hpow
      have hpos := (schattenPow_pos_iff hp0 S).mpr hS_ne
      linarith
    let lamMin : ℝ := Spos.inf' hSpos_ne lam
    have hlamMin_pos : 0 < lamMin := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact lt_of_le_of_ne (hG0.eigenvalues_nonneg i) (Ne.symm (Finset.mem_filter.mp hi).2)
    let β : ℝ := (2 * ‖v1E‖ ^ 2 + (1 / 2) * ‖WithLp.toLp 2 qv‖ ^ 2 + 1) / lamMin
    have hβ_pos : 0 < β := div_pos (by positivity) hlamMin_pos
    refine ⟨β, hβ_pos, ?_⟩
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    have hHerm : ((β : ℂ) • G0 - ((2 : ℂ) • outerMat v1 v1 + ((1 / 2 : ℝ) : ℂ) • outerMat qv qv)).IsHermitian := by
      rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
        hG0.isHermitian.eq, (outerMat_posSemidef v1).isHermitian.eq, (outerMat_posSemidef qv).isHermitian.eq]
      simp [Complex.conj_ofReal]
    refine ⟨hHerm, fun x => ?_⟩
    rw [Complex.nonneg_iff]
    refine ⟨?_, (isHermitian_im_dotProduct_mulVec_self hHerm x).symm⟩
    -- Project x onto Vp + Vpᗮ
    let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 x
    let xP : EuclideanSpace ℂ (Fin n) := Vp.starProjection xE
    let xK : EuclideanSpace ℂ (Fin n) := xE - xP
    have hxK_orth : xK ∈ Vpᗮ := Submodule.sub_starProjection_mem_orthogonal xE
    have hxK_kerG0 : G0.mulVec xK.ofLp = 0 := by
      have h2 : inner ℂ (Matrix.toEuclideanLin G0 xK) (Matrix.toEuclideanLin G0 xK) = 0 := by
        have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
          rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
        rw [← LinearMap.adjoint_inner_right, hadj]
        have hmem : Matrix.toEuclideanLin G0 (Matrix.toEuclideanLin G0 xK) ∈ Vp := ⟨_, rfl⟩
        exact Submodule.inner_left_of_mem_orthogonal hmem hxK_orth
      exact congrArg WithLp.ofLp (inner_self_eq_zero.mp h2)
    -- Bound xᴴ G0 x ≥ lamMin * ‖xP‖^2
    have hG0_lb : lamMin * ‖xP‖ ^ 2 ≤ (star x ⬝ᵥ G0.mulVec x).re := by
      have hxG0 : star x ⬝ᵥ G0.mulVec x = inner ℂ xE (Matrix.toEuclideanLin G0 xE) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; rfl
      rw [hxG0]
      have hexp : (inner ℂ xE (Matrix.toEuclideanLin G0 xE)).re = ∑ i : Fin n, lam i * ‖inner ℂ (b i) xE‖ ^ 2 := by
        nth_rw 2 [← b.sum_repr' xE]
        rw [map_sum, inner_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hterm : inner ℂ xE (Matrix.toEuclideanLin G0 (inner ℂ (b i) xE • b i)) =
            (lam i : ℂ) * ((‖inner ℂ (b i) xE‖ ^ 2 : ℝ) : ℂ) := by
          rw [map_smul, inner_smul_right]
          have heig : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
            apply WithLp.ofLp_injective 2
            simpa [b, lam, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using hG0.isHermitian.mulVec_eigenvectorBasis i
          have hsym : inner ℂ xE (b i) = (starRingEnd ℂ) (inner ℂ (b i) xE) :=
            (inner_conj_symm xE (b i)).symm
          rw [heig, inner_smul_right, hsym]
          have hcm : (starRingEnd ℂ) (inner ℂ (b i) xE) * inner ℂ (b i) xE = (‖inner ℂ (b i) xE‖ : ℂ) ^ 2 :=
            Complex.conj_mul' _
          calc inner ℂ (b i) xE * ((lam i : ℂ) * (starRingEnd ℂ) (inner ℂ (b i) xE))
              = (lam i : ℂ) * ((starRingEnd ℂ) (inner ℂ (b i) xE) * inner ℂ (b i) xE) := by ring
            _ = (lam i : ℂ) * (‖inner ℂ (b i) xE‖ : ℂ) ^ 2 := by rw [hcm]
            _ = (lam i : ℂ) * ((‖inner ℂ (b i) xE‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
        rw [hterm, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hexp]
      have hxP_sq : ‖xP‖ ^ 2 = ∑ i ∈ Spos, ‖inner ℂ (b i) xE‖ ^ 2 := by
        have hparseval : ‖xP‖ ^ 2 = ∑ i : Fin n, ‖inner ℂ (b i) xP‖ ^ 2 := by
          have := b.sum_sq_norm_inner_right xP
          simpa using this.symm
        rw [hparseval]
        have hzero : ∀ i : Fin n, i ∉ Spos → inner ℂ (b i) xP = 0 := by
          intro i hi
          have hlam0 : lam i = 0 := by simpa [Spos] using hi
          have hbi_orth : b i ∈ Vpᗮ := by
            rw [Submodule.mem_orthogonal]; rintro _ ⟨y, rfl⟩
            have hadj : (Matrix.toEuclideanLin G0).adjoint = Matrix.toEuclideanLin G0 := by
              rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hG0.isHermitian.eq]
            rw [← LinearMap.adjoint_inner_right, hadj]
            have heig : Matrix.toEuclideanLin G0 (b i) = 0 := by
              apply WithLp.ofLp_injective 2
              have := hG0.isHermitian.mulVec_eigenvectorBasis i
              simpa [b, lam, hlam0, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using this
            rw [heig, inner_zero_right]
          exact Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem Vp xE) hbi_orth
        have hsame : ∀ i ∈ Spos, inner ℂ (b i) xP = inner ℂ (b i) xE := by
          intro i hi
          have hlam_ne : lam i ≠ 0 := (Finset.mem_filter.mp hi).2
          have hbi_Vp : b i ∈ Vp := by
            refine ⟨((lam i)⁻¹ : ℂ) • b i, ?_⟩
            rw [map_smul]
            have heig : Matrix.toEuclideanLin G0 (b i) = (lam i : ℂ) • b i := by
              apply WithLp.ofLp_injective 2
              simpa [b, lam, Matrix.toLpLin_apply, Matrix.toEuclideanLin] using hG0.isHermitian.mulVec_eigenvectorBasis i
            rw [heig, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hlam_ne), one_smul]
          have hdiff : inner ℂ (b i) xK = 0 := Submodule.inner_right_of_mem_orthogonal hbi_Vp hxK_orth
          simp only [xK, inner_sub_right] at hdiff
          exact sub_eq_zero.mp hdiff |>.symm
        calc ∑ i : Fin n, ‖inner ℂ (b i) xP‖ ^ 2
            = ∑ i ∈ Spos, ‖inner ℂ (b i) xP‖ ^ 2 := by
                symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun i _ hi => by
                  rw [hzero i hi]; simp
          _ = ∑ i ∈ Spos, ‖inner ℂ (b i) xE‖ ^ 2 :=
                Finset.sum_congr rfl fun i hi => by rw [hsame i hi]
      rw [hxP_sq, Finset.mul_sum]
      calc ∑ i ∈ Spos, lamMin * ‖inner ℂ (b i) xE‖ ^ 2
          ≤ ∑ i ∈ Spos, lam i * ‖inner ℂ (b i) xE‖ ^ 2 :=
            Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (Finset.inf'_le lam hi) (sq_nonneg _)
        _ ≤ ∑ i : Fin n, lam i * ‖inner ℂ (b i) xE‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
              mul_nonneg (hG0.eigenvalues_nonneg i) (sq_nonneg _)
    -- Upper bound xᴴ (2 v1 v1ᴴ + (1/2) qv qvᴴ) x ≤ (2 ‖v1E‖^2 + (1/2) ‖qv‖^2) * ‖xP‖^2
    have hB1_ub : (star x ⬝ᵥ ((2 : ℂ) • outerMat v1 v1 + ((1 / 2 : ℝ) : ℂ) • outerMat qv qv).mulVec x).re ≤
        (2 * ‖v1E‖ ^ 2 + (1 / 2) * ‖WithLp.toLp 2 qv‖ ^ 2) * ‖xP‖ ^ 2 := by
      have hout : ∀ w : EuclideanSpace ℂ (Fin n), w ∈ Vp →
          (star x ⬝ᵥ (outerMat w.ofLp w.ofLp).mulVec x).re ≤ ‖w‖ ^ 2 * ‖xP‖ ^ 2 := by
        intro w hw
        rw [outerMat_quad]
        have hinner : star w.ofLp ⬝ᵥ x = inner ℂ w xE := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        have hinner_conj : star x ⬝ᵥ w.ofLp = (starRingEnd ℂ) (inner ℂ w xE) := by
          rw [← hinner]; simp only [dotProduct, Pi.star_apply, map_sum, map_mul, Complex.star_def,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
          refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]
        rw [hinner, hinner_conj, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
        have heq_P : inner ℂ w xE = inner ℂ w xP := by
          have h0 : inner ℂ w xK = 0 := Submodule.inner_right_of_mem_orthogonal hw hxK_orth
          simp only [xK, inner_sub_right] at h0
          exact sub_eq_zero.mp h0
        rw [heq_P]
        have hcs := norm_inner_le_norm (𝕜 := ℂ) w xP
        have hsq := pow_le_pow_left₀ (norm_nonneg _) hcs 2
        simpa [mul_pow] using hsq
      have h1 := hout v1E hv1_Vp
      have h2 := hout (WithLp.toLp 2 qv) hqv_Vp
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
        dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul,
        Complex.mul_re, Complex.mul_re]
      simp only [Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, Complex.ofReal_im]
      nlinarith
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, Complex.sub_re,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hβ_eq : β * lamMin = 2 * ‖v1E‖ ^ 2 + (1 / 2) * ‖WithLp.toLp 2 qv‖ ^ 2 + 1 :=
      div_mul_cancel₀ _ hlamMin_pos.ne'
    have hβ_mul : β * (lamMin * ‖xP‖ ^ 2) ≤ β * (star x ⬝ᵥ G0.mulVec x).re :=
      mul_le_mul_of_nonneg_left hG0_lb hβ_pos.le
    nlinarith [sq_nonneg ‖xP‖]
  obtain ⟨β, hβ_pos, hβ_psd⟩ := hbeta
  -- Step 2: Choose small η > 0 so that (1 - β η)^q ‖S‖_p^p + (η ‖r0‖^2)^q > ‖S‖_p^p!
  let q : ℝ := p / 2
  have hq0 : 0 < q := half_pos hp0
  have hq1 : q < 1 := by dsimp [q]; linarith
  have h1mq : 0 < 1 - q := by linarith
  let rn2 : ℝ := ∑ i : Fin n, ‖r0 i‖ ^ 2
  have hrn2_pos : 0 < rn2 := by
    have : ∃ i : Fin n, r0 i ≠ 0 := by
      by_contra h; push Not at h; exact hr0_ne (funext h)
    obtain ⟨i, hi⟩ := this
    have hpos : 0 < ‖r0 i‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hi)
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => ‖r0 j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  let D : ℝ := β * schattenPow p S + 1
  have hD_pos : 0 < D := by have := schattenPow_nonneg p S; positivity
  let η : ℝ := min (min (1 / 4) (1 / (2 * β))) ((rn2 ^ q / (2 * D)) ^ (1 / (1 - q)))
  have hη_pos : 0 < η := lt_min (lt_min (by norm_num) (by positivity))
    (Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hrn2_pos q) (by positivity)) _)
  have hη_le14 : η ≤ 1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hη_le_beta : β * η ≤ 1 / 2 := by
    have h1 : η ≤ 1 / (2 * β) := (min_le_left _ _).trans (min_le_right _ _)
    have := mul_le_mul_of_nonneg_left h1 hβ_pos.le
    rw [mul_one_div, div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hβ_pos.ne', one_mul] at this
    simpa [one_div] using this
  have hη_strict : β * schattenPow p S * η < (η * rn2) ^ q := by
    have h1 : η ^ (1 - q) ≤ rn2 ^ q / (2 * D) := by
      calc η ^ (1 - q) ≤ ((rn2 ^ q / (2 * D)) ^ (1 / (1 - q))) ^ (1 - q) :=
            Real.rpow_le_rpow hη_pos.le (min_le_right _ _) h1mq.le
        _ = rn2 ^ q / (2 * D) := by
            rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1mq.ne', Real.rpow_one]
    have h2 : D * η ^ (1 - q) < rn2 ^ q := by
      have hmul := mul_le_mul_of_nonneg_left h1 hD_pos.le
      have hsimp : D * (rn2 ^ q / (2 * D)) = rn2 ^ q / 2 := by field_simp [hD_pos.ne']
      rw [hsimp] at hmul
      linarith [Real.rpow_pos_of_pos hrn2_pos q]
    have h3 : (β * schattenPow p S) * η ^ (1 - q) < rn2 ^ q := by
      have hle : β * schattenPow p S ≤ D := by dsimp [D]; linarith
      have : (β * schattenPow p S) * η ^ (1 - q) ≤ D * η ^ (1 - q) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hη_pos.le _)
      linarith
    have h4 := mul_lt_mul_of_pos_left h3 (Real.rpow_pos_of_pos hη_pos q)
    rw [← Real.mul_rpow hη_pos.le hrn2_pos.le] at h4
    have hlhs : η ^ q * (β * schattenPow p S * η ^ (1 - q)) = β * schattenPow p S * η := by
      calc η ^ q * (β * schattenPow p S * η ^ (1 - q))
          = β * schattenPow p S * (η ^ q * η ^ (1 - q)) := by ring
        _ = β * schattenPow p S * η := by
            rw [← Real.rpow_add hη_pos, add_sub_cancel, Real.rpow_one]
    rwa [hlhs] at h4
  -- Step 3: Build the (n+1) × (n+1) Givens unitary Q and tuple A'
  let c : ℝ := 1 - η
  have hc_pos : 0 < c := by dsimp [c]; linarith
  let t : ℝ := Real.sqrt (2 * η - η ^ 2)
  have ht_sq : t ^ 2 = 2 * η - η ^ 2 := Real.sq_sqrt (by nlinarith)
  have hct_sq : c ^ 2 + t ^ 2 = 1 := by dsimp [c]; rw [ht_sq]; ring
  let whatp : Fin (n + 1) → ℂ := fun i => if hi : i.val < n then what ⟨i.val, hi⟩ else 0
  let elast : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1
  have hwp_unit : star whatp ⬝ᵥ whatp = 1 := by
    rw [← hwhat_unit]
    simp only [dotProduct, Pi.star_apply, whatp]
    rw [Fin.sum_univ_castSucc]
    simp [Fin.val_last, Fin.val_castSucc, Fin.is_lt]
  have hel_unit : star elast ⬝ᵥ elast = 1 := by
    simp [dotProduct, elast, Pi.single_apply]
  have hwp_el : star whatp ⬝ᵥ elast = 0 := by
    simp [dotProduct, whatp, elast, Pi.single_apply]
  have hel_wp : star elast ⬝ᵥ whatp = 0 := by
    simp only [dotProduct, Pi.star_apply, whatp, elast, Pi.single_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = Fin.last n
    · subst hx; simp
    · simp [hx]
  have houter_mul : ∀ a b x y : Fin (n + 1) → ℂ,
      outerMat a b * outerMat x y = (star b ⬝ᵥ x) • outerMat a y := by
    intro a b x y
    ext i j
    simp only [outerMat, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      dotProduct, Pi.star_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => by ring
  let Pmat : Mat (n + 1) := outerMat whatp whatp + outerMat elast elast
  let Jmat : Mat (n + 1) := outerMat elast whatp - outerMat whatp elast
  let Qmat : Mat (n + 1) := (1 : Mat (n + 1)) - (η : ℂ) • Pmat + (t : ℂ) • Jmat
  have hP_herm : Pmatᴴ = Pmat := by
    simp [Pmat, (outerMat_posSemidef whatp).isHermitian.eq, (outerMat_posSemidef elast).isHermitian.eq]
  have hJ_skew : Jmatᴴ = -Jmat := by
    ext i j; simp only [Jmat, outerMat, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.of_apply, star_sub, star_mul', star_star]; ring
  have hP_sq : Pmat * Pmat = Pmat := by
    simp only [Pmat, Matrix.add_mul, Matrix.mul_add, houter_mul, hwp_unit, hel_unit, hwp_el, hel_wp,
      one_smul, zero_smul, add_zero, zero_add]
  have hJ_sq : Jmat * Jmat = -Pmat := by
    simp only [Jmat, Pmat, Matrix.sub_mul, Matrix.mul_sub, houter_mul, hwp_unit, hel_unit,
      hwp_el, hel_wp, one_smul, zero_smul, sub_zero, zero_sub]
    abel
  have hPJ : Pmat * Jmat = Jmat := by
    simp only [Pmat, Jmat, Matrix.add_mul, Matrix.mul_sub, houter_mul, hwp_unit, hel_unit,
      hwp_el, hel_wp, one_smul, zero_smul]
    abel
  have hJP : Jmat * Pmat = Jmat := by
    simp only [Pmat, Jmat, Matrix.sub_mul, Matrix.mul_add, houter_mul, hwp_unit, hel_unit,
      hwp_el, hel_wp, one_smul, zero_smul, sub_zero, zero_sub]
    abel
  have hQ_mem : Qmat ∈ Matrix.unitaryGroup (Fin (n + 1)) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    have hQH' : Qmatᴴ = (1 : Mat (n + 1)) - (η : ℂ) • Pmat - (t : ℂ) • Jmat := by
      dsimp only [Qmat]
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, hP_herm, hJ_skew,
        Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal, smul_neg, ← sub_eq_add_neg]
    rw [Matrix.star_eq_conjTranspose, hQH']
    have hηt : (-2 * (η : ℂ) + (η : ℂ) ^ 2 + (t : ℂ) ^ 2) = 0 := by
      have : (t : ℂ) ^ 2 = 2 * (η : ℂ) - (η : ℂ) ^ 2 := by exact_mod_cast ht_sq
      rw [this]; ring
    calc ((1 : Mat (n + 1)) - (η : ℂ) • Pmat - (t : ℂ) • Jmat) *
            ((1 : Mat (n + 1)) - (η : ℂ) • Pmat + (t : ℂ) • Jmat)
        = (1 : Mat (n + 1)) + (-2 * (η : ℂ) + (η : ℂ) ^ 2 + (t : ℂ) ^ 2) • Pmat := by
            simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add,
              Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
              hP_sq, hJ_sq, hPJ, hJP, smul_neg]
            ext i j; simp; ring
      _ = 1 := by rw [hηt, zero_smul, add_zero]
  let Qu : Matrix.unitaryGroup (Fin (n + 1)) ℂ := ⟨Qmat, hQ_mem⟩
  let A' : Fin m → Mat (n + 1) := Function.update (fun j => padZero (A j)) k0 (Qmat * padZero (A k0))
  -- Moduli sum of A' equals padZero H!
  have hH'_eq : ∑ j, matAbs (A' j) = padZero H := by
    have h1 : ∀ j, matAbs (A' j) = padZero (matAbs (A j)) := by
      intro j
      by_cases hjk : j = k0
      · subst hjk
        simp only [A', Function.update_self]
        change matAbs ((Qu : Mat (n + 1)) * padZero (A j)) = padZero (matAbs (A j))
        rw [matAbs_unitary_mul, matAbs_padZero]
      · simp [A', Function.update_of_ne hjk, matAbs_padZero]
    simp_rw [h1]
    exact padZero_sum _ _
  have hH'_ne : ∑ j, matAbs (A' j) ≠ 0 := by
    rw [hH'_eq]
    intro h0; exact hH_ne (padZero_injective (h0.trans padZero_zero.symm))
  -- Compute S' := ∑ j, A' j and its Gram matrix S'ᴴ * S' = padZero (G0 + η (2 r rᴴ - qv rᴴ - r qvᴴ))!
  let rp : Fin (n + 1) → ℂ := fun i => if hi : i.val < n then r ⟨i.val, hi⟩ else 0
  let qp : Fin (n + 1) → ℂ := fun i => if hi : i.val < n then qv ⟨i.val, hi⟩ else 0
  have hel_pad : ∀ B : Mat n, outerMat whatp elast * padZero B = 0 ∧ outerMat elast elast * padZero B = 0 := by
    intro B
    constructor <;> (
      ext i j
      simp only [outerMat, padZero, elast, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply,
        Pi.single_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = Fin.last n
      · subst hl; simp
      · simp [hl])
  have hwp_Ak0 : outerMat whatp whatp * padZero (A k0) = outerMat whatp rp ∧
      outerMat elast whatp * padZero (A k0) = outerMat elast rp := by
    have hrow : ∀ j : Fin (n + 1), ∑ l : Fin (n + 1), star (whatp l) * padZero (A k0) l j = star (rp j) := by
      intro j
      rw [Fin.sum_univ_castSucc]
      simp only [whatp, padZero, Matrix.of_apply, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
        star_zero, zero_mul, add_zero, Fin.val_castSucc, Fin.is_lt]
      by_cases hj : j.val < n
      · simp only [hj, ↓reduceDIte, rp]
        have hrj : r ⟨j.val, hj⟩ = ∑ l : Fin n, star ((A k0) l ⟨j.val, hj⟩) * what l := by
          simp [r, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
        rw [hrj, star_sum]
        refine Finset.sum_congr rfl fun l _ => by rw [star_mul', star_star, mul_comm]
      · simp [hj, rp]
    constructor <;> (
      ext i j
      simp only [outerMat, Matrix.mul_apply, Matrix.of_apply, mul_assoc, ← Finset.mul_sum, hrow j])
  have hS'_eq : ∑ j, A' j = padZero S - (η : ℂ) • outerMat whatp rp + (t : ℂ) • outerMat elast rp := by
    have hsum1 := Finset.sum_update_of_mem (Finset.mem_univ k0) (fun j => padZero (A j)) (Qmat * padZero (A k0))
    change ∑ j, Function.update (fun j => padZero (A j)) k0 (Qmat * padZero (A k0)) j = _
    rw [hsum1, Finset.sdiff_singleton_eq_erase]
    have hsum_er : ∑ j ∈ Finset.univ.erase k0, padZero (A j) = padZero S - padZero (A k0) := by
      have h2 := Finset.add_sum_erase Finset.univ (fun j => padZero (A j)) (Finset.mem_univ k0)
      rw [padZero_sum Finset.univ A] at h2
      change padZero (A k0) + _ = padZero S at h2
      rw [← h2]; abel
    rw [hsum_er]
    have hQ_Ak0 : Qmat * padZero (A k0) = padZero (A k0) - (η : ℂ) • outerMat whatp rp + (t : ℂ) • outerMat elast rp := by
      simp only [Qmat, Pmat, Jmat, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
        (hel_pad (A k0)).1, (hel_pad (A k0)).2, hwp_Ak0.1, hwp_Ak0.2, add_zero, sub_zero]
    rw [hQ_Ak0]; abel
  -- Now compute S'ᴴ * S' = padZero M_eta!
  let M_eta : Mat n := G0 + (η : ℂ) • ((2 : ℂ) • outerMat r r - outerMat qv r - outerMat r qv)
  have hS'_gram : (∑ j, A' j)ᴴ * (∑ j, A' j) = padZero M_eta := by
    have hSp_what : (padZero S)ᴴ * outerMat whatp rp = outerMat qp rp := by
      ext i j
      simp only [padZero, outerMat, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [whatp, Fin.val_last, lt_self_iff_false, ↓reduceDIte, mul_zero, zero_mul, add_zero,
        Fin.val_castSucc, Fin.is_lt]
      by_cases hi : i.val < n
      · simp only [hi, ↓reduceDIte, qp, ← mul_assoc, ← Finset.sum_mul]
        congr 1
      · simp [hi, qp]
    have hSp_el : (padZero S)ᴴ * outerMat elast rp = 0 := by
      ext i j
      simp only [padZero, outerMat, elast, Matrix.mul_apply, Matrix.of_apply,
        Matrix.conjTranspose_apply, Matrix.zero_apply, Pi.single_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = Fin.last n
      · subst hl; simp
      · simp [hl]
    have hwhat_Sp : (outerMat whatp rp)ᴴ * padZero S = outerMat rp qp := by
      have h1 := congrArg Matrix.conjTranspose hSp_what
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h1
      rw [h1]; ext i j
      simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
    have hel_Sp : (outerMat elast rp)ᴴ * padZero S = 0 := by
      have h1 := congrArg Matrix.conjTranspose hSp_el
      simpa [Matrix.conjTranspose_mul] using h1
    have hout_H : ∀ a b : Fin (n + 1) → ℂ, (outerMat a b)ᴴ = outerMat b a := fun a b => by
      ext i j; simp only [outerMat, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul', star_star]; ring
    -- Expand (X - Y + Z)ᴴ * (X - Y + Z) cleanly without simp explosion!
    have hexp9 : ∀ X Y Z : Mat (n + 1),
        (X - Y + Z)ᴴ * (X - Y + Z) =
          Xᴴ * X - Xᴴ * Y + Xᴴ * Z - Yᴴ * X + Yᴴ * Y - Yᴴ * Z + Zᴴ * X - Zᴴ * Y + Zᴴ * Z := by
      intro X Y Z
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.add_mul, Matrix.sub_mul,
        Matrix.mul_add, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_sub]
      abel
    rw [hS'_eq, hexp9]
    have hT1 : (padZero S)ᴴ * ((η : ℂ) • outerMat whatp rp) = (η : ℂ) • outerMat qp rp := by
      rw [Matrix.mul_smul, hSp_what]
    have hT2 : (padZero S)ᴴ * ((t : ℂ) • outerMat elast rp) = 0 := by
      rw [Matrix.mul_smul, hSp_el, smul_zero]
    have hT3 : ((η : ℂ) • outerMat whatp rp)ᴴ * padZero S = (η : ℂ) • outerMat rp qp := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, hwhat_Sp]
    have hT4 : ((η : ℂ) • outerMat whatp rp)ᴴ * ((η : ℂ) • outerMat whatp rp) = ((η : ℂ) * (η : ℂ)) • outerMat rp rp := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, hout_H, houter_mul, hwp_unit, one_smul, smul_smul]
    have hT5 : ((η : ℂ) • outerMat whatp rp)ᴴ * ((t : ℂ) • outerMat elast rp) = 0 := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, hout_H, houter_mul, hwp_el, zero_smul, smul_zero, smul_zero]
    have hT6 : ((t : ℂ) • outerMat elast rp)ᴴ * padZero S = 0 := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, hel_Sp, smul_zero]
    have hT7 : ((t : ℂ) • outerMat elast rp)ᴴ * ((η : ℂ) • outerMat whatp rp) = 0 := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, hout_H, houter_mul, hel_wp, zero_smul, smul_zero, smul_zero]
    have hT8 : ((t : ℂ) • outerMat elast rp)ᴴ * ((t : ℂ) • outerMat elast rp) = ((t : ℂ) * (t : ℂ)) • outerMat rp rp := by
      rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, hout_H, houter_mul, hel_unit, one_smul, smul_smul]
    rw [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8]
    have hηt2 : (η : ℂ) * (η : ℂ) + (t : ℂ) * (t : ℂ) = (η : ℂ) * 2 := by
      have : (t : ℂ) ^ 2 = 2 * (η : ℂ) - (η : ℂ) ^ 2 := by exact_mod_cast ht_sq
      linear_combination this
    have hpad_outer : ∀ u v : Fin n → ℂ,
        outerMat (fun i : Fin (n + 1) => if hi : i.val < n then u ⟨i.val, hi⟩ else 0)
                 (fun i : Fin (n + 1) => if hi : i.val < n then v ⟨i.val, hi⟩ else 0) =
        padZero (outerMat u v) := fun u v => by
      ext i j; simp only [outerMat, padZero, Matrix.of_apply]
      by_cases hi : i.val < n <;> by_cases hj : j.val < n <;> simp [hi, hj]
    have hrr : outerMat rp rp = padZero (outerMat r r) := hpad_outer r r
    have hqr : outerMat qp rp = padZero (outerMat qv r) := hpad_outer qv r
    have hrq : outerMat rp qp = padZero (outerMat r qv) := hpad_outer r qv
    have hG0p : (padZero S)ᴴ * padZero S = padZero G0 := by
      rw [padZero_conjTranspose, ← padZero_mul]
    rw [hG0p, hrr, hqr, hrq]
    ext i j
    simp only [M_eta, padZero, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul, add_zero, sub_zero]
    by_cases hi : i.val < n <;> by_cases hj : j.val < n
    · simp only [hi, hj, ↓reduceDIte]
      linear_combination (outerMat r r ⟨i.val, hi⟩ ⟨j.val, hj⟩) * hηt2
    · simp [hi, hj]
    · simp [hi]
    · simp [hi]
  -- Step 4: Square-completion Loewner lower bound: M_eta ⪰ (1 - β η) • G0 + η • outerMat r0 r0!
  let L_eta : Mat n := ((1 - β * η : ℝ) : ℂ) • G0 + (η : ℂ) • outerMat r0 r0
  have hL_psd : L_eta.PosSemidef := by
    have h1 : (((1 - β * η : ℝ) : ℂ) • G0) = (1 - β * η) • G0 := by ext i j; simp [Complex.real_smul]
    have h2 : ((η : ℂ) • outerMat r0 r0) = η • outerMat r0 r0 := by ext i j; simp [Complex.real_smul]
    rw [show L_eta = _ + _ from rfl, h1, h2]
    exact (hG0.smul (by linarith)).add ((outerMat_posSemidef r0).smul hη_pos.le)
  have hM_psd : M_eta.PosSemidef := by
    have h1 : (padZero M_eta).PosSemidef := by rw [← hS'_gram]; exact Matrix.posSemidef_conjTranspose_mul_self _
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h1 ⊢
    refine ⟨?_, fun x => ?_⟩
    · have := congrArg Matrix.conjTranspose (rfl : padZero M_eta = padZero M_eta)
      ext i j
      have h := congr_fun (congr_fun h1.1.eq i.castSucc) j.castSucc
      simpa [padZero_conjTranspose, padZero, i.isLt, j.isLt] using h
    · let xp : Fin (n + 1) → ℂ := fun i => if hi : i.val < n then x ⟨i.val, hi⟩ else 0
      have hq : star x ⬝ᵥ M_eta.mulVec x = star xp ⬝ᵥ (padZero M_eta).mulVec xp := by
        simp only [dotProduct, Matrix.mulVec, Pi.star_apply, padZero, Matrix.of_apply, xp]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_last, lt_self_iff_false, ↓reduceDIte, star_zero, zero_mul, add_zero,
          Fin.val_castSucc, Fin.is_lt]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1; rw [Fin.sum_univ_castSucc]; simp [Fin.val_last, Fin.val_castSucc, Fin.is_lt]
      rw [hq]; exact h1.2 xp
  have hML_psd : (M_eta - L_eta).PosSemidef := by
    -- Exact algebraic identity:
    -- M_eta - L_eta = η • (2 v1 + r0)(2 v1 + r0)ᴴ + η • (β G0 - (2 v1 v1ᴴ + (1/2) qv qvᴴ))!
    have hdecomp : M_eta - L_eta =
        η • outerMat ((2 : ℂ) • v1 + r0) ((2 : ℂ) • v1 + r0) +
        η • ((β : ℂ) • G0 - ((2 : ℂ) • outerMat v1 v1 + ((1 / 2 : ℝ) : ℂ) • outerMat qv qv)) := by
      have hv1_def : ∀ i, v1 i = r1 i - (1 / 2 : ℂ) * qv i := fun i => by
        simp [v1, v1E, r1]
      have hr_def : ∀ i, r i = r1 i + r0 i := fun i => congr_fun hr_split i
      ext i j
      simp only [M_eta, L_eta, outerMat, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
        star_add, star_mul', star_sub, hv1_def, hr_def]
      simp only [Complex.star_def, map_ofNat, map_div₀, map_one]
      push_cast; ring
    rw [hdecomp]
    exact ((outerMat_posSemidef _).smul hη_pos.le).add (hβ_psd.smul hη_pos.le)
  -- Step 5: Combine monotonicity + exact spectral formula + η choice to get ‖S‖_p^p < ‖S'‖_p^p!
  have hPowS'_gt : schattenPow p S < schattenPow p (∑ j, A' j) := by
    have h1 : schattenPow p (∑ j, A' j) = schattenPow q M_eta := by
      rw [← schattenPow_gram hp0 (∑ j, A' j), hS'_gram, schattenPow_padZero hq0]
    have h2 : schattenPow q L_eta ≤ schattenPow q M_eta :=
      schattenPow_mono_of_posSemidef_lt_one hq0 hq1 hL_psd hM_psd hML_psd
    have h3 : schattenPow q L_eta = (1 - β * η) ^ q * schattenPow p S + (η * rn2) ^ q := by
      have hG0_pow : schattenPow q G0 = schattenPow p S := schattenPow_gram hp0 S
      rw [← hG0_pow]
      exact schattenPow_add_kernel_rankOne hq0 hG0 (by linarith) hη_pos.le r0 hr0_ne hr0_kerG0
    -- For 0 ≤ 1 - β η ≤ 1 and 0 < q < 1, (1 - β η)^q ≥ 1 - β η!
    have hconc : 1 - β * η ≤ (1 - β * η) ^ q := by
      have hx0 : 0 ≤ 1 - β * η := by linarith
      have hx1 : 1 - β * η ≤ 1 := by nlinarith
      simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hq0.le hq1.le
    have h4 : (1 - β * η) * schattenPow p S ≤ (1 - β * η) ^ q * schattenPow p S :=
      mul_le_mul_of_nonneg_right hconc (schattenPow_nonneg p S)
    linarith
  -- Step 6: Conclude leeRatio p A < leeRatio p A' since ‖H'‖_p = ‖H‖_p!
  refine ⟨A', hH'_ne, ?_⟩
  have hH'_norm : schattenNorm p (∑ j, matAbs (A' j)) = schattenNorm p H := by
    rw [hH'_eq, schattenNorm_padZero hp0]
  have hH_pos : 0 < schattenNorm p H := (schattenNorm_pos_iff hp0 H).mpr hH_ne
  rw [leeRatio, leeRatio, hH'_norm]
  exact div_lt_div_of_pos_right
    (Real.rpow_lt_rpow (schattenPow_nonneg p S) hPowS'_gt (one_div_pos.mpr hp0)) hH_pos

end MI20
