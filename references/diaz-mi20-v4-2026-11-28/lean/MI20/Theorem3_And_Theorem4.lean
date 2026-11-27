/-
  MI20/Theorem3_And_Theorem4.lean
  ===============================
  Authors: Marcio Díaz (Space Research AI, https://spaceresearch.ai)
  Complete Mathlib-grounded, zero-sorry Lean 4.33.1 formalization of:
    - Theorem 3: Universal 2×2 collapse C_{p,m}(2) = C_{p,2}(2) for all 1 < p < 2, m ≥ 2,
                 exact 2×2 variational formula, and exact closed form at p = 3/2:
                   C_{3/2,m}(2) = ((107 + 51 * √17) / 256)^(1/6).
    - Theorem 4: Pure-integer operator-monotone Sylvester-minor certificate proving
                 end-to-end in Mathlib that the explicit two-digit 3×3 pair
                   A = [[49, 62, -1], [11, 14, 0], [0, 0, 0]],  B = diag(81, 0, 0)
                 strictly beats C_{3/2,m}(2), certifying C_{3/2,2}(2) < C_{3/2,2}(3).
-/

import MI20.Lemma4_And_Theorem1

set_option autoImplicit false

namespace MI20.Cert3

/-- Exact 3×3 integer matrix stored as 9 explicit entries (instant kernel `decide` reduction). -/
structure Mat3 where
  m00 : ℤ
  m01 : ℤ
  m02 : ℤ
  m10 : ℤ
  m11 : ℤ
  m12 : ℤ
  m20 : ℤ
  m21 : ℤ
  m22 : ℤ
  deriving DecidableEq

namespace Mat3

def add (X Y : Mat3) : Mat3 :=
  ⟨X.m00 + Y.m00, X.m01 + Y.m01, X.m02 + Y.m02,
   X.m10 + Y.m10, X.m11 + Y.m11, X.m12 + Y.m12,
   X.m20 + Y.m20, X.m21 + Y.m21, X.m22 + Y.m22⟩

def sub (X Y : Mat3) : Mat3 :=
  ⟨X.m00 - Y.m00, X.m01 - Y.m01, X.m02 - Y.m02,
   X.m10 - Y.m10, X.m11 - Y.m11, X.m12 - Y.m12,
   X.m20 - Y.m20, X.m21 - Y.m21, X.m22 - Y.m22⟩

def scale (c : ℤ) (X : Mat3) : Mat3 :=
  ⟨c * X.m00, c * X.m01, c * X.m02,
   c * X.m10, c * X.m11, c * X.m12,
   c * X.m20, c * X.m21, c * X.m22⟩

def trans (X : Mat3) : Mat3 :=
  ⟨X.m00, X.m10, X.m20,
   X.m01, X.m11, X.m21,
   X.m02, X.m12, X.m22⟩

def mul (X Y : Mat3) : Mat3 :=
  ⟨X.m00*Y.m00 + X.m01*Y.m10 + X.m02*Y.m20,
   X.m00*Y.m01 + X.m01*Y.m11 + X.m02*Y.m21,
   X.m00*Y.m02 + X.m01*Y.m12 + X.m02*Y.m22,
   X.m10*Y.m00 + X.m11*Y.m10 + X.m12*Y.m20,
   X.m10*Y.m01 + X.m11*Y.m11 + X.m12*Y.m21,
   X.m10*Y.m02 + X.m11*Y.m12 + X.m12*Y.m22,
   X.m20*Y.m00 + X.m21*Y.m10 + X.m22*Y.m20,
   X.m20*Y.m01 + X.m21*Y.m11 + X.m22*Y.m21,
   X.m20*Y.m02 + X.m21*Y.m12 + X.m22*Y.m22⟩

def diag (a b c : ℤ) : Mat3 := ⟨a, 0, 0, 0, b, 0, 0, 0, c⟩

def minor1 (X : Mat3) : ℤ := X.m00
def minor2 (X : Mat3) : ℤ := X.m00 * X.m11 - X.m01 * X.m10
def minor3 (X : Mat3) : ℤ :=
    X.m00 * (X.m11 * X.m22 - X.m12 * X.m21)
  - X.m01 * (X.m10 * X.m22 - X.m12 * X.m20)
  + X.m02 * (X.m10 * X.m21 - X.m11 * X.m20)

def IsSymPosDef (X : Mat3) : Prop :=
  X = X.trans ∧ X.minor1 > 0 ∧ X.minor2 > 0 ∧ X.minor3 > 0

instance (X : Mat3) : Decidable (IsSymPosDef X) := by
  unfold IsSymPosDef; infer_instance

end Mat3

-- Exact integer witness matrices and certificate constants (verified constructively by kernel `decide`!)
def A_mat : Mat3 := ⟨49, 62, -1, 11, 14, 0, 0, 0, 0⟩
def B_mat : Mat3 := ⟨81, 0, 0, 0, 0, 0, 0, 0, 0⟩
def S_mat : Mat3 := Mat3.add A_mat B_mat

def N_A : ℤ := 1000000000000
def UA_mat : Mat3 :=
  ⟨31137293167063,  39396185181747, -640946834916,
   39396185181747,  49873886383270, -733515582123,
    -640946834916,   -733515582123,  226166071368⟩

def N_Q : ℤ := 3765439130012390
def Q_mat : Mat3 :=
  ⟨  -2754699207390,  1641554318888100, -3388779082737700,
    -53429001111900, -3388455869640388, -1641354319812834,
  -3765059042737700,    46883680187166,    25771438835388⟩

def N_D : ℤ := 10000000
def d1 : ℤ := 4640130
def d2 : ℤ := 55496286
def d3 : ℤ := 114552923

def N_R : ℤ := 10000000
def r1 : ℤ := 120380588
def r2 : ℤ := 28024717

theorem cert_SST_exact :
    Mat3.mul S_mat S_mat.trans = ⟨20745, 2298, 0, 2298, 317, 0, 0, 0, 0⟩ := by decide

theorem cert1_UA_posdef : UA_mat.IsSymPosDef := by decide

theorem cert2_operator_monotone_bound :
    (Mat3.sub (Mat3.mul UA_mat UA_mat)
              (Mat3.scale (N_A * N_A) (Mat3.mul A_mat.trans A_mat))).IsSymPosDef := by decide

theorem cert3_Q_orthogonal :
    Mat3.mul Q_mat.trans Q_mat = Mat3.diag (N_Q * N_Q) (N_Q * N_Q) (N_Q * N_Q) := by decide

theorem cert4_diagonal_upper_bound :
    let UH := Mat3.add UA_mat (Mat3.scale N_A B_mat)
    let M  := Mat3.mul Q_mat.trans (Mat3.mul UH Q_mat)
    let sc := N_Q * N_Q * N_A
    let D  := Mat3.diag (sc * d1 * d1) (sc * d2 * d2) (sc * d3 * d3)
    (Mat3.sub D (Mat3.scale (N_D * N_D) M)).IsSymPosDef := by decide

theorem cert5_numerator_root_bracketing :
    let NR4 := N_R ^ 4
    let x1  := r1 ^ 4
    let x2  := r2 ^ 4
    x2 < 10531 * NR4 ∧
    x2 * x2 - 21062 * x2 * NR4 + 1295361 * NR4 * NR4 > 0 ∧
    x1 * x1 - 21062 * x1 * NR4 + 1295361 * NR4 * NR4 < 0 := by decide

theorem cert6_beats_2x2_ceiling :
    let P := r1 ^ 3 + r2 ^ 3
    let Q := d1 ^ 3 + d2 ^ 3 + d3 ^ 3
    let gap := 256 * P ^ 4 - 107 * Q ^ 4
    gap > 0 ∧ gap * gap > 51 * 51 * 17 * Q ^ 8 := by decide

end MI20.Cert3

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section

namespace MI20

/-! ==========================================================================
    PART 1: Theorem 3 — Universal 2×2 Collapse & Exact Closed Form at p = 3/2
    ========================================================================== -/

/-- General Schatten interpolation inequality for 1 < p < 2 (sharp at n = 2!):
    For any m, n ≥ 1 and any tuple A : Fin m → Mat n with S = ∑ A_j and H = ∑ |A_j|,
      ‖S‖_p^2 ≤ (∑ i, λ_i(H)) * (∑ i, λ_i(H)^(p/(2-p)))^((2-p)/p). -/
theorem schattenNorm_sq_le_trace_mul_rpow {m n : ℕ} {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (A : Fin m → Mat n) :
    let H : Mat n := ∑ j, matAbs (A j)
    let hH : H.PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    (schattenNorm p (∑ j, A j)) ^ 2 ≤
      (∑ i : Fin n, hH.isHermitian.eigenvalues i) *
        (∑ i : Fin n, (hH.isHermitian.eigenvalues i) ^ (p / (2 - p))) ^ ((2 - p) / p) := by
  intro H hH
  have hp0 : 0 < p := by linarith
  have hpm1 : 0 < p - 1 := by linarith
  have h2mp : 0 < 2 - p := by linarith
  set S : Mat n := ∑ j, A j
  by_cases hS0 : S = 0
  · rw [hS0, schattenNorm_zero hp0, sq, zero_mul]
    exact mul_nonneg (Finset.sum_nonneg fun i _ => hH.eigenvalues_nonneg i)
      (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hH.eigenvalues_nonneg i) _) _)
  have hS_pos : 0 < schattenNorm p S := schattenNorm_pos_of_ne_zero hp0 hS0
  have hSpow_pos : 0 < schattenPow p S := by
    rw [← schattenNorm_rpow hp0 S]; exact Real.rpow_pos_of_pos hS_pos p
  -- Step 1: SVD of S and G = dualOp p S = V * R with V unitary, R PSD, ‖R‖_q^q = ‖S‖_p^p
  obtain ⟨U_S, V_S, σ, hσ, hS_eq, hG_eq, _⟩ := exists_svd_dualOp p S
  let G : Mat n := dualOp p S
  let r : Fin n → ℝ := fun i => (σ i) ^ (p - 1)
  have hr_nn : ∀ i, 0 ≤ r i := fun i => Real.rpow_nonneg (hσ i) _
  let R : Mat n := (V_S : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (V_S : Mat n)ᴴ
  have hR_psd : R.PosSemidef := by
    have hd : (Matrix.diagonal (fun i => (r i : ℂ))).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast hr_nn i
    simpa [R] using hd.mul_mul_conjTranspose_same (V_S : Mat n)
  let Vu : Matrix.unitaryGroup (Fin n) ℂ := U_S * star V_S
  have hGH_eq : Gᴴ = R * (Vu : Mat n)ᴴ := by
    have hV_eq : (Vu : Mat n)ᴴ = (V_S : Mat n) * (U_S : Mat n)ᴴ := by
      change ((U_S : Mat n) * (V_S : Mat n)ᴴ)ᴴ = _
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hG1 : Gᴴ = (V_S : Mat n) * Matrix.diagonal (fun i => (r i : ℂ)) * (U_S : Mat n)ᴴ := by
      dsimp only [G]
      rw [hG_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
      congr 2; ext i j; by_cases hij : i = j
      · subst hij; simp [r, Complex.conj_ofReal]
      · simp [Matrix.diagonal, hij]
    rw [hG1, hV_eq]
    simp only [R, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V_S : Mat n)ᴴ (V_S : Mat n), unitary_conjTranspose_mul_self V_S, Matrix.one_mul]
  -- Step 2: Polar decompose each A_j = U_j * X_j and spectrally decompose X_j = ∑_ℓ y_{j,ℓ} y_{j,ℓ}ᴴ
  have hpolar : ∀ j : Fin m, ∃ Uj : Matrix.unitaryGroup (Fin n) ℂ, A j = (Uj : Mat n) * matAbs (A j) :=
    fun j => exists_polar_unitary (A j)
  choose Uj hUj using hpolar
  let y : Fin m → Fin n → (Fin n → ℂ) := fun j ℓ =>
    let hX := matAbs_posSemidef (A j)
    let lamX := hX.isHermitian.eigenvalues ℓ
    let eX := (hX.isHermitian.eigenvectorBasis ℓ).ofLp
    ((Real.sqrt lamX : ℝ) : ℂ) • eX
  have hXj_eq : ∀ j : Fin m, matAbs (A j) = ∑ ℓ : Fin n, outerMat (y j ℓ) (y j ℓ) := by
    intro j
    have hX := matAbs_posSemidef (A j)
    have hspec := hX.isHermitian.spectral_theorem
    let Ux := hX.isHermitian.eigenvectorUnitary
    let d := hX.isHermitian.eigenvalues
    have h1 : matAbs (A j) = (Ux : Mat n) * Matrix.diagonal (fun ℓ => (d ℓ : ℂ)) * (Ux : Mat n)ᴴ := by
      simpa [Ux, d, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hspec
    rw [h1]
    ext a b
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
      outerMat, Matrix.of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have hcol : ∀ i : Fin n, (Ux : Mat n) i ℓ = (hX.isHermitian.eigenvectorBasis ℓ).ofLp i := by
      intro i; rfl
    simp only [y, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal, hcol]
    have hsq : ((Real.sqrt (d ℓ) : ℝ) : ℂ) * ((Real.sqrt (d ℓ) : ℝ) : ℂ) = (d ℓ : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hX.eigenvalues_nonneg ℓ)]
    calc ((hX.isHermitian.eigenvectorBasis ℓ).ofLp a * (d ℓ : ℂ)) *
            (starRingEnd ℂ) ((hX.isHermitian.eigenvectorBasis ℓ).ofLp b)
        = (d ℓ : ℂ) * ((hX.isHermitian.eigenvectorBasis ℓ).ofLp a *
            (starRingEnd ℂ) ((hX.isHermitian.eigenvectorBasis ℓ).ofLp b)) := by ring
      _ = (((Real.sqrt (d ℓ) : ℝ) : ℂ) * ((Real.sqrt (d ℓ) : ℝ) : ℂ)) *
            ((hX.isHermitian.eigenvectorBasis ℓ).ofLp a *
            (starRingEnd ℂ) ((hX.isHermitian.eigenvectorBasis ℓ).ofLp b)) := by rw [hsq]
      _ = _ := by ring
  -- Step 3: Cauchy-Schwarz term-by-term: schattenPow p S ≤ √(Re Tr(R^2 H)) * √(Re Tr(H))
  have hCS_main : schattenPow p S ≤
      Real.sqrt ((R * R * H).trace.re) * Real.sqrt (H.trace.re) := by
    have htrS : schattenPow p S = ∑ p_idx : Fin m × Fin n,
        (star (y p_idx.1 p_idx.2) ⬝ᵥ
          (R * ((Vu : Mat n)ᴴ * (Uj p_idx.1 : Mat n))).mulVec (y p_idx.1 p_idx.2)).re := by
      rw [← dualOp_trace_self hp1 S]
      change (Gᴴ * ∑ j : Fin m, A j).trace.re = _
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hUj j, hGH_eq, hXj_eq j, Matrix.mul_sum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      have hassoc : R * (Vu : Mat n)ᴴ * ((Uj j : Mat n) * outerMat (y j ℓ) (y j ℓ)) =
          (R * ((Vu : Mat n)ᴴ * (Uj j : Mat n))) * outerMat (y j ℓ) (y j ℓ) := by
        simp only [Matrix.mul_assoc]
      rw [hassoc, trace_mul_outerMat]
    have hterm : ∀ idx : Fin m × Fin n,
        (star (y idx.1 idx.2) ⬝ᵥ
          (R * ((Vu : Mat n)ᴴ * (Uj idx.1 : Mat n))).mulVec (y idx.1 idx.2)).re ≤
        ‖WithLp.toLp 2 (R.mulVec (y idx.1 idx.2))‖ * ‖WithLp.toLp 2 (y idx.1 idx.2)‖ := by
      intro ⟨j, ℓ⟩
      let Wu : Matrix.unitaryGroup (Fin n) ℂ := star Vu * Uj j
      let yE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (y j ℓ)
      let RyE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (R.mulVec (y j ℓ))
      let WyE : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 ((Wu : Mat n).mulVec (y j ℓ))
      have hdot : star (y j ℓ) ⬝ᵥ (R * ((Vu : Mat n)ᴴ * (Uj j : Mat n))).mulVec (y j ℓ) =
          inner ℂ RyE WyE := by
        have h1 : (R * ((Vu : Mat n)ᴴ * (Uj j : Mat n))).mulVec (y j ℓ) =
            R.mulVec ((Wu : Mat n).mulVec (y j ℓ)) := by
          rw [← Matrix.mulVec_mulVec]; rfl
        rw [h1, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm WyE.ofLp]
        change star (y j ℓ) ⬝ᵥ R.mulVec ((Wu : Mat n).mulVec (y j ℓ)) =
          star (R.mulVec (y j ℓ)) ⬝ᵥ (Wu : Mat n).mulVec (y j ℓ)
        rw [Matrix.star_mulVec, hR_psd.isHermitian.eq, ← Matrix.dotProduct_mulVec]
      have hnormW : ‖WyE‖ = ‖yE‖ := by
        have hsq : ‖WyE‖ ^ 2 = ‖yE‖ ^ 2 := by
          have h1 : inner ℂ WyE WyE = inner ℂ yE yE := by
            rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct,
              dotProduct_comm WyE.ofLp, dotProduct_comm yE.ofLp]
            change star ((Wu : Mat n).mulVec (y j ℓ)) ⬝ᵥ (Wu : Mat n).mulVec (y j ℓ) = star (y j ℓ) ⬝ᵥ y j ℓ
            rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
              unitary_conjTranspose_mul_self Wu, Matrix.one_mulVec]
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
            ← RCLike.ofReal_pow] at h1
          exact (RCLike.ofReal_inj (K := ℂ)).mp h1
        nlinarith [norm_nonneg WyE, norm_nonneg yE]
      rw [hdot, ← hnormW]
      exact (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) RyE WyE)
    have hsum1 : ∑ idx : Fin m × Fin n, ‖WithLp.toLp 2 (R.mulVec (y idx.1 idx.2))‖ ^ 2 =
        (R * R * H).trace.re := by
      rw [Fintype.sum_prod_type]
      have hH_sum : (R * R * H).trace.re = ∑ j : Fin m, ∑ ℓ : Fin n,
          (R * R * outerMat (y j ℓ) (y j ℓ)).trace.re := by
        simp only [H, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hXj_eq j, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
      rw [hH_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ℓ _ => ?_
      rw [trace_mul_outerMat]
      have h1 : (star (y j ℓ) ⬝ᵥ (R * R).mulVec (y j ℓ)).re =
          (star (R.mulVec (y j ℓ)) ⬝ᵥ R.mulVec (y j ℓ)).re := by
        rw [Matrix.star_mulVec, hR_psd.isHermitian.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      rw [h1]
      have h2 : star (R.mulVec (y j ℓ)) ⬝ᵥ R.mulVec (y j ℓ) =
          inner ℂ (WithLp.toLp 2 (R.mulVec (y j ℓ))) (WithLp.toLp 2 (R.mulVec (y j ℓ))) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
      change ‖WithLp.toLp 2 (R.mulVec (y j ℓ))‖ ^ 2 = ((‖WithLp.toLp 2 (R.mulVec (y j ℓ))‖ ^ 2 : ℝ) : ℂ).re
      exact (Complex.ofReal_re _).symm
    have hsum2 : ∑ idx : Fin m × Fin n, ‖WithLp.toLp 2 (y idx.1 idx.2)‖ ^ 2 = H.trace.re := by
      rw [Fintype.sum_prod_type]
      have hH_sum : H.trace.re = ∑ j : Fin m, ∑ ℓ : Fin n, (outerMat (y j ℓ) (y j ℓ)).trace.re := by
        simp only [H, Matrix.trace_sum, Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hXj_eq j, Matrix.trace_sum, Complex.re_sum]
      rw [hH_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ℓ _ => ?_
      have htr : (outerMat (y j ℓ) (y j ℓ)).trace = star (y j ℓ) ⬝ᵥ y j ℓ := by
        simpa using trace_mul_outerMat (1 : Mat n) (y j ℓ)
      rw [htr]
      have h2 : star (y j ℓ) ⬝ᵥ y j ℓ = inner ℂ (WithLp.toLp 2 (y j ℓ)) (WithLp.toLp 2 (y j ℓ)) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [h2, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
      change ‖WithLp.toLp 2 (y j ℓ)‖ ^ 2 = ((‖WithLp.toLp 2 (y j ℓ)‖ ^ 2 : ℝ) : ℂ).re
      exact (Complex.ofReal_re _).symm
    calc schattenPow p S
        ≤ ∑ idx : Fin m × Fin n,
            ‖WithLp.toLp 2 (R.mulVec (y idx.1 idx.2))‖ * ‖WithLp.toLp 2 (y idx.1 idx.2)‖ := by
          rw [htrS]; exact Finset.sum_le_sum fun idx _ => hterm idx
      _ ≤ Real.sqrt (∑ idx : Fin m × Fin n, ‖WithLp.toLp 2 (R.mulVec (y idx.1 idx.2))‖ ^ 2) *
          Real.sqrt (∑ idx : Fin m × Fin n, ‖WithLp.toLp 2 (y idx.1 idx.2)‖ ^ 2) :=
          Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
      _ = Real.sqrt ((R * R * H).trace.re) * Real.sqrt (H.trace.re) := by rw [hsum1, hsum2]
  -- Step 4: Doubly-stochastic Parseval + Young bound for Re Tr(R^2 H)!
  let UH := hH.isHermitian.eigenvectorUnitary
  let lam := hH.isHermitian.eigenvalues
  have hH_eq : H = (UH : Mat n) * Matrix.diagonal (fun j => (lam j : ℂ)) * (UH : Mat n)ᴴ := by
    simpa [UH, lam, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
      using hH.isHermitian.spectral_theorem
  have hH_tr : H.trace.re = ∑ j : Fin n, lam j := by
    rw [hH_eq, Matrix.trace_mul_cycle, unitary_conjTranspose_mul_self UH, Matrix.one_mul,
      Matrix.trace_diagonal, Complex.re_sum]; simp
  have hRR_eq : R * R = (V_S : Mat n) * Matrix.diagonal (fun i => (((r i ^ 2 : ℝ) : ℂ))) * (V_S : Mat n)ᴴ := by
    dsimp only [R]; simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (V_S : Mat n)ᴴ (V_S : Mat n), unitary_conjTranspose_mul_self V_S,
      Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    congr 2; ext i j; by_cases hij : i = j
    · subst hij; simp [sq]
    · simp [Matrix.diagonal, hij]
  let Qu : Matrix.unitaryGroup (Fin n) ℂ := star V_S * UH
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
  have hRRH_tr : (R * R * H).trace.re = ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (r i ^ 2 * lam j) := by
    have hQeq : (V_S : Mat n)ᴴ * (UH : Mat n) = Q := rfl
    have hQHeq : (UH : Mat n)ᴴ * (V_S : Mat n) = Qᴴ := by
      change (UH : Mat n)ᴴ * (V_S : Mat n) = ((V_S : Mat n)ᴴ * (UH : Mat n))ᴴ
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    set DR : Mat n := Matrix.diagonal (fun i => (((r i ^ 2 : ℝ) : ℂ)))
    set DH : Mat n := Matrix.diagonal (fun j => (lam j : ℂ))
    have hprod : (R * R * H).trace = ((DR * Q) * (DH * Qᴴ)).trace := by
      rw [hRR_eq, hH_eq]
      calc (((V_S : Mat n) * DR * (V_S : Mat n)ᴴ) * ((UH : Mat n) * DH * (UH : Mat n)ᴴ)).trace
          = ((V_S : Mat n) * (DR * ((V_S : Mat n)ᴴ * (UH : Mat n)) * DH * (UH : Mat n)ᴴ)).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DR * Q * DH * (UH : Mat n)ᴴ) * (V_S : Mat n)).trace := by
              rw [hQeq, Matrix.trace_mul_comm (V_S : Mat n)]
        _ = ((DR * Q) * (DH * ((UH : Mat n)ᴴ * (V_S : Mat n)))).trace := by
              congr 1; simp only [Matrix.mul_assoc]
        _ = ((DR * Q) * (DH * Qᴴ)).trace := by rw [hQHeq]
    rw [hprod, Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.diag, Matrix.mul_apply, DR, DH, Matrix.diagonal_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Matrix.conjTranspose_apply]
    have hmul : (((r i ^ 2 : ℝ) : ℂ) * Q i j * ((lam j : ℂ) * star (Q i j))) =
        (((r i ^ 2 * lam j : ℝ) : ℂ) * (Q i j * star (Q i j))) := by push_cast; ring
    rw [hmul, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]; ring
  -- Hölder via Young with α = p / (2*(p-1)) > 1 and β = p / (2-p) > 1 (1/α + 1/β = 1)!
  let α : ℝ := p / (2 * (p - 1))
  let β : ℝ := p / (2 - p)
  have hα_pos : 0 < α := div_pos hp0 (by linarith)
  have hβ_pos : 0 < β := div_pos hp0 h2mp
  have hα_inv : α⁻¹ = 2 * (p - 1) / p := by dsimp [α]; rw [inv_div]
  have hβ_inv : β⁻¹ = (2 - p) / p := by dsimp [β]; rw [inv_div]
  have hconj : α⁻¹ + β⁻¹ = 1 := by rw [hα_inv, hβ_inv]; field_simp [hp0.ne']; ring
  have hsum_r : ∑ i : Fin n, (r i ^ 2) ^ α = schattenPow p S := by
    have hSpow : schattenPow p S = ∑ i : Fin n, (σ i) ^ p := by
      rw [hS_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
        schattenPow_diagonal hp0 σ hσ]
    rw [hSpow]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [r, α]
    rw [← Real.rpow_two, ← Real.rpow_mul (hσ i), ← Real.rpow_mul (hσ i)]
    congr 1; field_simp [hpm1.ne']
  let BH : ℝ := ∑ j : Fin n, (lam j) ^ β
  have hBH_nn : 0 ≤ BH := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hH.eigenvalues_nonneg j) _
  have hRRH_le : (R * R * H).trace.re ≤ (schattenPow p S) ^ α⁻¹ * BH ^ β⁻¹ := by
    by_cases hBH0 : BH = 0
    · have hlam0 : ∀ j : Fin n, lam j = 0 := fun j => by
        have hj0 : (lam j) ^ β = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun k _ => Real.rpow_nonneg (hH.eigenvalues_nonneg k) _).mp hBH0 j (Finset.mem_univ j)
        exact (Real.rpow_eq_zero (hH.eigenvalues_nonneg j) hβ_pos.ne').mp hj0
      rw [hRRH_tr]
      simp [hlam0, hBH0, Real.zero_rpow (inv_pos.mpr hβ_pos).ne']
    · have hBH_pos : 0 < BH := lt_of_le_of_ne hBH_nn (Ne.symm hBH0)
      let Ar : ℝ := (schattenPow p S) ^ α⁻¹
      let Bh : ℝ := BH ^ β⁻¹
      have hAr_pos : 0 < Ar := Real.rpow_pos_of_pos hSpow_pos _
      have hBh_pos : 0 < Bh := Real.rpow_pos_of_pos hBH_pos _
      rw [hRRH_tr]
      suffices hnorm : ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((r i ^ 2 / Ar) * (lam j / Bh)) ≤ 1 by
        have hfact : ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (r i ^ 2 * lam j) =
            (Ar * Bh) * ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((r i ^ 2 / Ar) * (lam j / Bh)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
          field_simp [hAr_pos.ne', hBh_pos.ne']
        rw [hfact]
        calc (Ar * Bh) * ∑ i, ∑ j, ‖Q i j‖ ^ 2 * ((r i ^ 2 / Ar) * (lam j / Bh))
            ≤ (Ar * Bh) * 1 := mul_le_mul_of_nonneg_left hnorm (mul_pos hAr_pos hBh_pos).le
          _ = Ar * Bh := mul_one _
      calc ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * ((r i ^ 2 / Ar) * (lam j / Bh))
          ≤ ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 *
              (α⁻¹ * (r i ^ 2 / Ar) ^ α + β⁻¹ * (lam j / Bh) ^ β) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            have hlam_nn : 0 ≤ lam j := hH.eigenvalues_nonneg j
            have hy := Real.geom_mean_le_arith_mean2_weighted (inv_pos.mpr hα_pos).le
              (inv_pos.mpr hβ_pos).le (Real.rpow_nonneg (div_nonneg (sq_nonneg (r i)) hAr_pos.le) α)
              (Real.rpow_nonneg (div_nonneg hlam_nn hBh_pos.le) β) hconj
            rw [← Real.rpow_mul (div_nonneg (sq_nonneg (r i)) hAr_pos.le), mul_inv_cancel₀ hα_pos.ne',
              Real.rpow_one, ← Real.rpow_mul (div_nonneg hlam_nn hBh_pos.le),
              mul_inv_cancel₀ hβ_pos.ne', Real.rpow_one] at hy
            exact hy
        _ = α⁻¹ * (∑ i : Fin n, (r i ^ 2 / Ar) ^ α) + β⁻¹ * (∑ j : Fin n, (lam j / Bh) ^ β) := by
            have hsplit : ∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 *
                (α⁻¹ * (r i ^ 2 / Ar) ^ α + β⁻¹ * (lam j / Bh) ^ β) =
                (∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (α⁻¹ * (r i ^ 2 / Ar) ^ α)) +
                (∑ i : Fin n, ∑ j : Fin n, ‖Q i j‖ ^ 2 * (β⁻¹ * (lam j / Bh) ^ β)) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => by ring
            rw [hsplit]
            congr 1
            · rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hRowQ i, one_mul]
            · rw [Finset.sum_comm, Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hColQ j, one_mul]
        _ = α⁻¹ * 1 + β⁻¹ * 1 := by
            congr 2
            · have : ∑ i : Fin n, (r i ^ 2 / Ar) ^ α = (∑ i : Fin n, (r i ^ 2) ^ α) / Ar ^ α := by
                rw [Finset.sum_div]
                refine Finset.sum_congr rfl fun i _ => Real.div_rpow (sq_nonneg _) hAr_pos.le α
              rw [this, hsum_r, show Ar ^ α = schattenPow p S by
                dsimp [Ar]; rw [← Real.rpow_mul hSpow_pos.le, inv_mul_cancel₀ hα_pos.ne', Real.rpow_one],
                div_self hSpow_pos.ne']
            · have : ∑ j : Fin n, (lam j / Bh) ^ β = BH / Bh ^ β := by
                rw [Finset.sum_div]
                refine Finset.sum_congr rfl fun j _ => Real.div_rpow (hH.eigenvalues_nonneg j) hBh_pos.le β
              rw [this, show Bh ^ β = BH by
                dsimp [Bh]; rw [← Real.rpow_mul hBH_pos.le, inv_mul_cancel₀ hβ_pos.ne', Real.rpow_one],
                div_self hBH_pos.ne']
        _ = 1 := by linarith [hconj]
  -- Step 5: Square hCS_main and cancel (schattenPow p S)^(2*(p-1)/p) to get ‖S‖_p^2 ≤ Tr(H) * BH^((2-p)/p)!
  have hsq : (schattenPow p S) ^ 2 ≤ (R * R * H).trace.re * H.trace.re := by
    have hRRH_nn : 0 ≤ (R * R * H).trace.re := by
      have hRR_psd : (R * R).PosSemidef := by
        rw [hRR_eq]
        have hd : (Matrix.diagonal (fun i => (((r i ^ 2 : ℝ) : ℂ)))).PosSemidef := by
          rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast sq_nonneg (r i)
        simpa using hd.mul_mul_conjTranspose_same (V_S : Mat n)
      exact re_trace_mul_nonneg_of_posSemidef hRR_psd hH
    have hH_tr_nn : 0 ≤ H.trace.re := by
      rw [hH_tr]; exact Finset.sum_nonneg fun j _ => hH.eigenvalues_nonneg j
    calc (schattenPow p S) ^ 2
        ≤ (Real.sqrt ((R * R * H).trace.re) * Real.sqrt (H.trace.re)) ^ 2 :=
          pow_le_pow_left₀ hSpow_pos.le hCS_main 2
      _ = (R * R * H).trace.re * H.trace.re := by
          rw [mul_pow, Real.sq_sqrt hRRH_nn, Real.sq_sqrt hH_tr_nn]
  have hcomb : (schattenPow p S) ^ 2 ≤ (schattenPow p S) ^ α⁻¹ * ((∑ j, lam j) * BH ^ β⁻¹) := by
    have hH_tr_nn : 0 ≤ ∑ j, lam j := Finset.sum_nonneg fun j _ => hH.eigenvalues_nonneg j
    have h1 := hsq.trans (mul_le_mul_of_nonneg_right hRRH_le (hH_tr ▸ hH_tr_nn))
    rw [hH_tr] at h1; linarith
  have hpow_split : (schattenPow p S) ^ 2 = (schattenPow p S) ^ α⁻¹ * (schattenNorm p S) ^ 2 := by
    have h1 : (schattenNorm p S) ^ 2 = (schattenPow p S) ^ (2 / p) := by
      rw [← Real.rpow_two, show schattenNorm p S = (schattenPow p S) ^ (1 / p) from rfl,
        ← Real.rpow_mul hSpow_pos.le]; congr 1; ring
    rw [h1, ← Real.rpow_add hSpow_pos, ← Real.rpow_two, hα_inv]
    congr 1; field_simp [hp0.ne']; ring
  rw [hpow_split] at hcomb
  have hfac_pos : 0 < (schattenPow p S) ^ α⁻¹ := Real.rpow_pos_of_pos hSpow_pos _
  have hfinal := le_of_mul_le_mul_left hcomb hfac_pos
  simpa only [BH, β, hβ_inv] using hfinal

/-- Exact real-number version of the zero-calculus P_8 global optimality identity for p = 3/2:
    For ALL reals u, v ≥ 0,
      256 * (u^2 + v^2)^3 * (u^6 + v^6) ≤ (107 + 51 * √17) * (u^3 + v^3)^4,
    with equality whenever 2*u^2 - (1 + √17)*u*v + 2*v^2 = 0! -/
theorem p32_global_polynomial_identity (u v : ℝ) :
    let s17 : ℝ := Real.sqrt 17
    let c0 : ℝ := -149 + 51 * s17
    let c1 : ℝ := 718 - 98 * s17
    let c2 : ℝ := -1181 + 363 * s17
    let c3 : ℝ := 2302 - 434 * s17
    let c4 : ℝ := -2052 + 668 * s17
    4 * ((107 + 51 * s17) * (u ^ 3 + v ^ 3) ^ 4 - 256 * (u ^ 2 + v ^ 2) ^ 3 * (u ^ 6 + v ^ 6)) =
      (2 * u ^ 2 - (1 + s17) * u * v + 2 * v ^ 2) ^ 2 *
        (c0 * (u ^ 8 + v ^ 8) + c1 * (u ^ 7 * v + u * v ^ 7) +
         c2 * (u ^ 6 * v ^ 2 + u ^ 2 * v ^ 6) + c3 * (u ^ 5 * v ^ 3 + u ^ 3 * v ^ 5) +
         c4 * (u ^ 4 * v ^ 4)) := by
  intro s17 c0 c1 c2 c3 c4
  have hs : s17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs3 : s17 ^ 3 = 17 * s17 := by calc s17 ^ 3 = s17 ^ 2 * s17 := by ring
    _ = 17 * s17 := by rw [hs]
  dsimp only [c0, c1, c2, c3, c4]
  ring_nf
  simp only [hs, hs3]
  ring

theorem p32_global_polynomial_ineq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    256 * (u ^ 2 + v ^ 2) ^ 3 * (u ^ 6 + v ^ 6) ≤ (107 + 51 * Real.sqrt 17) * (u ^ 3 + v ^ 3) ^ 4 := by
  set s17 : ℝ := Real.sqrt 17
  have hs0 : 0 < s17 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < -149 + 51 * s17 := by nlinarith
  have hc1 : 0 < 718 - 98 * s17 := by nlinarith
  have hc2 : 0 < -1181 + 363 * s17 := by nlinarith
  have hc3 : 0 < 2302 - 434 * s17 := by nlinarith
  have hc4 : 0 < -2052 + 668 * s17 := by nlinarith
  have hP8 : 0 ≤ (-149 + 51 * s17) * (u ^ 8 + v ^ 8) + (718 - 98 * s17) * (u ^ 7 * v + u * v ^ 7) +
      (-1181 + 363 * s17) * (u ^ 6 * v ^ 2 + u ^ 2 * v ^ 6) +
      (2302 - 434 * s17) * (u ^ 5 * v ^ 3 + u ^ 3 * v ^ 5) +
      (-2052 + 668 * s17) * (u ^ 4 * v ^ 4) := by positivity
  have hid := p32_global_polynomial_identity u v
  have hprod : 0 ≤ (2 * u ^ 2 - (1 + s17) * u * v + 2 * v ^ 2) ^ 2 *
      ((-149 + 51 * s17) * (u ^ 8 + v ^ 8) + (718 - 98 * s17) * (u ^ 7 * v + u * v ^ 7) +
       (-1181 + 363 * s17) * (u ^ 6 * v ^ 2 + u ^ 2 * v ^ 6) +
       (2302 - 434 * s17) * (u ^ 5 * v ^ 3 + u ^ 3 * v ^ 5) +
       (-2052 + 668 * s17) * (u ^ 4 * v ^ 4)) :=
    mul_nonneg (sq_nonneg _) hP8
  linarith

set_option maxHeartbeats 400000 in
/-- Helper: Explicit 2×2 real rank-one witness pair realizing the exact upper bound for any t ≥ 1
    and 1 < p < 2:
      A0 = u1 v1ᵀ, A1 = u2 v2ᵀ, where v1 = u1 = (1, 0), v2 = (c, √(1-c²)), u2 = (γ, √(1-γ²))
      with c = (t-1)/(t+1), γ = (t^(p/(2-p)) - 1)/(t^(p/(2-p)) + 1). -/
lemma exists_2x2_rankOne_witness {m : ℕ} (hm : 2 ≤ m) {p t : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (ht : 1 ≤ t) :
    ∃ A : Fin m → Mat 2, (∑ j, matAbs (A j)) ≠ 0 ∧
      leeRatio p A = Real.sqrt (t + 1) * (t ^ (p / (2 - p)) + 1) ^ ((2 - p) / (2 * p)) /
        (t ^ p + 1) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h2mp : 0 < 2 - p := by linarith
  have ht0 : 0 < t := by linarith
  let β : ℝ := p / (2 - p)
  have hβ_pos : 0 < β := div_pos hp0 h2mp
  have htβ_ge1 : 1 ≤ t ^ β := Real.one_le_rpow ht hβ_pos.le
  let c : ℝ := (t - 1) / (t + 1)
  let s_c : ℝ := Real.sqrt (1 - c ^ 2)
  let γ : ℝ := (t ^ β - 1) / (t ^ β + 1)
  let s_γ : ℝ := Real.sqrt (1 - γ ^ 2)
  have hc_lt1 : c < 1 := by dsimp [c]; rw [div_lt_one (by linarith)]; linarith
  have hc_nn : 0 ≤ c := div_nonneg (by linarith) (by linarith)
  have hγ_lt1 : γ < 1 := by dsimp [γ]; rw [div_lt_one (by linarith)]; linarith
  have hγ_nn : 0 ≤ γ := div_nonneg (by linarith) (by linarith)
  have hsc_sq : c ^ 2 + s_c ^ 2 = 1 := by
    have : 0 ≤ 1 - c ^ 2 := by nlinarith
    simp [s_c, Real.sq_sqrt this]
  have hsγ_sq : γ ^ 2 + s_γ ^ 2 = 1 := by
    have : 0 ≤ 1 - γ ^ 2 := by nlinarith
    simp [s_γ, Real.sq_sqrt this]
  let e0 : Fin 2 → ℂ := ![1, 0]
  let v2 : Fin 2 → ℂ := ![(c : ℂ), (s_c : ℂ)]
  let u2 : Fin 2 → ℂ := ![(γ : ℂ), (s_γ : ℂ)]
  have he0_unit : star e0 ⬝ᵥ e0 = 1 := by simp [e0, dotProduct, Fin.sum_univ_two]
  have hv2_unit : star v2 ⬝ᵥ v2 = 1 := by
    simp only [v2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq, hsc_sq,
      Complex.ofReal_one]
  have hu2_unit : star u2 ⬝ᵥ u2 = 1 := by
    simp only [u2, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq, hsγ_sq,
      Complex.ofReal_one]
  let A0 : Mat 2 := outerMat e0 e0
  let A1 : Mat 2 := outerMat u2 v2
  let A : Fin m → Mat 2 := fun j => if j.val = 0 then A0 else if j.val = 1 then A1 else 0
  have hAbs_rankOne : ∀ u v : Fin 2 → ℂ, star u ⬝ᵥ u = 1 → star v ⬝ᵥ v = 1 →
      matAbs (outerMat u v) = outerMat v v := by
    intro u v hu hv
    refine matAbs_eq_of_posSemidef_sq (outerMat_posSemidef v) ?_
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, outerMat, Matrix.of_apply,
      Fin.sum_univ_two]
    have hu' : star (u 0) * u 0 + star (u 1) * u 1 = 1 := by
      simpa [dotProduct, Fin.sum_univ_two] using hu
    have hv' : star (v 0) * v 0 + star (v 1) * v 1 = 1 := by
      simpa [dotProduct, Fin.sum_univ_two] using hv
    have hL : star (u 0 * star (v i)) * (u 0 * star (v j)) +
        star (u 1 * star (v i)) * (u 1 * star (v j)) =
        (v i * star (v j)) * (star (u 0) * u 0 + star (u 1) * u 1) := by
      simp only [star_mul', star_star]; ring
    have hR : v i * star (v 0) * (v 0 * star (v j)) +
        v i * star (v 1) * (v 1 * star (v j)) =
        (v i * star (v j)) * (star (v 0) * v 0 + star (v 1) * v 1) := by ring
    rw [hL, hR, hu', hv']
  have hSumA : ∑ j : Fin m, A j = A0 + A1 := by
    let j0 : Fin m := ⟨0, by omega⟩
    let j1 : Fin m := ⟨1, by omega⟩
    have hj01 : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; dsimp [j0, j1] at this; omega
    have h1 : ∑ j : Fin m, A j = A j0 + A j1 + ∑ j ∈ (Finset.univ.erase j0).erase j1, A j := by
      rw [← Finset.add_sum_erase _ A (Finset.mem_univ j0)]
      have hmem1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj01.symm, Finset.mem_univ j1⟩
      rw [← Finset.add_sum_erase _ A hmem1]; abel
    have hrest : ∑ j ∈ (Finset.univ.erase j0).erase j1, A j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne1 : j ≠ j1 := (Finset.mem_erase.mp hj).1
      have hne0 : j ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hv0 : j.val ≠ 0 := fun h => hne0 (Fin.ext h)
      have hv1 : j.val ≠ 1 := fun h => hne1 (Fin.ext h)
      simp [A, hv0, hv1]
    rw [h1, hrest, add_zero]
    simp [A, j0, j1]
  have hSumH : ∑ j : Fin m, matAbs (A j) = outerMat e0 e0 + outerMat v2 v2 := by
    let j0 : Fin m := ⟨0, by omega⟩
    let j1 : Fin m := ⟨1, by omega⟩
    have hj01 : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; dsimp [j0, j1] at this; omega
    have h1 : ∑ j : Fin m, matAbs (A j) = matAbs (A j0) + matAbs (A j1) +
        ∑ j ∈ (Finset.univ.erase j0).erase j1, matAbs (A j) := by
      rw [← Finset.add_sum_erase _ (fun j => matAbs (A j)) (Finset.mem_univ j0)]
      have hmem1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj01.symm, Finset.mem_univ j1⟩
      rw [← Finset.add_sum_erase _ (fun j => matAbs (A j)) hmem1]; abel
    have hrest : ∑ j ∈ (Finset.univ.erase j0).erase j1, matAbs (A j) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne1 : j ≠ j1 := (Finset.mem_erase.mp hj).1
      have hne0 : j ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hv0 : j.val ≠ 0 := fun h => hne0 (Fin.ext h)
      have hv1 : j.val ≠ 1 := fun h => hne1 (Fin.ext h)
      simp [A, hv0, hv1, matAbs_zero]
    rw [h1, hrest, add_zero]
    simp only [A, j0, j1, ↓reduceIte, Nat.one_ne_zero]
    rw [hAbs_rankOne e0 e0 he0_unit he0_unit, hAbs_rankOne u2 v2 hu2_unit hv2_unit]
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  let aH : ℝ := Real.sqrt ((1 + c) / 2)
  let bH : ℝ := Real.sqrt ((1 - c) / 2)
  have haH_sq : aH ^ 2 = (1 + c) / 2 := Real.sq_sqrt (by linarith)
  have hbH_sq : bH ^ 2 = (1 - c) / 2 := Real.sq_sqrt (by linarith)
  have habH : 2 * aH * bH = s_c := by
    have h1 : aH * bH = Real.sqrt (((1 + c) / 2) * ((1 - c) / 2)) :=
      (Real.sqrt_mul (by linarith) _).symm
    have h2 : ((1 + c) / 2) * ((1 - c) / 2) = (1 - c ^ 2) / 4 := by ring
    have h3 : Real.sqrt ((1 - c ^ 2) / 4) = s_c / 2 := by
      rw [Real.sqrt_div (by nlinarith), hsqrt4]
    rw [mul_assoc, h1, h2, h3]; ring
  let QH_mat : Mat 2 := Matrix.of ![![(aH : ℂ), (-(bH : ℂ))], ![(bH : ℂ), (aH : ℂ)]]
  have hQH_unit : QH_mat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QH_mat, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Complex.conj_ofReal]
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq,
        haH_sq, hbH_sq, show (1 + c) / 2 + (1 - c) / 2 = 1 by ring, Complex.ofReal_one]
    · ring
    · ring
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq,
        haH_sq, hbH_sq, show (1 - c) / 2 + (1 + c) / 2 = 1 by ring, Complex.ofReal_one]
  let QH : Matrix.unitaryGroup (Fin 2) ℂ := ⟨QH_mat, hQH_unit⟩
  have hH_diag : outerMat e0 e0 + outerMat v2 v2 =
      (QH : Mat 2) * Matrix.diagonal (fun i : Fin 2 => (if i = 0 then ((1 + c : ℝ) : ℂ) else ((1 - c : ℝ) : ℂ))) *
        (QH : Mat 2)ᴴ := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [outerMat, e0, v2, QH, QH_mat, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply,
        Matrix.diagonal_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Complex.star_def, Complex.conj_ofReal, ↓reduceIte, Fin.zero_eta,
        Fin.mk_one, Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, Nat.reduceEqDiff, map_neg, map_one,
        map_zero]
    · have : (1 : ℂ) * 1 + (c : ℂ) * (c : ℂ) = (((1 + c ^ 2 : ℝ) : ℂ)) := by push_cast; ring
      rw [this]
      have hR : ((aH : ℂ) * ((1 + c : ℝ) : ℂ) * (aH : ℂ) + (-(bH : ℂ)) * ((1 - c : ℝ) : ℂ) * (-(bH : ℂ))) =
          (((aH ^ 2 * (1 + c) + bH ^ 2 * (1 - c) : ℝ) : ℂ)) := by push_cast; ring
      have hsimp : (((aH : ℂ) * ((1 + c : ℝ) : ℂ) + (-(bH : ℂ)) * 0) * (aH : ℂ) +
          ((aH : ℂ) * 0 + (-(bH : ℂ)) * ((1 - c : ℝ) : ℂ)) * (-(bH : ℂ))) =
          ((aH : ℂ) * ((1 + c : ℝ) : ℂ) * (aH : ℂ) + (-(bH : ℂ)) * ((1 - c : ℝ) : ℂ) * (-(bH : ℂ))) := by ring
      rw [hsimp, hR]; congr 1; nlinarith [haH_sq, hbH_sq]
    · have hL : (1 : ℂ) * 0 + (c : ℂ) * (s_c : ℂ) = (((c * s_c : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((aH : ℂ) * ((1 + c : ℝ) : ℂ) + (-(bH : ℂ)) * 0) * (bH : ℂ) +
          ((aH : ℂ) * 0 + (-(bH : ℂ)) * ((1 - c : ℝ) : ℂ)) * (aH : ℂ)) =
          ((((2 * aH * bH) * c : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR, habH]; congr 1; ring
    · have hL : (0 : ℂ) * 1 + (s_c : ℂ) * (c : ℂ) = (((c * s_c : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((bH : ℂ) * ((1 + c : ℝ) : ℂ) + (aH : ℂ) * 0) * (aH : ℂ) +
          ((bH : ℂ) * 0 + (aH : ℂ) * ((1 - c : ℝ) : ℂ)) * (-(bH : ℂ))) =
          ((((2 * aH * bH) * c : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR, habH]; congr 1; ring
    · have hL : (0 : ℂ) * 0 + (s_c : ℂ) * (s_c : ℂ) = (((s_c ^ 2 : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((bH : ℂ) * ((1 + c : ℝ) : ℂ) + (aH : ℂ) * 0) * (bH : ℂ) +
          ((bH : ℂ) * 0 + (aH : ℂ) * ((1 - c : ℝ) : ℂ)) * (aH : ℂ)) =
          (((bH ^ 2 * (1 + c) + aH ^ 2 * (1 - c) : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR]; congr 1; nlinarith [haH_sq, hbH_sq, hsc_sq]
  -- Similarly diagonalize S = A0 + A1 via QU * diag(√((1+γ)(1+c)), √((1-γ)(1-c))) * QHᴴ!
  let aU : ℝ := Real.sqrt ((1 + γ) / 2)
  let bU : ℝ := Real.sqrt ((1 - γ) / 2)
  have haU_sq : aU ^ 2 = (1 + γ) / 2 := Real.sq_sqrt (by linarith)
  have hbU_sq : bU ^ 2 = (1 - γ) / 2 := Real.sq_sqrt (by linarith)
  have habU : 2 * aU * bU = s_γ := by
    have h1 : aU * bU = Real.sqrt (((1 + γ) / 2) * ((1 - γ) / 2)) :=
      (Real.sqrt_mul (by linarith) _).symm
    have h2 : ((1 + γ) / 2) * ((1 - γ) / 2) = (1 - γ ^ 2) / 4 := by ring
    have h3 : Real.sqrt ((1 - γ ^ 2) / 4) = s_γ / 2 := by
      rw [Real.sqrt_div (by nlinarith), hsqrt4]
    rw [mul_assoc, h1, h2, h3]; ring
  let QU_mat : Mat 2 := Matrix.of ![![(aU : ℂ), (-(bU : ℂ))], ![(bU : ℂ), (aU : ℂ)]]
  have hQU_unit : QU_mat ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [QU_mat, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Complex.conj_ofReal]
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq,
        haU_sq, hbU_sq, show (1 + γ) / 2 + (1 - γ) / 2 = 1 by ring, Complex.ofReal_one]
    · ring
    · ring
    · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq,
        haU_sq, hbU_sq, show (1 - γ) / 2 + (1 + γ) / 2 = 1 by ring, Complex.ofReal_one]
  let QU : Matrix.unitaryGroup (Fin 2) ℂ := ⟨QU_mat, hQU_unit⟩
  let σ0 : ℝ := Real.sqrt ((1 + γ) * (1 + c))
  let σ1 : ℝ := Real.sqrt ((1 - γ) * (1 - c))
  have hS_svd : A0 + A1 =
      (QU : Mat 2) * Matrix.diagonal (fun i : Fin 2 => (if i = 0 then (σ0 : ℂ) else (σ1 : ℂ))) *
        (QH : Mat 2)ᴴ := by
    have h1pc : 0 ≤ 1 + c := by linarith
    have h1mc : 0 ≤ 1 - c := by linarith
    have h1pg : 0 ≤ 1 + γ := by linarith
    have h1mg : 0 ≤ 1 - γ := by linarith
    have h1c2 : 0 ≤ 1 - c ^ 2 := by nlinarith only [hc_nn, hc_lt1]
    have h1g2 : 0 ≤ 1 - γ ^ 2 := by nlinarith only [hγ_nn, hγ_lt1]
    have h1pc2 : 0 ≤ (1 + c) / 2 := div_nonneg h1pc (by norm_num)
    have h1mc2 : 0 ≤ (1 - c) / 2 := div_nonneg h1mc (by norm_num)
    have h1pg2 : 0 ≤ (1 + γ) / 2 := div_nonneg h1pg (by norm_num)
    have h1mg2 : 0 ≤ (1 - γ) / 2 := div_nonneg h1mg (by norm_num)
    have hσ0_a : aU * aH * σ0 = (1 + γ) * (1 + c) / 2 := by
      have h1 : aU * aH = Real.sqrt (((1 + γ) / 2) * ((1 + c) / 2)) :=
        (Real.sqrt_mul h1pg2 _).symm
      have h2 : ((1 + γ) / 2) * ((1 + c) / 2) * ((1 + γ) * (1 + c)) =
          ((1 + γ) * (1 + c) / 2) ^ 2 := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1pg2 h1pc2), h2,
        Real.sqrt_sq (div_nonneg (mul_nonneg h1pg h1pc) (by norm_num))]
    have hσ1_b : bU * bH * σ1 = (1 - γ) * (1 - c) / 2 := by
      have h1 : bU * bH = Real.sqrt (((1 - γ) / 2) * ((1 - c) / 2)) :=
        (Real.sqrt_mul h1mg2 _).symm
      have h2 : ((1 - γ) / 2) * ((1 - c) / 2) * ((1 - γ) * (1 - c)) =
          ((1 - γ) * (1 - c) / 2) ^ 2 := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1mg2 h1mc2), h2,
        Real.sqrt_sq (div_nonneg (mul_nonneg h1mg h1mc) (by norm_num))]
    have hσ0_ab : aU * bH * σ0 = (1 + γ) * s_c / 2 := by
      have h1 : aU * bH = Real.sqrt (((1 + γ) / 2) * ((1 - c) / 2)) :=
        (Real.sqrt_mul h1pg2 _).symm
      have h2 : ((1 + γ) / 2) * ((1 - c) / 2) * ((1 + γ) * (1 + c)) =
          ((1 + γ) / 2) ^ 2 * (1 - c ^ 2) := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1pg2 h1mc2), h2,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1pg2]; dsimp [s_c]; ring
    have hσ1_ba : bU * aH * σ1 = (1 - γ) * s_c / 2 := by
      have h1 : bU * aH = Real.sqrt (((1 - γ) / 2) * ((1 + c) / 2)) :=
        (Real.sqrt_mul h1mg2 _).symm
      have h2 : ((1 - γ) / 2) * ((1 + c) / 2) * ((1 - γ) * (1 - c)) =
          ((1 - γ) / 2) ^ 2 * (1 - c ^ 2) := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1mg2 h1pc2), h2,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1mg2]; dsimp [s_c]; ring
    have hσ0_ba : bU * aH * σ0 = s_γ * (1 + c) / 2 := by
      have h1 : bU * aH = Real.sqrt (((1 - γ) / 2) * ((1 + c) / 2)) :=
        (Real.sqrt_mul h1mg2 _).symm
      have h2 : ((1 - γ) / 2) * ((1 + c) / 2) * ((1 + γ) * (1 + c)) =
          (1 - γ ^ 2) * ((1 + c) / 2) ^ 2 := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1mg2 h1pc2), h2,
        Real.sqrt_mul h1g2, Real.sqrt_sq h1pc2]; dsimp [s_γ]; ring
    have hσ1_ab : aU * bH * σ1 = s_γ * (1 - c) / 2 := by
      have h1 : aU * bH = Real.sqrt (((1 + γ) / 2) * ((1 - c) / 2)) :=
        (Real.sqrt_mul h1pg2 _).symm
      have h2 : ((1 + γ) / 2) * ((1 - c) / 2) * ((1 - γ) * (1 - c)) =
          (1 - γ ^ 2) * ((1 - c) / 2) ^ 2 := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1pg2 h1mc2), h2,
        Real.sqrt_mul h1g2, Real.sqrt_sq h1mc2]; dsimp [s_γ]; ring
    have hσ0_bb : bU * bH * σ0 = s_γ * s_c / 2 := by
      have h1 : bU * bH = Real.sqrt (((1 - γ) / 2) * ((1 - c) / 2)) :=
        (Real.sqrt_mul h1mg2 _).symm
      have h2 : ((1 - γ) / 2) * ((1 - c) / 2) * ((1 + γ) * (1 + c)) =
          ((1 - γ ^ 2) * (1 - c ^ 2)) / 4 := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1mg2 h1mc2), h2,
        Real.sqrt_div (mul_nonneg h1g2 h1c2), Real.sqrt_mul h1g2, hsqrt4]
    have hσ1_aa : aU * aH * σ1 = s_γ * s_c / 2 := by
      have h1 : aU * aH = Real.sqrt (((1 + γ) / 2) * ((1 + c) / 2)) :=
        (Real.sqrt_mul h1pg2 _).symm
      have h2 : ((1 + γ) / 2) * ((1 + c) / 2) * ((1 - γ) * (1 - c)) =
          ((1 - γ ^ 2) * (1 - c ^ 2)) / 4 := by ring
      rw [h1, ← Real.sqrt_mul (mul_nonneg h1pg2 h1pc2), h2,
        Real.sqrt_div (mul_nonneg h1g2 h1c2), Real.sqrt_mul h1g2, hsqrt4]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp only [A0, A1, outerMat, e0, u2, v2, QU, QU_mat, QH, QH_mat, Matrix.add_apply,
        Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.star_def,
        Complex.conj_ofReal, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.one_eq_zero_iff,
        Fin.zero_eq_one_iff, Nat.reduceEqDiff, map_neg, map_one, map_zero]
    · have hL : (1 : ℂ) * 1 + (γ : ℂ) * (c : ℂ) = (((1 + γ * c : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((aU : ℂ) * (σ0 : ℂ) + (-(bU : ℂ)) * 0) * (aH : ℂ) +
          ((aU : ℂ) * 0 + (-(bU : ℂ)) * (σ1 : ℂ)) * (-(bH : ℂ))) =
          (((aU * aH * σ0 + bU * bH * σ1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR, hσ0_a, hσ1_b]; congr 1; ring
    · have hL : (1 : ℂ) * 0 + (γ : ℂ) * (s_c : ℂ) = (((γ * s_c : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((aU : ℂ) * (σ0 : ℂ) + (-(bU : ℂ)) * 0) * (bH : ℂ) +
          ((aU : ℂ) * 0 + (-(bU : ℂ)) * (σ1 : ℂ)) * (aH : ℂ)) =
          (((aU * bH * σ0 - bU * aH * σ1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR, hσ0_ab, hσ1_ba]; congr 1; ring
    · have hL : (0 : ℂ) * 1 + (s_γ : ℂ) * (c : ℂ) = (((s_γ * c : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((bU : ℂ) * (σ0 : ℂ) + (aU : ℂ) * 0) * (aH : ℂ) +
          ((bU : ℂ) * 0 + (aU : ℂ) * (σ1 : ℂ)) * (-(bH : ℂ))) =
          (((bU * aH * σ0 - aU * bH * σ1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR, hσ0_ba, hσ1_ab]; congr 1; ring
    · have hL : (0 : ℂ) * 0 + (s_γ : ℂ) * (s_c : ℂ) = (((s_γ * s_c : ℝ) : ℂ)) := by push_cast; ring
      have hR : (((bU : ℂ) * (σ0 : ℂ) + (aU : ℂ) * 0) * (bH : ℂ) +
          ((bU : ℂ) * 0 + (aU : ℂ) * (σ1 : ℂ)) * (aH : ℂ)) =
          (((bU * bH * σ0 + aU * aH * σ1 : ℝ) : ℂ)) := by push_cast; ring
      rw [hL, hR, hσ0_bb, hσ1_aa]; congr 1; ring
  -- Compute schattenPow p H and schattenPow p S directly from the diagonalizations!
  have h1pc : 1 + c = 2 * t / (t + 1) := by dsimp [c]; field_simp [show t + 1 ≠ 0 by linarith]; ring
  have h1mc : 1 - c = 2 / (t + 1) := by dsimp [c]; field_simp [show t + 1 ≠ 0 by linarith]; ring
  have h1pγ : 1 + γ = 2 * t ^ β / (t ^ β + 1) := by
    dsimp [γ]; field_simp [show t ^ β + 1 ≠ 0 by linarith]; ring
  have h1mγ : 1 - γ = 2 / (t ^ β + 1) := by
    dsimp [γ]; field_simp [show t ^ β + 1 ≠ 0 by linarith]; ring
  have hPowH : schattenPow p (∑ j, matAbs (A j)) = (2 / (t + 1)) ^ p * (t ^ p + 1) := by
    rw [hSumH, hH_diag, schattenPow_unitary_mul_conjTranspose_right hp0.le,
      schattenPow_unitary_mul_left]
    have hd : ∀ i : Fin 2, 0 ≤ (if i = 0 then (1 + c) else (1 - c)) := fun i => by
      fin_cases i
      · change 0 ≤ 1 + c; linarith only [hc_nn]
      · change 0 ≤ 1 - c; linarith only [hc_lt1]
    have hdiag_eq : (fun i : Fin 2 => (if i = 0 then ((1 + c : ℝ) : ℂ) else ((1 - c : ℝ) : ℂ))) =
        (fun i : Fin 2 => (((if i = 0 then (1 + c) else (1 - c)) : ℝ) : ℂ)) := by
      ext i; fin_cases i <;> simp
    rw [hdiag_eq, schattenPow_diagonal hp0 _ hd, Fin.sum_univ_two]
    simp only [↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff, h1pc, h1mc]
    rw [show 2 * t / (t + 1) = (2 / (t + 1)) * t by ring,
      Real.mul_rpow (by positivity) ht0.le]; ring
  have hPowS : schattenPow p (∑ j, A j) =
      (2 / (t + 1)) ^ (p / 2) * (2 / (t ^ β + 1)) ^ (p / 2) * (t ^ β + 1) := by
    rw [hSumA, hS_svd, schattenPow_unitary_mul_conjTranspose_right hp0.le,
      schattenPow_unitary_mul_left]
    have hd : ∀ i : Fin 2, 0 ≤ (if i = 0 then σ0 else σ1) := fun i => by
      fin_cases i <;> simp [σ0, σ1]
    have hdiag_eq : (fun i : Fin 2 => (if i = 0 then (σ0 : ℂ) else (σ1 : ℂ))) =
        (fun i : Fin 2 => (((if i = 0 then σ0 else σ1) : ℝ) : ℂ)) := by
      ext i; fin_cases i <;> simp
    rw [hdiag_eq, schattenPow_diagonal hp0 _ hd, Fin.sum_univ_two]
    simp only [↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff, σ0, σ1, h1pc, h1mc, h1pγ, h1mγ]
    have hσ0_pow : (Real.sqrt (2 * t ^ β / (t ^ β + 1) * (2 * t / (t + 1)))) ^ p =
        (2 / (t + 1)) ^ (p / 2) * (2 / (t ^ β + 1)) ^ (p / 2) * t ^ β := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      have harg : 2 * t ^ β / (t ^ β + 1) * (2 * t / (t + 1)) =
          (2 / (t + 1)) * (2 / (t ^ β + 1)) * (t ^ β * t) := by ring
      rw [harg, show (1 / 2 : ℝ) * p = p / 2 by ring,
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      have ht_exp : (t ^ β * t) ^ (p / 2) = t ^ β := by
        rw [show t ^ β * t = t ^ (β + 1) by rw [Real.rpow_add ht0, Real.rpow_one],
          ← Real.rpow_mul ht0.le]
        congr 1; dsimp [β]; field_simp [h2mp.ne']; ring
      exact ht_exp
    have hσ1_pow : (Real.sqrt (2 / (t ^ β + 1) * (2 / (t + 1)))) ^ p =
        (2 / (t + 1)) ^ (p / 2) * (2 / (t ^ β + 1)) ^ (p / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), show (1 / 2 : ℝ) * p = p / 2 by ring,
        mul_comm (2 / (t ^ β + 1)), Real.mul_rpow (by positivity) (by positivity)]
    rw [hσ0_pow, hσ1_pow]; ring
  have hH_ne : (∑ j, matAbs (A j)) ≠ 0 := by
    intro h0
    have := congrArg (schattenPow p) h0
    rw [hPowH, schattenPow_zero hp0] at this
    have hpos : 0 < (2 / (t + 1)) ^ p * (t ^ p + 1) := by positivity
    linarith
  refine ⟨A, hH_ne, ?_⟩
  -- Simplify leeRatio p A = (schattenPow p S)^(1/p) / (schattenPow p H)^(1/p)!
  unfold leeRatio schattenNorm
  rw [hPowS, hPowH]
  have hS_norm : ((2 / (t + 1)) ^ (p / 2) * (2 / (t ^ β + 1)) ^ (p / 2) * (t ^ β + 1)) ^ (1 / p) =
      (2 / (t + 1)) ^ (1 / 2 : ℝ) * (2 ^ (1 / 2 : ℝ)) * (t ^ β + 1) ^ ((2 - p) / (2 * p)) := by
    have hmid : (2 / (t ^ β + 1)) ^ (1 / 2 : ℝ) * (t ^ β + 1) ^ (1 / p) =
        2 ^ (1 / 2 : ℝ) * (t ^ β + 1) ^ ((2 - p) / (2 * p)) := by
      rw [Real.div_rpow (by norm_num) (by positivity),
        show (2 : ℝ) ^ (1 / 2 : ℝ) / (t ^ β + 1) ^ (1 / 2 : ℝ) * (t ^ β + 1) ^ (1 / p) =
          2 ^ (1 / 2 : ℝ) * ((t ^ β + 1) ^ (1 / p) * (t ^ β + 1) ^ (-(1 / 2 : ℝ))) by
          rw [Real.rpow_neg (by positivity)]; ring,
        ← Real.rpow_add (by positivity), show 1 / p + -(1 / 2 : ℝ) = (2 - p) / (2 * p) by
          field_simp [hp0.ne']; ring]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      show p / 2 * (1 / p) = (1 / 2 : ℝ) by field_simp [hp0.ne'],
      mul_assoc, hmid, mul_assoc]
  have hH_norm : ((2 / (t + 1)) ^ p * (t ^ p + 1)) ^ (1 / p) =
      (2 / (t + 1)) * (t ^ p + 1) ^ (1 / p) := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by positivity), mul_one_div_cancel hp0.ne', Real.rpow_one]
  rw [hS_norm, hH_norm]
  have hratio_front : (2 / (t + 1)) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) / (2 / (t + 1)) =
      Real.sqrt (t + 1) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow (by norm_num) (by positivity)]
    have h2 : (2 : ℝ) ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have htp : (t + 1) ^ (1 / 2 : ℝ) * (t + 1) ^ (1 / 2 : ℝ) = t + 1 := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have hne1 : (t + 1) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
    have hne2 : t + 1 ≠ 0 := by linarith
    field_simp [hne1, hne2]
    rw [sq, sq, h2, htp]
  have hden_ne : (t ^ p + 1) ^ (1 / p) ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have h2t_ne : 2 / (t + 1) ≠ 0 := (div_pos (by norm_num) (by linarith)).ne'
  calc (2 / (t + 1)) ^ (1 / 2 : ℝ) * 2 ^ (1 / 2 : ℝ) * (t ^ β + 1) ^ ((2 - p) / (2 * p)) /
        (2 / (t + 1) * (t ^ p + 1) ^ (1 / p))
      = ((2 / (t + 1)) ^ (1 / 2 : ℝ) * 2 ^ (1 / 2 : ℝ) / (2 / (t + 1))) *
        (t ^ β + 1) ^ ((2 - p) / (2 * p)) / (t ^ p + 1) ^ (1 / p) := by ring
    _ = Real.sqrt (t + 1) * (t ^ β + 1) ^ ((2 - p) / (2 * p)) / (t ^ p + 1) ^ (1 / p) := by
        rw [hratio_front]

/-- Theorem 3 (Part A — Universal 2×2 Collapse for 1 < p < 2):
    For ALL 1 < p < 2 and ALL m ≥ 2, C_{p,m}(2) = C_{p,2}(2)! -/
theorem theorem3_universal_2x2_collapse {m : ℕ} (hm : 2 ≤ m) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    leeConst p m 2 = leeConst p 2 2 := by
  have hp0 : 0 < p := by linarith
  have h2mp : 0 < 2 - p := by linarith
  apply le_antisymm
  · -- Upper bound: every m-tuple in ℂ^{2×2} has ratio ≤ leeConst p 2 2 via exists_2x2_rankOne_witness!
    obtain ⟨A, hH_ne, hC_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := 2) hp1 (by omega : 1 ≤ m) (by norm_num : 1 ≤ 2)
    rw [← hC_eq]
    set H : Mat 2 := ∑ j, matAbs (A j)
    have hH : H.PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    have hbound := schattenNorm_sq_le_trace_mul_rpow hp1 hp2 A
    dsimp only at hbound
    set l0 : ℝ := hH.isHermitian.eigenvalues 0
    set l1 : ℝ := hH.isHermitian.eigenvalues 1
    have hl0 : 0 ≤ l0 := hH.eigenvalues_nonneg 0
    have hl1 : 0 ≤ l1 := hH.eigenvalues_nonneg 1
    have hPowH : schattenPow p H = l0 ^ p + l1 ^ p := by
      have hH_eq : H = (hH.isHermitian.eigenvectorUnitary : Mat 2) *
          Matrix.diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) *
          (hH.isHermitian.eigenvectorUnitary : Mat 2)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hH.isHermitian.spectral_theorem
      rw [hH_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
        schattenPow_diagonal hp0 _ hH.eigenvalues_nonneg, Fin.sum_univ_two]
    have hH_norm_pos : 0 < schattenNorm p H := schattenNorm_pos_of_ne_zero hp0 hH_ne
    -- Split whether min(l0, l1) = 0 (ratio ≤ 1 < leeConst p 2 2) or > 0 (t = max/min ≥ 1)!
    let a : ℝ := max l0 l1
    let b : ℝ := min l0 l1
    have ha_nn : 0 ≤ a := le_max_of_le_left hl0
    have hb_nn : 0 ≤ b := le_min hl0 hl1
    have hsum1 : ∑ i : Fin 2, hH.isHermitian.eigenvalues i = a + b := by
      rw [Fin.sum_univ_two]; exact (max_add_min l0 l1).symm
    have hsum_β : ∑ i : Fin 2, (hH.isHermitian.eigenvalues i) ^ (p / (2 - p)) =
        a ^ (p / (2 - p)) + b ^ (p / (2 - p)) := by
      rw [Fin.sum_univ_two]
      change l0 ^ (p / (2 - p)) + l1 ^ (p / (2 - p)) = a ^ (p / (2 - p)) + b ^ (p / (2 - p))
      rcases le_total l0 l1 with h | h <;> simp [a, b, h, add_comm]
    have hsum_p : l0 ^ p + l1 ^ p = a ^ p + b ^ p := by
      rcases le_total l0 l1 with h | h <;> simp [a, b, h, add_comm]
    by_cases hb0 : b = 0
    · -- Ratio ≤ 1 < leeConst p 2 2!
      have hle1 : leeRatio p A ≤ 1 := by
        have hS_le : schattenNorm p (∑ j, A j) ≤ a := by
          have h1 : (schattenNorm p (∑ j, A j)) ^ 2 ≤ a ^ 2 := by
            rw [hsum1, hsum_β, hb0, add_zero, Real.zero_rpow (div_pos hp0 h2mp).ne', add_zero,
              ← Real.rpow_mul ha_nn, show p / (2 - p) * ((2 - p) / p) = 1 by field_simp [hp0.ne', h2mp.ne'],
              Real.rpow_one, ← sq] at hbound
            exact hbound
          nlinarith [schattenNorm_nonneg p (∑ j, A j)]
        have hH_eq_a : schattenNorm p H = a := by
          unfold schattenNorm; rw [hPowH, hsum_p, hb0, Real.zero_rpow hp0.ne', add_zero,
            ← Real.rpow_mul ha_nn, mul_one_div_cancel hp0.ne', Real.rpow_one]
        unfold leeRatio; rw [hH_eq_a]; exact (div_le_one (hH_eq_a ▸ hH_norm_pos)).mpr hS_le
      exact hle1.trans (one_lt_leeConst_two hp1 le_rfl).le
    · have hb_pos : 0 < b := lt_of_le_of_ne hb_nn (Ne.symm hb0)
      let t : ℝ := a / b
      have ht_ge1 : 1 ≤ t := (one_le_div hb_pos).mpr (min_le_max)
      obtain ⟨W, hW_ne, hW_ratio⟩ := exists_2x2_rankOne_witness (m := 2) le_rfl hp1 hp2 ht_ge1
      have hW_le : leeRatio p W ≤ leeConst p 2 2 :=
        le_csSup (leeConst_bddAbove hp1) ⟨W, hW_ne, rfl⟩
      refine le_trans ?_ (hW_ratio ▸ hW_le)
      -- Show leeRatio p A ≤ √(t+1) * (t^(p/(2-p)) + 1)^((2-p)/(2p)) / (t^p + 1)^(1/p)!
      have ha_eq : a = b * t := by dsimp [t]; field_simp [hb_pos.ne']
      have hS_le : schattenNorm p (∑ j, A j) ≤
          b * (Real.sqrt (t + 1) * (t ^ (p / (2 - p)) + 1) ^ ((2 - p) / (2 * p))) := by
        rw [hsum1, hsum_β, ha_eq] at hbound
        have h1 : (b * t + b) * ((b * t) ^ (p / (2 - p)) + b ^ (p / (2 - p))) ^ ((2 - p) / p) =
            (b * (Real.sqrt (t + 1) * (t ^ (p / (2 - p)) + 1) ^ ((2 - p) / (2 * p)))) ^ 2 := by
          have hfact1 : b * t + b = b * (t + 1) := by ring
          have hfact2 : (b * t) ^ (p / (2 - p)) + b ^ (p / (2 - p)) =
              b ^ (p / (2 - p)) * (t ^ (p / (2 - p)) + 1) := by
            rw [Real.mul_rpow hb_pos.le (by linarith)]; ring
          have hsq_rpow : ((t ^ (p / (2 - p)) + 1) ^ ((2 - p) / (2 * p))) ^ 2 =
              (t ^ (p / (2 - p)) + 1) ^ ((2 - p) / p) := by
            rw [← Real.rpow_two, ← Real.rpow_mul (by positivity),
              show (2 - p) / (2 * p) * 2 = (2 - p) / p by field_simp [hp0.ne']]
          rw [hfact1, hfact2, Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hb_pos.le, show p / (2 - p) * ((2 - p) / p) = 1 by field_simp [hp0.ne', h2mp.ne'],
            Real.rpow_one, mul_pow, mul_pow, Real.sq_sqrt (by linarith), hsq_rpow]; ring
        rw [h1] at hbound
        nlinarith [schattenNorm_nonneg p (∑ j, A j),
          mul_nonneg hb_pos.le (mul_nonneg (Real.sqrt_nonneg (t + 1))
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ t ^ (p / (2 - p)) + 1) ((2 - p) / (2 * p))))]
      have hH_eq_b : schattenNorm p H = b * (t ^ p + 1) ^ (1 / p) := by
        unfold schattenNorm
        rw [hPowH, hsum_p, ha_eq, Real.mul_rpow hb_pos.le (by linarith),
          show b ^ p * t ^ p + b ^ p = b ^ p * (t ^ p + 1) by ring,
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hb_pos.le, mul_one_div_cancel hp0.ne', Real.rpow_one]
      unfold leeRatio
      rw [hH_eq_b]
      calc schattenNorm p (∑ j, A j) / (b * (t ^ p + 1) ^ (1 / p))
          ≤ (b * (Real.sqrt (t + 1) * (t ^ (p / (2 - p)) + 1) ^ ((2 - p) / (2 * p)))) /
            (b * (t ^ p + 1) ^ (1 / p)) :=
            div_le_div_of_nonneg_right hS_le (by positivity)
        _ = Real.sqrt (t + 1) * (t ^ (p / (2 - p)) + 1) ^ ((2 - p) / (2 * p)) /
            (t ^ p + 1) ^ (1 / p) := by
            rw [mul_div_mul_left _ _ hb_pos.ne']
  · -- Lower bound: pad any 2-tuple with (m - 2) zero matrices!
    obtain ⟨A, hH_ne, hC_eq, _⟩ := exists_leeConst_maximizer (m := 2) (n := 2) hp1 (by norm_num : 1 ≤ 2) (by norm_num : 1 ≤ 2)
    rw [← hC_eq]
    let B : Fin m → Mat 2 := fun j => if hj : j.val < 2 then A ⟨j.val, hj⟩ else 0
    have hSB : ∑ j : Fin m, B j = ∑ j : Fin 2, A j := by
      let j0 : Fin m := ⟨0, by omega⟩
      let j1 : Fin m := ⟨1, by omega⟩
      have hj01 : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; dsimp [j0, j1] at this; omega
      have h1 : ∑ j : Fin m, B j = B j0 + B j1 + ∑ j ∈ (Finset.univ.erase j0).erase j1, B j := by
        rw [← Finset.add_sum_erase _ B (Finset.mem_univ j0)]
        have hmem1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj01.symm, Finset.mem_univ j1⟩
        rw [← Finset.add_sum_erase _ B hmem1]; abel
      have hrest : ∑ j ∈ (Finset.univ.erase j0).erase j1, B j = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne1 : j ≠ j1 := (Finset.mem_erase.mp hj).1
        have hne0 : j ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hge : ¬ j.val < 2 := by
          intro hlt; have : j.val = 0 ∨ j.val = 1 := by omega
          rcases this with h | h
          · exact hne0 (Fin.ext h)
          · exact hne1 (Fin.ext h)
        simp only [B, hge, ↓reduceDIte]
      rw [h1, hrest, add_zero, Fin.sum_univ_two]
      simp [B, j0, j1]
    have hHB : ∑ j : Fin m, matAbs (B j) = ∑ j : Fin 2, matAbs (A j) := by
      let j0 : Fin m := ⟨0, by omega⟩
      let j1 : Fin m := ⟨1, by omega⟩
      have hj01 : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; dsimp [j0, j1] at this; omega
      have h1 : ∑ j : Fin m, matAbs (B j) = matAbs (B j0) + matAbs (B j1) +
          ∑ j ∈ (Finset.univ.erase j0).erase j1, matAbs (B j) := by
        rw [← Finset.add_sum_erase _ (fun j => matAbs (B j)) (Finset.mem_univ j0)]
        have hmem1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj01.symm, Finset.mem_univ j1⟩
        rw [← Finset.add_sum_erase _ (fun j => matAbs (B j)) hmem1]; abel
      have hrest : ∑ j ∈ (Finset.univ.erase j0).erase j1, matAbs (B j) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        have hne1 : j ≠ j1 := (Finset.mem_erase.mp hj).1
        have hne0 : j ≠ j0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hge : ¬ j.val < 2 := by
          intro hlt; have : j.val = 0 ∨ j.val = 1 := by omega
          rcases this with h | h
          · exact hne0 (Fin.ext h)
          · exact hne1 (Fin.ext h)
        simp only [B, hge, ↓reduceDIte, matAbs_zero]
      rw [h1, hrest, add_zero, Fin.sum_univ_two]
      simp [B, j0, j1]
    have hrat : leeRatio p B = leeRatio p A := by simp [leeRatio, hSB, hHB]
    rw [← hrat]
    exact le_csSup (leeConst_bddAbove hp1) ⟨B, hHB ▸ hH_ne, rfl⟩

/-- Theorem 3 (Part B — Exact Closed Form at p = 3/2):
    For ALL m ≥ 2,
      C_{3/2,m}(2) = ((107 + 51 * √17) / 256) ^ (1 / 6). -/
theorem theorem3_exact_p32 {m : ℕ} (hm : 2 ≤ m) :
    leeConst (3 / 2) m 2 = ((107 + 51 * Real.sqrt 17) / 256) ^ (1 / 6 : ℝ) := by
  have hp1 : (1 : ℝ) < 3 / 2 := by norm_num
  have hp2 : (3 / 2 : ℝ) < 2 := by norm_num
  have hp0 : (0 : ℝ) < 3 / 2 := by norm_num
  set Cval : ℝ := ((107 + 51 * Real.sqrt 17) / 256) ^ (1 / 6 : ℝ)
  have hCval_pos : 0 < Cval := Real.rpow_pos_of_pos (by positivity) _
  have hCval6 : Cval ^ 6 = (107 + 51 * Real.sqrt 17) / 256 := by
    rw [← Real.rpow_natCast, show (6 : ℕ) = (6 : ℝ) by norm_num,
      show Cval = ((107 + 51 * Real.sqrt 17) / 256) ^ (1 / 6 : ℝ) from rfl,
      ← Real.rpow_mul (by positivity)]
    norm_num
  apply le_antisymm
  · -- Upper bound via p32_global_polynomial_ineq!
    obtain ⟨A, hH_ne, hC_eq, _⟩ := exists_leeConst_maximizer (m := m) (n := 2) hp1 (by omega : 1 ≤ m) (by norm_num : 1 ≤ 2)
    rw [← hC_eq]
    set H : Mat 2 := ∑ j, matAbs (A j)
    have hH : H.PosSemidef := by
      have : ∀ s : Finset (Fin m), (∑ j ∈ s, matAbs (A j)).PosSemidef := by
        intro s; induction s using Finset.induction_on with
        | empty => simpa using Matrix.PosSemidef.zero
        | insert a s ha ih => rw [Finset.sum_insert ha]; exact (matAbs_posSemidef (A a)).add ih
      exact this Finset.univ
    have hbound := schattenNorm_sq_le_trace_mul_rpow hp1 hp2 A
    dsimp only at hbound
    set l0 : ℝ := hH.isHermitian.eigenvalues 0
    set l1 : ℝ := hH.isHermitian.eigenvalues 1
    let u : ℝ := Real.sqrt l0
    let v : ℝ := Real.sqrt l1
    have hu : 0 ≤ u := Real.sqrt_nonneg _
    have hv : 0 ≤ v := Real.sqrt_nonneg _
    have hl0 : l0 = u ^ 2 := (Real.sq_sqrt (hH.eigenvalues_nonneg 0)).symm
    have hl1 : l1 = v ^ 2 := (Real.sq_sqrt (hH.eigenvalues_nonneg 1)).symm
    have hPowH : schattenPow (3 / 2) H = u ^ 3 + v ^ 3 := by
      have hH_eq : H = (hH.isHermitian.eigenvectorUnitary : Mat 2) *
          Matrix.diagonal (fun i => (hH.isHermitian.eigenvalues i : ℂ)) *
          (hH.isHermitian.eigenvectorUnitary : Mat 2)ᴴ := by
        simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def]
          using hH.isHermitian.spectral_theorem
      rw [hH_eq, schattenPow_unitary_mul_conjTranspose_right hp0.le, schattenPow_unitary_mul_left,
        schattenPow_diagonal hp0 _ hH.eigenvalues_nonneg, Fin.sum_univ_two]
      change l0 ^ (3 / 2 : ℝ) + l1 ^ (3 / 2 : ℝ) = u ^ 3 + v ^ 3
      rw [hl0, hl1, ← Real.rpow_two, ← Real.rpow_two, ← Real.rpow_mul hu, ← Real.rpow_mul hv]
      norm_num
    have hH6 : (schattenNorm (3 / 2) H) ^ 6 = (u ^ 3 + v ^ 3) ^ 4 := by
      have h1 : schattenNorm (3 / 2) H = (u ^ 3 + v ^ 3) ^ (2 / 3 : ℝ) := by
        unfold schattenNorm; rw [hPowH]; norm_num
      rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have hS6 : (schattenNorm (3 / 2) (∑ j, A j)) ^ 6 ≤ (u ^ 2 + v ^ 2) ^ 3 * (u ^ 6 + v ^ 6) := by
      have hexp1 : (3 / 2 : ℝ) / (2 - 3 / 2) = 3 := by norm_num
      have hexp2 : (2 - 3 / 2 : ℝ) / (3 / 2) = 1 / 3 := by norm_num
      rw [hexp1, hexp2, Fin.sum_univ_two, Fin.sum_univ_two] at hbound
      change (schattenNorm (3 / 2) (∑ j, A j)) ^ 2 ≤
        (l0 + l1) * (l0 ^ (3 : ℝ) + l1 ^ (3 : ℝ)) ^ (1 / 3 : ℝ) at hbound
      rw [hl0, hl1] at hbound
      have hcube : ((schattenNorm (3 / 2) (∑ j, A j)) ^ 2) ^ 3 ≤
          ((u ^ 2 + v ^ 2) * ((u ^ 2) ^ (3 : ℝ) + (v ^ 2) ^ (3 : ℝ)) ^ (1 / 3 : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (sq_nonneg _) hbound 3
      have hL : ((schattenNorm (3 / 2) (∑ j, A j)) ^ 2) ^ 3 = (schattenNorm (3 / 2) (∑ j, A j)) ^ 6 := by ring
      have hR : ((u ^ 2 + v ^ 2) * ((u ^ 2) ^ (3 : ℝ) + (v ^ 2) ^ (3 : ℝ)) ^ (1 / 3 : ℝ)) ^ 3 =
          (u ^ 2 + v ^ 2) ^ 3 * (u ^ 6 + v ^ 6) := by
        have hcube_rpow : (((u ^ 2) ^ (3 : ℝ) + (v ^ 2) ^ (3 : ℝ)) ^ (1 / 3 : ℝ)) ^ 3 =
            (u ^ 2) ^ (3 : ℝ) + (v ^ 2) ^ (3 : ℝ) := by
          rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num
        rw [mul_pow, hcube_rpow]
        have h1 : (u ^ 2) ^ (3 : ℝ) = u ^ 6 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
        have h2 : (v ^ 2) ^ (3 : ℝ) = v ^ 6 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
        rw [h1, h2]
      linarith
    have hpoly := p32_global_polynomial_ineq hu hv
    have hratio6 : (leeRatio (3 / 2) A) ^ 6 ≤ Cval ^ 6 := by
      have hH_pos : 0 < schattenNorm (3 / 2) H := schattenNorm_pos_of_ne_zero hp0 hH_ne
      unfold leeRatio
      rw [div_pow, hH6, hCval6, div_le_iff₀ (by rw [← hH6]; positivity)]
      linarith
    by_contra hgt; push Not at hgt
    have := pow_lt_pow_left₀ hgt hCval_pos.le (by norm_num : 6 ≠ 0)
    linarith
  · -- Lower bound: witness at y_* = (1 + √17 + √(2 + 2√17)) / 4 where 2 y_*^2 - (1 + √17) y_* + 2 = 0!
    set s17 : ℝ := Real.sqrt 17
    have hs17_pos : 0 < s17 := Real.sqrt_pos.mpr (by norm_num)
    have hs17_sq : s17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have hs17_gt4 : 4 < s17 := by nlinarith
    let rD : ℝ := Real.sqrt (2 + 2 * s17)
    have hrD_sq : rD ^ 2 = 2 + 2 * s17 := Real.sq_sqrt (by linarith)
    let ystar : ℝ := (1 + s17 + rD) / 4
    have hystar_ge1 : 1 ≤ ystar := by
      have hrD_nn : 0 ≤ rD := Real.sqrt_nonneg _
      dsimp [ystar]; linarith
    have hcrit : 2 * ystar ^ 2 - (1 + s17) * ystar + 2 = 0 := by
      dsimp [ystar]; nlinarith [hs17_sq, hrD_sq]
    let tstar : ℝ := ystar ^ 2
    have htstar_ge1 : 1 ≤ tstar := by dsimp [tstar]; nlinarith
    obtain ⟨W, hW_ne, hW_ratio⟩ := exists_2x2_rankOne_witness hm hp1 hp2 htstar_ge1
    have hW_le : leeRatio (3 / 2) W ≤ leeConst (3 / 2) m 2 :=
      le_csSup (leeConst_bddAbove hp1) ⟨W, hW_ne, rfl⟩
    have hW_eq : leeRatio (3 / 2) W = Cval := by
      have hW_nn : 0 ≤ leeRatio (3 / 2) W := by
        rw [hW_ratio]; positivity
      have hW6 : (leeRatio (3 / 2) W) ^ 6 = (ystar ^ 2 + 1) ^ 3 * (ystar ^ 6 + 1) / (ystar ^ 3 + 1) ^ 4 := by
        rw [hW_ratio]
        have hexp1 : (3 / 2 : ℝ) / (2 - 3 / 2) = 3 := by norm_num
        have hexp2 : (2 - 3 / 2 : ℝ) / (2 * (3 / 2)) = 1 / 6 := by norm_num
        have hexp3 : (1 : ℝ) / (3 / 2) = 2 / 3 := by norm_num
        rw [hexp1, hexp2, hexp3, div_pow, mul_pow]
        have h1 : (Real.sqrt (tstar + 1)) ^ 6 = (ystar ^ 2 + 1) ^ 3 := by
          have : (Real.sqrt (tstar + 1)) ^ 6 = ((Real.sqrt (tstar + 1)) ^ 2) ^ 3 := by ring
          rw [this, Real.sq_sqrt (by linarith)]
        have h2 : ((tstar ^ (3 : ℝ) + 1) ^ (1 / 6 : ℝ)) ^ 6 = ystar ^ 6 + 1 := by
          rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul (by positivity)]
          norm_num
          dsimp [tstar]; ring
        have h3 : ((tstar ^ (3 / 2 : ℝ) + 1) ^ (2 / 3 : ℝ)) ^ 6 = (ystar ^ 3 + 1) ^ 4 := by
          rw [← Real.rpow_natCast _ 6, ← Real.rpow_mul (by positivity)]
          norm_num
          have ht32 : tstar ^ (3 / 2 : ℝ) = ystar ^ 3 := by
            dsimp [tstar]; rw [← Real.rpow_two, ← Real.rpow_mul (by linarith)]; norm_num
          rw [ht32]
        rw [h1, h2, h3]
      have hid := p32_global_polynomial_identity ystar 1
      simp only [one_pow, mul_one] at hid
      rw [hcrit, zero_pow (by norm_num : 2 ≠ 0), zero_mul] at hid
      have hW6_eq : (leeRatio (3 / 2) W) ^ 6 = Cval ^ 6 := by
        rw [hW6, hCval6, div_eq_div_iff (by positivity) (by norm_num)]
        linarith
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := pow_lt_pow_left₀ hlt hW_nn (by norm_num : 6 ≠ 0); linarith
      · have := pow_lt_pow_left₀ hgt hCval_pos.le (by norm_num : 6 ≠ 0); linarith
    exact hW_eq ▸ hW_le


/-! ==========================================================================
    PART 2: Theorem 4 (p = 3/2) — End-to-End Pure-Integer Operator-Monotone
            Sylvester Certificate in Mathlib Proving C_{3/2,2}(2) < C_{3/2,2}(3)
    ========================================================================== -/

namespace Cert3.Mat3

/-- Embed an exact integer 3×3 matrix into Mathlib's `Mat 3 = Matrix (Fin 3) (Fin 3) ℂ`. -/
def toMat (X : Mat3) : Mat 3 :=
  Matrix.of ![![(X.m00 : ℂ), (X.m01 : ℂ), (X.m02 : ℂ)],
    ![(X.m10 : ℂ), (X.m11 : ℂ), (X.m12 : ℂ)],
    ![(X.m20 : ℂ), (X.m21 : ℂ), (X.m22 : ℂ)]]

lemma toMat_add (X Y : Mat3) : (add X Y).toMat = X.toMat + Y.toMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [add, toMat]

lemma toMat_sub (X Y : Mat3) : (sub X Y).toMat = X.toMat - Y.toMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sub, toMat]

lemma toMat_scale (c : ℤ) (X : Mat3) : (scale c X).toMat = (c : ℂ) • X.toMat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [scale, toMat]

lemma toMat_trans (X : Mat3) : X.trans.toMat = X.toMatᴴ := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [trans, toMat, Matrix.conjTranspose_apply]

lemma toMat_mul (X Y : Mat3) : (mul X Y).toMat = X.toMat * Y.toMat := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [mul, toMat, Matrix.mul_apply, Fin.sum_univ_three]

lemma toMat_diag (a b c : ℤ) :
    (diag a b c).toMat = Matrix.diagonal ![(a : ℂ), (b : ℂ), (c : ℂ)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag, toMat]

/-- Soundness of Sylvester's criterion in Mathlib: if `X.IsSymPosDef`, then `X.toMat.PosSemidef`!
    Proved directly over `ℂ` via the exact scaled Hermitian LDLᴴ sum-of-norms identity:
      Δ1 * Δ2 * Re(vᴴ X v) = Δ2 * ‖u1‖² + ‖u2‖² + m00 * Δ3 * ‖v2‖² ≥ 0. -/
theorem toMat_posSemidef_of_isSymPosDef (X : Mat3) (hX : X.IsSymPosDef) :
    X.toMat.PosSemidef := by
  rcases hX with ⟨hsym, hd1, hd2, hd3⟩
  have h01 : X.m10 = X.m01 := by simpa [trans] using congrArg Mat3.m10 hsym
  have h02 : X.m20 = X.m02 := by simpa [trans] using congrArg Mat3.m20 hsym
  have h12 : X.m21 = X.m12 := by simpa [trans] using congrArg Mat3.m21 hsym
  have hHerm : X.toMat.IsHermitian := by
    rw [Matrix.IsHermitian, ← toMat_trans, ← hsym]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hHerm, fun v => ?_⟩
  rw [Complex.nonneg_iff]
  refine ⟨?_, (isHermitian_im_dotProduct_mulVec_self hHerm v).symm⟩
  let Δ1 : ℝ := (X.minor1 : ℝ)
  let Δ2 : ℝ := (X.minor2 : ℝ)
  let Δ3 : ℝ := (X.minor3 : ℝ)
  have hΔ1 : 0 < Δ1 := by dsimp [Δ1]; exact_mod_cast hd1
  have hΔ2 : 0 < Δ2 := by dsimp [Δ2]; exact_mod_cast hd2
  have hΔ3 : 0 < Δ3 := by dsimp [Δ3]; exact_mod_cast hd3
  let u1 : ℂ := (X.m00 : ℂ) * v 0 + (X.m01 : ℂ) * v 1 + (X.m02 : ℂ) * v 2
  let u2 : ℂ := (X.minor2 : ℂ) * v 1 + ((X.m00 * X.m12 - X.m01 * X.m02 : ℤ) : ℂ) * v 2
  -- Exact complex Hermitian completion-of-squares identity!
  have hid : ((Δ1 * Δ2 : ℝ) : ℂ) * (star v ⬝ᵥ X.toMat.mulVec v) =
      ((Δ2 : ℝ) : ℂ) * (star u1 * u1) + (star u2 * u2) +
      (((X.m00 : ℝ) * Δ3 : ℝ) : ℂ) * (star (v 2) * v 2) := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three, toMat, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Pi.star_apply, u1, u2,
      Δ1, Δ2, Δ3, minor1, minor2, minor3, h01, h02, h12, star_add, star_sub, star_mul',
      Complex.star_def, map_intCast, Int.cast_mul, Int.cast_sub, Int.cast_add,
      Complex.ofReal_intCast, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add]
    ring
  have hre := congrArg Complex.re hid
  have hre_lhs : (((Δ1 * Δ2 : ℝ) : ℂ) * (star v ⬝ᵥ X.toMat.mulVec v)).re =
      (Δ1 * Δ2) * (star v ⬝ᵥ X.toMat.mulVec v).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hre_sq : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hre_r1 : (((Δ2 : ℝ) : ℂ) * (star u1 * u1)).re = Δ2 * (star u1 * u1).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hre_r2 : ((((X.m00 : ℝ) * Δ3 : ℝ) : ℂ) * (star (v 2) * v 2)).re =
      ((X.m00 : ℝ) * Δ3) * (star (v 2) * v 2).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  rw [hre_lhs, Complex.add_re, Complex.add_re, hre_r1, hre_r2,
    hre_sq u1, hre_sq u2, hre_sq (v 2)] at hre
  have hm00 : (0 : ℝ) < (X.m00 : ℝ) := hΔ1
  have hrhs_nn : 0 ≤ Δ2 * ‖u1‖ ^ 2 + ‖u2‖ ^ 2 + (X.m00 : ℝ) * Δ3 * ‖v 2‖ ^ 2 := by positivity
  nlinarith [mul_pos hΔ1 hΔ2]

end Cert3.Mat3

set_option maxHeartbeats 600000 in
/-- Theorem 4 (End-to-End Machine-Checked Explicit 3×3 Integer Counterexample at p = 3/2):
    For A = [[49, 62, -1], [11, 14, 0], [0, 0, 0]] and B = diag(81, 0, 0),
    the Mathlib Schatten-(3/2) Lee ratio strictly exceeds C_{3/2,2}(2) = ((107 + 51√17)/256)^(1/6),
    certifying C_{3/2,2}(2) < C_{3/2,2}(3) with zero floating-point arithmetic! -/
theorem theorem4_witness_p32 :
    let A : Mat 3 := Cert3.A_mat.toMat
    let B : Mat 3 := Cert3.B_mat.toMat
    (∑ j : Fin 2, matAbs (![A, B] j)) ≠ 0 ∧
      leeConst (3 / 2) 2 2 < leeRatio (3 / 2) ![A, B] := by
  intro A B
  have hp1 : (1 : ℝ) < 3 / 2 := by norm_num
  have hp0 : (0 : ℝ) < 3 / 2 := by norm_num
  -- Part 1: Operator-monotone upper bound on ‖H‖_{3/2}^{3/2} ≤ (d1^3 + d2^3 + d3^3) / N_D^3
  let H : Mat 3 := matAbs A + matAbs B
  have hSumH : ∑ j : Fin 2, matAbs (![A, B] j) = H := by simp [H, Fin.sum_univ_two]
  have hSumS : ∑ j : Fin 2, (![A, B] j) = Cert3.S_mat.toMat := by
    rw [Fin.sum_univ_two]; exact (Cert3.Mat3.toMat_add Cert3.A_mat Cert3.B_mat).symm
  have hB_abs : matAbs B = B := by
    have hB_psd : B.PosSemidef := by
      have : B = Matrix.diagonal ![(81 : ℂ), 0, 0] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [B, Cert3.B_mat, Cert3.Mat3.toMat]
      rw [this, Matrix.posSemidef_diagonal_iff]; intro i; fin_cases i <;> simp
    exact matAbs_eq_of_posSemidef_sq hB_psd (by rw [hB_psd.isHermitian.eq])
  let UA : Mat 3 := (((Cert3.N_A : ℝ)⁻¹ : ℝ) : ℂ) • Cert3.UA_mat.toMat
  have hNA_pos : (0 : ℝ) < (Cert3.N_A : ℝ) := by norm_num [Cert3.N_A]
  have hUA_psd : UA.PosSemidef := by
    have h1 := Cert3.Mat3.toMat_posSemidef_of_isSymPosDef Cert3.UA_mat Cert3.cert1_UA_posdef
    have : UA = (Cert3.N_A : ℝ)⁻¹ • Cert3.UA_mat.toMat := by ext i j; simp [UA, Complex.real_smul]
    rw [this]; exact h1.smul (inv_pos.mpr hNA_pos).le
  -- From Cert 2: (UA^2 - Aᴴ A).PosSemidef → by Löwner–Heinz at q = 1/2, (UA - |A|).PosSemidef!
  have hUA_ge_absA : (UA - matAbs A).PosSemidef := by
    have hcert2 := Cert3.Mat3.toMat_posSemidef_of_isSymPosDef _ Cert3.cert2_operator_monotone_bound
    rw [Cert3.Mat3.toMat_sub, Cert3.Mat3.toMat_mul, Cert3.Mat3.toMat_scale,
      Cert3.Mat3.toMat_mul, Cert3.Mat3.toMat_trans] at hcert2
    have hdiff_sq : UA * UA - Aᴴ * A =
        (((Cert3.N_A : ℝ) ^ 2)⁻¹ : ℝ) •
          (Cert3.UA_mat.toMat * Cert3.UA_mat.toMat -
            ((Cert3.N_A * Cert3.N_A : ℤ) : ℂ) • (Aᴴ * A)) := by
      ext i j
      simp only [UA, Matrix.sub_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
        smul_eq_mul, Complex.real_smul, Int.cast_mul, Complex.ofReal_inv, Complex.ofReal_pow,
        Complex.ofReal_intCast]
      have hne : ((Cert3.N_A : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hNA_pos.ne'
      field_simp [hne]
    have hsq_psd : (UA * UA - Aᴴ * A).PosSemidef := by
      rw [hdiff_sq]; exact hcert2.smul (inv_nonneg.mpr (sq_nonneg _))
    have hUA2_psd : (UA * UA).PosSemidef := by
      simpa [hUA_psd.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self UA
    have hlow := psdPow_mono_of_posSemidef (q := 1 / 2) (by norm_num) (by norm_num)
      (Matrix.posSemidef_conjTranspose_mul_self A) hUA2_psd hsq_psd
    -- Show psdPow (1/2) (UA * UA) = UA and psdPow (1/2) (Aᴴ * A) = matAbs A directly via matAbs_eq_of_posSemidef_sq!
    have hpsdHalf_sq : ∀ M : Mat 3, M.PosSemidef → psdPow (1 / 2) M * psdPow (1 / 2) M = M := fun M hM => by
      rw [psdPow_eq_spectral (by norm_num) hM]
      let UM := hM.isHermitian.eigenvectorUnitary
      let lamM := hM.isHermitian.eigenvalues
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (UM : Mat 3)ᴴ (UM : Mat 3), unitary_conjTranspose_mul_self UM,
        Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
      have hdiag : Matrix.diagonal (fun i => (((lamM i) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((lamM i) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
          Matrix.diagonal (fun i => (lamM i : ℂ)) := by
        congr 1; ext i
        rw [← Complex.ofReal_mul]; congr 1
        dsimp only [lamM]
        rcases eq_or_lt_of_le (hM.eigenvalues_nonneg i) with h0 | hpos
        · rw [← h0, Real.zero_rpow (by norm_num), zero_mul]
        · rw [← Real.rpow_add hpos]; norm_num
      rw [hdiag]
      simpa [UM, lamM, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def,
        Matrix.mul_assoc] using hM.isHermitian.spectral_theorem.symm
    have hL : psdPow (1 / 2) (UA * UA) = UA := by
      have hQ_psd : (psdPow (1 / 2) (UA * UA)).PosSemidef := psdPow_posSemidef (by norm_num) hUA2_psd
      have h1 : matAbs UA = psdPow (1 / 2) (UA * UA) :=
        matAbs_eq_of_posSemidef_sq hQ_psd (by rw [hpsdHalf_sq _ hUA2_psd, hUA_psd.isHermitian.eq])
      have h2 : matAbs UA = UA := matAbs_eq_of_posSemidef_sq hUA_psd (by rw [hUA_psd.isHermitian.eq])
      rw [← h1, h2]
    have hR : psdPow (1 / 2) (Aᴴ * A) = matAbs A := by
      have hG_psd := Matrix.posSemidef_conjTranspose_mul_self A
      have hQ_psd : (psdPow (1 / 2) (Aᴴ * A)).PosSemidef := psdPow_posSemidef (by norm_num) hG_psd
      exact (matAbs_eq_of_posSemidef_sq hQ_psd (hpsdHalf_sq _ hG_psd)).symm
    rwa [hL, hR] at hlow
  -- Build Q0 = (1/N_Q) • Q_mat ∈ unitaryGroup (Fin 3) ℂ from Cert 3!
  have hNQ_pos : (0 : ℝ) < (Cert3.N_Q : ℝ) := by norm_num [Cert3.N_Q]
  let Q0_mat : Mat 3 := (((Cert3.N_Q : ℝ)⁻¹ : ℝ) : ℂ) • Cert3.Q_mat.toMat
  have hQ0_mem : Q0_mat ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h3 := congrArg Cert3.Mat3.toMat Cert3.cert3_Q_orthogonal
    rw [Cert3.Mat3.toMat_mul, Cert3.Mat3.toMat_trans, Cert3.Mat3.toMat_diag] at h3
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, h3]
    ext i j
    have hne : ((Cert3.N_Q : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hNQ_pos.ne'
    fin_cases i <;> fin_cases j <;> simp [Int.cast_mul, Complex.ofReal_intCast]
    all_goals field_simp [hne]
  let Q0 : Matrix.unitaryGroup (Fin 3) ℂ := ⟨Q0_mat, hQ0_mem⟩
  -- From Cert 4: D_diag - Q0ᴴ (UA + B) Q0 ⪰ 0!
  have hND_pos : (0 : ℝ) < (Cert3.N_D : ℝ) := by norm_num [Cert3.N_D]
  let dv_D : Fin 3 → ℝ := ![((Cert3.d1 : ℝ) / Cert3.N_D) ^ 2,
    ((Cert3.d2 : ℝ) / Cert3.N_D) ^ 2, ((Cert3.d3 : ℝ) / Cert3.N_D) ^ 2]
  let D_mat : Mat 3 := Matrix.diagonal (fun i => (dv_D i : ℂ))
  have hD_psd : D_mat.PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i
    change (0 : ℂ) ≤ ((dv_D i : ℝ) : ℂ)
    exact_mod_cast (by fin_cases i <;> exact sq_nonneg _ : 0 ≤ dv_D i)
  have hD_ge_Q0HQ0 : (D_mat - (Q0 : Mat 3)ᴴ * H * (Q0 : Mat 3)).PosSemidef := by
    have hcert4 := Cert3.Mat3.toMat_posSemidef_of_isSymPosDef _ Cert3.cert4_diagonal_upper_bound
    simp only [Cert3.Mat3.toMat_sub, Cert3.Mat3.toMat_diag, Cert3.Mat3.toMat_scale,
      Cert3.Mat3.toMat_mul, Cert3.Mat3.toMat_trans, Cert3.Mat3.toMat_add] at hcert4
    have hsc_pos : (0 : ℝ) < (Cert3.N_Q : ℝ) ^ 2 * (Cert3.N_A : ℝ) * (Cert3.N_D : ℝ) ^ 2 := by positivity
    have hdiff_D : D_mat - (Q0 : Mat 3)ᴴ * (UA + B) * (Q0 : Mat 3) =
        (((Cert3.N_Q : ℝ) ^ 2 * (Cert3.N_A : ℝ) * (Cert3.N_D : ℝ) ^ 2)⁻¹ : ℝ) •
          (Matrix.diagonal ![( (Cert3.N_Q * Cert3.N_Q * Cert3.N_A * Cert3.d1 * Cert3.d1 : ℤ) : ℂ),
              ((Cert3.N_Q * Cert3.N_Q * Cert3.N_A * Cert3.d2 * Cert3.d2 : ℤ) : ℂ),
              ((Cert3.N_Q * Cert3.N_Q * Cert3.N_A * Cert3.d3 * Cert3.d3 : ℤ) : ℂ)] -
            ((Cert3.N_D * Cert3.N_D : ℤ) : ℂ) •
              (Cert3.Q_mat.toMatᴴ * ((Cert3.UA_mat.toMat + (Cert3.N_A : ℂ) • B) * Cert3.Q_mat.toMat))) := by
      have hneQ : ((Cert3.N_Q : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hNQ_pos.ne'
      have hneA : ((Cert3.N_A : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hNA_pos.ne'
      have hneD : ((Cert3.N_D : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hND_pos.ne'
      have hQ0H : (Q0 : Mat 3)ᴴ * (UA + B) * (Q0 : Mat 3) =
          (((Cert3.N_Q : ℝ) ^ 2 * (Cert3.N_A : ℝ))⁻¹ : ℂ) •
            (Cert3.Q_mat.toMatᴴ * ((Cert3.UA_mat.toMat + (Cert3.N_A : ℂ) • B) * Cert3.Q_mat.toMat)) := by
        dsimp only [Q0, Q0_mat, UA]
        rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
        ext i j
        simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
          Fin.sum_univ_three, Complex.ofReal_inv, Complex.ofReal_intCast]
        field_simp [hneQ, hneA]; ring
      rw [hQ0H]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [D_mat, dv_D, Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, smul_eq_mul,
          Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_pow,
          Complex.ofReal_div, Complex.ofReal_intCast, Int.cast_mul, ↓reduceIte,
          Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq]
      all_goals (field_simp [hneQ, hneA, hneD]; try ring)
    have h1 : (D_mat - (Q0 : Mat 3)ᴴ * (UA + B) * (Q0 : Mat 3)).PosSemidef := by
      rw [hdiff_D]; exact hcert4.smul (inv_pos.mpr hsc_pos).le
    have h2 : ((Q0 : Mat 3)ᴴ * ((UA + B) - H) * (Q0 : Mat 3)).PosSemidef := by
      have hUAB_H : (UA + B) - H = UA - matAbs A := by dsimp [H]; rw [hB_abs]; abel
      rw [hUAB_H]
      simpa using hUA_ge_absA.conjTranspose_mul_mul_same (Q0 : Mat 3)
    have hsum : D_mat - (Q0 : Mat 3)ᴴ * H * (Q0 : Mat 3) =
        (D_mat - (Q0 : Mat 3)ᴴ * (UA + B) * (Q0 : Mat 3)) +
        (Q0 : Mat 3)ᴴ * ((UA + B) - H) * (Q0 : Mat 3) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [hsum]; exact h1.add h2
  have hH_psd : H.PosSemidef := (matAbs_posSemidef A).add (matAbs_posSemidef B)
  have hPowH_ub : schattenPow (3 / 2) H ≤
      ((Cert3.d1 : ℝ) ^ 3 + (Cert3.d2 : ℝ) ^ 3 + (Cert3.d3 : ℝ) ^ 3) / (Cert3.N_D : ℝ) ^ 3 := by
    have hQ0HQ0_psd : ((Q0 : Mat 3)ᴴ * H * (Q0 : Mat 3)).PosSemidef := by
      simpa using hH_psd.conjTranspose_mul_mul_same (Q0 : Mat 3)
    have hmono := schattenPow_mono_of_posSemidef hp1 hQ0HQ0_psd hD_psd hD_ge_Q0HQ0
    have hinv : schattenPow (3 / 2) ((Q0 : Mat 3)ᴴ * H * (Q0 : Mat 3)) = schattenPow (3 / 2) H := by
      have hstar : (Q0 : Mat 3)ᴴ = ((star Q0 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat 3) := rfl
      have hQ0_eq : (Q0 : Mat 3) = ((star Q0 : Matrix.unitaryGroup (Fin 3) ℂ) : Mat 3)ᴴ := by
        change (Q0 : Mat 3) = ((Q0 : Mat 3)ᴴ)ᴴ; rw [Matrix.conjTranspose_conjTranspose]
      rw [Matrix.mul_assoc, hstar, schattenPow_unitary_mul_left, hQ0_eq,
        schattenPow_unitary_mul_conjTranspose_right hp0.le]
    rw [hinv] at hmono
    have hD_pow : schattenPow (3 / 2) D_mat =
        ((Cert3.d1 : ℝ) ^ 3 + (Cert3.d2 : ℝ) ^ 3 + (Cert3.d3 : ℝ) ^ 3) / (Cert3.N_D : ℝ) ^ 3 := by
      have hdv_nn : ∀ i, 0 ≤ dv_D i := fun i => by fin_cases i <;> exact sq_nonneg _
      rw [schattenPow_diagonal hp0 dv_D hdv_nn, Fin.sum_univ_three]
      simp only [dv_D, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hd1_nn : 0 ≤ (Cert3.d1 : ℝ) / Cert3.N_D := by norm_num [Cert3.d1, Cert3.N_D]
      have hd2_nn : 0 ≤ (Cert3.d2 : ℝ) / Cert3.N_D := by norm_num [Cert3.d2, Cert3.N_D]
      have hd3_nn : 0 ≤ (Cert3.d3 : ℝ) / Cert3.N_D := by norm_num [Cert3.d3, Cert3.N_D]
      have hrp : ∀ x : ℝ, 0 ≤ x → (x ^ 2) ^ (3 / 2 : ℝ) = x ^ 3 := fun x hx => by
        rw [← Real.rpow_two, ← Real.rpow_mul hx]; norm_num
      rw [hrp _ hd1_nn, hrp _ hd2_nn, hrp _ hd3_nn, div_pow, div_pow, div_pow]
      ring
    rwa [hD_pow] at hmono
  -- Part 2: Exact 2×2 quadratic root lower bound on ‖S‖_{3/2}^{3/2} > (r1^3 + r2^3) / N_R^3!
  set S : Mat 3 := Cert3.S_mat.toMat
  have hNR_pos : (0 : ℝ) < (Cert3.N_R : ℝ) := by norm_num [Cert3.N_R]
  have hPowS_lb : ((Cert3.r1 : ℝ) ^ 3 + (Cert3.r2 : ℝ) ^ 3) / (Cert3.N_R : ℝ) ^ 3 <
      schattenPow (3 / 2) S := by
    -- Compute schattenPow (3/2) S = schattenPow (3/4) (S * Sᴴ) via explicit 2×2 diagonalization of S * Sᴴ!
    have hSST_eq : S * Sᴴ = Matrix.of ![![(20745 : ℂ), 2298, 0], ![2298, 317, 0], ![0, 0, 0]] := by
      have h1 := congrArg Cert3.Mat3.toMat Cert3.cert_SST_exact
      rw [Cert3.Mat3.toMat_mul, Cert3.Mat3.toMat_trans] at h1
      simpa [S, Cert3.Mat3.toMat] using h1
    have hPowS_SST : schattenPow (3 / 2) S = schattenPow (3 / 4) (S * Sᴴ) := by
      have h1 : schattenPow (3 / 2) S = schattenPow (3 / 2) Sᴴ := by
        obtain ⟨U, V, σ, hσ, hS_svd, _⟩ := exists_svd S
        have hSH : Sᴴ = (V : Mat 3) * Matrix.diagonal (fun i => (σ i : ℂ)) * (U : Mat 3)ᴴ := by
          rw [hS_svd, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
            Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc]
          congr 2; ext i j; by_cases hij : i = j
          · subst hij; simp [Complex.conj_ofReal]
          · simp [Matrix.diagonal, hij]
        rw [hSH, hS_svd, schattenPow_unitary_mul_conjTranspose_right hp0.le,
          schattenPow_unitary_mul_left, schattenPow_unitary_mul_conjTranspose_right hp0.le,
          schattenPow_unitary_mul_left]
      rw [h1, ← schattenPow_gram hp0 Sᴴ, Matrix.conjTranspose_conjTranspose]; norm_num
    -- Explicitly diagonalize the 2×2 upper-left block [[20745, 2298], [2298, 317]]!
    let Δ : ℝ := Real.sqrt (10531 ^ 2 - 1295361)
    have hΔ_pos : 0 < Δ := Real.sqrt_pos.mpr (by norm_num)
    have hΔ_sq : Δ ^ 2 = 10531 ^ 2 - 1295361 := Real.sq_sqrt (by norm_num)
    let μ1 : ℝ := 10531 + Δ
    let μ2 : ℝ := 10531 - Δ
    have hμ1_pos : 0 < μ1 := by dsimp [μ1]; linarith
    have hμ2_pos : 0 < μ2 := by dsimp [μ2]; nlinarith
    have hμ1_quad : μ1 ^ 2 - 21062 * μ1 + 1295361 = 0 := by dsimp [μ1]; nlinarith [hΔ_sq]
    have hμ2_quad : μ2 ^ 2 - 21062 * μ2 + 1295361 = 0 := by dsimp [μ2]; nlinarith [hΔ_sq]
    have hμ_sum : μ1 + μ2 = 21062 := by dsimp [μ1, μ2]; ring
    have hμ_prod : μ1 * μ2 = 1295361 := by dsimp [μ1, μ2]; nlinarith [hΔ_sq]
    -- Unit eigenvectors of [[20745, 2298], [2298, 317]]:
    -- v1 = (2298, μ1 - 20745) / n1, v2 = (-(μ1 - 20745), 2298) / n1!
    let α : ℝ := μ1 - 20745
    let n1 : ℝ := Real.sqrt (2298 ^ 2 + α ^ 2)
    have hn1_pos : 0 < n1 := Real.sqrt_pos.mpr (by positivity)
    have hn1_sq : n1 ^ 2 = 2298 ^ 2 + α ^ 2 := Real.sq_sqrt (by positivity)
    let c0 : ℝ := 2298 / n1
    let s0 : ℝ := α / n1
    have hcs_sq : c0 ^ 2 + s0 ^ 2 = 1 := by
      dsimp [c0, s0]; rw [div_pow, div_pow, ← add_div, ← hn1_sq, div_self (sq_pos_of_pos hn1_pos).ne']
    let U_mat : Mat 3 := Matrix.of ![![(c0 : ℂ), (-(s0 : ℂ)), 0], ![(s0 : ℂ), (c0 : ℂ), 0], ![0, 0, 1]]
    have hU_mem : U_mat ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [U_mat, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_three,
          Complex.conj_ofReal]
      · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq, hcs_sq,
          Complex.ofReal_one]
      · ring
      · ring
      · rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← sq, ← sq,
          add_comm (s0 ^ 2), hcs_sq, Complex.ofReal_one]
    let U : Matrix.unitaryGroup (Fin 3) ℂ := ⟨U_mat, hU_mem⟩
    have hdiag_SST : S * Sᴴ = (U : Mat 3) * Matrix.diagonal ![(μ1 : ℂ), (μ2 : ℂ), 0] * (U : Mat 3)ᴴ := by
      have hα_quad : α ^ 2 + 20428 * α - 2298 ^ 2 = 0 := by dsimp [α]; linarith [hμ1_quad]
      have h_00 : c0 ^ 2 * μ1 + s0 ^ 2 * μ2 = 20745 := by
        dsimp [c0, s0]
        rw [div_pow, div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
          div_eq_iff (sq_pos_of_pos hn1_pos).ne']
        rw [hn1_sq]; dsimp [α, μ1, μ2] at hα_quad ⊢; nlinarith [hΔ_sq]
      have h_01 : c0 * s0 * (μ1 - μ2) = 2298 := by
        dsimp [c0, s0]; rw [div_mul_div_comm, ← sq, div_mul_eq_mul_div,
          div_eq_iff (sq_pos_of_pos hn1_pos).ne', hn1_sq]
        dsimp [α, μ1, μ2] at hα_quad ⊢; nlinarith [hΔ_sq]
      have h_11 : s0 ^ 2 * μ1 + c0 ^ 2 * μ2 = 317 := by
        nlinarith [h_00, hcs_sq, hμ_sum]
      rw [hSST_eq]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [U, U_mat, Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply,
          Matrix.conjTranspose_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val, Complex.star_def, Complex.conj_ofReal,
          ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, map_neg,
          map_zero, map_one, mul_zero, zero_mul, add_zero, zero_add, mul_one]
      · have hR : ((c0 : ℂ) * (μ1 : ℂ) * (c0 : ℂ) + (-(s0 : ℂ)) * (μ2 : ℂ) * (-(s0 : ℂ))) =
            (((c0 ^ 2 * μ1 + s0 ^ 2 * μ2 : ℝ) : ℂ)) := by push_cast; ring
        rw [hR, h_00]; norm_num
      · have hR : ((c0 : ℂ) * (μ1 : ℂ) * (s0 : ℂ) + (-(s0 : ℂ)) * (μ2 : ℂ) * (c0 : ℂ)) =
            (((c0 * s0 * (μ1 - μ2) : ℝ) : ℂ)) := by push_cast; ring
        rw [hR, h_01]; norm_num
      · have hR : ((s0 : ℂ) * (μ1 : ℂ) * (c0 : ℂ) + (c0 : ℂ) * (μ2 : ℂ) * (-(s0 : ℂ))) =
            (((c0 * s0 * (μ1 - μ2) : ℝ) : ℂ)) := by push_cast; ring
        rw [hR, h_01]; norm_num
      · have hR : ((s0 : ℂ) * (μ1 : ℂ) * (s0 : ℂ) + (c0 : ℂ) * (μ2 : ℂ) * (c0 : ℂ)) =
            (((s0 ^ 2 * μ1 + c0 ^ 2 * μ2 : ℝ) : ℂ)) := by push_cast; ring
        rw [hR, h_11]; norm_num
    have hPowS_val : schattenPow (3 / 2) S = μ1 ^ (3 / 4 : ℝ) + μ2 ^ (3 / 4 : ℝ) := by
      rw [hPowS_SST, hdiag_SST, schattenPow_unitary_mul_conjTranspose_right (by norm_num),
        schattenPow_unitary_mul_left]
      have hd : ∀ i : Fin 3, 0 ≤ (![μ1, μ2, 0] i) := fun i => by
        fin_cases i <;> simp [hμ1_pos.le, hμ2_pos.le]
      have hdiag_eq : Matrix.diagonal ![(μ1 : ℂ), (μ2 : ℂ), 0] =
          Matrix.diagonal (fun i : Fin 3 => ((![μ1, μ2, 0] i : ℝ) : ℂ)) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      rw [hdiag_eq, schattenPow_diagonal (by norm_num) _ hd, Fin.sum_univ_three]
      simp [Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0)]
    -- Use Cert 5 to prove (r1/N_R)^4 < μ1 and (r2/N_R)^4 < μ2!
    obtain ⟨hc5_1, hc5_2, hc5_3⟩ := Cert3.cert5_numerator_root_bracketing
    let y1 : ℝ := ((Cert3.r1 : ℝ) / Cert3.N_R) ^ 4
    let y2 : ℝ := ((Cert3.r2 : ℝ) / Cert3.N_R) ^ 4
    have hy2_lt_mid : y2 < 10531 := by
      have h1 : ((Cert3.r2 : ℝ) ^ 4) < 10531 * ((Cert3.N_R : ℝ) ^ 4) := by exact_mod_cast hc5_1
      dsimp [y2]; rw [div_pow, div_lt_iff₀ (by positivity)]; exact h1
    have hy2_poly : 0 < y2 ^ 2 - 21062 * y2 + 1295361 := by
      have h1 : (0 : ℝ) < ((Cert3.r2 : ℝ) ^ 4) ^ 2 - 21062 * ((Cert3.r2 : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4) +
          1295361 * ((Cert3.N_R : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4) := by exact_mod_cast hc5_2
      dsimp [y2]; rw [div_pow]
      have hden : 0 < ((Cert3.N_R : ℝ) ^ 4) ^ 2 := by positivity
      have hrew : ((Cert3.r2 : ℝ) ^ 4 / (Cert3.N_R : ℝ) ^ 4) ^ 2 -
          21062 * ((Cert3.r2 : ℝ) ^ 4 / (Cert3.N_R : ℝ) ^ 4) + 1295361 =
          (((Cert3.r2 : ℝ) ^ 4) ^ 2 - 21062 * ((Cert3.r2 : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4) +
            1295361 * ((Cert3.N_R : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4)) / ((Cert3.N_R : ℝ) ^ 4) ^ 2 := by
        have hNRne : (Cert3.N_R : ℝ) ≠ 0 := hNR_pos.ne'
        generalize (Cert3.r2 : ℝ) = a
        generalize (Cert3.N_R : ℝ) = b at hNRne ⊢
        field_simp [hNRne]
      rw [hrew]; exact div_pos h1 hden
    have hy1_poly : y1 ^ 2 - 21062 * y1 + 1295361 < 0 := by
      have h1 : ((Cert3.r1 : ℝ) ^ 4) ^ 2 - 21062 * ((Cert3.r1 : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4) +
          1295361 * ((Cert3.N_R : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4) < 0 := by exact_mod_cast hc5_3
      dsimp [y1]; rw [div_pow]
      have hden : 0 < ((Cert3.N_R : ℝ) ^ 4) ^ 2 := by positivity
      have hrew : ((Cert3.r1 : ℝ) ^ 4 / (Cert3.N_R : ℝ) ^ 4) ^ 2 -
          21062 * ((Cert3.r1 : ℝ) ^ 4 / (Cert3.N_R : ℝ) ^ 4) + 1295361 =
          (((Cert3.r1 : ℝ) ^ 4) ^ 2 - 21062 * ((Cert3.r1 : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4) +
            1295361 * ((Cert3.N_R : ℝ) ^ 4) * ((Cert3.N_R : ℝ) ^ 4)) / ((Cert3.N_R : ℝ) ^ 4) ^ 2 := by
        have hNRne : (Cert3.N_R : ℝ) ≠ 0 := hNR_pos.ne'
        generalize (Cert3.r1 : ℝ) = a
        generalize (Cert3.N_R : ℝ) = b at hNRne ⊢
        field_simp [hNRne]
      rw [hrew]; exact div_neg_of_neg_of_pos h1 hden
    have hy1_lt_μ1 : y1 < μ1 := by
      have : (y1 - μ1) * (y1 - μ2) < 0 := by
        have hfac : (y1 - μ1) * (y1 - μ2) = y1 ^ 2 - 21062 * y1 + 1295361 := by
          nlinarith [hμ_sum, hμ_prod]
        linarith
      nlinarith [hΔ_pos]
    have hy2_lt_μ2 : y2 < μ2 := by
      have : (y2 - μ1) * (y2 - μ2) > 0 := by
        have hfac : (y2 - μ1) * (y2 - μ2) = y2 ^ 2 - 21062 * y2 + 1295361 := by
          nlinarith [hμ_sum, hμ_prod]
        linarith
      have h2lt1 : y2 < μ1 := by dsimp [μ1]; linarith
      nlinarith
    have hr1_nn : 0 ≤ (Cert3.r1 : ℝ) / Cert3.N_R := by norm_num [Cert3.r1, Cert3.N_R]
    have hr2_nn : 0 ≤ (Cert3.r2 : ℝ) / Cert3.N_R := by norm_num [Cert3.r2, Cert3.N_R]
    have hlt1 : ((Cert3.r1 : ℝ) / Cert3.N_R) ^ 3 < μ1 ^ (3 / 4 : ℝ) := by
      have := Real.rpow_lt_rpow (by positivity) hy1_lt_μ1 (by norm_num : (0 : ℝ) < 3 / 4)
      have heq : y1 ^ (3 / 4 : ℝ) = ((Cert3.r1 : ℝ) / Cert3.N_R) ^ 3 := by
        dsimp [y1]; rw [show ((Cert3.r1 : ℝ) / Cert3.N_R) ^ 4 = ((Cert3.r1 : ℝ) / Cert3.N_R) ^ (4 : ℝ) by norm_num,
          ← Real.rpow_mul hr1_nn]; norm_num
      rwa [heq] at this
    have hlt2 : ((Cert3.r2 : ℝ) / Cert3.N_R) ^ 3 < μ2 ^ (3 / 4 : ℝ) := by
      have := Real.rpow_lt_rpow (by positivity) hy2_lt_μ2 (by norm_num : (0 : ℝ) < 3 / 4)
      have heq : y2 ^ (3 / 4 : ℝ) = ((Cert3.r2 : ℝ) / Cert3.N_R) ^ 3 := by
        dsimp [y2]; rw [show ((Cert3.r2 : ℝ) / Cert3.N_R) ^ 4 = ((Cert3.r2 : ℝ) / Cert3.N_R) ^ (4 : ℝ) by norm_num,
          ← Real.rpow_mul hr2_nn]; norm_num
      rwa [heq] at this
    rw [hPowS_val, add_div, ← div_pow, ← div_pow]; linarith
  -- Part 3: Combine with Cert 6 to conclude leeConst (3/2) 2 2 < leeRatio (3/2) ![A, B]!
  have hH_ne : H ≠ 0 := by
    intro h0
    have hB0 : (star ![1, 0, 0] ⬝ᵥ H.mulVec ![1, 0, 0]).re = 0 := by
      rw [h0, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
    have hA_nn : 0 ≤ (star ![1, 0, 0] ⬝ᵥ (matAbs A).mulVec ![1, 0, 0]).re := by
      simpa [RCLike.re_to_complex] using (matAbs_posSemidef A).re_dotProduct_nonneg _
    have hB_val : (star ![1, 0, 0] ⬝ᵥ (matAbs B).mulVec ![1, 0, 0]).re = 81 := by
      rw [hB_abs]; simp [B, Cert3.B_mat, Cert3.Mat3.toMat, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    have hsplit : (star ![1, 0, 0] ⬝ᵥ H.mulVec ![1, 0, 0]).re =
        (star ![1, 0, 0] ⬝ᵥ (matAbs A).mulVec ![1, 0, 0]).re +
        (star ![1, 0, 0] ⬝ᵥ (matAbs B).mulVec ![1, 0, 0]).re := by
      simp [H, Matrix.add_mulVec, dotProduct_add]
    linarith
  refine ⟨hSumH ▸ hH_ne, ?_⟩
  rw [theorem3_exact_p32 le_rfl]
  let P : ℝ := (Cert3.r1 : ℝ) ^ 3 + (Cert3.r2 : ℝ) ^ 3
  let Q : ℝ := (Cert3.d1 : ℝ) ^ 3 + (Cert3.d2 : ℝ) ^ 3 + (Cert3.d3 : ℝ) ^ 3
  have hP_pos : 0 < P := by norm_num [P, Cert3.r1, Cert3.r2]
  have hQ_pos : 0 < Q := by norm_num [Q, Cert3.d1, Cert3.d2, Cert3.d3]
  have hND_eq_NR : (Cert3.N_D : ℝ) = (Cert3.N_R : ℝ) := by norm_num [Cert3.N_D, Cert3.N_R]
  have hH_pow_pos : 0 < schattenPow (3 / 2) H := by
    rw [← schattenNorm_rpow hp0 H]; exact Real.rpow_pos_of_pos (schattenNorm_pos_of_ne_zero hp0 hH_ne) _
  have hPQ_lt : P / Q < schattenPow (3 / 2) S / schattenPow (3 / 2) H := by
    have h1 : P / (Cert3.N_R : ℝ) ^ 3 < schattenPow (3 / 2) S := hPowS_lb
    have h2 : schattenPow (3 / 2) H ≤ Q / (Cert3.N_R : ℝ) ^ 3 := by rwa [← hND_eq_NR]
    rw [div_lt_div_iff₀ hQ_pos hH_pow_pos]
    have hNR3 : 0 < (Cert3.N_R : ℝ) ^ 3 := by positivity
    have h1' : P < schattenPow (3 / 2) S * (Cert3.N_R : ℝ) ^ 3 := (div_lt_iff₀ hNR3).mp h1
    have h2' : schattenPow (3 / 2) H * (Cert3.N_R : ℝ) ^ 3 ≤ Q := (le_div_iff₀ hNR3).mp h2
    have hmul : P * (schattenPow (3 / 2) H * (Cert3.N_R : ℝ) ^ 3) <
        (schattenPow (3 / 2) S * (Cert3.N_R : ℝ) ^ 3) * Q := by
      calc P * (schattenPow (3 / 2) H * (Cert3.N_R : ℝ) ^ 3)
          ≤ P * Q := mul_le_mul_of_nonneg_left h2' hP_pos.le
        _ < (schattenPow (3 / 2) S * (Cert3.N_R : ℝ) ^ 3) * Q := mul_lt_mul_of_pos_right h1' hQ_pos
    have hmul' : (P * schattenPow (3 / 2) H) * (Cert3.N_R : ℝ) ^ 3 <
        (schattenPow (3 / 2) S * Q) * (Cert3.N_R : ℝ) ^ 3 := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hmul
    exact lt_of_mul_lt_mul_right hmul' hNR3.le
  obtain ⟨hgap_pos, hgap_sq⟩ := Cert3.cert6_beats_2x2_ceiling
  have hgap_core : ∀ (pV qV : ℝ), 0 < qV → 0 < 256 * pV ^ 4 - 107 * qV ^ 4 →
      (256 * pV ^ 4 - 107 * qV ^ 4) * (256 * pV ^ 4 - 107 * qV ^ 4) > 51 * 51 * 17 * qV ^ 8 →
      (107 + 51 * Real.sqrt 17) / 256 < (pV / qV) ^ 4 := by
    intro pV qV hqv hgp hgsq
    rw [div_pow, div_lt_div_iff₀ (by norm_num) (by positivity)]
    have hs17 : (Real.sqrt 17) ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have h51 : (51 * Real.sqrt 17 * qV ^ 4) ^ 2 = 51 * 51 * 17 * qV ^ 8 := by
      have : (51 * Real.sqrt 17 * qV ^ 4) ^ 2 = 51 * 51 * (Real.sqrt 17) ^ 2 * qV ^ 8 := by ring
      rw [this, hs17]
    have hy_nn : 0 ≤ 51 * Real.sqrt 17 * qV ^ 4 := by positivity
    have hsq_lt : (51 * Real.sqrt 17 * qV ^ 4) ^ 2 < (256 * pV ^ 4 - 107 * qV ^ 4) ^ 2 := by
      rw [h51, sq]; exact hgsq
    have hxy : 51 * Real.sqrt 17 * qV ^ 4 < 256 * pV ^ 4 - 107 * qV ^ 4 := by
      nlinarith only [hgp, hy_nn, hsq_lt]
    linarith only [hxy]
  have hgap_pos_R : 0 < 256 * P ^ 4 - 107 * Q ^ 4 := by
    dsimp only [P, Q]; exact_mod_cast hgap_pos
  have hgap_sq_R : (256 * P ^ 4 - 107 * Q ^ 4) * (256 * P ^ 4 - 107 * Q ^ 4) > 51 * 51 * 17 * Q ^ 8 := by
    dsimp only [P, Q]; exact_mod_cast hgap_sq
  have hC2_lt_PQ4 : (107 + 51 * Real.sqrt 17) / 256 < (P / Q) ^ 4 :=
    hgap_core P Q hQ_pos hgap_pos_R hgap_sq_R
  -- Now relate leeRatio (3/2) ![A, B] = (schattenPow (3/2) S / schattenPow (3/2) H)^(2/3)!
  have hrat_eq : leeRatio (3 / 2) ![A, B] = (schattenPow (3 / 2) S / schattenPow (3 / 2) H) ^ (2 / 3 : ℝ) := by
    unfold leeRatio schattenNorm
    rw [hSumS, hSumH, Real.div_rpow (schattenPow_nonneg (3 / 2) S) hH_pow_pos.le]
    norm_num
  rw [hrat_eq]
  have hlt_pow : ((107 + 51 * Real.sqrt 17) / 256) ^ (1 / 6 : ℝ) < ((P / Q) ^ 4) ^ (1 / 6 : ℝ) :=
    Real.rpow_lt_rpow (by positivity) hC2_lt_PQ4 (by norm_num)
  have hPQ_eq : ((P / Q) ^ 4) ^ (1 / 6 : ℝ) = (P / Q) ^ (2 / 3 : ℝ) := by
    rw [show (P / Q) ^ 4 = (P / Q) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by positivity)]
    norm_num
  have hlt2 : (P / Q) ^ (2 / 3 : ℝ) < (schattenPow (3 / 2) S / schattenPow (3 / 2) H) ^ (2 / 3 : ℝ) :=
    Real.rpow_lt_rpow (by positivity) hPQ_lt (by norm_num)
  linarith

end MI20
