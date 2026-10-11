import OAI.Analysis.DirectCrouzeix.PolynomialCalculus

namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_eq_sum_norm_sq {ι : Type u_8} {κ : Type u_9} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [hsSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

def hsVector {ι : Type u_10} {κ : Type u_11} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) :
    EuclideanSpace ℂ (ι × κ) := WithLp.toLp 2 (fun p => M p.1 p.2)

theorem hsSq_eq_norm_hsVector_sq {ι : Type u_12} {κ : Type u_13} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq M = ‖hsVector M‖ ^ 2 := by
  simp [hsSq_eq_sum_norm_sq, EuclideanSpace.norm_sq_eq, hsVector, Fintype.sum_prod_type]

theorem hsSq_conjTranspose {ι : Type u_14} {κ : Type u_15} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

theorem hsSq_smul {ι : Type u_16} {κ : Type u_17} [Fintype ι] [Fintype κ]
    (c : ℂ) (M : Matrix ι κ ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq_eq_sum_norm_sq, Matrix.smul_apply, smul_eq_mul, norm_mul,
    mul_pow, Finset.mul_sum]

def entryPair {ι : Type u_18} {κ : Type u_19} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ℂ := ∑ i, ∑ j, M i j * C i j

theorem entryPair_conj {ι : Type u_20} {κ : Type u_21} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : entryPair M (M.map star) = (hsSq M : ℂ) := by
  simp only [entryPair, Matrix.map_apply, hsSq_eq_sum_norm_sq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.normSq_eq_norm_sq]
  exact Complex.mul_conj _

theorem hsSq_map_star {ι : Type u_22} {κ : Type u_23} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℂ) : hsSq (M.map star) = hsSq M := by
  simp [hsSq_eq_sum_norm_sq]

theorem hsSq_mul_le {ι : Type u_24} {κ : Type u_25} {τ : Type u_26} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ ‖F‖ ^ 2 * hsSq G := by
  have col (M : Matrix ι τ ℂ) :
      hsSq M = ∑ j, ‖(WithLp.toLp 2 (fun i => M i j) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    exact Finset.sum_comm
  have colG : hsSq G = ∑ j,
      ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    exact Finset.sum_comm
  rw [col, colG, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := Matrix.l2_opNorm_mulVec F (WithLp.toLp 2 (fun i => G i j))
  have h' : ‖(WithLp.toLp 2 (fun i => (F * G) i j) : EuclideanSpace ℂ ι)‖ ≤
      ‖F‖ * ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖ := h
  calc
    _ ≤ (‖F‖ * ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = _ := mul_pow _ _ _

theorem hsSq_mul_le_right {ι : Type u_27} {κ : Type u_28} {τ : Type u_29} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq τ] [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ hsSq F * ‖G‖ ^ 2 := by
  simpa only [← Matrix.conjTranspose_mul, hsSq_conjTranspose,
    Matrix.l2_opNorm_conjTranspose, mul_comm] using hsSq_mul_le Gᴴ Fᴴ

theorem entryPair_eq_inner {ι : Type u_30} {κ : Type u_31} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) :
    entryPair M C = inner ℂ (hsVector (M.map star)) (hsVector C) := by
  simp [entryPair, hsVector, PiLp.inner_apply, Fintype.sum_prod_type, mul_comm]

theorem norm_entryPair_sq_le {ι : Type u_32} {κ : Type u_33} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) : ‖entryPair M C‖ ^ 2 ≤ hsSq M * hsSq C := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (hsVector (M.map star)) (hsVector C)
  have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← entryPair_eq_inner, mul_pow, ← hsSq_eq_norm_hsVector_sq,
    ← hsSq_eq_norm_hsVector_sq, hsSq_map_star] at h'
  exact h'

theorem norm_sum_entryPair_sq_le {ρ : Type u_34} {ι : Type u_35} {κ : Type u_36} [Fintype ρ]
    [Fintype ι] [Fintype κ]
    (M C : ρ → Matrix ι κ ℂ) :
    ‖∑ k, entryPair (M k) (C k)‖ ^ 2 ≤ (∑ k, hsSq (M k)) * ∑ k, hsSq (C k) := by
  have h := norm_entryPair_sq_le
    (fun (p : ρ × ι) (j : κ) => M p.1 p.2 j)
    (fun (p : ρ × ι) (j : κ) => C p.1 p.2 j)
  rw [hsSq_eq_sum_norm_sq (fun (p : ρ × ι) (j : κ) => M p.1 p.2 j),
    hsSq_eq_sum_norm_sq (fun (p : ρ × ι) (j : κ) => C p.1 p.2 j)] at h
  simpa only [entryPair, hsSq_eq_sum_norm_sq, Fintype.sum_prod_type] using h

end DirectCrouzeix

end

end OAI
