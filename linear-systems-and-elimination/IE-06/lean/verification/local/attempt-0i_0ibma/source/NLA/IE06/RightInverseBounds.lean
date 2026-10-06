/-
Deterministic right-inverse bounds for the Gaussian append argument. Exact
contracts and constants were approved in reviews/gaussian-append-specification.md.
-/
import NLA.IE06.KyFan

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator
namespace NLA.IE06.RightInverseBounds
open Spectral KyFan

/-- A Hermitian idempotent is a Euclidean contraction, also in dimension zero. -/
theorem opNorm_projection_le_one {d : Type*} [Fintype d] [DecidableEq d]
    (P : Matrix d d ℝ) (hs : Pᴴ = P) (hi : P*P=P) : opNorm P ≤ 1 := by
  have he : opNorm P ^ 2 = opNorm P := by
    simp only [opNorm_eq_l2, pow_two]
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hs, hi]
  have hn := opNorm_nonneg P
  nlinarith

theorem gram_posDef_of_rightInverse {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (J : Matrix (Fin n) (Fin m) ℝ) (hJ : A*J=1) : (A*Aᴴ).PosDef := by
  apply gram_posDef_of_surjective
  intro y
  refine ⟨euclideanMap J y, ?_⟩
  have h := congrArg Matrix.toEuclideanLin hJ
  simp only [Matrix.toLpLin_mul_same, Matrix.toLpLin_one] at h
  exact congrArg (fun f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) => f y) h

theorem pinv_projection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : (A*Aᴴ).PosDef) :
    (pinv A*A)ᴴ = pinv A*A ∧ (pinv A*A)*(pinv A*A)=pinv A*A := by
  constructor
  · have hh := (Matrix.isHermitian_mul_conjTranspose_self A).inv.eq
    rw [pinv_eq_gram_inverse_of_posDef A hA]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh,
      Matrix.mul_assoc]
  · calc
      _ = pinv A*(A*pinv A)*A := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [mul_pinv_eq_one A hA.isUnit, Matrix.mul_one]

theorem pinv_norms_le_rightInverse {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (J : Matrix (Fin n) (Fin m) ℝ) (hJ : A*J=1) :
    opNorm (pinv A) ≤ opNorm J ∧ frobeniusNorm (pinv A) ≤ frobeniusNorm J := by
  have hA := gram_posDef_of_rightInverse A J hJ
  obtain ⟨hs,hi⟩ := pinv_projection A hA
  have hp := opNorm_projection_le_one (pinv A*A) hs hi
  have he : pinv A = (pinv A*A)*J := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  constructor
  · rw [he]
    exact (Matrix.l2_opNorm_mul _ _).trans
      ((mul_le_mul_of_nonneg_right hp (opNorm_nonneg J)).trans_eq (one_mul _))
  · rw [he]
    exact (frobeniusNorm_mul_left _ _).trans
      ((mul_le_mul_of_nonneg_right hp (frobeniusNorm_nonneg J)).trans_eq (one_mul _))

/-- Horizontal concatenation with canonical Fin coordinates. -/
def append {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) : Matrix (Fin m) (Fin (n+p)) ℝ :=
  fun i => Fin.addCases (A i) (B i)

/-- Vertical concatenation in the same canonical coordinates. -/
def stack {m n p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin (m+n)) (Fin p) ℝ :=
  Fin.addCases A B

theorem append_mul_stack {m n p q : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin m) (Fin p) ℝ) (C : Matrix (Fin n) (Fin q) ℝ)
    (D : Matrix (Fin p) (Fin q) ℝ) : append A B * stack C D = A*C+B*D := by
  ext i j
  simp [Matrix.mul_apply, append, stack, Fin.sum_univ_add]

theorem stack_gram {m n p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : (stack A B)ᴴ*stack A B=Aᴴ*A+Bᴴ*B := by
  ext i j
  simp [Matrix.mul_apply, stack, Fin.sum_univ_add]

theorem opNorm_stack_sq_le {m n p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) :
    opNorm (stack A B)^2 ≤ opNorm A^2+opNorm B^2 := by
  simp only [opNorm_eq_l2, pow_two]
  rw [← Matrix.l2_opNorm_conjTranspose_mul_self, stack_gram,
    ← Matrix.l2_opNorm_conjTranspose_mul_self A,
    ← Matrix.l2_opNorm_conjTranspose_mul_self B]
  exact norm_add_le _ _

theorem frobeniusNorm_stack_sq {m n p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) :
    frobeniusNorm (stack A B)^2 = frobeniusNorm A^2+frobeniusNorm B^2 := by
  simp [frobeniusNorm_sq, stack, Fin.sum_univ_add]

theorem opNorm_orthonormal_columns_le_one {n k : ℕ} (U : Matrix (Fin n) (Fin k) ℝ)
    (hU : Uᴴ*U=1) : opNorm U ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖euclideanMap U x‖ ≤ 1*‖x‖
  rw [SpectralStacking.norm_map_of_orthonormal_columns U hU, one_mul]

theorem frobeniusNorm_le_sqrt_columns_opNorm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusNorm A ≤ Real.sqrt n * opNorm A := by
  simpa only [frobeniusNorm_conjTranspose, opNorm_conjTranspose] using
    frobeniusNorm_le_sqrt_rows_opNorm Aᴴ

/-- The cross term vanishes because the retained inverse kills the discarded
left singular subspace. This exact identity avoids a factor two in its trace. -/
theorem frobeniusNorm_sub_mul_sq {m n k : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin m) (Fin k) ℝ)
    (hRU : R*U=0) :
    frobeniusNorm (R-H*Uᴴ)^2 = frobeniusNorm R^2+frobeniusNorm (H*Uᴴ)^2 := by
  have hc (i : Fin m) : ∑ j, R i j * (H*Uᴴ) i j = 0 := by
    calc
      _ = ∑ l, H i l * (R*U) i l := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by simp [hRU]
  simp only [frobeniusNorm_sq, Matrix.sub_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : ∑ j, (R i j-(H*Uᴴ) i j)^2 =
      (∑ j, (R i j)^2) + (∑ j, ((H*Uᴴ) i j)^2) - 2*∑ j, R i j*(H*Uᴴ) i j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, hc, mul_zero, sub_zero]

/-- A concrete right inverse of the appended matrix. -/
def appendRightInverse {n k p : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (P : Matrix (Fin p) (Fin k) ℝ) : Matrix (Fin (n+p)) (Fin n) ℝ :=
  stack (R-R*G*P*Uᴴ) (P*Uᴴ)

theorem append_mul_rightInverse {n k p : ℕ} (M R : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (P : Matrix (Fin p) (Fin k) ℝ) (hMR : M*R=1-U*Uᴴ) (hXP : (Uᴴ*G)*P=1) :
    append M G * appendRightInverse R U G P = 1 := by
  rw [appendRightInverse, append_mul_stack]
  calc
    _ = M*R-(M*R)*G*P*Uᴴ+G*P*Uᴴ := by simp only [Matrix.mul_sub, Matrix.mul_assoc]
    _ = (1-U*Uᴴ)-(1-U*Uᴴ)*G*P*Uᴴ+G*P*Uᴴ := by rw [hMR]
    _ = 1-U*Uᴴ+U*((Uᴴ*G)*P)*Uᴴ := by
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    _ = 1 := by rw [hXP]; simp

theorem appendRightInverse_bounds {n k p : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin k) ℝ) (G : Matrix (Fin n) (Fin p) ℝ)
    (P : Matrix (Fin p) (Fin k) ℝ) (hU : Uᴴ*U=1) (hRU : R*U=0) :
    opNorm (appendRightInverse R U G P)^2 ≤
      2*opNorm R^2+4*(1+opNorm (R*G)^2)*opNorm P^2 ∧
    frobeniusNorm (appendRightInverse R U G P)^2 ≤
      frobeniusNorm R^2+(k:ℝ)*(1+opNorm (R*G)^2)*opNorm P^2 := by
  have hUt : opNorm Uᴴ ≤ 1 := by
    rw [opNorm_conjTranspose]
    exact opNorm_orthonormal_columns_le_one U hU
  have hmul (a b c : ℕ) (A : Matrix (Fin a) (Fin b) ℝ)
      (B : Matrix (Fin b) (Fin c) ℝ) : opNorm (A*B) ≤ opNorm A*opNorm B :=
    Matrix.l2_opNorm_mul A B
  have hPU : opNorm (P*Uᴴ) ≤ opNorm P := by
    exact (hmul _ _ _ P Uᴴ).trans
      ((mul_le_mul_of_nonneg_left hUt (opNorm_nonneg P)).trans_eq (mul_one _))
  have hH : opNorm (R*G*P*Uᴴ) ≤ opNorm (R*G)*opNorm P := by
    calc
      _ ≤ opNorm (R*G*P)*opNorm Uᴴ := hmul _ _ _ _ _
      _ ≤ opNorm (R*G*P) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hUt (opNorm_nonneg (R*G*P))
      _ ≤ _ := hmul _ _ _ _ _
  have hV : opNorm (R-R*G*P*Uᴴ) ≤ opNorm R+opNorm (R*G)*opNorm P := by
    have ht : opNorm (R-R*G*P*Uᴴ) ≤ opNorm R+opNorm (R*G*P*Uᴴ) :=
      norm_sub_le R (R*G*P*Uᴴ)
    exact ht.trans (add_le_add le_rfl hH)
  have hFP : frobeniusNorm P ≤ Real.sqrt k*opNorm P :=
    frobeniusNorm_le_sqrt_columns_opNorm P
  have hFW : frobeniusNorm (P*Uᴴ) ≤ Real.sqrt k*opNorm P := by
    calc
      _ ≤ frobeniusNorm P*opNorm Uᴴ := frobeniusNorm_mul_right P Uᴴ
      _ ≤ frobeniusNorm P := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hUt (frobeniusNorm_nonneg P)
      _ ≤ _ := hFP
  have hFH : frobeniusNorm (R*G*P*Uᴴ) ≤ Real.sqrt k*opNorm (R*G)*opNorm P := by
    calc
      _ ≤ frobeniusNorm (R*G*P)*opNorm Uᴴ := frobeniusNorm_mul_right _ _
      _ ≤ frobeniusNorm (R*G*P) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hUt (frobeniusNorm_nonneg (R*G*P))
      _ ≤ opNorm (R*G)*frobeniusNorm P := frobeniusNorm_mul_left _ _
      _ ≤ opNorm (R*G)*(Real.sqrt k*opNorm P) :=
        mul_le_mul_of_nonneg_left hFP (opNorm_nonneg _)
      _ = _ := by ring
  constructor
  · have h1 := opNorm_stack_sq_le (R-R*G*P*Uᴴ) (P*Uᴴ)
    have h2 := pow_le_pow_left₀ (opNorm_nonneg _) hV 2
    have h3 := pow_le_pow_left₀ (opNorm_nonneg _) hPU 2
    dsimp only [appendRightInverse]
    nlinarith only [h1, h2, h3, sq_nonneg (opNorm R-opNorm (R*G)*opNorm P),
      sq_nonneg (opNorm P), sq_nonneg (opNorm (R*G)*opNorm P)]
  · rw [appendRightInverse, frobeniusNorm_stack_sq,
      frobeniusNorm_sub_mul_sq R U (R*G*P) hRU]
    have h1 := pow_le_pow_left₀ (frobeniusNorm_nonneg _) hFW 2
    have h2 := pow_le_pow_left₀ (frobeniusNorm_nonneg _) hFH 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)] at h1
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)] at h2
    nlinarith only [h1,h2]

#assert_trust kernel opNorm_projection_le_one
#print axioms opNorm_projection_le_one
#assert_trust kernel gram_posDef_of_rightInverse
#print axioms gram_posDef_of_rightInverse
#assert_trust kernel pinv_projection
#print axioms pinv_projection
#assert_trust kernel pinv_norms_le_rightInverse
#print axioms pinv_norms_le_rightInverse
#assert_trust kernel append
#print axioms append
#assert_trust kernel stack
#print axioms stack
#assert_trust kernel append_mul_stack
#print axioms append_mul_stack
#assert_trust kernel stack_gram
#print axioms stack_gram
#assert_trust kernel opNorm_stack_sq_le
#print axioms opNorm_stack_sq_le
#assert_trust kernel frobeniusNorm_stack_sq
#print axioms frobeniusNorm_stack_sq
#assert_trust kernel opNorm_orthonormal_columns_le_one
#print axioms opNorm_orthonormal_columns_le_one
#assert_trust kernel frobeniusNorm_le_sqrt_columns_opNorm
#print axioms frobeniusNorm_le_sqrt_columns_opNorm
#assert_trust kernel frobeniusNorm_sub_mul_sq
#print axioms frobeniusNorm_sub_mul_sq
#assert_trust kernel appendRightInverse
#print axioms appendRightInverse
#assert_trust kernel append_mul_rightInverse
#print axioms append_mul_rightInverse
#assert_trust kernel appendRightInverse_bounds
#print axioms appendRightInverse_bounds
end NLA.IE06.RightInverseBounds
