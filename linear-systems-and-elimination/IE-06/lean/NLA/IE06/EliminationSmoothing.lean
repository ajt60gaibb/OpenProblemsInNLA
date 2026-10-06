import NLA.IE06.EliminationBlock
import NLA.IE06.KyFan
import NLA.IE06.SpectralStacking

/-! Exact cancellation of discarded inverse directions. The mathematical
contract was independently approved before implementation; see
reviews/elimination-smoothing-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix WithLp
open scoped BigOperators Matrix.Norms.L2Operator
namespace NLA.IE06.EliminationSmoothing
open Spectral KyFan

def rowNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : ℝ :=
  ‖(toLp 2 (A i) : EuclideanSpace ℝ (Fin n))‖

theorem rowNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    0 ≤ rowNorm A i := norm_nonneg _

theorem rowNorm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    rowNorm A i ^ 2 = ∑ j, (A i j)^2 := EuclideanSpace.real_norm_sq_eq _

theorem rowNorm_sub_le {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    rowNorm (A-B) i ≤ rowNorm A i + rowNorm B i := by
  change ‖(toLp 2 (A i) : EuclideanSpace ℝ (Fin n)) - toLp 2 (B i)‖ ≤ _
  exact norm_sub_le _ _

theorem rowNorm_mul_le {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) (i : Fin m) :
    rowNorm (A*B) i ≤ rowNorm A i * opNorm B := by
  have h := (euclideanMap Bᴴ).toContinuousLinearMap.le_opNorm
    (toLp 2 (A i))
  have he : euclideanMap Bᴴ (toLp 2 (A i)) =
      (toLp 2 ((A*B) i) : EuclideanSpace ℝ (Fin p)) := by
    ext j
    simp [euclideanMap, Matrix.toLpLin_apply, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, mul_comm]
  change ‖euclideanMap Bᴴ (toLp 2 (A i))‖ ≤ opNorm Bᴴ * rowNorm A i at h
  rw [he, opNorm_conjTranspose, mul_comm] at h
  exact h

theorem rowNorm_left_mul_le {n p : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin p) ℝ) (i : Fin n) {B : ℝ}
    (hA : ∀ j, rowNorm A j ≤ B) :
    rowNorm (J*A) i ≤ rowL1 J i * B := by
  have he : (toLp 2 ((J*A) i) : EuclideanSpace ℝ (Fin p)) =
      ∑ j : Fin n, J i j • (toLp 2 (A j) : EuclideanSpace ℝ (Fin p)) := by
    ext k
    simp [Matrix.mul_apply]
  rw [rowNorm, he]
  calc
    _ ≤ ∑ j : Fin n, ‖J i j • (toLp 2 (A j) : EuclideanSpace ℝ (Fin p))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin n, |J i j| * B := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_smul, Real.norm_eq_abs, rowNorm] using
        mul_le_mul_of_nonneg_left (hA j) (abs_nonneg (J i j))
    _ = rowL1 J i * B := (Finset.sum_mul _ _ _).symm

theorem opNorm_le_one_of_isometry {n r : ℕ} (Q : Matrix (Fin n) (Fin r) ℝ)
    (hQ : Qᴴ * Q = 1) : opNorm Q ≤ 1 := by
  apply (euclideanMap Q).toContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  exact (SpectralStacking.norm_map_of_orthonormal_columns Q hQ x).le

/-- Cancellation uses an arbitrary actual right inverse, so the algebra does
not rely on a totalized division convention. -/
theorem cancellation {n r s : ℕ} (E X : Matrix (Fin n) (Fin n) ℝ)
    (Y Q : Matrix (Fin n) (Fin r) ℝ) (G : Matrix (Fin n) (Fin s) ℝ)
    (P : Matrix (Fin s) (Fin r) ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (hE : E = X + Y * Qᴴ) (hP : (Qᴴ * G) * P = 1)
    (hzero : (J * E) * G = 0) :
    J * E = J * (X - (X * G * P) * Qᴴ) := by
  have hz := congrArg (fun B : Matrix (Fin n) (Fin s) ℝ => B * P) hzero
  rw [hE, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.zero_mul] at hz
  have hYP : (J * (Y * Qᴴ) * G) * P = J * Y := by
    calc
      _ = (J * Y) * ((Qᴴ * G) * P) := by simp only [Matrix.mul_assoc]
      _ = J * Y := by rw [hP, Matrix.mul_one]
  rw [hYP] at hz
  have hY : J * Y = -(J * X * G * P) := (eq_neg_iff_add_eq_zero).mpr (by rw [add_comm]; exact hz)
  calc
    J * E = J * X + (J * Y) * Qᴴ := by rw [hE, Matrix.mul_add, ← Matrix.mul_assoc]
    _ = J * X - (J * X * G * P) * Qᴴ := by rw [hY, Matrix.neg_mul]; rfl
    _ = J * (X - (X * G * P) * Qᴴ) := by
      rw [Matrix.mul_sub]
      simp only [Matrix.mul_assoc]

/-- The discarded directions contribute no uncontrolled norm of Y. -/
theorem cancellation_row_bound {n r s : ℕ} (E X : Matrix (Fin n) (Fin n) ℝ)
    (Y Q : Matrix (Fin n) (Fin r) ℝ) (G : Matrix (Fin n) (Fin s) ℝ)
    (P : Matrix (Fin s) (Fin r) ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (hE : E = X + Y * Qᴴ) (hQ : Qᴴ * Q = 1) (hP : (Qᴴ * G) * P = 1)
    (hzero : (J * E) * G = 0) {ζ B L : ℝ}
    (hζ : 0 ≤ ζ) (hB : 0 ≤ B) (_hL : 0 ≤ L)
    (hX : ∀ i, rowNorm X i ≤ ζ) (hXG : ∀ i, rowNorm (X*G) i ≤ B)
    (hJ : ∀ i, rowL1 J i ≤ L) (i : Fin n) :
    rowNorm (J*E) i ≤ L * (ζ+B*opNorm P) := by
  have hQnorm : opNorm Qᴴ ≤ 1 := by
    rw [opNorm_conjTranspose]
    exact opNorm_le_one_of_isometry Q hQ
  have hrows (a : Fin n) : rowNorm (X - (X*G*P)*Qᴴ) a ≤ ζ+B*opNorm P := by
    apply (rowNorm_sub_le _ _ a).trans
    apply add_le_add (hX a)
    calc
      _ ≤ rowNorm (X*G*P) a * opNorm Qᴴ := rowNorm_mul_le _ _ a
      _ ≤ rowNorm (X*G*P) a * 1 :=
        mul_le_mul_of_nonneg_left hQnorm (rowNorm_nonneg _ _)
      _ = rowNorm (X*G*P) a := mul_one _
      _ ≤ rowNorm (X*G) a * opNorm P := rowNorm_mul_le _ _ a
      _ ≤ B * opNorm P := mul_le_mul_of_nonneg_right (hXG a) (opNorm_nonneg P)
  rw [cancellation E X Y Q G P J hE hP hzero]
  exact (rowNorm_left_mul_le J _ i hrows).trans
    (mul_le_mul_of_nonneg_right (hJ i) (add_nonneg hζ (mul_nonneg hB (opNorm_nonneg P))))

theorem cancellation_pinv_row_bound {n r s : ℕ} (E X : Matrix (Fin n) (Fin n) ℝ)
    (Y Q : Matrix (Fin n) (Fin r) ℝ) (G : Matrix (Fin n) (Fin s) ℝ)
    (J : Matrix (Fin n) (Fin n) ℝ)
    (hE : E = X + Y * Qᴴ) (hQ : Qᴴ * Q = 1)
    (hrank : ((Qᴴ*G) * (Qᴴ*G)ᴴ).PosDef) (hzero : (J*E)*G = 0)
    {ζ B L : ℝ} (hζ : 0 ≤ ζ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hX : ∀ i, rowNorm X i ≤ ζ) (hXG : ∀ i, rowNorm (X*G) i ≤ B)
    (hJ : ∀ i, rowL1 J i ≤ L) (i : Fin n) :
    rowNorm (J*E) i ≤ L*(ζ+B*opNorm (pinv (Qᴴ*G))) :=
  cancellation_row_bound E X Y Q G (pinv (Qᴴ*G)) J hE hQ
    (mul_pinv_eq_one _ hrank.isUnit) hzero hζ hB hL hX hXG hJ i

#assert_trust kernel rowNorm
#assert_trust kernel rowNorm_nonneg
#assert_trust kernel rowNorm_sq
#assert_trust kernel rowNorm_sub_le
#assert_trust kernel rowNorm_mul_le
#assert_trust kernel rowNorm_left_mul_le
#assert_trust kernel opNorm_le_one_of_isometry
#assert_trust kernel cancellation
#assert_trust kernel cancellation_row_bound
#assert_trust kernel cancellation_pinv_row_bound
#print axioms cancellation
#print axioms cancellation_row_bound
#print axioms cancellation_pinv_row_bound
end NLA.IE06.EliminationSmoothing
