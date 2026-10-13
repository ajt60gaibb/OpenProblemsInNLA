import NLA.Proofs.RA10.OperatorMonotoneCompression

/-! All-size matrix concavity, obtained from monotonicity and continuity by
orthogonal block rotation and the compression inequality. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

def blockRotation {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ℝ) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := fromBlocks (p • 1) (q • 1) (-q • 1) (p • 1)

theorem blockRotation_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p q : ℝ} (hpq : p ^ 2 + q ^ 2 = 1) :
    (blockRotation (ι := ι) p q).transpose * blockRotation p q = 1 := by
  simp only [blockRotation, fromBlocks_transpose, transpose_smul, transpose_one,
    fromBlocks_multiply, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, smul_smul]
  have hpp : p * p + -q * -q = 1 := by nlinarith
  have hqq : q * q + p * p = 1 := by nlinarith
  have hzero : p * q + -q * p = 0 := by ring
  have hzero' : q * p + p * -q = 0 := by ring
  simp only [← add_smul, hpp, hqq, hzero, hzero', one_smul, zero_smul, fromBlocks_one]

theorem blockRotation_compression {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ℝ) (A B : Matrix ι ι ℝ) :
    (blockRotation p q * fromBlocks A 0 0 B * (blockRotation p q).transpose).toBlocks₁₁ =
      p ^ 2 • A + q ^ 2 • B := by
  simp only [blockRotation, fromBlocks_transpose, transpose_smul, transpose_one,
    fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  ext i j
  simp [toBlocks₁₁, pow_two]

theorem operatorMonotone_matrix_concave {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : OperatorMonotoneOnPositive f)
    (hcont : ContinuousOn f (Set.Ioi 0))
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (cfc f (t • A + (1 - t) • B) - (t • cfc f A + (1 - t) • cfc f B)).PosSemidef := by
  let p := Real.sqrt t
  let q := Real.sqrt (1 - t)
  have hp : p ^ 2 = t := Real.sq_sqrt ht
  have hq : q ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hpq : p ^ 2 + q ^ 2 = 1 := by rw [hp, hq]; ring
  let U := blockRotation (ι := ι) p q
  have hU : U.transpose * U = 1 := blockRotation_orthogonal hpq
  have hu : IsUnit U := isUnit_iff_exists_inv.mpr ⟨U.transpose, mul_eq_one_comm.mp hU⟩
  have hD := matrix_blockDiagonal_posDef hA hB
  have hX : (U * fromBlocks A 0 0 B * U.transpose).PosDef := by
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      hu.posDef_star_right_conjugate_iff.mpr hD
  have h := operatorMonotone_compression hf hcont hX
  rw [matrix_cfc_orthogonal f hD.1 hU, matrix_cfc_blockDiagonal f hA.1 hB.1] at h
  simpa only [U, blockRotation_compression, hp, hq] using h

theorem normalizedProfile_matrix_concave {ι : Type*} [Fintype ι] [DecidableEq ι]
    {g : PositiveArgument → ℝ} (hg : g ∈ normalizedAdmissibleCompactClass)
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (cfc (positiveProfileExtension g) (t • A + (1 - t) • B) -
      (t • cfc (positiveProfileExtension g) A +
        (1 - t) • cfc (positiveProfileExtension g) B)).PosSemidef :=
  operatorMonotone_matrix_concave (normalizedAdmissibleCompactClass_operatorMonotone hg)
    (normalizedAdmissibleCompactClass_continuousOn hg) hA hB ht ht1

#assert_trust kernel blockRotation_orthogonal
#assert_trust kernel blockRotation_compression
#assert_trust kernel operatorMonotone_matrix_concave
#assert_trust kernel normalizedProfile_matrix_concave
#print axioms normalizedProfile_matrix_concave

end NLA.Proofs.RA10
