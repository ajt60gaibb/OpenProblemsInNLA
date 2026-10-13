import NLA.Proofs.RA10.SpectralFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Functional calculus under change of indices, orthogonal conjugation and
block direct sums. These allow the frozen all-size monotonicity assumption to
be used in block-matrix arguments without imposing a new spectral convention. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix
open scoped BigOperators Matrix

namespace NLA.Proofs.RA10

theorem matrix_cfc_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (f : ℝ → ℝ)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    cfc f (reindex e e A) = reindex e e (cfc f A) := by
  let φ : Matrix ι ι ℝ ≃⋆ₐ[ℝ] Matrix κ κ ℝ :=
    { reindexAlgEquiv ℝ ℝ e with
      map_smul' := fun r M => by ext i j; rfl
      map_star' := fun M => by
        ext i j
        rfl }
  have hφ : Continuous φ := by
    change Continuous (fun M : Matrix ι ι ℝ => M.submatrix e.symm e.symm)
    fun_prop
  have hc : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  exact (StarAlgHomClass.map_cfc φ f A hc hφ hA (hA.submatrix e.symm)).symm

theorem matrix_operatorMonotone_cfc {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ℝ → ℝ} (hf : OperatorMonotoneOnPositive f)
    {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (A - B).PosSemidef) : (cfc f A - cfc f B).PosSemidef := by
  let e := Fintype.equivFin ι
  have h := operatorMonotoneOnPositive_cfc hf
    (hA.submatrix e.symm.injective) (hB.submatrix e.symm.injective)
    (hAB.submatrix e.symm)
  change (cfc f (reindex e e A) - cfc f (reindex e e B)).PosSemidef at h
  rw [matrix_cfc_reindex e f hA.1, matrix_cfc_reindex e f hB.1] at h
  have heq : (reindex e e (cfc f A) - reindex e e (cfc f B)).submatrix e e =
      cfc f A - cfc f B := by ext i j; simp [reindex_apply]
  exact heq ▸ h.submatrix e

theorem matrix_cfc_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) {A U : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hU : U.transpose * U = 1) :
    cfc f (U * A * U.transpose) = U * cfc f A * U.transpose := by
  let u : unitary (Matrix ι ι ℝ) := ⟨U, by
    constructor
    · simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using hU
    · simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
        using mul_eq_one_comm.mp hU⟩
  let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) u
  have hφ : Continuous φ := by
    change Continuous (fun M : Matrix ι ι ℝ => U * M * star U)
    fun_prop
  have hc : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  simpa only [φ, u, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] using!
    (StarAlgHomClass.map_cfc φ f A hc hφ hA (by
      change (U * A * Uᴴ).IsHermitian
      exact isHermitian_mul_mul_conjTranspose U hA)).symm

theorem matrix_cfc_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℝ → ℝ) (a : ι → ℝ) : cfc f (diagonal a) = diagonal (fun i => f (a i)) := by
  have hA : (diagonal a).IsHermitian := isHermitian_diagonal a
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU := mul_eq_one_comm.mp hU
  have heq : diagonal a = U * diagonal hA.eigenvalues * U.transpose := by
    simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hA.spectral_theorem
  have hi : diagonal a * U = U * diagonal hA.eigenvalues := by
    conv_lhs => rw [heq]
    simp only [Matrix.mul_assoc, hU, mul_one]
  have hf : diagonal (fun i => f (a i)) * U = U * diagonal (fun i => f (hA.eigenvalues i)) := by
    ext i j
    have hij := congrArg (fun M : Matrix ι ι ℝ => M i j) hi
    simp only [diagonal_mul, mul_diagonal] at hij ⊢
    by_cases hab : a i = hA.eigenvalues j
    · rw [hab, mul_comm]
    · have hz : U i j = 0 := by
        have hm : (a i - hA.eigenvalues j) * U i j = 0 := by nlinarith [hij]
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hab)
      simp [hz]
  rw [hA.cfc_eq]
  change U * diagonal (fun i => f (hA.eigenvalues i)) * U.transpose = diagonal (fun i => f (a i))
  rw [← hf, Matrix.mul_assoc, hUU, mul_one]

theorem matrix_cfc_blockDiagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ℝ → ℝ)
    {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    cfc f (fromBlocks A 0 0 B) = fromBlocks (cfc f A) 0 0 (cfc f B) := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  let V : Matrix κ κ ℝ := hB.eigenvectorUnitary
  have hU : U.transpose * U = 1 := by
    simpa only [U, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hV : V.transpose * V = 1 := by
    simpa only [V, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hW : (fromBlocks U 0 0 V).transpose * fromBlocks U 0 0 V = 1 := by
    simp [fromBlocks_transpose, fromBlocks_multiply, hU, hV]
  have heq : fromBlocks A 0 0 B = fromBlocks U 0 0 V *
      diagonal (Sum.elim hA.eigenvalues hB.eigenvalues) * (fromBlocks U 0 0 V).transpose := by
    rw [← fromBlocks_diagonal]
    simp only [fromBlocks_transpose, transpose_zero, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    have ha : A = U * diagonal hA.eigenvalues * U.transpose := by
      simpa [U, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hA.spectral_theorem
    have hb : B = V * diagonal hB.eigenvalues * V.transpose := by
      simpa [V, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hB.spectral_theorem
    simpa only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] using
      congrArg₂ (fun X Y => fromBlocks X (0 : Matrix ι κ ℝ) (0 : Matrix κ ι ℝ) Y) ha hb
  rw [heq, matrix_cfc_orthogonal f (isHermitian_diagonal _) hW, matrix_cfc_diagonal]
  have hd : diagonal (fun i => f (Sum.elim hA.eigenvalues hB.eigenvalues i)) =
      fromBlocks (diagonal (fun i => f (hA.eigenvalues i))) 0 0
        (diagonal (fun i => f (hB.eigenvalues i))) := by
    rw [fromBlocks_diagonal]
    congr 1
    funext i
    cases i <;> rfl
  rw [hd, hA.cfc_eq, hB.cfc_eq]
  simp only [fromBlocks_transpose, transpose_zero, fromBlocks_multiply,
    Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, Function.comp_def, RCLike.ofReal_real_eq_id,
    id_eq, U, V, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

#assert_trust kernel matrix_cfc_reindex
#assert_trust kernel matrix_operatorMonotone_cfc
#assert_trust kernel matrix_cfc_orthogonal
#assert_trust kernel matrix_cfc_diagonal
#assert_trust kernel matrix_cfc_blockDiagonal
#print axioms matrix_operatorMonotone_cfc

end NLA.Proofs.RA10
