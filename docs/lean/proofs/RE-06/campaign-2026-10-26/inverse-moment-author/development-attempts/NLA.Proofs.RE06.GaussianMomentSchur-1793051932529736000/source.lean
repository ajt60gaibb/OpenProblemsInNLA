import NLA.Proofs.RE06.GaussianMomentAlgebra
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment
open NLA.Computation.NonadaptiveMatrixQuery

theorem inverse_block_first_entry {d : ℕ}
    (A : Matrix Unit Unit ℝ) (B : Matrix Unit (Fin d) ℝ)
    (C : Matrix (Fin d) Unit ℝ) (D : Matrix (Fin d) (Fin d) ℝ)
    (hD : D.det ≠ 0) (hG : (Matrix.fromBlocks A B C D).det ≠ 0) :
    (Matrix.fromBlocks A B C D)⁻¹ (Sum.inl ()) (Sum.inl ()) =
      ((A - B * D⁻¹ * C) () ())⁻¹ := by
  letI : Invertible D := Matrix.invertibleOfIsUnitDet D (isUnit_iff_ne_zero.mpr hD)
  letI : Invertible (Matrix.fromBlocks A B C D) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hG)
  letI : Invertible (A - B * ⅟D * C) :=
    Matrix.invertibleOfFromBlocks₂₂Invertible A B C D
  have h := Matrix.invOf_fromBlocks₂₂_eq A B C D
  simp only [Matrix.invOf_eq_nonsing_inv] at h
  have hentry := congrArg (fun M => M (Sum.inl ()) (Sum.inl ())) h
  simpa only [Matrix.fromBlocks_apply₁₁, Matrix.inv_subsingleton,
    Matrix.diagonal_apply_eq, Ring.inverse_eq_inv] using hentry

def singleRow {p : ℕ} (z : Fin p → ℝ) : Matrix Unit (Fin p) ℝ := fun _ => z

def rowStack {d p : ℕ} (z : Fin p → ℝ) (W : Matrix (Fin d) (Fin p) ℝ) :
    Matrix (Unit ⊕ Fin d) (Fin p) ℝ := Matrix.fromRows (singleRow z) W

def rowSchur {d p : ℕ} (z : Fin p → ℝ) (W : Matrix (Fin d) (Fin p) ℝ) : ℝ :=
  ((singleRow z) * (singleRow z).transpose -
    ((singleRow z) * W.transpose) * (W * W.transpose)⁻¹ *
      (W * (singleRow z).transpose)) () ()

theorem rowStack_gram {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) :
    rowStack z W * (rowStack z W).transpose =
      Matrix.fromBlocks
        ((singleRow z) * (singleRow z).transpose)
        ((singleRow z) * W.transpose)
        (W * (singleRow z).transpose) (W * W.transpose) := by
  simp only [rowStack, Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols]

theorem inverse_gram_first_entry {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0)
    (hG : (rowStack z W * (rowStack z W).transpose).det ≠ 0) :
    (rowStack z W * (rowStack z W).transpose)⁻¹ (Sum.inl ()) (Sum.inl ()) =
      (rowSchur z W)⁻¹ := by
  rw [rowStack_gram] at hG ⊢
  exact inverse_block_first_entry _ _ _ _ hW hG

def rowComplement {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := 1 - pseudoInverse W * W

theorem rowComplement_transpose {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    (rowComplement W).transpose = rowComplement W := by
  simp only [rowComplement, Matrix.transpose_sub, Matrix.transpose_one,
    Pseudo.pseudoinverse_mul_transpose]

theorem rowComplement_idempotent {d p : ℕ} (W : Matrix (Fin d) (Fin p) ℝ) :
    rowComplement W * rowComplement W = rowComplement W := by
  have hP : (pseudoInverse W * W) * (pseudoInverse W * W) = pseudoInverse W * W := by
    rw [← Matrix.mul_assoc, Pseudo.pseudoinverse_mul_pseudoinverse]
  simp only [rowComplement, Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_one, hP, sub_self, sub_zero]

theorem rowSchur_complement {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) (hW : (W * W.transpose).det ≠ 0) :
    rowSchur z W =
      (singleRow z * rowComplement W * (singleRow z).transpose) () () := by
  simp only [rowSchur, rowComplement, Pseudo.full_row_formula W hW,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, Matrix.sub_apply]

theorem rowSchur_residual_normSq {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) (hW : (W * W.transpose).det ≠ 0) :
    rowSchur z W = ∑ j, ((singleRow z * rowComplement W) () j) ^ 2 := by
  have hR : (singleRow z * rowComplement W) *
      (singleRow z * rowComplement W).transpose =
      singleRow z * rowComplement W * (singleRow z).transpose := by
    simp only [Matrix.transpose_mul, rowComplement_transpose]
    calc
      _ = singleRow z * (rowComplement W * rowComplement W) *
          (singleRow z).transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [rowComplement_idempotent]
  rw [rowSchur_complement z W hW, ← hR]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem rowSchur_nonneg {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ) (hW : (W * W.transpose).det ≠ 0) :
    0 ≤ rowSchur z W := by
  rw [rowSchur_residual_normSq z W hW]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem inverse_gram_first_entry_residual {d p : ℕ} (z : Fin p → ℝ)
    (W : Matrix (Fin d) (Fin p) ℝ)
    (hW : (W * W.transpose).det ≠ 0)
    (hG : (rowStack z W * (rowStack z W).transpose).det ≠ 0) :
    (rowStack z W * (rowStack z W).transpose)⁻¹ (Sum.inl ()) (Sum.inl ()) =
      (∑ j, ((singleRow z * rowComplement W) () j) ^ 2)⁻¹ := by
  rw [inverse_gram_first_entry z W hW hG, rowSchur_residual_normSq z W hW]

end NLA.Proofs.RE06.GaussianMoment
