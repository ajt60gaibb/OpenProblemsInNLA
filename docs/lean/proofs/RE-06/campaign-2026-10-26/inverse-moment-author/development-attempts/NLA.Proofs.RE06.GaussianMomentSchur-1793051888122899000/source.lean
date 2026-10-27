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

end NLA.Proofs.RE06.GaussianMoment
