import NLA.Proofs.RA10.NuclearTraceDualAttains
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! RA-10: the frozen nuclear norm of a real positive semidefinite matrix
equals its trace. This is a generic partial dependency for source Eq. (8). -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

private theorem trace_orthogonal_mul_posSemidef_le {n : ℕ}
    (U Y : Matrix (Fin n) (Fin n) ℝ)
    (_hUleft : U.transpose * U = 1) (hUright : U * U.transpose = 1)
    (hY : Matrix.PosSemidef Y) :
    Matrix.trace (U.transpose * Y) ≤ Matrix.trace Y := by
  have hsym : Y.transpose = Y := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hY.1.eq
  have hP : Matrix.PosSemidef ((1 - U).transpose * Y * (1 - U)) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hY.conjTranspose_mul_mul_same (1 - U)
  have hnonneg : 0 ≤ Matrix.trace ((1 - U).transpose * Y * (1 - U)) :=
    hP.trace_nonneg
  have hcycle : Matrix.trace (U.transpose * Y * U) = Matrix.trace Y := by
    calc
      Matrix.trace (U.transpose * Y * U) = Matrix.trace (U * U.transpose * Y) := by
        rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace Y := by rw [hUright, one_mul]
  have htranspose : Matrix.trace (Y * U) = Matrix.trace (U.transpose * Y) := by
    calc
      Matrix.trace (Y * U) = Matrix.trace ((Y * U).transpose) :=
        (Matrix.trace_transpose _).symm
      _ = Matrix.trace (U.transpose * Y) := by rw [Matrix.transpose_mul, hsym]
  have hexpand :
      Matrix.trace ((1 - U).transpose * Y * (1 - U)) =
        Matrix.trace Y - Matrix.trace (U.transpose * Y) -
        Matrix.trace (Y * U) + Matrix.trace (U.transpose * Y * U) := by
    simp only [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, mul_sub,
      one_mul, mul_one, Matrix.trace_sub]
    ring
  rw [hexpand, hcycle, htranspose] at hnonneg
  linarith

theorem nuclearNorm_eq_trace_of_posSemidef {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Matrix.PosSemidef Y) :
    NLA.Statements.RA10.NuclearNorm Y = Matrix.trace Y := by
  obtain ⟨U, hUleft, hUright, hUtrace⟩ := nuclearNorm_trace_orthogonal_attains Y
  apply le_antisymm
  · exact hUtrace.symm.trans_le
      (trace_orthogonal_mul_posSemidef_le U Y hUleft hUright hY)
  · simpa using (nuclearNorm_trace_orthogonal_le
      (1 : Matrix (Fin n) (Fin n) ℝ) Y (by simp) (by simp))

#assert_trust kernel trace_orthogonal_mul_posSemidef_le
#assert_trust kernel nuclearNorm_eq_trace_of_posSemidef
#print axioms nuclearNorm_eq_trace_of_posSemidef

end NLA.Proofs.RA10
