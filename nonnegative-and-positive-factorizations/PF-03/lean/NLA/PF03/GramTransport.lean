import NLA.PF03.Definitions
import Mathlib.LinearAlgebra.Matrix.DotProduct
import LeanCert.Tactic

/-!
C19, following the frozen statement gate. The residual of the projection R L
has zero Gram matrix and therefore vanishes over the ordered field of rationals.
No rank or positivity assumption on C, and no restriction on its finite width,
is introduced.

Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. Author: /root.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem gram_factor_transport {N d m : ℕ} (R : QMat N d) (L : QMat d N)
    (C : QMat N m) (hLR : L * R = 1) (hC : C * Cᵀ = R * Rᵀ) :
    R * (L * C) = C ∧ (L * C) * (L * C)ᵀ = 1 := by
  let M : QMat N N := 1 - R * L
  have hMR : M * R = 0 := by
    simp only [M, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hLR,
      Matrix.mul_one, sub_self]
  have hgram : (M * C) * (M * C)ᵀ = 0 := by
    calc
      (M * C) * (M * C)ᵀ = M * (C * Cᵀ) * Mᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M * (R * Rᵀ) * Mᵀ := by rw [hC]
      _ = 0 := by rw [← Matrix.mul_assoc M R Rᵀ, hMR, Matrix.zero_mul, Matrix.zero_mul]
  have hMC : M * C = 0 := by
    ext i j
    have hs : ∑ k : Fin m, ((M * C) i k) ^ 2 = 0 := by
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, ← sq,
        Matrix.zero_apply] using congrFun (congrFun hgram i) i
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_hk : k ∈ (Finset.univ : Finset (Fin m))) => sq_nonneg ((M * C) i k))).mp hs
        j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hj
  refine ⟨?_, ?_⟩
  · have hz : C - R * (L * C) = 0 := by
      simpa only [M, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc] using hMC
    exact (sub_eq_zero.mp hz).symm
  · calc
      (L * C) * (L * C)ᵀ = L * (C * Cᵀ) * Lᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (L * R) * (L * R)ᵀ := by
        rw [hC]
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hLR, Matrix.transpose_one, Matrix.mul_one]

#print axioms gram_factor_transport
#assert_trust kernel gram_factor_transport

end NLA.PF03
