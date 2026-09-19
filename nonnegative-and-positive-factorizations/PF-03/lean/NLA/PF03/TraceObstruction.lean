import NLA.PF03.Definitions
import LeanCert.Tactic

/-!
C20: expand finite sums and use every entry of X Xᵀ = I. No positivity,
rank, or nonzero-width premise is introduced.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. Author: /root.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

theorem trace_obstruction {m : ℕ} (X : RMat 7 m) (hX : X * Xᵀ = 1) :
    (∑ j : Fin m, quad quadraticSeed (fun r => X r j)) = Matrix.trace quadraticSeed := by
  have hentry (r s : Fin 7) :
      (∑ j : Fin m, X r j * X s j) = (1 : RMat 7 7) r s := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply] using congrFun (congrFun hX r) s
  calc
    (∑ j : Fin m, quad quadraticSeed (fun r => X r j)) =
        ∑ r : Fin 7, ∑ s : Fin 7,
          quadraticSeed r s * (∑ j : Fin m, X r j * X s j) := by
      simp only [quad, bilinear]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = Matrix.trace quadraticSeed := by
      simp_rw [hentry]
      simp [Matrix.one_apply, Matrix.trace, Matrix.diag]

#print axioms trace_obstruction
#assert_trust kernel trace_obstruction

end NLA.PF03
