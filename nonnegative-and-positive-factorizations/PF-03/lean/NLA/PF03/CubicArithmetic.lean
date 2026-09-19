/-
Original mathematics and seed: Sidney Holden, Flatiron Institute,
Simons Foundation. Formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology; Codex assistance.
Explicit arithmetic modulo the actually proved equation alpha^3=2.
-/
import NLA.PF03.RootCertificate

set_option autoImplicit false
noncomputable section
namespace NLA.PF03

lemma alpha_pow_four : alpha ^ 4 = 2 * alpha := by
  calc
    alpha ^ 4 = alpha ^ 3 * alpha := by ring
    _ = 2 * alpha := by rw [alpha_certificate.1]

theorem cubic_eval_operations :
    cubicEval cubicZero = 0 ∧ cubicEval cubicOne = 1 ∧
      (∀ x y : Cubic, cubicEval (cubicAdd x y) = cubicEval x + cubicEval y) ∧
      (∀ x y : Cubic, cubicEval (cubicMul x y) = cubicEval x * cubicEval y) := by
  refine ⟨by simp [cubicEval, cubicZero], by simp [cubicEval, cubicOne], ?_, ?_⟩
  · intro x y
    simp only [cubicEval, cubicAdd, Rat.cast_add]
    ring
  · intro x y
    simp only [cubicEval, cubicMul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
    ring_nf
    simp only [alpha_certificate.1, alpha_pow_four]
    ring

#print axioms cubic_eval_operations
#assert_trust kernel cubic_eval_operations

end NLA.PF03
