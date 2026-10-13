import NLA.Statements.RA10
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-! RA-10 source Equation (8): exact reflection algebra behind two-block
pinching. Nuclear-norm contraction remains open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA10

def reflection {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := P + P - 1

def pinch {n : ℕ} (P M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  P * M * P + (1 - P) * M * (1 - P)

theorem reflection_transpose {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hsym : P.transpose = P) :
    (reflection P).transpose = reflection P := by
  simp [reflection, hsym]

theorem reflection_square {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hid : P * P = P) :
    reflection P * reflection P = 1 := by
  unfold reflection
  noncomm_ring [hid]

theorem reflection_orthogonal {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hsym : P.transpose = P) (hid : P * P = P) :
    (reflection P).transpose * reflection P = 1 ∧
      reflection P * (reflection P).transpose = 1 := by
  rw [reflection_transpose P hsym]
  exact ⟨reflection_square P hid, reflection_square P hid⟩

theorem pinch_eq_reflection_average {n : ℕ}
    (P M : Matrix (Fin n) (Fin n) ℝ) :
    pinch P M = (1 / 2 : ℝ) • (M + reflection P * M * reflection P) := by
  have hdouble : pinch P M + pinch P M =
      M + reflection P * M * reflection P := by
    unfold pinch reflection
    noncomm_ring
  calc
    pinch P M = (1 / 2 : ℝ) • (pinch P M + pinch P M) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    _ = (1 / 2 : ℝ) • (M + reflection P * M * reflection P) := by
      rw [hdouble]

#assert_trust kernel reflection_transpose
#assert_trust kernel reflection_square
#assert_trust kernel reflection_orthogonal
#assert_trust kernel pinch_eq_reflection_average
#print axioms pinch_eq_reflection_average

end NLA.Proofs.RA10
