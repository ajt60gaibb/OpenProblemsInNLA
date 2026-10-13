import NLA.Statements.RA10
import Mathlib.Tactic.Ring

/-! RA-10 selected projection, exact frozen truncation, and symmetry.
The idempotence, rank and supported functional calculus gates follow in
separate modules; the full RA-10 transfer target remains open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

def selectedProjection {n : ℕ} (k : ℕ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ a : Fin n,
    if a.val < k then Q i a * Q j a else 0

theorem selectedProjection_eq_functionTruncation {n : ℕ}
    (k : ℕ) (eigenvalues : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    selectedProjection k Q =
      NLA.Statements.RA10.FunctionTruncation k (fun _ => (1 : ℝ)) eigenvalues Q := by
  ext i j
  simp [selectedProjection, NLA.Statements.RA10.FunctionTruncation]

theorem selectedProjection_transpose {n : ℕ}
    (k : ℕ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    (selectedProjection k Q).transpose = selectedProjection k Q := by
  ext i j
  simp only [Matrix.transpose_apply, selectedProjection, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

#assert_trust kernel selectedProjection_eq_functionTruncation
#assert_trust kernel selectedProjection_transpose
#print axioms selectedProjection_transpose

end NLA.Proofs.RA10
