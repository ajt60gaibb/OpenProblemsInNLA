/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! RA-19: the exact generic count of all smooth bilinear distance critical
points with one fixed zero. See docs/lean/statements/RA-19/NUMERICAL_TARGETS.md.
No resultant count or ED-degree theorem is asserted as proved. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.ReviewedStatements.RA19

/-- d ranges over all naturals, so the actual matrix order ranges over all n>=3. -/
abbrev Square (d : ℕ) := Matrix (Fin (d + 3)) (Fin (d + 3)) ℂ

/-- The exact determinant derivative, valid at singular matrices too. -/
def DetDifferential {d : ℕ} (X Z : Square d) : ℂ :=
  Matrix.trace (X.adjugate * Z)

/-- The restricted determinant is a nonzero squarefree polynomial on X_00=0.
Its smooth locus is exactly nonvanishing of this restricted differential. -/
def SmoothPoint {d : ℕ} (X : Square d) : Prop :=
  X 0 0 = 0 ∧ X.det = 0 ∧
    ∃ Z : Square d, Z 0 0 = 0 ∧ DetDifferential X Z ≠ 0

/-- Vanishing bilinear distance derivative on every tangent direction.
There is no conjugation, inverse, rank surrogate or missing smoothness guard. -/
def Critical {d : ℕ} (U X : Square d) : Prop :=
  SmoothPoint X ∧ ∀ Z : Square d,
    Z 0 0 = 0 → DetDifferential X Z = 0 →
      (∑ i, ∑ j, (X i j - U i j) * Z i j) = 0

/-- A nonempty principal algebraic open of data has exactly 5n-7 distinct
smooth critical points, with a bijection certifying the complete finite count. -/
def Target : Prop :=
  ∀ d : ℕ, ∃ p : MvPolynomial (Fin (d + 3) × Fin (d + 3)) ℂ,
    (∃ U₀ : Square d, MvPolynomial.eval (fun ij => U₀ ij.1 ij.2) p ≠ 0) ∧
    ∀ U : Square d, MvPolynomial.eval (fun ij => U ij.1 ij.2) p ≠ 0 →
      Nonempty ({X : Square d // Critical U X} ≃ Fin (5 * (d + 3) - 7))

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.RA19
