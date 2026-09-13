/- Exact consumers of the three independently reviewed RA-09 contracts.
Development diagnostics, never imported by the implementation. -/
import NLA.RA09.Frobenius

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA09.RootContractChecks

theorem frobenius_semantics_exact_consumer {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusSquared M = frobeniusNorm M ^ 2 ∧
    frobeniusSquared M = ∑ i, ∑ j, |M i j| ^ 2 ∧
    frobeniusSquared M = Matrix.trace (M.transpose * M) ∧
    0 ≤ frobeniusSquared M ∧
    (frobeniusSquared M = 0 ↔ M = 0) := by
  exact frobenius_semantics_proved M

#assert_trust kernel frobenius_semantics_exact_consumer
#print axioms frobenius_semantics_exact_consumer

theorem frobenius_orthogonal_invariance_exact_consumer {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin m) ℝ) (V : Matrix.unitaryGroup (Fin n) ℝ) :
    frobeniusSquared
      ((U : RealMatrix m) * M * (V : RealMatrix n)) = frobeniusSquared M := by
  exact frobenius_orthogonal_invariance_proved M U V

#assert_trust kernel frobenius_orthogonal_invariance_exact_consumer
#print axioms frobenius_orthogonal_invariance_exact_consumer

theorem trace_deficit_reduction_exact_consumer {n : ℕ} (A B : RealMatrix n)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hBA : B ≤ A) :
    frobeniusSquared (A-B) = frobeniusSquared A - frobeniusSquared B -
      2 * Matrix.trace (B * (A-B)) ∧
    0 ≤ Matrix.trace (B * (A-B)) ∧
    frobeniusSquared (A-B) ≤ frobeniusSquared A - frobeniusSquared B := by
  exact trace_deficit_reduction_proved A B hA hB hBA

#assert_trust kernel trace_deficit_reduction_exact_consumer
#print axioms trace_deficit_reduction_exact_consumer

end NLA.RA09.RootContractChecks
