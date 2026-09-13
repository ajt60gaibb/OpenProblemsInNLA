/- Exact consumer of reviewed RA-09 contract14; never imported by implementation. -/
import NLA.RA09.ZeroColumn
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.RA09.RootContractChecks

theorem zero_column_average_exact_consumer {n : ℕ} (a p : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (f : ℝ → ℝ) (hf : AdmissibleFunction f) (τ : ℝ) :
    (f 0)^2 - 2*f 0*(∑ i, p i*f (a i)) ≤
      ∑ i, p i * scalarAuxiliary f τ (a i) := by
  exact zero_column_average_proved a p ha hp hsum f hf τ

#assert_trust kernel zero_column_average_exact_consumer
#print axioms zero_column_average_exact_consumer
end NLA.RA09.RootContractChecks
