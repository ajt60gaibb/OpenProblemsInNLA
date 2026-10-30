import NLA.Proofs.RE05.Attained
import NLA.Proofs.RE05.SVDTotal
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example : NLA.Statements.RE05.AttainedOptimum := NLA.Proofs.RE05.attainedOptimum
example : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := NLA.Proofs.RE05.svd_total
example (n q : ℕ) (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.optimum P A ≤ frobenius A (represent P d) :=
  NLA.Proofs.RE05.attained_optimum P A
example : ∀ (n q : ℕ) (P : Basis n q) (A : Square n), Independent P →
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.optimum P A ≤ frobenius A (represent P d) :=
  NLA.Proofs.RE05.attainedOptimum
example : ∀ (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ),
    ValidSVDResult B (exactSVD B) := NLA.Proofs.RE05.svd_total

#assert_trust kernel NLA.Proofs.RE05.matrixVector
#assert_trust kernel NLA.Proofs.RE05.representationMap
#assert_trust kernel NLA.Proofs.RE05.frobenius_eq_norm
#assert_trust kernel NLA.Proofs.RE05.exists_frobenius_minimum
#assert_trust kernel NLA.Proofs.RE05.attained_optimum
#assert_trust kernel NLA.Proofs.RE05.attainedOptimum
#assert_trust kernel NLA.Proofs.RE05.svd_total
#print axioms NLA.Proofs.RE05.matrixVector
#print axioms NLA.Proofs.RE05.representationMap
#print axioms NLA.Proofs.RE05.frobenius_eq_norm
#print axioms NLA.Proofs.RE05.exists_frobenius_minimum
#print axioms NLA.Proofs.RE05.attained_optimum
#print axioms NLA.Proofs.RE05.attainedOptimum
#print axioms NLA.Proofs.RE05.svd_total
