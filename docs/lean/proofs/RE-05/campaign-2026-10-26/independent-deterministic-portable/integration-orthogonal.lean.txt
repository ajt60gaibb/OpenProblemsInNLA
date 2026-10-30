import NLA.Proofs.RE05.OrthogonalOptimum
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
open scoped InnerProductSpace

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example (n : ℕ) (A B : Square n) : frobenius A B = 0 ↔ A = B :=
  NLA.Proofs.RE05.frobenius_eq_zero_iff A B
example (n : ℕ) (A B C : Square n) :
    frobenius A C ≤ frobenius A B + frobenius B C :=
  NLA.Proofs.RE05.frobenius_triangle A B C
example (n q : ℕ) (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        ⟪NLA.Proofs.RE05.matrixVector A - NLA.Proofs.RE05.representationMap P c,
          NLA.Proofs.RE05.representationMap P d⟫_ℝ = 0 :=
  NLA.Proofs.RE05.exists_orthogonal_optimum P A
example (n q : ℕ) (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        frobenius A (represent P d) ^ 2 =
          NLA.Computation.LinearFamilyQuery.optimum P A ^ 2 +
          frobenius (represent P c) (represent P d) ^ 2 :=
  NLA.Proofs.RE05.exists_pythagorean_optimum P A
example (n q : ℕ) (P : Basis n q) (A : Square n) :
    NLA.Computation.LinearFamilyQuery.optimum P A = 0 ↔
      ∃ c : Fin (q + 1) → ℝ, A = represent P c :=
  NLA.Proofs.RE05.optimum_eq_zero_iff P A

#assert_trust kernel NLA.Proofs.RE05.matrixVector_sub
#assert_trust kernel NLA.Proofs.RE05.frobenius_eq_zero_iff
#assert_trust kernel NLA.Proofs.RE05.frobenius_triangle
#assert_trust kernel NLA.Proofs.RE05.exists_orthogonal_optimum
#assert_trust kernel NLA.Proofs.RE05.exists_pythagorean_optimum
#assert_trust kernel NLA.Proofs.RE05.optimum_eq_zero_iff
#print axioms NLA.Proofs.RE05.matrixVector_sub
#print axioms NLA.Proofs.RE05.frobenius_eq_zero_iff
#print axioms NLA.Proofs.RE05.frobenius_triangle
#print axioms NLA.Proofs.RE05.exists_orthogonal_optimum
#print axioms NLA.Proofs.RE05.exists_pythagorean_optimum
#print axioms NLA.Proofs.RE05.optimum_eq_zero_iff
