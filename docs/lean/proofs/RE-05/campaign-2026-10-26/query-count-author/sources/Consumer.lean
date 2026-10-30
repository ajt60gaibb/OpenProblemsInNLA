import NLA.Proofs.RE05.QueryCount
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example (n q : ℕ) (P : Basis n q) (ε : ℝ) (ω : ℕ → ℝ) :
    (batchQueries (plans P ε ω)).length =
      15 * (NLA.Proofs.RE05.selectedCount P ε + gaussianWidth q (squaredAccuracy ε)) :=
  NLA.Proofs.RE05.batchQueries_length P ε ω
example (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    0 < baseWidth q (squaredAccuracy ε) := NLA.Proofs.RE05.baseWidth_positive q ε hε
example (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    threshold q (squaredAccuracy ε) * baseWidth q (squaredAccuracy ε) =
      Real.sqrt ((q + 1 : ℕ) * baseWidth q (squaredAccuracy ε)) :=
  NLA.Proofs.RE05.threshold_mul_width q ε hε
example (n q : ℕ) (P : Basis n q) (ε : ℝ) (hε : 0 < ε)
    (hcharge : (NLA.Proofs.RE05.selectedCount P ε : ℝ) * threshold q (squaredAccuracy ε) ≤
      (q + 1 : ℕ)) :
    ∀ ω : ℕ → ℝ, ((batchQueries (plans P ε ω)).length : ℝ) ≤
      15 * (2 * Real.sqrt ((q + 1 : ℕ) * baseWidth q (squaredAccuracy ε)) +
        8 * Real.log (20 * (q + 1 : ℕ)) + 1) :=
  NLA.Proofs.RE05.sourceQueryBound_of_selected_charge P ε hε hcharge

#assert_trust kernel NLA.Proofs.RE05.selectedCount
#assert_trust kernel NLA.Proofs.RE05.batchQueries_length
#assert_trust kernel NLA.Proofs.RE05.baseWidth_positive
#assert_trust kernel NLA.Proofs.RE05.threshold_mul_width
#assert_trust kernel NLA.Proofs.RE05.sourceQueryBound_of_selected_charge
#print axioms NLA.Proofs.RE05.selectedCount
#print axioms NLA.Proofs.RE05.batchQueries_length
#print axioms NLA.Proofs.RE05.baseWidth_positive
#print axioms NLA.Proofs.RE05.threshold_mul_width
#print axioms NLA.Proofs.RE05.sourceQueryBound_of_selected_charge
