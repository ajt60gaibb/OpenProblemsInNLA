import NLA.Proofs.MF03.Reduction
import NLA.Proofs.MF03.Transport
import NLA.Proofs.MF03.OrderOne
import NLA.Proofs.MF03.Finite02
import NLA.Proofs.MF03.Finite03
import NLA.Proofs.MF03.Finite04
import NLA.Proofs.MF03.Finite05
import NLA.Proofs.MF03.Finite06
import NLA.Proofs.MF03.Finite07
import NLA.Proofs.MF03.Finite08
import NLA.Proofs.MF03.Finite09
import NLA.Proofs.MF03.Finite10
import NLA.Proofs.MF03.Finite11
import NLA.Proofs.MF03.Finite12
import NLA.Proofs.MF03.Finite13
import NLA.Proofs.MF03.Finite14
import NLA.Proofs.MF03.Finite15

/-! The exact MF-03 target clause for each order from one through fifteen. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private theorem target_clause_of_normalized_disk
    (m : ℕ) (P₀ Q₀ : Polynomial ℂ)
    (h₀ : NormalizedPadeRepresentation m P₀ Q₀)
    (hdisk₀ : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
      Q₀.eval z ≠ 0 ∧ ‖(1 : ℂ) - P₀.eval z / Q₀.eval z‖ ≤ (2 : ℝ)) :
    (∃ P Q : Polynomial ℂ, ReducedPadeRepresentation m P Q) ∧
      ∀ P Q : Polynomial ℂ, ReducedPadeRepresentation m P Q →
        ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
          Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) := by
  obtain ⟨Pᵣ, Qᵣ, hred, _⟩ := normalized_exists_reduced m P₀ Q₀ h₀
  refine ⟨⟨Pᵣ, Qᵣ, hred⟩, ?_⟩
  intro P Q h
  exact disk_bound_for_every_reduced_pair m P₀ Q₀ h₀ hdisk₀ P Q h

/-- The complete MF-03 closed-disk clause is proved at every positive order
through fifteen, including existence of a reduced normalized pair. -/
theorem target_through_fifteen :
    ∀ m : ℕ, 1 ≤ m → m ≤ 15 →
      (∃ P Q : Polynomial ℂ, ReducedPadeRepresentation m P Q) ∧
        ∀ P Q : Polynomial ℂ, ReducedPadeRepresentation m P Q →
          ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
            Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) := by
  intro m hm hmax
  interval_cases m
  · exact order_one_target_clause
  · exact target_clause_of_normalized_disk 2 _ _ order_two_normalized order_two_disk
  · exact target_clause_of_normalized_disk 3 _ _ finite03_normalized finite03_disk
  · exact target_clause_of_normalized_disk 4 _ _ finite04_normalized finite04_disk
  · exact target_clause_of_normalized_disk 5 _ _ finite05_normalized finite05_disk
  · exact target_clause_of_normalized_disk 6 _ _ finite06_normalized finite06_disk
  · exact target_clause_of_normalized_disk 7 _ _ finite07_normalized finite07_disk
  · exact target_clause_of_normalized_disk 8 _ _ finite08_normalized finite08_disk
  · exact target_clause_of_normalized_disk 9 _ _ finite09_normalized finite09_disk
  · exact target_clause_of_normalized_disk 10 _ _ finite10_normalized finite10_disk
  · exact target_clause_of_normalized_disk 11 _ _ finite11_normalized finite11_disk
  · exact target_clause_of_normalized_disk 12 _ _ finite12_normalized finite12_disk
  · exact target_clause_of_normalized_disk 13 _ _ finite13_normalized finite13_disk
  · exact target_clause_of_normalized_disk 14 _ _ finite14_normalized finite14_disk
  · exact target_clause_of_normalized_disk 15 _ _ finite15_normalized finite15_disk

#print axioms target_through_fifteen
#assert_trust kernel target_through_fifteen

end NLA.Proofs.MF03
