import NLA.Proofs.MF03.FiniteRange
import NLA.Proofs.MF03.LargeOrderDisk
import NLA.Proofs.MF03.PadeHighEquations
import NLA.Proofs.MF03.PadeDenominatorTail

/-! The full frozen MF-03 target, combining the reviewed finite orders with
the original determinant-derived all-order Padé pair and sharp disk gate. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

/-- The original all-order MF-03 closed-disk statement for every positive
Padé order, with reduced representative existence and universal transport. -/
theorem all_order_target : Target := by
  intro m hm
  by_cases hsmall : m ≤ 15
  · exact target_through_fifteen m hm hsmall
  · have hlarge : 16 ≤ m := by omega
    let P := cosinePadeNumerator m
    let Q := cosinePadeDenominator m
    have hpair : NormalizedPadeRepresentation m P Q :=
      cosinePade_normalized m
    have hcoeff : ∀ j : ℕ, 1 ≤ j → j ≤ m →
        ‖Q.coeff j‖ ≤ (cosineTail m) ^ j := by
      intro j hjpos hjm
      exact cosinePadeDenominator_coeff_norm_le_tail m j hjpos hjm
    have hdisk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
        Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) :=
      largeOrder_disk_of_tail_coefficients m hlarge P Q hpair hcoeff
    obtain ⟨Pᵣ, Qᵣ, hred, _⟩ :=
      normalized_exists_reduced m P Q hpair
    refine ⟨⟨Pᵣ, Qᵣ, hred⟩, ?_⟩
    intro P' Q' hred'
    exact disk_bound_for_every_reduced_pair m P Q hpair hdisk P' Q' hred'

#assert_statement NLA.Statements.MF03.Target
#assert_trust kernel all_order_target
#print axioms all_order_target

end NLA.Proofs.MF03
