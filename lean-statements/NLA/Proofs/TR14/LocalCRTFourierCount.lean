import NLA.Proofs.TR14.LocalCRTFourierSigma

/-!
Exact natural-number count of the dependent CRT/Fourier node family.
This is an affine-chart root count, not yet the original form's
projective root count or a claim about minimum tensor width.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The dependent family has exactly the sum of its local fiber sizes. -/
theorem localCRTFourierNode_card (m : ℕ) (g : Polynomial ℂ) :
    Fintype.card (LocalCRTFourierNode m g) =
      ∑ α : LocalRootIndex g,
        localFourierCount m (localRootMultiplicity g α) := by
  classical
  simp only [LocalCRTFourierNode, Fintype.card_sigma, Fintype.card_fin]

private theorem localFourierCount_add_complement (m ℓ : ℕ)
    (hm : 3 ≤ m) (hℓ : 0 < ℓ) :
    localFourierCount m ℓ + (m - 2) = (m - 1) * ℓ := by
  have hm1 : m - 2 + 1 = m - 1 := by omega
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega
  calc
    localFourierCount m ℓ + (m - 2) =
        (m - 1) * (ℓ - 1) + (m - 1) := by
          unfold localFourierCount
          omega
    _ = (m - 1) * ℓ := by
      conv_lhs => rhs; rw [← mul_one (m - 1)]
      rw [← mul_add, hℓ1]

/-- Exact local-node sum, including every repeated-root multiplicity. -/
theorem localCRTFourierNode_card_formula (m : ℕ) (hm : 3 ≤ m)
    (g : Polynomial ℂ) :
    Fintype.card (LocalCRTFourierNode m g) =
      (m - 1) * g.natDegree -
        (m - 2) * (localRootSupport g).card := by
  classical
  rw [localCRTFourierNode_card]
  have hsum :
      (∑ α : LocalRootIndex g,
        localFourierCount m (localRootMultiplicity g α)) +
        (m - 2) * (localRootSupport g).card =
      (m - 1) * g.natDegree := by
    calc
      (∑ α : LocalRootIndex g,
          localFourierCount m (localRootMultiplicity g α)) +
          (m - 2) * (localRootSupport g).card =
        ∑ α : LocalRootIndex g,
          (localFourierCount m (localRootMultiplicity g α) + (m - 2)) := by
            simp [Finset.sum_add_distrib, mul_comm]
      _ = ∑ α : LocalRootIndex g,
            (m - 1) * localRootMultiplicity g α := by
              apply Finset.sum_congr rfl
              intro α _
              exact localFourierCount_add_complement m _ hm
                (localRootMultiplicity_pos g α)
      _ = (m - 1) * g.natDegree := by
            rw [← Finset.mul_sum, localRootMultiplicity_sum]
  omega

#assert_trust kernel localCRTFourierNode_card
#assert_trust kernel localFourierCount_add_complement
#assert_trust kernel localCRTFourierNode_card_formula
#print axioms localCRTFourierNode_card_formula

end
end NLA.Proofs.TR14
