import NLA.Proofs.TR14.LocalCRTShift
import Mathlib.Algebra.Algebra.Pi

/-!
The exact complex-algebra Chinese remainder equivalence of a monic
polynomial with all of its truncated local root factors. Multiplicities
are retained, and the quotient root maps to `α + z` in every component.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

private def localRootIdeal (g : Polynomial ℂ) (α : LocalRootIndex g) :
    Ideal (Polynomial ℂ) :=
  Ideal.span {localPrimaryFactor α.val (localRootMultiplicity g α)}

private theorem localRoot_product (g : Polynomial ℂ) (hg : g.Monic) :
    (∏ α : LocalRootIndex g,
      localPrimaryFactor α.val (localRootMultiplicity g α)) = g := by
  classical
  calc
    (∏ α : LocalRootIndex g,
        localPrimaryFactor α.val (localRootMultiplicity g α)) =
      ∏ α ∈ localRootSupport g,
        ((Polynomial.X : Polynomial ℂ) - Polynomial.C α) ^ g.roots.count α := by
          simpa only [localPrimaryFactor, localRootMultiplicity] using
            (Finset.prod_coe_sort (s := localRootSupport g)
              (f := fun α : ℂ =>
                ((Polynomial.X : Polynomial ℂ) - Polynomial.C α) ^ g.roots.count α))
    _ = g := (localRoot_factorization g hg).symm

private theorem localRootIdeal_pairwise (g : Polynomial ℂ) :
    Pairwise (fun α β : LocalRootIndex g =>
      IsCoprime (localRootIdeal g α) (localRootIdeal g β)) := by
  intro α β hne
  exact (Ideal.isCoprime_span_singleton_iff _ _).2
    (localRootFactors_pairwise_coprime g hne)

private theorem localRootIdeal_inf (g : Polynomial ℂ) (hg : g.Monic) :
    (⨅ α : LocalRootIndex g, localRootIdeal g α) = Ideal.span {g} := by
  classical
  have hcop := localRootFactors_pairwise_coprime g
  have hi := Ideal.iInf_span_singleton
    (I := fun α : LocalRootIndex g =>
      localPrimaryFactor α.val (localRootMultiplicity g α))
    (fun α β hne => hcop hne)
  simpa only [localRootIdeal, localRoot_product g hg] using hi

private def localCRTPrimaryEquiv (g : Polynomial ℂ) (hg : g.Monic) :
    AdjoinRoot g ≃ₐ[ℂ]
      (∀ α : LocalRootIndex g,
        AdjoinRoot (localPrimaryFactor α.val (localRootMultiplicity g α))) := by
  let I : LocalRootIndex g → Ideal (Polynomial ℂ) := localRootIdeal g
  have hI : Pairwise (fun α β : LocalRootIndex g => IsCoprime (I α) (I β)) :=
    localRootIdeal_pairwise g
  have hspan : Ideal.span ({g} : Set (Polynomial ℂ)) = ⨅ α, I α :=
    (localRootIdeal_inf g hg).symm
  let E₁ : (Polynomial ℂ ⧸ Ideal.span ({g} : Set (Polynomial ℂ))) ≃ₐ[ℂ]
      (Polynomial ℂ ⧸ ⨅ α, I α) :=
    Ideal.quotientEquivAlgOfEq ℂ hspan
  let E₂ : (Polynomial ℂ ⧸ ⨅ α, I α) ≃ₐ[ℂ]
      (∀ α : LocalRootIndex g, Polynomial ℂ ⧸ I α) :=
    { Ideal.quotientInfRingEquivPiQuotient I hI with
      commutes' := by
        intro c
        apply _root_.funext
        intro α
        change (Ideal.quotientInfRingEquivPiQuotient I hI)
          (Ideal.Quotient.mk (⨅ α, I α) (Polynomial.C c)) α =
            Ideal.Quotient.mk (I α) (Polynomial.C c)
        exact Ideal.quotientInfToPiQuotient_mk' I (Polynomial.C c) α }
  exact E₁.trans E₂

private theorem localCRTPrimaryEquiv_root (g : Polynomial ℂ) (hg : g.Monic)
    (α : LocalRootIndex g) :
    localCRTPrimaryEquiv g hg (AdjoinRoot.root g) α =
      AdjoinRoot.root (localPrimaryFactor α.val (localRootMultiplicity g α)) := by
  rfl

/-- Exact complex-algebra CRT, retaining every repeated root multiplicity. -/
def localCRTEquiv (g : Polynomial ℂ) (hg : g.Monic) :
    AdjoinRoot g ≃ₐ[ℂ]
      (∀ α : LocalRootIndex g, LocalTruncated (localRootMultiplicity g α)) :=
  (localCRTPrimaryEquiv g hg).trans
    (AlgEquiv.piCongrRight (fun α : LocalRootIndex g =>
      localShiftEquiv α.val (localRootMultiplicity g α)))

/-- The quotient root maps to `α+z` in the exact `α` component. -/
theorem localCRTEquiv_root (g : Polynomial ℂ) (hg : g.Monic)
    (α : LocalRootIndex g) :
    localCRTEquiv g hg (AdjoinRoot.root g) α =
      algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
        localRoot (localRootMultiplicity g α) := by
  change localShiftEquiv α.val (localRootMultiplicity g α)
    (localCRTPrimaryEquiv g hg (AdjoinRoot.root g) α) = _
  rw [localCRTPrimaryEquiv_root, localShiftEquiv_root]

/-- Every quotient-root power has the corresponding exact local power. -/
theorem localCRTEquiv_root_pow (g : Polynomial ℂ) (hg : g.Monic)
    (j : ℕ) (α : LocalRootIndex g) :
    localCRTEquiv g hg ((AdjoinRoot.root g) ^ j) α =
      (algebraMap ℂ (LocalTruncated (localRootMultiplicity g α)) α.val +
        localRoot (localRootMultiplicity g α)) ^ j := by
  rw [map_pow, Pi.pow_apply, localCRTEquiv_root]

/-- The CRT map preserves every finite product componentwise. -/
theorem localCRTEquiv_prod (g : Polynomial ℂ) (hg : g.Monic)
    {ι : Type*} (s : Finset ι) (x : ι → AdjoinRoot g)
    (α : LocalRootIndex g) :
    localCRTEquiv g hg (∏ i ∈ s, x i) α =
      ∏ i ∈ s, localCRTEquiv g hg (x i) α := by
  simp only [map_prod, Finset.prod_apply]

#assert_trust kernel localCRTEquiv
#assert_trust kernel localCRTEquiv_root
#assert_trust kernel localCRTEquiv_root_pow
#assert_trust kernel localCRTEquiv_prod
#print axioms localCRTEquiv_root

end
end NLA.Proofs.TR14
