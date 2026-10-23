import NLA.Proofs.TR14.BinaryTopRemainderFrobenius

/-! The least-apolar moment functional has an invertible top-remainder
representer. This supplies the unit inverse used in the binary upper proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
noncomputable section

/-- In the normalized least-apolar quotient, the moment functional is the
top-remainder functional multiplied by a unit. The second witness is its
inverse; no squarefreeness or extra Target hypothesis is assumed. -/
theorem binaryMomentUnitInverse {D : ℕ}
    (h : Fin (D + 1) → ℂ) (hh : h ≠ 0) (g : Polynomial ℂ)
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ D, d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    ∃ b c : AdjoinRoot g, b * c = 1 ∧
      ∀ a : AdjoinRoot g,
        quotientMomentFunctional h g hg hrD a =
          binaryTopRemainder g hg (by omega) (b * a) := by
  haveI : Module.Finite ℂ (AdjoinRoot g) := hg.finite_adjoinRoot
  let τ := binaryTopRemainder g hg (by omega : 0 < g.natDegree)
  let L := quotientMomentFunctional h g hg hrD
  have hτ : ∀ a : AdjoinRoot g,
      (∀ b : AdjoinRoot g, τ (a * b) = 0) → a = 0 :=
    binaryTopRemainder_frobenius g hg (by omega)
  have hL : ∀ a : AdjoinRoot g,
      (∀ b : AdjoinRoot g, L (a * b) = 0) → a = 0 :=
    quotientMomentFunctional_frobenius h hh g hg hrPos hrD hAp hmin
  obtain ⟨b, hb, _⟩ := frobenius_representer_exists_unique τ hτ L
  have hunit : IsUnit b := frobenius_representer_isUnit τ L hL b hb
  obtain ⟨c, hbc⟩ := isUnit_iff_exists_inv.mp hunit
  exact ⟨b, c, hbc, hb⟩

#assert_trust kernel binaryMomentUnitInverse
#print axioms binaryMomentUnitInverse

end
end NLA.Proofs.TR14
