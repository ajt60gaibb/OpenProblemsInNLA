import NLA.Proofs.TR14.LocalCRTFourierCount

/-!
Reindex the exact dependent CRT/Fourier node identity into the frozen
`SymmetricWidth` predicate. This gives one normalized-chart upper bound,
not the full TR-14 all-width equality or original projective-root count.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open NLA.Statements.TR14 Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- An actual equivalence with `Fin` turns the dependent-node coordinate
identity into the frozen symmetric decomposition witness. -/
theorem localCRTFourier_symmetricWidth_of_sigma {m n : ℕ}
    (h : Fin (m * (n - 1) + 1) → ℂ) (g : Polynomial ℂ)
    (w : ∀ α : LocalRootIndex g,
      LocalTruncated (localRootMultiplicity g α))
    (ζ : LocalRootIndex g → ℂ)
    (hSigma : ∀ i : Fin m → Fin n,
      Hankel h i = ∑ node : LocalCRTFourierNode m g,
        localCRTFourierCoefficient m g ζ node *
          ∏ k : Fin m, localCRTFourierVector m n g w ζ node (i k)) :
    SymmetricWidth (Hankel h)
      (Fintype.card (LocalCRTFourierNode m g)) := by
  classical
  let e : Fin (Fintype.card (LocalCRTFourierNode m g)) ≃
      LocalCRTFourierNode m g :=
    (Fintype.equivFin (LocalCRTFourierNode m g)).symm
  refine ⟨fun j => localCRTFourierCoefficient m g ζ (e j),
    fun j => localCRTFourierVector m n g w ζ (e j), ?_⟩
  intro i
  calc
    Hankel h i = ∑ node : LocalCRTFourierNode m g,
        localCRTFourierCoefficient m g ζ node *
          ∏ k : Fin m, localCRTFourierVector m n g w ζ node (i k) := hSigma i
    _ = ∑ j : Fin (Fintype.card (LocalCRTFourierNode m g)),
        localCRTFourierCoefficient m g ζ (e j) *
          ∏ k : Fin m, localCRTFourierVector m n g w ζ (e j) (i k) :=
            (Equiv.sum_comp e (fun node : LocalCRTFourierNode m g =>
              localCRTFourierCoefficient m g ζ node *
                ∏ k : Fin m, localCRTFourierVector m n g w ζ node (i k))).symm

/-- Exact normalized-chart symmetric upper bound from a nonzero monic
least-apolar form, with every root multiplicity retained. -/
theorem localCRTFourier_symmetricWidth_of_minimal {m n : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) (hh : h ≠ 0)
    (g : Polynomial ℂ) (hg : g.Monic) (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ m * (n - 1))
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ m * (n - 1), d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    SymmetricWidth (Hankel h)
      ((m - 1) * g.natDegree -
        (m - 2) * (localRootSupport g).card) := by
  obtain ⟨w, ζ, _, _, hSigma⟩ :=
    localCRT_fourier_sigma_of_minimal hm hn h hh g hg hrPos hrD hAp hmin
  have hWidth := localCRTFourier_symmetricWidth_of_sigma h g w ζ hSigma
  rwa [localCRTFourierNode_card_formula m hm g] at hWidth

#assert_trust kernel localCRTFourier_symmetricWidth_of_sigma
#assert_trust kernel localCRTFourier_symmetricWidth_of_minimal
#print axioms localCRTFourier_symmetricWidth_of_minimal

end
end NLA.Proofs.TR14
