import NLA.Proofs.RA05.HyperplaneDefinitions

/-! Pre-proof support contract. Deliberate Comparator placeholders only;
this file is not a proof and must not be imported by the implementation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
namespace NLA.Proofs.RA05

theorem unitHyperplane_projector {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∑ j, x j ^ 2 = 1) :
    NLA.Statements.RA05.Projector (d - 1) (UnitHyperplane x) := by
  sorry

theorem rowCost_unitHyperplane {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ)
    (x : Fin d → ℝ) (hx : ∑ j, x j ^ 2 = 1) (i : Fin n) :
    NLA.Statements.RA05.RowCost A p (UnitHyperplane x) i =
      Real.rpow |NLA.Statements.RA06.RowValue A i x| p := by
  sorry

/-- Every actual strong rank-(d-1) coreset preserves all-vector lp energy.
The conclusion retains the exact same weights, exponent and accuracy. -/
theorem strongCoreset_implies_allVectorEmbedding {n d : ℕ}
    (hd : 0 < d) (A : Matrix (Fin n) (Fin d) ℝ)
    (p ε : ℝ) (hp : 0 < p) (w : Fin n → ℝ)
    (hcore : NLA.Statements.RA05.StrongCoreset A p (d - 1) ε w) :
    ∀ x : Fin d → ℝ,
      (1 - ε) * NLA.Statements.RA06.InputEnergy A p x ≤
        WeightedInputEnergy A p w x ∧
      WeightedInputEnergy A p w x ≤
        (1 + ε) * NLA.Statements.RA06.InputEnergy A p x := by
  sorry

end NLA.Proofs.RA05
