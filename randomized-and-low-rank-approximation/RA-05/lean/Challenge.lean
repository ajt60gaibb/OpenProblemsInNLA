import NLA.Proofs.RA05.HyperplaneDefinitions

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA05.SupportMinimum

open NLA.Statements.RA05

theorem rowCost_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin n) :
    0 ≤ RowCost A p P i := by sorry

theorem cost_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ Cost A p P := by sorry

theorem strongCoreset_one {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    StrongCoreset A p k ε (fun _ => 1) := by sorry

theorem supportSize_one (n : ℕ) :
    SupportSize (fun _ : Fin n => (1 : ℝ)) = n := by sorry

theorem minimumSupport_le_support {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (w : Fin n → ℝ)
    (hw : StrongCoreset A p k ε w) :
    MinimumSupport A p k ε ≤ SupportSize w := by sorry

theorem minimumSupport_attained {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ w : Fin n → ℝ, StrongCoreset A p k ε w ∧
      SupportSize w = MinimumSupport A p k ε := by sorry

theorem minimumSupport_le_rowCount {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    MinimumSupport A p k ε ≤ n := by sorry

theorem minimumSupport_le_worstSupport {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ) (k : ℕ) (ε : ℝ)
    (hkd : k < d) :
    (MinimumSupport A p k ε : ENNReal) ≤ WorstSupport p k ε := by sorry

end NLA.Proofs.RA05.SupportMinimum

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
