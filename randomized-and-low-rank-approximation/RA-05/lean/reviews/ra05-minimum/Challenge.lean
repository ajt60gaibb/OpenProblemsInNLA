import NLA.Statements.RA05

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
