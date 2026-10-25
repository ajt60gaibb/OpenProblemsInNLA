import NLA.Statements.RA05
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-! Exact semantic lemmas for the retained RA-05 minimum/supremum definitions.
These prove neither the asymptotic classification nor its negative answer. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA05.SupportMinimum

open NLA.Statements.RA05

theorem rowCost_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (i : Fin n) :
    0 ≤ RowCost A p P i := by
  exact Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem cost_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (P : Matrix (Fin d) (Fin d) ℝ) :
    0 ≤ Cost A p P := by
  exact Finset.sum_nonneg fun i _ => rowCost_nonneg A p P i

theorem strongCoreset_one {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    StrongCoreset A p k ε (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun P _ => ?_⟩
  simp only [one_mul]
  change (1 - ε) * Cost A p P ≤ Cost A p P ∧
    Cost A p P ≤ (1 + ε) * Cost A p P
  have h := mul_nonneg hε (cost_nonneg A p P)
  constructor <;> nlinarith

theorem supportSize_one (n : ℕ) :
    SupportSize (fun _ : Fin n => (1 : ℝ)) = n := by
  simp [SupportSize]

theorem minimumSupport_le_support {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (w : Fin n → ℝ)
    (hw : StrongCoreset A p k ε w) :
    MinimumSupport A p k ε ≤ SupportSize w := by
  exact csInf_le' ⟨w, hw, le_rfl⟩

theorem minimumSupport_attained {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ w : Fin n → ℝ, StrongCoreset A p k ε w ∧
      SupportSize w = MinimumSupport A p k ε := by
  have hne : {s : ℕ | ∃ w : Fin n → ℝ,
      StrongCoreset A p k ε w ∧ SupportSize w ≤ s}.Nonempty :=
    ⟨SupportSize (fun _ => 1), fun _ => 1, strongCoreset_one A p k ε hε, le_rfl⟩
  obtain ⟨w, hw, hle⟩ := csInf_mem hne
  exact ⟨w, hw, le_antisymm hle (minimumSupport_le_support A p k ε w hw)⟩

theorem minimumSupport_le_rowCount {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (p : ℝ) (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    MinimumSupport A p k ε ≤ n := by
  simpa only [supportSize_one] using
    minimumSupport_le_support A p k ε (fun _ => 1) (strongCoreset_one A p k ε hε)

theorem minimumSupport_le_worstSupport {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (p : ℝ) (k : ℕ) (ε : ℝ)
    (hkd : k < d) :
    (MinimumSupport A p k ε : ENNReal) ≤ WorstSupport p k ε := by
  exact le_sSup ⟨n, d, hkd, A, rfl⟩

end NLA.Proofs.RA05.SupportMinimum
