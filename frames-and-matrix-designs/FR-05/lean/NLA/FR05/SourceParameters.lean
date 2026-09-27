/-
The numerical parameters used in Section 3.4 of the frozen source manuscript.
Keeping these as definitions (rather than informal comments) makes the
dimension match between the chart and its square Jacobian explicit.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- The row count `N = 4M - 5` in Proposition 3.1. -/
def sourceRowCount (M : ℕ) : ℕ := 4 * M - 5

/-- The tail dimension after fixing the two planted coordinates. -/
def sourceTailDimension (M : ℕ) : ℕ := M - 2

/-- The fixed mixture parameter in the planted radial density. -/
def sourceEta : ℝ := 1 / 100

/-- The hard lower radial cutoff `δ = M⁻²`. -/
def sourceDelta (M : ℕ) : ℝ := ((M : ℝ) ^ 2)⁻¹

/-- The planted imbalance width `ε = M⁻⁵⁰`. -/
def sourceEpsilon (M : ℕ) : ℝ := ((M : ℝ) ^ 50)⁻¹

/-- The least-singular-value cutoff `κ = M⁻¹²`. -/
def sourceKappa (M : ℕ) : ℝ := ((M : ℝ) ^ 12)⁻¹

/-- The polynomial chart has exactly as many real parameters as source rows:
one scalar, one complex coordinate, and two complex tail vectors. -/
theorem source_chart_real_parameter_count (M : ℕ) (hM : 2 ≤ M) :
    1 + 2 + 2 * sourceTailDimension M + 2 * sourceTailDimension M =
      sourceRowCount M := by
  unfold sourceTailDimension sourceRowCount
  lia

theorem sourceEta_pos : 0 < sourceEta := by
  norm_num [sourceEta]

theorem sourceEta_lt_one : sourceEta < 1 := by
  norm_num [sourceEta]

theorem sourceDelta_pos (M : ℕ) (hM : 1 ≤ M) : 0 < sourceDelta M := by
  unfold sourceDelta
  have hMreal : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hM
  positivity

theorem sourceEpsilon_pos (M : ℕ) (hM : 1 ≤ M) : 0 < sourceEpsilon M := by
  unfold sourceEpsilon
  have hMreal : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hM
  positivity

theorem sourceKappa_pos (M : ℕ) (hM : 1 ≤ M) : 0 < sourceKappa M := by
  unfold sourceKappa
  have hMreal : 0 < (M : ℝ) := by
    exact_mod_cast Nat.zero_lt_of_lt hM
  positivity

end NLA.FR05
