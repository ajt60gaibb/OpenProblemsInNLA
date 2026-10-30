import NLA.Proofs.RE06.WidthBounds

/-! The public uniform worst-case bound for every stream of prechosen queries.
No event, matrix input, probability estimate or success assumption is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RE06
open NLA.Computation.NonadaptiveMatrixQuery

theorem query_bound (n m : ℕ) (hn : 0 < n) (ε : ℝ) (hε0 : 0 < ε) (hεh : ε < 1 / 2) :
    NLA.Computation.NonadaptiveMatrixQuery.QueryBound n m ε 4000000 0 := by
  intro ω
  simp only [pow_zero, mul_one]
  rw [Counts.makePlan_query_count]
  have hmin : ((min n (firstWidth m ε + secondWidth m ε + thirdWidth m ε) : ℕ) : ℝ) ≤
      (firstWidth m ε + secondWidth m ε + thirdWidth m ε : ℕ) := by
    exact_mod_cast Nat.min_le_right n (firstWidth m ε + secondWidth m ε + thirdWidth m ε)
  have hs := Counts.total_width_bound m ε hε0 hεh
  have hr := Counts.rootWidth_le_three_sqrt_log m
  have hid : 67437 * (3 * Real.sqrt (Real.log (2 * (m + 2 : ℕ)))) / (ε / 4) ^ 2 =
      3236976 * Real.sqrt (Real.log (2 * (m + 2 : ℕ))) * ε⁻¹ ^ 2 := by
    field_simp
    <;> ring
  calc
    _ ≤ ((firstWidth m ε + secondWidth m ε + thirdWidth m ε : ℕ) : ℝ) := hmin
    _ ≤ 67437 * (rootWidth m : ℝ) / (ε / 4) ^ 2 := hs
    _ ≤ 67437 * (3 * Real.sqrt (Real.log (2 * (m + 2 : ℕ)))) / (ε / 4) ^ 2 := by
      gcongr
    _ = 3236976 * Real.sqrt (Real.log (2 * (m + 2 : ℕ))) * ε⁻¹ ^ 2 := hid
    _ ≤ 4000000 * Real.sqrt (Real.log (2 * (m + 2 : ℕ))) * ε⁻¹ ^ 2 := by
      gcongr <;> norm_num

#assert_trust kernel query_bound
#print axioms query_bound
end NLA.Proofs.RE06
