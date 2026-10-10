import NLA.Proofs.SP14.WeightedSobolevOperators

/-!
The literal weighted coefficient truncations converge in the complete `lp 2`
carrier. This is the density step for the actual infinite negative Fourier map.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem sobolevTruncation_eq_sum_single (s : ℝ)
    (y : SobolevCoeff s) (N : ℕ) :
    sobolevTruncation s N y =
      ∑ n ∈ Finset.range N, lp.single 2 n (y n) := by
  ext n
  simp only [sobolevTruncation_apply, lp.coeFn_sum, lp.coeFn_single,
    Finset.sum_apply, Finset.sum_pi_single]
  simp [Finset.mem_range]

/-- The exact first-`N` truncations tend to the original weighted sequence. -/
theorem tendsto_sobolevTruncation (s : ℝ) (y : SobolevCoeff s) :
    Filter.Tendsto (fun N : ℕ => sobolevTruncation s N y)
      Filter.atTop (nhds y) := by
  have hsum := (lp.hasSum_single (p := 2) (E := fun _ : ℕ => ℂ)
    (by norm_num : (2 : ENNReal) ≠ ⊤) y).tendsto_sum_nat
  simpa only [sobolevTruncation_eq_sum_single] using hsum

#assert_trust kernel tendsto_sobolevTruncation
#print axioms tendsto_sobolevTruncation

end NLA.Proofs.SP14
