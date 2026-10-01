import ProofProject.SourceWindowPhaseBounds

/-!
# Pointwise normalization of the source frequency gap

The actual phase derivative is expressed directly in the real parameter
`v = -2πξ sqrt(N)`. This allows finite-sum estimates to use pointwise reciprocal
square-root separation without identifying a distance between transformed sets.
-/

noncomputable section
open Set
namespace ProofProject

/-- Multiplying the center scale by `n sqrt(n)` leaves `sqrt(N)`. -/
theorem sourceWindowScale_mul_center {N : ℝ} (hN : 0 < N) (j : ℕ) :
    sourceWindowScale N j * (((j : ℝ) + 2) * Real.sqrt ((j : ℝ) + 2)) =
      Real.sqrt N := by
  have hn : 0 < (j : ℝ) + 2 := by positivity
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsn : 0 < Real.sqrt ((j : ℝ) + 2) := Real.sqrt_pos.mpr hn
  have hN2 := Real.sq_sqrt hN.le
  have hn2 := Real.sq_sqrt hn.le
  unfold sourceWindowScale
  rw [Real.sqrt_mul hN.le]
  apply (div_mul_eq_mul_div ..).trans ?_
  apply (div_eq_iff (by positivity : (Real.sqrt N * Real.sqrt ((j : ℝ) + 2)) ^ 3 ≠ 0)).mpr
  calc
    _ = (Real.sqrt N ^ 2) ^ 2 *
        ((Real.sqrt ((j : ℝ) + 2) ^ 2) * Real.sqrt ((j : ℝ) + 2)) := by rw [hN2, hn2]
    _ = _ := by ring

/-- The exact derivative normalization, including the `2π` frequency change. -/
theorem abs_sourceOscillatoryPhaseDeriv_normalized {N w ξ : ℝ} (hN : 0 < N)
    (j : ℕ) (hw : w ∈ Icc (1 / 2 : ℝ) (7 / 2)) :
    |sourceOscillatoryPhaseDeriv N j ξ w| =
      sourceWindowScale N j * (((j : ℝ) + 2) * Real.sqrt ((j : ℝ) + 2) *
        |-2 * Real.pi * ξ * Real.sqrt N - 1 / Real.sqrt ((j : ℝ) + w)|) := by
  have ht : 0 < (j : ℝ) + w := by
    have := Nat.cast_nonneg (α := ℝ) j
    linarith [hw.1]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hst : 0 < Real.sqrt ((j : ℝ) + w) := Real.sqrt_pos.mpr ht
  have hN2 := Real.sq_sqrt hN.le
  have hquot : N / (Real.sqrt N * Real.sqrt ((j : ℝ) + w)) =
      Real.sqrt N / Real.sqrt ((j : ℝ) + w) := by
    apply (div_eq_div_iff (mul_ne_zero hsN.ne' hst.ne') hst.ne').mpr
    nlinarith
  have hphase : sourceOscillatoryPhaseDeriv N j ξ w = Real.sqrt N *
      (1 / Real.sqrt ((j : ℝ) + w) - (-2 * Real.pi * ξ * Real.sqrt N)) := by
    unfold sourceOscillatoryPhaseDeriv
    rw [Real.sqrt_mul hN.le, hquot]
    rw [show 2 * Real.pi * N * ξ = 2 * Real.pi * Real.sqrt N ^ 2 * ξ by rw [hN2]]
    ring
  rw [hphase, abs_mul, abs_of_pos hsN, abs_sub_comm]
  rw [← mul_assoc, sourceWindowScale_mul_center hN j]

end ProofProject
