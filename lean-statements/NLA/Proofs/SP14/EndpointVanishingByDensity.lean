import NLA.Proofs.SP14.EndpointVanishingBasics
import NLA.Proofs.SP14.EndpointCirclePointwiseBound
import NLA.Proofs.SP14.EndpointFiniteRealizationPointwise

/-!
The actual continuous endpoint realization vanishes at the base-symbol zero
for every weighted input. Finite inverse polynomials are used only before
passing to the input-norm limit.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The actual two-sided endpoint extension vanishes at `-1` for every
weighted input in the reviewed `1/2 < r < 1` range. -/
theorem endpointCircleRealization_neg_one_zero (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    endpointCircleRealization r hrHalf hr1 y (-1 : Circle) = 0 := by
  let C := ‖endpointCircleWeightLp r hrHalf‖ *
    (1 + endpointSchurConstant r)
  have hfinite (N : ℕ) :
      endpointCircleRealization r hrHalf hr1
        (sobolevTruncation r N y) (-1 : Circle) = 0 := by
    have hsupport : ∀ k : ℕ, N ≤ k → sobolevTruncation r N y k = 0 := by
      intro k hk
      rw [sobolevTruncation_apply]
      simp [not_lt.mpr hk]
    rw [endpointCircleRealization_eq_finiteInverse r hrHalf hr1
      (sobolevTruncation r N y) N hsupport (-1 : Circle),
      endpointBaseSymbol_neg_one, zero_mul]
  have hsub : Filter.Tendsto
      (fun N : ℕ => y - sobolevTruncation r N y)
      Filter.atTop (nhds (0 : SobolevCoeff r)) := by
    convert (tendsto_const_nhds.sub (sobolevTruncation_tendsto r y)) using 1
    simp
  have hnorm : Filter.Tendsto
      (fun N : ℕ => ‖y - sobolevTruncation r N y‖)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hsub.norm
  have hupper : Filter.Tendsto
      (fun N : ℕ => C * ‖y - sobolevTruncation r N y‖)
      Filter.atTop (nhds (0 : ℝ)) := by
    convert tendsto_const_nhds.mul hnorm using 1
    simp [C]
  have hle (N : ℕ) :
      ‖endpointCircleRealization r hrHalf hr1 y (-1 : Circle)‖ ≤
        C * ‖y - sobolevTruncation r N y‖ := by
    simpa only [hfinite N, sub_zero, C] using
      (endpointCircleRealization_pointwise_sub_norm_le r hrHalf hr1
        y (sobolevTruncation r N y) (-1 : Circle))
  have hzero : ‖endpointCircleRealization r hrHalf hr1 y (-1 : Circle)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hupper
      (Filter.Eventually.of_forall hle)
  exact norm_le_zero_iff.mp hzero

#assert_trust kernel endpointCircleRealization_neg_one_zero
#print axioms endpointCircleRealization_neg_one_zero

end NLA.Proofs.SP14
