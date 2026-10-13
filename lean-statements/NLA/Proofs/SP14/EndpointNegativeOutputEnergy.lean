import NLA.Proofs.SP14.EndpointNegativeRowSummable
import NLA.Proofs.SP14.WeightedSobolevPhysical

/-!
Uniform square-energy bound for finite prefixes of the actual infinite
negative Fourier output. This is the estimate needed to construct its `lp 2`
operator in the next gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The actual absolutely convergent negative Fourier row on a weighted input. -/
noncomputable def endpointNegativeOutputCoeff (r : ℝ) (_hr : 0 < r)
    (_hr1 : r < 1) (y : SobolevCoeff r) (t : ℕ) : ℂ :=
  ∑' k : ℕ, endpointFiniteFourierEntry r t k * y k

private theorem endpointNegativeOutputCoeff_partial_tendsto (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (y : SobolevCoeff r) (t : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k : Fin N,
        endpointFiniteFourierEntry r t k.val * y k.val)
      Filter.atTop (nhds (endpointNegativeOutputCoeff r hr hr1 y t)) := by
  have hsum := (summable_endpointFiniteFourierEntry_mul r hr hr1 y t).hasSum.tendsto_sum_nat
  change Filter.Tendsto _ Filter.atTop
    (nhds (∑' k : ℕ, endpointFiniteFourierEntry r t k * y k))
  convert hsum using 1
  funext N
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Finset.mem_range.mp hk]

/-- Every finite prefix of the infinite negative output obeys the exact
`C_r²` energy bound, with `J=0` included. -/
theorem endpointNegativeOutput_square_prefix_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) (J : ℕ) :
    (∑ t : Fin J, ‖endpointNegativeOutputCoeff r hr hr1 y t.val‖ ^ 2) ≤
      endpointSchurConstant r ^ 2 * ‖y‖ ^ 2 := by
  classical
  have hnorm : ‖y‖ ^ 2 = ∑' k : ℕ, ‖y k‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal) y
    calc
      ‖y‖ ^ 2 = ‖y‖ ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = ∑' k : ℕ, ‖y k‖ ^ 2 := by simpa using h
  have hs : Summable (fun k : ℕ => ‖y k‖ ^ 2) := by
    simpa using ((lp.memℓp y).summable
      (by norm_num : 0 < (2 : ENNReal).toReal))
  have hinput (N : ℕ) :
      (∑ k : Fin N, ‖y k.val‖ ^ 2) ≤ ‖y‖ ^ 2 := by
    rw [hnorm]
    calc
      _ = ∑ k ∈ Finset.range N, ‖y k‖ ^ 2 := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        simp [Finset.mem_range.mp hk]
      _ ≤ _ := hs.sum_le_tsum (Finset.range N) (fun k hk => sq_nonneg _)
  have hfinite (N : ℕ) :
      (∑ t : Fin J,
        ‖∑ k : Fin N, endpointFiniteFourierEntry r t.val k.val * y k.val‖ ^ 2) ≤
        endpointSchurConstant r ^ 2 * ‖y‖ ^ 2 := by
    calc
      _ ≤ endpointSchurConstant r ^ 2 * (∑ k : Fin N, ‖y k.val‖ ^ 2) :=
        endpointFiniteFourierMatrix_bound r hr hr1 J N (fun k => y k.val)
      _ ≤ endpointSchurConstant r ^ 2 * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (hinput N) (sq_nonneg _)
  have hlim : Filter.Tendsto
      (fun N : ℕ => ∑ t : Fin J,
        ‖∑ k : Fin N, endpointFiniteFourierEntry r t.val k.val * y k.val‖ ^ 2)
      Filter.atTop
      (nhds (∑ t : Fin J, ‖endpointNegativeOutputCoeff r hr hr1 y t.val‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro t ht
    exact (endpointNegativeOutputCoeff_partial_tendsto r hr hr1 y t.val).norm.pow 2
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hfinite)

#assert_trust kernel endpointNegativeOutput_square_prefix_le
#print axioms endpointNegativeOutput_square_prefix_le

end NLA.Proofs.SP14
