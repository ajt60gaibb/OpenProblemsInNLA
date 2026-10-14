import NLA.Proofs.SP14.EndpointNegativeOutputEnergy

/-!
The actual negative-frequency part of the canonical square-root extension as
a bounded complex operator on the literal weighted coefficient space.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem summable_endpointNegativeOutput_norm_sq (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    Summable (fun t : ℕ => ‖endpointNegativeOutputCoeff r hr hr1 y t‖ ^ 2) := by
  apply summable_of_sum_range_le (fun t => sq_nonneg _)
  intro J
  calc
    (∑ t ∈ Finset.range J, ‖endpointNegativeOutputCoeff r hr hr1 y t‖ ^ 2) =
        ∑ t : Fin J, ‖endpointNegativeOutputCoeff r hr hr1 y t.val‖ ^ 2 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.mem_range.mp ht]
    _ ≤ endpointSchurConstant r ^ 2 * ‖y‖ ^ 2 :=
      endpointNegativeOutput_square_prefix_le r hr hr1 y J

/-- The actual negative Fourier output, in weighted `lp 2` coordinates. -/
noncomputable def endpointNegativeOutput (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) : SobolevCoeff r :=
  ⟨fun t : ℕ => endpointNegativeOutputCoeff r hr hr1 y t, by
    apply memℓp_gen
    simpa using summable_endpointNegativeOutput_norm_sq r hr hr1 y⟩

theorem endpointNegativeOutput_apply (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) (t : ℕ) :
    endpointNegativeOutput r hr hr1 y t =
      ∑' k : ℕ, endpointFiniteFourierEntry r t k * y k := rfl

private theorem endpointNegativeOutput_norm_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) :
    ‖endpointNegativeOutput r hr hr1 y‖ ≤
      endpointSchurConstant r * ‖y‖ := by
  have hC : 0 ≤ endpointSchurConstant r := by
    unfold endpointSchurConstant
    have : 0 < 1 - r := by linarith
    positivity
  have hnorm : ‖endpointNegativeOutput r hr hr1 y‖ ^ 2 =
      ∑' t : ℕ, ‖endpointNegativeOutputCoeff r hr hr1 y t‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal)
      (endpointNegativeOutput r hr hr1 y)
    calc
      _ = ‖endpointNegativeOutput r hr hr1 y‖ ^ (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = ∑' t : ℕ, ‖endpointNegativeOutputCoeff r hr hr1 y t‖ ^ 2 := by
        simpa [endpointNegativeOutput] using h
  have hsum : (∑' t : ℕ,
      ‖endpointNegativeOutputCoeff r hr hr1 y t‖ ^ 2) ≤
      endpointSchurConstant r ^ 2 * ‖y‖ ^ 2 := by
    apply Real.tsum_le_of_sum_range_le (fun t => sq_nonneg _)
    intro J
    calc
      (∑ t ∈ Finset.range J,
          ‖endpointNegativeOutputCoeff r hr hr1 y t‖ ^ 2) =
          ∑ t : Fin J,
            ‖endpointNegativeOutputCoeff r hr hr1 y t.val‖ ^ 2 := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro t ht
        simp [Finset.mem_range.mp ht]
      _ ≤ _ := endpointNegativeOutput_square_prefix_le r hr hr1 y J
  have hsq : ‖endpointNegativeOutput r hr hr1 y‖ ^ 2 ≤
      (endpointSchurConstant r * ‖y‖) ^ 2 := by
    rw [hnorm]
    nlinarith [hsum]
  nlinarith [norm_nonneg (endpointNegativeOutput r hr hr1 y),
    mul_nonneg hC (norm_nonneg y)]

private noncomputable def endpointNegativeLinear (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) : SobolevCoeff r →ₗ[ℂ] SobolevCoeff r where
  toFun := endpointNegativeOutput r hr hr1
  map_add' y z := by
    ext t
    change (∑' k : ℕ, endpointFiniteFourierEntry r t k * (y + z) k) =
      (∑' k : ℕ, endpointFiniteFourierEntry r t k * y k) +
        (∑' k : ℕ, endpointFiniteFourierEntry r t k * z k)
    simp_rw [lp.coeFn_add, Pi.add_apply, mul_add]
    exact (summable_endpointFiniteFourierEntry_mul r hr hr1 y t).tsum_add
      (summable_endpointFiniteFourierEntry_mul r hr hr1 z t)
  map_smul' c y := by
    ext t
    change (∑' k : ℕ, endpointFiniteFourierEntry r t k * (c • y) k) =
      c • (∑' k : ℕ, endpointFiniteFourierEntry r t k * y k)
    simp_rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    have hs := (summable_endpointFiniteFourierEntry_mul r hr hr1 y t).tsum_mul_left c
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hs

/-- The unconditional actual negative Fourier operator. -/
noncomputable def endpointNegativeOperator (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) : SobolevCoeff r →L[ℂ] SobolevCoeff r :=
  (endpointNegativeLinear r hr hr1).mkContinuous
    (endpointSchurConstant r)
    (endpointNegativeOutput_norm_le r hr hr1)

theorem endpointNegativeOperator_apply (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) (y : SobolevCoeff r) (t : ℕ) :
    endpointNegativeOperator r hr hr1 y t =
      ∑' k : ℕ, endpointFiniteFourierEntry r t k * y k := rfl

theorem endpointNegativeOperator_norm_le (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1) :
    ‖endpointNegativeOperator r hr hr1‖ ≤ endpointSchurConstant r := by
  have hC : 0 ≤ endpointSchurConstant r := by
    unfold endpointSchurConstant
    have : 0 < 1 - r := by linarith
    positivity
  exact LinearMap.mkContinuous_norm_le _ hC (endpointNegativeOutput_norm_le r hr hr1)

#assert_trust kernel endpointNegativeOperator_apply
#assert_trust kernel endpointNegativeOperator_norm_le
#print axioms endpointNegativeOperator_norm_le

end NLA.Proofs.SP14
