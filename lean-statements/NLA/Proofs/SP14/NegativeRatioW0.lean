import NLA.Proofs.SP14.PositiveEndpointRatio

/-!
The source's negative quotient by g₀, interpreted by its continuous endpoint
extension, has a literal W⁰ Fourier-integral bound with constant one.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem FourierCoefficient_mul_circle_mode'
    (f : Circle → ℂ) (ell k : ℤ) :
    FourierCoefficient (fun s => f s * (s : ℂ) ^ ell) k =
      FourierCoefficient f (k - ell) := by
  have hmode (t : ℝ) :
      (Circle.exp t : ℂ) ^ ell *
        Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ))) =
      Complex.exp (-(((k - ell : ℤ) : ℂ) * Complex.I * (t : ℂ))) := by
    rw [Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold FourierCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [mul_assoc] using
    congrArg (fun z : ℂ => f (Circle.exp t) * z) (hmode t)

private theorem FourierCoefficient_const_mul'
    (c : ℂ) (f : Circle → ℂ) (k : ℤ) :
    FourierCoefficient (fun s => c * f s) k = c * FourierCoefficient f k := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_finset_sum' {ι : Type*}
    (S : Finset ι) (f : ι → Circle → ℂ)
    (hf : ∀ i ∈ S, Continuous (f i)) (k : ℤ) :
    FourierCoefficient (fun s => ∑ i ∈ S, f i s) k =
      ∑ i ∈ S, FourierCoefficient (f i) k := by
  unfold FourierCoefficient
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro i hi
    have hc : Continuous (fun t : ℝ =>
        f i (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
      have hfi := hf i hi
      fun_prop
    exact hc.intervalIntegrable 0 (2 * Real.pi)

private theorem negativeRatioExtension_fourier
    (u : ℕ) (q : Fin u → ℝ) (k : ℤ) :
    FourierCoefficient (negativeRatioExtension u q) k =
      ∑ j : Fin u, (q j : ℂ) *
        FourierCoefficient baseExteriorFactor (k + (j.val : ℤ)) := by
  have hpoint : negativeRatioExtension u q =
      fun s : Circle => ∑ j : Fin u,
        (q j : ℂ) * (baseExteriorFactor s * (s : ℂ) ^ (-(j.val : ℤ))) := by
    funext s
    unfold negativeRatioExtension negativeLaurent
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
    have hpow : (s : ℂ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ)) =
        (s : ℂ) ^ (-(j.val : ℤ)) := by
      have he : (1 : ℤ) + -((j.val + 1 : ℕ) : ℤ) = -(j.val : ℤ) := by omega
      calc
        (s : ℂ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ)) =
            (s : ℂ) ^ (1 : ℤ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ)) := by simp
        _ = (s : ℂ) ^ (-(j.val : ℤ)) := by rw [← zpow_add₀ hs, he]
    rw [← hpow]
    ring
  rw [hpoint, FourierCoefficient_finset_sum']
  · apply Finset.sum_congr rfl
    intro j hj
    rw [FourierCoefficient_const_mul', FourierCoefficient_mul_circle_mode']
    simp only [sub_neg_eq_add]
  · intro j hj
    have hmode : Continuous (fun s : Circle => (s : ℂ) ^ (-(j.val : ℤ))) := by
      have hp : Continuous (fun s : Circle => (s : Circle) ^ (-(j.val : ℤ))) :=
        continuous_zpow _
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow _ _
    exact continuous_const.mul (continuous_baseExteriorFactor.mul hmode)

private noncomputable def ratioMajorant (u : ℕ) (q : Fin u → ℝ)
    (j : Fin u) (k : ℤ) : ℝ :=
  ‖(q j : ℂ)‖ * ‖FourierCoefficient baseExteriorFactor (k + (j.val : ℤ))‖

private theorem summable_ratioMajorant (u : ℕ) (q : Fin u → ℝ) (j : Fin u) :
    Summable (ratioMajorant u q j) := by
  unfold ratioMajorant
  have hshift : Summable (fun k : ℤ =>
      ‖FourierCoefficient baseExteriorFactor (k + (j.val : ℤ))‖) :=
    baseExteriorFactor_W0_summable.comp_injective
      (by intro a b hab; exact add_right_cancel hab)
  exact hshift.mul_left _

private theorem summable_ratioBound (u : ℕ) (q : Fin u → ℝ) :
    Summable (fun k : ℤ => ∑ j : Fin u, ratioMajorant u q j k) := by
  let S : Finset (Fin u) := Finset.univ
  have hs (T : Finset (Fin u)) :
      Summable (fun k : ℤ => ∑ j ∈ T, ratioMajorant u q j k) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hj ih =>
        simpa only [Finset.sum_insert hj] using
          (summable_ratioMajorant u q j).add ih
  simpa [S] using hs S

private theorem ratio_pointwise_le (u : ℕ) (q : Fin u → ℝ) (k : ℤ) :
    ‖FourierCoefficient (negativeRatioExtension u q) k‖ ≤
      ∑ j : Fin u, ratioMajorant u q j k := by
  rw [negativeRatioExtension_fourier]
  have hn : ‖∑ j : Fin u,
      (q j : ℂ) * FourierCoefficient baseExteriorFactor (k + (j.val : ℤ))‖ ≤
      ∑ j : Fin u,
        ‖(q j : ℂ) *
          FourierCoefficient baseExteriorFactor (k + (j.val : ℤ))‖ :=
    norm_sum_le _ _
  simpa [ratioMajorant, norm_mul] using hn

theorem summable_negativeRatioExtension_W0 (u : ℕ) (q : Fin u → ℝ) :
    Summable (fun k : ℤ =>
      ‖FourierCoefficient (negativeRatioExtension u q) k‖) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact norm_nonneg _
  · exact ratio_pointwise_le u q
  · exact summable_ratioBound u q

theorem negativeRatioExtension_W0_le (u : ℕ) (q : Fin u → ℝ) :
    wienerSizeAt 0 (negativeRatioExtension u q) ≤
      wienerSizeAt 0 baseExteriorFactor * (∑ j : Fin u, |q j|) := by
  have hprod := summable_negativeRatioExtension_W0 u q
  have hbound := summable_ratioBound u q
  unfold wienerSizeAt
  simp only [Real.rpow_zero, one_mul]
  calc
    (∑' k : ℤ, ‖FourierCoefficient (negativeRatioExtension u q) k‖) ≤
      ∑' k : ℤ, ∑ j : Fin u, ratioMajorant u q j k :=
      hprod.tsum_le_tsum (ratio_pointwise_le u q) hbound
    _ = (∑' k : ℤ, ‖FourierCoefficient baseExteriorFactor k‖) *
        (∑ j : Fin u, |q j|) := by
      rw [Summable.tsum_finsetSum]
      · have hshift (j : Fin u) :
            (∑' k : ℤ,
              ‖FourierCoefficient baseExteriorFactor (k + (j.val : ℤ))‖) =
              ∑' k : ℤ, ‖FourierCoefficient baseExteriorFactor k‖ := by
          simpa [Equiv.addRight] using
            (Equiv.addRight (j.val : ℤ) : ℤ ≃ ℤ).tsum_eq
              (fun x : ℤ => ‖FourierCoefficient baseExteriorFactor x‖)
        simp_rw [ratioMajorant, tsum_mul_left, hshift]
        rw [← Finset.sum_mul]
        have hsum : (∑ j : Fin u, ‖(q j : ℂ)‖) =
            ∑ j : Fin u, |q j| := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [Complex.norm_real, Real.norm_eq_abs]
        rw [hsum]
        ring
      · intro j hj
        exact summable_ratioMajorant u q j

#assert_trust kernel summable_negativeRatioExtension_W0
#assert_trust kernel negativeRatioExtension_W0_le

end NLA.Proofs.SP14
