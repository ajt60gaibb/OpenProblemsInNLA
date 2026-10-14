import NLA.Proofs.SP14.EndpointFiniteInverseEnergy
import NLA.Proofs.SP14.EndpointNegativeTruncation
import Mathlib.Analysis.Fourier.AddCircle

/-!
The actual finite endpoint inverse on the normalized additive circle.
Finite Parseval uses its frozen normalized Fourier coefficients; L² completion is separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

local instance endpointTwoPiPositive : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

private theorem continuous_endpointFiniteInverse_actual
    (r : ℝ) (y : SobolevCoeff r) (N : ℕ) :
    Continuous (endpointFiniteInverse r y N) := by
  unfold endpointFiniteInverse
  apply continuous_finsetSum
  intro k hk
  unfold endpointInverseMonomial
  apply continuous_const.mul
  apply continuous_finsetSum
  intro l hl
  exact continuous_const.mul (continuous_subtype_val.pow (k - l))

/-- The source's *same* finite triangular polynomial on the additive circle
of period `2π`, mapped to the unit complex circle. -/
noncomputable def endpointFiniteInverseAddCircle (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    C(AddCircle (2 * Real.pi), ℂ) :=
  ⟨fun θ => endpointFiniteInverse r y N (AddCircle.toCircle θ),
    (continuous_endpointFiniteInverse_actual r y N).comp AddCircle.continuous_toCircle⟩

/-- The finite inverse in probability-Haar `L²`, with no unnormalized volume. -/
noncomputable def endpointFiniteInverseLp (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) :=
  (endpointFiniteInverseAddCircle r y N).toLp 2
    (AddCircle.haarAddCircle (T := 2 * Real.pi)) ℂ

private theorem endpointFiniteInverse_toCircle_real (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) (t : ℝ) :
    endpointFiniteInverseAddCircle r y N (t : AddCircle (2 * Real.pi)) =
      endpointFiniteInverse r y N (Circle.exp t) := by
  unfold endpointFiniteInverseAddCircle
  change endpointFiniteInverse r y N
    (AddCircle.toCircle (t : AddCircle (2 * Real.pi))) =
      endpointFiniteInverse r y N (Circle.exp t)
  rw [AddCircle.toCircle_apply_mk]
  have hp : 2 * Real.pi / (2 * Real.pi) = (1 : ℝ) := by
    exact div_self (ne_of_gt Real.two_pi_pos)
  rw [hp, one_mul]

/-- Exact probability-Haar versus frozen real-interval normalization for
the square modulus of the finite inverse. -/
theorem endpointFiniteInverse_haar_eq_interval (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    (∫ θ : AddCircle (2 * Real.pi),
      ‖endpointFiniteInverseAddCircle r y N θ‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      ((1 / (2 * Real.pi) : ℝ) *
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          ‖endpointFiniteInverse r y N (Circle.exp t)‖ ^ 2) := by
  rw [AddCircle.integral_haarAddCircle]
  rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
  simp only [zero_add, inv_eq_one_div, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change ‖endpointFiniteInverseAddCircle r y N (t : AddCircle (2 * Real.pi))‖ ^ 2 =
    ‖endpointFiniteInverse r y N (Circle.exp t)‖ ^ 2
  rw [endpointFiniteInverse_toCircle_real]

private theorem endpointFiniteInverse_fourier_addCircle (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) (p : ℤ) :
    fourierCoeff (endpointFiniteInverseAddCircle r y N) p =
      FourierCoefficient (endpointFiniteInverse r y N) p := by
  rw [fourierCoeff_eq_intervalIntegral
    (endpointFiniteInverseAddCircle r y N) p 0]
  unfold FourierCoefficient
  simp only [zero_add, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change fourier (-p) (t : AddCircle (2 * Real.pi)) *
      endpointFiniteInverseAddCircle r y N (t : AddCircle (2 * Real.pi)) =
    endpointFiniteInverse r y N (Circle.exp t) *
      Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))
  rw [fourier_coe_apply]
  rw [endpointFiniteInverse_toCircle_real]
  have hperiod : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt Real.two_pi_pos)
  have hexp : Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I * (-(p : ℂ)) * (t : ℂ) /
        ((2 * Real.pi : ℝ) : ℂ)) =
      Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ))) := by
    congr 1
    have hcast : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
      push_cast
      ring
    rw [hcast]
    field_simp
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hexp
  push_cast
  rw [hexp]
  ring

private theorem endpointFiniteInverse_fourierLp (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) (p : ℤ) :
    fourierCoeff (endpointFiniteInverseLp r y N) p =
      FourierCoefficient (endpointFiniteInverse r y N) p := by
  unfold endpointFiniteInverseLp
  rw [fourierCoeff_toLp]
  exact endpointFiniteInverse_fourier_addCircle r y N p

private theorem endpointFiniteInverseCoeff_eq_zero_of_ge (r : ℝ)
    (y : SobolevCoeff r) (N d : ℕ) (hNd : N ≤ d) :
    endpointFiniteInverseCoeff r y N d = 0 := by
  simp [endpointFiniteInverseCoeff, Finset.Ico_eq_empty_of_le hNd]

private theorem endpointFiniteInverse_fourier_energy_eq (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    (∑' p : ℤ, ‖fourierCoeff (endpointFiniteInverseLp r y N) p‖ ^ 2) =
      ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 := by
  have hpos : Summable (fun d : ℕ =>
      ‖fourierCoeff (endpointFiniteInverseLp r y N) (d : ℤ)‖ ^ 2) := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro d hd
    rw [endpointFiniteInverse_fourierLp, endpointFiniteInverse_coeff,
      endpointFiniteInverseCoeff_eq_zero_of_ge r y N d (by
        simpa only [Finset.mem_range, not_lt] using hd)]
    simp
  have hneg : Summable (fun t : ℕ =>
      ‖fourierCoeff (endpointFiniteInverseLp r y N)
        (-((t + 1 : ℕ) : ℤ))‖ ^ 2) := by
    simp_rw [endpointFiniteInverse_fourierLp,
      endpointFiniteInversePolynomial_fourier_neg]
    simp
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  have hpossum : (∑' d : ℕ,
      ‖fourierCoeff (endpointFiniteInverseLp r y N) (d : ℤ)‖ ^ 2) =
      ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 := by
    rw [tsum_eq_sum (s := Finset.range N)]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [endpointFiniteInverse_fourierLp, endpointFiniteInverse_coeff]
    · intro d hd
      rw [endpointFiniteInverse_fourierLp, endpointFiniteInverse_coeff,
        endpointFiniteInverseCoeff_eq_zero_of_ge r y N d (by
          simpa only [Finset.mem_range, not_lt] using hd)]
      simp
  rw [hpossum]
  have hnegsum : (∑' t : ℕ,
      ‖fourierCoeff (endpointFiniteInverseLp r y N)
        (-((t + 1 : ℕ) : ℤ))‖ ^ 2) = 0 := by
    simp_rw [endpointFiniteInverse_fourierLp,
      endpointFiniteInversePolynomial_fourier_neg]
    simp
  have hnegsum' : (∑' n : ℕ,
      ‖fourierCoeff (endpointFiniteInverseLp r y N)
        (-((n : ℤ) + 1))‖ ^ 2) = 0 := by
    have heq (n : ℕ) : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    simp_rw [heq]
    exact hnegsum
  rw [hnegsum', add_zero]

/-- Parseval's identity for the actual finite triangular inverse under
the manuscript's `1/(2π)` real-interval normalization. -/
theorem endpointFiniteInverse_interval_parseval (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        ‖endpointFiniteInverse r y N (Circle.exp t)‖ ^ 2) =
      ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 := by
  rw [← endpointFiniteInverse_haar_eq_interval]
  rw [← endpointFiniteInverse_fourier_energy_eq]
  have hparseval := tsum_sq_fourierCoeff (endpointFiniteInverseLp r y N)
  rw [hparseval]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toAEEqFun
    (AddCircle.haarAddCircle (T := 2 * Real.pi))
    (endpointFiniteInverseAddCircle r y N)] with θ hθ
  change ‖(endpointFiniteInverseAddCircle r y N) θ‖ ^ 2 =
    ‖(ContinuousMap.toAEEqFun
      (AddCircle.haarAddCircle (T := 2 * Real.pi))
      (endpointFiniteInverseAddCircle r y N)) θ‖ ^ 2
  rw [hθ]

/-- The probability-Haar `L²` norm is exactly the finite inverse coefficient
energy, with no volume or Fourier-normalization factor left over. -/
theorem endpointFiniteInverseLp_norm_sq (r : ℝ)
    (y : SobolevCoeff r) (N : ℕ) :
    ‖endpointFiniteInverseLp r y N‖ ^ 2 =
      ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 := by
  let f := endpointFiniteInverseLp r y N
  have hL2 : ‖f‖ ^ 2 =
      ∫ θ : AddCircle (2 * Real.pi), ‖f θ‖ ^ 2 ∂AddCircle.haarAddCircle := by
    have h := congr_arg RCLike.re
      (@L2.inner_def (AddCircle (2 * Real.pi)) ℂ ℂ _ _ _ _ _ f f)
    rw [← integral_re] at h
    · simpa only [← norm_sq_eq_re_inner] using h
    · exact L2.integrable_inner f f
  calc
    ‖f‖ ^ 2 = ∫ θ : AddCircle (2 * Real.pi), ‖f θ‖ ^ 2
        ∂AddCircle.haarAddCircle := hL2
    _ = ∑' p : ℤ, ‖fourierCoeff f p‖ ^ 2 :=
      (tsum_sq_fourierCoeff f).symm
    _ = ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 :=
      endpointFiniteInverse_fourier_energy_eq r y N

#assert_trust kernel endpointFiniteInverse_haar_eq_interval
#print axioms endpointFiniteInverse_haar_eq_interval
#assert_trust kernel endpointFiniteInverse_interval_parseval
#print axioms endpointFiniteInverse_interval_parseval
#assert_trust kernel endpointFiniteInverseLp_norm_sq
#print axioms endpointFiniteInverseLp_norm_sq

end NLA.Proofs.SP14
