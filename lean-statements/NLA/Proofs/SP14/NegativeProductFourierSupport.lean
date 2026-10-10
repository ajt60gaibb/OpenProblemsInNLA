import NLA.Proofs.SP14.NegativeLaurentEndpointDivision
import NLA.Proofs.SP14.RegularizedBaseFactorFourier

/-!
The actual contact-corrected product `g₀ P₋` has only negative Fourier modes.
Its Fourier coefficients are the frozen normalized interval integrals.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem FourierCoefficient_mul_circle_mode
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

private theorem FourierCoefficient_const_mul
    (c : ℂ) (f : Circle → ℂ) (k : ℤ) :
    FourierCoefficient (fun s => c * f s) k = c * FourierCoefficient f k := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_finset_sum {ι : Type*}
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

theorem baseExterior_negativeLaurent_fourier_nonneg
    (u : ℕ) (p : Fin u → ℝ)
    (hcontact : negativeLaurent u p (-1 : Circle) = 0)
    (k : ℤ) (hk : 0 ≤ k) :
    FourierCoefficient
      (fun s : Circle => baseExteriorFactor s * negativeLaurent u p s) k = 0 := by
  obtain ⟨q, hqzero, hfactor⟩ := negativeLaurent_endpoint_factor u p hcontact
  have hproduct :
      (fun s : Circle => baseExteriorFactor s * negativeLaurent u p s) =
      (fun s : Circle => regularizedBaseFactor s * negativeLaurent u q s) := by
    funext s
    rw [hfactor s]
    simp [regularizedBaseFactor]
    ring
  rw [hproduct]
  have hsum :
      (fun s : Circle => regularizedBaseFactor s * negativeLaurent u q s) =
      (fun s : Circle => ∑ j : Fin u,
        (q j : ℂ) * (regularizedBaseFactor s *
          (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ)))) := by
    funext s
    simp only [negativeLaurent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  rw [FourierCoefficient_finset_sum]
  · apply Finset.sum_eq_zero
    intro j hj
    rw [FourierCoefficient_const_mul, FourierCoefficient_mul_circle_mode]
    by_cases hj0 : j.val = 0
    · have hq : q j = 0 := hqzero j hj0
      simp [hq]
    · have hfreq : 2 ≤ k - (-((j.val + 1 : ℕ) : ℤ)) := by omega
      have hne : k - (-((j.val + 1 : ℕ) : ℤ)) ≠ 1 := by omega
      have hnotnonpos : ¬ k - (-((j.val + 1 : ℕ) : ℤ)) ≤ 0 := by omega
      rw [regularizedBaseFactor_fourier]
      split_ifs with h1
      · omega
      · simp
  · intro j hj
    have hmode : Continuous
        (fun s : Circle => (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ))) := by
      have hp : Continuous
          (fun s : Circle => (s : Circle) ^ (-((j.val + 1 : ℕ) : ℤ))) :=
        continuous_zpow _
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow _ _
    exact continuous_const.mul (continuous_regularizedBaseFactor.mul hmode)

#assert_trust kernel baseExterior_negativeLaurent_fourier_nonneg

end NLA.Proofs.SP14
