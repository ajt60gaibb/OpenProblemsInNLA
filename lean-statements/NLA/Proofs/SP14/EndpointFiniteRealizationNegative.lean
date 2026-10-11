import NLA.Proofs.SP14.EndpointFiniteRealizationPositive
import NLA.Proofs.SP14.EndpointNegativeOperator

/-!
The actual negative Fourier coefficients of the finite endpoint extension.
This is the second coefficient identity in the independently approved finite
realization contract. Pointwise equality of circle functions is a later gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem FourierCoefficient_finset_sum_neg
    {ι : Type*} (s : Finset ι) (f : ι → Circle → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (p : ℤ) :
    FourierCoefficient (fun z => ∑ i ∈ s, f i z) p =
      ∑ i ∈ s, FourierCoefficient (f i) p := by
  unfold FourierCoefficient
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
  · intro i hi
    have hc : Continuous (fun t : ℝ =>
        f i (Circle.exp t) * Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))) := by
      have hfi := hf i hi
      fun_prop
    exact hc.intervalIntegrable 0 (2 * Real.pi)

private theorem FourierCoefficient_const_mul_neg
    (c : ℂ) (f : Circle → ℂ) (p : ℤ) :
    FourierCoefficient (fun z => c * f z) p =
      c * FourierCoefficient f p := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem continuous_endpointInverseMonomial_neg (k : ℕ) :
    Continuous (endpointInverseMonomial k) := by
  unfold endpointInverseMonomial
  apply continuous_finsetSum
  intro l hl
  fun_prop

private theorem endpointFiniteInverse_fourier_neg_sum
    (r : ℝ) (y : SobolevCoeff r) (N t : ℕ) :
    FourierCoefficient
      (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
      (-((t + 1 : ℕ) : ℤ)) =
      ∑ k ∈ Finset.range N,
        physicalCoeff r y k *
          FourierCoefficient
            (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
            (-((t + 1 : ℕ) : ℤ)) := by
  have hfun :
      (fun z : Circle => endpointBaseSymbol z * endpointFiniteInverse r y N z) =
      (fun z : Circle => ∑ k ∈ Finset.range N,
        physicalCoeff r y k *
          (endpointBaseSymbol z * endpointInverseMonomial k z)) := by
    funext z
    simp only [endpointFiniteInverse, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfun, FourierCoefficient_finset_sum_neg]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [FourierCoefficient_const_mul_neg]
  · intro k hk
    exact continuous_const.mul
      (continuous_endpointBaseSymbol.mul (continuous_endpointInverseMonomial_neg k))

/-- The finite canonical extension has the negative physical coefficients of
the actual frozen Fourier-row operator, including the first negative mode. -/
theorem endpointFiniteInverse_fourier_neg
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (N : ℕ)
    (hy : ∀ k : ℕ, N ≤ k → y k = 0) (t : ℕ) :
    FourierCoefficient
      (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
      (-((t + 1 : ℕ) : ℤ)) =
      physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t := by
  have hr : 0 < r := by linarith
  have htsum :
      (∑' k : ℕ, endpointFiniteFourierEntry r t k * y k) =
        ∑ k ∈ Finset.range N, endpointFiniteFourierEntry r t k * y k := by
    apply tsum_eq_sum (s := Finset.range N)
    intro k hk
    have hkN : N ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    simp [hy k hkN]
  have hpow :
      (((t + 1 : ℕ) : ℝ) ^ (-r)) * (((t + 1 : ℕ) : ℝ) ^ r) = 1 := by
    rw [← Real.rpow_add (by positivity : 0 < ((t + 1 : ℕ) : ℝ))]
    simp
  calc
    FourierCoefficient
        (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
        (-((t + 1 : ℕ) : ℤ)) =
        ∑ k ∈ Finset.range N,
          physicalCoeff r y k *
            FourierCoefficient
              (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
              (-((t + 1 : ℕ) : ℤ)) :=
      endpointFiniteInverse_fourier_neg_sum r y N t
    _ = ∑ k ∈ Finset.range N,
          (Complex.ofReal (((t + 1 : ℕ) : ℝ) ^ (-r))) *
            (endpointFiniteFourierEntry r t k * y k) := by
      apply Finset.sum_congr rfl
      intro k hk
      unfold endpointFiniteFourierEntry physicalCoeff
      simp only [Complex.ofReal_mul]
      let T : ℂ := Complex.ofReal (((t + 1 : ℕ) : ℝ) ^ (-r))
      let S : ℂ := Complex.ofReal (((t + 1 : ℕ) : ℝ) ^ r)
      let K : ℂ := Complex.ofReal (((k + 1 : ℕ) : ℝ) ^ (-r))
      let F : ℂ := FourierCoefficient
        (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
        (-((t + 1 : ℕ) : ℤ))
      have hTS : T * S = 1 := by
        dsimp [T, S]
        rw [← Complex.ofReal_mul, hpow]
        simp
      change K * y k * F = T * ((S * K) * F * y k)
      calc
        K * y k * F = (T * S) * (K * y k * F) := by rw [hTS]; ring
        _ = T * ((S * K) * F * y k) := by ring
    _ = Complex.ofReal (((t + 1 : ℕ) : ℝ) ^ (-r)) *
          (∑ k ∈ Finset.range N, endpointFiniteFourierEntry r t k * y k) := by
      rw [Finset.mul_sum]
    _ = physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t := by
      unfold physicalCoeff
      rw [endpointNegativeOperator_apply, htsum]

#assert_trust kernel endpointFiniteInverse_fourier_neg
#print axioms endpointFiniteInverse_fourier_neg

end NLA.Proofs.SP14
