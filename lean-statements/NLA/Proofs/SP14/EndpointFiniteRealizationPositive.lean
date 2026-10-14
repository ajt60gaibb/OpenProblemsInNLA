import NLA.Proofs.SP14.EndpointExtensionPositive
import NLA.Proofs.SP14.EndpointCircleEnergyBound

/-!
The actual nonnegative Fourier coefficients of the canonical finite endpoint
extension `g₀ V_N`. Pointwise equality with the infinite circle realization
and the negative Fourier coefficients are separate gates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- The source's triangular inverse polynomial of a finitely supported
physical input. -/
noncomputable def endpointFiniteInverse
    (r : ℝ) (y : SobolevCoeff r) (N : ℕ) (z : Circle) : ℂ :=
  ∑ k ∈ Finset.range N,
    physicalCoeff r y k * endpointInverseMonomial k z

private theorem continuous_endpointInverseMonomial' (k : ℕ) :
    Continuous (endpointInverseMonomial k) := by
  unfold endpointInverseMonomial
  apply continuous_finsetSum
  intro l hl
  fun_prop

private theorem FourierCoefficient_add_continuous'
    (a b : Circle → ℂ) (ha : Continuous a) (hb : Continuous b) (p : ℤ) :
    FourierCoefficient (fun z => a z + b z) p =
      FourierCoefficient a p + FourierCoefficient b p := by
  have hca : Continuous (fun t : ℝ =>
      a (Circle.exp t) * Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcb : Continuous (fun t : ℝ =>
      b (Circle.exp t) * Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hca.intervalIntegrable 0 (2 * Real.pi))
    (hcb.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem FourierCoefficient_const_mul'
    (c : ℂ) (a : Circle → ℂ) (p : ℤ) :
    FourierCoefficient (fun z => c * a z) p =
      c * FourierCoefficient a p := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_finset_sum'
    {ι : Type} (s : Finset ι) (f : ι → Circle → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (p : ℤ) :
    FourierCoefficient (fun z => ∑ i ∈ s, f i z) p =
      ∑ i ∈ s, FourierCoefficient (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FourierCoefficient]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [FourierCoefficient_add_continuous']
      · rw [ih]
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      · exact hf i (Finset.mem_insert_self _ _)
      · exact continuous_finsetSum _ (fun j hj =>
          hf j (Finset.mem_insert_of_mem hj))

/-- The finite endpoint source has exactly the input's nonnegative physical
Fourier coefficients, including mode zero and every frequency past `N`. -/
theorem endpointFiniteInverse_fourier_nonneg
    (r : ℝ) (y : SobolevCoeff r) (N : ℕ)
    (hy : ∀ k : ℕ, N ≤ k → y k = 0) (p : ℕ) :
    FourierCoefficient
      (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
      (p : ℤ) = physicalCoeff r y p := by
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
  rw [hfun, FourierCoefficient_finset_sum']
  · simp_rw [FourierCoefficient_const_mul', endpointExtension_fourier_nonneg]
    by_cases hp : p < N
    · rw [Finset.sum_eq_single p]
      · simp
      · intro k hk hkp
        simp [Ne.symm hkp]
      · intro hpnot
        exact False.elim (hpnot (Finset.mem_range.mpr hp))
    · have hzero : ∀ k ∈ Finset.range N,
          physicalCoeff r y k * (if p = k then 1 else 0) = 0 := by
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        have hne : p ≠ k := by omega
        simp [hne]
      rw [Finset.sum_eq_zero hzero]
      have hysupp : y p = 0 := hy p (Nat.le_of_not_gt hp)
      simp [physicalCoeff, hysupp]
  · intro k hk
    exact continuous_const.mul
      (continuous_endpointBaseSymbol.mul (continuous_endpointInverseMonomial' k))

#assert_trust kernel endpointFiniteInverse_fourier_nonneg
#print axioms endpointFiniteInverse_fourier_nonneg

end NLA.Proofs.SP14
