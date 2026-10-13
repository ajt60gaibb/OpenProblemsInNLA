import NLA.Proofs.SP14.EndpointFiniteRealizationPositive
import NLA.Proofs.SP14.BaseFourierMode

/-!
The actual normalized Fourier coefficients of the finite triangular inverse
polynomial. This is the first independently reviewed stage of its L² bound.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- The coefficient of the finite triangular inverse at analytic degree `d`.
The source's inverse index is `k-d`, and the sum is empty for `d ≥ N`. -/
noncomputable def endpointFiniteInverseCoeff (r : ℝ)
    (y : SobolevCoeff r) (N d : ℕ) : ℂ :=
  ∑ k ∈ Finset.Ico d N,
    (baseInverseCoeff (k - d) : ℂ) * physicalCoeff r y k

private theorem FourierCoefficient_add_continuous_inv
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

private theorem FourierCoefficient_const_mul_inv
    (c : ℂ) (a : Circle → ℂ) (p : ℤ) :
    FourierCoefficient (fun z => c * a z) p =
      c * FourierCoefficient a p := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_finset_sum_inv
    {ι : Type} (s : Finset ι) (f : ι → Circle → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (p : ℤ) :
    FourierCoefficient (fun z => ∑ i ∈ s, f i z) p =
      ∑ i ∈ s, FourierCoefficient (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FourierCoefficient]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [FourierCoefficient_add_continuous_inv]
      · rw [ih]
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      · exact hf i (Finset.mem_insert_self _ _)
      · exact continuous_finsetSum _ (fun j hj =>
          hf j (Finset.mem_insert_of_mem hj))

private theorem endpointFiniteInverse_fourier_sum
    (r : ℝ) (y : SobolevCoeff r) (N : ℕ) (p : ℤ) :
    FourierCoefficient (endpointFiniteInverse r y N) p =
      ∑ k ∈ Finset.range N, physicalCoeff r y k *
        ∑ l ∈ Finset.range (k + 1),
          (baseInverseCoeff l : ℂ) *
            (if ((k - l : ℕ) : ℤ) = p then 1 else 0) := by
  unfold endpointFiniteInverse endpointInverseMonomial
  rw [FourierCoefficient_finset_sum_inv]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [FourierCoefficient_const_mul_inv, FourierCoefficient_finset_sum_inv]
    · congr 1
      apply Finset.sum_congr rfl
      intro l hl
      rw [FourierCoefficient_const_mul_inv]
      exact congrArg ((baseInverseCoeff l : ℂ) * ·)
        (FourierCoefficient_circle_mode ((k - l : ℕ) : ℤ) p)
    · intro l hl
      exact continuous_const.mul (continuous_subtype_val.pow (k - l))
  · intro k hk
    exact continuous_const.mul (continuous_finsetSum _ fun l hl =>
      continuous_const.mul (continuous_subtype_val.pow (k - l)))

private theorem endpointInverse_inner_nonneg (k d : ℕ) :
    (∑ l ∈ Finset.range (k + 1),
      (baseInverseCoeff l : ℂ) *
        (if ((k - l : ℕ) : ℤ) = (d : ℤ) then 1 else 0)) =
      if d ≤ k then (baseInverseCoeff (k - d) : ℂ) else 0 := by
  by_cases hdk : d ≤ k
  · rw [if_pos hdk, Finset.sum_eq_single (k - d)]
    · have hsub : k - (k - d) = d := by omega
      simp [hsub]
    · intro l hl hne
      have hneq : ((k - l : ℕ) : ℤ) ≠ (d : ℤ) := by
        have hlk : l ≤ k := by
          have := Finset.mem_range.mp hl
          omega
        have : k - l ≠ d := by omega
        exact_mod_cast this
      simp [hneq]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hdk]
    apply Finset.sum_eq_zero
    intro l hl
    have hneq : ((k - l : ℕ) : ℤ) ≠ (d : ℤ) := by
      have : k - l ≠ d := by omega
      exact_mod_cast this
    simp [hneq]

private theorem endpointInverse_inner_neg (k t : ℕ) :
    (∑ l ∈ Finset.range (k + 1),
      (baseInverseCoeff l : ℂ) *
        (if ((k - l : ℕ) : ℤ) = -((t + 1 : ℕ) : ℤ) then 1 else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  have hneq : ((k - l : ℕ) : ℤ) ≠ -((t + 1 : ℕ) : ℤ) := by omega
  simp only [if_neg hneq, mul_zero]

/-- Exact nonnegative coefficient of the finite inverse polynomial under
the original `1/(2π)` normalized interval Fourier integral. -/
theorem endpointFiniteInverse_coeff (r : ℝ) (y : SobolevCoeff r)
    (N d : ℕ) :
    FourierCoefficient (endpointFiniteInverse r y N) (d : ℤ) =
      endpointFiniteInverseCoeff r y N d := by
  rw [endpointFiniteInverse_fourier_sum]
  simp_rw [endpointInverse_inner_nonneg]
  simp only [mul_ite, mul_zero]
  change (∑ k ∈ Finset.range N,
      if d ≤ k then physicalCoeff r y k * (baseInverseCoeff (k - d) : ℂ)
      else 0) =
    ∑ k ∈ Finset.Ico d N,
      (baseInverseCoeff (k - d) : ℂ) * physicalCoeff r y k
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range N).filter (fun k => d ≤ k) = Finset.Ico d N := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter]
  exact Finset.sum_congr rfl (fun k hk => mul_comm _ _)

/-- The finite triangular inverse has no strictly negative Fourier modes. -/
theorem endpointFiniteInversePolynomial_fourier_neg (r : ℝ)
    (y : SobolevCoeff r) (N t : ℕ) :
    FourierCoefficient (endpointFiniteInverse r y N)
      (-((t + 1 : ℕ) : ℤ)) = 0 := by
  rw [endpointFiniteInverse_fourier_sum]
  simp_rw [endpointInverse_inner_neg]
  simp

#assert_trust kernel endpointFiniteInverse_coeff
#assert_trust kernel endpointFiniteInversePolynomial_fourier_neg
#print axioms endpointFiniteInversePolynomial_fourier_neg

end NLA.Proofs.SP14
