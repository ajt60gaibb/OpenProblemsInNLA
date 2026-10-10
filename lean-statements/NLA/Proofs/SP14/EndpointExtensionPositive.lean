import NLA.Proofs.SP14.EndpointExtensionKernel

/-! The actual nonnegative Fourier projection of endpoint extension monomials. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem endpointBase_fourier_neg (r : ℕ) :
    FourierCoefficient endpointBaseSymbol (-(r : ℤ)) = baseCoeff r := by
  rw [endpointBaseSymbol_fourier_tsum]
  rw [tsum_eq_single r]
  · simp
  · intro n hn
    have hne : -(n : ℤ) ≠ -(r : ℤ) := by
      intro heq
      have : n = r := by exact_mod_cast (neg_inj.mp heq)
      exact hn this
    simp [hne]

private theorem endpointBase_fourier_pos (p : ℤ) (hp : 0 < p) :
    FourierCoefficient endpointBaseSymbol p = 0 := by
  rw [endpointBaseSymbol_fourier_tsum]
  have hzero (n : ℕ) :
      baseCoeff n * (if -(n : ℤ) = p then 1 else 0) = 0 := by
    have hne : -(n : ℤ) ≠ p := by omega
    simp [hne]
  simp_rw [hzero]
  simp

private theorem FourierCoefficient_add_of_continuous
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

private theorem FourierCoefficient_const_mul
    (c : ℂ) (a : Circle → ℂ) (p : ℤ) :
    FourierCoefficient (fun z => c * a z) p =
      c * FourierCoefficient a p := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_mul_mode
    (a : Circle → ℂ) (ell p : ℤ) :
    FourierCoefficient (fun z => a z * (z : ℂ) ^ ell) p =
      FourierCoefficient a (p - ell) := by
  have hmode (t : ℝ) :
      (Circle.exp t : ℂ) ^ ell *
          Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ))) =
        Complex.exp (-(((p - ell : ℤ) : ℂ) * Complex.I * (t : ℂ))) := by
    rw [Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold FourierCoefficient
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  simpa only [Function.comp_apply, mul_assoc] using
    congrArg (fun w : ℂ => a (Circle.exp t) * w) (hmode t)

private theorem FourierCoefficient_finset_sum
    {ι : Type} (s : Finset ι) (f : ι → Circle → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) (p : ℤ) :
    FourierCoefficient (fun z => ∑ i ∈ s, f i z) p =
      ∑ i ∈ s, FourierCoefficient (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FourierCoefficient]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [FourierCoefficient_add_of_continuous]
      · rw [ih]
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      · exact hf i (Finset.mem_insert_self _ _)
      · exact continuous_finset_sum _ (fun j hj =>
          hf j (Finset.mem_insert_of_mem hj))

private theorem endpointExtension_fourier_sum (k : ℕ) (p : ℤ) :
    FourierCoefficient
      (fun z => endpointBaseSymbol z * endpointInverseMonomial k z) p =
    ∑ l ∈ Finset.range (k + 1),
      (baseInverseCoeff l : ℂ) *
        FourierCoefficient endpointBaseSymbol (p - ((k - l : ℕ) : ℤ)) := by
  have hfun : (fun z => endpointBaseSymbol z * endpointInverseMonomial k z) =
      fun z => ∑ l ∈ Finset.range (k + 1),
        (baseInverseCoeff l : ℂ) *
          (endpointBaseSymbol z * (z : ℂ) ^ (k - l)) := by
    funext z
    simp only [endpointInverseMonomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hfun, FourierCoefficient_finset_sum]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [FourierCoefficient_const_mul]
    have hmode_cast :
        (fun z : Circle => endpointBaseSymbol z * (z : ℂ) ^ (k - l)) =
          (fun z : Circle => endpointBaseSymbol z * (z : ℂ) ^ ((k - l : ℕ) : ℤ)) := by
      funext z
      simp
    rw [hmode_cast]
    rw [FourierCoefficient_mul_mode]
  · intro l hl
    have hc : Continuous (fun z : Circle => (z : ℂ) ^ (k - l)) := by fun_prop
    exact continuous_const.mul (continuous_endpointBaseSymbol.mul hc)

private theorem endpoint_convolution_rev (n : ℕ) :
    (∑ l ∈ Finset.range (n + 1),
      baseInverseCoeff l * baseCoeffReal (n - l)) =
      if n = 0 then 1 else 0 := by
  have hseries :
      PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) *
        PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) = 1 := by
    rw [← PowerSeries.binomialSeries_add]
    norm_num
  have h := congrArg (PowerSeries.coeff n) hseries
  simpa [baseCoeffReal, baseInverseCoeff, PowerSeries.coeff_mul,
    PowerSeries.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    using h

/-- The actual nonnegative Fourier projection sends the endpoint extension
of the inverse monomial to that monomial, including `k=0` and `p>k`. -/
theorem endpointExtension_fourier_nonneg (k p : ℕ) :
    FourierCoefficient
        (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
        (p : ℤ) = if p = k then 1 else 0 := by
  rw [endpointExtension_fourier_sum]
  by_cases hpk : p ≤ k
  · let n := k - p
    have hnle : n ≤ k := Nat.sub_le _ _
    have hsum :
        (∑ l ∈ Finset.range (k + 1),
          (baseInverseCoeff l : ℂ) *
            FourierCoefficient endpointBaseSymbol
              ((p : ℤ) - ((k - l : ℕ) : ℤ))) =
        ∑ l ∈ Finset.range (n + 1),
          ((baseInverseCoeff l * baseCoeffReal (n - l) : ℝ) : ℂ) := by
      calc
        _ = ∑ l ∈ Finset.range (n + 1),
            (baseInverseCoeff l : ℂ) *
              FourierCoefficient endpointBaseSymbol
                ((p : ℤ) - ((k - l : ℕ) : ℤ)) := by
          refine (Finset.sum_subset
            (Finset.range_mono (by omega : n + 1 ≤ k + 1)) ?_).symm
          intro l hl hnot
          have hnl : n < l := by simpa using hnot
          have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have hpos : (0 : ℤ) < (p : ℤ) - ((k - l : ℕ) : ℤ) := by
            dsimp [n] at hnl
            omega
          rw [endpointBase_fourier_pos _ hpos]
          simp
        _ = _ := by
          apply Finset.sum_congr rfl
          intro l hl
          have hln : l ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
          have hfreq : (p : ℤ) - ((k - l : ℕ) : ℤ) =
              -((n - l : ℕ) : ℤ) := by
            dsimp [n]
            omega
          rw [hfreq, endpointBase_fourier_neg]
          have hcast : (baseCoeffReal (n - l) : ℂ) = baseCoeff (n - l) := by
            simpa [baseCoeffReal, baseCoeff] using
              (Ring.map_choose (algebraMap ℝ ℂ) (1 / 2 : ℝ) (n - l))
          rw [← hcast]
          push_cast
          ring
    rw [hsum]
    have hc := congrArg (fun x : ℝ => (x : ℂ)) (endpoint_convolution_rev n)
    push_cast at hc
    push_cast
    rw [hc]
    have heq : n = 0 ↔ p = k := by
      dsimp [n]
      omega
    simp [heq]
    split_ifs <;> simp
  · have hzero (l : ℕ) (hl : l ∈ Finset.range (k + 1)) :
        (baseInverseCoeff l : ℂ) *
          FourierCoefficient endpointBaseSymbol
            ((p : ℤ) - ((k - l : ℕ) : ℤ)) = 0 := by
      have hpos : (0 : ℤ) < (p : ℤ) - ((k - l : ℕ) : ℤ) := by omega
      rw [endpointBase_fourier_pos _ hpos]
      simp
    have hs : (∑ l ∈ Finset.range (k + 1),
        (baseInverseCoeff l : ℂ) *
          FourierCoefficient endpointBaseSymbol
            ((p : ℤ) - ((k - l : ℕ) : ℤ))) = 0 :=
      Finset.sum_eq_zero hzero
    rw [hs]
    simp [Nat.ne_of_gt (Nat.lt_of_not_ge hpk)]

#assert_trust kernel endpointExtension_fourier_nonneg
#print axioms endpointExtension_fourier_nonneg

end NLA.Proofs.SP14
