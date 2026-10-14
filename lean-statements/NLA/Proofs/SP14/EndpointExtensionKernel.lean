import NLA.Proofs.SP14.EndpointBaseFourier
import NLA.Proofs.SP14.BaseEndpointPartialConvolution

/-!
The actual Fourier kernel of the endpoint square-root extension on analytic
monomials. The weighted Schur and Hilbert--Schmidt estimates are separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem baseCoeffReal_cast (n : ℕ) :
    (baseCoeffReal n : ℂ) = baseCoeff n := by
  simpa [baseCoeffReal, baseCoeff] using
    (Ring.map_choose (algebraMap ℝ ℂ) (1 / 2 : ℝ) n)

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

/-- The finite triangular inverse of the analytic monomial `s^k`. -/
noncomputable def endpointInverseMonomial (k : ℕ) (z : Circle) : ℂ :=
  ∑ l ∈ Finset.range (k + 1),
    (baseInverseCoeff l : ℂ) * (z : ℂ) ^ (k - l)

private theorem continuous_endpointInverseMonomial (k : ℕ) :
    Continuous (endpointInverseMonomial k) := by
  unfold endpointInverseMonomial
  apply continuous_finset_sum
  intro l hl
  fun_prop

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

private theorem endpointExtension_fourier_neg_sum (k j : ℕ) :
    FourierCoefficient
        (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
        (-(j : ℤ)) =
      ((∑ d ∈ Finset.range (k + 1),
        baseCoeffReal (d + j) * baseInverseCoeff (k - d) : ℝ) : ℂ) := by
  rw [endpointExtension_fourier_sum]
  calc
    (∑ l ∈ Finset.range (k + 1),
        (baseInverseCoeff l : ℂ) *
          FourierCoefficient endpointBaseSymbol (-(j : ℤ) - ((k - l : ℕ) : ℤ))) =
      ∑ l ∈ Finset.range (k + 1),
        ((baseInverseCoeff l * baseCoeffReal (k + j - l) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
      have hfreq : -(j : ℤ) - ((k - l : ℕ) : ℤ) =
          -((k + j - l : ℕ) : ℤ) := by omega
      rw [hfreq, endpointBase_fourier_neg]
      rw [← baseCoeffReal_cast]
      push_cast
      ring
    _ = ((∑ d ∈ Finset.range (k + 1),
        baseCoeffReal (d + j) * baseInverseCoeff (k - d) : ℝ) : ℂ) := by
      rw [← Finset.sum_range_reflect]
      push_cast
      apply Finset.sum_congr rfl
      intro d hd
      have hdk : d ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
      have heq : k + j - (k - d) = d + j := by omega
      rw [heq]
      ring

/-- The actual negative-frequency endpoint extension kernel before taking
absolute values; all `k≥0` and all `j≥1` are included. -/
theorem endpointExtension_fourier_neg (k j : ℕ) (hj : 1 ≤ j) :
    FourierCoefficient
        (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
        (-(j : ℤ)) =
      (((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
        baseInverseCoeff k * baseInverseCoeff (j - 1) : ℂ) := by
  rw [endpointExtension_fourier_neg_sum]
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (baseEndpoint_partialConvolution k j hj)
  push_cast at h
  simpa using h

#assert_trust kernel endpointExtension_fourier_neg
#print axioms endpointExtension_fourier_neg

end NLA.Proofs.SP14
