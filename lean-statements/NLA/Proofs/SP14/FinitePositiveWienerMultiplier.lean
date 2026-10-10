import NLA.Proofs.SP14.PositiveEndpointRatio
import NLA.Proofs.SP14.FiniteNegativeWienerMultiplier

/-!
Constant-one W^(9/8) multiplier bound for the actual finite positive
Laurent correction, using the frozen normalized Fourier interval integral.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def finitePositiveWienerSize (v : ℕ) (q : Fin v → ℝ) : ℝ :=
  ∑ j : Fin v,
    wienerWeight (((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖

private theorem wienerWeight_nonneg' (k : ℤ) : 0 ≤ wienerWeight k := by
  unfold wienerWeight
  positivity

private theorem wienerWeight_sub_shift_le (k r : ℤ) :
    wienerWeight k ≤ wienerWeight (k - r) * wienerWeight r := by
  have htri : k.natAbs ≤ (k - r).natAbs + r.natAbs := by
    simpa using Int.natAbs_add_le (k - r) r
  have htriR : (k.natAbs : ℝ) ≤
      ((k - r).natAbs : ℝ) + (r.natAbs : ℝ) := by exact_mod_cast htri
  have ha : 0 ≤ (1 + ((k - r).natAbs : ℝ)) := by positivity
  have hb : 0 ≤ (1 + (r.natAbs : ℝ)) := by positivity
  have hmul : 1 + (k.natAbs : ℝ) ≤
      (1 + ((k - r).natAbs : ℝ)) * (1 + (r.natAbs : ℝ)) := by
    have hnat : 0 ≤ ((k - r).natAbs : ℝ) * (r.natAbs : ℝ) := by positivity
    nlinarith
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 + (k.natAbs : ℝ)))
    hmul (by norm_num : (0 : ℝ) ≤ 9 / 8)
  rw [Real.mul_rpow ha hb] at hpow
  simpa [wienerWeight] using hpow

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

private theorem mul_positiveLaurent_fourier
    (f : Circle → ℂ) (hf : Continuous f)
    (v : ℕ) (q : Fin v → ℝ) (k : ℤ) :
    FourierCoefficient (fun s => f s * positiveLaurent v q s) k =
      ∑ j : Fin v, (q j : ℂ) *
        FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ)) := by
  have hsum : (fun s : Circle => f s * positiveLaurent v q s) =
      (fun s : Circle => ∑ j : Fin v,
        (q j : ℂ) * (f s * (s : ℂ) ^ (((j.val + 1 : ℕ) : ℤ)))) := by
    funext s
    simp only [positiveLaurent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum, FourierCoefficient_finset_sum']
  · apply Finset.sum_congr rfl
    intro j hj
    rw [FourierCoefficient_const_mul', FourierCoefficient_mul_circle_mode']
  · intro j hj
    have hmode : Continuous
        (fun s : Circle => (s : ℂ) ^ (((j.val + 1 : ℕ) : ℤ))) := by
      have hp : Continuous
          (fun s : Circle => (s : Circle) ^ (((j.val + 1 : ℕ) : ℤ))) :=
        continuous_zpow _
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow _ _
    exact continuous_const.mul (hf.mul hmode)

private noncomputable def positiveMultiplierTerm (f : Circle → ℂ) (v : ℕ)
    (q : Fin v → ℝ) (j : Fin v) (k : ℤ) : ℝ :=
  (wienerWeight (((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖) *
    (wienerWeight (k - ((j.val + 1 : ℕ) : ℤ)) *
      ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖)

private theorem summable_positiveMultiplierTerm
    (f : Circle → ℂ)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (v : ℕ) (q : Fin v → ℝ) (j : Fin v) :
    Summable (positiveMultiplierTerm f v q j) := by
  unfold positiveMultiplierTerm
  have hshift : Summable (fun k : ℤ =>
      wienerWeight (k - ((j.val + 1 : ℕ) : ℤ)) *
        ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖) :=
    hfs.comp_injective (by
      intro a b hab
      dsimp at hab
      omega)
  exact hshift.mul_left _

private theorem summable_positiveMultiplierBound
    (f : Circle → ℂ)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (v : ℕ) (q : Fin v → ℝ) :
    Summable (fun k : ℤ => ∑ j : Fin v, positiveMultiplierTerm f v q j k) := by
  let S : Finset (Fin v) := Finset.univ
  have hs (T : Finset (Fin v)) :
      Summable (fun k : ℤ => ∑ j ∈ T, positiveMultiplierTerm f v q j k) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hj ih =>
        simpa only [Finset.sum_insert hj] using
          (summable_positiveMultiplierTerm f hfs v q j).add ih
  simpa [S] using hs S

private theorem positiveMultiplier_pointwise_le
    (f : Circle → ℂ) (hf : Continuous f)
    (v : ℕ) (q : Fin v → ℝ) (k : ℤ) :
    wienerWeight k *
        ‖FourierCoefficient (fun s => f s * positiveLaurent v q s) k‖ ≤
      ∑ j : Fin v, positiveMultiplierTerm f v q j k := by
  rw [mul_positiveLaurent_fourier f hf]
  have hn : ‖∑ j : Fin v,
      (q j : ℂ) * FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖ ≤
      ∑ j : Fin v,
        ‖(q j : ℂ) * FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖ :=
    norm_sum_le _ _
  calc
    wienerWeight k *
        ‖∑ j : Fin v,
          (q j : ℂ) * FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖ ≤
      wienerWeight k *
        (∑ j : Fin v,
          ‖(q j : ℂ) * FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖) :=
      mul_le_mul_of_nonneg_left hn (wienerWeight_nonneg' k)
    _ = ∑ j : Fin v,
        wienerWeight k *
          ‖(q j : ℂ) * FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin v, positiveMultiplierTerm f v q j k := by
      apply Finset.sum_le_sum
      intro j hj
      have hw := wienerWeight_sub_shift_le k ((j.val + 1 : ℕ) : ℤ)
      dsimp [positiveMultiplierTerm]
      rw [norm_mul]
      have hnonneg : 0 ≤ ‖(q j : ℂ)‖ *
          ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖ := by positivity
      have hm := mul_le_mul_of_nonneg_right hw hnonneg
      calc
        wienerWeight k *
            (‖(q j : ℂ)‖ *
              ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖) ≤
          (wienerWeight (k - ((j.val + 1 : ℕ) : ℤ)) *
              wienerWeight (((j.val + 1 : ℕ) : ℤ))) *
            (‖(q j : ℂ)‖ *
              ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖) := hm
        _ = (wienerWeight (((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖) *
            (wienerWeight (k - ((j.val + 1 : ℕ) : ℤ)) *
              ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖) := by ring

theorem summable_mul_positiveLaurent_wiener
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (v : ℕ) (q : Fin v → ℝ) :
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient (fun s => f s * positiveLaurent v q s) k‖) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (wienerWeight_nonneg' k) (norm_nonneg _)
  · exact positiveMultiplier_pointwise_le f hf v q
  · exact summable_positiveMultiplierBound f hfs v q

theorem weightedWienerSize_mul_positiveLaurent_le
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (v : ℕ) (q : Fin v → ℝ) :
    weightedWienerSize (fun s => f s * positiveLaurent v q s) ≤
      weightedWienerSize f * finitePositiveWienerSize v q := by
  have hprod := summable_mul_positiveLaurent_wiener f hf hfs v q
  have hbound := summable_positiveMultiplierBound f hfs v q
  unfold weightedWienerSize
  calc
    (∑' k : ℤ,
      wienerWeight k *
        ‖FourierCoefficient (fun s => f s * positiveLaurent v q s) k‖) ≤
      ∑' k : ℤ, ∑ j : Fin v, positiveMultiplierTerm f v q j k :=
      hprod.tsum_le_tsum (positiveMultiplier_pointwise_le f hf v q) hbound
    _ = (∑ j : Fin v,
          wienerWeight (((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖) *
        (∑' k : ℤ, wienerWeight k * ‖FourierCoefficient f k‖) := by
      rw [Summable.tsum_finsetSum]
      · simp_rw [positiveMultiplierTerm, tsum_mul_left]
        have hshift (j : Fin v) :
            (∑' k : ℤ,
              wienerWeight (k - ((j.val + 1 : ℕ) : ℤ)) *
                ‖FourierCoefficient f (k - ((j.val + 1 : ℕ) : ℤ))‖) =
              ∑' k : ℤ, wienerWeight k * ‖FourierCoefficient f k‖ := by
          simpa [Equiv.subRight] using
            (Equiv.subRight ((j.val + 1 : ℕ) : ℤ) : ℤ ≃ ℤ).tsum_eq
              (fun x : ℤ => wienerWeight x * ‖FourierCoefficient f x‖)
        simp_rw [hshift]
        rw [Finset.sum_mul]
      · intro j hj
        exact summable_positiveMultiplierTerm f hfs v q j
    _ = _ := by simp [finitePositiveWienerSize, mul_comm]

#assert_trust kernel summable_mul_positiveLaurent_wiener
#assert_trust kernel weightedWienerSize_mul_positiveLaurent_le

end NLA.Proofs.SP14
