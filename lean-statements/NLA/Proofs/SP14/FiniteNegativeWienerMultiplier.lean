import NLA.Proofs.SP14.FiniteNegativeWiener
import NLA.Proofs.SP14.NegativeProductFourierSupport

/-!
The source's literal W^(9/8) weight has a constant-one finite negative
Laurent multiplier bound under the actual SP-14 Fourier integral.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem wienerWeight_nonneg (k : ℤ) : 0 ≤ wienerWeight k := by
  unfold wienerWeight
  positivity

private theorem wienerWeight_shift_le (k r : ℤ) :
    wienerWeight k ≤ wienerWeight (k + r) * wienerWeight (-r) := by
  have htri : k.natAbs ≤ (k + r).natAbs + r.natAbs := by
    simpa using Int.natAbs_sub_le (k + r) r
  have htriR : (k.natAbs : ℝ) ≤
      ((k + r).natAbs : ℝ) + (r.natAbs : ℝ) := by exact_mod_cast htri
  have ha : 0 ≤ (1 + ((k + r).natAbs : ℝ)) := by positivity
  have hb : 0 ≤ (1 + (r.natAbs : ℝ)) := by positivity
  have hmul : 1 + (k.natAbs : ℝ) ≤
      (1 + ((k + r).natAbs : ℝ)) * (1 + (r.natAbs : ℝ)) := by
    have hnat : 0 ≤ ((k + r).natAbs : ℝ) * (r.natAbs : ℝ) := by positivity
    nlinarith
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 + (k.natAbs : ℝ)))
    hmul (by norm_num : (0 : ℝ) ≤ 9 / 8)
  rw [Real.mul_rpow ha hb] at hpow
  simpa [wienerWeight, Int.natAbs_neg] using hpow

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

private theorem mul_negativeLaurent_fourier
    (f : Circle → ℂ) (hf : Continuous f)
    (u : ℕ) (q : Fin u → ℝ) (k : ℤ) :
    FourierCoefficient (fun s => f s * negativeLaurent u q s) k =
      ∑ j : Fin u, (q j : ℂ) *
        FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ)) := by
  have hsum : (fun s : Circle => f s * negativeLaurent u q s) =
      (fun s : Circle => ∑ j : Fin u,
        (q j : ℂ) * (f s * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ)))) := by
    funext s
    simp only [negativeLaurent, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum, FourierCoefficient_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [FourierCoefficient_const_mul, FourierCoefficient_mul_circle_mode]
    congr 1
  · intro j hj
    have hmode : Continuous
        (fun s : Circle => (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ))) := by
      have hp : Continuous
          (fun s : Circle => (s : Circle) ^ (-((j.val + 1 : ℕ) : ℤ))) :=
        continuous_zpow _
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow _ _
    exact continuous_const.mul (hf.mul hmode)

private noncomputable def multiplierTerm (f : Circle → ℂ) (u : ℕ)
    (q : Fin u → ℝ) (j : Fin u) (k : ℤ) : ℝ :=
  (wienerWeight (-((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖) *
    (wienerWeight (k + ((j.val + 1 : ℕ) : ℤ)) *
      ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖)

private theorem summable_multiplierTerm
    (f : Circle → ℂ)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (u : ℕ) (q : Fin u → ℝ) (j : Fin u) :
    Summable (multiplierTerm f u q j) := by
  unfold multiplierTerm
  have hshift : Summable (fun k : ℤ =>
      wienerWeight (k + ((j.val + 1 : ℕ) : ℤ)) *
        ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖) :=
    hfs.comp_injective (by intro a b hab; exact add_right_cancel hab)
  exact hshift.mul_left _

private theorem summable_multiplierBound
    (f : Circle → ℂ)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (u : ℕ) (q : Fin u → ℝ) :
    Summable (fun k : ℤ => ∑ j : Fin u, multiplierTerm f u q j k) := by
  let S : Finset (Fin u) := Finset.univ
  have hs (T : Finset (Fin u)) :
      Summable (fun k : ℤ => ∑ j ∈ T, multiplierTerm f u q j k) := by
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hj ih =>
        simpa only [Finset.sum_insert hj] using
          (summable_multiplierTerm f hfs u q j).add ih
  simpa [S] using hs S

private theorem multiplier_pointwise_le
    (f : Circle → ℂ) (hf : Continuous f)
    (u : ℕ) (q : Fin u → ℝ) (k : ℤ) :
    wienerWeight k *
        ‖FourierCoefficient (fun s => f s * negativeLaurent u q s) k‖ ≤
      ∑ j : Fin u, multiplierTerm f u q j k := by
  rw [mul_negativeLaurent_fourier f hf]
  have hn : ‖∑ j : Fin u,
      (q j : ℂ) * FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖ ≤
      ∑ j : Fin u,
        ‖(q j : ℂ) * FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖ :=
    norm_sum_le _ _
  calc
    wienerWeight k *
        ‖∑ j : Fin u,
          (q j : ℂ) * FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖ ≤
      wienerWeight k *
        (∑ j : Fin u,
          ‖(q j : ℂ) * FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖) :=
      mul_le_mul_of_nonneg_left hn (wienerWeight_nonneg k)
    _ = ∑ j : Fin u,
        wienerWeight k *
          ‖(q j : ℂ) * FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin u, multiplierTerm f u q j k := by
      apply Finset.sum_le_sum
      intro j hj
      have hw := wienerWeight_shift_le k ((j.val + 1 : ℕ) : ℤ)
      dsimp [multiplierTerm]
      rw [norm_mul]
      have hnonneg : 0 ≤ ‖(q j : ℂ)‖ *
          ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖ := by positivity
      have hm := mul_le_mul_of_nonneg_right hw hnonneg
      calc
        wienerWeight k *
            (‖(q j : ℂ)‖ *
              ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖) ≤
          (wienerWeight (k + ((j.val + 1 : ℕ) : ℤ)) *
              wienerWeight (-((j.val + 1 : ℕ) : ℤ))) *
            (‖(q j : ℂ)‖ *
              ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖) := hm
        _ = (wienerWeight (-((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖) *
            (wienerWeight (k + ((j.val + 1 : ℕ) : ℤ)) *
              ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖) := by ring

theorem summable_mul_negativeLaurent_wiener
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (u : ℕ) (q : Fin u → ℝ) :
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient (fun s => f s * negativeLaurent u q s) k‖) := by
  apply Summable.of_nonneg_of_le
  · intro k
    exact mul_nonneg (wienerWeight_nonneg k) (norm_nonneg _)
  · exact multiplier_pointwise_le f hf u q
  · exact summable_multiplierBound f hfs u q

theorem weightedWienerSize_mul_negativeLaurent_le
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖))
    (u : ℕ) (q : Fin u → ℝ) :
    weightedWienerSize (fun s => f s * negativeLaurent u q s) ≤
      weightedWienerSize f * finiteNegativeWienerSize u q := by
  have hprod := summable_mul_negativeLaurent_wiener f hf hfs u q
  have hbound := summable_multiplierBound f hfs u q
  unfold weightedWienerSize
  calc
    (∑' k : ℤ,
      wienerWeight k *
        ‖FourierCoefficient (fun s => f s * negativeLaurent u q s) k‖) ≤
      ∑' k : ℤ, ∑ j : Fin u, multiplierTerm f u q j k :=
      hprod.tsum_le_tsum (multiplier_pointwise_le f hf u q) hbound
    _ = (∑ j : Fin u,
          wienerWeight (-((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖) *
        (∑' k : ℤ, wienerWeight k * ‖FourierCoefficient f k‖) := by
      rw [Summable.tsum_finsetSum]
      · simp_rw [multiplierTerm, tsum_mul_left]
        have hshift (j : Fin u) :
            (∑' k : ℤ,
              wienerWeight (k + ((j.val + 1 : ℕ) : ℤ)) *
                ‖FourierCoefficient f (k + ((j.val + 1 : ℕ) : ℤ))‖) =
              ∑' k : ℤ, wienerWeight k * ‖FourierCoefficient f k‖ := by
          simpa [Equiv.addRight] using
            (Equiv.addRight ((j.val + 1 : ℕ) : ℤ) : ℤ ≃ ℤ).tsum_eq
              (fun x : ℤ => wienerWeight x * ‖FourierCoefficient f x‖)
        simp_rw [hshift]
        rw [Finset.sum_mul]
      · intro j hj
        exact summable_multiplierTerm f hfs u q j
    _ = _ := by simp [finiteNegativeWienerSize, mul_comm]

#assert_trust kernel summable_mul_negativeLaurent_wiener
#assert_trust kernel weightedWienerSize_mul_negativeLaurent_le

end NLA.Proofs.SP14
