import NLA.Proofs.SP14.RegularizedFactorWiener
import NLA.Proofs.SP14.FiniteLaurentBackground
import NLA.Proofs.SP14.BaseFourierMode

/-!
The finite negative Laurent correction has exactly its literal finite
coefficient Wiener size under the frozen SP-14 Fourier integral.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def finiteNegativeWienerSize (u : ℕ) (q : Fin u → ℝ) : ℝ :=
  ∑ j : Fin u,
    wienerWeight (-((j.val + 1 : ℕ) : ℤ)) * ‖(q j : ℂ)‖

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

private def negativeMode {u : ℕ} (j : Fin u) : ℤ :=
  -((j.val + 1 : ℕ) : ℤ)

private theorem negativeMode_injective {u : ℕ} :
    Function.Injective (negativeMode (u := u)) := by
  intro i j h
  apply Fin.ext
  dsimp [negativeMode] at h
  omega

private theorem negativeLaurent_fourier (u : ℕ) (q : Fin u → ℝ) (k : ℤ) :
    FourierCoefficient (negativeLaurent u q) k =
      ∑ j : Fin u, (q j : ℂ) * (if negativeMode j = k then 1 else 0) := by
  unfold negativeLaurent
  rw [FourierCoefficient_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [FourierCoefficient_const_mul]
    simpa [negativeMode] using
      congrArg ((q j : ℂ) * ·)
        (FourierCoefficient_circle_mode (negativeMode j) k)
  · intro j hj
    have hmode : Continuous (fun s : Circle => (s : ℂ) ^ (negativeMode j)) := by
      have hp : Continuous (fun s : Circle => (s : Circle) ^ (negativeMode j)) :=
        continuous_zpow _
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow _ _
    exact continuous_const.mul hmode

private theorem negativeLaurent_wiener_term (u : ℕ) (q : Fin u → ℝ) (k : ℤ) :
    wienerWeight k * ‖FourierCoefficient (negativeLaurent u q) k‖ =
      ∑ j : Fin u,
        if negativeMode j = k then
          wienerWeight (negativeMode j) * ‖(q j : ℂ)‖ else 0 := by
  rw [negativeLaurent_fourier]
  by_cases hk : ∃ j : Fin u, negativeMode j = k
  · obtain ⟨j, hj⟩ := hk
    have hsingle :
        (∑ i : Fin u, (q i : ℂ) * (if negativeMode i = k then 1 else 0)) =
          (q j : ℂ) := by
      calc
        (∑ i : Fin u, (q i : ℂ) * (if negativeMode i = k then 1 else 0)) =
            (q j : ℂ) * (if negativeMode j = k then 1 else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hneq : negativeMode i ≠ k := by
              intro hi'
              exact hne (negativeMode_injective (hi'.trans hj.symm))
            simp [hneq]
          · simp
        _ = (q j : ℂ) := by simp [hj]
    have hsingle' :
        (∑ i : Fin u,
          if negativeMode i = k then
            wienerWeight (negativeMode i) * ‖(q i : ℂ)‖ else 0) =
          wienerWeight (negativeMode j) * ‖(q j : ℂ)‖ := by
      calc
        (∑ i : Fin u,
          if negativeMode i = k then
            wienerWeight (negativeMode i) * ‖(q i : ℂ)‖ else 0) =
            (if negativeMode j = k then
              wienerWeight (negativeMode j) * ‖(q j : ℂ)‖ else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hneq : negativeMode i ≠ k := by
              intro hi'
              exact hne (negativeMode_injective (hi'.trans hj.symm))
            simp [hneq]
          · simp
        _ = _ := by simp [hj]
    rw [hsingle, hsingle', hj]
  · have hzero (i : Fin u) : negativeMode i ≠ k := by
      intro hi
      exact hk ⟨i, hi⟩
    simp_rw [if_neg (hzero _)]
    simp

theorem negativeLaurent_wiener_eq (u : ℕ) (q : Fin u → ℝ) :
    weightedWienerSize (negativeLaurent u q) = finiteNegativeWienerSize u q := by
  unfold weightedWienerSize finiteNegativeWienerSize
  simp_rw [negativeLaurent_wiener_term]
  have hterms : ∀ j ∈ (Finset.univ : Finset (Fin u)),
      Summable (fun k : ℤ =>
        if negativeMode j = k then
          wienerWeight (negativeMode j) * ‖(q j : ℂ)‖ else 0) := by
    intro j hj
    apply summable_of_ne_finset_zero (s := {negativeMode j})
    intro k hk
    have hne : negativeMode j ≠ k := (by simpa using hk : k ≠ negativeMode j).symm
    simp [hne]
  rw [Summable.tsum_finsetSum hterms]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [tsum_eq_single (negativeMode j)]
    · simp [negativeMode]
    · intro k hne
      simp [hne.symm]

#assert_trust kernel negativeLaurent_wiener_eq

end NLA.Proofs.SP14
