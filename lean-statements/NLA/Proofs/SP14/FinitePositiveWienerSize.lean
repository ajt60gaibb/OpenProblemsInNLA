import NLA.Proofs.SP14.FinitePositiveWienerMultiplier

/-!
The finite positive coefficient size is exactly the literal W^(9/8)
Fourier-integral size of the source's positive Laurent correction.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

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

private def positiveMode {v : ℕ} (j : Fin v) : ℤ :=
  ((j.val + 1 : ℕ) : ℤ)

private theorem positiveMode_injective {v : ℕ} :
    Function.Injective (positiveMode (v := v)) := by
  intro i j h
  apply Fin.ext
  dsimp [positiveMode] at h
  omega

private theorem positiveLaurent_fourier (v : ℕ) (q : Fin v → ℝ) (k : ℤ) :
    FourierCoefficient (positiveLaurent v q) k =
      ∑ j : Fin v, (q j : ℂ) * (if positiveMode j = k then 1 else 0) := by
  unfold positiveLaurent
  rw [FourierCoefficient_finset_sum']
  · apply Finset.sum_congr rfl
    intro j hj
    rw [FourierCoefficient_const_mul']
    simpa [positiveMode] using
      congrArg ((q j : ℂ) * ·)
        (FourierCoefficient_circle_mode (positiveMode j) k)
  · intro j hj
    have hmode : Continuous (fun s : Circle => (s : ℂ) ^ (positiveMode j)) := by
      have hp : Continuous (fun s : Circle => (s : Circle) ^ (positiveMode j)) :=
        continuous_zpow _
      apply (continuous_subtype_val.comp hp).congr
      intro s
      exact Circle.coe_zpow _ _
    exact continuous_const.mul hmode

private theorem positiveLaurent_wiener_term (v : ℕ) (q : Fin v → ℝ) (k : ℤ) :
    wienerWeight k * ‖FourierCoefficient (positiveLaurent v q) k‖ =
      ∑ j : Fin v,
        if positiveMode j = k then
          wienerWeight (positiveMode j) * ‖(q j : ℂ)‖ else 0 := by
  rw [positiveLaurent_fourier]
  by_cases hk : ∃ j : Fin v, positiveMode j = k
  · obtain ⟨j, hj⟩ := hk
    have hsingle :
        (∑ i : Fin v, (q i : ℂ) * (if positiveMode i = k then 1 else 0)) =
          (q j : ℂ) := by
      calc
        (∑ i : Fin v, (q i : ℂ) * (if positiveMode i = k then 1 else 0)) =
            (q j : ℂ) * (if positiveMode j = k then 1 else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hneq : positiveMode i ≠ k := by
              intro hi'
              exact hne (positiveMode_injective (hi'.trans hj.symm))
            simp [hneq]
          · simp
        _ = (q j : ℂ) := by simp [hj]
    have hsingle' :
        (∑ i : Fin v,
          if positiveMode i = k then
            wienerWeight (positiveMode i) * ‖(q i : ℂ)‖ else 0) =
          wienerWeight (positiveMode j) * ‖(q j : ℂ)‖ := by
      calc
        (∑ i : Fin v,
          if positiveMode i = k then
            wienerWeight (positiveMode i) * ‖(q i : ℂ)‖ else 0) =
            (if positiveMode j = k then
              wienerWeight (positiveMode j) * ‖(q j : ℂ)‖ else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hneq : positiveMode i ≠ k := by
              intro hi'
              exact hne (positiveMode_injective (hi'.trans hj.symm))
            simp [hneq]
          · simp
        _ = _ := by simp [hj]
    rw [hsingle, hsingle', hj]
  · have hzero (i : Fin v) : positiveMode i ≠ k := by
      intro hi
      exact hk ⟨i, hi⟩
    simp_rw [if_neg (hzero _)]
    simp

theorem positiveLaurent_wiener_eq (v : ℕ) (q : Fin v → ℝ) :
    weightedWienerSize (positiveLaurent v q) =
      finitePositiveWienerSize v q := by
  unfold weightedWienerSize finitePositiveWienerSize
  simp_rw [positiveLaurent_wiener_term]
  have hterms : ∀ j ∈ (Finset.univ : Finset (Fin v)),
      Summable (fun k : ℤ =>
        if positiveMode j = k then
          wienerWeight (positiveMode j) * ‖(q j : ℂ)‖ else 0) := by
    intro j hj
    apply summable_of_ne_finset_zero (s := {positiveMode j})
    intro k hk
    have hne : positiveMode j ≠ k := (by simpa using hk : k ≠ positiveMode j).symm
    simp [hne]
  rw [Summable.tsum_finsetSum hterms]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tsum_eq_single (positiveMode j)]
  · simp [positiveMode]
  · intro k hne
    simp [hne.symm]

private theorem summable_wiener_constant_one :
    Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (fun _ : Circle => (1 : ℂ)) k‖) := by
  have hmode : (fun _ : Circle => (1 : ℂ)) =
      (fun s : Circle => (s : ℂ) ^ (0 : ℤ)) := by
    funext s
    simp
  rw [hmode]
  simp_rw [FourierCoefficient_circle_mode 0]
  apply summable_of_ne_finset_zero (s := {0})
  intro k hk
  have hne : (0 : ℤ) ≠ k := (by simpa using hk : k ≠ 0).symm
  simp [hne]

theorem summable_positiveLaurent_wiener (v : ℕ) (q : Fin v → ℝ) :
    Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient (positiveLaurent v q) k‖) := by
  have h := summable_mul_positiveLaurent_wiener
    (fun _ : Circle => (1 : ℂ)) continuous_const
    summable_wiener_constant_one v q
  simpa only [one_mul] using h

#assert_trust kernel positiveLaurent_wiener_eq
#assert_trust kernel summable_positiveLaurent_wiener

end NLA.Proofs.SP14
