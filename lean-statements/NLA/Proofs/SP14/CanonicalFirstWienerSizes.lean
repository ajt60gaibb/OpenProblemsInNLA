import NLA.Proofs.SP14.FiniteNegativeWiener
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Literal Fourier-integral Wiener sizes of finite negative and positive Laurent
polynomials. The exterior-factor W⁰ estimate is proved below in the same gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral Set

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def wienerSizeAt (β : ℝ) (f : Circle → ℂ) : ℝ :=
  ∑' k : ℤ, (1 + (k.natAbs : ℝ)) ^ β * ‖FourierCoefficient f k‖

theorem wienerSizeAt_nine_eighths (f : Circle → ℂ) :
    wienerSizeAt (9 / 8 : ℝ) f = weightedWienerSize f := by
  rfl

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

private theorem continuous_circle_mode' (ell : ℤ) :
    Continuous (fun s : Circle => (s : ℂ) ^ ell) := by
  have hp : Continuous (fun s : Circle => (s : Circle) ^ ell) := continuous_zpow _
  apply (continuous_subtype_val.comp hp).congr
  intro s
  exact Circle.coe_zpow _ _

private theorem finiteModes_fourier {u : ℕ}
    (ell : Fin u → ℤ) (p : Fin u → ℝ) (k : ℤ) :
    FourierCoefficient
      (fun s : Circle => ∑ j : Fin u, (p j : ℂ) * (s : ℂ) ^ (ell j)) k =
    ∑ j : Fin u, (p j : ℂ) * (if ell j = k then 1 else 0) := by
  rw [FourierCoefficient_finset_sum']
  · apply Finset.sum_congr rfl
    intro j hj
    rw [FourierCoefficient_const_mul']
    simpa using congrArg ((p j : ℂ) * ·)
      (FourierCoefficient_circle_mode (ell j) k)
  · intro j hj
    exact continuous_const.mul (continuous_circle_mode' (ell j))

private theorem finiteModes_term {u : ℕ}
    (ell : Fin u → ℤ) (hell : Function.Injective ell)
    (p : Fin u → ℝ) (β : ℝ) (k : ℤ) :
    (1 + (k.natAbs : ℝ)) ^ β *
        ‖FourierCoefficient
          (fun s : Circle => ∑ j : Fin u, (p j : ℂ) * (s : ℂ) ^ (ell j)) k‖ =
      ∑ j : Fin u,
        if ell j = k then
          (1 + ((ell j).natAbs : ℝ)) ^ β * ‖(p j : ℂ)‖ else 0 := by
  rw [finiteModes_fourier]
  by_cases hk : ∃ j : Fin u, ell j = k
  · obtain ⟨j, hj⟩ := hk
    have hsingle :
        (∑ i : Fin u, (p i : ℂ) * (if ell i = k then 1 else 0)) =
          (p j : ℂ) := by
      calc
        (∑ i : Fin u, (p i : ℂ) * (if ell i = k then 1 else 0)) =
            (p j : ℂ) * (if ell j = k then 1 else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hneq : ell i ≠ k := by
              intro hi'
              exact hne (hell (hi'.trans hj.symm))
            simp [hneq]
          · simp
        _ = (p j : ℂ) := by simp [hj]
    have hsingle' :
        (∑ i : Fin u,
          if ell i = k then
            (1 + ((ell i).natAbs : ℝ)) ^ β * ‖(p i : ℂ)‖ else 0) =
          (1 + ((ell j).natAbs : ℝ)) ^ β * ‖(p j : ℂ)‖ := by
      calc
        (∑ i : Fin u,
          if ell i = k then
            (1 + ((ell i).natAbs : ℝ)) ^ β * ‖(p i : ℂ)‖ else 0) =
            (if ell j = k then
              (1 + ((ell j).natAbs : ℝ)) ^ β * ‖(p j : ℂ)‖ else 0) := by
          apply Finset.sum_eq_single j
          · intro i hi hne
            have hneq : ell i ≠ k := by
              intro hi'
              exact hne (hell (hi'.trans hj.symm))
            simp [hneq]
          · simp
        _ = _ := by simp [hj]
    rw [hsingle, hsingle', hj]
  · have hzero (i : Fin u) : ell i ≠ k := by
      intro hi
      exact hk ⟨i, hi⟩
    simp_rw [if_neg (hzero _)]
    simp

private theorem finiteModes_wiener_eq {u : ℕ}
    (ell : Fin u → ℤ) (hell : Function.Injective ell)
    (p : Fin u → ℝ) (β : ℝ) :
    wienerSizeAt β
      (fun s : Circle => ∑ j : Fin u, (p j : ℂ) * (s : ℂ) ^ (ell j)) =
      ∑ j : Fin u,
        (1 + ((ell j).natAbs : ℝ)) ^ β * ‖(p j : ℂ)‖ := by
  unfold wienerSizeAt
  simp_rw [finiteModes_term ell hell p β]
  have hterms : ∀ j ∈ (Finset.univ : Finset (Fin u)),
      Summable (fun k : ℤ =>
        if ell j = k then
          (1 + ((ell j).natAbs : ℝ)) ^ β * ‖(p j : ℂ)‖ else 0) := by
    intro j hj
    apply summable_of_ne_finset_zero (s := {ell j})
    intro k hk
    have hne : ell j ≠ k := (by simpa using hk : k ≠ ell j).symm
    simp [hne]
  rw [Summable.tsum_finsetSum hterms]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tsum_eq_single (ell j)]
  · simp
  · intro k hne
    simp [hne.symm]

private def negativeMode' {u : ℕ} (j : Fin u) : ℤ :=
  -((j.val + 1 : ℕ) : ℤ)

private theorem negativeMode_injective' {u : ℕ} :
    Function.Injective (negativeMode' (u := u)) := by
  intro i j h
  apply Fin.ext
  dsimp [negativeMode'] at h
  omega

private def positiveMode' {v : ℕ} (j : Fin v) : ℤ :=
  ((j.val + 1 : ℕ) : ℤ)

private theorem positiveMode_injective' {v : ℕ} :
    Function.Injective (positiveMode' (v := v)) := by
  intro i j h
  apply Fin.ext
  dsimp [positiveMode'] at h
  omega

theorem negativeLaurent_W0_eq (u : ℕ) (p : Fin u → ℝ) :
    wienerSizeAt 0 (negativeLaurent u p) = ∑ j : Fin u, |p j| := by
  change wienerSizeAt 0
    (fun s : Circle => ∑ j : Fin u, (p j : ℂ) * (s : ℂ) ^ (negativeMode' j)) = _
  rw [finiteModes_wiener_eq negativeMode' negativeMode_injective']
  simp [Complex.norm_real, Real.norm_eq_abs]

theorem positiveLaurent_W4_eq (v : ℕ) (p : Fin v → ℝ) :
    wienerSizeAt 4 (positiveLaurent v p) =
      ∑ j : Fin v, ((j.val + 2 : ℕ) : ℝ) ^ 4 * |p j| := by
  change wienerSizeAt 4
    (fun s : Circle => ∑ j : Fin v, (p j : ℂ) * (s : ℂ) ^ (positiveMode' j)) = _
  rw [finiteModes_wiener_eq positiveMode' positiveMode_injective']
  apply Finset.sum_congr rfl
  intro j hj
  have hweight : 1 + ((positiveMode' j).natAbs : ℝ) =
      ((j.val + 2 : ℕ) : ℝ) := by
    have hnat : (positiveMode' j).natAbs = j.val + 1 := by
      simp only [positiveMode']
      omega
    rw [hnat]
    push_cast
    ring
  rw [hweight]
  simp [Complex.norm_real, Real.norm_eq_abs]

private noncomputable def baseFourierPhase (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))

private theorem baseFourierPhase_norm (k : ℤ) (t : ℝ) :
    ‖baseFourierPhase k t‖ = 1 := by
  have harg : -((k : ℂ) * Complex.I * (t : ℂ)) =
      (((-(k : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [baseFourierPhase, harg, Complex.norm_exp_ofReal_mul_I]

private noncomputable def baseFourierTerm (k : ℤ) (n : ℕ) : C(ℝ, ℂ) where
  toFun t := baseCoeff n * (Circle.exp t : ℂ) ^ (-(n : ℤ)) *
    baseFourierPhase k t
  continuous_toFun := by
    have hcoe : Continuous (fun t : ℝ => (Circle.exp t : ℂ) ^ (-(n : ℤ))) :=
      (continuous_circle_mode' (-(n : ℤ))).comp Circle.exp.continuous
    have hphase : Continuous (baseFourierPhase k) := by
      unfold baseFourierPhase
      fun_prop
    exact (continuous_const.mul hcoe).mul hphase

private theorem baseFourierTerm_norm (k : ℤ) (n : ℕ) (t : ℝ) :
    ‖baseFourierTerm k n t‖ = ‖baseCoeff n‖ := by
  simp only [baseFourierTerm, ContinuousMap.coe_mk, norm_mul, norm_zpow,
    Circle.norm_coe, one_zpow, baseFourierPhase_norm, mul_one]

private theorem baseExteriorFactor_fourier_tsum (k : ℤ) :
    FourierCoefficient baseExteriorFactor k =
      ∑' n : ℕ, baseCoeff n * (if -(n : ℤ) = k then 1 else 0) := by
  let F := baseFourierTerm k
  let K : TopologicalSpace.Compacts ℝ :=
    ⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩
  have hbound (n : ℕ) : ‖(F n).restrict K‖ ≤ ‖baseCoeff n‖ := by
    rw [ContinuousMap.norm_le ((F n).restrict K) (norm_nonneg _)]
    intro t
    exact le_of_eq (baseFourierTerm_norm k n t)
  have hsum : Summable (fun n : ℕ => ‖(F n).restrict K‖) := by
    apply Summable.of_norm_bounded summable_norm_baseCoeff
    intro n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound n
  have hintegral : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..(2 * Real.pi), F n t)
      (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
    exact intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (by simpa [K] using hsum)
  have hpoint (t : ℝ) : (∑' n : ℕ, F n t) =
      baseExteriorFactor (Circle.exp t) * baseFourierPhase k t := by
    have hs := (summable_baseExteriorFactor_terms (Circle.exp t)).hasSum.mul_right
      (baseFourierPhase k t)
    simpa [F, baseFourierTerm, baseExteriorFactor, mul_assoc] using hs.tsum_eq
  have hterm (n : ℕ) :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) =
          baseCoeff n * (if -(n : ℤ) = k then 1 else 0) := by
    have hmode := FourierCoefficient_circle_mode (-(n : ℤ)) k
    unfold FourierCoefficient at hmode
    change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (baseCoeff n * (Circle.exp t : ℂ) ^ (-(n : ℤ))) *
          baseFourierPhase k t) = _
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    calc
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (baseCoeff n * ∫ t in (0 : ℝ)..(2 * Real.pi),
            (Circle.exp t : ℂ) ^ (-(n : ℤ)) * baseFourierPhase k t) =
        baseCoeff n *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (0 : ℝ)..(2 * Real.pi),
              (Circle.exp t : ℂ) ^ (-(n : ℤ)) * baseFourierPhase k t) := by ring
      _ = _ := by
        simpa [baseFourierPhase] using congrArg (baseCoeff n * ·) hmode
  calc
    FourierCoefficient baseExteriorFactor k =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
      unfold FourierCoefficient
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simpa [baseFourierPhase] using (hpoint t).symm
    _ = ∑' n : ℕ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) :=
      (hintegral.mul_left _).tsum_eq.symm
    _ = ∑' n : ℕ, baseCoeff n * (if -(n : ℤ) = k then 1 else 0) := by
      apply tsum_congr
      intro n
      exact hterm n

theorem baseExteriorFactor_fourier (k : ℤ) :
    FourierCoefficient baseExteriorFactor k =
      if k ≤ 0 then baseCoeff k.natAbs else 0 := by
  rw [baseExteriorFactor_fourier_tsum]
  by_cases hk : k ≤ 0
  · have hn : -((k.natAbs : ℕ) : ℤ) = k := by omega
    have hsingle (n : ℕ) (hne : n ≠ k.natAbs) :
        baseCoeff n * (if -(n : ℤ) = k then 1 else 0) = 0 := by
      have hmode : -(n : ℤ) ≠ k := by
        intro heq
        have : n = k.natAbs := by omega
        exact hne this
      simp [hmode]
    rw [tsum_eq_single k.natAbs hsingle]
    rw [if_pos hn]
    simp [hk]
  · have hzero (n : ℕ) :
        baseCoeff n * (if -(n : ℤ) = k then 1 else 0) = 0 := by
      have hmode : -(n : ℤ) ≠ k := by omega
      simp [hmode]
    simp_rw [hzero]
    simp [hk]

private noncomputable def baseW0Term (k : ℤ) : ℝ :=
  ‖FourierCoefficient baseExteriorFactor k‖

private theorem baseW0Term_pos (n : ℕ) :
    baseW0Term ((n + 1 : ℕ) : ℤ) = 0 := by
  simp [baseW0Term, baseExteriorFactor_fourier]

private theorem baseW0Term_nonpos (n : ℕ) :
    baseW0Term (-(n : ℤ)) = ‖baseCoeff n‖ := by
  simp [baseW0Term, baseExteriorFactor_fourier, Int.natAbs_neg]

theorem baseExteriorFactor_W0_summable :
    Summable (fun k : ℤ => ‖FourierCoefficient baseExteriorFactor k‖) := by
  change Summable baseW0Term
  have hpos : Summable (fun n : ℕ => baseW0Term ((n + 1 : ℕ) : ℤ)) := by
    simp_rw [baseW0Term_pos]
    exact summable_zero
  have hneg : Summable (fun n : ℕ => baseW0Term (-((n + 1 : ℕ) : ℤ))) := by
    simpa only [baseW0Term_nonpos] using
      ((summable_nat_add_iff 1).mpr summable_norm_baseCoeff)
  exact Summable.of_add_one_of_neg_add_one hpos hneg

private theorem baseExteriorFactor_W0_eq :
    wienerSizeAt 0 baseExteriorFactor = ∑' n : ℕ, ‖baseCoeff n‖ := by
  have hpos : Summable (fun n : ℕ => baseW0Term ((n + 1 : ℕ) : ℤ)) := by
    simp_rw [baseW0Term_pos]
    exact summable_zero
  have hneg : Summable (fun n : ℕ => baseW0Term (-((n + 1 : ℕ) : ℤ))) := by
    simpa only [baseW0Term_nonpos] using
      ((summable_nat_add_iff 1).mpr summable_norm_baseCoeff)
  have hfull := tsum_of_add_one_of_neg_add_one hpos hneg
  have hsplit := summable_norm_baseCoeff.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  unfold wienerSizeAt
  simp only [Real.rpow_zero, one_mul]
  change (∑' k : ℤ, baseW0Term k) = _
  rw [hfull]
  have hposzero : (∑' n : ℕ, baseW0Term ((n : ℤ) + 1)) = 0 := by
    have hterm (n : ℕ) : baseW0Term ((n : ℤ) + 1) = 0 := by
      have hcast : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, baseW0Term_pos]
    simp_rw [hterm]
    simp
  have hnegseries :
      (∑' n : ℕ, baseW0Term (-((n : ℤ) + 1))) =
        ∑' n : ℕ, ‖baseCoeff (n + 1)‖ := by
    apply tsum_congr
    intro n
    have hcast : -((n : ℤ) + 1) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [hcast, baseW0Term_nonpos]
  have hzero : baseW0Term 0 = ‖baseCoeff 0‖ := by
    simpa using baseW0Term_nonpos 0
  rw [hposzero, hnegseries, hzero]
  simpa only [zero_add] using hsplit

private theorem baseCoeff_succ_mul' (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * baseCoeff (n + 1) =
      ((1 / 2 : ℂ) - n) * baseCoeff n := by
  unfold baseCoeff
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub]
  simp only [Polynomial.smeval_X, Polynomial.smeval_natCast, pow_zero, mul_one,
    nsmul_eq_mul]
  have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hf, hn]

private theorem baseCoeff_norm_succ' (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * ‖baseCoeff (n + 1)‖ =
      ((n : ℝ) - 1 / 2) * ‖baseCoeff n‖ := by
  have hnonpos : (1 / 2 : ℝ) - n ≤ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfactor : ‖(1 / 2 : ℂ) - (n : ℂ)‖ = (n : ℝ) - 1 / 2 := by
    have hcast : (1 / 2 : ℂ) - (n : ℂ) =
        (((1 / 2 : ℝ) - n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hnonpos]
    ring
  have h := congrArg norm (baseCoeff_succ_mul' n)
  have hnat : ‖((n + 1 : ℕ) : ℂ)‖ = (n : ℝ) + 1 := by
    rw [Complex.norm_natCast]
    push_cast
    ring
  rw [norm_mul, norm_mul, hnat, hfactor] at h
  exact h

private theorem baseCoeff_sum_range_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖baseCoeff n‖) ≤ 2 := by
  have hzero : ‖baseCoeff 0‖ = 1 := by simp [baseCoeff]
  have hone : ‖baseCoeff 1‖ = 1 / 2 := by
    norm_num [baseCoeff, Ring.choose_one_right]
  have htel (M : ℕ) :
      (∑ n ∈ Finset.range M, ‖baseCoeff (n + 1)‖) =
        1 - 2 * ((M : ℝ) + 1) * ‖baseCoeff (M + 1)‖ := by
    induction M with
    | zero => simp [hone]
    | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have hr := baseCoeff_norm_succ' (M + 1) (by omega : 1 ≤ M + 1)
      push_cast at hr ⊢
      nlinarith
  cases N with
  | zero => simp
  | succ N =>
    rw [Finset.sum_range_succ', htel, hzero]
    have hnonneg : 0 ≤ ‖baseCoeff (N + 1)‖ := norm_nonneg _
    nlinarith

theorem baseExteriorFactor_W0_le_two :
    wienerSizeAt 0 baseExteriorFactor ≤ 2 := by
  rw [baseExteriorFactor_W0_eq]
  exact summable_norm_baseCoeff.tsum_le_of_sum_range_le
    baseCoeff_sum_range_le_two

#assert_trust kernel wienerSizeAt_nine_eighths
#assert_trust kernel negativeLaurent_W0_eq
#assert_trust kernel positiveLaurent_W4_eq
#assert_trust kernel baseExteriorFactor_fourier
#assert_trust kernel baseExteriorFactor_W0_summable
#assert_trust kernel baseExteriorFactor_W0_le_two

end NLA.Proofs.SP14
