import ProofProject.DiagonalWitness
import ProofProject.GrowthRate
import ProofProject.Rescaling

/-!
# Transport of discrete peaks to all sufficiently large times

A linear bound on the double-logarithmic witness clock and a polynomial peak
bound suffice for the desired lower bound at every large time. The proof uses
the integer part of `growthLog t / C` and exact time rescaling of the witnesses.
-/

noncomputable section

namespace ProofProject

universe u

/-- Above two, the natural floor retains at least half the original value. -/
lemma half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

/-- Polynomially large discrete witnesses with a linear clock bound give
finite-dimensional witnesses of the same order at every sufficiently large
time. The class constant `M` is preserved by time rescaling. -/
theorem finiteWitness_lower_of_discrete {M α a C : ℝ}
    (hM : 0 ≤ M) (hα : 0 < α) (ha : 0 < a) (hC : 0 < C) (n₀ : ℕ)
    (hdiscrete : ∀ n : ℕ, n₀ ≤ n → ∃ s : ℝ, 0 < s ∧
      growthLog s ≤ C * (n : ℝ) ∧
      HasFiniteWitness.{u} M s (a * (n : ℝ) ^ α - 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t → HasFiniteWitness.{u} M t (c * growthLog t ^ α) := by
  let R : ℝ := (2 / a) ^ α⁻¹
  have hR : 0 < R := by dsimp [R]; positivity
  have hRpow : R ^ α = 2 / a := by
    exact Real.rpow_inv_rpow (by positivity) hα.ne'
  let B : ℝ := max 2 (max (2 * (n₀ : ℝ)) (2 * R))
  have hBtwo : 2 ≤ B := le_max_left _ _
  have hBn₀ : 2 * (n₀ : ℝ) ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hBR : 2 * R ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨tstar, htstar, hclockstar⟩ := exists_lt_growthLog (C * B)
  let t₀ := max 1 tstar
  have ht₀ : 0 < t₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let c : ℝ := a / (2 * (2 * C) ^ α)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, t₀, ht₀, ?_⟩
  intro t ht
  have htpos : 0 < t := ht₀.trans_le ht
  have hstart : tstar ≤ t := (le_max_right 1 tstar).trans ht
  have hclock : C * B ≤ growthLog t :=
    hclockstar.le.trans ((growthLog_le_growthLog_iff htstar htpos.le).mpr hstart)
  let x : ℝ := growthLog t / C
  let n : ℕ := ⌊x⌋₊
  have hBx : B ≤ x := by
    apply (le_div_iff₀ hC).mpr
    simpa [mul_comm] using hclock
  have hx2 : 2 ≤ x := hBtwo.trans hBx
  have hxn : x / 2 ≤ (n : ℝ) := half_le_nat_floor hx2
  have hxn₀ : (n₀ : ℝ) ≤ n := by linarith
  have hn₀ : n₀ ≤ n := by exact_mod_cast hxn₀
  have hnR : R ≤ (n : ℝ) := by linarith
  have hnclock : C * (n : ℝ) ≤ growthLog t := by
    have hnle : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
    have h := (le_div_iff₀ hC).mp hnle
    simpa [mul_comm] using h
  have hfloor : growthLog t / (2 * C) ≤ (n : ℝ) := by
    convert hxn using 1
    dsimp [x]
    ring
  have hpowR : 2 / a ≤ (n : ℝ) ^ α := by
    rw [← hRpow]
    exact Real.rpow_le_rpow hR.le hnR hα.le
  have habsorb : 2 ≤ a * (n : ℝ) ^ α := by
    have h := (div_le_iff₀ ha).mp hpowR
    simpa [mul_comm] using h
  have hlower : c * growthLog t ^ α ≤ a * (n : ℝ) ^ α - 1 := by
    calc
      _ = (a / 2) * (growthLog t / (2 * C)) ^ α := by
        rw [Real.div_rpow (growthLog_pos htpos.le).le (by positivity)]
        dsimp [c]
        ring
      _ ≤ (a / 2) * (n : ℝ) ^ α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity [growthLog_pos htpos.le]) hfloor hα.le)
        (by positivity)
      _ ≤ a * (n : ℝ) ^ α - 1 := by nlinarith
  obtain ⟨s, hs, hclock_s, hw⟩ := hdiscrete n hn₀
  have hst : s ≤ t := time_le_of_growthLog_bounds hs.le htpos.le hclock_s hnclock
  exact (hw.mono_time hM hs hst).mono_lower hlower

end ProofProject
