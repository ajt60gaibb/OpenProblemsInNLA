import NLA.IE21.EmpiricalTrimming
import NLA.IE21.BoundedConcentration

/-! Atom-robust, exact finite-sample concentration of the lower trimmed sum. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal
namespace NLA.IE21

theorem retainedRows_bounds (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (m : ℕ) :
    retainedRows θ m ≤ m ∧ (retainedRows θ m : ℝ) ≤ (m : ℝ) * θ ∧
      |(retainedRows θ m : ℝ) - m * θ| ≤ 1 := by
  have h0 : 0 ≤ θ * (m : ℝ) := mul_nonneg hθ.1.le (Nat.cast_nonneg m)
  have hlo := Nat.floor_le h0
  have hhi := Nat.lt_floor_add_one (θ * (m : ℝ))
  refine ⟨Nat.floor_le_of_le (by nlinarith [Nat.cast_nonneg (α := ℝ) m]), ?_, ?_⟩
  · simpa [retainedRows, mul_comm] using hlo
  · unfold retainedRows
    rw [abs_of_nonpos (by nlinarith)]
    linarith

/-- The sample error on the three good events, with the exact floor correction. -/
theorem finiteTrim_fractional_mean_error {m : ℕ} (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (y w : Fin m → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (b L : ℝ) (hb : 0 ≤ b) (hbL : b ≤ L)
    (halign : ∀ i, max (b - y i) 0 = (b - y i) * w i)
    (hcount : retainedRows θ m ≤ (Finset.univ.filter (fun i => y i ≤ L)).card)
    (P ε : ℝ) (_hε : 0 ≤ ε)
    (hW : |(∑ i, w i) - m * θ| ≤ m * ε)
    (hZ : |(∑ i, y i * w i) - m * P| ≤ m * L * ε) :
    |finiteTrim (retainedRows θ m) y / m - P| ≤ 2 * L * ε + L / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk := retainedRows_bounds θ hθ m
  have hwerror : |(retainedRows θ m : ℝ) - ∑ i, w i| ≤ 1 + m * ε := by
    have h := abs_sub_le (retainedRows θ m : ℝ) (m * θ) (∑ i, w i)
    rw [abs_sub_comm (m * θ)] at h
    linarith [hk.2.2]
  have htrim := finiteTrim_fractional_error hm (retainedRows θ m) hk.1 y w hy hw b L hb hbL halign hcount
  have habs := abs_sub_le (finiteTrim (retainedRows θ m) y) (∑ i, y i * w i) (m * P)
  have hbound : |finiteTrim (retainedRows θ m) y - m * P| ≤ (m : ℝ) * (2 * L * ε + L / m) := by
    have hmul := mul_le_mul_of_nonneg_left hwerror (hb.trans hbL)
    have heq : (m : ℝ) * (2 * L * ε + L / m) = L * (1 + m * ε) + m * L * ε := by
      field_simp
      ring
    rw [heq]
    linarith
  have heq : finiteTrim (retainedRows θ m) y / m - P =
      (finiteTrim (retainedRows θ m) y - m * P) / m := by field_simp
  rw [heq, abs_div, abs_of_pos hm0]
  exact (div_le_iff₀ hm0).2 (by simpa [mul_comm] using hbound)

/-- The complete five-tail estimate for arbitrary independent copies of a
nonnegative random variable of mean one. The quantile selector may be fractional
on an atom, so no atomlessness premise is required. -/
theorem independent_trim_concentration {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} (hm : 1 ≤ m) (R : Fin m → Ω → Ξ)
    (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R ν)
    (hlaw : ∀ i, ν.map (R i) = μ) (Y : Ξ → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ z, 0 ≤ Y z)
    (hmean : ∫ z, Y z ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (ε : ℝ) (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) :
    ν.real {ω | |finiteTrim (retainedRows θ m) (fun i => Y (R i ω)) / m - populationTrim θ μ Y| >
      2 * truncationScale θ * ε + truncationScale θ / m} ≤
      5 * Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  classical
  let L := truncationScale θ
  have hθ1 : 0 < 1 - θ := sub_pos.mpr hθ.2
  have hL : 0 < L := by dsimp [L, truncationScale]; positivity
  have hLeq : L * (1 - θ) = 2 := by dsimp [L, truncationScale]; field_simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  obtain ⟨b, hb, hbu, hbelow, habove⟩ := exists_bounded_quantile μ Y hYm hY hY0 hmean θ hθ
  have hbL : b ≤ L := hbu.trans (by dsimp [L, truncationScale]; gcongr; norm_num)
  obtain ⟨W, hWm, hWi, hZint, hW, hWbelow, hWabove, hWmean, hP⟩ :=
    exists_fractional_selector μ Y hYm hY θ hθ.2.le b hb hbelow habove
  have hZbounds (z : Ξ) : Y z * W z ∈ Icc 0 L := by
    refine ⟨mul_nonneg (hY0 z) (hW z).1, ?_⟩
    by_cases hyb : Y z ≤ b
    · nlinarith [hY0 z, (hW z).1, (hW z).2]
    · rw [hWabove z (lt_of_not_ge hyb), mul_zero]
      exact hL.le
  have halign (z : Ξ) : max (b - Y z) 0 = (b - Y z) * W z := by
    rcases lt_trichotomy (Y z) b with h | h | h
    · rw [hWbelow z h, mul_one, max_eq_left (sub_nonneg.mpr h.le)]
    · rw [h, sub_self, max_self, zero_mul]
    · rw [hWabove z h, mul_zero, max_eq_right (sub_nonpos.mpr h.le)]
  let C : Ξ → ℝ := {z | Y z ≤ L}.indicator (fun _ => 1)
  have hCm : Measurable C := measurable_const.indicator (measurableSet_le hYm measurable_const)
  have hCb (z : Ξ) : C z ∈ Icc 0 1 := by
    dsimp [C, Set.indicator]
    split_ifs <;> norm_num
  have hCi : Integrable C μ := Integrable.of_mem_Icc 0 1 hCm.aemeasurable (ae_of_all _ hCb)
  let q : ℝ := ∫ z, C z ∂μ
  have hq : θ + ε ≤ q := by
    have hp : ∀ z, L * (1 - C z) ≤ Y z := by
      intro z
      dsimp [C, Set.indicator]
      split_ifs with hy
      · simpa using hY0 z
      · simpa using (le_of_lt (lt_of_not_ge hy))
    have hh := integral_mono ((integrable_const (1 : ℝ)).sub hCi |>.const_mul L) hY hp
    simp only [Pi.sub_apply] at hh
    rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hCi, integral_const, probReal_univ, smul_eq_mul, one_mul, hmean] at hh
    change L * (1 - q) ≤ 1 at hh
    nlinarith
  have transfer (F : Ξ → ℝ) (hF : Measurable F) (i : Fin m) :
      (∫ ω, F (R i ω) ∂ν) = ∫ z, F z ∂μ := by
    rw [← integral_map (hR i).aemeasurable hF.aestronglyMeasurable, hlaw i]
  have hwtail := bounded_sum_abs_tail ν hm (fun i ω => W (R i ω))
    (fun i => hWm.comp (hR i)) (hind.comp (fun _ => W) (fun _ => hWm))
    1 zero_lt_one (fun i => ae_of_all _ fun ω => hW (R i ω)) θ
    (fun i => (transfer W hWm i).trans hWmean) ε hε.1.le
  have hztail := bounded_sum_abs_tail ν hm (fun i ω => Y (R i ω) * W (R i ω))
    (fun i => (hYm.mul hWm).comp (hR i))
    (hind.comp (fun _ z => Y z * W z) (fun _ => hYm.mul hWm))
    L hL (fun i => ae_of_all _ fun ω => hZbounds (R i ω)) (populationTrim θ μ Y)
    (fun i => (transfer (fun z => Y z * W z) (hYm.mul hWm) i).trans hP.symm) ε hε.1.le
  have hctail := bounded_sum_lower_tail ν hm (fun i ω => C (R i ω))
    (fun i => hCm.comp (hR i)) (hind.comp (fun _ => C) (fun _ => hCm))
    1 zero_lt_one (fun i => ae_of_all _ fun ω => hCb (R i ω)) q
    (fun i => transfer C hCm i) ε hε.1.le
  simp only [mul_one] at hwtail hctail
  let EW : Set Ω := {ω | (m : ℝ) * ε < |(∑ i, W (R i ω)) - m * θ|}
  let EZ : Set Ω := {ω | (m : ℝ) * L * ε < |(∑ i, Y (R i ω) * W (R i ω)) - m * populationTrim θ μ Y|}
  let EC : Set Ω := {ω | (m : ℝ) * ε < m * q - ∑ i, C (R i ω)}
  have hsubset : {ω | |finiteTrim (retainedRows θ m) (fun i => Y (R i ω)) / m - populationTrim θ μ Y| >
      2 * L * ε + L / m} ⊆ EW ∪ EZ ∪ EC := by
    intro ω hbad
    by_contra hnot
    have hWgood : |(∑ i, W (R i ω)) - m * θ| ≤ m * ε := by
      by_contra hh
      exact hnot (Or.inl (Or.inl (lt_of_not_ge hh)))
    have hZgood : |(∑ i, Y (R i ω) * W (R i ω)) - m * populationTrim θ μ Y| ≤ m * L * ε := by
      by_contra hh
      exact hnot (Or.inl (Or.inr (lt_of_not_ge hh)))
    have hCgood : m * q - (∑ i, C (R i ω)) ≤ m * ε := by
      by_contra hh
      exact hnot (Or.inr (lt_of_not_ge hh))
    have hCsum : (∑ i, C (R i ω)) = ((Finset.univ.filter (fun i => Y (R i ω) ≤ L)).card : ℝ) := by
      simp [C, Set.indicator]
    have hcount : retainedRows θ m ≤ (Finset.univ.filter (fun i => Y (R i ω) ≤ L)).card := by
      have hk := (retainedRows_bounds θ hθ m).2.1
      rw [hCsum] at hCgood
      exact_mod_cast (show (retainedRows θ m : ℝ) ≤ ((Finset.univ.filter (fun i => Y (R i ω) ≤ L)).card : ℝ) by nlinarith)
    have hgood := finiteTrim_fractional_mean_error hm θ hθ (fun i => Y (R i ω)) (fun i => W (R i ω))
      (fun i => hY0 (R i ω)) (fun i => hW (R i ω)) b L hb hbL (fun i => halign (R i ω)) hcount
      (populationTrim θ μ Y) ε hε.1.le hWgood hZgood
    exact not_lt_of_ge hgood hbad
  have hprob : ν.real (EW ∪ EZ ∪ EC) ≤ ν.real EW + ν.real EZ + ν.real EC := by
    have h1 := measureReal_union_le (μ := ν) (EW ∪ EZ) EC
    have h2 := measureReal_union_le (μ := ν) EW EZ
    linarith
  exact ((measureReal_mono hsubset).trans hprob).trans (by dsimp [EW, EZ, EC]; linarith)

end NLA.IE21
