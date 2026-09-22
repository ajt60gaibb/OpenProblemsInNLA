import NLA.IE21.GaussianTrimming
import Mathlib.Probability.Moments.SubGaussian

/-! Exact finite-sample Hoeffding bounds for the bounded selector variables. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal
namespace NLA.IE21

/-- One upper Hoeffding tail with the exact source exponent. -/
theorem bounded_sum_upper_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (L : ℝ) (hL : 0 < L) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 L)
    (a : ℝ) (ha : ∀ i, ∫ ω, X i ω ∂μ = a) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * L * ε < (∑ i, X i ω) - m * a} ≤
      Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let c : ℝ≥0 := (‖L - 0‖₊ / 2) ^ 2
  have hc : (c : ℝ) = L ^ 2 / 4 := by
    simp [c, Real.norm_eq_abs, abs_of_pos hL]
    ring
  have hsg (i : Fin m) : HasSubgaussianMGF (fun ω => X i ω - a) c μ := by
    simpa only [ha i] using hasSubgaussianMGF_of_mem_Icc (hX i).aemeasurable (hb i)
  have hind : iIndepFun (fun i ω => X i ω - a) μ := by
    simpa only [Function.comp_def] using hi.comp (fun _ (z : ℝ) => z - a) (by intro i; fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => c) (fun i _ => hsg i)
    (show 0 ≤ (m : ℝ) * L * ε by positivity)
  have hsum (ω : Ω) : (∑ i, (X i ω - a)) = (∑ i, X i ω) - m * a := by
    simp [Finset.sum_sub_distrib]
  simp only [hsum] at h
  have hexp : -((m : ℝ) * L * ε) ^ 2 / (2 * ∑ _i : Fin m, (c : ℝ)) =
      -2 * (m : ℝ) * ε ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
    field_simp
    ring
  simp only [NNReal.coe_sum] at h
  rw [hexp] at h
  apply (measureReal_mono (show {ω | (m : ℝ) * L * ε < (∑ i, X i ω) - m * a} ⊆
    {ω | (m : ℝ) * L * ε ≤ (∑ i, X i ω) - m * a} from by
      intro ω hω
      change (m : ℝ) * L * ε ≤ (∑ i, X i ω) - m * a
      exact le_of_lt hω)).trans h

/-- The lower tail is obtained by reflecting each observation in its interval. -/
theorem bounded_sum_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (L : ℝ) (hL : 0 < L) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 L)
    (a : ℝ) (ha : ∀ i, ∫ ω, X i ω ∂μ = a) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * L * ε < m * a - (∑ i, X i ω)} ≤
      Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have h := bounded_sum_upper_tail μ hm (fun i ω => L - X i ω)
    (fun i => (hX i).const_sub L)
    (hi.comp (fun _ (z : ℝ) => L - z) (by intro i; fun_prop)) L hL
    (fun i => (hb i).mono fun ω h => ⟨by linarith [h.2], by linarith [h.1]⟩)
    (L - a) (fun i => by
      rw [integral_sub (integrable_const L) (Integrable.of_mem_Icc 0 L (hX i).aemeasurable (hb i))]
      simp [ha i]) ε hε
  have heq (ω : Ω) : (∑ i, (L - X i ω)) - m * (L - a) = m * a - ∑ i, X i ω := by
    simp [Finset.sum_sub_distrib]
    ring
  simpa only [heq] using h

/-- Two-sided Hoeffding for a bounded independent sample with a common mean. -/
theorem bounded_sum_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (L : ℝ) (hL : 0 < L) (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Icc 0 L)
    (a : ℝ) (ha : ∀ i, ∫ ω, X i ω ∂μ = a) (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | (m : ℝ) * L * ε < |(∑ i, X i ω) - m * a|} ≤
      2 * Real.exp (-2 * (m : ℝ) * ε ^ 2) := by
  have hs : {ω | (m : ℝ) * L * ε < |(∑ i, X i ω) - m * a|} ⊆
      {ω | (m : ℝ) * L * ε < (∑ i, X i ω) - m * a} ∪
      {ω | (m : ℝ) * L * ε < m * a - (∑ i, X i ω)} := by
    intro ω hω
    change (m : ℝ) * L * ε < |(∑ i, X i ω) - m * a| at hω
    rcases lt_abs.mp hω with h | h
    · exact Or.inl h
    · apply Or.inr
      change (m : ℝ) * L * ε < m * a - ∑ i, X i ω
      linarith
  have hu := bounded_sum_upper_tail μ hm X hX hi L hL hb a ha ε hε
  have hl := bounded_sum_lower_tail μ hm X hX hi L hL hb a ha ε hε
  exact ((measureReal_mono hs).trans (measureReal_union_le _ _)).trans (by linarith)

end NLA.IE21
