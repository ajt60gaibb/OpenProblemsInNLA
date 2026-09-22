import NLA.IE21.RowLaw
import Mathlib.Tactic

/-! Exact Chernoff constants used by the IE-21 covariance estimate.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NLA.IE21

lemma independent_mgf_sum_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) (a : ℝ)
    (hmgf : ∀ i, mgf (X i) μ a ≤ Real.exp (32 * a ^ 2)) :
    mgf (fun ω => ∑ i, X i ω) μ a ≤ Real.exp (32 * (m : ℝ) * a ^ 2) := by
  have h := hind.mgf_sum hX (Finset.univ : Finset (Fin m)) (t := a)
  have heq : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    simp
  rw [heq, h]
  calc
    (∏ i, mgf (X i) μ a) ≤ ∏ _i : Fin m, Real.exp (32 * a ^ 2) :=
      Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => hmgf i)
    _ = Real.exp (32 * (m : ℝ) * a ^ 2) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      ring

lemma independent_mgf_average_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1 ≤ m)
    (X : Fin m → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hmgf : ∀ (a : ℝ), |a| ≤ 1 / 8 → ∀ i,
      Integrable (fun ω => Real.exp (a * X i ω)) μ ∧
      mgf (X i) μ a ≤ Real.exp (32 * a ^ 2))
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) :
    μ.real {ω | s < |(∑ i, X i ω) / m|} ≤
      2 * Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
  have hspos : 0 < s := hs.1
  have hmp : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hm)
  let Z : Ω → ℝ := fun ω => ∑ i, X i ω
  have hp : |s / 64| ≤ (1 : ℝ) / 8 := by rw [abs_of_pos (by positivity)]; linarith [hs.2]
  have hn : |(-s) / 64| ≤ (1 : ℝ) / 8 := by simpa only [neg_div, abs_neg] using hp
  have hi (a : ℝ) (ha : |a| ≤ 1 / 8) : Integrable (fun ω => Real.exp (a * Z ω)) μ := by
    have h := hind.integrable_exp_mul_sum hX
      (s := (Finset.univ : Finset (Fin m))) (fun i _ => (hmgf a ha i).1)
    simpa only [Finset.sum_apply] using h
  have hu : μ.real {ω | (m : ℝ) * s ≤ Z ω} ≤
      Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := Z)
      ((m : ℝ) * s) (show 0 ≤ s / 64 by positivity) (hi (s / 64) hp)
    have hb := independent_mgf_sum_bound μ X hX hind (s / 64) (fun i => (hmgf _ hp i).2)
    have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-(s / 64) * ((m : ℝ) * s))).le
    refine h.trans (hmul.trans_eq ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  have hl : μ.real {ω | Z ω ≤ -(m : ℝ) * s} ≤
      Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
    have h := measure_le_le_exp_mul_mgf (μ := μ) (X := Z)
      (-(m : ℝ) * s) (show (-s) / 64 ≤ 0 by linarith [hs.1]) (hi ((-s) / 64) hn)
    have hb := independent_mgf_sum_bound μ X hX hind ((-s) / 64) (fun i => (hmgf _ hn i).2)
    have hmul := mul_le_mul_of_nonneg_left hb
      (Real.exp_pos (-((-s) / 64) * (-(m : ℝ) * s))).le
    refine h.trans (hmul.trans_eq ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  have hsub : {ω | s < |(∑ i, X i ω) / m|} ⊆
      {ω | (m : ℝ) * s ≤ Z ω} ∪ {ω | Z ω ≤ -(m : ℝ) * s} := by
    intro ω hω
    change s < |(∑ i, X i ω) / m| at hω
    rcases lt_abs.mp hω with hω | hω
    · left
      exact (by nlinarith [(lt_div_iff₀ hmp).mp hω] : (m : ℝ) * s ≤ Z ω)
    · right
      change Z ω ≤ -(m : ℝ) * s
      have hh : Z ω / (m : ℝ) < -s := by linarith
      nlinarith [(div_lt_iff₀ hmp).mp hh]
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (by linarith))

end NLA.IE21
