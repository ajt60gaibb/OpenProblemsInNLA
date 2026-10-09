import NLA.IE06.Semantics
import NLA.IE06.Measurability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib

/-! Exact Gaussian input-normalization exception. These are the reviewed F8
probability statements; no numerical value for the interval mass is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace NLA.IE06

def gaussianUnitIntervalMass : ℝ :=
  (gaussianReal 0 1 (Set.Ioo (-1 : ℝ) 1)).toReal

theorem gaussianUnitIntervalMass_bounds :
    0 < gaussianUnitIntervalMass ∧ gaussianUnitIntervalMass < 1 := by
  let μ := gaussianReal 0 1
  have hac : (volume : Measure ℝ) ≪ μ :=
    gaussianReal_absolutelyContinuous' 0 (by norm_num)
  have hin : μ (Set.Ioo (-1 : ℝ) 1) ≠ 0 := by
    intro hz
    have h := hac hz
    norm_num at h
  have hout : μ (Set.Ioo (2 : ℝ) 3) ≠ 0 := by
    intro hz
    have h := hac hz
    norm_num at h
  have hcomp : μ (Set.Ioo (-1 : ℝ) 1)ᶜ ≠ 0 := by
    intro hz
    apply hout
    apply measure_mono_null _ hz
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Ioo] at *
    intro hxIn
    linarith [hx.1, hxIn.2]
  have hlt : μ (Set.Ioo (-1 : ℝ) 1) < 1 := by
    calc
      μ (Set.Ioo (-1 : ℝ) 1) <
          μ (Set.Ioo (-1 : ℝ) 1) + μ (Set.Ioo (-1 : ℝ) 1)ᶜ :=
        ENNReal.lt_add_right (measure_ne_top _ _) hcomp
      _ = 1 := by rw [measure_add_measure_compl measurableSet_Ioo, measure_univ]
  constructor
  · exact ENNReal.toReal_pos hin (measure_ne_top _ _)
  · change (μ (Set.Ioo (-1 : ℝ) 1)).toReal < (1 : ENNReal).toReal
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2 hlt

/-- The strict input-max event is precisely the product of open unit intervals,
including the dimension-zero case. -/
theorem entryMax_lt_one_iff {n : ℕ} (A : Mat n) :
    entryMax A < 1 ↔ ∀ i j, |A i j| < 1 := by
  change (entryMaxNN A : ℝ) < (1 : ℝ) ↔ _
  rw [← NNReal.coe_one, NNReal.coe_lt_coe]
  rw [entryMaxNN, Finset.sup_lt_iff (by norm_num : (⊥ : ℝ≥0) < 1)]
  simp only [Finset.mem_univ, forall_true_left, Prod.forall]
  simp only [← NNReal.coe_lt_coe, NNReal.coe_one, coe_nnnorm, Real.norm_eq_abs]

theorem gaussian_entryMax_lt_one_probability (n : ℕ) :
    gaussianMatrix n {A : Mat n | entryMax A < 1} =
      ENNReal.ofReal (gaussianUnitIntervalMass ^ (n ^ 2)) := by
  have hset : {A : Mat n | entryMax A < 1} =
      Set.univ.pi (fun _ : Fin n =>
        Set.univ.pi (fun _ : Fin n => Set.Ioo (-1 : ℝ) 1)) := by
    ext A
    change (entryMax A < 1) ↔ (∀ i ∈ (Set.univ : Set (Fin n)),
      ∀ j ∈ (Set.univ : Set (Fin n)), A i j ∈ Set.Ioo (-1 : ℝ) 1)
    simp only [entryMax_lt_one_iff, Set.mem_univ, forall_true_left, Set.mem_Ioo, abs_lt]
  rw [hset]
  change (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1) _ = _
  simp only [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  have hq : gaussianReal 0 1 (Set.Ioo (-1 : ℝ) 1) =
      ENNReal.ofReal gaussianUnitIntervalMass := by
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hq, ← ENNReal.ofReal_pow (gaussianUnitIntervalMass_bounds.1.le), pow_two]

/-- The exact normalization exception is eventually smaller than every inverse
real power. The cutoff is existential; no large integer is evaluated. -/
theorem gaussian_entryMax_lt_one_eventually (α : ℝ) :
    ∀ᶠ n : ℕ in atTop, gaussianMatrix n {A : Mat n | entryMax A < 1} <
      ENNReal.ofReal ((n : ℝ) ^ (-α)) := by
  obtain ⟨hq0, hq1⟩ := gaussianUnitIntervalMass_bounds
  let q := gaussianUnitIntervalMass
  have hlog : 0 < -Real.log q := neg_pos.mpr (Real.log_neg hq0 hq1)
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ α * q ^ n) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero α
      (-Real.log q) hlog).comp tendsto_natCast_atTop_atTop
    convert h using 1
    funext n
    simp only [Function.comp_apply, neg_neg]
    rw [mul_comm (Real.log q), Real.exp_nat_mul, Real.exp_log hq0]
  have hev := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hpow : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hn0 α
  have hdecay : q ^ n < (n : ℝ) ^ (-α) := by
    rw [Real.rpow_neg hn0.le, ← one_div]
    exact (lt_div_iff₀ hpow).2 (by simpa only [mul_comm] using hn)
  rw [gaussian_entryMax_lt_one_probability]
  apply (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hn0 _)).mpr
  exact lt_of_le_of_lt
    (pow_le_pow_of_le_one hq0.le hq1.le (by nlinarith : n ≤ n ^ 2)) hdecay

#assert_trust kernel gaussianUnitIntervalMass_bounds
#assert_trust kernel entryMax_lt_one_iff
#assert_trust kernel gaussian_entryMax_lt_one_probability
#assert_trust kernel gaussian_entryMax_lt_one_eventually
#print axioms gaussian_entryMax_lt_one_eventually
#print axioms gaussianUnitIntervalMass_bounds
#print axioms entryMax_lt_one_iff
#print axioms gaussian_entryMax_lt_one_probability

end NLA.IE06
