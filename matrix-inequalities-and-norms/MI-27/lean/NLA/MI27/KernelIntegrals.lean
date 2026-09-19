import NLA.MI27.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Exact symbolic integration of the two scalar weights in the MI-27 entropy
argument. These are the frozen C13 and C14 obligations, including R = 1.
No numerical quadrature or discretization is used.

Analytic resolution: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.MI27

private theorem kernelAB_integral (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hR : 1 ≤ R) :
    IntervalIntegrable (kernelAB a b) MeasureTheory.volume 1 R ∧
      (∫ γ in (1 : ℝ)..R, kernelAB a b γ) =
        a * Real.log (R / (b + a * R)) := by
  have hpos (x : ℝ) (hx : 1 ≤ x) : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hden (x : ℝ) (hx : 1 ≤ x) : 0 < b + a * x :=
    add_pos hb (mul_pos ha (hpos x hx))
  have hc : ContinuousOn (kernelAB a b) (Set.Icc 1 R) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_id.mul (continuousOn_const.add (continuousOn_const.mul continuousOn_id)))
    intro x hx
    exact mul_ne_zero (hpos x hx.1).ne' (hden x hx.1).ne'
  have hi : IntervalIntegrable (kernelAB a b) MeasureTheory.volume 1 R :=
    hc.intervalIntegrable_of_Icc hR
  refine ⟨hi, ?_⟩
  have hd : ∀ x ∈ Set.uIcc (1 : ℝ) R,
      HasDerivAt (fun t : ℝ => a * (Real.log t - Real.log (b + a * t)))
        (kernelAB a b x) x := by
    intro x hx
    have hx' : 1 ≤ x := (Set.uIcc_of_le hR ▸ hx).1
    have hdx := (Real.hasDerivAt_log (hpos x hx').ne').sub
      ((((hasDerivAt_id x).const_mul a).const_add b).log (hden x hx').ne')
    convert hdx.const_mul a using 1 <;> try rfl
    dsimp [kernelAB]
    field_simp [(hpos x hx').ne', (hden x hx').ne']
    <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  have hba : b + a = 1 := by linarith
  rw [Real.log_div (hpos R hR).ne' (hden R hR).ne']
  simp [hba]

/-- C13: exact primitives and integrability of both canonical kernels. -/
theorem kernel_integrals (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hR : 1 ≤ R) :
    IntervalIntegrable (kernelAB a b) MeasureTheory.volume 1 R ∧
      IntervalIntegrable (kernelBA a b) MeasureTheory.volume 1 R ∧
      (∫ γ in (1 : ℝ)..R, kernelAB a b γ) = a * Real.log (R / (b + a * R)) ∧
      (∫ γ in (1 : ℝ)..R, kernelBA a b γ) = b * Real.log (R / (a + b * R)) := by
  obtain ⟨hi₁, he₁⟩ := kernelAB_integral a b R ha hb hab hR
  obtain ⟨hi₂, he₂⟩ := kernelAB_integral b a R hb ha (by linarith) hR
  have heq : kernelBA a b = kernelAB b a := by
    funext x
    simp only [kernelBA, kernelAB, mul_comm a b]
  refine ⟨hi₁, ?_, he₁, ?_⟩
  · simpa only [heq] using hi₂
  · simpa only [heq] using he₂

private theorem kernel_log_mass_bounds (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hR : 1 ≤ R) :
    0 ≤ a * Real.log (R / (b + a * R)) ∧
      a * Real.log (R / (b + a * R)) ≤ -a * Real.log a := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hd : 0 < b + a * R := add_pos hb (mul_pos ha hRp)
  have hdR : b + a * R ≤ R := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hR)]
  have hlo : 1 ≤ R / (b + a * R) := (le_div_iff₀ hd).2 (by simpa using hdR)
  have hup : R / (b + a * R) ≤ 1 / a :=
    (div_le_div_iff₀ hd ha).2 (by nlinarith)
  have hlog := Real.log_le_log (div_pos hRp hd) hup
  rw [Real.log_div one_ne_zero ha.ne', Real.log_one, zero_sub] at hlog
  refine ⟨mul_nonneg ha.le (Real.log_nonneg hlo), ?_⟩
  calc
    a * Real.log (R / (b + a * R)) ≤ a * (-Real.log a) :=
      mul_le_mul_of_nonneg_left hlog ha.le
    _ = -a * Real.log a := by ring

/-- C14: the finite kernel mass is nonnegative and bounded by binary entropy. -/
theorem kernel_entropy_mass_bound (a b R : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hR : 1 ≤ R) :
    0 ≤ (∫ γ in (1 : ℝ)..R, kernelAB a b γ) ∧
      (∫ γ in (1 : ℝ)..R, kernelAB a b γ) ≤ -a * Real.log a ∧
      0 ≤ (∫ γ in (1 : ℝ)..R, kernelBA a b γ) ∧
      (∫ γ in (1 : ℝ)..R, kernelBA a b γ) ≤ -b * Real.log b ∧
      (∫ γ in (1 : ℝ)..R, kernelAB a b γ) +
        (∫ γ in (1 : ℝ)..R, kernelBA a b γ) ≤ h a b := by
  obtain ⟨_, _, he₁, he₂⟩ := kernel_integrals a b R ha hb hab hR
  rw [he₁, he₂]
  obtain ⟨hlo₁, hup₁⟩ := kernel_log_mass_bounds a b R ha hb hab hR
  obtain ⟨hlo₂, hup₂⟩ := kernel_log_mass_bounds b a R hb ha (by linarith) hR
  refine ⟨hlo₁, hup₁, hlo₂, hup₂, ?_⟩
  simpa only [h, sub_eq_add_neg, neg_mul] using add_le_add hup₁ hup₂

#print axioms kernel_integrals
#print axioms kernel_entropy_mass_bound

end NLA.MI27
