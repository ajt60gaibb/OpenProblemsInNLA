import NLA.Proofs.RE06.GaussianQuadratic
import NLA.Proofs.RE06.GaussianLogBounds

/-! Source-strength lower and upper tails for finite weighted Gaussian
sketch energies under the actual stream measure. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Head entries contribute a fixed logarithmic cost, while the tail
pays for its own below-mean threshold. -/
theorem quadratic_trimmed_log_bound (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (head : Finset ι) (a : ℝ) (ha : 0 < a)
    (hhead : ∀ i ∈ head, a ≤ w i) (htail : ∀ i ∉ head, w i ≤ a)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (head.card : ℝ) * (η / 2) +
      (1 - η) * (η / a) * (∑ i ∈ headᶜ, w i) ≤
      ∑ i, Real.log (1 + (η / a) * w i) := by
  have hηa : 0 ≤ η / a := le_of_lt (div_pos hη0 ha)
  have hh : ∑ i ∈ head, η / 2 ≤ ∑ i ∈ head, Real.log (1 + (η / a) * w i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply (log_one_add_ge_half η hη0.le hη1).trans
    apply Real.log_le_log (by linarith)
    have hmul := mul_le_mul_of_nonneg_left (hhead i hi) hηa
    have he : (η / a) * a = η := div_mul_cancel₀ η ha.ne'
    linarith
  have ht : ∑ i ∈ headᶜ, (1 - η) * ((η / a) * w i) ≤
      ∑ i ∈ headᶜ, Real.log (1 + (η / a) * w i) := by
    apply Finset.sum_le_sum
    intro i hi
    apply log_one_add_ge_scaled η ((η / a) * w i) hη0.le (mul_nonneg hηa (hw i))
    have hmul := mul_le_mul_of_nonneg_left (htail i (Finset.mem_compl.mp hi)) hηa
    simpa only [div_mul_cancel₀ η ha.ne'] using hmul
  have hsplit := Finset.sum_add_sum_compl head (fun i => Real.log (1 + (η / a) * w i))
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  rw [← Finset.mul_sum] at ht
  rw [← Finset.mul_sum] at ht
  nlinarith

/-- Exact source lower-tail exponent for a sorted-spectrum split. The chosen
`a` is the first tail weight, so these hypotheses are deterministic. -/
theorem streamQuadratic_trimmed_lower_tail (s : ℕ)
    (f : ι × Fin s → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (head : Finset ι)
    (a : ℝ) (ha : 0 < a)
    (hhead : ∀ i ∈ head, a ≤ w i) (htail : ∀ i ∉ head, w i ≤ a)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    GaussianLaw.real {ω | gaussianQuadratic (fun p : ι × Fin s => w p.1)
      (fun p => ω (f p)) < (s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i} ≤
      Real.exp (-(s : ℝ) * (head.card : ℝ) * η / 4) := by
  let θ : ℝ := η / (2 * a)
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hlog := quadratic_trimmed_log_bound w hw head a ha hhead htail η hη0 hη1
  have hlogs : (∑ p : ι × Fin s, Real.log (1 + 2 * θ * w p.1)) =
      (s : ℝ) * ∑ i, Real.log (1 + (η / a) * w i) := by
    have he (i : ι) : 2 * θ * w i = (η / a) * w i := by dsimp [θ]; ring
    simp only [he, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hc := streamQuadratic_lower_chernoff f hf (fun p : ι × Fin s => w p.1)
    (fun p => hw p.1) θ hθ ((s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i)
  have hm := measureReal_mono (μ := GaussianLaw) (show
    {ω | gaussianQuadratic (fun p : ι × Fin s => w p.1) (fun p => ω (f p)) <
      (s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i} ⊆
    {ω | gaussianQuadratic (fun p : ι × Fin s => w p.1) (fun p => ω (f p)) ≤
      (s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i} from fun _ h => h.le)
  apply hm.trans (hc.trans _)
  apply Real.exp_le_exp.mpr
  rw [hlogs]
  have hs : (0 : ℝ) ≤ s := by positivity
  have h := mul_le_mul_of_nonneg_left hlog hs
  have hθa : θ = (η / a) / 2 := by dsimp [θ]; ring
  rw [hθa]
  nlinarith

/-- A zero tail makes the strict lower-tail bad event empty. -/
theorem streamQuadratic_zero_tail (s : ℕ) (f : ι × Fin s → ℕ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    GaussianLaw {ω | gaussianQuadratic (fun p : ι × Fin s => w p.1)
      (fun p => ω (f p)) < 0} = 0 := by
  have he : {ω | gaussianQuadratic (fun p : ι × Fin s => w p.1)
      (fun p => ω (f p)) < 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (not_lt_of_ge (Finset.sum_nonneg (fun p _ =>
      mul_nonneg (hw p.1) (sq_nonneg (ω (f p)))))) hω
  rw [he, measure_empty]

#assert_trust kernel quadratic_trimmed_log_bound
#assert_trust kernel streamQuadratic_trimmed_lower_tail
#assert_trust kernel streamQuadratic_zero_tail
#print axioms quadratic_trimmed_log_bound
#print axioms streamQuadratic_trimmed_lower_tail
#print axioms streamQuadratic_zero_tail
end NLA.Proofs.RE06
