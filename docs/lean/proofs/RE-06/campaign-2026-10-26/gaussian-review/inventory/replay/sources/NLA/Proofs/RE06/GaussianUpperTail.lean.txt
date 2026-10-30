import NLA.Proofs.RE06.GaussianTails
import NLA.Proofs.RE06.GaussianUpperChernoff

/-! The one fixed-residual upper tail for the original unscaled Gaussian block. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06
variable {ι : Type*} [Fintype ι]

theorem streamQuadratic_normalized_upper_tail (s : ℕ)
    (f : ι × Fin s → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    GaussianLaw.real {ω : ℕ → ℝ | (s : ℝ) * (1 + η) <
      gaussianQuadratic (fun p : ι × Fin s => w p.1) (fun p => ω (f p))} ≤
      Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
  let θ : ℝ := η / (2 * (1 + η))
  have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 / 2 := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (1 + η))).2
    linarith
  have hw1 (i : ι) : w i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  have hdom (p : ι × Fin s) : θ * w p.1 < 1 / 2 := by
    exact (mul_le_of_le_one_right hθ0 (hw1 p.1)).trans_lt hθ1
  have hlog : Real.log (1 - 2 * θ) ≤ ∑ i, Real.log (1 - 2 * θ * w i) := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      log_one_sub_mul_ge_mul_log (2 * θ) (w i) (by positivity) (by linarith) (hw i) (hw1 i))
    simpa only [← Finset.sum_mul, hsum, one_mul] using h
  have hlogs : (∑ p : ι × Fin s, Real.log (1 - 2 * θ * w p.1)) =
      (s : ℝ) * ∑ i, Real.log (1 - 2 * θ * w i) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  have hc := streamQuadratic_upper_chernoff f hf (fun p : ι × Fin s => w p.1)
    θ hθ0 hdom ((s : ℝ) * (1 + η))
  have hm := measureReal_mono (μ := GaussianLaw) (show
    {ω : ℕ → ℝ | (s : ℝ) * (1 + η) < gaussianQuadratic (fun p : ι × Fin s => w p.1)
      (fun p => ω (f p))} ⊆
    {ω : ℕ → ℝ | (s : ℝ) * (1 + η) ≤ gaussianQuadratic (fun p : ι × Fin s => w p.1)
      (fun p => ω (f p))} from by
      intro ω h
      simp only [Set.mem_ofPred_eq] at h ⊢
      exact le_of_lt h)
  apply hm.trans (hc.trans _)
  apply Real.exp_le_exp.mpr
  rw [hlogs]
  have hcancel : θ * (1 + η) = η / 2 := by
    dsimp [θ]
    field_simp
  have hinv : 1 - 2 * θ = (1 + η)⁻¹ := by
    dsimp [θ]
    field_simp
    ring
  have hs : (0 : ℝ) ≤ s := by positivity
  have hlogscaled := mul_le_mul_of_nonneg_left hlog hs
  rw [hinv, Real.log_inv] at hlogscaled
  have hgap := log_one_add_le_sub_quarter_sq η hη0.le hη1
  have hgapscaled := mul_le_mul_of_nonneg_left hgap hs
  have hcancels := congrArg (fun x : ℝ => (s : ℝ) * x) hcancel
  nlinarith

/-- The arbitrary nonnegative-spectrum upper tail, including zero residuals. -/
theorem streamQuadratic_upper_tail (s : ℕ)
    (f : ι × Fin s → ℕ) (hf : Function.Injective f)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    GaussianLaw.real {ω : ℕ → ℝ | (s : ℝ) * (1 + η) * (∑ i, w i) <
      gaussianQuadratic (fun p : ι × Fin s => w p.1) (fun p => ω (f p))} ≤
      Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
  have hW : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  rcases hW.eq_or_lt with hzero | hpos
  · have hwi (i : ι) : w i = 0 := by
      have hle : w i ≤ ∑ j, w j := Finset.single_le_sum
        (fun j _ => hw j) (Finset.mem_univ i)
      linarith [hw i]
    simp only [gaussianQuadratic, hwi, zero_mul, Finset.sum_const_zero, mul_zero,
      lt_self_iff_false, Set.ofPred_false, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hn (i : ι) : 0 ≤ w i / (∑ j, w j) := div_nonneg (hw i) hpos.le
    have hsum : ∑ i, w i / (∑ j, w j) = 1 := by
      rw [← Finset.sum_div, div_self hpos.ne']
    have he (ω : ℕ → ℝ) :
        gaussianQuadratic (fun p : ι × Fin s => w p.1 / ∑ j, w j) (fun p => ω (f p)) =
        gaussianQuadratic (fun p : ι × Fin s => w p.1) (fun p => ω (f p)) / (∑ j, w j) := by
      simp only [gaussianQuadratic, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _
      ring
    have h := streamQuadratic_normalized_upper_tail s f hf
      (fun i => w i / (∑ j, w j)) hn hsum η hη0 hη1
    simp only [he, lt_div_iff₀ hpos] at h
    exact h

#assert_trust kernel streamQuadratic_normalized_upper_tail
#assert_trust kernel streamQuadratic_upper_tail
#print axioms streamQuadratic_normalized_upper_tail
#print axioms streamQuadratic_upper_tail
end NLA.Proofs.RE06
