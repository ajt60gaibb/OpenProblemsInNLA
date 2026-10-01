import Mathlib

/-!
# The analytic weight factor in the supplied construction

This is the source's exact principal-power formula. All three bases of complex
powers lie in the open right half-plane on the open unit disk. Consequently,
the normalizing, reciprocal, and holomorphic identities have no hidden branch
hypotheses. The boundary estimates additionally require `0 < α < 1`.
-/

noncomputable section

namespace ProofProject

/-- The source's inward-correction exponent. -/
def sourceWeightNu (α : ℝ) : ℝ := (1 - α) / 2

/-- The Cayley transform appearing in the source weight factor. -/
def sourceCayley (z : ℂ) : ℂ := (1 + z) / (1 - z)

/-- The actual analytic weight factor, using principal complex powers. -/
def sourceWeightFactor (α : ℝ) (z : ℂ) : ℂ :=
  sourceCayley z ^ ((α / 2 : ℝ) : ℂ) *
    Complex.exp (((α / 4 : ℝ) : ℂ) *
      ((1 - z) ^ ((sourceWeightNu α : ℝ) : ℂ) -
        (1 + z) ^ ((sourceWeightNu α : ℝ) : ℂ)))

lemma sourceWeightNu_pos {α : ℝ} (hα : α < 1) : 0 < sourceWeightNu α := by
  unfold sourceWeightNu
  linarith

lemma sourceWeightNu_lt_half {α : ℝ} (hα : 0 < α) : sourceWeightNu α < 1 / 2 := by
  unfold sourceWeightNu
  linarith

lemma source_one_add_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 + z).re := by
  have hr := (abs_le.mp (Complex.abs_re_le_norm z)).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

lemma source_one_sub_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (1 - z).re := by
  have hr := Complex.re_le_norm z
  simp only [Complex.sub_re, Complex.one_re]
  linarith

lemma source_one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro heq
  have h := source_one_add_re_pos hz
  rw [heq, Complex.zero_re] at h
  exact (lt_irrefl 0) h

lemma source_one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ≠ 0 := by
  intro heq
  have h := source_one_sub_re_pos hz
  rw [heq, Complex.zero_re] at h
  exact (lt_irrefl 0) h

/-- The explicit positive-real-part identity for the Cayley transform. -/
lemma sourceCayley_re (z : ℂ) :
    (sourceCayley z).re = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
  rw [sourceCayley, Complex.div_re, ← add_div]
  congr 1
  simp [Complex.normSq_apply]
  ring

lemma sourceCayley_re_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (sourceCayley z).re := by
  rw [sourceCayley_re]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  · exact Complex.normSq_pos.mpr (source_one_sub_ne_zero hz)

lemma sourceCayley_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : sourceCayley z ≠ 0 :=
  div_ne_zero (source_one_add_ne_zero hz) (source_one_sub_ne_zero hz)

lemma source_one_add_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ∈ Complex.slitPlane :=
  Or.inl (source_one_add_re_pos hz)

lemma source_one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : 1 - z ∈ Complex.slitPlane :=
  Or.inl (source_one_sub_re_pos hz)

lemma sourceCayley_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) : sourceCayley z ∈ Complex.slitPlane :=
  Or.inl (sourceCayley_re_pos hz)

@[simp] lemma sourceCayley_zero : sourceCayley 0 = 1 := by simp [sourceCayley]

@[simp] lemma sourceWeightFactor_zero (α : ℝ) : sourceWeightFactor α 0 = 1 := by
  simp [sourceWeightFactor]

/-- The source weight never vanishes inside the disk. -/
lemma sourceWeightFactor_ne_zero (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    sourceWeightFactor α z ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (sourceCayley_ne_zero hz))
  · exact Complex.exp_ne_zero _

/-- Reflection interchanges the numerator and denominator of the Cayley transform. -/
lemma sourceCayley_neg (z : ℂ) : sourceCayley (-z) = (sourceCayley z)⁻¹ := by
  simp [sourceCayley, inv_div, sub_eq_add_neg]

/-- Reciprocal symmetry under the exact branch condition, also usable on
the unit circle away from its exceptional endpoints. -/
lemma sourceWeightFactor_neg_of_mem_slitPlane (α : ℝ) {z : ℂ}
    (hz : sourceCayley z ∈ Complex.slitPlane) :
    sourceWeightFactor α (-z) = (sourceWeightFactor α z)⁻¹ := by
  rw [sourceWeightFactor, sourceCayley_neg,
    Complex.inv_cpow _ _ (Complex.slitPlane_arg_ne_pi hz)]
  simp only [sub_neg_eq_add, ← sub_eq_add_neg]
  have harg : ((α / 4 : ℝ) : ℂ) *
      ((1 + z) ^ ((sourceWeightNu α : ℝ) : ℂ) - (1 - z) ^ ((sourceWeightNu α : ℝ) : ℂ)) =
      -(((α / 4 : ℝ) : ℂ) *
        ((1 - z) ^ ((sourceWeightNu α : ℝ) : ℂ) - (1 + z) ^ ((sourceWeightNu α : ℝ) : ℂ))) := by ring
  rw [harg, Complex.exp_neg, sourceWeightFactor, mul_inv]

/-- The exact reciprocal symmetry throughout the open disk. -/
lemma sourceWeightFactor_neg (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    sourceWeightFactor α (-z) = (sourceWeightFactor α z)⁻¹ :=
  sourceWeightFactor_neg_of_mem_slitPlane α (sourceCayley_mem_slitPlane hz)

lemma sourceCayley_conj (z : ℂ) : sourceCayley (starRingEnd ℂ z) =
    starRingEnd ℂ (sourceCayley z) := by
  simp [sourceCayley]

/-- Conjugation symmetry with branch assumptions displayed explicitly. -/
lemma sourceWeightFactor_conj_of_mem_slitPlane (α : ℝ) {z : ℂ}
    (hc : sourceCayley z ∈ Complex.slitPlane)
    (hm : 1 - z ∈ Complex.slitPlane) (hp : 1 + z ∈ Complex.slitPlane) :
    sourceWeightFactor α (starRingEnd ℂ z) = starRingEnd ℂ (sourceWeightFactor α z) := by
  have hpow (w : ℂ) (a : ℝ) (hw : w ∈ Complex.slitPlane) :
      (starRingEnd ℂ w) ^ (a : ℂ) = starRingEnd ℂ (w ^ (a : ℂ)) := by
    simpa using Complex.conj_cpow w (a : ℂ) (Complex.slitPlane_arg_ne_pi hw)
  have hminus : 1 - starRingEnd ℂ z = starRingEnd ℂ (1 - z) := by simp
  have hplus : 1 + starRingEnd ℂ z = starRingEnd ℂ (1 + z) := by simp
  rw [sourceWeightFactor, sourceCayley_conj, hminus, hplus,
    hpow _ _ hc, hpow _ _ hm, hpow _ _ hp]
  simp only [sourceWeightFactor, map_mul, map_sub, Complex.conj_ofReal, ← Complex.exp_conj]

lemma sourceWeightFactor_conj (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    sourceWeightFactor α (starRingEnd ℂ z) = starRingEnd ℂ (sourceWeightFactor α z) :=
  sourceWeightFactor_conj_of_mem_slitPlane α (sourceCayley_mem_slitPlane hz)
    (source_one_sub_mem_slitPlane hz) (source_one_add_mem_slitPlane hz)

/-- Holomorphy at every point of the open disk, with branch conditions explicit. -/
lemma differentiableAt_sourceWeightFactor (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (sourceWeightFactor α) z := by
  have hadd : DifferentiableAt ℂ (fun w : ℂ => 1 + w) z := by fun_prop
  have hsub : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hc : DifferentiableAt ℂ sourceCayley z :=
    hadd.div hsub (source_one_sub_ne_zero hz)
  exact (hc.cpow_const (sourceCayley_mem_slitPlane hz)).mul
    (((hsub.cpow_const (source_one_sub_mem_slitPlane hz)).sub
      (hadd.cpow_const (source_one_add_mem_slitPlane hz))).const_mul _).cexp

lemma differentiableOn_sourceWeightFactor (α : ℝ) :
    DifferentiableOn ℂ (sourceWeightFactor α) (Metric.ball 0 1) := by
  intro z hz
  exact (differentiableAt_sourceWeightFactor α (by simpa using hz)).differentiableWithinAt

/-- Analyticity on the full open unit disk. -/
lemma analyticOnNhd_sourceWeightFactor (α : ℝ) :
    AnalyticOnNhd ℂ (sourceWeightFactor α) (Metric.ball 0 1) :=
  (differentiableOn_sourceWeightFactor α).analyticOnNhd Metric.isOpen_ball

/-- The reciprocal factor is analytic on the same disk. -/
lemma analyticOnNhd_sourceWeightFactor_inv (α : ℝ) :
    AnalyticOnNhd ℂ (fun z => (sourceWeightFactor α z)⁻¹) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  exact (differentiableOn_sourceWeightFactor α).inv fun z hz =>
    sourceWeightFactor_ne_zero α (by simpa using hz)

end ProofProject
