import ProofProject.SourcePhasePolar
import ProofProject.SourceMomentDefs

/-!
# Radial limits of the exact source weight factor

At every boundary angle other than `0` and `±π`, all three principal-power
bases avoid the logarithm cut. Ordinary pointwise continuity therefore supplies
the radial limits used in dominated convergence; no boundary theorem for Hardy
spaces is assumed.
-/

noncomputable section

open Filter MeasureTheory Topology

namespace ProofProject

lemma sourceCircle_sin_ne_zero {θ : ℝ} (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    Real.sin θ ≠ 0 := by
  rcases lt_or_gt_of_ne (abs_pos.mp hθ0) with hneg | hpos
  · have hs : 0 < Real.sin (-θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by simpa only [abs_of_neg hneg] using hθπ)
    rw [Real.sin_neg] at hs
    linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi hpos
      (by simpa only [abs_of_pos hpos] using hθπ)).ne'

lemma one_add_sourceCircle_mem_slitPlane_abs {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    1 + sourceCircle θ ∈ Complex.slitPlane := by
  apply Or.inr
  simpa using sourceCircle_sin_ne_zero hθ0 hθπ

lemma one_sub_sourceCircle_mem_slitPlane_abs {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    1 - sourceCircle θ ∈ Complex.slitPlane := by
  apply Or.inr
  simpa using sourceCircle_sin_ne_zero hθ0 hθπ

lemma sourceCayley_sourceCircle_mem_slitPlane_abs {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    sourceCayley (sourceCircle θ) ∈ Complex.slitPlane := by
  apply Or.inr
  rw [sourceCayley_sourceCircle_im]
  exact div_ne_zero (mul_ne_zero (by norm_num) (sourceCircle_sin_ne_zero hθ0 hθπ))
    (Complex.normSq_pos.mpr (Complex.slitPlane_ne_zero
      (one_sub_sourceCircle_mem_slitPlane_abs hθ0 hθπ))).ne'

/-- The exact weight formula is continuous wherever its principal-power
bases lie in the slit plane. -/
lemma continuousAt_sourceWeightFactor_of_mem_slitPlane (α : ℝ) {z : ℂ}
    (hc : sourceCayley z ∈ Complex.slitPlane)
    (hm : 1 - z ∈ Complex.slitPlane) (hp : 1 + z ∈ Complex.slitPlane) :
    ContinuousAt (sourceWeightFactor α) z := by
  have hadd : ContinuousAt (fun w : ℂ => 1 + w) z := by fun_prop
  have hsub : ContinuousAt (fun w : ℂ => 1 - w) z := by fun_prop
  have hcay : ContinuousAt sourceCayley z :=
    hadd.div hsub (Complex.slitPlane_ne_zero hm)
  exact ((continuousAt_cpow_const hc).comp hcay).mul
    (Complex.continuous_exp.continuousAt.comp
      ((((continuousAt_cpow_const hm).comp hsub).sub
        ((continuousAt_cpow_const hp).comp hadd)).const_mul _))

/-- Boundary continuity holds on both open semicircles, for every real α. -/
lemma continuousAt_sourceWeightFactor_circle (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    ContinuousAt (sourceWeightFactor α) (sourceCircle θ) :=
  continuousAt_sourceWeightFactor_of_mem_slitPlane α
    (sourceCayley_sourceCircle_mem_slitPlane_abs hθ0 hθπ)
    (one_sub_sourceCircle_mem_slitPlane_abs hθ0 hθπ)
    (one_add_sourceCircle_mem_slitPlane_abs hθ0 hθπ)

lemma sourceRadius_pos (n : ℕ) : 0 < sourceRadius n := by
  have hden : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hsmall : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one hden).mpr (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  unfold sourceRadius
  linarith

lemma sourceRadius_lt_one (n : ℕ) : sourceRadius n < 1 := by
  unfold sourceRadius
  have hfrac : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  linarith

lemma tendsto_sourceRadius : Tendsto sourceRadius atTop (𝓝 (1 : ℝ)) := by
  have hg : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hg
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 : ℝ))
  simpa only [sub_zero] using tendsto_const_nhds.sub hinv

lemma norm_sourceRadius_mul_sourceCircle_lt_one (n : ℕ) (θ : ℝ) :
    ‖(sourceRadius n : ℂ) * sourceCircle θ‖ < 1 := by
  rw [norm_mul, norm_sourceCircle, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sourceRadius_pos n)]
  exact sourceRadius_lt_one n

lemma tendsto_sourceRadius_mul_sourceCircle (θ : ℝ) :
    Tendsto (fun n => (sourceRadius n : ℂ) * sourceCircle θ) atTop (𝓝 (sourceCircle θ)) := by
  have hcast : Tendsto (fun n => (sourceRadius n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_sourceRadius
  simpa only [one_mul] using hcast.mul (tendsto_const_nhds (x := sourceCircle θ))

/-- Pointwise radial convergence of the source factor. -/
theorem tendsto_sourceWeightFactor_radial (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    Tendsto (fun n => sourceWeightFactor α ((sourceRadius n : ℂ) * sourceCircle θ)) atTop
      (𝓝 (sourceWeightFactor α (sourceCircle θ))) :=
  (continuousAt_sourceWeightFactor_circle α hθ0 hθπ).tendsto.comp
    (tendsto_sourceRadius_mul_sourceCircle θ)

/-- The same pointwise limit for the analytic square used in the second moment. -/
theorem tendsto_sourceWeightFactor_sq_radial (α : ℝ) {θ : ℝ}
    (hθ0 : 0 < |θ|) (hθπ : |θ| < Real.pi) :
    Tendsto (fun n => sourceWeightFactor α ((sourceRadius n : ℂ) * sourceCircle θ) ^ 2) atTop
      (𝓝 (sourceWeightFactor α (sourceCircle θ) ^ 2)) :=
  (tendsto_sourceWeightFactor_radial α hθ0 hθπ).pow 2

/-- Removing the three exceptional angles gives the required a.e. radial limit
on the full principal angular interval. -/
theorem ae_tendsto_sourceWeightFactor_radial (α : ℝ) :
    ∀ᵐ θ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      Tendsto (fun n => sourceWeightFactor α ((sourceRadius n : ℂ) * sourceCircle θ)) atTop
        (𝓝 (sourceWeightFactor α (sourceCircle θ))) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne 0,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne Real.pi,
    (volume.restrict (Set.Icc (-Real.pi) Real.pi)).ae_ne (-Real.pi)] with θ hθ hθ0 hθπ hθnegπ
  apply tendsto_sourceWeightFactor_radial α (abs_pos.mpr hθ0)
  exact abs_lt.mpr ⟨lt_of_le_of_ne hθ.1 hθnegπ.symm, lt_of_le_of_ne hθ.2 hθπ⟩

/-- A.e. radial convergence of the square, on the same restricted measure. -/
theorem ae_tendsto_sourceWeightFactor_sq_radial (α : ℝ) :
    ∀ᵐ θ ∂volume.restrict (Set.Icc (-Real.pi) Real.pi),
      Tendsto (fun n => sourceWeightFactor α ((sourceRadius n : ℂ) * sourceCircle θ) ^ 2) atTop
        (𝓝 (sourceWeightFactor α (sourceCircle θ) ^ 2)) := by
  filter_upwards [ae_tendsto_sourceWeightFactor_radial α] with θ hθ
  exact hθ.pow 2

end ProofProject
