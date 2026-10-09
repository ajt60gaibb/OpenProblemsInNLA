import Mathlib.Analysis.Fourier.AddCircle

/-!
# Finite Hilbert-valued Parseval on the normalized circle

Only finite character orthogonality is used. The vector space need not be
complete: all integrals used in the identity are real or complex valued.
The period is one and `AddCircle.haarAddCircle` has total mass one.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

universe u v

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma continuous_finset_fourier_smul (s : Finset ℤ) (a : ℤ → H) :
    Continuous (fun z : AddCircle (1 : ℝ) => ∑ q ∈ s, fourier q z • a q) :=
  continuous_finsetSum s fun q _ => (fourier q).continuous.smul continuous_const

/-- The finite Fourier polynomial itself is integrable, even without a
completeness assumption on its target space. -/
lemma integrable_finset_fourier_smul (s : Finset ℤ) (a : ℤ → H) :
    Integrable (fun z : AddCircle (1 : ℝ) => ∑ q ∈ s, fourier q z • a q)
      AddCircle.haarAddCircle := by
  simpa only [MeasureTheory.integrableOn_univ] using
    (continuous_finset_fourier_smul s a).continuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle) isCompact_univ

lemma integrable_finset_fourier_smul_norm_sq (s : Finset ℤ) (a : ℤ → H) :
    Integrable (fun z : AddCircle (1 : ℝ) => ‖∑ q ∈ s, fourier q z • a q‖ ^ 2)
      AddCircle.haarAddCircle := by
  simpa only [MeasureTheory.integrableOn_univ] using
    ((continuous_finset_fourier_smul s a).norm.fun_pow 2).continuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle) isCompact_univ

/-- Scalar character orthogonality with Mathlib's conjugation convention. -/
lemma finiteCircle_character_inner (i j : ℤ) :
    (∫ z : AddCircle (1 : ℝ), fourier j z * starRingEnd ℂ (fourier i z)
      ∂AddCircle.haarAddCircle) = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) i j
  rwa [ContinuousMap.inner_toLp] at h

lemma integrable_fourier_smul_inner (i j : ℤ) (a b : H) :
    Integrable (fun z : AddCircle (1 : ℝ) =>
      inner ℂ (fourier i z • a) (fourier j z • b)) AddCircle.haarAddCircle := by
  have hc : Continuous (fun z : AddCircle (1 : ℝ) =>
      inner ℂ (fourier i z • a) (fourier j z • b)) :=
    ((fourier i).continuous.smul continuous_const).inner
      ((fourier j).continuous.smul continuous_const)
  simpa only [MeasureTheory.integrableOn_univ] using
    hc.continuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle) isCompact_univ

lemma finiteCircle_integral_smul_inner (i j : ℤ) (a b : H) :
    (∫ z : AddCircle (1 : ℝ), inner ℂ (fourier i z • a) (fourier j z • b)
      ∂AddCircle.haarAddCircle) = if i = j then inner ℂ a b else 0 := by
  calc
    _ = ∫ z : AddCircle (1 : ℝ),
        (fourier j z * starRingEnd ℂ (fourier i z)) * inner ℂ a b
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ)]
        ring
    _ = (∫ z : AddCircle (1 : ℝ), fourier j z * starRingEnd ℂ (fourier i z)
        ∂AddCircle.haarAddCircle) * inner ℂ a b := integral_mul_const _ _
    _ = _ := by rw [finiteCircle_character_inner]; split_ifs <;> simp

/-- Finite vector-valued character orthogonality, before taking real parts. -/
theorem finiteCircle_integral_inner (s : Finset ℤ) (a b : ℤ → H) :
    (∫ z : AddCircle (1 : ℝ),
      inner ℂ (∑ q ∈ s, fourier q z • a q) (∑ q ∈ s, fourier q z • b q)
        ∂AddCircle.haarAddCircle) = ∑ q ∈ s, inner ℂ (a q) (b q) := by
  simp_rw [sum_inner, inner_sum]
  rw [integral_finsetSum s (fun i _ => integrable_finsetSum s fun j _ =>
    integrable_fourier_smul_inner i j (a i) (b j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum s (fun j _ => integrable_fourier_smul_inner i j (a i) (b j))]
  simp_rw [finiteCircle_integral_smul_inner]
  simp [hi]

/-- Genuine finite Parseval for arbitrary complex inner-product spaces, with
normalized Haar measure and no completeness assumption on `H`. -/
theorem finiteCircleParseval (s : Finset ℤ) (a : ℤ → H) :
    (∫ z : AddCircle (1 : ℝ), ‖∑ q ∈ s, fourier q z • a q‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ q ∈ s, ‖a q‖ ^ 2 := by
  have hi : Integrable (fun z : AddCircle (1 : ℝ) =>
      inner ℂ (∑ q ∈ s, fourier q z • a q) (∑ q ∈ s, fourier q z • a q))
      AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.integrableOn_univ] using
      ((continuous_finset_fourier_smul s a).inner
        (continuous_finset_fourier_smul s a)).continuousOn.integrableOn_compact
          (μ := AddCircle.haarAddCircle) isCompact_univ
  have h := congrArg (RCLike.re : ℂ → ℝ) (finiteCircle_integral_inner s a a)
  rw [← integral_re hi] at h
  simpa only [map_sum, inner_self_eq_norm_sq] using h

/-- Every circle character has unit pointwise norm. -/
lemma finiteCircle_fourier_norm (q : ℤ) (z : AddCircle (1 : ℝ)) : ‖fourier q z‖ = 1 :=
  Circle.norm_coe _

/-- The finite-family form allows arbitrary distinct integer frequencies,
including the reversed frequencies used in the weighted transference. -/
theorem finiteCircleParseval_indexed {ι : Type v} [Fintype ι]
    (k : ι → ℤ) (hk : Function.Injective k) (a : ι → H) :
    (∫ z : AddCircle (1 : ℝ), ‖∑ j, fourier (k j) z • a j‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hc : Continuous (fun z : AddCircle (1 : ℝ) => ∑ j, fourier (k j) z • a j) :=
    continuous_finsetSum Finset.univ fun j _ => (fourier (k j)).continuous.smul continuous_const
  have hi : Integrable (fun z : AddCircle (1 : ℝ) =>
      inner ℂ (∑ j, fourier (k j) z • a j) (∑ j, fourier (k j) z • a j))
      AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.integrableOn_univ] using
      (hc.inner hc).continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  have hinner : (∫ z : AddCircle (1 : ℝ),
      inner ℂ (∑ j, fourier (k j) z • a j) (∑ j, fourier (k j) z • a j)
        ∂AddCircle.haarAddCircle) = ∑ j, inner ℂ (a j) (a j) := by
    simp_rw [sum_inner, inner_sum]
    rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ fun j _ =>
      integrable_fourier_smul_inner (k i) (k j) (a i) (a j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Finset.univ (fun j _ =>
      integrable_fourier_smul_inner (k i) (k j) (a i) (a j))]
    simp_rw [finiteCircle_integral_smul_inner, hk.eq_iff]
    simp
  have h := congrArg (RCLike.re : ℂ → ℝ) hinner
  rw [← integral_re hi] at h
  simpa only [map_sum, inner_self_eq_norm_sq] using h

end ProofProject
