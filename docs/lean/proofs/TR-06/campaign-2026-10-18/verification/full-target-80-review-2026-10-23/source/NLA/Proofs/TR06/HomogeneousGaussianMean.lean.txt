/-
Copyright (c) 2026. Released under Apache 2.0 license.
The p=0 and p=1 consequences for the actual Gaussian measure and numerator.
These are support gates; tensor annular bounds and locus correspondences remain
separate actual-model obligations.
-/
import NLA.Proofs.TR06.HomogeneousGaussian

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal NNReal Pointwise
open MeasureTheory Set
namespace NLA.Proofs.TR06.HomogeneousGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] in
theorem measurable_gaussian : Measurable (gaussian : E → ℝ≥0∞) := by
  unfold gaussian
  fun_prop

/-- Positive actual annular volume forces a positive Gaussian normalizer. -/
theorem gaussian_normalizer_pos (k : ℕ) {C : Set E}
    (hpos : 0 < (μHE[k] : Measure E) (annulus C)) :
    0 < ∫⁻ x in C, gaussian x ∂(μHE[k] : Measure E) := by
  rw [setLIntegral_pos_iff measurable_gaussian]
  have hs : Function.support (gaussian : E → ℝ≥0∞) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (gaussian_pos x).ne'
  rw [hs, Set.univ_inter]
  exact hpos.trans_le (measure_mono (fun _ hx => hx.1))

/-- Finite annular Hausdorff volume gives a finite actual Gaussian normalizer. -/
theorem gaussian_normalizer_lt_top {k : ℕ} (hk : 0 < k)
    {C : Set E} (hC : MeasurableSet C) (hcone : PositiveCone C)
    (hzero : (0 : E) ∉ C) (hfinite : (μHE[k] : Measure E) (annulus C) < ⊤) :
    (∫⁻ x in C, gaussian x ∂(μHE[k] : Measure E)) < ⊤ := by
  have h := gaussian_lintegral_lt_top k 0 hk hC hcone hzero (fun _ => 1)
    (by intro t ht x hx; simp) (by simpa using hfinite)
  simpa using h

/-- A degree -1 angular function has finite Gaussian numerator whenever its
literal annular integral is finite and the cone dimension exceeds one. -/
theorem gaussian_numerator_lt_top {k : ℕ} (hk : 1 < k)
    {C : Set E} (hC : MeasurableSet C) (hcone : PositiveCone C)
    (hzero : (0 : E) ∉ C) (f : E → ℝ≥0∞)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x ∈ C,
      f (t • x) = (ENNReal.ofReal t)⁻¹ * f x)
    (hfinite : (∫⁻ x in annulus C, f x ∂(μHE[k] : Measure E)) < ⊤) :
    (∫⁻ x in C, f x * gaussian x ∂(μHE[k] : Measure E)) < ⊤ := by
  have hk' : k - 1 + 1 = k := by omega
  have h := gaussian_lintegral_lt_top (k-1) 1 (by omega) hC hcone hzero f
    (by simpa using hhom) (by simpa only [hk'] using hfinite)
  simpa only [hk'] using h

/-- The actual normalized expectation is finite once the annular geometric
inputs are supplied. Every quantity here is its literal Hausdorff integral. -/
theorem finite_gaussian_mean_of_annulus {k : ℕ} (hk : 1 < k)
    {C : Set E} (hC : MeasurableSet C) (hcone : PositiveCone C)
    (hzero : (0 : E) ∉ C) (f : E → ℝ≥0∞)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x ∈ C,
      f (t • x) = (ENNReal.ofReal t)⁻¹ * f x)
    (hvolpos : 0 < (μHE[k] : Measure E) (annulus C))
    (hvolfinite : (μHE[k] : Measure E) (annulus C) < ⊤)
    (hfinite : (∫⁻ x in annulus C, f x ∂(μHE[k] : Measure E)) < ⊤) :
    let Z := ∫⁻ x in C, gaussian x ∂(μHE[k] : Measure E)
    0 < Z ∧ Z < ⊤ ∧
      (∫⁻ x in C, f x * gaussian x ∂(μHE[k] : Measure E)) / Z < ⊤ := by
  dsimp only
  have hZpos := gaussian_normalizer_pos k hvolpos
  have hZfin := gaussian_normalizer_lt_top (by omega : 0 < k) hC hcone hzero hvolfinite
  refine ⟨hZpos, hZfin, ?_⟩
  exact ENNReal.div_lt_top
    (gaussian_numerator_lt_top hk hC hcone hzero f hhom hfinite).ne hZpos.ne'

#print axioms measurable_gaussian
#print axioms gaussian_normalizer_pos
#print axioms gaussian_normalizer_lt_top
#print axioms gaussian_numerator_lt_top
#print axioms finite_gaussian_mean_of_annulus
#assert_trust kernel measurable_gaussian
#assert_trust kernel gaussian_normalizer_pos
#assert_trust kernel gaussian_normalizer_lt_top
#assert_trust kernel gaussian_numerator_lt_top
#assert_trust kernel finite_gaussian_mean_of_annulus
end NLA.Proofs.TR06.HomogeneousGaussian
