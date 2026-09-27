import NLA.FR05.Gaussian.GaussianGram
import NLA.FR05.Likelihood.SourceCorrelation
import NLA.FR05.Overlap.Overlap
import Mathlib.Data.Matrix.ColumnRowPartitioned

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix WithLp

namespace NLA.FR05

instance sourceUnitaryPolishSpace (M : ℕ) : PolishSpace (SourceUnitary M) := by
  let : PolishSpace (Matrix (Fin M) (Fin M) ℂ) :=
    inferInstanceAs (PolishSpace (Fin M → Fin M → ℂ))
  exact (isClosed_unitary (R := Matrix (Fin M) (Fin M) ℂ)).polishSpace

def sourcePairColumns {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    Matrix (Fin M) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromCols (sourceTwoFrame hM U) (sourceTwoFrame hM V)

/-- The shared projections have the block Gram matrix from the source. -/
theorem sourcePairColumns_gram {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    (sourcePairColumns hM U V)ᴴ * sourcePairColumns hM U V =
      Matrix.fromBlocks 1 (sourceOverlap hM U V) (sourceOverlap hM U V)ᴴ 1 := by
  simp only [sourcePairColumns, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols, sourceTwoFrame_orthonormal, sourceOverlap,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem charFun_sourcePairProjection {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M)
    (t : EuclideanSpace ℂ (Fin 2 ⊕ Fin 2)) :
    charFun ((standardComplexGaussianTail M).map
      (gaussianMatrixProjection (sourcePairColumns hM U V))) t =
      Complex.exp (-(((star (ofLp t) ⬝ᵥ
        (Matrix.fromBlocks 1 (sourceOverlap hM U V) (sourceOverlap hM U V)ᴴ 1 *ᵥ ofLp t)).re
        / 4 : ℝ) : ℂ)) := by
  rw [charFun_gaussianMatrixProjection_eq_exp, signalEnergy_mulVec_eq_gram,
    sourcePairColumns_gram]

def unpackSourceProjections (z : EuclideanSpace ℂ (Fin 2 ⊕ Fin 2)) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) :=
  (fun j ↦ z (Sum.inl j), fun j ↦ z (Sum.inr j))

theorem continuous_unpackSourceProjections : Continuous unpackSourceProjections :=
  (continuous_pi fun j ↦ PiLp.continuous_apply _ _ (Sum.inl j)).prodMk
    (continuous_pi fun j ↦ PiLp.continuous_apply _ _ (Sum.inr j))

def sourceJointProjectionLaw {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    Measure ((Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
  (standardComplexGaussianTail M).map
    (fun x ↦ (sourceProjectedRow hM U x, sourceProjectedRow hM V x))

theorem measurable_sourceJointProjection {M : ℕ} (hM : 2 ≤ M)
    (U V : SourceUnitary M) :
    Measurable (fun x ↦ (sourceProjectedRow hM U x, sourceProjectedRow hM V x)) :=
  ((continuous_sourceProjectedRow hM).measurable.comp
    (measurable_const.prodMk measurable_id)).prodMk
  ((continuous_sourceProjectedRow hM).measurable.comp
    (measurable_const.prodMk measurable_id))

instance {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    IsProbabilityMeasure (sourceJointProjectionLaw hM U V) := by
  exact Measure.isProbabilityMeasure_map (measurable_sourceJointProjection hM U V).aemeasurable

theorem sourceJointProjectionLaw_eq_map {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    sourceJointProjectionLaw hM U V =
      ((standardComplexGaussianTail M).map
        (gaussianMatrixProjection (sourcePairColumns hM U V))).map unpackSourceProjections := by
  rw [Measure.map_map continuous_unpackSourceProjections.measurable
    (continuous_gaussianMatrixProjection _).measurable]
  rfl

/-- Equal overlaps determine the same joint law, even across ambient dimensions. -/
theorem sourceJointProjectionLaw_eq_of_overlap {M N : ℕ} (hM : 2 ≤ M) (hN : 2 ≤ N)
    (U V : SourceUnitary M) (U' V' : SourceUnitary N)
    (h : sourceOverlap hM U V = sourceOverlap hN U' V') :
    sourceJointProjectionLaw hM U V = sourceJointProjectionLaw hN U' V' := by
  rw [sourceJointProjectionLaw_eq_map, sourceJointProjectionLaw_eq_map]
  congr 1
  apply gaussianMatrixProjection_law_eq_of_gram
  rw [sourcePairColumns_gram, sourcePairColumns_gram, h]

theorem sourcePairKernel_eq_integral_jointLaw {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (U V : SourceUnitary M) :
    sourcePairKernel hM a b U V =
      ∫ z, sourceDensity a M z.1 * sourceDensity b M z.2
        ∂sourceJointProjectionLaw hM U V := by
  have hf : Measurable (fun z : (Fin 2 → ℂ) × (Fin 2 → ℂ) ↦
      sourceDensity a M z.1 * sourceDensity b M z.2) :=
    ((measurable_sourceDensity a M).comp measurable_fst).mul
      ((measurable_sourceDensity b M).comp measurable_snd)
  unfold sourceJointProjectionLaw
  rw [integral_map (measurable_sourceJointProjection hM U V).aemeasurable
    hf.aestronglyMeasurable]
  rfl

/-- All four correlation kernels depend only on the two-by-two overlap. -/
theorem sourcePairKernel_eq_of_overlap {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (U V U' V' : SourceUnitary M)
    (h : sourceOverlap hM U V = sourceOverlap hM U' V') :
    sourcePairKernel hM a b U V = sourcePairKernel hM a b U' V' := by
  rw [sourcePairKernel_eq_integral_jointLaw, sourcePairKernel_eq_integral_jointLaw,
    sourceJointProjectionLaw_eq_of_overlap hM hM U V U' V' h]

theorem sourcePairKernel_factorsThrough {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) :
    Function.FactorsThrough
      (fun p : SourceUnitary M × SourceUnitary M ↦ sourcePairKernel hM a b p.1 p.2)
      (fun p ↦ sourceOverlap hM p.1 p.2) :=
  fun {_ _} h ↦ sourcePairKernel_eq_of_overlap hM a b _ _ _ _ h

/-- Zero extension outside realizable overlaps; values on the support are canonical. -/
def sourceOverlapKernel {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    SourceOverlapMatrix → ℝ :=
  Function.extend (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2)
    (fun p ↦ sourcePairKernel hM a b p.1 p.2) (fun _ ↦ 0)

theorem sourceOverlapKernel_apply {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (U V : SourceUnitary M) :
    sourceOverlapKernel hM a b (sourceOverlap hM U V) = sourcePairKernel hM a b U V :=
  (sourcePairKernel_factorsThrough hM a b).extend_apply (fun _ ↦ 0) (U, V)

theorem sourceOverlapKernel_eq_zero {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (K : SourceOverlapMatrix)
    (hK : K ∉ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦
      sourceOverlap hM p.1 p.2)) :
    sourceOverlapKernel hM a b K = 0 :=
  Function.extend_apply' _ _ K hK

theorem measurable_sourceOverlapKernel {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    Measurable (sourceOverlapKernel hM a b) := by
  let : MeasurableSpace.CountablySeparated SourceOverlapMatrix :=
    inferInstanceAs (MeasurableSpace.CountablySeparated (Fin 2 → Fin 2 → ℂ))
  let : MeasurableSpace.CountablySeparated (Set.range
      (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2)) :=
    MeasurableSpace.Subtype.countablySeparated
  have hr : MeasurableSet (Set.range (fun p : SourceUnitary M × SourceUnitary M ↦
      sourceOverlap hM p.1 p.2)) :=
    (isCompact_range (continuous_sourceOverlap hM)).measurableSet
  apply measurable_of_restrict_of_restrict_compl hr
  · apply (continuous_sourceOverlap hM).measurable.measurable_comp_iff_restrict.mp
    simpa only [Function.comp_def, sourceOverlapKernel_apply] using
      measurable_sourcePairKernel hM a b
  · have heq : (Set.range (fun p : SourceUnitary M × SourceUnitary M ↦
        sourceOverlap hM p.1 p.2))ᶜ.domRestrict (sourceOverlapKernel hM a b) =
        fun _ ↦ (0 : ℝ) := by
      funext K
      exact sourceOverlapKernel_eq_zero hM a b K K.property
    rw [heq]
    exact measurable_const

/-- Equation (3.17), for the concrete source likelihoods and overlap law. -/
theorem source_second_moment_eq_overlap_integral {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) :
    (∫ A, sourceLikelihood hM (sourceDensity a M) A *
      sourceLikelihood hM (sourceDensity b M) A
      ∂standardComplexGaussianFrame (sourceRowCount M) M) =
      ∫ K, sourceOverlapKernel hM a b K ^ sourceRowCount M ∂sourceOverlapLaw M hM := by
  rw [source_second_moment_eq_pair_kernel]
  unfold sourceOverlapLaw
  rw [integral_map (continuous_sourceOverlap hM).measurable.aemeasurable
    ((measurable_sourceOverlapKernel hM a b).pow_const _).aestronglyMeasurable]
  simp only [sourceOverlapKernel_apply]

theorem integrable_sourceOverlapKernel_pow {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) (N : ℕ) :
    Integrable (fun K ↦ sourceOverlapKernel hM a b K ^ N) (sourceOverlapLaw M hM) := by
  unfold sourceOverlapLaw
  apply (integrable_map_measure
    ((measurable_sourceOverlapKernel hM a b).pow_const N).aestronglyMeasurable
    (continuous_sourceOverlap hM).measurable.aemeasurable).mpr
  simpa only [Function.comp_def, sourceOverlapKernel_apply] using
    integrable_sourcePairKernel_pow hM a b N

theorem integral_sourceOverlapLaw {M : ℕ} (hM : 2 ≤ M)
    {f : SourceOverlapMatrix → ℝ} (hf : Measurable f) :
    (∫ K, f K ∂sourceOverlapLaw M hM) =
      ∫ p : SourceUnitary M × SourceUnitary M, f (sourceOverlap hM p.1 p.2)
        ∂(sourceUnitaryLaw M).prod (sourceUnitaryLaw M) :=
  integral_map (continuous_sourceOverlap hM).measurable.aemeasurable hf.aestronglyMeasurable

/-- The exact overlap integral to be estimated in Proposition 3.2. -/
theorem sourceLikelihoodL2_eq_overlap_integral (M : ℕ) (hM : 2 ≤ M) :
    sourceLikelihoodL2 M hM =
      ∫ K, (sourceOverlapKernel hM .planted .planted K ^ sourceRowCount M +
        sourceOverlapKernel hM .reference .reference K ^ sourceRowCount M) -
        2 * sourceOverlapKernel hM .planted .reference K ^ sourceRowCount M
        ∂sourceOverlapLaw M hM := by
  have hf : Measurable (fun K ↦
      (sourceOverlapKernel hM .planted .planted K ^ sourceRowCount M +
        sourceOverlapKernel hM .reference .reference K ^ sourceRowCount M) -
        2 * sourceOverlapKernel hM .planted .reference K ^ sourceRowCount M) :=
    (((measurable_sourceOverlapKernel hM .planted .planted).pow_const _).add
      ((measurable_sourceOverlapKernel hM .reference .reference).pow_const _)).sub
      (((measurable_sourceOverlapKernel hM .planted .reference).pow_const _).const_mul _)
  rw [integral_sourceOverlapLaw hM hf]
  simpa only [sourceOverlapKernel_apply] using sourceLikelihoodL2_eq_pair_integral M hM

theorem sourceLikelihoodL2_le_overlap_differences (M : ℕ) (hM : 2 ≤ M) :
    sourceLikelihoodL2 M hM ≤
      (∫ K, |sourceOverlapKernel hM .planted .planted K ^ sourceRowCount M -
        sourceOverlapKernel hM .reference .reference K ^ sourceRowCount M|
        ∂sourceOverlapLaw M hM) +
      2 * (∫ K, |sourceOverlapKernel hM .planted .reference K ^ sourceRowCount M -
        sourceOverlapKernel hM .reference .reference K ^ sourceRowCount M|
        ∂sourceOverlapLaw M hM) := by
  have hf (a b : SourceDensityKind) : Measurable (fun K ↦
      |sourceOverlapKernel hM a b K ^ sourceRowCount M -
        sourceOverlapKernel hM .reference .reference K ^ sourceRowCount M|) :=
    (((measurable_sourceOverlapKernel hM a b).pow_const _).sub
      ((measurable_sourceOverlapKernel hM .reference .reference).pow_const _)).abs
  rw [integral_sourceOverlapLaw hM (hf .planted .planted),
    integral_sourceOverlapLaw hM (hf .planted .reference)]
  simpa only [sourceOverlapKernel_apply] using sourceLikelihoodL2_le_pair_differences M hM

end NLA.FR05
