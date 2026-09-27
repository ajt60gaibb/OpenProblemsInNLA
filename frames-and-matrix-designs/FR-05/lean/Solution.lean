/-
The unconditional FR-05 bound and limit, with supporting checked exports.
-/
import NLA.FR05.Proof

set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal Topology
noncomputable section

namespace NLA.FR05

/-- Li's Theorem 1.4, for the original iid complex-Gaussian frame law and
the original all-signals phase-retrieval injectivity predicate. -/
theorem phaseRetrieval_injective_probability_le_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
      phaseRetrievalProbability d ≤ C / d := by
  exact phaseRetrieval_injective_probability_le_inv_proved

/-- The original FR-05 target: injectivity probability tends to zero at
the measurement count `4d - 5`. -/
theorem phaseRetrieval_injective_probability_tendsto_zero :
    Filter.Tendsto phaseRetrievalProbability Filter.atTop (𝓝 0) := by
  exact phaseRetrieval_injective_probability_tendsto_zero_proved

theorem explicit_noninjective_frame (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  exact explicit_noninjective_frame_proved d hd

/-- The exact iid planted-frame law used in the source's Proposition 3.1
factors through the checked deterministic planted-row construction. -/
theorem source_planted_frame_law_representation {M : ℕ} (hM : 1 ≤ M) :
    sourcePlantedFrameLawAt M =
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceRowCount M) (sourceTailDimension M)).map
        (fun p => plantedFrame (sourceRowsFromCoordinates p)) := by
  exact sourcePlantedFrameLawAt_eq_viaPlantedRows hM

/-- The radial coordinate of the source's planted law has the explicit
exponential tail used in its norm event. -/
theorem source_planted_radial_tail {M : ℕ} (hM : 1 ≤ M) :
    sourceRadialLaw sourceEta (sourceDelta M) (Set.Ici (8 * (M : ℝ))) ≤
      (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
  exact sourceRadialLaw_sourceM_apply_Ici_le hM

/-- The source's conditioned radial sampler is exactly the radial density
appearing in the planted two-coordinate law. -/
theorem source_planted_radial_density {M : ℕ} (hM : 1 ≤ M) :
    sourceRadialLaw sourceEta (sourceDelta M) =
      (volume.restrict (Set.Ici (sourceDelta M))).withDensity
        (fun s ↦ ENNReal.ofReal (plantedRadiusDensity M s)) := by
  exact sourceRadialLaw_sourceEta_eq_density hM

/-- The source sampler's entire planted column equals the two-coordinate
density law (3.1), together with its independent Gaussian tail. -/
theorem source_planted_column_density_head_tail {M n : ℕ} (hM : 1 ≤ M) :
    sourcePlantedColumnLaw sourceEta (sourceDelta M) (sourceEpsilon M) n =
      ((sourceDensityLaw .planted M).prod (standardComplexGaussianTail n)).map
        sourceHeadTailJoin := by
  exact sourcePlantedColumnLaw_eq_density_head_tail hM

/-- The full Haar-mixed planted sampler has the literal likelihood (3.5)
relative to the original Gaussian frame law, after the dimension relabelling. -/
theorem source_haar_planted_frame_law_eq_likelihood {M : ℕ} (hM : 2 ≤ M) :
    (sourceHaarPlantedFrameLawAt M).map (sourceFrameAtDimension hM) =
      (standardComplexGaussianFrame (sourceRowCount M) M).withDensity
        (fun A ↦ ENNReal.ofReal (sourcePlantedLikelihood hM A)) := by
  exact sourceHaarPlantedFrameLawAt_eq_likelihood hM

/-- The Haar-oriented reference Gaussian deformation has the literal
reference likelihood (3.5) relative to the original Gaussian frame law. -/
theorem source_reference_frame_law_eq_likelihood {M : ℕ} (hM : 2 ≤ M) :
    sourceHaarReferenceFrameLawAt M hM =
      (standardComplexGaussianFrame (sourceRowCount M) M).withDensity
        (fun A ↦ ENNReal.ofReal (sourceReferenceLikelihood hM A)) := by
  exact sourceHaarReferenceFrameLawAt_eq_likelihood hM

/-- Reference reweighting preserves the exact all-signals injectivity
probability, because its Gaussian deformation is invertible. -/
theorem source_reference_injective_probability {M : ℕ} (hM : 2 ≤ M) :
    ((standardComplexGaussianFrame (sourceRowCount M) M).withDensity
      (fun A ↦ ENNReal.ofReal (sourceReferenceLikelihood hM A))).real
        {A | PhaseRetrievalInjective A} = phaseRetrievalProbability M := by
  exact sourceReferenceLikelihood_injective_probability hM

/-- The reference likelihood integrates to the original injectivity
probability on the injectivity event. -/
theorem source_reference_injective_integral {M : ℕ} (hM : 2 ≤ M) :
    (∫ A in {A | PhaseRetrievalInjective A}, sourceReferenceLikelihood hM A
      ∂standardComplexGaussianFrame (sourceRowCount M) M) = phaseRetrievalProbability M := by
  exact integral_sourceReferenceLikelihood_injective hM

theorem likelihood_l2_bound_of_second_moment_estimates
    {Ω : ℕ → Type*} [∀ M, MeasurableSpace (Ω M)]
    (μ : ∀ M, Measure (Ω M)) (Lg Lr : ∀ M, Ω M → ℝ)
    (D : ℕ) (C : ℝ)
    (hcomparisons : ∀ M : ℕ, D ≤ M →
      Integrable (fun ω ↦ Lg M ω * Lg M ω) (μ M) ∧
      Integrable (fun ω ↦ Lr M ω * Lr M ω) (μ M) ∧
      Integrable (fun ω ↦ Lg M ω * Lr M ω) (μ M) ∧
      |(∫ ω, Lg M ω * Lg M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M ∧
      |(∫ ω, Lg M ω * Lr M ω ∂μ M) -
        (∫ ω, Lr M ω * Lr M ω ∂μ M)| ≤ C / M) :
    ∀ M : ℕ, D ≤ M →
      (∫ ω, (Lg M ω - Lr M ω) ^ 2 ∂μ M) ≤ 3 * C / M := by
  exact eventual_likelihood_l2_le_of_second_moment_comparisons_proved
    μ Lg Lr D C hcomparisons

#print axioms proposition_3_1
#print axioms proposition_3_1_haar
#print axioms proposition_3_2
#print axioms explicit_noninjective_frame
#print axioms source_planted_frame_law_representation
#print axioms source_planted_radial_tail
#print axioms source_planted_radial_density
#print axioms source_planted_column_density_head_tail
#print axioms source_haar_planted_frame_law_eq_likelihood
#print axioms source_reference_frame_law_eq_likelihood
#print axioms source_reference_injective_probability
#print axioms source_reference_injective_integral
#print axioms likelihood_l2_bound_of_second_moment_estimates
#print axioms phaseRetrieval_injective_probability_le_inv_of_source_comparison
#print axioms phaseRetrieval_probability_le_planted_add_sqrt
#print axioms phaseRetrieval_injective_probability_le_inv
#print axioms phaseRetrieval_injective_probability_tendsto_zero

end NLA.FR05
