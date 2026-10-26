import NLA.Proofs.RE06.GaussianMomentInverse

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment
open NLA.Computation.NonadaptiveMatrixQuery

theorem pseudoinverse_frobeniusSq_measurable (d p : ℕ) :
    Measurable (fun x : (Fin d × Fin p) → ℝ =>
      Pseudo.frobeniusSq (pseudoInverse (entryMatrix x))) := by
  have hm := (Pseudo.measurable_actual d p).comp (entryMatrix_measurable d p)
  unfold Pseudo.frobeniusSq
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)).pow_const 2

theorem pseudoinverse_frobeniusSq_integrable_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d p : ℕ) (hdp : d + 1 < p) (X : Ω → (Fin d × Fin p) → ℝ)
    (hX : HasLaw X (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) P) :
    Integrable (fun ω => Pseudo.frobeniusSq (pseudoInverse (entryMatrix (X ω)))) P := by
  have hi : Integrable (fun x : (Fin d × Fin p) → ℝ =>
      Pseudo.frobeniusSq (pseudoInverse (entryMatrix x))) (P.map X) := by
    rw [hX.map_eq]
    exact pseudoinverse_frobeniusSq_integrable d p hdp
  exact hi.comp_aemeasurable hX.aemeasurable

theorem pseudoinverse_frobeniusSq_integral_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (d p : ℕ) (hdp : d + 1 < p) (X : Ω → (Fin d × Fin p) → ℝ)
    (hX : HasLaw X (Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1)) P) :
    (∫ ω, Pseudo.frobeniusSq (pseudoInverse (entryMatrix (X ω))) ∂P) =
      (d : ℝ) / ((p : ℝ) - (d : ℝ) - 1) := by
  exact (hX.integral_comp (pseudoinverse_frobeniusSq_integrable d p hdp).aestronglyMeasurable).trans
    (pseudoinverse_frobeniusSq_integral d p hdp)

theorem stream_block_pseudoinverse_frobeniusSq_integrable (d p offset : ℕ)
    (hdp : d + 1 < p) :
    Integrable (fun ω => Pseudo.frobeniusSq (pseudoInverse (gaussianBlock d p offset ω)))
      GaussianLaw :=
  pseudoinverse_frobeniusSq_integrable_of_hasLaw _ d p hdp _
    (gaussianBlock_entries_hasLaw d p offset)

theorem stream_block_pseudoinverse_frobeniusSq_integral (d p offset : ℕ)
    (hdp : d + 1 < p) :
    (∫ ω, Pseudo.frobeniusSq (pseudoInverse (gaussianBlock d p offset ω)) ∂GaussianLaw) =
      (d : ℝ) / ((p : ℝ) - (d : ℝ) - 1) :=
  pseudoinverse_frobeniusSq_integral_of_hasLaw _ d p hdp _
    (gaussianBlock_entries_hasLaw d p offset)

end NLA.Proofs.RE06.GaussianMoment
