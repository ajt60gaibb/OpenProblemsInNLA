import NLA.Proofs.RE06.RegressionCoordinates
import NLA.Proofs.RE06.GaussianProductMomentTransport
import NLA.Proofs.RE06.GaussianMomentInverse

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

def regressionCoefficient (d ell : ℕ) (y : Fin d × Fin ell → ℝ) :
    Matrix (Fin d) (Fin ell) ℝ :=
  pseudoInverse (GaussianMoment.entryMatrix y).transpose

theorem regressionCoefficient_measurable (d ell : ℕ) :
    Measurable (regressionCoefficient d ell) :=
  (Pseudo.measurable_actual ell d).comp
    (Pseudo.measurable_matrix_transpose (GaussianMoment.entryMatrix_measurable d ell))

theorem regressionCoefficient_energy (d ell : ℕ) (y : Fin d × Fin ell → ℝ) :
    squaredFrobenius (regressionCoefficient d ell y) 0 =
      Pseudo.frobeniusSq (pseudoInverse (GaussianMoment.entryMatrix y)) := by
  rw [regressionCoefficient, Pseudo.transpose, squaredFrobenius_transpose_zero]
  simp only [squaredFrobenius, Pseudo.frobeniusSq, Matrix.zero_apply, sub_zero]

theorem regressionCoefficient_integrable (d ell : ℕ) (hdell : d+1<ell) :
    Integrable (fun y : Fin d × Fin ell → ℝ => squaredFrobenius
      (regressionCoefficient d ell y) 0)
      (Measure.pi (fun _ : Fin d × Fin ell => gaussianReal 0 1)) := by
  simpa only [regressionCoefficient_energy] using
    GaussianMoment.pseudoinverse_frobeniusSq_integrable d ell hdell

theorem regressionCoefficient_integral (d ell : ℕ) (hdell : d+1<ell) :
    (∫ y : Fin d × Fin ell → ℝ, squaredFrobenius (regressionCoefficient d ell y) 0
      ∂Measure.pi (fun _ : Fin d × Fin ell => gaussianReal 0 1)) =
        (d:ℝ)/((ell:ℝ)-(d:ℝ)-1) := by
  simpa only [regressionCoefficient_energy] using
    GaussianMoment.pseudoinverse_frobeniusSq_integral d ell hdell

def transposeEntries (a b : ℕ) (x : Fin a × Fin b → ℝ) : Fin b × Fin a → ℝ :=
  fun p => x (p.2,p.1)

theorem measurable_transposeEntries (a b : ℕ) : Measurable (transposeEntries a b) := by
  apply measurable_pi_lambda
  intro p
  exact measurable_pi_apply (p.2,p.1)

theorem transposeEntries_hasLaw (a b : ℕ) :
    HasLaw (transposeEntries a b)
      (Measure.pi (fun _ : Fin b × Fin a => gaussianReal 0 1))
      (Measure.pi (fun _ : Fin a × Fin b => gaussianReal 0 1)) := by
  exact (measurePreserving_piCongrLeft
    (fun _ : Fin b × Fin a => gaussianReal 0 1) (Equiv.prodComm (Fin a) (Fin b))).hasLaw

#assert_trust kernel regressionCoefficient_measurable
#assert_trust kernel regressionCoefficient_energy
#assert_trust kernel regressionCoefficient_integrable
#assert_trust kernel regressionCoefficient_integral
#assert_trust kernel measurable_transposeEntries
#assert_trust kernel transposeEntries_hasLaw
#print axioms regressionCoefficient_integral
end NLA.Proofs.RE06.Repair
