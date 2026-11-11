import NLA.Proofs.RE06.OrthogonalCompletion
import NLA.Proofs.RE06.RepairMeasurable

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

def rotateEntries {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (q : ℕ)
    (x : Fin n × Fin q → ℝ) : Fin n × Fin q → ℝ :=
  fun p => (O.transpose*Matrix.of (fun i j => x (i,j))) p.1 p.2

theorem measurable_rotateEntries {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (q : ℕ) :
    Measurable (rotateEntries O q) := by
  apply measurable_pi_lambda
  intro p
  simp only [rotateEntries, Matrix.mul_apply, Matrix.of_apply]
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (measurable_pi_apply (i,p.2))

theorem actual_gaussian_rotated_entries_hasLaw {n : ℕ}
    (O : Matrix (Fin n) (Fin n) ℝ) (hO : O*O.transpose=1) (q : ℕ) :
    HasLaw (fun ω => rotateEntries O q (fun p => gaussianBlock n q 0 ω p.1 p.2))
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) GaussianLaw := by
  have ho : O.transpose.transpose*O.transpose=1 := by
    simpa only [Matrix.transpose_transpose] using hO
  have h := gaussianBlock_rotated_entries_hasLaw n q 0
    (fun _ => orthogonalEuclidean n O.transpose ho)
  convert h using 1
  funext ω p
  have he := congrFun (orthogonalEuclidean_apply n O.transpose ho
    (WithLp.toLp 2 (fun i : Fin n => gaussianBlock n q 0 ω i p.2))) p.1
  exact he.symm

theorem hasLaw_fixed_gaussian_rotation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (hO : O*O.transpose=1) (q : ℕ) (X : Ω → (Fin n × Fin q → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) μ) :
    HasLaw (fun ω => rotateEntries O q (X ω))
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) μ :=
  HasLaw.comp_of_hasLaw_comp (measurable_rotateEntries O q).aemeasurable
    (gaussianBlock_entries_hasLaw n q 0) hX (actual_gaussian_rotated_entries_hasLaw O hO q)

#assert_trust kernel measurable_rotateEntries
#assert_trust kernel actual_gaussian_rotated_entries_hasLaw
#assert_trust kernel hasLaw_fixed_gaussian_rotation
#print axioms hasLaw_fixed_gaussian_rotation
end NLA.Proofs.RE06.Repair
