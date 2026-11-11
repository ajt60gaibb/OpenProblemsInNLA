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

theorem gaussian_regression_split_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n : ℕ} (O : Matrix (Fin n) (Fin n) ℝ) (hO : O*O.transpose=1)
    (d ell : ℕ) (hd : d ≤ n) (X : Ω → (Fin n × Fin ell → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1)) μ) :
    HasLaw (fun ω =>
      (gaussianHeadEntries n d ell hd (rotateEntries O ell (X ω)),
        transposeEntries (n-d) ell (gaussianTailEntries n d ell hd (rotateEntries O ell (X ω)))))
      ((Measure.pi (fun _ : Fin d × Fin ell => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : Fin ell × Fin (n-d) => gaussianReal 0 1))) μ := by
  have hRot := hasLaw_fixed_gaussian_rotation μ O hO ell X hX
  have hSplit := hasLaw_gaussian_row_split μ n d ell hd _ hRot
  have hTrans := ((MeasurePreserving.id
      (Measure.pi (fun _ : Fin d × Fin ell => gaussianReal 0 1))).prod
    ((transposeEntries_hasLaw (n-d) ell).measurePreserving
      (measurable_transposeEntries (n-d) ell))).hasLaw
  exact hTrans.fun_comp hSplit

/-- The exact fixed-range regression moment under the genuine Gaussian law,
with every dimension and the orthogonality condition explicit. -/
theorem gaussian_regression_energy_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n d c ell : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (hd : d ≤ n) (R : Matrix (Fin n) (Fin c) ℝ)
    (hR : Q.transpose*R=0) (hdell : d+1<ell)
    (X : Ω → (Fin n × Fin ell → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1)) μ) :
    Integrable (fun ω => squaredFrobenius
      (pseudoInverse ((Matrix.of (fun i j => X ω (i,j))).transpose*Q)*
        ((Matrix.of (fun i j => X ω (i,j))).transpose*R)) 0) μ ∧
      (∫ ω, squaredFrobenius
        (pseudoInverse ((Matrix.of (fun i j => X ω (i,j))).transpose*Q)*
          ((Matrix.of (fun i j => X ω (i,j))).transpose*R)) 0 ∂μ) =
        ((d:ℝ)/((ell:ℝ)-(d:ℝ)-1))*squaredFrobenius R 0 := by
  obtain ⟨O,hOg,hOc,hOE⟩ := exists_orthogonal_completion Q hQ hd
  let ν := Measure.pi (fun _ : Fin d × Fin ell => gaussianReal 0 1)
  let U := regressionCoefficient d ell
  let T := tailCoefficients O d hd R
  let Y := fun ω => gaussianHeadEntries n d ell hd (rotateEntries O ell (X ω))
  let Z := fun ω => transposeEntries (n-d) ell
    (gaussianTailEntries n d ell hd (rotateEntries O ell (X ω)))
  have hU : ∀ i l, Measurable (fun y => U y i l) := fun i l =>
    (measurable_pi_apply l).comp ((measurable_pi_apply i).comp (regressionCoefficient_measurable d ell))
  have hV : ∀ k j, Measurable (fun _ : Fin d × Fin ell → ℝ => T k j) :=
    fun _ _ => measurable_const
  have henergy : Integrable (fun y => squaredFrobenius (U y) 0*squaredFrobenius T 0) ν :=
    (regressionCoefficient_integrable d ell hdell).mul_const _
  have hJoint := gaussian_regression_split_law μ O hOc d ell hd X hX
  have hInt := hasLaw_gaussian_product_fubini_integrable ν U (fun _ => T)
    hU hV henergy Y Z hJoint
  have hVal := hasLaw_gaussian_product_fubini_integral ν U (fun _ => T)
    hU hV henergy Y Z hJoint
  have hUeq (ω : Ω) : U (Y ω) =
      pseudoInverse ((Matrix.of (fun i j => X ω (i,j))).transpose*Q) := by
    exact congrArg pseudoInverse (regression_head_coordinates O hd Q hOE (X ω))
  have hReq (ω : Ω) : (Matrix.of (fun i j => X ω (i,j))).transpose*R =
      Matrix.of (fun i j => Z ω (i,j))*T :=
    regression_tail_coordinates O hOc hd Q hOE R hR (X ω)
  have hEq (ω : Ω) : squaredFrobenius
      (pseudoInverse ((Matrix.of (fun i j => X ω (i,j))).transpose*Q)*
        ((Matrix.of (fun i j => X ω (i,j))).transpose*R)) 0 =
      squaredFrobenius (U (Y ω)*Matrix.of (fun i j => Z ω (i,j))*T) 0 := by
    rw [hUeq, hReq]
    simp only [Matrix.mul_assoc]
  refine ⟨hInt.congr (ae_of_all _ (fun ω => (hEq ω).symm)),?_⟩
  rw [integral_congr_ae (ae_of_all _ hEq), hVal, integral_mul_const]
  change (∫ y, squaredFrobenius (regressionCoefficient d ell y) 0 ∂ν)*
    squaredFrobenius T 0=_
  rw [regressionCoefficient_integral d ell hdell,
    tailCoefficients_energy O hOc hd Q hOE R hR]

#assert_trust kernel gaussian_regression_split_law
#assert_trust kernel gaussian_regression_energy_moment
#print axioms gaussian_regression_energy_moment
end NLA.Proofs.RE06.Repair
