import NLA.Proofs.RE06.GaussianMomentPolynomialNull
import NLA.Proofs.RE06.PseudoInverseRankEvents
import NLA.Proofs.RE06.GaussianStream

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace NLA.Proofs.RE06.GaussianMoment

def entryMatrix {d p : ℕ} (x : Fin d × Fin p → ℝ) : Matrix (Fin d) (Fin p) ℝ :=
  fun i j => x (i, j)

def variableMatrix (d p : ℕ) : Matrix (Fin d) (Fin p) (MvPolynomial (Fin d × Fin p) ℝ) :=
  fun i j => MvPolynomial.X (i, j)

def gramDetPolynomial (d p : ℕ) : MvPolynomial (Fin d × Fin p) ℝ :=
  (variableMatrix d p * (variableMatrix d p).transpose).det

theorem eval_gramDetPolynomial (d p : ℕ) (x : Fin d × Fin p → ℝ) :
    MvPolynomial.eval x (gramDetPolynomial d p) =
      (entryMatrix x * (entryMatrix x).transpose).det := by
  unfold gramDetPolynomial
  rw [(MvPolynomial.eval x).map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.mul_apply, variableMatrix, entryMatrix]

theorem gramDetPolynomial_ne_zero (d p : ℕ) (hdp : d ≤ p) : gramDetPolynomial d p ≠ 0 := by
  let W : Matrix (Fin d) (Fin p) ℝ := fun i j => if j = Fin.castLE hdp i then 1 else 0
  have hW : W * W.transpose = 1 := by
    ext i j
    simp [W, Matrix.mul_apply, Matrix.one_apply]
  have he : MvPolynomial.eval (fun ij => W ij.1 ij.2) (gramDetPolynomial d p) = 1 := by
    rw [eval_gramDetPolynomial]
    change (W * W.transpose).det = 1
    rw [hW, Matrix.det_one]
  intro hz
  rw [hz, map_zero] at he
  norm_num at he

theorem gaussian_gram_det_ne_zero_ae (d p : ℕ) (hdp : d ≤ p) :
    ∀ᵐ x : Fin d × Fin p → ℝ
      ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1),
      (entryMatrix x * (entryMatrix x).transpose).det ≠ 0 := by
  have h := mvPolynomial_fintype_eval_ne_zero_ae (gramDetPolynomial d p)
    (gramDetPolynomial_ne_zero d p hdp)
  filter_upwards [h] with x hx
  simpa only [eval_gramDetPolynomial] using hx

theorem gaussian_surjective_ae (d p : ℕ) (hdp : d ≤ p) :
    ∀ᵐ x : Fin d × Fin p → ℝ
      ∂Measure.pi (fun _ : Fin d × Fin p => gaussianReal 0 1),
      Function.Surjective (entryMatrix x).mulVec := by
  filter_upwards [gaussian_gram_det_ne_zero_ae d p hdp] with x hx
  exact (Pseudo.gram_det_ne_zero_iff_surjective (entryMatrix x)).mp hx

theorem stream_block_gram_det_ne_zero_ae (d p offset : ℕ) (hdp : d ≤ p) :
    ∀ᵐ ω ∂NLA.Computation.NonadaptiveMatrixQuery.GaussianLaw,
      (gaussianBlock d p offset ω * (gaussianBlock d p offset ω).transpose).det ≠ 0 := by
  have hm : Measurable (fun x : Fin d × Fin p → ℝ =>
      (entryMatrix x * (entryMatrix x).transpose).det ≠ 0) := by
    have hc : Continuous (fun x : Fin d × Fin p → ℝ => entryMatrix x) := by
      apply continuous_matrix
      intro i j
      exact continuous_apply (i, j)
    exact measurableSet_setOfPred.mp
      (isOpen_ne_fun ((hc.matrix_mul hc.matrix_transpose).matrix_det) continuous_const).measurableSet
  exact ((gaussianBlock_entries_hasLaw d p offset).ae_iff hm).mpr
    (gaussian_gram_det_ne_zero_ae d p hdp)

#assert_trust kernel gramDetPolynomial_ne_zero
#assert_trust kernel gaussian_gram_det_ne_zero_ae
#assert_trust kernel gaussian_surjective_ae
#assert_trust kernel stream_block_gram_det_ne_zero_ae
#print axioms stream_block_gram_det_ne_zero_ae
end NLA.Proofs.RE06.GaussianMoment
