import NLA.Proofs.RE06.PseudoInverseRange

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery MeasureTheory

/-- The finite entrywise product sigma algebra, matching the function-valued
Gaussian block laws. Matrix is a type synonym, so this transport is explicit. -/
instance realMatrixMeasurableSpace (a b : ℕ) :
    MeasurableSpace (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin a → Fin b → ℝ))

instance realMatrixBorelSpace (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → ℝ))

theorem measurable_nonsing_inverse (n : ℕ) :
    Measurable (fun B : Matrix (Fin n) (Fin n) ℝ => B⁻¹) := by
  have hd : Measurable (fun B : Matrix (Fin n) (Fin n) ℝ => B.det) :=
    continuous_id.matrix_det.measurable
  have ha : Measurable (fun B : Matrix (Fin n) (Fin n) ℝ => B.adjugate) :=
    continuous_id.matrix_adjugate.measurable
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using hd.inv.smul ha

theorem measurable_matrix_mul {Ω : Type*} [MeasurableSpace Ω] {a b c : ℕ}
    {A : Ω → Matrix (Fin a) (Fin b) ℝ} {B : Ω → Matrix (Fin b) (Fin c) ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun ω => A ω * B ω) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  simp only [Matrix.mul_apply]
  apply Finset.measurable_sum
  intro k _
  exact ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

theorem measurable_matrix_transpose {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    {A : Ω → Matrix (Fin a) (Fin b) ℝ} (hA : Measurable A) :
    Measurable (fun ω => (A ω).transpose) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp hA)

theorem measurable_full_row_representative (a b : ℕ) :
    Measurable (fun B : Matrix (Fin a) (Fin b) ℝ => B.transpose * (B * B.transpose)⁻¹) := by
  have ht := measurable_matrix_transpose (measurable_id :
    Measurable (fun B : Matrix (Fin a) (Fin b) ℝ => B))
  exact measurable_matrix_mul ht
    ((measurable_nonsing_inverse a).comp (measurable_matrix_mul measurable_id ht))

theorem aemeasurable_actual_of_full_row {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (X : Ω → Matrix (Fin a) (Fin b) ℝ) (hX : Measurable X)
    (hdet : ∀ᵐ ω ∂μ, ((X ω) * (X ω).transpose).det ≠ 0) :
    AEMeasurable (fun ω => pseudoInverse (X ω)) μ := by
  apply ((measurable_full_row_representative a b).comp hX).aemeasurable.congr
  filter_upwards [hdet] with ω hω
  exact (full_row_formula (X ω) hω).symm

#assert_trust kernel measurable_nonsing_inverse
#assert_trust kernel measurable_full_row_representative
#assert_trust kernel aemeasurable_actual_of_full_row
#print axioms aemeasurable_actual_of_full_row
end NLA.Proofs.RE06.Pseudo
