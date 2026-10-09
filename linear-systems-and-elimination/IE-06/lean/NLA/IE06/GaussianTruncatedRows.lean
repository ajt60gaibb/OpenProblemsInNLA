/- Exact finite-row union of the fixed-fiber Gaussian truncation bound.
Root approved the explicit count and threshold before implementation; see reviews/.
-/
import NLA.IE06.GaussianPivotConditioning
import NLA.IE06.KyFan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace NLA.IE06.GaussianTruncatedRows
open GaussianPivotConditioning

/-- Actual squared Euclidean norm of the row-vector product. -/
def rowEnergy {t p : ℕ} (M : Matrix (Fin t) (Fin p) ℝ) (z : Fin t → ℝ) : ℝ :=
  ∑ a : Fin p, (z ᵥ* M) a ^ 2

theorem rowEnergy_eq_quadratic {t p : ℕ} (M : Matrix (Fin t) (Fin p) ℝ)
    (z : Fin t → ℝ) : rowEnergy M z = SubGaussianQuadratic.quadratic M z := by
  simp only [rowEnergy,SubGaussianQuadratic.quadratic,SubGaussianQuadratic.projection,
    Matrix.vecMul,dotProduct,mul_comm]

theorem frobeniusNorm_sq_eq {t p : ℕ} (M : Matrix (Fin t) (Fin p) ℝ) :
    KyFan.frobeniusNorm M^2 = SubGaussianQuadratic.frobeniusSq M := by
  rw [KyFan.frobeniusNorm_sq]
  exact Finset.sum_comm

theorem measurable_rowEnergy {t p : ℕ} (M : Matrix (Fin t) (Fin p) ℝ) :
    Measurable (rowEnergy M) := by
  unfold rowEnergy
  simp only [Matrix.vecMul,dotProduct]
  fun_prop

/-- Single actual restricted row with an explicit larger Frobenius threshold. -/
theorem single_row_tail {t p : ℕ} (T : Mat t) (M : Matrix (Fin t) (Fin p) ℝ)
    {x τ : ℝ} (hx : 0 ≤ x) (hτ : KyFan.frobeniusNorm M^2 ≤ τ) :
    GaussianRestriction.restrictedGaussian (truncationBody T)
      {z | (2+4*x)*τ < rowEnergy M z} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  apply (measure_mono ?_).trans (fiber_quadratic_tail T M x hx)
  intro z hz
  change (2+4*x)*SubGaussianQuadratic.frobeniusSq M < SubGaussianQuadratic.quadratic M z
  rw [← frobeniusNorm_sq_eq,← rowEnergy_eq_quadratic]
  exact (mul_le_mul_of_nonneg_left hτ (by linarith)).trans_lt hz

/-- Exact marginal of any row of the finite product of normalized restrictions. -/
theorem coordinate_tail {ι : Type*} [Fintype ι] {t p : ℕ} (T : Mat t)
    (M : Matrix (Fin t) (Fin p) ℝ) {x τ : ℝ}
    (hx : 0 ≤ x) (hτ : KyFan.frobeniusNorm M^2 ≤ τ) (i : ι) :
    (Measure.pi (fun _ : ι => GaussianRestriction.restrictedGaussian (truncationBody T)))
      {Z | (2+4*x)*τ < rowEnergy M (Z i)} ≤ ENNReal.ofReal (Real.exp (-x)) := by
  classical
  let _ := GaussianRestriction.restrictedGaussian_probability
    (ne_of_gt (truncationBody_mass_pos T))
  have hm : MeasurableSet {z | (2+4*x)*τ < rowEnergy M z} :=
    measurableSet_lt measurable_const (measurable_rowEnergy M)
  have he := (measurePreserving_eval (fun _ : ι =>
    GaussianRestriction.restrictedGaussian (truncationBody T)) i).measure_preimage hm.nullMeasurableSet
  exact he.le.trans (single_row_tail T M hx hτ)

/-- Fixed-fiber B1 bound with exactly the finite number of rows, including zero. -/
theorem rows_tail {ι : Type*} [Fintype ι] {t p : ℕ} (T : Mat t)
    (M : Matrix (Fin t) (Fin p) ℝ) {x τ : ℝ}
    (hx : 0 ≤ x) (hτ : KyFan.frobeniusNorm M^2 ≤ τ) :
    (Measure.pi (fun _ : ι => GaussianRestriction.restrictedGaussian (truncationBody T)))
      {Z | ∃ i : ι, (2+4*x)*τ < ∑ a : Fin p, ((Z i) ᵥ* M) a ^ 2} ≤
      (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-x)) := by
  classical
  have he : {Z : ι → Fin t → ℝ | ∃ i : ι, (2+4*x)*τ < ∑ a : Fin p, ((Z i) ᵥ* M) a ^ 2} =
      ⋃ i : ι, {Z | (2+4*x)*τ < rowEnergy M (Z i)} := by
    ext Z
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,rowEnergy]
  rw [he]
  calc
    _ ≤ ∑ i : ι, (Measure.pi (fun _ : ι =>
      GaussianRestriction.restrictedGaussian (truncationBody T)))
        {Z | (2+4*x)*τ < rowEnergy M (Z i)} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (Real.exp (-x)) :=
      Finset.sum_le_sum (fun i _ => coordinate_tail T M hx hτ i)
    _ = _ := by simp

#assert_trust kernel rowEnergy
#print axioms rowEnergy
#assert_trust kernel rowEnergy_eq_quadratic
#print axioms rowEnergy_eq_quadratic
#assert_trust kernel frobeniusNorm_sq_eq
#print axioms frobeniusNorm_sq_eq
#assert_trust kernel measurable_rowEnergy
#print axioms measurable_rowEnergy
#assert_trust kernel single_row_tail
#print axioms single_row_tail
#assert_trust kernel coordinate_tail
#print axioms coordinate_tail
#assert_trust kernel rows_tail
#print axioms rows_tail
end NLA.IE06.GaussianTruncatedRows
