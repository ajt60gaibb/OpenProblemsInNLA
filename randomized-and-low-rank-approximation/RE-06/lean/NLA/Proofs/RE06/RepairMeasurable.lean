import NLA.Proofs.RE06.ActualRangeFinder
import NLA.Proofs.RE06.PseudoInverseGlobalMeasurable
import NLA.Proofs.RE06.GaussianRepairSelectionActual

/-! Measurability of actual repair and basis-free excess, without a measurable
choice of singular vectors or an orthonormal basis for a varying range. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem measurable_matrix_sub {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    {X Y : Ω → Matrix (Fin a) (Fin b) ℝ} (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun ω => X ω-Y ω) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hY))

theorem measurable_squaredFrobenius_zero {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    {X : Ω → Matrix (Fin a) (Fin b) ℝ} (hX : Measurable X) :
    Measurable (fun ω => squaredFrobenius (X ω) 0) := by
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero]
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)).pow_const 2

theorem measurable_actualProjector {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    {Y : Ω → Matrix (Fin n) (Fin k) ℝ} (hY : Measurable Y) :
    Measurable (fun ω => actualProjector (Y ω)) :=
  Pseudo.measurable_matrix_mul hY ((Pseudo.measurable_actual n k).comp hY)

theorem measurable_actualRangeResidual {Ω : Type*} [MeasurableSpace Ω] {n k c : ℕ}
    {Y : Ω → Matrix (Fin n) (Fin k) ℝ} (hY : Measurable Y)
    (C : Matrix (Fin n) (Fin c) ℝ) :
    Measurable (fun ω => actualRangeResidual (Y ω) C) :=
  measurable_matrix_sub measurable_const
    (Pseudo.measurable_matrix_mul (measurable_actualProjector hY) measurable_const)

theorem measurable_actualRegressionEnergy {Ω : Type*} [MeasurableSpace Ω]
    {n k c ell : ℕ} {Y : Ω → Matrix (Fin n) (Fin k) ℝ}
    {Ht : Ω → Matrix (Fin ell) (Fin n) ℝ} (hY : Measurable Y) (hHt : Measurable Ht)
    (C : Matrix (Fin n) (Fin c) ℝ) :
    Measurable (fun ω => actualRegressionEnergy (Y ω) C (Ht ω)) := by
  apply measurable_squaredFrobenius_zero
  exact measurable_matrix_sub
    (Pseudo.measurable_matrix_mul (measurable_actualProjector hY) measurable_const)
    (Pseudo.measurable_matrix_mul
      (Pseudo.measurable_matrix_mul hY
        ((Pseudo.measurable_actual ell k).comp (Pseudo.measurable_matrix_mul hHt hY)))
      (Pseudo.measurable_matrix_mul hHt measurable_const))

theorem measurable_tailRandomEnergy {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    {G : Ω → Matrix (Fin n) (Fin k) ℝ} (hG : Measurable G) :
    Measurable (fun ω => tailRandomEnergy C r hr (G ω)) := by
  apply measurable_squaredFrobenius_zero
  exact Pseudo.measurable_matrix_mul
    (Pseudo.measurable_matrix_mul measurable_const
      (Pseudo.measurable_matrix_mul measurable_const hG))
    ((Pseudo.measurable_actual r k).comp
      (Pseudo.measurable_matrix_mul measurable_const hG))

theorem measurable_actualExcessMajorant {Ω : Type*} [MeasurableSpace Ω] {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    {G : Ω → Matrix (Fin n) (Fin k) ℝ} {Ht : Ω → Matrix (Fin ell) (Fin n) ℝ}
    (hG : Measurable G) (hHt : Measurable Ht) :
    Measurable (fun ω => actualExcessMajorant C r hr (G ω) (Ht ω)) :=
  (measurable_tailRandomEnergy C r hr hG).add
    (measurable_actualRegressionEnergy (Pseudo.measurable_matrix_mul measurable_const hG) hHt C)

theorem measurable_repairErrorFromEntries {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (k ell : ℕ) :
    Measurable (repairErrorFromEntries C k ell) := by
  have hG : Measurable (fun p : RepairEntries n k ell =>
      Matrix.of (fun i j => p.1 (i,j))) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (i,j)).comp measurable_fst
  have hH : Measurable (fun p : RepairEntries n k ell =>
      Matrix.of (fun i j => p.2 (i,j))) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact (measurable_pi_apply (i,j)).comp measurable_snd
  have hHt := Pseudo.measurable_matrix_transpose hH
  have hY := Pseudo.measurable_matrix_mul (measurable_const (a:=C)) hG
  exact measurable_matrix_sub measurable_const
    (Pseudo.measurable_matrix_mul
      (Pseudo.measurable_matrix_mul hY
        ((Pseudo.measurable_actual ell k).comp (Pseudo.measurable_matrix_mul hHt hY)))
      (Pseudo.measurable_matrix_mul hHt measurable_const))

theorem measurableSet_repairFailureSet {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (k ell r : ℕ) (η : ℝ) :
    MeasurableSet (repairFailureSet C k ell r η) :=
  measurableSet_lt measurable_const
    (measurable_squaredFrobenius_zero (measurable_repairErrorFromEntries C k ell))

theorem nullMeasurableSet_repairFailureSet {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (k ell r : ℕ) (η : ℝ) :
    NullMeasurableSet (repairFailureSet C k ell r η) (gaussianRepairLaw n k ell) :=
  (measurableSet_repairFailureSet C k ell r η).nullMeasurableSet

#assert_trust kernel measurable_matrix_sub
#assert_trust kernel measurable_squaredFrobenius_zero
#assert_trust kernel measurable_actualProjector
#assert_trust kernel measurable_actualRangeResidual
#assert_trust kernel measurable_actualRegressionEnergy
#assert_trust kernel measurable_tailRandomEnergy
#assert_trust kernel measurable_actualExcessMajorant
#assert_trust kernel measurable_repairErrorFromEntries
#assert_trust kernel measurableSet_repairFailureSet
#assert_trust kernel nullMeasurableSet_repairFailureSet
#print axioms nullMeasurableSet_repairFailureSet
end NLA.Proofs.RE06.Repair
