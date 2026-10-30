import NLA.Proofs.RE06.PseudoInverseTikhonovLimit

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

theorem measurable_tikhonov (a b : ℕ) (t : ℝ) :
    Measurable (fun B : Matrix (Fin a) (Fin b) ℝ => tikhonov B t) := by
  have ht := measurable_matrix_transpose (measurable_id :
    Measurable (fun B : Matrix (Fin a) (Fin b) ℝ => B))
  have hg : Measurable (fun B : Matrix (Fin a) (Fin b) ℝ =>
      B * B.transpose + t • (1 : Matrix (Fin a) (Fin a) ℝ)) := by
    have hm := measurable_matrix_mul (measurable_id :
      Measurable (fun B : Matrix (Fin a) (Fin b) ℝ => B)) ht
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    change Measurable (fun B : Matrix (Fin a) (Fin b) ℝ =>
      (B * B.transpose) i j + (t • (1 : Matrix (Fin a) (Fin a) ℝ)) i j)
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hm)).add measurable_const
  exact measurable_matrix_mul ht ((measurable_nonsing_inverse a).comp hg)

/-- The actual SVD-defined Moore–Penrose matrix is globally Borel measurable.
This does not claim measurability of the arbitrary selected singular bases. -/
theorem measurable_actual (a b : ℕ) :
    Measurable (fun B : Matrix (Fin a) (Fin b) ℝ => pseudoInverse B) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_of_tendsto_metrizable (fun n =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_tikhonov a b (regularizationParameter n))))
  apply tendsto_pi_nhds.mpr
  intro B
  exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tikhonov_tendsto B) i) j

theorem aemeasurable_actual {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (X : Ω → Matrix (Fin a) (Fin b) ℝ) (hX : AEMeasurable X μ) :
    AEMeasurable (fun ω => pseudoInverse (X ω)) μ :=
  (measurable_actual a b).comp_aemeasurable hX

#assert_trust kernel measurable_actual
#assert_trust kernel aemeasurable_actual
#print axioms measurable_actual
end NLA.Proofs.RE06.Pseudo
