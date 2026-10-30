import NLA.Proofs.RE05.RegressionOffset
import NLA.Proofs.RE05.BasisProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

theorem measuredLeft_eq_trace {n : ℕ} (plan : Plan n) (A B : Square n) :
    (∑ h : Fin plan.selected.length,
      dot (A.transpose *ᵥ uColumn plan h) (B.transpose *ᵥ uColumn plan h)) =
      (((B.transpose * planFrame plan).transpose) * (A.transpose * planFrame plan)).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, dot, planFrame]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem measuredLeft_inner_selected {n : ℕ} (plan : Plan n) (A B : Square n) :
    (∑ h : Fin plan.selected.length,
      dot (A.transpose *ᵥ uColumn plan h) (B.transpose *ᵥ uColumn plan h)) =
      NLA.Computation.LinearFamilyQuery.inner A (selectedProjection plan * B) := by
  rw [measuredLeft_eq_trace, matrix_inner_trace, selectedProjection,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    ((planFrame plan).transpose * B * (A.transpose * planFrame plan)).trace =
        ((planFrame plan).transpose * B * A.transpose * planFrame plan).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A.transpose * planFrame plan * ((planFrame plan).transpose * B)).trace :=
      (Matrix.trace_mul_cycle A.transpose (planFrame plan)
        ((planFrame plan).transpose * B)).symm
    _ = _ := by simp only [Matrix.mul_assoc]

theorem measuredLeft_inner_projection {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) (A B : Square n) :
    (∑ h : Fin plan.selected.length,
      dot (A.transpose *ᵥ uColumn plan h) (B.transpose *ᵥ uColumn plan h)) =
      NLA.Computation.LinearFamilyQuery.inner (selectedProjection plan * A)
        (selectedProjection plan * B) := by
  rw [measuredLeft_inner_selected, matrix_inner_trace, matrix_inner_trace]
  have hm : (selectedProjection plan * A).transpose * (selectedProjection plan * B) =
      A.transpose * (selectedProjection plan * B) := by
    rw [Matrix.transpose_mul, (selectedProjection_symmetric plan).eq]
    calc
      A.transpose * selectedProjection plan * (selectedProjection plan * B) =
          A.transpose * ((selectedProjection plan * selectedProjection plan) * B) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [selectedProjection_idempotent plan hF]
  rw [hm]

theorem dot_mulVec_quadratic {n : ℕ} (A B : Square n) (g : Fin n → ℝ) :
    dot (A *ᵥ g) (B *ᵥ g) = dot g ((A.transpose * B) *ᵥ g) := by
  change (A *ᵥ g) ⬝ᵥ (B *ᵥ g) = g ⬝ᵥ ((A.transpose * B) *ᵥ g)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem dot_quadratic_eq_sum {n : ℕ} (M : Square n) (g : Fin n → ℝ) :
    dot g (M *ᵥ g) = ∑ i : Fin n, ∑ j : Fin n, M i j * g i * g j := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact quadratic matrix of an actual residual-basis rhs coordinate. -/
def offsetQuadraticMatrix {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : Square n) (j : Fin (q + 1)) : Square n :=
  (residualBasisBlock P plan j).transpose * (residualProjection plan * R)

/-- The actual residual projector is fixed before every random draw/copy. -/
theorem makePlan_residualProjection_eq {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω ω' : ℕ → ℝ) (copy copy' : Fin 15) :
    residualProjection (makePlan P ξ ω copy) = residualProjection (makePlan P ξ ω' copy') := rfl

/-- The actual quadratic matrix is deterministic when its residual is fixed. -/
theorem makePlan_offsetQuadraticMatrix_eq {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω ω' : ℕ → ℝ) (copy copy' : Fin 15) (R : Square n) (j : Fin (q + 1)) :
    offsetQuadraticMatrix P (makePlan P ξ ω copy) R j =
      offsetQuadraticMatrix P (makePlan P ξ ω' copy') R j := rfl

theorem offsetQuadraticMatrix_trace {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : Square n) (j : Fin (q + 1)) :
    (offsetQuadraticMatrix P plan R j).trace =
      NLA.Computation.LinearFamilyQuery.inner (residualBasisBlock P plan j)
        (residualProjection plan * R) := (matrix_inner_trace _ _).symm

theorem actualResidualOffset_centered_unscaled {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) (j : Fin (q + 1))
    (hOrth : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) R = 0) :
    regressionOffset (orthonormalMember P) (makePlan P ξ ω copy) R j =
      (1 / ((makePlan P ξ ω copy).s : ℝ)) *
        (∑ g : Fin (makePlan P ξ ω copy).s,
          dot (fun k => (makePlan P ξ ω copy).G k g)
            (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j *ᵥ
              (fun k => (makePlan P ξ ω copy).G k g))) -
        (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j).trace := by
  let plan := makePlan P ξ ω copy
  have hF := makePlan_frame_gram P ξ ω copy
  have hsplit := projection_matrix_inner_split plan hF (orthonormalMember P j) R
  rw [hOrth] at hsplit
  have hleft : NLA.Computation.LinearFamilyQuery.inner
      (selectedProjection plan * orthonormalMember P j) (selectedProjection plan * R) =
      -(offsetQuadraticMatrix P plan R j).trace := by
    rw [offsetQuadraticMatrix_trace]
    change NLA.Computation.LinearFamilyQuery.inner
      (selectedProjection plan * orthonormalMember P j) (selectedProjection plan * R) =
      -NLA.Computation.LinearFamilyQuery.inner (residualProjection plan * orthonormalMember P j)
        (residualProjection plan * R)
    linarith
  have hquad (g : Fin plan.s) :
      dot (complement plan (orthonormalMember P j *ᵥ (fun k => plan.G k g)))
        (complement plan (R *ᵥ (fun k => plan.G k g))) =
      dot (fun k => plan.G k g) (offsetQuadraticMatrix P plan R j *ᵥ (fun k => plan.G k g)) := by
    simp only [complement_eq_mulVec, Matrix.mulVec_mulVec]
    exact dot_mulVec_quadratic _ _ _
  unfold regressionOffset rhs
  simp only [observedLeft_planAnswers, observedRight_planAnswers]
  change (∑ h : Fin plan.selected.length,
      dot ((orthonormalMember P j).transpose *ᵥ uColumn plan h) (R.transpose *ᵥ uColumn plan h)) +
    (1 / (plan.s : ℝ)) * ∑ g : Fin plan.s,
      dot (complement plan (orthonormalMember P j *ᵥ (fun k => plan.G k g)))
        (complement plan (R *ᵥ (fun k => plan.G k g))) = _
  rw [measuredLeft_inner_projection plan hF, hleft]
  simp only [hquad]
  ring

theorem gaussianWidth_positive (q : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    0 < gaussianWidth q ξ := by
  have hl : 0 < Real.log (20 * (q + 1 : ℕ)) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 20 * (q + 1) by omega)
  have hB : 0 < baseWidth q ξ := by unfold baseWidth; positivity
  have ht : 0 ≤ threshold q ξ := Real.sqrt_nonneg _
  apply Nat.ceil_pos.mpr
  exact add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hl) (mul_nonneg ht hB.le)

/-- The actual rhs coordinate is an average of centered finite quadratics,
on the same original plan and its same true residual answers. -/
theorem actualResidualOffset_centered {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (hξ : 0 < ξ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n)
    (j : Fin (q + 1))
    (hOrth : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) R = 0) :
    regressionOffset (orthonormalMember P) (makePlan P ξ ω copy) R j =
      (1 / ((makePlan P ξ ω copy).s : ℝ)) *
        ∑ g : Fin (makePlan P ξ ω copy).s,
          (dot (fun k => (makePlan P ξ ω copy).G k g)
            (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j *ᵥ
              (fun k => (makePlan P ξ ω copy).G k g)) -
            (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j).trace) := by
  rw [actualResidualOffset_centered_unscaled P ξ ω copy R j hOrth,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : ((makePlan P ξ ω copy).s : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussianWidth_positive q ξ hξ)
  field_simp [hs]

end NLA.Proofs.RE05
