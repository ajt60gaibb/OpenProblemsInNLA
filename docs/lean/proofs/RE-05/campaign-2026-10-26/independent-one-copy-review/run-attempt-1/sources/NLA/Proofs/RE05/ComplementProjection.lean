import NLA.Proofs.RE05.SelectedCharge

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix

/-- Exactly the columns looked up by the model's `uColumn`. -/
def planFrame {n : ℕ} (plan : Plan n) : Matrix (Fin n) (Fin plan.selected.length) ℝ :=
  fun i h => uColumn plan h i

def selectedProjection {n : ℕ} (plan : Plan n) : Square n :=
  planFrame plan * (planFrame plan).transpose

def residualProjection {n : ℕ} (plan : Plan n) : Square n :=
  1 - selectedProjection plan

theorem projection_add_residual {n : ℕ} (plan : Plan n) :
    selectedProjection plan + residualProjection plan = 1 := by
  unfold residualProjection
  abel

theorem selectedProjection_symmetric {n : ℕ} (plan : Plan n) :
    (selectedProjection plan).IsSymm := by
  change (planFrame plan * (planFrame plan).transpose).transpose =
    planFrame plan * (planFrame plan).transpose
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem residualProjection_symmetric {n : ℕ} (plan : Plan n) :
    (residualProjection plan).IsSymm := by
  change (1 - selectedProjection plan).transpose = 1 - selectedProjection plan
  rw [Matrix.transpose_sub, Matrix.transpose_one, (selectedProjection_symmetric plan).eq]

/-- Entrywise equality with the actual model complement, for every plan. -/
theorem complement_eq_mulVec {n : ℕ} (plan : Plan n) (x : Fin n → ℝ) :
    complement plan x = residualProjection plan *ᵥ x := by
  rw [residualProjection, Matrix.sub_mulVec, Matrix.one_mulVec, selectedProjection,
    ← Matrix.mulVec_mulVec]
  ext i
  simp only [complement, Matrix.mulVec, Matrix.transpose_apply, dotProduct, Pi.sub_apply,
    planFrame, dot]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem complement_selfAdjoint {n : ℕ} (plan : Plan n) (x y : Fin n → ℝ) :
    dot (complement plan x) y = dot x (complement plan y) := by
  simp only [complement_eq_mulVec, dot]
  change (residualProjection plan *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (residualProjection plan *ᵥ y)
  calc
    (residualProjection plan *ᵥ x) ⬝ᵥ y = y ⬝ᵥ (residualProjection plan *ᵥ x) :=
      dotProduct_comm _ _
    _ = x ⬝ᵥ ((residualProjection plan).transpose *ᵥ y) :=
      (Matrix.dotProduct_transpose_mulVec _ _ _).symm
    _ = x ⬝ᵥ (residualProjection plan *ᵥ y) := by
      rw [(residualProjection_symmetric plan).eq]

theorem makePlan_selected_nodup {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (makePlan P ξ ω copy).selected.Nodup :=
  (List.nodup_finRange n).filter _

theorem makePlan_frame_gram {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (planFrame (makePlan P ξ ω copy)).transpose * planFrame (makePlan P ξ ω copy) = 1 := by
  let plan := makePlan P ξ ω copy
  have hI (a b : Fin plan.selected.length) : (plan.selected[a] = plan.selected[b]) ↔ a = b := by
    constructor
    · intro hab
      apply Fin.ext
      exact (makePlan_selected_nodup P ξ ω copy).getElem_inj_iff.mp hab
    · rintro rfl
      rfl
  ext a b
  change (∑ i : Fin n, plan.U i plan.selected[a] * plan.U i plan.selected[b]) =
    if a = b then 1 else 0
  have h : (∑ i : Fin n, plan.U i plan.selected[a] * plan.U i plan.selected[b]) =
      if plan.selected[a] = plan.selected[b] then 1 else 0 :=
    (svd_total n n (leverage P)).1 plan.selected[a] plan.selected[b]
  rw [h]
  simp only [hI]

theorem selectedProjection_idempotent {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    selectedProjection plan * selectedProjection plan = selectedProjection plan := by
  unfold selectedProjection
  calc
    (planFrame plan * (planFrame plan).transpose) *
        (planFrame plan * (planFrame plan).transpose) =
      planFrame plan * (((planFrame plan).transpose * planFrame plan) *
        (planFrame plan).transpose) := by simp only [Matrix.mul_assoc]
    _ = planFrame plan * (planFrame plan).transpose := by rw [hF]; simp

theorem residualProjection_idempotent {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    residualProjection plan * residualProjection plan = residualProjection plan := by
  unfold residualProjection
  calc
    (1 - selectedProjection plan) * (1 - selectedProjection plan) =
        1 - selectedProjection plan - selectedProjection plan +
          selectedProjection plan * selectedProjection plan := by noncomm_ring
    _ = 1 - selectedProjection plan := by rw [selectedProjection_idempotent plan hF]; abel

theorem makePlan_complement_idempotent {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    complement (makePlan P ξ ω copy) (complement (makePlan P ξ ω copy) x) =
      complement (makePlan P ξ ω copy) x := by
  simp only [complement_eq_mulVec, Matrix.mulVec_mulVec,
    residualProjection_idempotent _ (makePlan_frame_gram P ξ ω copy)]

theorem makePlan_selectedProjection_idempotent {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedProjection (makePlan P ξ ω copy) * selectedProjection (makePlan P ξ ω copy) =
      selectedProjection (makePlan P ξ ω copy) :=
  selectedProjection_idempotent _ (makePlan_frame_gram P ξ ω copy)

theorem makePlan_residualProjection_idempotent {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (makePlan P ξ ω copy) * residualProjection (makePlan P ξ ω copy) =
      residualProjection (makePlan P ξ ω copy) :=
  residualProjection_idempotent _ (makePlan_frame_gram P ξ ω copy)

theorem projection_basis_split {n : ℕ} (plan : Plan n) (E : Square n) :
    selectedProjection plan * E + residualProjection plan * E = E := by
  rw [← Matrix.add_mul, projection_add_residual, Matrix.one_mul]

theorem selected_residual_mul_zero {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    selectedProjection plan * residualProjection plan = 0 := by
  rw [residualProjection, Matrix.mul_sub, Matrix.mul_one, selectedProjection_idempotent plan hF,
    sub_self]

theorem residual_selected_mul_zero {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    residualProjection plan * selectedProjection plan = 0 := by
  rw [residualProjection, Matrix.sub_mul, Matrix.one_mul, selectedProjection_idempotent plan hF,
    sub_self]

end NLA.Proofs.RE05
