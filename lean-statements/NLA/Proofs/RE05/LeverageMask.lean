import NLA.Proofs.RE05.ComplementProjection
import NLA.Proofs.RE05.PositiveSVDColumns

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
open scoped BigOperators Matrix

def leverageFrame {n q : ℕ} (P : Basis n q) : Square n :=
  (NLA.Computation.NonadaptiveMatrixQuery.exactSVD (leverage P)).U

def leverageSingularValues {n q : ℕ} (P : Basis n q) : Fin n → ℝ :=
  squareSingularValues (NLA.Computation.NonadaptiveMatrixQuery.exactSVD (leverage P)).sigma

def selectedMask {n q : ℕ} (P : Basis n q) (ξ : ℝ) (j : Fin n) : ℝ :=
  if threshold q ξ < leverageSingularValues P j then 1 else 0

def residualMask {n q : ℕ} (P : Basis n q) (ξ : ℝ) (j : Fin n) : ℝ :=
  if threshold q ξ < leverageSingularValues P j then 0 else 1

theorem validSVD_left_gram {n : ℕ} {B U V : Square n}
    {sigma : Fin (min n n) → ℝ} (h : ValidSVD B U sigma V) : U.transpose * U = 1 := by
  ext i j
  exact h.1 i j

theorem leverageFrame_gram {n q : ℕ} (P : Basis n q) :
    (leverageFrame P).transpose * leverageFrame P = 1 :=
  validSVD_left_gram (svd_total n n (leverage P))

theorem leverageFrame_cogram {n q : ℕ} (P : Basis n q) :
    leverageFrame P * (leverageFrame P).transpose = 1 :=
  mul_eq_one_comm.mp (leverageFrame_gram P)

theorem frame_conjugate_mul {n : ℕ} (U : Square n) (hU : U.transpose * U = 1)
    (A B : Square n) :
    (U * A * U.transpose) * (U * B * U.transpose) = U * (A * B) * U.transpose := by
  calc
    (U * A * U.transpose) * (U * B * U.transpose) =
        U * (A * ((U.transpose * U) * B)) * U.transpose := by
      simp only [Matrix.mul_assoc]
    _ = U * (A * B) * U.transpose := by rw [hU]; simp

theorem makePlan_sum_selected {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (f : Fin n → ℝ) :
    (∑ h : Fin (makePlan P ξ ω copy).selected.length,
      f (makePlan P ξ ω copy).selected[h]) =
      ∑ j : Fin n, if threshold q ξ < leverageSingularValues P j then f j else 0 := by
  let l := (makePlan P ξ ω copy).selected
  have hl : l.Nodup := makePlan_selected_nodup P ξ ω copy
  change (∑ h : Fin l.length, f l[h.val]) = _
  rw [Fin.sum_univ_fun_getElem, ← List.sum_toFinset f hl]
  have hs : l.toFinset = Finset.univ.filter
      (fun j => threshold q ξ < leverageSingularValues P j) := by
    simp [l, makePlan, leverageSingularValues, squareSingularValues]
    rfl
  rw [hs, Finset.sum_filter]

/-- The actual selected lookup projector is the corresponding diagonal mask
in the full U returned by the actual exact SVD. -/
theorem makePlan_selectedProjection_mask {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedProjection (makePlan P ξ ω copy) =
      leverageFrame P * Matrix.diagonal (selectedMask P ξ) * (leverageFrame P).transpose := by
  ext i k
  change (∑ h : Fin (makePlan P ξ ω copy).selected.length,
    leverageFrame P i (makePlan P ξ ω copy).selected[h] *
      leverageFrame P k (makePlan P ξ ω copy).selected[h]) = _
  erw [makePlan_sum_selected P ξ ω copy (fun j => leverageFrame P i j * leverageFrame P k j)]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, selectedMask]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem residualMask_diagonal {n q : ℕ} (P : Basis n q) (ξ : ℝ) :
    Matrix.diagonal (residualMask P ξ) = 1 - Matrix.diagonal (selectedMask P ξ) := by
  rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext j
  simp only [residualMask, selectedMask]
  split_ifs <;> norm_num

theorem makePlan_residualProjection_mask {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (makePlan P ξ ω copy) =
      leverageFrame P * Matrix.diagonal (residualMask P ξ) * (leverageFrame P).transpose := by
  rw [residualMask_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    leverageFrame_cogram]
  unfold residualProjection
  rw [makePlan_selectedProjection_mask]

theorem leverage_diagonalization {n q : ℕ} (P : Basis n q) :
    leverage P = leverageFrame P * Matrix.diagonal (leverageSingularValues P) *
      (leverageFrame P).transpose :=
  validSVD_posSemidef_diagonalization (svd_total n n (leverage P)) (leverage_posSemidef P)

theorem makePlan_residualProjection_posSemidef {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (residualProjection (makePlan P ξ ω copy)).PosSemidef := by
  rw [makePlan_residualProjection_mask]
  have hd : (Matrix.diagonal (residualMask P ξ)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => by unfold residualMask; split_ifs <;> norm_num)
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (leverageFrame P)

end NLA.Proofs.RE05
