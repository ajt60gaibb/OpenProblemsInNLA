import NLA.Proofs.TR04.SVDResidual
import NLA.Proofs.TR04.SVDFrameProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators InnerProductSpace
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem orthonormal_matrixColumns {m : ℕ} {U : Matrix (Fin m) (Fin m) ℝ}
    (hU : OrthonormalColumns U) : Orthonormal ℝ (matrixColumn U) := by
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormalColumns hU
  have heq : (b : Fin m → Space m) = matrixColumn U := funext hb
  rw [← heq]
  exact b.orthonormal

theorem orthonormal_selected_singularDirections {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) : Orthonormal ℝ
      (fun k : {k // P k} => matrixColumn U (Fin.castLE (Nat.min_le_left m l) k.val)) := by
  apply (orthonormal_matrixColumns hU).comp
  intro i j hij
  apply Subtype.ext
  exact Fin.ext (congrArg (fun k : Fin m => k.val) hij)

theorem finrank_singularSubspace {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] :
    Module.finrank ℝ (singularSubspace U P) = Fintype.card {k // P k} := by
  exact finrank_span_eq_card (orthonormal_selected_singularDirections hU P).linearIndependent

theorem starProjection_singularSubspace {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] (k : Fin (min m l)) :
    (singularSubspace U P).starProjection
      (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =
        if P k then matrixColumn U (Fin.castLE (Nat.min_le_left m l) k) else 0 := by
  by_cases hk : P k
  · rw [if_pos hk]
    apply (singularSubspace U P).starProjection_eq_self_iff.mpr
    exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  · rw [if_neg hk]
    let x := matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)
    have hL : singularSubspace U P ≤ (innerSL ℝ x).ker := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      change ⟪x, matrixColumn U (Fin.castLE (Nat.min_le_left m l) i.val)⟫_ℝ = 0
      apply (orthonormal_matrixColumns hU).inner_eq_zero
      intro he
      have hki : k = i.val := Fin.ext (congrArg (fun j : Fin m => j.val) he)
      exact hk (hki ▸ i.property)
    apply (singularSubspace U P).starProjection_apply_eq_zero_iff.mpr
    apply ((singularSubspace U P).mem_orthogonal' _).mpr
    intro y hy
    exact hL hy

theorem projectionWeight_singularSubspace {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] (k : Fin (min m l)) :
    projectionWeight (singularSubspace U P) U (Fin.castLE (Nat.min_le_left m l) k) =
      if P k then 1 else 0 := by
  unfold projectionWeight
  rw [starProjection_singularSubspace hU P k]
  split_ifs with hk
  · rw [(orthonormal_matrixColumns hU).norm_eq_one]
    norm_num
  · simp

theorem validSVD_selected_energy {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (P : Fin (min m l) → Prop) [DecidablePred P] :
    matrixEnergy (projectMatrix (singularSubspace U P) B) =
      ∑ k, if P k then (sigma k)^2 else 0 := by
  rw [validSVD_project_energy h]
  apply Finset.sum_congr rfl
  intro k _
  rw [projectionWeight_singularSubspace h.1 P k]
  split_ifs <;> simp

theorem validSVD_selected_error {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (P : Fin (min m l) → Prop) [DecidablePred P] :
    matrixEnergy (B - projectMatrix (singularSubspace U P) B) =
      ∑ k, if P k then 0 else (sigma k)^2 := by
  have hpy := projectMatrix_energy_decomposition (singularSubspace U P) B
  rw [validSVD_energy h, validSVD_selected_energy h] at hpy
  have hsplit : (∑ k, if P k then (sigma k)^2 else 0) +
      (∑ k, if P k then 0 else (sigma k)^2) = ∑ k, (sigma k)^2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  linarith

#assert_trust kernel finrank_singularSubspace
#assert_trust kernel starProjection_singularSubspace
#assert_trust kernel validSVD_selected_energy
#assert_trust kernel validSVD_selected_error
#print axioms validSVD_selected_error
end NLA.Proofs.TR04.SVD
