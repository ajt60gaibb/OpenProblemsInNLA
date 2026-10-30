import NLA.Proofs.TR04.SVDCyclicWindows

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators InnerProductSpace
namespace NLA.Proofs.TR04.SVD

theorem norm_starProjection_span_orthonormal {ι : Type*} [Fintype ι] {m : ℕ}
    {v : ι → Space m} (hv : Orthonormal ℝ v) (x : Space m) :
    ‖(Submodule.span ℝ (Set.range v)).starProjection x‖^2 = ∑ i, ⟪v i, x⟫_ℝ^2 := by
  classical
  let S := Submodule.span ℝ (↑(Finset.univ.image v) : Set (Space m))
  let b := OrthonormalBasis.span hv Finset.univ
  have hb := b.sum_sq_inner_right (S.orthogonalProjectionOnto x)
  have hi (a : (Finset.univ : Finset ι)) :
      ⟪b a, S.orthogonalProjectionOnto x⟫_ℝ = ⟪v a.val, x⟫_ℝ := by
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    simp only [b, OrthonormalBasis.span_apply]
  have h : ‖S.starProjection x‖^2 =
      ∑ a : (Finset.univ : Finset ι), ⟪v a.val, x⟫_ℝ^2 := by
    simpa only [Submodule.starProjection_apply, Submodule.coe_norm, hi] using hb.symm
  simpa [S] using h

theorem norm_singularSubspace_projection {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] (x : Space m) :
    ‖(singularSubspace U P).starProjection x‖^2 =
      ∑ k, if P k then ⟪matrixColumn U (Fin.castLE (Nat.min_le_left m l) k), x⟫_ℝ^2 else 0 := by
  classical
  rw [singularSubspace, norm_starProjection_span_orthonormal
    (orthonormal_selected_singularDirections hU P)]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter P) (by simp)
    (fun k => ⟪matrixColumn U (Fin.castLE (Nat.min_le_left m l) k), x⟫_ℝ^2)).symm

def singularCoordinateEnergy {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin l) ℝ) (k : Fin (min m l)) : ℝ :=
  ∑ j, ⟪matrixColumn U (Fin.castLE (Nat.min_le_left m l) k), matrixColumn R j⟫_ℝ^2

theorem singularCoordinateEnergy_nonneg {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin l) ℝ) (k : Fin (min m l)) :
    0 ≤ singularCoordinateEnergy U R k := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem singularSubspace_projectMatrix_energy {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] (R : Matrix (Fin m) (Fin l) ℝ) :
    matrixEnergy (projectMatrix (singularSubspace U P) R) =
      ∑ k, if P k then singularCoordinateEnergy U R k else 0 := by
  rw [matrixEnergy_eq_sum_column_norm]
  simp_rw [matrixColumn_projectMatrix, norm_singularSubspace_projection hU P]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp_all [singularCoordinateEnergy]

theorem sum_singularCoordinateEnergy_le {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (R : Matrix (Fin m) (Fin l) ℝ) :
    (∑ k, singularCoordinateEnergy U R k) ≤ matrixEnergy R := by
  have hp := projectMatrix_energy_decomposition (singularSubspace U (fun _ : Fin (min m l) => True)) R
  rw [singularSubspace_projectMatrix_energy hU] at hp
  simp only [ite_true] at hp
  have hn := matrixEnergy_nonneg (R - projectMatrix
    (singularSubspace U (fun _ : Fin (min m l) => True)) R)
  linarith

#assert_trust kernel norm_starProjection_span_orthonormal
#assert_trust kernel singularSubspace_projectMatrix_energy
#assert_trust kernel sum_singularCoordinateEnergy_le
#print axioms singularSubspace_projectMatrix_energy
end NLA.Proofs.TR04.SVD
