import NLA.Proofs.TR04.SVDSelectedProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

theorem toEuclideanLin_eq_sum_columns {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ)
    (x : Space l) : Matrix.toEuclideanLin M x = ∑ j, x j • matrixColumn M j := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, matrixColumn,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem toEuclideanLin_projectMatrix {m l : ℕ} (S : Submodule ℝ (Space m))
    (M : Matrix (Fin m) (Fin l) ℝ) :
    Matrix.toEuclideanLin (projectMatrix S M) =
      S.starProjection.toLinearMap ∘ₗ Matrix.toEuclideanLin M := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, toEuclideanLin_eq_sum_columns,
    ContinuousLinearMap.coe_coe, map_sum, map_smul, matrixColumn_projectMatrix]

theorem columnSpace_projectMatrix_le {m l : ℕ} (S : Submodule ℝ (Space m))
    (M : Matrix (Fin m) (Fin l) ℝ) : columnSpace (projectMatrix S M) ≤ S := by
  rintro y ⟨x, rfl⟩
  rw [toEuclideanLin_projectMatrix, LinearMap.comp_apply]
  exact S.starProjection_apply_mem _

theorem rank_projectMatrix_le_finrank {m l : ℕ} (S : Submodule ℝ (Space m))
    (M : Matrix (Fin m) (Fin l) ℝ) : Matrix.rank (projectMatrix S M) ≤ Module.finrank ℝ S := by
  rw [← finrank_columnSpace]
  exact Submodule.finrank_mono (columnSpace_projectMatrix_le S M)

theorem rank_selected_projection_le_card {m l : ℕ}
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U)
    (P : Fin (min m l) → Prop) [DecidablePred P] (M : Matrix (Fin m) (Fin l) ℝ) :
    Matrix.rank (projectMatrix (singularSubspace U P) M) ≤ Fintype.card {k // P k} := by
  rw [← finrank_singularSubspace hU P]
  exact rank_projectMatrix_le_finrank _ _

#assert_trust kernel toEuclideanLin_projectMatrix
#assert_trust kernel rank_projectMatrix_le_finrank
#assert_trust kernel rank_selected_projection_le_card
#print axioms rank_selected_projection_le_card
end NLA.Proofs.TR04.SVD
