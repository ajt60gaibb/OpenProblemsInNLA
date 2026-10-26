import NLA.Proofs.TR04.SVDConsequences

/-! Actual subspace and residual consequences of the frozen equality theorem.
This module leaves all frozen SVD/Eckart prerequisites unchanged. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped InnerProductSpace BigOperators
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

def singularSubspace {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (P : Fin (min m l) → Prop) : Submodule ℝ (Space m) :=
  Submodule.span ℝ (Set.range (fun k : {k // P k} =>
    matrixColumn U (Fin.castLE (Nat.min_le_left m l) k.val)))

theorem singularSubspace_le {m l : ℕ} (U : Matrix (Fin m) (Fin m) ℝ)
    (P : Fin (min m l) → Prop) (S : Submodule ℝ (Space m))
    (hP : ∀ k, P k → matrixColumn U (Fin.castLE (Nat.min_le_left m l) k) ∈ S) :
    singularSubspace U P ≤ S := by
  apply Submodule.span_le.mpr
  rintro x ⟨k, rfl⟩
  exact hP k.val k.property

theorem projectMatrix_residual_eq_zero_of_le {m l : ℕ}
    (H S : Submodule ℝ (Space m)) (hHS : H ≤ S) (B : Matrix (Fin m) (Fin l) ℝ) :
    projectMatrix H (B - projectMatrix S B) = 0 := by
  ext i j
  change H.starProjection (matrixColumn (B - projectMatrix S B) j) i = 0
  rw [matrixColumn_sub, matrixColumn_projectMatrix]
  have hz : H.starProjection (matrixColumn B j - S.starProjection (matrixColumn B j)) = 0 := by
    apply H.starProjection_apply_eq_zero_iff.mpr
    apply (H.mem_orthogonal' _).mpr
    intro w hw
    exact S.starProjection_inner_eq_zero _ _ (hHS hw)
  rw [hz]
  rfl

theorem validSVD_equality_above_span_residual {m l : ℕ}
    {B : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) (a : Fin (min m l)) (ha : 0 < sigma a)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    singularSubspace U (fun k => sigma a < sigma k) ≤ columnSpace Y ∧
      projectMatrix (singularSubspace U (fun k => sigma a < sigma k)) (B - Y) = 0 := by
  have hs := validSVD_eckartYoung_eq_last_retained h a ha Y hY heq
  have hH : singularSubspace U (fun k => sigma a < sigma k) ≤ columnSpace Y := by
    apply singularSubspace_le
    intro k hk
    exact (columnSpace Y).starProjection_eq_self_iff.mp (hs.2.2.1 k hk)
  refine ⟨hH, ?_⟩
  rw [hs.1]
  exact projectMatrix_residual_eq_zero_of_le _ _ hH B

#assert_trust kernel singularSubspace_le
#assert_trust kernel projectMatrix_residual_eq_zero_of_le
#assert_trust kernel validSVD_equality_above_span_residual
#print axioms validSVD_equality_above_span_residual
end NLA.Proofs.TR04.SVD
