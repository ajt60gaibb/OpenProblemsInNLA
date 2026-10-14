import NLA.Proofs.RA10.NuclearIdealOperatorBridge
import Mathlib.Analysis.InnerProductSpace.Trace

/-! RA-10: the upper half of the exact orthogonal trace duality for the
frozen all-singular-value nuclear norm. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped InnerProductSpace BigOperators

namespace NLA.Proofs.RA10

private theorem trace_toEuclideanLin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.toEuclideanLin A).trace ℝ (EuclideanSpace ℝ (Fin n)) =
      Matrix.trace A := by
  simpa only [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    Matrix.trace_toLin_eq A (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

private theorem orthogonal_euclidean_norm {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℝ) (hleft : U.transpose * U = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin U x‖ = ‖x‖ := by
  let V := Matrix.toEuclideanLin U
  have hadj : V.adjoint ∘ₗ V = 1 := by
    have hT : Matrix.toEuclideanLin U.transpose = V.adjoint := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint U
    have h := congrArg Matrix.toEuclideanLin hleft
    rw [toEuclideanLin_mul_exact, hT] at h
    simpa [V, Module.End.one_eq_id] using h
  have hinner : ∀ y z : EuclideanSpace ℝ (Fin n),
      ⟪V y, V z⟫_ℝ = ⟪y, z⟫_ℝ := by
    intro y z
    calc
      ⟪V y, V z⟫_ℝ = ⟪y, V.adjoint (V z)⟫_ℝ :=
        (V.adjoint_inner_right y (V z)).symm
      _ = ⟪y, z⟫_ℝ := by simp [← LinearMap.comp_apply, hadj]
  exact (LinearMap.norm_map_iff_inner_map_map V).2 hinner x

private theorem norm_map_gram_eigenvector {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (i : Fin n) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp) i)‖ =
      T.singularValues i.val := by
  let G := T.adjoint ∘ₗ T
  let hG := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hG.eigenvectorBasis hn
  have hunit : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  have heig : G (b i) = hG.eigenvalues hn i • b i := by
    simp [G, b, hG.apply_eigenvectorBasis]
  have hsq : ‖T (b i)‖ ^ 2 = hG.eigenvalues hn i := by
    rw [← real_inner_self_eq_norm_sq]
    calc
      ⟪T (b i), T (b i)⟫_ℝ = ⟪b i, G (b i)⟫_ℝ := by
        simpa [G, LinearMap.comp_apply] using
          (T.adjoint_inner_right (b i) (T (b i))).symm
      _ = ⟪b i, (hG.eigenvalues hn i) • b i⟫_ℝ := by
        rw [heig]
      _ = hG.eigenvalues hn i := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
        ring
  have hsig := T.sq_singularValues_fin hn i
  have hnonneg := T.singularValues_nonneg i.val
  have hnorm : 0 ≤ ‖T (b i)‖ := norm_nonneg _
  have hmain : ‖T (b i)‖ = T.singularValues i.val := by
    nlinarith
  simpa [b, hG] using hmain

private theorem trace_orthogonal_pairing_sum {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.trace (U.transpose * M) =
      ∑ i : Fin n,
        ⟪Matrix.toEuclideanLin U
            (Matrix.toEuclideanLin M |>.isSymmetric_adjoint_comp_self.eigenvectorBasis
              (by simp) i),
          Matrix.toEuclideanLin M
            (Matrix.toEuclideanLin M |>.isSymmetric_adjoint_comp_self.eigenvectorBasis
              (by simp) i)⟫_ℝ := by
  let T := Matrix.toEuclideanLin M
  let V := Matrix.toEuclideanLin U
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  have hmat : Matrix.toEuclideanLin (U.transpose * M) = V.adjoint ∘ₗ T := by
    rw [toEuclideanLin_mul_exact]
    have hT : Matrix.toEuclideanLin U.transpose = V.adjoint := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint U
    rw [hT]
  calc
    Matrix.trace (U.transpose * M) =
        (Matrix.toEuclideanLin (U.transpose * M)).trace ℝ
          (EuclideanSpace ℝ (Fin n)) := (trace_toEuclideanLin _).symm
    _ = (V.adjoint ∘ₗ T).trace ℝ (EuclideanSpace ℝ (Fin n)) := by rw [hmat]
    _ = ∑ i : Fin n, ⟪b i, (V.adjoint ∘ₗ T) (b i)⟫_ℝ :=
      LinearMap.trace_eq_sum_inner _ b
    _ = ∑ i : Fin n, ⟪V (b i), T (b i)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [LinearMap.comp_apply] using
        (V.adjoint_inner_right (b i) (T (b i)))
    _ = _ := by rfl

theorem nuclearNorm_trace_orthogonal_le {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ)
    (hleft : U.transpose * U = 1) (_hright : U * U.transpose = 1) :
    Matrix.trace (U.transpose * M) ≤ NLA.Statements.RA10.NuclearNorm M := by
  let T := Matrix.toEuclideanLin M
  let V := Matrix.toEuclideanLin U
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  rw [trace_orthogonal_pairing_sum]
  unfold NLA.Statements.RA10.NuclearNorm
  apply Finset.sum_le_sum
  intro i _
  have hnormV : ‖V (b i)‖ = 1 :=
    (orthogonal_euclidean_norm U hleft (b i)).trans (b.orthonormal.norm_eq_one i)
  have hnormT : ‖T (b i)‖ = T.singularValues i.val := by
    simpa [b, T] using norm_map_gram_eigenvector T i
  calc
    ⟪V (b i), T (b i)⟫_ℝ ≤ ‖V (b i)‖ * ‖T (b i)‖ :=
      real_inner_le_norm _ _
    _ = T.singularValues i.val := by rw [hnormV, hnormT, one_mul]

#assert_trust kernel trace_toEuclideanLin
#assert_trust kernel orthogonal_euclidean_norm
#assert_trust kernel norm_map_gram_eigenvector
#assert_trust kernel trace_orthogonal_pairing_sum
#assert_trust kernel nuclearNorm_trace_orthogonal_le
#print axioms nuclearNorm_trace_orthogonal_le

end NLA.Proofs.RA10
