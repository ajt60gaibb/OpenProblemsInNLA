import NLA.Proofs.RA10.NuclearTraceDualUpper
import Mathlib.Analysis.InnerProductSpace.Trace

/-! RA-10: attainment in the exact orthogonal trace duality for the frozen
sum of all singular values. -/
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

private theorem trace_pairing_basis {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℝ)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    Matrix.trace (U.transpose * M) =
      ∑ i : Fin n,
        ⟪Matrix.toEuclideanLin U (b i), Matrix.toEuclideanLin M (b i)⟫_ℝ := by
  let T := Matrix.toEuclideanLin M
  let V := Matrix.toEuclideanLin U
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
      _ = ⟪b i, (hG.eigenvalues hn i) • b i⟫_ℝ := by rw [heig]
      _ = hG.eigenvalues hn i := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hunit]
        ring
  have hsig := T.sq_singularValues_fin hn i
  have hnonneg := T.singularValues_nonneg i.val
  have hnorm : 0 ≤ ‖T (b i)‖ := norm_nonneg _
  have hmain : ‖T (b i)‖ = T.singularValues i.val := by nlinarith
  simpa [b, hG] using hmain

private theorem inner_map_gram_eigenvector_ne {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (i j : Fin n) (hij : i ≠ j) :
    ⟪T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp) i),
      T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp) j)⟫_ℝ = 0 := by
  let G := T.adjoint ∘ₗ T
  let hG := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hG.eigenvectorBasis hn
  have heig : G (b j) = hG.eigenvalues hn j • b j := by
    simp [G, b, hG.apply_eigenvectorBasis]
  have hinner : ⟪b i, b j⟫_ℝ = 0 := b.orthonormal.inner_eq_zero hij
  have hmain : ⟪T (b i), T (b j)⟫_ℝ = 0 := by
    calc
      ⟪T (b i), T (b j)⟫_ℝ = ⟪b i, G (b j)⟫_ℝ := by
        simpa [G, LinearMap.comp_apply] using
          (T.adjoint_inner_right (b i) (T (b j))).symm
      _ = ⟪b i, hG.eigenvalues hn j • b j⟫_ℝ := by rw [heig]
      _ = 0 := by rw [real_inner_smul_right, hinner, mul_zero]
  simpa [b, hG] using hmain

private theorem exists_polar_basis {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ c : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ i : Fin n, 0 < T.singularValues i.val →
        c i = (T.singularValues i.val)⁻¹ •
          T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis (by simp) i) := by
  classical
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  let σ : Fin n → ℝ := fun i => T.singularValues i.val
  let s : Set (Fin n) := {i | 0 < σ i}
  let w : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => (σ i)⁻¹ • T (b i)
  have hnorm (i : Fin n) (hi : i ∈ s) : ‖w i‖ = 1 := by
    have hsig : 0 < σ i := hi
    have hmap : ‖T (b i)‖ = σ i := by
      simpa [b, σ] using norm_map_gram_eigenvector T i
    calc
      ‖w i‖ = ‖(σ i)⁻¹‖ * ‖T (b i)‖ := by simp [w, norm_smul]
      _ = (σ i)⁻¹ * σ i := by
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos hsig, hmap]
      _ = 1 := inv_mul_cancel₀ hsig.ne'
  have hinner (i j : Fin n) (hij : i ≠ j) : ⟪w i, w j⟫_ℝ = 0 := by
    have hzero : ⟪T (b i), T (b j)⟫_ℝ = 0 := by
      simpa [b] using inner_map_gram_eigenvector_ne T i j hij
    simp [w, real_inner_smul_left, real_inner_smul_right, hzero]
  have horth : Orthonormal ℝ (s.domRestrict w) := by
    constructor
    · intro i
      exact hnorm i.val i.property
    · intro i j hij
      apply hinner i.val j.val
      exact fun h => hij (Subtype.ext h)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Fintype.card (Fin n) := by simp
  obtain ⟨c, hc⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨c, ?_⟩
  intro i hi
  have his : i ∈ s := hi
  simpa [w, σ, b] using hc i his

theorem nuclearNorm_trace_orthogonal_attains {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ U : Matrix (Fin n) (Fin n) ℝ,
      U.transpose * U = 1 ∧ U * U.transpose = 1 ∧
        Matrix.trace (U.transpose * M) = NLA.Statements.RA10.NuclearNorm M := by
  classical
  let T := Matrix.toEuclideanLin M
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  obtain ⟨c, hc⟩ := exists_polar_basis T
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    b.equiv c (Equiv.refl (Fin n))
  let U : Matrix (Fin n) (Fin n) ℝ := Matrix.toEuclideanLin.symm e.toLinearMap
  have hU : Matrix.toEuclideanLin U = e.toLinearMap := by simp [U]
  have hUt : Matrix.toEuclideanLin U.transpose = e.symm.toLinearMap := by
    have ht : Matrix.toEuclideanLin U.transpose = (Matrix.toEuclideanLin U).adjoint := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.toEuclideanLin_conjTranspose_eq_adjoint U
    rw [ht, hU, e.adjoint_toLinearMap_eq_symm]
  have hleft : U.transpose * U = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul_exact, hUt, hU]
    apply LinearMap.ext
    intro x
    simp
  have hright : U * U.transpose = 1 := by
    apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul_exact, hUt, hU]
    apply LinearMap.ext
    intro x
    simp
  have hUbi (i : Fin n) : Matrix.toEuclideanLin U (b i) = c i := by
    rw [hU]
    simp [e]
  have htrace : Matrix.trace (U.transpose * M) =
      ∑ i : Fin n, ⟪c i, T (b i)⟫_ℝ := by
    rw [trace_pairing_basis U M b]
    apply Finset.sum_congr rfl
    intro i _
    rw [hUbi]
  refine ⟨U, hleft, hright, ?_⟩
  rw [htrace]
  unfold NLA.Statements.RA10.NuclearNorm
  apply Finset.sum_congr rfl
  intro i _
  have hnorm : ‖T (b i)‖ = T.singularValues i.val := by
    simpa [b, T] using norm_map_gram_eigenvector T i
  by_cases hi : 0 < T.singularValues i.val
  · calc
      ⟪c i, T (b i)⟫_ℝ =
          ⟪(T.singularValues i.val)⁻¹ • T (b i), T (b i)⟫_ℝ := by
            rw [hc i hi]
      _ = (T.singularValues i.val)⁻¹ * ‖T (b i)‖ ^ 2 := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      _ = T.singularValues i.val := by
        rw [hnorm]
        field_simp
  · have hz : T.singularValues i.val = 0 :=
      le_antisymm (le_of_not_gt hi) (T.singularValues_nonneg i.val)
    have hTzero : T (b i) = 0 := norm_eq_zero.mp (hnorm.trans hz)
    change ⟪c i, T (b i)⟫_ℝ = T.singularValues i.val
    rw [hTzero]
    simpa using hz.symm

#assert_trust kernel trace_toEuclideanLin
#assert_trust kernel trace_pairing_basis
#assert_trust kernel norm_map_gram_eigenvector
#assert_trust kernel inner_map_gram_eigenvector_ne
#assert_trust kernel exists_polar_basis
#assert_trust kernel nuclearNorm_trace_orthogonal_attains
#print axioms nuclearNorm_trace_orthogonal_attains

end NLA.Proofs.RA10
