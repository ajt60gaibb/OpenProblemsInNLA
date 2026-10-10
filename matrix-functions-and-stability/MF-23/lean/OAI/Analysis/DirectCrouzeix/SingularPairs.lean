import OAI.Analysis.DirectCrouzeix.HilbertSchmidt

namespace OAI

universe u_37 u_38 u_39 u_40

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem positive_compression_blocks {n m : ℕ}
    (R : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Matrix (Fin n) (Fin m) ℂ) (hR : (R + Rᴴ).PosSemidef) :
    (Matrix.fromBlocks
      (Xᴴ * R * X + (Xᴴ * R * X)ᴴ)
      ((Yᴴ * R * X + (Xᴴ * R * Y)ᴴ)ᴴ)
      (Yᴴ * R * X + (Xᴴ * R * Y)ᴴ)
      (Yᴴ * R * Y + (Yᴴ * R * Y)ᴴ)).PosSemidef := by
  have h := hR.conjTranspose_mul_mul_same (Matrix.fromCols X Y)
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols] at h
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
    add_comm] using h

theorem exists_norm_attainer {ι : Type u_37} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    ∃ x : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖ := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ ι) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
    T.continuous.norm.continuousOn
  have hx' : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx', le_antisymm ?_ ?_⟩
  · simpa [hx'] using T.le_opNorm x
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro v
    by_cases hv : v = 0
    · simp [hv]
    let u : EuclideanSpace ℂ ι := (‖v‖ : ℂ)⁻¹ • v
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
    have hm : ‖T u‖ ≤ ‖T x‖ := hmax (by simpa using hu)
    have he : ‖T u‖ = ‖T v‖ / ‖v‖ := by
      simp [u, norm_smul, div_eq_mul_inv, mul_comm]
    rw [he] at hm
    exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp hm

theorem exists_singular_pair {ι : Type u_38} [Fintype ι] [Nonempty ι]
    (T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hT : 0 < ‖T‖) :
    ∃ x y : EuclideanSpace ℂ ι, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
      T x = (‖T‖ : ℂ) • y ∧
      ContinuousLinearMap.adjoint T y = (‖T‖ : ℂ) • x := by
  obtain ⟨x, hx, hTx⟩ := exists_norm_attainer T
  let y : EuclideanSpace ℂ ι := (‖T‖ : ℂ)⁻¹ • T x
  have hn : (‖T‖ : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, hTx, ne_of_gt hT]
  have hxy : T x = (‖T‖ : ℂ) • y := by simp [y, smul_smul, hn]
  refine ⟨x, y, hx, hy, hxy, ?_⟩
  have ha : ‖ContinuousLinearMap.adjoint T y‖ ≤ ‖T‖ := by
    simpa [hy] using (ContinuousLinearMap.adjoint T).le_opNorm y
  have hi : inner ℂ (ContinuousLinearMap.adjoint T y) x = (‖T‖ : ℂ) := by
    rw [ContinuousLinearMap.adjoint_inner_left, hxy, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hy]
    simp
  have hd : ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖ ^ 2 =
      ‖ContinuousLinearMap.adjoint T y‖ ^ 2 - ‖T‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi]
    simp [norm_smul, hx]
    ring
  have he : ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖ = 0 := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) ha 2
    nlinarith [sq_nonneg ‖ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x‖,
      norm_nonneg (ContinuousLinearMap.adjoint T y - (‖T‖ : ℂ) • x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

def matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    Matrix (Fin n) (Fin m) ℂ := fun i j => x (i, j)

@[simp] theorem hsVector_matrixify {n m : ℕ} (x : EuclideanSpace ℂ (Fin n × Fin m)) :
    hsVector (matrixify x) = x := by
  apply WithLp.ofLp_injective
  rfl

theorem tensor_entryPair {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (X Y : Matrix (Fin n) (Fin m) ℂ) :
    inner ℂ (hsVector Y)
      (Matrix.toEuclideanCLM (n := Fin n × Fin m) (𝕜 := ℂ) (A ⊗ₖ C) (hsVector X)) =
      entryPair (Yᴴ * A * X) C := by
  simp only [hsVector, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanCLM_toLp, dotProduct, Matrix.mulVec,
    Pi.star_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    entryPair, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2
    intro a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem entryPair_smul_right {ι : Type u_39} {κ : Type u_40} [Fintype ι] [Fintype κ]
    (M C : Matrix ι κ ℂ) (c : ℂ) : entryPair M (c • C) = c * entryPair M C := by
  simp [entryPair, Finset.mul_sum, mul_left_comm]

end DirectCrouzeix

end

end OAI
