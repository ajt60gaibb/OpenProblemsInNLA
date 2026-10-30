import NLA.Proofs.TR04.SVDWeights
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators InnerProductSpace

namespace NLA.Proofs.TR04.SVD

def matrixColumn {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) (j : Fin l) : Space m :=
  WithLp.toLp 2 (fun i => M i j)

def projectMatrix {m l : ℕ} (S : Submodule ℝ (Space m))
    (M : Matrix (Fin m) (Fin l) ℝ) : Matrix (Fin m) (Fin l) ℝ :=
  fun i j => S.starProjection (matrixColumn M j) i

@[simp] theorem matrixColumn_projectMatrix {m l : ℕ} (S : Submodule ℝ (Space m))
    (M : Matrix (Fin m) (Fin l) ℝ) (j : Fin l) :
    matrixColumn (projectMatrix S M) j = S.starProjection (matrixColumn M j) := rfl

@[simp] theorem matrixColumn_sub {m l : ℕ} (M N : Matrix (Fin m) (Fin l) ℝ) (j : Fin l) :
    matrixColumn (M - N) j = matrixColumn M j - matrixColumn N j := rfl

theorem matrixEnergy_eq_sum_column_norm {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) :
    matrixEnergy M = ∑ j, ‖matrixColumn M j‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, matrixColumn]
  exact Finset.sum_comm

theorem projectMatrix_energy_decomposition {m l : ℕ} (S : Submodule ℝ (Space m))
    (M : Matrix (Fin m) (Fin l) ℝ) :
    matrixEnergy M = matrixEnergy (projectMatrix S M) +
      matrixEnergy (M - projectMatrix S M) := by
  simp only [matrixEnergy_eq_sum_column_norm, matrixColumn_sub,
    matrixColumn_projectMatrix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [S.starProjection_orthogonal_val] using
    S.norm_sq_eq_add_norm_sq_starProjection (matrixColumn M j)

theorem projectMatrix_error_decomposition {m l : ℕ} (S : Submodule ℝ (Space m))
    (M Y : Matrix (Fin m) (Fin l) ℝ)
    (hY : ∀ j, matrixColumn Y j ∈ S) :
    matrixEnergy (M - Y) = matrixEnergy (M - projectMatrix S M) +
      matrixEnergy (projectMatrix S M - Y) := by
  simp only [matrixEnergy_eq_sum_column_norm, matrixColumn_sub,
    matrixColumn_projectMatrix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hy : S.starProjection (matrixColumn Y j) = matrixColumn Y j :=
    S.starProjection_eq_self_iff.mpr (hY j)
  have h := S.norm_sq_eq_add_norm_sq_starProjection (matrixColumn M j - matrixColumn Y j)
  rw [S.starProjection_orthogonal_val, map_sub, hy] at h
  have hc : matrixColumn M j - matrixColumn Y j -
      (S.starProjection (matrixColumn M j) - matrixColumn Y j) =
        matrixColumn M j - S.starProjection (matrixColumn M j) := by abel
  rw [hc, add_comm] at h
  exact h

theorem projectMatrix_error_le {m l : ℕ} (S : Submodule ℝ (Space m))
    (M Y : Matrix (Fin m) (Fin l) ℝ) (hY : ∀ j, matrixColumn Y j ∈ S) :
    matrixEnergy (M - projectMatrix S M) ≤ matrixEnergy (M - Y) := by
  rw [projectMatrix_error_decomposition S M Y hY]
  exact le_add_of_nonneg_right (matrixEnergy_nonneg _)

theorem projectMatrix_error_eq_iff {m l : ℕ} (S : Submodule ℝ (Space m))
    (M Y : Matrix (Fin m) (Fin l) ℝ) (hY : ∀ j, matrixColumn Y j ∈ S) :
    matrixEnergy (M - Y) = matrixEnergy (M - projectMatrix S M) ↔
      Y = projectMatrix S M := by
  rw [projectMatrix_error_decomposition S M Y hY, add_eq_left,
    matrixError_eq_zero_iff, eq_comm]

theorem exists_basis_of_orthonormalColumns {m : ℕ} {U : Matrix (Fin m) (Fin m) ℝ}
    (hU : OrthonormalColumns U) :
    ∃ b : OrthonormalBasis (Fin m) ℝ (Space m), ∀ i, b i = matrixColumn U i := by
  have horth : Orthonormal ℝ (Set.univ.domRestrict (matrixColumn U)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa [matrixColumn, PiLp.inner_apply, mul_comm, Subtype.ext_iff] using hU i j
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (by simp [Space])
  exact ⟨b, fun i => hb i (Set.mem_univ i)⟩

theorem projection_norm_sq_basis_sum {m : ℕ} (S : Submodule ℝ (Space m)) (x : Space m) :
    ‖S.starProjection x‖^2 =
      ∑ a : Fin (Module.finrank ℝ S),
        ⟪(stdOrthonormalBasis ℝ S a : Space m), x⟫_ℝ^2 := by
  have h := (stdOrthonormalBasis ℝ S).sum_sq_inner_right (S.orthogonalProjectionOnto x)
  simpa only [Submodule.starProjection_apply, Submodule.coe_norm,
    ← Submodule.coe_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using h.symm

def projectionWeight {m : ℕ} (S : Submodule ℝ (Space m))
    (U : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : ℝ :=
  ‖S.starProjection (matrixColumn U i)‖^2

theorem projectionWeight_nonneg {m : ℕ} (S : Submodule ℝ (Space m))
    (U : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) : 0 ≤ projectionWeight S U i :=
  sq_nonneg _

theorem projectionWeight_le_one {m : ℕ} (S : Submodule ℝ (Space m))
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U) (i : Fin m) :
    projectionWeight S U i ≤ 1 := by
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormalColumns hU
  have hu : ‖matrixColumn U i‖ = 1 := by rw [← hb]; exact b.norm_eq_one i
  have hp := S.norm_starProjection_apply_le (matrixColumn U i)
  unfold projectionWeight
  rw [hu] at hp
  nlinarith [norm_nonneg (S.starProjection (matrixColumn U i))]

theorem sum_projectionWeight {m : ℕ} (S : Submodule ℝ (Space m))
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U) :
    (∑ i, projectionWeight S U i) = Module.finrank ℝ S := by
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormalColumns hU
  simp_rw [projectionWeight, projection_norm_sq_basis_sum]
  rw [Finset.sum_comm]
  have hi (a : Fin (Module.finrank ℝ S)) :
      (∑ i : Fin m, ⟪(stdOrthonormalBasis ℝ S a : Space m), matrixColumn U i⟫_ℝ^2) = 1 := by
    simp_rw [← hb]
    rw [b.sum_sq_inner_left]
    change ‖stdOrthonormalBasis ℝ S a‖^2 = 1
    rw [(stdOrthonormalBasis ℝ S).norm_eq_one]
    norm_num
  simp_rw [hi]
  simp

#assert_trust kernel projectMatrix_error_decomposition
#assert_trust kernel projectMatrix_error_eq_iff
#assert_trust kernel sum_projectionWeight
#print axioms sum_projectionWeight

end NLA.Proofs.TR04.SVD
