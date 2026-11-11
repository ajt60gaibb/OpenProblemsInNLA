import NLA.Proofs.RE06.RepairProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Classical
namespace NLA.Proofs.RE06.Repair

abbrev RealSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

def subspaceBasis {n : ℕ} (S : Submodule ℝ (RealSpace n)) :
    OrthonormalBasis (Fin (Module.finrank ℝ S)) ℝ S := stdOrthonormalBasis ℝ S

def subspaceMatrix {n : ℕ} (S : Submodule ℝ (RealSpace n)) :
    Matrix (Fin n) (Fin (Module.finrank ℝ S)) ℝ :=
  fun i j => ((subspaceBasis S j : S) : RealSpace n) i

theorem subspaceMatrix_gram {n : ℕ} (S : Submodule ℝ (RealSpace n)) :
    (subspaceMatrix S).transpose*subspaceMatrix S=1 := by
  ext i j
  have h := (subspaceBasis S).inner_eq_ite i j
  change (∑ k, (((subspaceBasis S j : S) : RealSpace n) k) *
    (((subspaceBasis S i : S) : RealSpace n) k)) = _ at h
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    subspaceMatrix, mul_comm] using h

theorem subspaceMatrix_map {n : ℕ} (S : Submodule ℝ (RealSpace n))
    (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ S))) :
    Matrix.toEuclideanLin (subspaceMatrix S) v =
      ∑ j, v j • ((subspaceBasis S j : S) : RealSpace n) := by
  ext i
  simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, subspaceMatrix,
    mul_comm]

theorem subspaceMatrix_range {n : ℕ} (S : Submodule ℝ (RealSpace n)) :
    LinearMap.range (Matrix.toEuclideanLin (subspaceMatrix S)) = S := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    rw [subspaceMatrix_map]
    exact S.sum_mem (fun j _ => S.smul_mem (v j) (subspaceBasis S j).property)
  · intro x hx
    let xS : S := ⟨x,hx⟩
    refine ⟨(subspaceBasis S).repr xS, ?_⟩
    rw [subspaceMatrix_map]
    have h := congrArg (fun z : S => (z : RealSpace n)) ((subspaceBasis S).sum_repr xS)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h

def rangeDimension {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin Y))

def rangeBasisMatrix {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin (rangeDimension Y)) ℝ :=
  subspaceMatrix (LinearMap.range (Matrix.toEuclideanLin Y))

theorem rangeDimension_le {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    rangeDimension Y ≤ k := by
  simpa [rangeDimension] using
    (Matrix.toEuclideanLin Y).finrank_range_le

theorem rangeBasisMatrix_gram {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    (rangeBasisMatrix Y).transpose*rangeBasisMatrix Y=1 :=
  subspaceMatrix_gram _

theorem rangeBasisMatrix_range {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    Set.range (rangeBasisMatrix Y).mulVec = Set.range Y.mulVec := by
  apply Set.Subset.antisymm
  · rintro x ⟨v,rfl⟩
    have hm : Matrix.toEuclideanLin (rangeBasisMatrix Y) (WithLp.toLp 2 v) ∈
        LinearMap.range (Matrix.toEuclideanLin Y) := by
      rw [← subspaceMatrix_range (LinearMap.range (Matrix.toEuclideanLin Y))]
      exact ⟨WithLp.toLp 2 v,rfl⟩
    obtain ⟨w,hw⟩ := hm
    exact ⟨WithLp.ofLp w, congrArg WithLp.ofLp hw⟩
  · rintro x ⟨v,rfl⟩
    have hm : Matrix.toEuclideanLin Y (WithLp.toLp 2 v) ∈
        LinearMap.range (Matrix.toEuclideanLin Y) := ⟨WithLp.toLp 2 v,rfl⟩
    rw [← subspaceMatrix_range (LinearMap.range (Matrix.toEuclideanLin Y))] at hm
    obtain ⟨w,hw⟩ := hm
    exact ⟨WithLp.ofLp w, congrArg WithLp.ofLp hw⟩

#assert_trust kernel subspaceMatrix_gram
#assert_trust kernel subspaceMatrix_map
#assert_trust kernel subspaceMatrix_range
#assert_trust kernel rangeDimension_le
#assert_trust kernel rangeBasisMatrix_gram
#assert_trust kernel rangeBasisMatrix_range
#print axioms rangeBasisMatrix_range
end NLA.Proofs.RE06.Repair
