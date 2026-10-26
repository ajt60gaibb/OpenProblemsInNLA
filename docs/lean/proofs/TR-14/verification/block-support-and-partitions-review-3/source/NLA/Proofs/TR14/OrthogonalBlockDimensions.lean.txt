import NLA.Proofs.TR14.ReducedPrimitiveBlocks
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual dimension partitions from complete orthogonal idempotents. The
linear equivalence is multiplication into the actual ambient image blocks,
with inverse the sum of their ambient inclusions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
noncomputable section

variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]
  {ι : Type*} [Fintype ι]

/-- Multiplication by a complete orthogonal idempotent family gives a genuine
linear equivalence with the product of its actual ambient image blocks. -/
def orthogonalBlockEquiv (e : ι → B)
    (hidem : ∀ j, e j * e j = e j)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ j, e j = 1) :
    B ≃ₗ[K] (∀ j, LinearMap.range (LinearMap.mulLeft K (e j))) where
  toFun x j := ⟨e j * x, ⟨x, rfl⟩⟩
  invFun x := ∑ j, (x j : B)
  left_inv x := by
    change (∑ j, e j * x) = x
    rw [← Finset.sum_mul, hsum, one_mul]
  right_inv x := by
    classical
    funext j
    apply Subtype.ext
    change e j * (∑ i, (x i : B)) = (x j : B)
    rw [Finset.mul_sum]
    calc
      (∑ i, e j * (x i : B)) = e j * (x j : B) := by
        apply Finset.sum_eq_single j
        · intro i _ hij
          obtain ⟨a, ha⟩ := (x i).property
          change e i * a = (x i : B) at ha
          rw [← ha, ← mul_assoc, horth j i (Ne.symm hij), zero_mul]
        · intro hj
          exact (hj (Finset.mem_univ j)).elim
      _ = (x j : B) := by
        obtain ⟨a, ha⟩ := (x j).property
        change e j * a = (x j : B) at ha
        rw [← ha, ← mul_assoc, hidem]
  map_add' x y := by
    funext j
    apply Subtype.ext
    exact mul_add (e j) x y
  map_smul' c x := by
    funext j
    apply Subtype.ext
    exact (LinearMap.mulLeft K (e j)).map_smul c x

@[simp]
theorem orthogonalBlockEquiv_apply (e : ι → B)
    (hidem : ∀ j, e j * e j = e j)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ j, e j = 1) (x : B) (j : ι) :
    (orthogonalBlockEquiv (K := K) e hidem horth hsum x j : B) = e j * x := rfl

/-- The actual block-image dimensions partition the whole ambient dimension. -/
theorem sum_finrank_orthogonalBlocks [FiniteDimensional K B] (e : ι → B)
    (hidem : ∀ j, e j * e j = e j)
    (horth : ∀ i j, i ≠ j → e i * e j = 0)
    (hsum : ∑ j, e j = 1) :
    (∑ j, Module.finrank K (LinearMap.range (LinearMap.mulLeft K (e j)))) =
      Module.finrank K B := by
  rw [← Module.finrank_pi_fintype]
  exact (orthogonalBlockEquiv (K := K) e hidem horth hsum).finrank_eq.symm

variable {D : Type*} [CommRing D] [Algebra ℂ D] [FiniteDimensional ℂ D]

/-- Every actual algebra projection of the primitive scalar indicators gives
an actual dimension partition in its target algebra. In particular this
applies to both projections of an ambient product A × ℂ^R. -/
theorem sum_finrank_mapped_reducedBlocks {C : Type*} [CommRing C] [Algebra ℂ C]
    (S : Subalgebra ℂ C) {t : ℕ} (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) (f : C →ₐ[ℂ] D) :
    (∑ j, Module.finrank ℂ (LinearMap.range
      (LinearMap.mulLeft ℂ (f (reducedBlockIdempotent S φ j))))) =
      Module.finrank ℂ D := by
  apply sum_finrank_orthogonalBlocks
  · intro j
    rw [← map_mul, reducedBlockIdempotent_mul_self]
  · intro i j hij
    rw [← map_mul, reducedBlockIdempotent_mul_eq_zero S φ hij, map_zero]
  · rw [← map_sum, reducedBlockIdempotent_sum, map_one]

#assert_trust kernel orthogonalBlockEquiv
#assert_trust kernel sum_finrank_orthogonalBlocks
#assert_trust kernel sum_finrank_mapped_reducedBlocks
#print axioms orthogonalBlockEquiv
#print axioms sum_finrank_mapped_reducedBlocks

end
end NLA.Proofs.TR14
