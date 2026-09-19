import NLA.PF03.SeedOrthogonalData
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
C04: transport the actual rational cubic certificates to the real seed.
The reverse Gram identity follows abstractly from the finite-square inverse
theorem; it is not a second closed numerical matrix calculation.
Original mathematics and seed: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

private theorem orthogonalCache_eq_seed : orthogonalCache = orthogonalSeed := by
  ext r i
  change cubicEval (RawData.orthogonalMatrix r i) =
    ∑ k : Fin 3, (RawData.coefficientMatrices k r i : ℝ) * alphaVector k
  simp only [cubicEval, seed_cache_coordinates r i 0,
    seed_cache_coordinates r i 1, seed_cache_coordinates r i 2]
  simp [alphaVector, Fin.sum_univ_three]

private theorem orthogonalCache_mul_transpose :
    orthogonalCache * orthogonalCacheᵀ = 1 := by
  ext r s
  calc
    (orthogonalCache * orthogonalCacheᵀ) r s =
        ∑ i : Fin 7, cubicEval (RawData.orthogonalMatrix r i) *
          cubicEval (RawData.orthogonalMatrix s i) := rfl
    _ = ∑ i : Fin 7, cubicEval
        (cubicMul (RawData.orthogonalMatrix r i) (RawData.orthogonalMatrix s i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (cubic_eval_operations.2.2.2 _ _).symm
    _ = cubicEval (seedCubicGram r s) :=
      (cubicEval_finset_sum Finset.univ
        (fun i : Fin 7 => cubicMul (RawData.orthogonalMatrix r i)
          (RawData.orthogonalMatrix s i))).symm
    _ = (if r = s then 1 else 0) := by
      rw [seed_cubic_gram]
      by_cases h : r = s
      · simp only [if_pos h, cubic_eval_operations.2.1]
      · simp only [if_neg h, cubic_eval_operations.1]
    _ = (1 : RMat 7 7) r s := by simp only [Matrix.one_apply]

/-- C04: literal cache fidelity and both exact real orthogonalities. -/
theorem seed_orthogonal :
    orthogonalCache = orthogonalSeed ∧
      orthogonalSeed * orthogonalSeedᵀ = 1 ∧
      orthogonalSeedᵀ * orthogonalSeed = 1 ∧
      (∀ i : Fin 7, (fun r => orthogonalSeed r i) =
        (castMatrix (seedC i)).mulVec alphaVector) := by
  have hcache := orthogonalCache_eq_seed
  have hgram : orthogonalSeed * orthogonalSeedᵀ = 1 := by
    simpa only [hcache] using orthogonalCache_mul_transpose
  refine ⟨hcache, hgram, mul_eq_one_symm hgram, ?_⟩
  intro i
  rfl

#print axioms seed_orthogonal
#assert_trust kernel seed_orthogonal

end NLA.PF03
