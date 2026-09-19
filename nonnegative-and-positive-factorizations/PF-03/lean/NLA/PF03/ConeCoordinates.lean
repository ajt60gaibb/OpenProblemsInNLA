import NLA.PF03.ConeFunctional
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Exact reindexing of all21 real cone coefficients into7 groups of3.
No generator, zero coefficient, or sign case is discarded.
Sidney Holden: original mathematics. George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology: formalization;
Codex assistance. Author: /root. -/
set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

lemma castMatrix_mul {m n k : ℕ} (A : QMat m n) (B : QMat n k) :
    castMatrix (A * B) = castMatrix A * castMatrix B := by
  ext i j
  simp [castMatrix, Matrix.mul_apply]

lemma castMatrix_mulVec_generators (lam : Fin 21 → ℝ) :
    (castMatrix generatorMatrix).mulVec lam =
      ∑ i : Fin 7, ∑ a : Fin 3,
        lam (finProdFinEquiv (i, a)) • castVector (generator i a) := by
  funext r
  change (∑ j : Fin 21, (generatorMatrix r j : ℝ) * lam j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21)]
  rw [Fintype.sum_prod_type]
  simp only [generatorMatrix, Equiv.symm_apply_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, castVector]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

lemma K_mem_coordinates (x : Fin 7 → ℝ) :
    x ∈ K ↔ ∃ lam : Fin 7 → Fin 3 → ℝ,
      (∀ i a, 0 ≤ lam i a) ∧
      x = ∑ i : Fin 7, ∑ a : Fin 3, lam i a • castVector (generator i a) := by
  constructor
  · rintro ⟨lam, hnonneg, hx⟩
    exact ⟨fun i a => lam (finProdFinEquiv (i, a)),
      fun i a => hnonneg _, hx.trans (castMatrix_mulVec_generators lam)⟩
  · rintro ⟨lam, hnonneg, hx⟩
    let w : Fin 21 → ℝ := fun j =>
      lam ((finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).symm j).1
        ((finProdFinEquiv : Fin 7 × Fin 3 ≃ Fin 21).symm j).2
    refine ⟨w, fun j => hnonneg _ _, ?_⟩
    rw [castMatrix_mulVec_generators]
    simpa only [w, Equiv.symm_apply_apply] using hx

lemma local_generator_sum (i : Fin 7) (lam : Fin 3 → ℝ) :
    (∑ a : Fin 3, lam a • castVector (generator i a)) =
      (castMatrix (seedC i)).mulVec ((castMatrix triangle).mulVec lam) := by
  rw [Matrix.mulVec_mulVec, ← castMatrix_mul]
  funext r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castVector,
    generator, castMatrix, Matrix.mulVec, dotProduct, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

#print axioms K_mem_coordinates
#assert_trust kernel K_mem_coordinates
#print axioms local_generator_sum
#assert_trust kernel local_generator_sum
end NLA.PF03
