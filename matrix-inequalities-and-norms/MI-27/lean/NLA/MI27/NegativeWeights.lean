/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted source development by Codex coordinator /root.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. This finite-dimensional
inertia argument supports the relative-entropy pencil representation of
Peter E. Frenkel. It asserts no full C11 or original-target completion.

The exact statement was independently reviewed before implementation by
/root/nr04_mf14_final_referee_b and /root/new_math_nr01; see STATEMENT-FREEZE.json.
All zero-dimensional, singular and repeated-weight cases are retained.
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.MI27

lemma c11_negative_weights_card_le {m n : ℕ}
    (a : Fin m → ℝ) (b : Fin n → ℝ) (T : Matrix (Fin m) (Fin n) ℂ)
    (hform : ∀ v : Fin n → ℂ,
      (∑ j : Fin n, b j * Complex.normSq (v j)) =
        ∑ i : Fin m, a i * Complex.normSq ((T *ᵥ v) i)) :
    Fintype.card {j : Fin n // b j < 0} ≤
      Fintype.card {i : Fin m // a i < 0} := by
  classical
  let B := {j : Fin n // b j < 0}
  let A := {i : Fin m // a i < 0}
  let E : (B → ℂ) →ₗ[ℂ] (Fin n → ℂ) := {
    toFun := fun v j => if h : b j < 0 then v ⟨j, h⟩ else 0
    map_add' := by
      intro u v
      funext j
      by_cases hj : b j < 0 <;> simp [hj]
    map_smul' := by
      intro c v
      funext j
      by_cases hj : b j < 0 <;> simp [hj]
  }
  let F : (B → ℂ) →ₗ[ℂ] (A → ℂ) := {
    toFun := fun v i => (T *ᵥ E v) i.val
    map_add' := by
      intro u v
      funext i
      simp only [map_add, Matrix.mulVec_add, Pi.add_apply]
    map_smul' := by
      intro c v
      funext i
      simp only [map_smul, Matrix.mulVec_smul, Pi.smul_apply, RingHom.id_apply]
  }
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    funext j
    change v j = 0
    by_contra hj
    have hleft : (∑ k : Fin n, b k * Complex.normSq (E v k)) < 0 := by
      apply Finset.sum_neg'
      · intro k _
        by_cases hk : b k < 0
        · exact mul_nonpos_of_nonpos_of_nonneg hk.le (Complex.normSq_nonneg _)
        · simp [E, hk]
      · refine ⟨j.val, Finset.mem_univ _, ?_⟩
        have he : E v j.val = v j := by simp [E, j.property]
        rw [he]
        exact mul_neg_of_neg_of_pos j.property (Complex.normSq_pos.mpr hj)
    have hright : 0 ≤ ∑ i : Fin m, a i * Complex.normSq ((T *ᵥ E v) i) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : a i < 0
      · have hz := congrArg (fun w : A → ℂ => w ⟨i, hi⟩) hv
        change (T *ᵥ E v) i = 0 at hz
        simp [hz]
      · exact mul_nonneg (le_of_not_gt hi) (Complex.normSq_nonneg _)
    linarith [hform (E v)]
  simpa only [Module.finrank_fintype_fun_eq_card] using
    (LinearMap.finrank_le_finrank_of_injective hinj)

#print axioms c11_negative_weights_card_le
#assert_trust kernel c11_negative_weights_card_le

end NLA.MI27
