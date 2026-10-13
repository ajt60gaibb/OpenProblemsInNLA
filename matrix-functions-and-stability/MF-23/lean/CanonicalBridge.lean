import OAI.Analysis.DirectCrouzeix.CompleteBound
import CanonicalStatement

namespace NLA.MF23

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

private def reindexStarAlgEquiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix β β ℂ :=
  .ofAlgEquiv (Matrix.reindexAlgEquiv ℂ ℂ e) (by
    intro M
    change Matrix.reindex e e Mᴴ = (Matrix.reindex e e M)ᴴ
    rfl)

private theorem norm_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix α α ℂ) :
    ‖Matrix.reindex e e M‖ = ‖M‖ := by
  exact StarAlgEquiv.norm_map (reindexStarAlgEquiv e) M

private theorem blockEvaluation_eq_reindex {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    blockEvaluation A B =
      Matrix.reindex (Equiv.prodComm (Fin n) (Fin m))
        (Equiv.prodComm (Fin n) (Fin m))
        (OAI.DirectCrouzeix.tensorEvaluation A B) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  simp [blockEvaluation, OAI.DirectCrouzeix.tensorEvaluation,
    Matrix.reindex_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply, mul_comm]

theorem canonical_crouzeix_proved : Target := by
  intro n m d hn hm A B
  calc
    ‖blockEvaluation A B‖ = ‖OAI.DirectCrouzeix.tensorEvaluation A B‖ := by
      rw [blockEvaluation_eq_reindex, norm_reindex]
    _ ≤ 2 * OAI.DirectCrouzeix.rangeMaximum A B :=
      OAI.DirectCrouzeix.complete_crouzeix n m d hn hm A B

end

end NLA.MF23
