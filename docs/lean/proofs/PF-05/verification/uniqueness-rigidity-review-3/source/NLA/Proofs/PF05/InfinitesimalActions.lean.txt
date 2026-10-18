import NLA.Proofs.PF05.CoordinateActions

/-! Convert the actual unique coordinate operator into literal matrix actions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions

theorem feasible_direction_actions {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A E : Fin p → M2) (B F : Fin q → M2)
    (hfact : Factorization M A B) (hrank : M.rank = 3)
    (hdir : FeasibleDirection A E B F) :
    ∃ T : M3, (∀ i, E i=primal T (A i)) ∧ (∀ j, F j= -dual T (B j)) := by
  obtain ⟨T, hE, hF⟩ := (feasible_direction_operator M A E B F hfact hrank hdir).exists
  refine ⟨T, ?_, ?_⟩
  · intro i
    apply leftVector_injective_symmetric _ _ (hdir.1 i) (primal_symmetric _ _)
    rw [leftVector_primal]
    funext a
    exact congrArg (fun Z => Z i a) hE
  · intro j
    have hs : Symmetric (-dual T (B j)) := by
      intro a b
      simp [Matrix.neg_apply,dual_symmetric T (B j) a b]
    apply rightVector_injective_symmetric _ _ (hdir.2.1 j) hs
    have hneg : rightVector (-dual T (B j))= -rightVector (dual T (B j)) := by
      funext a; fin_cases a <;> simp [rightVector]
    rw [hneg,rightVector_dual]
    funext a
    exact congrArg (fun Z => Z a j) hF

#assert_trust kernel feasible_direction_actions
#print axioms feasible_direction_actions
end NLA.Proofs.PF05
