import NLA.Proofs.TR04.MachineRelocation

/-! Finite ordinary-step forms of the frozen relocation interface. They are
used only for actual scalar paths; legal-trace contracts are supplied separately. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem RoutineEmbedding.ordinary_iterate_relates {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t : State Q} (h : E.Relates s t) (n : ℕ)
    (hexit : ∀ k<n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false) :
    E.Relates ((ordinaryStep P)^[n] s) ((ordinaryStep Q)^[n] t) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
      exact E.ordinaryStep_relates (ih (fun k hk => hexit k (by omega))) (hexit n (by omega))

theorem RoutineEmbedding.ordinary_iterate_natural_outside {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t : State Q} (h : E.Relates s t) (n : ℕ)
    (hexit : ∀ k<n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (j : Fin (Q.extraNatRegisters+1)) (hj : ∀ i,j ≠ E.naturals i) :
    ((ordinaryStep Q)^[n] t).natural j = t.natural j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hr := E.ordinary_iterate_relates h n (fun k hk => hexit k (by omega))
      rw [Function.iterate_succ_apply',E.ordinaryStep_natural_outside hr.label (hexit n (by omega)) j hj]
      exact ih (fun k hk => hexit k (by omega))

theorem RoutineEmbedding.ordinary_iterate_real_outside {P Q : Program} (E : RoutineEmbedding P Q)
    {s : State P} {t : State Q} (h : E.Relates s t) (n : ℕ)
    (hexit : ∀ k<n, instructionIsHalt (P.code ((ordinaryStep P)^[k] s).label) = false)
    (j : Fin Q.realRegisters) (hj : ∀ i,j ≠ E.reals i) :
    ((ordinaryStep Q)^[n] t).real j = t.real j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hr := E.ordinary_iterate_relates h n (fun k hk => hexit k (by omega))
      rw [Function.iterate_succ_apply',E.ordinaryStep_real_outside hr.label (hexit n (by omega)) j hj]
      exact ih (fun k hk => hexit k (by omega))

#assert_trust kernel RoutineEmbedding.ordinary_iterate_relates
#assert_trust kernel RoutineEmbedding.ordinary_iterate_natural_outside
#assert_trust kernel RoutineEmbedding.ordinary_iterate_real_outside
#print axioms RoutineEmbedding.ordinary_iterate_relates
end NLA.Proofs.TR04
