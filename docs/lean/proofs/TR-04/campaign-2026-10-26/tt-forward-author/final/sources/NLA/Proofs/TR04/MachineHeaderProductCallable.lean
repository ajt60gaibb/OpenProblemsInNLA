import NLA.Proofs.TR04.MachineHeaderProduct
import NLA.Proofs.TR04.MachineTraceComposition
import NLA.Proofs.TR04.MachineNoEarlyHalt

/-! Callable actual header-product initialization, returning before the local
halt instruction to arbitrary finite caller continuation code. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def headerProductReturnTime (values : ℕ → ℕ) (d : ℕ) : ℕ := headerPrefixTime values d+3

def headerProductReturnState (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) : State headerProductProgram :=
  { headerProductLoopState memory d values d counter reals with label := 10 }

theorem headerProduct_exit_test (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (counter : ℕ) (reals : Fin 2 → ℝ) :
    ordinaryStep headerProductProgram (headerProductLoopState memory d values d counter reals) =
      headerProductReturnState memory d values counter reals := by
  apply machineState_ext <;>
    simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
      -Fin.val_eq_zero_iff,Fin.ext_iff,ordinaryStep,headerProductProgram,
      headerProductLoopState,headerProductReturnState] <;> rfl

theorem headerProduct_return (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (hm : ∀ j<d,memory j = (values j : ℝ)) :
    ∃ counter : ℕ, ∃ reals : Fin 2 → ℝ,
      (ordinaryStep headerProductProgram)^[headerProductReturnTime values d]
        (initial headerProductProgram d memory) = headerProductReturnState memory d values counter reals := by
  obtain ⟨counter,reals,hv⟩ := headerProduct_iterations memory d values hm 0 (fun _ => 0) d le_rfl
  refine ⟨counter,reals,?_⟩
  have htime : headerProductReturnTime values d = 1+(headerPrefixTime values d+2) := by
    unfold headerProductReturnTime;omega
  rw [htime,Function.iterate_add_apply,Function.iterate_add_apply,headerProduct_initial,hv,
    Function.iterate_one]
  exact headerProduct_exit_test memory d values counter reals

theorem headerProduct_return_running (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (hm : ∀ j<d,memory j = (values j : ℝ)) :
    ((ordinaryStep headerProductProgram)^[headerProductReturnTime values d]
      (initial headerProductProgram d memory)).status = .running := by
  obtain ⟨counter,reals,hv⟩ := headerProduct_return memory d values hm
  rw [hv]
  rfl

/-- Every legal caller trace obtains the exact decoded product under the actual
instruction charges; no caller continuation instruction is executed here. -/
theorem RoutineEmbedding.headerProduct_run_at {Q : Program}
    (E : RoutineEmbedding headerProductProgram Q) (memory : ℕ → ℝ) (d : ℕ) (values : ℕ → ℕ)
    (hm : ∀ j<d,memory j = (values j : ℝ)) {start : State Q} {trace : Trace Q}
    (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (initial headerProductProgram d memory) (trace.state offset)) :
    ∃ counter : ℕ, ∃ reals : Fin 2 → ℝ,
      E.Relates (headerProductReturnState memory d values counter reals)
        (trace.state (offset+headerProductReturnTime values d)) ∧
      CostThrough Q trace (offset+headerProductReturnTime values d) ≤
        CostThrough Q trace offset+headerProductReturnTime values d := by
  have hn := ordinary_nohalt_prefix_of_running (initial headerProductProgram d memory)
    (headerProductReturnTime values d) (headerProduct_return_running memory d values hm)
  have hc : ∀ k<headerProductReturnTime values d, instructionIsSVD
      (headerProductProgram.code ((ordinaryStep headerProductProgram)^[k]
        (initial headerProductProgram d memory)).label) = false := fun _ _ => headerProductProgram_scalar _
  obtain ⟨counter,reals,hv⟩ := headerProduct_return memory d values hm
  have hr := E.scalar_trace_prefix _ hs (legalTrace_shift ht offset) _ hn hc
  rw [hv] at hr
  exact ⟨counter,reals,hr,costThrough_compose_le le_rfl
    (E.scalar_trace_cost_le _ hs (legalTrace_shift ht offset) _ hn hc)⟩

#assert_trust kernel headerProduct_exit_test
#assert_trust kernel headerProduct_return
#assert_trust kernel headerProduct_return_running
#assert_trust kernel RoutineEmbedding.headerProduct_run_at
#print axioms RoutineEmbedding.headerProduct_run_at
end NLA.Proofs.TR04
