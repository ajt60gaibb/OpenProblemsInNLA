import NLA.Proofs.TR04.MachineHeaderProductCallable

/-! Single-natural decoding using the same literal header-product instruction
bank. Enter its decoder at label5 with cursor=end and product1; after decoding,
the multiplication and cursor increment force the outer test to exit. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def headerSingleReturnState (memory : ℕ → ℝ) (d value : ℕ) : State headerProductProgram where
  label := 10
  real := ![(value : ℝ),(value : ℝ)]
  natural := ![d,d+1,value,value]
  memory := memory
  status := .running

theorem headerSingle_after_decode (memory : ℕ → ℝ) (d value : ℕ) :
    (ordinaryStep headerProductProgram)^[3] (headerProductAfterDecode memory d d 1 value) =
      headerSingleReturnState memory d value := by
  have hnot : ¬ d+1<d := by omega
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Function.iterate_succ_apply',ordinaryStep,
    headerProductProgram,headerProductAfterDecode,headerSingleReturnState,hnot]
  all_goals try rfl
  funext r
  fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq,-Fin.reduceNe,
    -Fin.val_eq_zero_iff,Fin.ext_iff,Matrix.cons_val_succ',Matrix.cons_val_zero']

theorem headerSingle_return (memory : ℕ → ℝ) (d value : ℕ) (scratch : ℝ) :
    (ordinaryStep headerProductProgram)^[3*value+5]
      (headerProductDecodeState memory d d 1 value scratch) = headerSingleReturnState memory d value := by
  rw [show 3*value+5 = 3+(3*value+2) by omega,Function.iterate_add_apply,headerProduct_decode]
  exact headerSingle_after_decode memory d value

theorem RoutineEmbedding.headerSingle_run_at {Q : Program}
    (E : RoutineEmbedding headerProductProgram Q) (memory : ℕ → ℝ) (d value : ℕ) (scratch : ℝ)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (headerProductDecodeState memory d d 1 value scratch) (trace.state offset)) :
    E.Relates (headerSingleReturnState memory d value) (trace.state (offset+(3*value+5))) ∧
      CostThrough Q trace (offset+(3*value+5)) ≤ CostThrough Q trace offset+(3*value+5) := by
  have hrunning : ((ordinaryStep headerProductProgram)^[3*value+5]
      (headerProductDecodeState memory d d 1 value scratch)).status = .running := by
    rw [headerSingle_return];rfl
  have hn := ordinary_nohalt_prefix_of_running _ _ hrunning
  have hc : ∀ k<3*value+5, instructionIsSVD (headerProductProgram.code
      ((ordinaryStep headerProductProgram)^[k] (headerProductDecodeState memory d d 1 value scratch)).label) = false :=
    fun _ _ => headerProductProgram_scalar _
  have hr := E.scalar_trace_prefix _ hs (legalTrace_shift ht offset) _ hn hc
  rw [headerSingle_return] at hr
  exact ⟨hr,costThrough_compose_le le_rfl (E.scalar_trace_cost_le _ hs (legalTrace_shift ht offset) _ hn hc)⟩

#assert_trust kernel headerSingle_after_decode
#assert_trust kernel headerSingle_return
#assert_trust kernel RoutineEmbedding.headerSingle_run_at
#print axioms RoutineEmbedding.headerSingle_run_at
end NLA.Proofs.TR04
