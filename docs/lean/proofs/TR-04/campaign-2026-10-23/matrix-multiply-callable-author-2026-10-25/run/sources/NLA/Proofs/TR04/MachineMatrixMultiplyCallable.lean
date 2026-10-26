import NLA.Proofs.TR04.MachineMatrixMultiplyCorrectness
import NLA.Proofs.TR04.MachineTraceComposition
import NLA.Proofs.TR04.MachineNoEarlyHalt

/-! Callable multiplication stops at the local halt label before executing it.
The caller may put its own continuation at that label. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def matrixMultiplyReturnTime (p : MatrixMultiplyData) : ℕ :=
  matrixMultiplyRowTime p * p.rows + 1

def matrixMultiplyReturnState (p : MatrixMultiplyData) (scratch : MatrixMultiplyScratch) :
    State matrixMultiplyProgram :=
  { matrixMultiplyRowState p p.rows scratch with label := 21 }

theorem matrixMultiplyProgram_return_step (p : MatrixMultiplyData)
    (scratch : MatrixMultiplyScratch) :
    ordinaryStep matrixMultiplyProgram (matrixMultiplyRowState p p.rows scratch) =
      matrixMultiplyReturnState p scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, ordinaryStep, matrixMultiplyProgram, matrixMultiplyReturnState,
    matrixMultiplyRowState, matrixMultiplyState]
  all_goals rfl

theorem matrixMultiplyProgram_return (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch) :
    ∃ result : MatrixMultiplyScratch,
      (ordinaryStep matrixMultiplyProgram)^[matrixMultiplyReturnTime p]
        (matrixMultiplyRowState p 0 scratch) = matrixMultiplyReturnState p result := by
  obtain ⟨result, hr⟩ := matrixMultiplyProgram_rows p h scratch p.rows le_rfl
  refine ⟨result, ?_⟩
  rw [matrixMultiplyReturnTime, Nat.add_comm (matrixMultiplyRowTime p * p.rows),
    Function.iterate_add_apply, hr]
  exact matrixMultiplyProgram_return_step p result

theorem matrixMultiplyReturnState_product (p : MatrixMultiplyData)
    (scratch : MatrixMultiplyScratch) :
    (matrixMultiplyReturnState p scratch).label = 21 ∧
    (matrixMultiplyReturnState p scratch).status = .running ∧
    readMatrix (matrixMultiplyReturnState p scratch).memory p.rows p.cols p.dBase =
      p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (matrixMultiplyReturnState p scratch).memory address = p.memory address) := by
  refine ⟨rfl, rfl, p.outputPrefix_read, ?_⟩
  intro address ha
  exact prefixMemory_outside _ _ _ _ _ ha

theorem matrixMultiplyReturnTime_le_cubic (p : MatrixMultiplyData) :
    matrixMultiplyReturnTime p ≤ 17 * (p.rows + p.inner + p.cols + 1) ^ 3 := by
  have ht := matrixMultiplyTime_le_cubic p
  unfold matrixMultiplyReturnTime matrixMultiplyTime at *
  omega

theorem matrixMultiplyProgram_nohalt (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch) (k : ℕ)
    (hk : k < matrixMultiplyReturnTime p) :
    instructionIsHalt (matrixMultiplyProgram.code
      ((ordinaryStep matrixMultiplyProgram)^[k] (matrixMultiplyRowState p 0 scratch)).label) =
      false := by
  obtain ⟨result, hr⟩ := matrixMultiplyProgram_return p h scratch
  have hfinal : ((ordinaryStep matrixMultiplyProgram)^[matrixMultiplyReturnTime p]
      (matrixMultiplyRowState p 0 scratch)).status = .running := by rw [hr]; rfl
  exact ordinary_nohalt_prefix_of_running _ _ hfinal k hk

/-- Every legal caller trace executes the local multiplication and reaches its
own continuation. Charges are measured in that actual caller trace; registers
outside the injected frame retain their values at the call time. -/
theorem RoutineEmbedding.matrixMultiply_run_at {Q : Program}
    (E : RoutineEmbedding matrixMultiplyProgram Q) (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState p 0 scratch) (trace.state offset)) :
    ∃ result : MatrixMultiplyScratch,
      E.Relates (matrixMultiplyReturnState p result)
        (trace.state (offset + matrixMultiplyReturnTime p)) ∧
      CostThrough Q trace (offset + matrixMultiplyReturnTime p) ≤
        CostThrough Q trace offset + matrixMultiplyReturnTime p ∧
      CostThrough Q trace (offset + matrixMultiplyReturnTime p) ≤
        CostThrough Q trace offset + 17 * (p.rows + p.inner + p.cols + 1) ^ 3 ∧
      (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →
        (trace.state (offset + matrixMultiplyReturnTime p)).real j = (trace.state offset).real j) ∧
      (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
        (trace.state (offset + matrixMultiplyReturnTime p)).natural j =
          (trace.state offset).natural j) := by
  obtain ⟨result, hr⟩ := matrixMultiplyProgram_return p h scratch
  have hno := matrixMultiplyProgram_nohalt p h scratch
  have hscalar : ∀ k < matrixMultiplyReturnTime p,
      instructionIsSVD (matrixMultiplyProgram.code
        ((ordinaryStep matrixMultiplyProgram)^[k] (matrixMultiplyRowState p 0 scratch)).label) =
        false := fun _ _ => matrixMultiplyProgram_scalar _
  have htail := legalTrace_shift ht offset
  have hrel := E.scalar_trace_prefix _ hs htail _ hno hscalar
  have hcost := E.scalar_trace_cost_le _ hs htail _ hno hscalar
  have hc : CostThrough Q trace (offset + matrixMultiplyReturnTime p) ≤
      CostThrough Q trace offset + matrixMultiplyReturnTime p :=
    costThrough_compose_le le_rfl hcost
  rw [hr] at hrel
  refine ⟨result, hrel, hc, ?_, ?_, ?_⟩
  · exact hc.trans (Nat.add_le_add_left (matrixMultiplyReturnTime_le_cubic p) _)
  · intro j hj
    exact E.scalar_trace_real_outside _ hs htail _ hno hscalar j hj
  · intro j hj
    exact E.scalar_trace_natural_outside _ hs htail _ hno hscalar j hj

/-- Literal caller fields at the return point, without executing the local halt. -/
theorem RoutineEmbedding.matrixMultiply_product_at {Q : Program}
    (E : RoutineEmbedding matrixMultiplyProgram Q) (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    {start : State Q} {trace : Trace Q} (ht : LegalTrace Q start trace) (offset : ℕ)
    (hs : E.Relates (matrixMultiplyRowState p 0 scratch) (trace.state offset)) :
    (trace.state (offset + matrixMultiplyReturnTime p)).label = E.labels 21 ∧
    (trace.state (offset + matrixMultiplyReturnTime p)).status = .running ∧
    readMatrix (trace.state (offset + matrixMultiplyReturnTime p)).memory
      p.rows p.cols p.dBase = p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (trace.state (offset + matrixMultiplyReturnTime p)).memory address = p.memory address) ∧
    CostThrough Q trace (offset + matrixMultiplyReturnTime p) ≤
      CostThrough Q trace offset + 17 * (p.rows + p.inner + p.cols + 1) ^ 3 ∧
    (∀ j : Fin Q.realRegisters, (∀ i, j ≠ E.reals i) →
      (trace.state (offset + matrixMultiplyReturnTime p)).real j = (trace.state offset).real j) ∧
    (∀ j : Fin (Q.extraNatRegisters + 1), (∀ i, j ≠ E.naturals i) →
      (trace.state (offset + matrixMultiplyReturnTime p)).natural j =
        (trace.state offset).natural j) := by
  obtain ⟨result, hr, _, hc, hreal, hnatural⟩ :=
    E.matrixMultiply_run_at p h scratch ht offset hs
  obtain ⟨_, _, hp, ho⟩ := matrixMultiplyReturnState_product p result
  refine ⟨hr.label, hr.status, ?_, ?_, hc, hreal, hnatural⟩
  · rw [hr.memory]
    exact hp
  · rw [hr.memory]
    exact ho

#assert_trust kernel matrixMultiplyProgram_return
#assert_trust kernel matrixMultiplyReturnState_product
#assert_trust kernel matrixMultiplyReturnTime_le_cubic
#assert_trust kernel matrixMultiplyProgram_nohalt
#assert_trust kernel RoutineEmbedding.matrixMultiply_run_at
#assert_trust kernel RoutineEmbedding.matrixMultiply_product_at
#print axioms matrixMultiplyProgram_return
#print axioms RoutineEmbedding.matrixMultiply_run_at
#print axioms RoutineEmbedding.matrixMultiply_product_at
end NLA.Proofs.TR04
