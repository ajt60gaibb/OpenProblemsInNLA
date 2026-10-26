import NLA.Proofs.TR04.MachineMatrixMultiply

/-! Every legal run of the fixed strided matrix multiplication program returns
the actual matrix product, preserves all other memory, and has an explicit
polynomial bound in the literal charged trace semantics. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def matrixMultiplyCellTime (p : MatrixMultiplyData) : ℕ := 8 * p.inner + 11
def matrixMultiplyRowTime (p : MatrixMultiplyData) : ℕ :=
  matrixMultiplyCellTime p * p.cols + 4
def matrixMultiplyTime (p : MatrixMultiplyData) : ℕ :=
  matrixMultiplyRowTime p * p.rows + 2

def matrixMultiplyStart (p : MatrixMultiplyData) : State matrixMultiplyProgram :=
  matrixMultiplyState p 0 p.cols 0 0 0 p.dBase (fun _ => 0) p.memory 0

theorem matrixMultiplyStart_eq_row (p : MatrixMultiplyData) :
    matrixMultiplyStart p = matrixMultiplyRowState p 0 ⟨0, 0, 0, fun _ => 0⟩ := by
  simp [matrixMultiplyStart, matrixMultiplyRowState, MatrixMultiplyData.outputPrefix,
    prefixMemory_zero]

theorem matrixMultiplyProgram_exists_trace (p : MatrixMultiplyData) :
    ∃ trace : Trace matrixMultiplyProgram,
      LegalTrace matrixMultiplyProgram (matrixMultiplyStart p) trace := by
  apply exists_legalTrace_of_step_total
  intro s
  exact ⟨ordinaryStep matrixMultiplyProgram s,
    (step_iff_ordinary_of_scalar (fun _ => matrixMultiplyProgram_scalar s)).2 ⟨rfl, rfl⟩⟩

theorem matrixMultiplyProgram_cell (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (i j : ℕ) (scratch : MatrixMultiplyScratch)
    (hi : i < p.rows) (hj : j < p.cols) :
    ∃ result : MatrixMultiplyScratch,
      (ordinaryStep matrixMultiplyProgram)^[matrixMultiplyCellTime p]
        (matrixMultiplyCellState p i j scratch) = matrixMultiplyCellState p i (j + 1) result := by
  obtain ⟨rb, rc, hs⟩ := matrixMultiplyProgram_inner_iterations p h i j
    (scratch.real 1) (scratch.real 2) hi hj p.inner le_rfl
  refine ⟨⟨p.inner, p.bAddress i p.inner, p.cAddress p.inner j,
    ![p.partialProduct i j p.inner, rb, rc]⟩, ?_⟩
  have ht : matrixMultiplyCellTime p = 4 + (8 * p.inner + 7) := by
    unfold matrixMultiplyCellTime
    omega
  rw [ht, Function.iterate_add_apply, Function.iterate_add_apply,
    matrixMultiplyProgram_cell_setup p i j scratch hj, hs]
  exact matrixMultiplyProgram_cell_exit p i j rb rc hi hj

theorem matrixMultiplyProgram_cells (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (i : ℕ) (scratch : MatrixMultiplyScratch)
    (hi : i < p.rows) (j : ℕ) (hj : j ≤ p.cols) :
    ∃ result : MatrixMultiplyScratch,
      (ordinaryStep matrixMultiplyProgram)^[matrixMultiplyCellTime p * j]
        (matrixMultiplyCellState p i 0 scratch) = matrixMultiplyCellState p i j result := by
  induction j with
  | zero => exact ⟨scratch, rfl⟩
  | succ j ih =>
      obtain ⟨middle, hm⟩ := ih (by omega)
      obtain ⟨result, hr⟩ := matrixMultiplyProgram_cell p h i j middle hi (by omega)
      refine ⟨result, ?_⟩
      rw [Nat.mul_succ, Nat.add_comm (matrixMultiplyCellTime p * j),
        Function.iterate_add_apply, hm]
      exact hr

theorem matrixMultiplyProgram_row_setup (p : MatrixMultiplyData)
    (i : ℕ) (scratch : MatrixMultiplyScratch) (hi : i < p.rows) :
    (ordinaryStep matrixMultiplyProgram)^[2] (matrixMultiplyRowState p i scratch) =
      matrixMultiplyCellState p i 0 scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Function.iterate_succ_apply', ordinaryStep,
    matrixMultiplyProgram, matrixMultiplyRowState, matrixMultiplyCellState,
    matrixMultiplyState, hi]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem matrixMultiplyProgram_row_exit (p : MatrixMultiplyData)
    (i : ℕ) (scratch : MatrixMultiplyScratch) :
    (ordinaryStep matrixMultiplyProgram)^[2] (matrixMultiplyCellState p i p.cols scratch) =
      matrixMultiplyRowState p (i + 1) scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Function.iterate_succ_apply', ordinaryStep,
    matrixMultiplyProgram, matrixMultiplyRowState, matrixMultiplyCellState,
    matrixMultiplyState, Nat.add_mul, Nat.add_assoc]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem matrixMultiplyProgram_row (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (i : ℕ) (scratch : MatrixMultiplyScratch)
    (hi : i < p.rows) :
    ∃ result : MatrixMultiplyScratch,
      (ordinaryStep matrixMultiplyProgram)^[matrixMultiplyRowTime p]
        (matrixMultiplyRowState p i scratch) = matrixMultiplyRowState p (i + 1) result := by
  obtain ⟨result, hr⟩ := matrixMultiplyProgram_cells p h i scratch hi p.cols le_rfl
  refine ⟨result, ?_⟩
  have ht : matrixMultiplyRowTime p = 2 + (matrixMultiplyCellTime p * p.cols + 2) := by
    unfold matrixMultiplyRowTime
    omega
  rw [ht, Function.iterate_add_apply, Function.iterate_add_apply,
    matrixMultiplyProgram_row_setup p i scratch hi, hr]
  exact matrixMultiplyProgram_row_exit p i result

theorem matrixMultiplyProgram_rows (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    (i : ℕ) (hi : i ≤ p.rows) :
    ∃ result : MatrixMultiplyScratch,
      (ordinaryStep matrixMultiplyProgram)^[matrixMultiplyRowTime p * i]
        (matrixMultiplyRowState p 0 scratch) = matrixMultiplyRowState p i result := by
  induction i with
  | zero => exact ⟨scratch, rfl⟩
  | succ i ih =>
      obtain ⟨middle, hm⟩ := ih (by omega)
      obtain ⟨result, hr⟩ := matrixMultiplyProgram_row p h i middle (by omega)
      refine ⟨result, ?_⟩
      rw [Nat.mul_succ, Nat.add_comm (matrixMultiplyRowTime p * i),
        Function.iterate_add_apply, hm]
      exact hr

def matrixMultiplyFinalState (p : MatrixMultiplyData) (scratch : MatrixMultiplyScratch) :
    State matrixMultiplyProgram :=
  { matrixMultiplyRowState p p.rows scratch with label := 21, status := .halted p.dBase }

theorem matrixMultiplyProgram_exit (p : MatrixMultiplyData) (scratch : MatrixMultiplyScratch) :
    (ordinaryStep matrixMultiplyProgram)^[2] (matrixMultiplyRowState p p.rows scratch) =
      matrixMultiplyFinalState p scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Function.iterate_succ_apply', ordinaryStep,
    matrixMultiplyProgram, matrixMultiplyFinalState, matrixMultiplyRowState,
    matrixMultiplyState]
  all_goals rfl

theorem matrixMultiplyProgram_trace_result (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyRowState p 0 scratch) trace) :
    ∃ result : MatrixMultiplyScratch,
      trace.state (matrixMultiplyTime p) = matrixMultiplyFinalState p result := by
  obtain ⟨result, hr⟩ := matrixMultiplyProgram_rows p h scratch p.rows le_rfl
  refine ⟨result, ?_⟩
  rw [legalTrace_scalar_prefix htrace _ (fun _ _ _ => matrixMultiplyProgram_scalar _),
    matrixMultiplyTime, Nat.add_comm (matrixMultiplyRowTime p * p.rows),
    Function.iterate_add_apply, hr]
  exact matrixMultiplyProgram_exit p result

/-- Exact readback of the actual matrix product and preservation of all other cells. -/
theorem matrixMultiplyProgram_trace_product (p : MatrixMultiplyData)
    (h : p.InputsOutsideOutput) (scratch : MatrixMultiplyScratch)
    (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyRowState p 0 scratch) trace) :
    (trace.state (matrixMultiplyTime p)).status = .halted p.dBase ∧
    readMatrix (trace.state (matrixMultiplyTime p)).memory p.rows p.cols p.dBase =
      p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (trace.state (matrixMultiplyTime p)).memory address = p.memory address) := by
  obtain ⟨result, hr⟩ := matrixMultiplyProgram_trace_result p h scratch trace htrace
  rw [hr]
  refine ⟨rfl, p.outputPrefix_read, ?_⟩
  intro address ha
  exact prefixMemory_outside _ _ _ _ _ ha

/-- The bound concerns the actual instruction charges, with no cost oracle. -/
theorem matrixMultiplyProgram_trace_cost (p : MatrixMultiplyData)
    (scratch : MatrixMultiplyScratch) (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyRowState p 0 scratch) trace) :
    CostThrough matrixMultiplyProgram trace (matrixMultiplyTime p) ≤
      ((8 * p.inner + 11) * p.cols + 4) * p.rows + 2 :=
  costThrough_le_scalar htrace matrixMultiplyProgram_scalar _

theorem matrixMultiplyTime_le_cubic (p : MatrixMultiplyData) :
    matrixMultiplyTime p ≤ 17 * (p.rows + p.inner + p.cols + 1) ^ 3 := by
  let s := p.rows + p.inner + p.cols + 1
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hm : p.rows ≤ s := by dsimp [s]; omega
  have hn : p.cols ≤ s := by dsimp [s]; omega
  have hf : 8 * p.inner + 11 ≤ 11 * s := by dsimp [s]; omega
  have hs2 : 1 ≤ s * s := by simpa only [Nat.one_mul] using Nat.mul_le_mul hs hs
  have hs3 : 1 ≤ s * s * s := by simpa only [Nat.one_mul] using Nat.mul_le_mul hs2 hs
  have hc : (8 * p.inner + 11) * p.cols ≤ 11 * (s * s) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hf hn
  have hr : (8 * p.inner + 11) * p.cols + 4 ≤ 15 * (s * s) := by omega
  have ht : ((8 * p.inner + 11) * p.cols + 4) * p.rows ≤ 15 * (s * s) * s :=
    Nat.mul_le_mul hr hm
  change ((8 * p.inner + 11) * p.cols + 4) * p.rows + 2 ≤ 17 * s ^ 3
  have hcubic : s ^ 3 = s * s * s := by simp [pow_succ]
  rw [hcubic]
  have hcomm : 15 * (s * s) * s = 15 * (s * s * s) := Nat.mul_assoc _ _ _
  rw [hcomm] at ht
  omega

/-- A caller can start with literal parameter registers and old memory. Every
legal trace then returns the product with a uniform cubic charged-cost bound. -/
theorem matrixMultiplyProgram_run (p : MatrixMultiplyData) (h : p.InputsOutsideOutput)
    (trace : Trace matrixMultiplyProgram)
    (htrace : LegalTrace matrixMultiplyProgram (matrixMultiplyStart p) trace) :
    (trace.state (matrixMultiplyTime p)).status = .halted p.dBase ∧
    readMatrix (trace.state (matrixMultiplyTime p)).memory p.rows p.cols p.dBase =
      p.leftMatrix * p.rightMatrix ∧
    (∀ address, ¬ (p.dBase ≤ address ∧ address < p.dBase + p.rows * p.cols) →
      (trace.state (matrixMultiplyTime p)).memory address = p.memory address) ∧
    CostThrough matrixMultiplyProgram trace (matrixMultiplyTime p) ≤
      17 * (p.rows + p.inner + p.cols + 1) ^ 3 := by
  rw [matrixMultiplyStart_eq_row] at htrace
  obtain ⟨hh, hp, ho⟩ := matrixMultiplyProgram_trace_product p h _ trace htrace
  exact ⟨hh, hp, ho, le_trans (matrixMultiplyProgram_trace_cost p _ trace htrace)
    (matrixMultiplyTime_le_cubic p)⟩

#assert_trust kernel matrixMultiplyProgram_trace_product
#assert_trust kernel matrixMultiplyProgram_trace_cost
#assert_trust kernel matrixMultiplyProgram_exists_trace
#assert_trust kernel matrixMultiplyProgram_run
#print axioms matrixMultiplyProgram_trace_product
#print axioms matrixMultiplyProgram_trace_cost
#print axioms matrixMultiplyProgram_exists_trace
#print axioms matrixMultiplyProgram_run
end NLA.Proofs.TR04
