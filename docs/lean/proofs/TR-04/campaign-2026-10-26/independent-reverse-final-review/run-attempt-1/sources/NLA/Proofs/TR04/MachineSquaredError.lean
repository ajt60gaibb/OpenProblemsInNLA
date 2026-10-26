import NLA.Proofs.TR04.MachineTraceComposition
import Mathlib.Tactic.FinCases

/-! One fixed literal finite-RAM program computes the squared error of two
dense arrays. It performs only actual reads and scalar arithmetic, and never
writes memory. Its output is actual real register zero. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Real registers: accumulator, first/square scratch, second scratch.
Natural registers: index, count, first pointer, second pointer, halt address. -/
def squaredErrorProgram : Program where
  extraLabels := 10
  realRegisters := 3
  extraNatRegisters := 4
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .subReal 0 0 0 1
    | 1 => .lessNat 0 1 2 10
    | 2 => .read 1 2 3
    | 3 => .read 2 3 4
    | 4 => .subReal 1 1 2 5
    | 5 => .mulReal 1 1 1 6
    | 6 => .addReal 0 0 1 7
    | 7 => .increment 2 8
    | 8 => .increment 3 9
    | 9 => .increment 0 1
    | _ => .halt 4

instance squaredErrorProgram_nonzero_realRegisters : NeZero squaredErrorProgram.realRegisters :=
  ⟨by decide⟩

def squaredErrorSum (memory : ℕ → ℝ) (baseA baseB count : ℕ) : ℝ :=
  ∑ i ∈ Finset.range count, (memory (baseA + i) - memory (baseB + i))^2

theorem squaredErrorSum_zero (memory : ℕ → ℝ) (baseA baseB : ℕ) :
    squaredErrorSum memory baseA baseB 0 = 0 := by simp [squaredErrorSum]

theorem squaredErrorSum_succ (memory : ℕ → ℝ) (baseA baseB i : ℕ) :
    squaredErrorSum memory baseA baseB (i + 1) = squaredErrorSum memory baseA baseB i +
      (memory (baseA + i) - memory (baseB + i))^2 := by
  exact Finset.sum_range_succ _ _

def squaredErrorLoopState (memory : ℕ → ℝ) (baseA baseB count i : ℕ)
    (scratchA scratchB : ℝ) : State squaredErrorProgram where
  label := 1
  real := ![squaredErrorSum memory baseA baseB i, scratchA, scratchB]
  natural := ![i, count, baseA + i, baseB + i, 0]
  memory := memory
  status := .running

def squaredErrorStart (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) : State squaredErrorProgram :=
  { squaredErrorLoopState memory baseA baseB count 0 scratchA scratchB with
    label := 0, real := ![accumulator, scratchA, scratchB] }

theorem squaredErrorProgram_scalar (s : State squaredErrorProgram) :
    instructionIsSVD (squaredErrorProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

theorem squaredErrorProgram_initialize (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) :
    ordinaryStep squaredErrorProgram (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) =
      squaredErrorLoopState memory baseA baseB count 0 scratchA scratchB := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, ordinaryStep, squaredErrorProgram,
    squaredErrorStart, squaredErrorLoopState, squaredErrorSum_zero]
  all_goals try rfl
  funext k
  fin_cases k <;> simp [Function.update, Fin.ext_iff]

set_option maxHeartbeats 1000000 in
theorem squaredErrorProgram_nine_steps (memory : ℕ → ℝ) (baseA baseB count i : ℕ)
    (scratchA scratchB : ℝ) (hi : i < count) :
    (ordinaryStep squaredErrorProgram)^[9] (squaredErrorLoopState memory baseA baseB count i scratchA scratchB) =
      squaredErrorLoopState memory baseA baseB count (i + 1)
        ((memory (baseA + i) - memory (baseB + i))^2) (memory (baseB + i)) := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    squaredErrorProgram, squaredErrorLoopState, hi]
  all_goals try rfl
  · funext k
    fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, squaredErrorSum_succ, pow_two]
  · funext k
    fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Nat.add_assoc]

theorem squaredErrorProgram_iterations (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (scratchA scratchB : ℝ) (i : ℕ) (hi : i ≤ count) :
    ∃ a b : ℝ, (ordinaryStep squaredErrorProgram)^[9 * i]
      (squaredErrorLoopState memory baseA baseB count 0 scratchA scratchB) =
        squaredErrorLoopState memory baseA baseB count i a b := by
  induction i with
  | zero => exact ⟨scratchA, scratchB, rfl⟩
  | succ i ih =>
    obtain ⟨a, b, hv⟩ := ih (by omega)
    refine ⟨(memory (baseA + i) - memory (baseB + i))^2, memory (baseB + i), ?_⟩
    rw [Nat.mul_succ, Nat.add_comm (9 * i) 9, Function.iterate_add_apply, hv]
    exact squaredErrorProgram_nine_steps memory baseA baseB count i a b (by omega)

def squaredErrorFinalState (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (scratchA scratchB : ℝ) : State squaredErrorProgram :=
  { squaredErrorLoopState memory baseA baseB count count scratchA scratchB with
    label := 10, status := .halted 0 }

theorem squaredErrorProgram_exit (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (scratchA scratchB : ℝ) :
    (ordinaryStep squaredErrorProgram)^[2]
      (squaredErrorLoopState memory baseA baseB count count scratchA scratchB) =
        squaredErrorFinalState memory baseA baseB count scratchA scratchB := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Function.iterate_succ_apply', ordinaryStep,
    squaredErrorProgram, squaredErrorLoopState, squaredErrorFinalState]
  all_goals rfl

theorem squaredErrorProgram_finish (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) :
    ∃ a b : ℝ, (ordinaryStep squaredErrorProgram)^[9 * count + 3]
      (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) =
        squaredErrorFinalState memory baseA baseB count a b := by
  obtain ⟨a, b, hv⟩ := squaredErrorProgram_iterations memory baseA baseB count
    scratchA scratchB count le_rfl
  have hinit : (ordinaryStep squaredErrorProgram)^[9 * count + 1]
      (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) =
        squaredErrorLoopState memory baseA baseB count count a b := by
    rw [Function.iterate_succ_apply, squaredErrorProgram_initialize, hv]
  refine ⟨a, b, ?_⟩
  rw [show 9 * count + 3 = 2 + (9 * count + 1) by omega,
    Function.iterate_add_apply, hinit]
  exact squaredErrorProgram_exit memory baseA baseB count a b

/-- Every legal trace halts with the literal squared error in real register zero
and preserves every input memory cell, including when the count is zero. -/
theorem squaredErrorProgram_trace_result (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) (trace : Trace squaredErrorProgram)
    (htrace : LegalTrace squaredErrorProgram
      (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) trace) :
    (trace.state (9 * count + 3)).status = .halted 0 ∧
      (trace.state (9 * count + 3)).real 0 = squaredErrorSum memory baseA baseB count ∧
      (trace.state (9 * count + 3)).memory = memory := by
  obtain ⟨a, b, hv⟩ := squaredErrorProgram_finish memory baseA baseB count
    accumulator scratchA scratchB
  rw [legalTrace_scalar_prefix htrace _ (fun _ _ _ => squaredErrorProgram_scalar _), hv]
  exact ⟨rfl, rfl, rfl⟩

theorem squaredErrorProgram_trace_cost (memory : ℕ → ℝ) (baseA baseB count : ℕ)
    (accumulator scratchA scratchB : ℝ) (trace : Trace squaredErrorProgram)
    (htrace : LegalTrace squaredErrorProgram
      (squaredErrorStart memory baseA baseB count accumulator scratchA scratchB) trace) :
    CostThrough squaredErrorProgram trace (9 * count + 3) ≤ 9 * count + 3 :=
  costThrough_le_scalar htrace squaredErrorProgram_scalar _

#assert_trust kernel squaredErrorProgram
#assert_trust kernel squaredErrorProgram_initialize
#assert_trust kernel squaredErrorProgram_nine_steps
#assert_trust kernel squaredErrorProgram_iterations
#assert_trust kernel squaredErrorProgram_exit
#assert_trust kernel squaredErrorProgram_finish
#assert_trust kernel squaredErrorProgram_trace_result
#assert_trust kernel squaredErrorProgram_trace_cost
#print axioms squaredErrorProgram_trace_result
end NLA.Proofs.TR04
