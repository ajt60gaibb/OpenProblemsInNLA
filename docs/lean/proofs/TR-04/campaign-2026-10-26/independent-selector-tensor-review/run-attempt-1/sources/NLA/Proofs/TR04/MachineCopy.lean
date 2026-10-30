import NLA.Proofs.TR04.MachineScalarBlocks
import Mathlib.Tactic.FinCases

/-! A fixed actual finite RAM program for copying a dense array. All reads,
writes, counter updates, branches and the final halt are instructions of the
unchanged machine. This is an implementation component, not the TT solver. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Natural registers: index, count, source pointer, destination pointer,
retained output base. Real register zero is the one-cell read/write scratch. -/
def copyProgram : Program where
  extraLabels := 6
  realRegisters := 1
  extraNatRegisters := 4
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .lessNat 0 1 1 6
    | 1 => .read 0 2 2
    | 2 => .write 3 0 3
    | 3 => .increment 2 4
    | 4 => .increment 3 5
    | 5 => .increment 0 0
    | _ => .halt 4

def copiedMemory (memory : ℕ → ℝ) (src dst count address : ℕ) : ℝ :=
  if dst ≤ address ∧ address < dst + count then memory (src + (address - dst))
  else memory address

/-- Invariant at the loop label after precisely i entries have been copied. -/
def copyLoopState (memory : ℕ → ℝ) (src dst count i : ℕ) (scratch : ℝ) :
    State copyProgram where
  label := 0
  real := fun _ => scratch
  natural := ![i, count, src + i, dst + i, dst]
  memory := copiedMemory memory src dst i
  status := .running

theorem copiedMemory_zero (memory : ℕ → ℝ) (src dst : ℕ) :
    copiedMemory memory src dst 0 = memory := by
  funext a
  simp [copiedMemory]

theorem copiedMemory_outside (memory : ℕ → ℝ) (src dst count a : ℕ)
    (ha : ¬ (dst ≤ a ∧ a < dst + count)) :
    copiedMemory memory src dst count a = memory a := by
  simp [copiedMemory, ha]

theorem copiedMemory_source_next (memory : ℕ → ℝ) (src dst count i : ℕ)
    (hdisjoint : DisjointBlocks src count dst count) (hi : i < count) :
    copiedMemory memory src dst i (src + i) = memory (src + i) := by
  apply copiedMemory_outside
  rcases hdisjoint with hz | hz | hsd | hds <;> omega

theorem copiedMemory_succ (memory : ℕ → ℝ) (src dst i : ℕ) :
    Function.update (copiedMemory memory src dst i) (dst + i) (memory (src + i)) =
      copiedMemory memory src dst (i + 1) := by
  funext a
  by_cases ha : a = dst + i
  · subst a
    simp [copiedMemory]
  · rw [Function.update_of_ne ha]
    unfold copiedMemory
    by_cases h : dst ≤ a ∧ a < dst + i
    · have h' : dst ≤ a ∧ a < dst + (i + 1) := by omega
      rw [if_pos h, if_pos h']
    · have h' : ¬ (dst ≤ a ∧ a < dst + (i + 1)) := by omega
      rw [if_neg h, if_neg h']

theorem copyProgram_scalar (s : State copyProgram) :
    instructionIsSVD (copyProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

/-- One complete iteration has exactly six literal transitions. -/
theorem copyProgram_six_steps (memory : ℕ → ℝ) (src dst count i : ℕ) (scratch : ℝ)
    (hdisjoint : DisjointBlocks src count dst count) (hi : i < count) :
    (ordinaryStep copyProgram)^[6] (copyLoopState memory src dst count i scratch) =
      copyLoopState memory src dst count (i + 1) (memory (src + i)) := by
  classical
  have hsrc := copiedMemory_source_next memory src dst count i hdisjoint hi
  have hmem := copiedMemory_succ memory src dst i
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe, -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep, copyProgram, copyLoopState,
    hi, hsrc, hmem]
  all_goals try rfl
  · funext k
    fin_cases k
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe, -Fin.val_eq_zero_iff, Fin.ext_iff]
  · funext k
    fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe, -Fin.val_eq_zero_iff, Fin.ext_iff, Nat.add_assoc]

/-- Every complete iteration follows the same literal loop invariant. -/
theorem copyProgram_iterations (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hdisjoint : DisjointBlocks src count dst count) (i : ℕ) (hi : i ≤ count) :
    ∃ value : ℝ,
      (ordinaryStep copyProgram)^[6 * i] (copyLoopState memory src dst count 0 scratch) =
        copyLoopState memory src dst count i value := by
  induction i with
  | zero => exact ⟨scratch, rfl⟩
  | succ i ih =>
      obtain ⟨value, hv⟩ := ih (by omega)
      refine ⟨memory (src + i), ?_⟩
      rw [Nat.mul_succ, Nat.add_comm (6 * i) 6, Function.iterate_add_apply, hv]
      exact copyProgram_six_steps memory src dst count i value hdisjoint (by omega)

def copyFinalState (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ) :
    State copyProgram :=
  { copyLoopState memory src dst count count scratch with label := 6, status := .halted dst }

/-- The failed loop test and actual halt instruction take two more transitions. -/
theorem copyProgram_exit (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ) :
    (ordinaryStep copyProgram)^[2] (copyLoopState memory src dst count count scratch) =
      copyFinalState memory src dst count scratch := by
  apply machineState_ext <;>
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      copyProgram, copyLoopState, copyFinalState] <;> rfl

/-- Every legal trace reaches the actual copied memory and retained output pointer. -/
theorem copyProgram_trace_result (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hdisjoint : DisjointBlocks src count dst count) (trace : Trace copyProgram)
    (htrace : LegalTrace copyProgram (copyLoopState memory src dst count 0 scratch) trace) :
    ∃ value : ℝ, trace.state (6 * count + 2) = copyFinalState memory src dst count value := by
  obtain ⟨value, hv⟩ := copyProgram_iterations memory src dst count scratch hdisjoint count le_rfl
  refine ⟨value, ?_⟩
  rw [legalTrace_scalar_prefix htrace _ (fun _ _ _ => copyProgram_scalar _),
    Nat.add_comm (6 * count) 2, Function.iterate_add_apply, hv]
  exact copyProgram_exit memory src dst count value

theorem copyProgram_trace_cells (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hdisjoint : DisjointBlocks src count dst count) (trace : Trace copyProgram)
    (htrace : LegalTrace copyProgram (copyLoopState memory src dst count 0 scratch) trace) :
    (trace.state (6 * count + 2)).status = .halted dst ∧
      (∀ i < count, (trace.state (6 * count + 2)).memory (dst + i) = memory (src + i)) ∧
      (∀ a, ¬ (dst ≤ a ∧ a < dst + count) →
        (trace.state (6 * count + 2)).memory a = memory a) := by
  obtain ⟨value, hv⟩ := copyProgram_trace_result memory src dst count scratch hdisjoint trace htrace
  rw [hv]
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    simp [copyFinalState, copyLoopState, copiedMemory, hi]
  · intro a ha
    exact copiedMemory_outside memory src dst count a ha

/-- The literal copy run has a linear bound under the model's actual charge. -/
theorem copyProgram_trace_cost (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (trace : Trace copyProgram)
    (htrace : LegalTrace copyProgram (copyLoopState memory src dst count 0 scratch) trace) :
    CostThrough copyProgram trace (6 * count + 2) ≤ 6 * count + 2 :=
  costThrough_le_scalar htrace copyProgram_scalar _

#assert_trust kernel copyProgram_trace_cost
#assert_trust kernel copyProgram
#assert_trust kernel copiedMemory_zero
#assert_trust kernel copiedMemory_source_next
#assert_trust kernel copiedMemory_succ
#assert_trust kernel copyProgram_scalar
#assert_trust kernel copyProgram_six_steps
#assert_trust kernel copyProgram_iterations
#assert_trust kernel copyProgram_exit
#assert_trust kernel copyProgram_trace_result
#assert_trust kernel copyProgram_trace_cells
#print axioms copyProgram_trace_cells
end NLA.Proofs.TR04
