import NLA.Proofs.TR04.MachineCopy
import NLA.Proofs.TR04.MachineHeaderDecode
import NLA.Proofs.TR04.MachineRelocation
import Mathlib.Tactic.IntervalCases

/-! The actual copy/header programs as callable instruction blocks. Execution
stops at their halt labels before executing those labels, which may hold caller
continuation code. The bounds concern the caller's actual legal trace. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

theorem copyProgram_nohalt_phase (memory : ℕ → ℝ) (src dst count i : ℕ) (scratch : ℝ)
    (hi : i < count) (j : Fin 6) :
    instructionIsHalt (copyProgram.code
      ((ordinaryStep copyProgram)^[j.val] (copyLoopState memory src dst count i scratch)).label) = false := by
  fin_cases j <;>
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      copyProgram, copyLoopState, instructionIsHalt, hi] <;> rfl

theorem copyProgram_nohalt_prefix (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hd : DisjointBlocks src count dst count) (k : ℕ) (hk : k < 6 * count + 1) :
    instructionIsHalt (copyProgram.code
      ((ordinaryStep copyProgram)^[k] (copyLoopState memory src dst count 0 scratch)).label) = false := by
  have hmod : k % 6 < 6 := Nat.mod_lt _ (by omega)
  have hdecomp : k = k % 6 + 6 * (k / 6) := by omega
  by_cases hi : k / 6 < count
  · obtain ⟨value,hv⟩ := copyProgram_iterations memory src dst count scratch hd (k / 6) (by omega)
    rw [hdecomp, Function.iterate_add_apply, hv]
    exact copyProgram_nohalt_phase memory src dst count (k / 6) value hi ⟨k % 6,hmod⟩
  · have heq : k = 6 * count := by omega
    obtain ⟨value,hv⟩ := copyProgram_iterations memory src dst count scratch hd count le_rfl
    rw [heq,hv]
    rfl

def copyReturnState (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ) :
    State copyProgram := { copyLoopState memory src dst count count scratch with label := 6 }

theorem copyProgram_return (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hd : DisjointBlocks src count dst count) :
    ∃ value : ℝ,
      (ordinaryStep copyProgram)^[6 * count + 1] (copyLoopState memory src dst count 0 scratch) =
        copyReturnState memory src dst count value := by
  obtain ⟨value,hv⟩ := copyProgram_iterations memory src dst count scratch hd count le_rfl
  refine ⟨value,?_⟩
  rw [Function.iterate_succ_apply',hv]
  apply machineState_ext <;>
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, ordinaryStep, copyProgram, copyLoopState,
      copyReturnState] <;> rfl

/-- Copy is callable inside any literal embedding; continuation code is arbitrary. -/
theorem RoutineEmbedding.copy_run {Q : Program} (E : RoutineEmbedding copyProgram Q)
    (memory : ℕ → ℝ) (src dst count : ℕ) (scratch : ℝ)
    (hd : DisjointBlocks src count dst count) {start : State Q} {trace : Trace Q}
    (hs : E.Relates (copyLoopState memory src dst count 0 scratch) start)
    (ht : LegalTrace Q start trace) :
    (∃ value : ℝ, E.Relates (copyReturnState memory src dst count value)
      (trace.state (6 * count + 1))) ∧ CostThrough Q trace (6 * count + 1) ≤ 6 * count + 1 := by
  have hno := copyProgram_nohalt_prefix memory src dst count scratch hd
  have hscalar : ∀ k < 6 * count + 1, instructionIsSVD (copyProgram.code
      ((ordinaryStep copyProgram)^[k] (copyLoopState memory src dst count 0 scratch)).label) = false :=
    fun _ _ => copyProgram_scalar _
  obtain ⟨value,hv⟩ := copyProgram_return memory src dst count scratch hd
  refine ⟨⟨value,?_⟩, E.scalar_trace_cost_le _ hs ht _ hno hscalar⟩
  have hr := E.scalar_trace_prefix _ hs ht _ hno hscalar
  rwa [hv] at hr

theorem decodeNaturalProgram_nohalt_phase (memory : ℕ → ℝ) (base count i : ℕ)
    (scratch : ℝ) (hi : i < count) (j : Fin 3) :
    instructionIsHalt (decodeNaturalProgram.code
      ((ordinaryStep decodeNaturalProgram)^[j.val] (decodeNaturalLoopState memory base count i scratch)).label) = false := by
  have hne : (i : ℝ) ≠ (count : ℝ) := by exact_mod_cast (Nat.ne_of_lt hi)
  fin_cases j <;>
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      decodeNaturalProgram, decodeNaturalLoopState, instructionIsHalt, hne]

theorem decodeNaturalProgram_nohalt_initial (memory : ℕ → ℝ) (base count i : ℕ)
    (scratch : ℝ) (j : Fin 2) :
    instructionIsHalt (decodeNaturalProgram.code
      ((ordinaryStep decodeNaturalProgram)^[j.val] (decodeNaturalLoopState memory base count i scratch)).label) = false := by
  fin_cases j <;>
    simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      decodeNaturalProgram, decodeNaturalLoopState, instructionIsHalt]

theorem decodeNaturalProgram_nohalt_prefix (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ)
    (k : ℕ) (hk : k < 3 * count + 2) :
    instructionIsHalt (decodeNaturalProgram.code
      ((ordinaryStep decodeNaturalProgram)^[k] (decodeNaturalLoopState memory base count 0 scratch)).label) = false := by
  have hmod : k % 3 < 3 := Nat.mod_lt _ (by omega)
  have hdecomp : k = k % 3 + 3 * (k / 3) := by omega
  by_cases hi : k / 3 < count
  · obtain ⟨value,hv⟩ := decodeNaturalProgram_iterations memory base count scratch (k / 3) (by omega)
    rw [hdecomp, Function.iterate_add_apply, hv]
    exact decodeNaturalProgram_nohalt_phase memory base count (k / 3) value hi ⟨k % 3,hmod⟩
  · have heq : k / 3 = count := by omega
    have hj : k % 3 < 2 := by omega
    obtain ⟨value,hv⟩ := decodeNaturalProgram_iterations memory base count scratch (k / 3) (by omega)
    rw [hdecomp, Function.iterate_add_apply, hv]
    exact decodeNaturalProgram_nohalt_initial memory base count (k / 3) value ⟨k % 3,hj⟩

def decodeNaturalReturnState (memory : ℕ → ℝ) (base count : ℕ) :
    State decodeNaturalProgram := { decodeNaturalFinalState memory base count with status := .running }

theorem decodeNaturalProgram_return (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ) :
    (ordinaryStep decodeNaturalProgram)^[3 * count + 2]
      (decodeNaturalLoopState memory base count 0 scratch) =
        decodeNaturalReturnState memory base count := by
  obtain ⟨value,hv⟩ := decodeNaturalProgram_iterations memory base count scratch count le_rfl
  rw [Nat.add_comm (3 * count) 2, Function.iterate_add_apply, hv]
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    decodeNaturalProgram, decodeNaturalLoopState, decodeNaturalReturnState, decodeNaturalFinalState]
  all_goals try rfl
  funext k
  fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff]

/-- The header decoder can be called inside a fixed caller program, which resumes
at the mapped exit with the exact decoded natural in its injected register. -/
theorem RoutineEmbedding.decodeNatural_run {Q : Program} (E : RoutineEmbedding decodeNaturalProgram Q)
    (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ)
    {start : State Q} {trace : Trace Q}
    (hs : E.Relates (decodeNaturalLoopState memory base count 0 scratch) start)
    (ht : LegalTrace Q start trace) :
    E.Relates (decodeNaturalReturnState memory base count) (trace.state (3 * count + 2)) ∧
      CostThrough Q trace (3 * count + 2) ≤ 3 * count + 2 := by
  have hno := decodeNaturalProgram_nohalt_prefix memory base count scratch
  have hscalar : ∀ k < 3 * count + 2, instructionIsSVD (decodeNaturalProgram.code
      ((ordinaryStep decodeNaturalProgram)^[k] (decodeNaturalLoopState memory base count 0 scratch)).label) = false :=
    fun _ _ => decodeNaturalProgram_scalar _
  refine ⟨?_,E.scalar_trace_cost_le _ hs ht _ hno hscalar⟩
  have hr := E.scalar_trace_prefix _ hs ht _ hno hscalar
  rwa [decodeNaturalProgram_return] at hr

#assert_trust kernel decodeNaturalProgram_nohalt_phase
#assert_trust kernel decodeNaturalProgram_nohalt_initial
#assert_trust kernel decodeNaturalProgram_nohalt_prefix
#assert_trust kernel decodeNaturalProgram_return
#assert_trust kernel RoutineEmbedding.decodeNatural_run
#assert_trust kernel copyProgram_nohalt_phase
#assert_trust kernel copyProgram_nohalt_prefix
#assert_trust kernel copyProgram_return
#assert_trust kernel RoutineEmbedding.copy_run
#print axioms RoutineEmbedding.copy_run
end NLA.Proofs.TR04
