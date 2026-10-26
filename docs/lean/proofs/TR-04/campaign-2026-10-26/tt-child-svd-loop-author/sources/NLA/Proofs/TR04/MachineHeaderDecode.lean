import NLA.Proofs.TR04.MachineScalarBlocks
import Mathlib.Tactic.FinCases

/-! Decode a real header known to contain a natural number using only literal
castNat, equality, increment and halt instructions. No real-to-natural opcode or
unbounded search oracle is introduced. The actual charged runtime is linear in
the encoded natural number. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Real0 retains the header, real1 the cast counter; nat0 is the counter,
nat1 the retained halt pointer. -/
def decodeNaturalProgram : Program where
  extraLabels := 3
  realRegisters := 2
  extraNatRegisters := 1
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .castNat 1 0 1
    | 1 => .equalReal 1 0 3 2
    | 2 => .increment 0 0
    | _ => .halt 1

def decodeNaturalLoopState (memory : ℕ → ℝ) (base count i : ℕ) (scratch : ℝ) :
    State decodeNaturalProgram where
  label := 0
  real := ![(count : ℝ), scratch]
  natural := ![i, base]
  memory := memory
  status := .running

theorem decodeNaturalProgram_scalar (s : State decodeNaturalProgram) :
    instructionIsSVD (decodeNaturalProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

/-- An unequal cast counter takes exactly three ordinary transitions. -/
theorem decodeNaturalProgram_three_steps (memory : ℕ → ℝ) (base count i : ℕ)
    (scratch : ℝ) (hi : i < count) :
    (ordinaryStep decodeNaturalProgram)^[3] (decodeNaturalLoopState memory base count i scratch) =
      decodeNaturalLoopState memory base count (i + 1) (i : ℝ) := by
  have hne : (i : ℝ) ≠ (count : ℝ) := by exact_mod_cast (Nat.ne_of_lt hi)
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    decodeNaturalProgram, decodeNaturalLoopState, hne]
  all_goals try rfl
  · funext k
    fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]
  · funext k
    fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem decodeNaturalProgram_iterations (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ)
    (i : ℕ) (hi : i ≤ count) :
    ∃ value : ℝ,
      (ordinaryStep decodeNaturalProgram)^[3 * i]
        (decodeNaturalLoopState memory base count 0 scratch) =
          decodeNaturalLoopState memory base count i value := by
  induction i with
  | zero => exact ⟨scratch, rfl⟩
  | succ i ih =>
      obtain ⟨value, hv⟩ := ih (by omega)
      refine ⟨(i : ℝ), ?_⟩
      rw [Nat.mul_succ, Nat.add_comm (3 * i) 3, Function.iterate_add_apply, hv]
      exact decodeNaturalProgram_three_steps memory base count i value (by omega)

def decodeNaturalFinalState (memory : ℕ → ℝ) (base count : ℕ) :
    State decodeNaturalProgram where
  label := 3
  real := ![(count : ℝ), (count : ℝ)]
  natural := ![count, base]
  memory := memory
  status := .halted base

theorem decodeNaturalProgram_exit (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ) :
    (ordinaryStep decodeNaturalProgram)^[3] (decodeNaturalLoopState memory base count count scratch) =
      decodeNaturalFinalState memory base count := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    decodeNaturalProgram, decodeNaturalLoopState, decodeNaturalFinalState]
  all_goals try rfl
  funext k
  fin_cases k <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff]

/-- Every legal execution decodes the natural header into an actual natural
register and halts with unchanged memory. -/
theorem decodeNaturalProgram_trace_result (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ)
    (trace : Trace decodeNaturalProgram)
    (htrace : LegalTrace decodeNaturalProgram (decodeNaturalLoopState memory base count 0 scratch) trace) :
    trace.state (3 * count + 3) = decodeNaturalFinalState memory base count := by
  obtain ⟨value, hv⟩ := decodeNaturalProgram_iterations memory base count scratch count le_rfl
  rw [legalTrace_scalar_prefix htrace _ (fun _ _ _ => decodeNaturalProgram_scalar _),
    Nat.add_comm (3 * count) 3, Function.iterate_add_apply, hv]
  exact decodeNaturalProgram_exit memory base count value

theorem decodeNaturalProgram_trace_cost (memory : ℕ → ℝ) (base count : ℕ) (scratch : ℝ)
    (trace : Trace decodeNaturalProgram)
    (htrace : LegalTrace decodeNaturalProgram (decodeNaturalLoopState memory base count 0 scratch) trace) :
    CostThrough decodeNaturalProgram trace (3 * count + 3) ≤ 3 * count + 3 :=
  costThrough_le_scalar htrace decodeNaturalProgram_scalar _

#assert_trust kernel decodeNaturalProgram
#assert_trust kernel decodeNaturalProgram_scalar
#assert_trust kernel decodeNaturalProgram_three_steps
#assert_trust kernel decodeNaturalProgram_iterations
#assert_trust kernel decodeNaturalProgram_exit
#assert_trust kernel decodeNaturalProgram_trace_result
#assert_trust kernel decodeNaturalProgram_trace_cost
#print axioms decodeNaturalProgram_trace_result
#print axioms decodeNaturalProgram_trace_cost
end NLA.Proofs.TR04
