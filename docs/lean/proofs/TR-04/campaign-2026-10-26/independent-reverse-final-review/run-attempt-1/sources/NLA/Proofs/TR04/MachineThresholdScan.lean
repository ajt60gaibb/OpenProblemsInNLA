import NLA.Proofs.TR04.MachineThresholdScanCounts
import NLA.Proofs.TR04.MachineNoEarlyHalt
import Mathlib.Tactic.FinCases

/-! A literal read-only RAM scan. Threshold is real register zero; actual
natural registers five/six/seven return above/tied/retained-tied counts. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def thresholdScanProgram : Program where
  extraLabels := 22
  realRegisters := 2
  extraNatRegisters := 7
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .natural 0 0 1
    | 1 => .natural 5 0 2
    | 2 => .natural 6 0 3
    | 3 => .natural 7 0 4
    | 4 => .copyNat 4 3 5
    | 5 => .lessNat 0 1 6 22
    | 6 => .read 1 4 7
    | 7 => .lessReal 0 1 8 10
    | 8 => .increment 5 9
    | 9 => .jump 18
    | 10 => .equalReal 1 0 11 14
    | 11 => .increment 6 12
    | 12 => .lessNat 0 2 13 15
    | 13 => .increment 7 16
    | 14 => .jump 20
    | 15 => .jump 16
    | 16 => .increment 4 17
    | 17 => .increment 0 5
    | 18 => .jump 19
    | 19 => .jump 16
    | 20 => .jump 21
    | 21 => .jump 16
    | _ => .halt 3

instance thresholdScanProgram_nonzero_reals : NeZero thresholdScanProgram.realRegisters := ⟨by decide⟩

def thresholdScanLoopState (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau : ℝ) (k : ℕ) (scratch : ℝ) : State thresholdScanProgram where
  label := 5
  real := ![tau, scratch]
  natural := ![k, P.count, P.rank, P.base, P.base + k,
    thresholdAboveCount memory P tau k, thresholdTiedCount memory P tau k, thresholdTakeCount memory P tau k]
  memory := memory
  status := .running

def thresholdScanStart (memory : ℕ → ℝ) (P : ThresholdScanParameters) (tau scratch : ℝ)
    (aux : Fin 5 → ℕ) : State thresholdScanProgram where
  label := 0
  real := ![tau, scratch]
  natural := ![aux 0, P.count, P.rank, P.base, aux 1, aux 2, aux 3, aux 4]
  memory := memory
  status := .running

theorem thresholdScanProgram_scalar (s : State thresholdScanProgram) :
    instructionIsSVD (thresholdScanProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

set_option maxHeartbeats 1000000 in
theorem thresholdScanProgram_initialize (memory : ℕ → ℝ) (P : ThresholdScanParameters)
    (tau scratch : ℝ) (aux : Fin 5 → ℕ) :
    (ordinaryStep thresholdScanProgram)^[5] (thresholdScanStart memory P tau scratch aux) =
      thresholdScanLoopState memory P tau 0 scratch := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    thresholdScanProgram, thresholdScanStart, thresholdScanLoopState,
    thresholdAboveCount_zero, thresholdTiedCount_zero, thresholdTakeCount_zero]
  all_goals try rfl
  funext r
  fin_cases r <;> simp [Function.update, Fin.ext_iff]

#assert_trust kernel thresholdScanProgram
#assert_trust kernel thresholdScanProgram_scalar
#assert_trust kernel thresholdScanProgram_initialize
#print axioms thresholdScanProgram_initialize
end NLA.Proofs.TR04
