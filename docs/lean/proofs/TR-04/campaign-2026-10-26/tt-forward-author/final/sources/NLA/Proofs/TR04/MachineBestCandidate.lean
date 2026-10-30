import NLA.Proofs.TR04.MachineBestCandidateMemory
import NLA.Proofs.TR04.MachineRelocationOrdinary

/-! A fixed read-only RAM selector. It computes every actual squared error,
initializes at the first candidate, and replaces the winner only on strict
lessReal. Explicit padding keeps every iteration at the same literal length. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

/-- Natural registers: K,N,A,store,j,winner,winnerBase,currentBase, then the
five injected squared-error registers. Real3 retains the winning error. -/
def bestCandidateProgram : Program where
  extraLabels := 29
  realRegisters := 4
  extraNatRegisters := 12
  constantCount := 0
  constants := Fin.elim0
  code label := match label.val with
    | 0 => .natural 4 0 1
    | 1 => .copyNat 7 3 2
    | 2 => .lessNat 4 0 3 25
    | 3 => .natural 8 0 4
    | 4 => .copyNat 9 1 5
    | 5 => .copyNat 10 2 6
    | 6 => .copyNat 11 7 7
    | 7 => .natural 12 0 8
    | 8 => .subReal 0 0 0 9
    | 9 => .lessNat 8 9 10 18
    | 10 => .read 1 10 11
    | 11 => .read 2 11 12
    | 12 => .subReal 1 1 2 13
    | 13 => .mulReal 1 1 1 14
    | 14 => .addReal 0 0 1 15
    | 15 => .increment 10 16
    | 16 => .increment 11 17
    | 17 => .increment 8 9
    | 18 => .equalNat 4 12 26 19
    | 19 => .lessReal 0 3 20 27
    | 20 => .copyReal 3 0 21
    | 21 => .copyNat 5 4 22
    | 22 => .copyNat 6 7 23
    | 23 => .increment 4 24
    | 24 => .addNat 7 7 1 2
    | 25 => .halt 6
    | 26 => .jump 20
    | 27 => .jump 28
    | 28 => .jump 29
    | _ => .jump 23

instance bestCandidateProgram_nonzero_realRegisters : NeZero bestCandidateProgram.realRegisters :=
  ⟨by decide⟩

def bestCandidateErrorLabels (i : Fin 11) : Fin 30 := ⟨8 + i.val, by omega⟩
def bestCandidateErrorNaturals (i : Fin 5) : Fin 13 := ⟨8 + i.val, by omega⟩
def bestCandidateErrorReals (i : Fin 3) : Fin 4 := ⟨i.val, by omega⟩

def bestCandidateErrorEmbedding : RoutineEmbedding squaredErrorProgram bestCandidateProgram where
  labels := bestCandidateErrorLabels
  reals := bestCandidateErrorReals
  naturals := bestCandidateErrorNaturals
  constants := Fin.elim0
  reals_injective := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 4 => x.val) h
  naturals_injective := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [bestCandidateErrorNaturals] at hv
    omega
  constant_values := by intro i; exact Fin.elim0 i
  code := by intro l hl; fin_cases l <;> first | rfl | cases hl

structure BestCandidateScratch where
  index : ℕ
  count : ℕ
  ptrA : ℕ
  ptrB : ℕ
  haltAddress : ℕ
  real : Fin 3 → ℝ

def bestCandidateState (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (scratch : BestCandidateScratch) (label : Fin 30) : State bestCandidateProgram where
  label := label
  real := ![scratch.real 0, scratch.real 1, scratch.real 2, value]
  natural r := if h : r.val < 8 then
    ![p.count, p.entries, p.baseA, p.store, j, winner, p.candidateBase winner,
      p.candidateBase j] ⟨r.val, h⟩
    else ![scratch.index, scratch.count, scratch.ptrA, scratch.ptrB, scratch.haltAddress]
      ⟨r.val - 8, by have hr : r.val < 13 := r.isLt; omega⟩
  memory := p.memory
  status := .running

def bestCandidateLoopState (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (scratch : BestCandidateScratch) : State bestCandidateProgram :=
  bestCandidateState p j winner value scratch 2

def bestCandidateErrorState (p : BestCandidateData) (j winner : ℕ) (value : ℝ)
    (reals : Fin 3 → ℝ) : State bestCandidateProgram :=
  bestCandidateState p j winner value
    ⟨0, p.entries, p.baseA, p.candidateBase j, 0, reals⟩ 8

def bestCandidateAfterError (p : BestCandidateData) (j winner : ℕ) (value a b : ℝ) :
    State bestCandidateProgram :=
  bestCandidateState p j winner value
    ⟨p.entries, p.entries, p.baseA + p.entries, p.candidateBase j + p.entries, 0,
      ![p.candidateError j, a, b]⟩ 18

theorem bestCandidateProgram_scalar (s : State bestCandidateProgram) :
    instructionIsSVD (bestCandidateProgram.code s.label) = false := by
  rcases s with ⟨label, reals, naturals, memory, status⟩
  fin_cases label <;> rfl

theorem bestCandidateProgram_setup (p : BestCandidateData) (j winner : ℕ)
    (value : ℝ) (scratch : BestCandidateScratch) (hj : j < p.count) :
    (ordinaryStep bestCandidateProgram)^[6] (bestCandidateLoopState p j winner value scratch) =
      bestCandidateErrorState p j winner value scratch.real := by
  apply machineState_ext
  all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
    -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
    bestCandidateProgram, bestCandidateLoopState, bestCandidateErrorState, bestCandidateState, hj]
  · funext r
    fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

theorem bestCandidate_error_relates (p : BestCandidateData) (j winner : ℕ)
    (value : ℝ) (reals : Fin 3 → ℝ) :
    bestCandidateErrorEmbedding.Relates
      (squaredErrorStart p.memory p.baseA (p.candidateBase j) p.entries
        (reals 0) (reals 1) (reals 2)) (bestCandidateErrorState p j winner value reals) := by
  constructor
  · rfl
  · funext r
    fin_cases r <;> rfl
  · funext r
    fin_cases r <;> rfl
  · rfl
  · rfl

#assert_trust kernel bestCandidateErrorEmbedding
#assert_trust kernel bestCandidateProgram_setup
#assert_trust kernel bestCandidate_error_relates
#print axioms bestCandidateErrorEmbedding
end NLA.Proofs.TR04
