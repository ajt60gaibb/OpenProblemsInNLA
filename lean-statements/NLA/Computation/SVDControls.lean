import NLA.Statements.TR04
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Kernel controls for actual SVD data, bulk writes, charged transitions and
mixed-radix tensor placement. These do not implement the TR-04 solver. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.Computation.SVDMachine.Controls

/-- Exact reconstruction and full bases, not a named spectral-law assumption. -/
theorem scalar_svd :
    ValidSVD (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ _ => 1) (fun _ => 2) (fun _ _ => 1) := by
  norm_num [ValidSVD]

theorem negative_sigma_rejected :
    ¬ ValidSVD (fun _ _ : Fin 1 => (2 : ℝ)) (fun _ _ => 1) (fun _ => -2) (fun _ _ => -1) := by
  norm_num [ValidSVD]

private abbrev identity2 : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 1 else 0
private abbrev swap2 : Matrix (Fin 2) (Fin 2) ℝ := fun i j => if i = j then 0 else 1

/-- Tied singular values admit different full bases in the same relation. -/
theorem tied_bases :
    ValidSVD identity2 identity2 (fun _ => 1) identity2 ∧
    ValidSVD identity2 swap2 (fun _ => 1) swap2 := by
  constructor
  · norm_num [ValidSVD, identity2, Fin.forall_fin_two, Fin.sum_univ_two]
  · have orthogonal : ∀ i j : Fin 2,
        (∑ a : Fin 2, swap2 a i * swap2 a j) = if i = j then 1 else 0 := by
      intro i j
      rw [Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> norm_num [swap2]
    refine ⟨orthogonal, orthogonal, ?_, ?_, ?_⟩
    · intro k
      norm_num
    · intro i j hij
      exact le_rfl
    · intro i j
      change identity2 i j = ∑ k : Fin 2, swap2 i k * (1 : ℝ) * swap2 j k
      rw [Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;> norm_num [identity2, swap2]

/-- Empty blocks never spuriously overlap; genuine overlap is rejected. -/
theorem block_guards :
    OutputBlocksDisjoint 1 1 3 4 5 ∧
    ¬ OutputBlocksDisjoint 1 1 3 3 5 ∧
    OutputBlocksDisjoint 0 0 7 7 7 ∧
    DisjointBlocks 5 0 0 10 := by
  norm_num [OutputBlocksDisjoint, DisjointBlocks]

/-- All three old-store output blocks are materialized and other cells survive. -/
theorem bulk_write :
    let memory := writeSVD (fun _ => (17 : ℝ)) 3 4 5
      (fun _ _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) (fun _ _ : Fin 1 => (1 : ℝ))
    memory 2 = 17 ∧ memory 3 = 1 ∧ memory 4 = 2 ∧ memory 5 = 1 ∧ memory 6 = 17 := by
  norm_num [writeSVD, matrixCell]

private abbrev svdProgram : Program where
  extraLabels := 1
  realRegisters := 0
  extraNatRegisters := 5
  constantCount := 0
  constants := Fin.elim0
  code := fun label => if label = 0 then .svd 0 1 2 3 4 5 1 else .halt 3

private abbrev svdStart : State svdProgram :=
  { initial svdProgram 1 (fun address => if address = 0 then 2 else 17) with
    natural := ![1, 1, 0, 3, 4, 5] }

private abbrev svdEnd : State svdProgram :=
  { svdStart with
    label := 1
    memory := writeSVD svdStart.memory 3 4 5
      (fun _ _ : Fin 1 => 1) (fun _ : Fin 1 => 2) (fun _ _ : Fin 1 => 1) }

/-- Actual legal SVD transition pays the fixed cubic cost 27. -/
theorem charged_svd : Step svdProgram svdStart svdEnd 27 := by
  classical
  refine ⟨by norm_num [charge, svdStart, initial, svdProgram], ?_⟩
  change if OutputBlocksDisjoint 1 1 3 4 5 then _ else _
  rw [if_pos block_guards.1]
  refine ⟨(fun _ _ : Fin 1 => 1), (fun _ => 2), (fun _ _ => 1), ?_, rfl⟩
  change ValidSVD (readMatrix (fun address => if address = 0 then 2 else 17) 1 1 0) _ _ _
  have h : readMatrix (fun address => if address = 0 then 2 else 17) 1 1 0 = (fun _ _ => (2 : ℝ)) := by
    funext i j
    fin_cases i
    fin_cases j
    rfl
  rw [h]
  exact scalar_svd

/-- A guard failure cannot produce a successful pointer. -/
theorem overlap_fails :
    let s : State svdProgram := { svdStart with natural := ![1, 1, 0, 3, 3, 5] }
    Step svdProgram s { s with status := .failed } 27 := by
  classical
  norm_num [Step, charge, svdStart, initial, svdProgram, OutputBlocksDisjoint, DisjointBlocks]
  dsimp
  norm_num

/-- A successful halt is charged separately after the SVD instruction. -/
theorem halt_charged :
    Step svdProgram svdEnd { svdEnd with status := .halted 3 } 1 := by
  classical
  norm_num [Step, charge, ordinaryStep, svdEnd, svdStart, initial, svdProgram]
  rfl

theorem terminal_zero_cost (P : Program) (s : State P) (h : s.status = .failed) :
    Step P s s 0 := by
  classical
  simp [Step, charge, h]

open NLA.Computation.TensorTrainApproximation

private abbrev shape232 : Shape where
  order := 3
  order_ge := by decide
  mode := ![2, 3, 2]
  mode_ge := by intro i; fin_cases i <;> decide

private abbrev tensor232 (a : Index shape232) : ℝ :=
  100 * (a 0).val + 10 * (a 1).val + (a 2).val

/-- All headers and the twelve entries use the declared last-index-fastest order. -/
theorem tensor_layout :
    InputMemory shape232 (fun _ => 1) tensor232 0 = 2 ∧
    InputMemory shape232 (fun _ => 1) tensor232 1 = 3 ∧
    InputMemory shape232 (fun _ => 1) tensor232 2 = 2 ∧
    InputMemory shape232 (fun _ => 1) tensor232 3 = 1 ∧
    InputMemory shape232 (fun _ => 1) tensor232 4 = 1 ∧
    InputMemory shape232 (fun _ => 1) tensor232 5 = 0 ∧
    InputMemory shape232 (fun _ => 1) tensor232 6 = 1 ∧
    InputMemory shape232 (fun _ => 1) tensor232 7 = 10 ∧
    InputMemory shape232 (fun _ => 1) tensor232 10 = 21 ∧
    InputMemory shape232 (fun _ => 1) tensor232 11 = 100 ∧
    InputMemory shape232 (fun _ => 1) tensor232 16 = 121 ∧
    InputMemory shape232 (fun _ => 1) tensor232 17 = 0 := by
  repeat' constructor
  all_goals norm_num [InputMemory, shape232, DenseSize, Decode, SuffixSize, tensor232,
    Fin.prod_univ_succ, Finset.prod_filter]
  all_goals dsimp
  all_goals norm_num

#assert_trust kernel scalar_svd
#assert_trust kernel negative_sigma_rejected
#assert_trust kernel tied_bases
#assert_trust kernel block_guards
#assert_trust kernel bulk_write
#assert_trust kernel charged_svd
#assert_trust kernel overlap_fails
#assert_trust kernel halt_charged
#assert_trust kernel terminal_zero_cost
#assert_trust kernel tensor_layout

end NLA.Computation.SVDMachine.Controls
