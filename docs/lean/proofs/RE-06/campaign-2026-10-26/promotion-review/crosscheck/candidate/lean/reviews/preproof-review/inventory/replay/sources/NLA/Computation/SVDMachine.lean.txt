import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega

/-! Concrete finite exact-real arithmetic RAM with an explicit full-SVD relation.
This separate model does not change the reviewed random IE-12 machine. SVD
responses are arbitrary valid full decompositions, and every response is legal.
No solver, arbitrary evaluator or free cost function is included. -/
set_option autoImplicit false
open scoped BigOperators

namespace NLA.Computation.SVDMachine

/-- Every register, literal and successor is a finite piece of program syntax.
Natural literals are fixed with the program. There is no real-to-natural operation. -/
inductive Instruction (labels reals naturals constants : ℕ) where
  | constant (dst : Fin reals) (value : Fin constants) (next : Fin labels)
  | copyReal (dst src : Fin reals) (next : Fin labels)
  | addReal (dst left right : Fin reals) (next : Fin labels)
  | subReal (dst left right : Fin reals) (next : Fin labels)
  | mulReal (dst left right : Fin reals) (next : Fin labels)
  | divReal (dst left right : Fin reals) (next : Fin labels)
  | sqrtReal (dst src : Fin reals) (next : Fin labels)
  | lessReal (left right : Fin reals) (yes no : Fin labels)
  | equalReal (left right : Fin reals) (yes no : Fin labels)
  | natural (dst : Fin naturals) (value : ℕ) (next : Fin labels)
  | copyNat (dst src : Fin naturals) (next : Fin labels)
  | increment (dst : Fin naturals) (next : Fin labels)
  | decrement (dst : Fin naturals) (next : Fin labels)
  | addNat (dst left right : Fin naturals) (next : Fin labels)
  | mulNat (dst left right : Fin naturals) (next : Fin labels)
  | lessNat (left right : Fin naturals) (yes no : Fin labels)
  | equalNat (left right : Fin naturals) (yes no : Fin labels)
  | castNat (dst : Fin reals) (src : Fin naturals) (next : Fin labels)
  | read (dst : Fin reals) (address : Fin naturals) (next : Fin labels)
  | write (address : Fin naturals) (src : Fin reals) (next : Fin labels)
  | svd (rows cols inputBase uBase sigmaBase vBase : Fin naturals) (next : Fin labels)
  | jump (next : Fin labels)
  | halt (address : Fin naturals)

/-- `extraLabels+1` and `extraNatRegisters+1` ensure the initial label and
input-size register exist. The constant pool and scratch-register count may be zero. -/
structure Program where
  extraLabels : ℕ
  realRegisters : ℕ
  extraNatRegisters : ℕ
  constantCount : ℕ
  constants : Fin constantCount → ℝ
  code : Fin (extraLabels + 1) →
    Instruction (extraLabels + 1) realRegisters (extraNatRegisters + 1) constantCount

/-- A successful halt records an ordinary memory address, not an output oracle. -/
inductive Status where
  | running
  | halted (address : ℕ)
  | failed
  deriving DecidableEq

structure State (P : Program) where
  label : Fin (P.extraLabels + 1)
  real : Fin P.realRegisters → ℝ
  natural : Fin (P.extraNatRegisters + 1) → ℕ
  memory : ℕ → ℝ
  status : Status

/-- Only concrete input size and preplaced memory enter initialization. -/
def initial (P : Program) (inputSize : ℕ) (memory : ℕ → ℝ) : State P where
  label := 0
  real := fun _ => 0
  natural := fun r => if r = 0 then inputSize else 0
  memory := memory
  status := .running

/-- Deterministic scalar operations, reading all operands from the old state.
The SVD placeholder is never used by Step, which supplies its full relation. -/
noncomputable def ordinaryStep (P : Program) (s : State P) : State P := by
  classical
  exact match s.status with
  | .halted _ => s
  | .failed => s
  | .running => match P.code s.label with
    | .constant dst value next =>
        { s with label := next, real := Function.update s.real dst (P.constants value) }
    | .copyReal dst src next =>
        { s with label := next, real := Function.update s.real dst (s.real src) }
    | .addReal dst left right next =>
        { s with label := next, real := Function.update s.real dst (s.real left + s.real right) }
    | .subReal dst left right next =>
        { s with label := next, real := Function.update s.real dst (s.real left - s.real right) }
    | .mulReal dst left right next =>
        { s with label := next, real := Function.update s.real dst (s.real left * s.real right) }
    | .divReal dst left right next =>
        if s.real right = 0 then { s with status := .failed }
        else { s with label := next, real := Function.update s.real dst (s.real left / s.real right) }
    | .sqrtReal dst src next =>
        if s.real src < 0 then { s with status := .failed }
        else { s with label := next, real := Function.update s.real dst (Real.sqrt (s.real src)) }
    | .lessReal left right yes no =>
        { s with label := if s.real left < s.real right then yes else no }
    | .equalReal left right yes no =>
        { s with label := if s.real left = s.real right then yes else no }
    | .natural dst value next =>
        { s with label := next, natural := Function.update s.natural dst value }
    | .copyNat dst src next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural src) }
    | .increment dst next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural dst + 1) }
    | .decrement dst next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural dst - 1) }
    | .addNat dst left right next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural left + s.natural right) }
    | .mulNat dst left right next =>
        { s with label := next, natural := Function.update s.natural dst (s.natural left * s.natural right) }
    | .lessNat left right yes no =>
        { s with label := if s.natural left < s.natural right then yes else no }
    | .equalNat left right yes no =>
        { s with label := if s.natural left = s.natural right then yes else no }
    | .castNat dst src next =>
        { s with label := next, real := Function.update s.real dst (s.natural src : ℝ) }
    | .read dst address next =>
        { s with label := next, real := Function.update s.real dst (s.memory (s.natural address)) }
    | .write address src next =>
        { s with label := next, memory := Function.update s.memory (s.natural address) (s.real src) }
    | .svd _ _ _ _ _ _ _ => { s with status := .failed }
    | .jump next => { s with label := next }
    | .halt address => { s with status := .halted (s.natural address) }

/-- All full orthogonal bases, all nonnegative singular values in descending
order, and literal rectangular reconstruction, including empty dimensions. -/
def ValidSVD {m l : ℕ} (B : Matrix (Fin m) (Fin l) ℝ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) : Prop :=
  (∀ i j, (∑ a, U a i * U a j) = if i = j then 1 else 0) ∧
  (∀ i j, (∑ a, V a i * V a j) = if i = j then 1 else 0) ∧
  (∀ k, 0 ≤ sigma k) ∧
  (∀ i j, i ≤ j → sigma j ≤ sigma i) ∧
  ∀ i j, B i j = ∑ k : Fin (min m l),
    U i ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left m l)⟩ * sigma k *
      V j ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right m l)⟩

/-- Exact disjointness of finite half-open address blocks, including empty ones. -/
def DisjointBlocks (a countA b countB : ℕ) : Prop :=
  countA = 0 ∨ countB = 0 ∨ a + countA ≤ b ∨ b + countB ≤ a

def OutputBlocksDisjoint (m l uBase sigmaBase vBase : ℕ) : Prop :=
  DisjointBlocks uBase (m * m) sigmaBase (min m l) ∧
  DisjointBlocks uBase (m * m) vBase (l * l) ∧
  DisjointBlocks sigmaBase (min m l) vBase (l * l)

/-- Row-major finite matrix lookup; only initialization/output materialization
uses quotient and remainder, not a real-to-natural instruction. -/
def matrixCell {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) (offset : ℕ) : ℝ :=
  if h : offset < m * l then
    have hl : 0 < l := by
      by_contra hz
      have : l = 0 := by omega
      simp_all
    A ⟨offset / l, (Nat.div_lt_iff_lt_mul hl).mpr h⟩
      ⟨offset % l, Nat.mod_lt offset hl⟩
  else 0

/-- The entire old input matrix is read before any output store updates. -/
def readMatrix (memory : ℕ → ℝ) (m l base : ℕ) : Matrix (Fin m) (Fin l) ℝ :=
  fun i j => memory (base + i.val * l + j.val)

/-- All U, sigma and V cells are written, preserving every other old cell. -/
def writeSVD {m l : ℕ} (memory : ℕ → ℝ) (uBase sigmaBase vBase : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) (sigma : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (address : ℕ) : ℝ :=
  if uBase ≤ address ∧ address < uBase + m * m then
    matrixCell U (address - uBase)
  else if hs : sigmaBase ≤ address ∧ address < sigmaBase + min m l then
    sigma ⟨address - sigmaBase, by omega⟩
  else if vBase ≤ address ∧ address < vBase + l * l then
    matrixCell V (address - vBase)
  else memory address

/-- A concrete fixed charge for the current instruction, positive while running. -/
def charge (P : Program) (s : State P) : ℕ :=
  match s.status with
  | .halted _ => 0
  | .failed => 0
  | .running => match P.code s.label with
    | .svd rows cols _ _ _ _ _ => (s.natural rows + s.natural cols + 1)^3
    | _ => 1

/-- Actual structural transition relation. SVD replies range over every tuple
satisfying ValidSVD; no selected basis, assumed solver or choice oracle appears. -/
def Step (P : Program) (s t : State P) (cost : ℕ) : Prop := by
  classical
  exact cost = charge P s ∧
  match s.status with
  | .halted _ => t = s
  | .failed => t = s
  | .running => match P.code s.label with
    | .svd rows cols inputBase uBase sigmaBase vBase next =>
      let m := s.natural rows
      let l := s.natural cols
      if OutputBlocksDisjoint m l (s.natural uBase) (s.natural sigmaBase) (s.natural vBase)
      then ∃ U : Matrix (Fin m) (Fin m) ℝ, ∃ sigma : Fin (min m l) → ℝ,
        ∃ V : Matrix (Fin l) (Fin l) ℝ,
          ValidSVD (readMatrix s.memory m l (s.natural inputBase)) U sigma V ∧
          t = { s with
            label := next
            memory := writeSVD s.memory (s.natural uBase) (s.natural sigmaBase)
              (s.natural vBase) U sigma V }
      else t = { s with status := .failed }
    | _ => t = ordinaryStep P s

/-- Trace costs must satisfy Step; they are not caller-supplied runtime bounds. -/
structure Trace (P : Program) where
  state : ℕ → State P
  cost : ℕ → ℕ

def LegalTrace (P : Program) (start : State P) (trace : Trace P) : Prop :=
  trace.state 0 = start ∧ ∀ t, Step P (trace.state t) (trace.state (t + 1)) (trace.cost t)

def CostThrough (P : Program) (trace : Trace P) (t : ℕ) : ℕ :=
  ∑ s ∈ Finset.range t, trace.cost s

end NLA.Computation.SVDMachine
