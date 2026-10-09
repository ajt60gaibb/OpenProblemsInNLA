import NLA.Computation.QueryTape
import NLA.Computation.Complexity

/-! The reviewed finite three-tape oracle model. Only the query instruction
can call the oracle, on the actual finite query-tape word. Failed and successful
terminal outcomes differ. Query logs are mathematical observations of execution,
never unbounded registers available to the program. -/
set_option autoImplicit false

namespace NLA.Computation

inductive OracleStatus
  | running
  | halted
  | failed
  deriving DecidableEq

/-- An ordinary block performs at most one move/write on each of three tapes.
All labels are fixed finite constructor data. -/
inductive OracleInstruction (stateBound : ℕ)
  | halt
  | work (next : Fin (stateBound + 1))
      (main work query : Option (Turing.TM0.Stmt Symbol))
  | query (yes no : Fin (stateBound + 1))

structure OracleMachine where
  stateBound : ℕ
  table : Fin (stateBound + 1) → Symbol → Symbol → Symbol →
    OracleInstruction stateBound

namespace OracleMachine

structure Configuration (M : OracleMachine) where
  state : Fin (M.stateBound + 1)
  main : Turing.Tape Symbol
  work : Turing.Tape Symbol
  query : Turing.Tape Symbol
  status : OracleStatus

def initial (M : OracleMachine) (w : Word) : M.Configuration :=
  ⟨0, Turing.Tape.mk₁ (w.map some), Turing.Tape.mk₁ [],
    Turing.Tape.mk₁ [], .running⟩

def applyAction (action : Option (Turing.TM0.Stmt Symbol))
    (tape : Turing.Tape Symbol) : Turing.Tape Symbol :=
  match action with
  | none => tape
  | some (.move direction) => tape.move direction
  | some (.write symbol) => tape.write symbol

/-- One counted transition. Query construction is restricted to work actions;
the actual query step leaves every tape unchanged and returns only one bit of
control information. Malformed tape words lead to the distinct failed tag. -/
def step (M : OracleMachine) (oracle : Word → Bool)
    (c : M.Configuration) : M.Configuration :=
  match c.status with
  | .halted => c
  | .failed => c
  | .running =>
      match M.table c.state c.main.head c.work.head c.query.head with
      | .halt => { c with status := .halted }
      | .work next main work query =>
          ⟨next, applyAction main c.main, applyAction work c.work,
            applyAction query c.query, .running⟩
      | .query yes no =>
          match QueryTape.read c.query with
          | none => { c with status := .failed }
          | some word => { c with state := if oracle word then yes else no }

def run (M : OracleMachine) (oracle : Word → Bool) (w : Word) : ℕ → M.Configuration
  | 0 => M.initial w
  | t + 1 => M.step oracle (M.run oracle w t)

/-- A query is observed only when an actual running query instruction has a
well-formed tape word. A halt, work step or malformed query produces no call. -/
def queryWord (M : OracleMachine) (c : M.Configuration) : Option Word :=
  match c.status with
  | .halted => none
  | .failed => none
  | .running =>
      match M.table c.state c.main.head c.work.head c.query.head with
      | .query _ _ => QueryTape.read c.query
      | _ => none

structure QueryEvent (M : OracleMachine) where
  time : ℕ
  before : M.Configuration
  word : Word

/-- The exact chronological query log from the first t transitions, including
the pre-query configuration. It is derived from execution, never guessed. -/
def queryTrace (M : OracleMachine) (oracle : Word → Bool) (w : Word)
    (t : ℕ) : List M.QueryEvent :=
  (List.range t).filterMap fun i =>
    let c := M.run oracle w i
    (M.queryWord c).map fun word => ⟨i, c, word⟩

def HasOutput (M : OracleMachine) (c : M.Configuration) (output : Word) : Prop :=
  c.main.right₀ = Turing.ListBlank.mk (output.map some)

/-- Success, output, runtime and legality all belong to the same actual run.
Every recorded query is checked, including adaptive queries after earlier answers.
The successful halt instruction itself costs one transition. -/
def RunsWithin (M : OracleMachine) (oracle : Word → Bool) (legal : Set Word)
    (input output : Word) (bound : ℕ) : Prop :=
  ∃ t : ℕ, t ≤ bound ∧
    (M.run oracle input t).status = .halted ∧
    M.HasOutput (M.run oracle input t) output ∧
    ∀ event ∈ M.queryTrace oracle input t, event.word ∈ legal

/-- Correctness is required on every legal instance. Off-promise answers are
unrestricted; a reduction is separately required never to ask such queries. -/
def Compatible (legal yes : Set Word) (oracle : Word → Bool) : Prop :=
  ∀ word : Word, word ∈ legal → (oracle word = true ↔ word ∈ yes)

end OracleMachine

namespace Complexity

/-- The same machine and bound work for every compatible promised oracle and
every source word. There is no oracle-specific or input-specific runtime constant. -/
def PolynomialOracleReduces (L legal yes : Language) : Prop :=
  ∃ M : OracleMachine, ∃ bound : PolynomialBound,
    ∀ oracle : Word → Bool, OracleMachine.Compatible legal yes oracle →
      ∀ word : Word, ∃ bit : Bool,
        M.RunsWithin oracle legal word [bit] (bound.atLength word.length) ∧
        (bit = true ↔ word ∈ L)

def OracleNPHard (legal yes : Language) : Prop :=
  ∀ L : Language, InNP L → PolynomialOracleReduces L legal yes

end Complexity

end NLA.Computation
