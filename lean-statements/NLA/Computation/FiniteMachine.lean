import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Computability.StateTransition

/-! Ordinary binary computation for the reviewed computational-model specification.
The alphabet and control state are finite; the transition function is a finite
table, not a function on arbitrary mathematical inputs. No algorithm is assumed. -/
set_option autoImplicit false

namespace NLA.Computation

abbrev Word := List Bool
abbrev Symbol := Option Bool

/-- There are `stateBound + 1` states, with the canonical initial state zero.
The three tape symbols are blank, zero and one. -/
structure FiniteMachine where
  stateBound : ℕ
  table : Turing.TM0.Machine Symbol (Fin (stateBound + 1))

namespace FiniteMachine

abbrev Configuration (M : FiniteMachine) :=
  Turing.TM0.Cfg Symbol (Fin (M.stateBound + 1))

def step (M : FiniteMachine) : M.Configuration → Option M.Configuration :=
  Turing.TM0.step M.table

def initial (M : FiniteMachine) (w : Word) : M.Configuration :=
  Turing.TM0.init (w.map some)

/-- The complete suffix from the final head is the output word followed by
blanks. Nonblank bit symbols distinguish even trailing zero bits from blanks. -/
def HasOutput (M : FiniteMachine) (c : M.Configuration) (v : Word) : Prop :=
  c.Tape.right₀ = Turing.ListBlank.mk (v.map some)

/-- At most T actual move/write transitions reach an output configuration,
and that configuration must halt. Reaching an intermediate state is insufficient. -/
def RunsWithin (M : FiniteMachine) (w v : Word) (T : ℕ) : Prop :=
  ∃ c : M.Configuration,
    Nonempty (StateTransition.EvalsToInTime M.step (M.initial w) (some c) T) ∧
    M.step c = none ∧ M.HasOutput c v

/-- A decision output is exactly one bit, never an arbitrary truth predicate. -/
def DecidesWithin (M : FiniteMachine) (w : Word) (b : Bool) (T : ℕ) : Prop :=
  M.RunsWithin w [b] T

end FiniteMachine

/-- Uniform bounds are chosen once with the algorithm, before every input. -/
structure PolynomialBound where
  coefficient : ℕ
  exponent : ℕ
  coefficient_pos : 0 < coefficient

def PolynomialBound.atLength (p : PolynomialBound) (n : ℕ) : ℕ :=
  p.coefficient * (n + 1) ^ p.exponent

end NLA.Computation
