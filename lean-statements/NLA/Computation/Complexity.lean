import NLA.Computation.FiniteMachine
import NLA.Computation.BinaryEncoding

/-! Polynomial language classes defined using actual bounded finite-machine
execution and the single fixed binary pair encoder. These are definitions,
not proofs that any catalog problem is easy, hard or complete. -/
set_option autoImplicit false

namespace NLA.Computation.Complexity

abbrev Language := Set Word

/-- A total decision machine on all binary words. -/
def InP (L : Language) : Prop :=
  ∃ M : FiniteMachine, ∃ bound : PolynomialBound,
    ∀ w : Word, ∃ bit : Bool,
      M.DecidesWithin w bit (bound.atLength w.length) ∧ (bit = true ↔ w ∈ L)

/-- Certificates have uniformly polynomial length. The finite verifier also
halts within its one fixed polynomial bound on every pair, including witnesses
longer than the certificate bound. Its acceptance is an actual bounded run. -/
def InNP (L : Language) : Prop :=
  ∃ V : FiniteMachine, ∃ certificateBound timeBound : PolynomialBound,
    (∀ w certificate : Word, ∃ bit : Bool,
      V.DecidesWithin (BinaryEncoding.encodePair w certificate) bit
        (timeBound.atLength (BinaryEncoding.encodePair w certificate).length)) ∧
    ∀ w : Word,
      w ∈ L ↔ ∃ certificate : Word,
        certificate.length ≤ certificateBound.atLength w.length ∧
        V.DecidesWithin (BinaryEncoding.encodePair w certificate) true
          (timeBound.atLength (BinaryEncoding.encodePair w certificate).length)

def InCoNP (L : Language) : Prop := InNP Lᶜ

/-- The reduction output must be produced by the actual finite transducer.
There is no independently supplied map with an assumed operation count. -/
def PolynomialManyOneReduces (L K : Language) : Prop :=
  ∃ M : FiniteMachine, ∃ bound : PolynomialBound,
    ∀ w : Word, ∃ output : Word,
      M.RunsWithin w output (bound.atLength w.length) ∧ (w ∈ L ↔ output ∈ K)

/-- A promised many-one reduction must produce a legal target instance on
every source word. The target problem supplies concrete `legal` and `yes`. -/
def PolynomialPromiseManyOneReduces (L legal yes : Language) : Prop :=
  ∃ M : FiniteMachine, ∃ bound : PolynomialBound,
    ∀ w : Word, ∃ output : Word,
      M.RunsWithin w output (bound.atLength w.length) ∧
      output ∈ legal ∧ (w ∈ L ↔ output ∈ yes)

def ManyOneNPHard (K : Language) : Prop :=
  ∀ L : Language, InNP L → PolynomialManyOneReduces L K

end NLA.Computation.Complexity
