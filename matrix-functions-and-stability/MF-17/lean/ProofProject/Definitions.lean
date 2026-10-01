import Mathlib

/-!
# MF-17 statement definitions

A generator is represented by its complete strong right-derivative graph. This
includes unbounded generators; `IsGeneratorInverse` asserts both inverse
identities on the actual generator domain.
-/

noncomputable section

namespace ProofProject

universe u

/-- A strongly continuous semigroup with the normalized exponential bound.
Only nonnegative times are used; values at negative times are immaterial. -/
structure StableSemigroup (M : ℝ) (H : Type u) [NormedAddCommGroup H]
    [NormedSpace ℂ H] where
  op : ℝ → H →L[ℂ] H
  at_zero : op 0 = ContinuousLinearMap.id ℂ H
  add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → op (s + t) = (op s).comp (op t)
  strong_continuous : ∀ x : H, ContinuousOn (fun s : ℝ => op s x) (Set.Ici 0)
  bound : ∀ s : ℝ, 0 ≤ s → ‖op s‖ ≤ M * Real.exp (-s)

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The graph of the (possibly unbounded) infinitesimal generator. -/
def GeneratorGraph (T : StableSemigroup M H) (x y : H) : Prop :=
  HasDerivWithinAt (fun s : ℝ => T.op s x) y (Set.Ici 0) 0

/-- `B` is the everywhere-defined bounded inverse of the full generator. -/
def IsGeneratorInverse (T : StableSemigroup M H) (B : H →L[ℂ] H) : Prop :=
  ∀ x y : H, GeneratorGraph T x y ↔ B y = x

/-- The norm-convergent exponential of the bounded inverse. -/
def inverseEvolution (B : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((t : ℂ) • B)

/-- The slowly varying rate in the supplied proof. -/
def growthLog (t : ℝ) : ℝ := Real.log (Real.log (t + Real.exp (Real.exp 1)))

/-- The claimed sharp exponent. -/
def growthExponent (M : ℝ) : ℝ := (2 / Real.pi) * Real.arccos (1 / M)

/-- Values attained across all complex Hilbert spaces in an arbitrary universe. -/
def attainableNorms (M t : ℝ) : Set ℝ :=
  {r | ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (T : StableSemigroup M H) (B : H →L[ℂ] H),
    IsGeneratorInverse T B ∧ r = ‖inverseEvolution B t‖}

/-- The envelope in the source. Boundedness of its defining set is a proof
obligation, so no conclusion may use `csSup` without discharging it. -/
def growthEnvelope (M t : ℝ) : ℝ := sSup (attainableNorms.{u} M t)

/-- Finite-dimensional witnesses, retaining the full semigroup bound M. -/
def HasFiniteWitness (M t lower : ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : FiniteDimensional ℂ H)
    (T : StableSemigroup M H) (B : H →L[ℂ] H),
    IsGeneratorInverse T B ∧ lower ≤ ‖inverseEvolution B t‖

end ProofProject
