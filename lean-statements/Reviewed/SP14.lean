/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Support
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! SP-14: the complete original Widom canonical-distribution conjecture
and its negative resolution. The original source and exact numerical contract
are retained under docs/lean/statements/SP-14/. This defines a proposition;
it does not prove the counterexample. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open MeasureTheory Filter intervalIntegral

namespace NLA.ReviewedStatements.SP14

/-- The original Fourier coefficient `aₖ=(1/(2π))∫₀²π a(eⁱᵗ)e⁻ⁱᵏᵗ dt`,
for every integer frequency, with the genuine real interval integral. -/
noncomputable def FourierCoefficient (a : Circle → ℂ) (k : ℤ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi),
      a (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))

/-- The actual `n × n` Toeplitz section, with row-minus-column indexing. -/
noncomputable def Toeplitz (a : Circle → ℂ) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => FourierCoefficient a ((i.val : ℤ) - (j.val : ℤ))

/-- A holomorphic extension from an inner annulus, continuous to the unit
circle from that side and agreeing there with the given symbol. -/
def InnerExtension (a : Circle → ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} ∧
      ContinuousOn f {z : ℂ | r < ‖z‖ ∧ ‖z‖ ≤ 1} ∧
      ∀ z : Circle, f (z : ℂ) = a z

/-- The corresponding outer annular extension. No behavior is imposed at
the unrelated outer radius. -/
def OuterExtension (a : Circle → ℂ) : Prop :=
  ∃ R : ℝ, 1 < R ∧
    ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < R} ∧
      ContinuousOn f {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ < R} ∧
      ∀ z : Circle, f (z : ℂ) = a z

/-- The full characteristic-root multiset retains algebraic multiplicity,
including for nonnormal and nondiagonalizable Toeplitz matrices. -/
noncomputable def Empirical (a : Circle → ℂ) (F : ℂ → ℂ) (n : ℕ) : ℂ :=
  (1 / (n : ℂ)) * ((Toeplitz a n).charpoly.roots.map F).sum

/-- Normalized real-circle average, with complex-valued test and integral. -/
noncomputable def Canonical (a : Circle → ℂ) (F : ℂ → ℂ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), F (a (Circle.exp t))

/-- Every continuous symbol with neither one-sided annular extension has
the full-sequence canonical eigenvalue distribution for every continuous
compactly supported complex test. This is Widom's complete original claim. -/
def OriginalConjecture : Prop :=
  ∀ a : Circle → ℂ, Continuous a →
    ¬ InnerExtension a → ¬ OuterExtension a →
      ∀ F : ℂ → ℂ, Continuous F → HasCompactSupport F →
        Tendsto (fun n : ℕ => Empirical a F n) atTop (nhds (Canonical a F))

/-- The recorded Solved answer is negative: the entire original universal
claim is false, with no restriction to a test subclass or symbol subclass. -/
def Target : Prop := ¬ OriginalConjecture

#assert_statement OriginalConjecture
#assert_statement Target
#assert_trust kernel OriginalConjecture
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.SP14
