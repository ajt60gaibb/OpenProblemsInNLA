import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! IE-26: both complete perturbed-grid Fourier interpolation bounds.
The approved specification is docs/lean/statements/IE-26/NUMERICAL_TARGETS.md.
The constants have different quantifier scopes; neither bound is proved here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Statements.IE26

abbrev Width (N : ℕ) : ℕ := 2 * N + 1

/-- Cast before subtraction so the frequencies run from -N through N. -/
def Frequency (N : ℕ) (j : Fin (Width N)) : ℝ :=
  (j.val : ℝ) - (N : ℝ)

noncomputable def Spacing (N : ℕ) : ℝ :=
  2 * Real.pi / (Width N : ℝ)

def Admissible {N : ℕ} (α : ℝ) (s : Fin (Width N) → ℝ) : Prop :=
  ∀ k, |s k| ≤ α

noncomputable def Node (N : ℕ) (s : Fin (Width N) → ℝ)
    (k : Fin (Width N)) : ℝ :=
  (Frequency N k + s k) * Spacing N

/-- Node rows and frequency columns, without the Fourier normalization. -/
noncomputable def EvaluationMatrix (N : ℕ) (s : Fin (Width N) → ℝ) :
    Matrix (Fin (Width N)) (Fin (Width N)) ℂ :=
  fun k j => Complex.exp (Complex.I * ((Frequency N j * Node N s k : ℝ) : ℂ))

/-- The actual square Fourier matrix has normalization 1/sqrt(2N+1). -/
noncomputable def FourierMatrix (N : ℕ) (s : Fin (Width N) → ℝ) :
    Matrix (Fin (Width N)) (Fin (Width N)) ℂ :=
  fun k j => (((1 : ℝ) / Real.sqrt (Width N : ℝ) : ℝ) : ℂ) *
    EvaluationMatrix N s k j

/-- Interpolation uses the unnormalized evaluation matrix inverse. -/
noncomputable def Interpolant (N : ℕ) (s : Fin (Width N) → ℝ)
    (y : Fin (Width N) → ℂ) (x : ℝ) : ℂ :=
  ∑ j, ((EvaluationMatrix N s)⁻¹).mulVec y j *
    Complex.exp (Complex.I * ((Frequency N j * x : ℝ) : ℂ))

/-- The full complex data polydisk and full real interval jointly define the
interpolation infinity norm. On the target domain this is a finite maximum. -/
noncomputable def LebesgueConstant (N : ℕ) (s : Fin (Width N) → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ y : Fin (Width N) → ℂ,
    (∀ k, ‖y k‖ ≤ 1) ∧ ∃ x : ℝ,
      -Real.pi ≤ x ∧ x ≤ Real.pi ∧ r = ‖Interpolant N s y x‖}

/-- Genuine complex Euclidean operator norm of the normalized inverse. -/
noncomputable def InverseNorm (N : ℕ) (s : Fin (Width N) → ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((FourierMatrix N s)⁻¹))‖

/-- One absolute constant works for every alpha, every N and every shift. -/
def FirstBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ α : ℝ, 0 < α → α < (1 : ℝ) / 2 →
      ∀ s : Fin (Width N) → ℝ, Admissible α s →
        LebesgueConstant N s ≤ C * ((N : ℝ) ^ (2 * α) - 1) / (α * (1 - 2 * α))

/-- The second constant may depend on alpha, with no logarithmic loss. -/
def SecondBound : Prop :=
  ∀ α : ℝ, (1 : ℝ) / 4 < α → α < (1 : ℝ) / 2 →
    ∃ Cα : ℝ, 0 < Cα ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ s : Fin (Width N) → ℝ, Admissible α s →
        InverseNorm N s ≤ Cα * (N : ℝ) ^ (4 * α - 1)

def Target : Prop := FirstBound ∧ SecondBound

#assert_statement FirstBound
#assert_statement SecondBound
#assert_statement Target
#assert_trust kernel FirstBound
#assert_trust kernel SecondBound
#assert_trust kernel Target
#print axioms FirstBound
#print axioms SecondBound
#print axioms Target

end NLA.Statements.IE26
