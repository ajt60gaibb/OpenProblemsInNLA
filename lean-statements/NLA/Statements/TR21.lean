import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Sqrt
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-21: the exact expected injective norm comparison for arbitrary iid
integrable centered real tensor entries. See the complete source and numerical
specification in docs/lean/statements/TR-21/. No comparison theorem is proved
in this statement-only module. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open MeasureTheory

namespace NLA.Statements.TR21

/-- All rectangular tensor coordinates, with one finite index per mode. -/
abbrev TensorIndex (r : ℕ) (n : Fin r → ℕ) := (j : Fin r) → Fin (n j)

abbrev Tensor (r : ℕ) (n : Fin r → ℕ) := TensorIndex r n → ℝ

/-- A tuple of real Euclidean unit vectors, one for every mode. -/
def UnitVectors {r : ℕ} {n : Fin r → ℕ}
    (x : (j : Fin r) → Fin (n j) → ℝ) : Prop :=
  ∀ j : Fin r, (∑ a : Fin (n j), (x j a) ^ 2) = 1

/-- Full multilinear contraction against arbitrary real unit vectors. -/
def Contraction {r : ℕ} {n : Fin r → ℕ} (t : Tensor r n)
    (x : (j : Fin r) → Fin (n j) → ℝ) : ℝ :=
  ∑ i : TensorIndex r n, t i * ∏ j : Fin r, x j (i j)

/-- The true injective norm: the absolute value surrounds the full
contraction, and the supremum ranges over all tuples of unit vectors. -/
noncomputable def InjectiveNorm {r : ℕ} {n : Fin r → ℕ}
    (t : Tensor r n) : ℝ :=
  sSup {y : ℝ | ∃ x : (j : Fin r) → Fin (n j) → ℝ,
    UnitVectors x ∧ y = |Contraction t x|}

/-- Euclidean norm of a mode-j fiber. A full index fixes every coordinate
except j; duplicate descriptions of the same fiber do not affect a maximum. -/
noncomputable def FiberNorm {r : ℕ} {n : Fin r → ℕ}
    (t : Tensor r n) (j : Fin r) (i : TensorIndex r n) : ℝ :=
  Real.sqrt (∑ a : Fin (n j), (t (Function.update i j a)) ^ 2)

/-- Samplewise maximum over every mode-j fiber. -/
noncomputable def FiberMaximum {r : ℕ} {n : Fin r → ℕ}
    (t : Tensor r n) (j : Fin r) : ℝ :=
  sSup {y : ℝ | ∃ i : TensorIndex r n, y = FiberNorm t j i}

/-- An arbitrary centered integrable common entry law. Its first absolute
moment is finite; no variance, density, symmetry or tail hypothesis occurs. -/
def AdmissibleLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ Integrable (fun z : ℝ => z) μ ∧
    (∫ z : ℝ, z ∂μ) = 0

/-- Finite product of the common entry law: exactly the iid joint law.
The measure may vary with the rectangular dimensions in the target. -/
noncomputable def TensorLaw (r : ℕ) (n : Fin r → ℕ)
    (μ : Measure ℝ) : Measure (Tensor r n) :=
  Measure.pi (fun _ : TensorIndex r n => μ)

/-- The mode maximum is outside the expectation; each fiber maximum is
inside its expectation. -/
noncomputable def FiberScale (r : ℕ) (n : Fin r → ℕ)
    (μ : Measure ℝ) : ℝ :=
  sSup {y : ℝ | ∃ j : Fin r,
    y = ∫ t : Tensor r n, FiberMaximum t j ∂TensorLaw r n μ}

noncomputable def ExpectedInjectiveNorm (r : ℕ) (n : Fin r → ℕ)
    (μ : Measure ℝ) : ℝ :=
  ∫ t : Tensor r n, InjectiveNorm t ∂TensorLaw r n μ

/-- The complete original comparison. Each pair of constants is chosen
before every rectangular format and every dimension-dependent entry law. -/
def Target : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ n : Fin r → ℕ, (∀ j : Fin r, 2 ≤ n j) →
        ∀ μ : Measure ℝ, AdmissibleLaw μ →
          c * FiberScale r n μ ≤ ExpectedInjectiveNorm r n μ ∧
            ExpectedInjectiveNorm r n μ ≤ C * FiberScale r n μ

/-- The resolution's additional lower coefficient exactly one, separately
recorded so the principal target remains the original conjecture. -/
def ManuscriptQuantitativeBound : Prop :=
  ∀ r : ℕ, 3 ≤ r →
    ∃ C : ℝ, 0 < C ∧
      ∀ n : Fin r → ℕ, (∀ j : Fin r, 2 ≤ n j) →
        ∀ μ : Measure ℝ, AdmissibleLaw μ →
          FiberScale r n μ ≤ ExpectedInjectiveNorm r n μ ∧
            ExpectedInjectiveNorm r n μ ≤ C * FiberScale r n μ

#assert_statement Target
#assert_statement ManuscriptQuantitativeBound
#assert_trust kernel Target
#assert_trust kernel ManuscriptQuantitativeBound
#print axioms Target

end NLA.Statements.TR21
