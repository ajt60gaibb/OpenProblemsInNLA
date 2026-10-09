import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! SP-13: full complex spectral distributions under trace-norm-small
perturbations. Exact specification: docs/lean/statements/SP-13/NUMERICAL_TARGETS.md.
The proposition is defined, not proved. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators
open MeasureTheory Filter

namespace NLA.Statements.SP13

abbrev MatrixSequence := (n : ℕ) → Matrix (Fin n) (Fin n) ℂ

/-- Complex Hermitian symmetry, with conjugation. -/
def Hermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i j, A i j = star (A j i)

/-- All n singular values of the actual matrix between complex Euclidean spaces. -/
noncomputable def NuclearNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i : Fin n, (Matrix.toEuclideanLin A).singularValues i.val

/-- Characteristic roots are a multiset, retaining algebraic multiplicities. -/
noncomputable def Empirical {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (F : ℂ → ℂ) : ℂ :=
  (1 / (n : ℂ)) * (A.charpoly.roots.map F).sum

/-- Only values on the unit interval are used; no regularity is imposed outside it. -/
noncomputable def SymbolIntegral (f : ℝ → ℝ) (F : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ, F (f t : ℂ) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Every complex-valued continuous compactly supported test is quantified. -/
def Distributed (A : MatrixSequence) (f : ℝ → ℝ) : Prop :=
  ∀ F : ℂ → ℂ, Continuous F → HasCompactSupport F →
    Tendsto (fun n => Empirical (A n) F) atTop (nhds (SymbolIntegral f F))

/-- Full original domain: arbitrary perturbations, no uniform spectral bounds,
and Lebesgue-measurable symbols up to their irrelevant null-set values. -/
def Target : Prop :=
  ∀ H E : MatrixSequence, ∀ f : ℝ → ℝ,
    AEMeasurable f (volume.restrict (Set.Icc (0 : ℝ) 1)) →
    (∀ n, Hermitian (H n)) → Distributed H f →
    Tendsto (fun n => NuclearNorm (E n) / (n : ℝ)) atTop (nhds 0) →
    Distributed (fun n => H n + E n) f

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.Statements.SP13
