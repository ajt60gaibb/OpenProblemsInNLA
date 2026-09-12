/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Statement definitions for Matthew J. Colbrook's counterexample to MI-26.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI26

/-- Exactly the canonical real-valued concave function class on the nonnegative
half-line. Values at negative arguments are unrestricted and are irrelevant for
positive semidefinite inputs. No continuity, monotonicity, or global
nonnegativity assumption is added. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ConcaveOn ℝ (Set.Ici 0) f ∧ 0 ≤ f 0

/-- Genuine real continuous functional calculus in the complex matrix algebra.
Every function is continuous on a Hermitian matrix's finite spectrum, even
when it is not continuous at an endpoint of the entire half-line. -/
def functionalCalculus {n : ℕ} (f : ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cfc (R := ℝ) f A

/-- Conjugation by an arbitrary complex unitary, with its actual conjugate transpose. -/
def unitaryConjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (H : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U : Matrix (Fin n) (Fin n) ℂ) * H *
    (U : Matrix (Fin n) (Fin n) ℂ).conjTranspose

/-- The complete original MI-26 conjecture. The order is the genuine positive
semidefinite matrix order, and the unitaries may depend on all previous inputs. -/
def SubadditivityConjecture : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ A B : Matrix (Fin n) (Fin n) ℂ,
    A.PosSemidef → B.PosSemidef → ∀ f : ℝ → ℝ, AdmissibleFunction f →
      ∃ U V : Matrix.unitaryGroup (Fin n) ℂ,
        functionalCalculus f (A + B) ≤
          unitaryConjugate U (functionalCalculus f A) +
            unitaryConjugate V (functionalCalculus f B)

/-- Colbrook's real-valued concave polynomial; it is negative when `t > 1`. -/
def witnessFunction (t : ℝ) : ℝ := t - t ^ 2

/-- The first rational rank-one orthogonal projection in the source. -/
def witnessP : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The projection onto the unit vector `(3/5,4/5)`. -/
def witnessQ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![9 / 25, 12 / 25; 12 / 25, 16 / 25]

/-- The exact matrix obtained by applying `t - t²` to `P+Q`. This is a
named numerical target, not a replacement for the actual functional calculus. -/
def witnessImage : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-18 / 25, -12 / 25; -12 / 25, 0]

/-- A vector on which the actual image has a strictly positive quadratic form. -/
def witnessVector : Fin 2 → ℂ := ![1, -2]

end NLA.MI26
