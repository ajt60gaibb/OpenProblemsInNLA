/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical counterexample: Matthew J. Colbrook.
AI-assisted statement draft. No completed proof or verification is claimed.
-/
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

noncomputable section
open scoped BigOperators TensorProduct LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace NLA.TR27

/-- A finite coordinate presentation of a projective algebraic subset of an
arbitrary complex vector space. No geometric admissibility or rank conclusion
is built into these data; those properties are stated separately below. -/
structure ProjectiveVariety (W : Type*) [AddCommGroup W] [Module ℂ W] where
  dimension : ℕ
  coordinates : W ≃ₗ[ℂ] (Fin dimension → ℂ)
  ideal : Ideal (MvPolynomial (Fin dimension) ℂ)

namespace ProjectiveVariety

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The entire affine zero locus, transported by the actual coordinate map. -/
def cone (X : ProjectiveVariety W) : Set W :=
  X.coordinates ⁻¹' MvPolynomial.zeroLocus ℂ X.ideal

/-- Projective points of the entire zero locus, using Mathlib representatives.
Homogeneity ensures representative independence; Challenge requires its proof. -/
def points (X : ProjectiveVariety W) : Set (ℙ ℂ W) :=
  {p | p.rep ∈ X.cone}

/-- Classical reduced irreducible nondegenerate projective-variety conditions
in homogeneous coordinates. There is no rank, decomposition or answer premise. -/
def Admissible (X : ProjectiveVariety W) : Prop :=
  X.ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin X.dimension) ℂ) ∧
  X.ideal.IsPrime ∧
  IsReduced ((MvPolynomial (Fin X.dimension) ℂ) ⧸ X.ideal) ∧
  (∃ v : W, v ∈ X.cone ∧ v ≠ 0) ∧
  Submodule.span ℂ X.cone = ⊤

/-- Common zero set of all homogeneous equations vanishing on the given
projective point set. The degree ranges over every natural number. -/
def zariskiClosure (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) : Set (ℙ ℂ W) :=
  {p | ∀ (f : MvPolynomial (Fin X.dimension) ℂ) (d : ℕ),
    f.IsHomogeneous d →
    (∀ q ∈ Y, MvPolynomial.eval (X.coordinates q.rep) f = 0) →
    MvPolynomial.eval (X.coordinates p.rep) f = 0}

def IsClosed (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) : Prop :=
  X.zariskiClosure Y = Y

/-- The classical closed-set union criterion, stated at complex points rather
than the generic prime-ideal points of a scheme spectrum. -/
def IsIrreducible (X : ProjectiveVariety W) (Y : Set (ℙ ℂ W)) : Prop :=
  Y.Nonempty ∧ ∀ A B : Set (ℙ ℂ W), X.IsClosed A → X.IsClosed B →
    Y ⊆ A ∪ B → Y ⊆ A ∨ Y ⊆ B

/-- Ordinary all-polynomial affine Zariski closure in the same coordinates. -/
def affineClosure (X : ProjectiveVariety W) (A : Set W) : Set W :=
  X.coordinates ⁻¹' MvPolynomial.zeroLocus ℂ
    (MvPolynomial.vanishingIdeal ℂ (X.coordinates '' A))

/-- Change of ambient vector space with the original coordinate ideal retained. -/
def transport {U : Type*} [AddCommGroup U] [Module ℂ U]
    (X : ProjectiveVariety W) (e : W ≃ₗ[ℂ] U) : ProjectiveVariety U where
  dimension := X.dimension
  coordinates := e.symm.trans X.coordinates
  ideal := X.ideal

end ProjectiveVariety

section RankDefinitions

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- At most r projective points, with their actual projective linear span.
Lists may repeat points; the length k may be zero. -/
def ProjectiveRankAtMost (X : Set (ℙ ℂ W)) (r : ℕ) (p : ℙ ℂ W) : Prop :=
  ∃ k : ℕ, k ≤ r ∧ ∃ q : Fin k → ℙ ℂ W,
    (∀ i, q i ∈ X) ∧ p ∈ Projectivization.Subspace.span (Set.range q)

/-- Least spanning length. The Challenge separately requires nonempty length
sets for admissible varieties, so no default infimum is used as evidence. -/
def projectiveRank (X : Set (ℙ ℂ W)) (p : ℙ ℂ W) : ℕ :=
  sInf {r : ℕ | ProjectiveRankAtMost X r p}

def borderRank (X : ProjectiveVariety W) (p : ℙ ℂ W) : ℕ :=
  sInf {r : ℕ | p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points r q}}

/-- Affine form of a span decomposition, with unrestricted complex scalars. -/
def ConeRankAtMost (C : Set W) (r : ℕ) (v : W) : Prop :=
  ∃ k : ℕ, k ≤ r ∧ ∃ (a : Fin k → ℂ) (x : Fin k → W),
    (∀ i, x i ∈ C) ∧ v = ∑ i, a i • x i

/-- Both tensor factors are selected independently from the whole cone. -/
def TensorRankAtMost (C : Set W) (r : ℕ) (z : W ⊗[ℂ] W) : Prop :=
  ∃ k : ℕ, k ≤ r ∧ ∃ (a : Fin k → ℂ) (x y : Fin k → W),
    (∀ i, x i ∈ C ∧ y i ∈ C) ∧ z = ∑ i, a i • (x i ⊗ₜ[ℂ] y i)

/-- Nonzero scalar equality with a representative of a projective point. -/
def Represents (v : W) (p : ℙ ℂ W) : Prop :=
  ∃ a : ℂ, a ≠ 0 ∧ p.rep = a • v

/-- The full Segre image, formed in the ordinary unmerged tensor product. -/
def segrePoints (X : Set (ℙ ℂ W)) : Set (ℙ ℂ (W ⊗[ℂ] W)) :=
  {q | ∃ x ∈ X, ∃ y ∈ X, Represents (x.rep ⊗ₜ[ℂ] y.rep) q}

/-- The point represented by p tensor p, without selecting a new representative.
Challenge explicitly requires existence and uniqueness for this relation. -/
def IsTensorSquare (p : ℙ ℂ W) (q : ℙ ℂ (W ⊗[ℂ] W)) : Prop :=
  Represents (p.rep ⊗ₜ[ℂ] p.rep) q

end RankDefinitions

/-- The complete original universal implication, over arbitrary complex vector
spaces equipped with a finite coordinate presentation of an admissible variety.
The coordinates do not constrain its dimension, variety, points or coefficients.
All finite-dimensional complex spaces admit such coordinates (required below). -/
def CanonicalConjecture : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
    (X : ProjectiveVariety W), X.Admissible →
    ∀ (p : ℙ ℂ W) (q : ℙ ℂ (W ⊗[ℂ] W)), IsTensorSquare p q →
      borderRank X p < projectiveRank X.points p →
      projectiveRank (segrePoints X.points) q < (projectiveRank X.points p) ^ 2

abbrev SourceSpace := Fin 13 → ℂ
abbrev Space := Fin 12 → ℂ
abbrev ParameterSpace := Fin 2 → ℂ
abbrev CoordinatePolynomial := MvPolynomial (Fin 12) ℂ
abbrev ParameterPolynomial := MvPolynomial (Fin 2) ℂ

/-- Ordered coordinates 0,2,3,...,12 of the source space. -/
def coordinateIndex (j : Fin 12) : Fin 13 := if j = 0 then 0 else j.succ

def powerSum (j : ℕ) : ℂ := 1 + 2 ^ j + 3 ^ j

def sourceUnit (i : Fin 13) : SourceSpace := fun j => if i = j then 1 else 0

def sourceCurve (t : Option ℂ) : SourceSpace :=
  match t with
  | none => sourceUnit 12
  | some a => fun j => a ^ (j : ℕ)

def center : SourceSpace :=
  sourceUnit 1 - sourceCurve (some 1) - sourceCurve (some 2) - sourceCurve (some 3)

/-- Explicit quotient-coordinate function. Its actual linearity and kernel are
required Challenge obligations, rather than assumptions or opaque fields. -/
def quotientMap (w : SourceSpace) : Space :=
  fun j => 5 * w (coordinateIndex j) - powerSum (coordinateIndex j : ℕ) * w 1

def curve (t : Option ℂ) : Space := quotientMap (sourceCurve t)
def witnessVector : Space := quotientMap (sourceUnit 1)

/-- Every scalar multiple of every finite-parameter or infinity point. -/
def parameterizedCone : Set Space :=
  {w | w = 0 ∨ ∃ a : ℂ, a ≠ 0 ∧ ∃ t : Option ℂ, w = a • curve t}

def homogeneousCoordinate (j : Fin 12) : ParameterPolynomial :=
  MvPolynomial.C 5 * MvPolynomial.X 0 ^ (12 - (coordinateIndex j : ℕ)) *
      MvPolynomial.X 1 ^ (coordinateIndex j : ℕ) -
    MvPolynomial.C (powerSum (coordinateIndex j : ℕ)) *
      MvPolynomial.X 0 ^ 11 * MvPolynomial.X 1

def homogeneousMap (w : ParameterSpace) : Space :=
  fun j => MvPolynomial.eval w (homogeneousCoordinate j)

def coordinateSubstitution : CoordinatePolynomial →ₐ[ℂ] ParameterPolynomial :=
  MvPolynomial.aeval homogeneousCoordinate

def witnessIdeal : Ideal CoordinatePolynomial :=
  RingHom.ker (coordinateSubstitution : CoordinatePolynomial →+* ParameterPolynomial)

def witnessVariety : ProjectiveVariety Space where
  dimension := 12
  coordinates := LinearEquiv.refl ℂ Space
  ideal := witnessIdeal

/-- Polynomial extension of (g(t)-g(0))/t, including t=0. -/
def borderCurve (t : ℂ) : Space := fun j =>
  if coordinateIndex j = 0 then -3
  else 5 * t ^ ((coordinateIndex j : ℕ) - 1) - powerSum (coordinateIndex j : ℕ)

end NLA.TR27
