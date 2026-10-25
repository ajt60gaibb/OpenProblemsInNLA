import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.Bornology.Basic

/-!
# Challenge: Schiffer to Pompeiu

This is the single trusted statement module presented to Lean's comparator.
It imports only Mathlib.  Its two proof holes are the star-shaped Schiffer
statement and the fixed-domain Schiffer-to-Pompeiu bridge.  The usual simply
connected Schiffer statement follows because a nonempty star-shaped set is
contractible, hence path connected and simply connected.  The two Pompeiu
existence theorems then follow immediately inside this file.

We identify the Euclidean plane with `ℂ`.  The theorem says that there is a
bounded, simply connected domain with `C²` boundary, not a disk, and a nonzero
continuous real function whose integral vanishes over every rigid copy of the
domain.  Here a rigid motion `ℂ ≃ᵃⁱ[ℝ] ℂ` is a bijective real-affine isometry,
that is, a map `x ↦ A x + b` with `A` orthogonal; this includes translations,
rotations, and reflections.
-/

noncomputable section

open Set Bornology MeasureTheory
open scoped Gradient Laplacian

namespace Schiffer.Comparator

/- Here `ℂ` is the real Euclidean plane.  Accordingly, Mathlib's Laplacian is
the real Laplacian
`Δu = D²u(1, 1) + D²u(Complex.I, Complex.I) = ∂²u/∂x² + ∂²u/∂y²`,
as confirmed by the Mathlib declaration
`InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane`. -/

/-- `Ω` is an ordinary open Euclidean disk, with arbitrary center and radius. -/
def IsEuclideanDisk (Ω : Set ℂ) : Prop :=
  ∃ c : ℂ, ∃ r : ℝ, Ω = Metric.ball c r

/-- `Ω` is a regular `C²` super-level set.  In particular, `Ω` is open,
because a `C²` defining function is continuous. -/
def HasC2Boundary (Ω : Set ℂ) : Prop :=
  ∃ F : ℂ → ℝ,
    ContDiff ℝ 2 F ∧
    Ω = {x | 0 < F x} ∧
    ∀ x, F x = 0 → ∇ F x ≠ 0

/-- Schiffer 1: the star-shaped counterexample, and the first proof hole. -/
theorem Schiffer_Star_Shaped :
  ∃ (Ω : Set ℂ) (u : ℂ → ℝ),
    IsBounded Ω ∧
    Nonempty Ω ∧
    -- Every line segment from the origin to a point of `Ω` stays in `Ω`.
    StarConvex ℝ 0 Ω ∧
    HasC2Boundary Ω ∧
    ¬ IsEuclideanDisk Ω ∧
    ContDiff ℝ 2 u ∧
    (∀ x ∈ Ω, -(Δ u) x = u x) ∧
    (∀ x ∈ frontier Ω, u x = 1) ∧
    (∀ x ∈ frontier Ω, ∇ u x = 0) := by
  sorry

/-- Schiffer 2: the usual simply connected counterexample, derived from
Schiffer 1 via contractibility. -/
theorem Schiffer_SimplyConnected :
  ∃ (Ω : Set ℂ) (u : ℂ → ℝ),
    IsBounded Ω ∧
    Nonempty Ω ∧
    IsPathConnected Ω ∧
    IsSimplyConnected Ω ∧
    HasC2Boundary Ω ∧
    ¬ IsEuclideanDisk Ω ∧
    ContDiff ℝ 2 u ∧
    (∀ x ∈ Ω, -(Δ u) x = u x) ∧
    (∀ x ∈ frontier Ω, u x = 1) ∧
    (∀ x ∈ frontier Ω, ∇ u x = 0) := by
  obtain ⟨Ω, u, hb, hn, hs, hC2, hD, hu, hEq, hVal, hDiff⟩ :=
    Schiffer_Star_Shaped
  letI : ContractibleSpace Ω :=
    hs.contractibleSpace (Set.nonempty_coe_sort.mp hn)
  exact ⟨Ω, u, hb, hn, isPathConnected_iff_pathConnectedSpace.mpr inferInstance,
    SimplyConnectedSpace.ofContractible Ω, hC2, hD, hu, hEq, hVal, hDiff⟩

/--
Pompeiu 3, and the second proof hole: the classical implication "Pompeiu
implies Schiffer", written in the contrapositive direction useful here.  If
one fixed domain carries Schiffer data, then that same domain fails the
Pompeiu property.
-/
theorem SchifferToPompeiu
    {Ω : Set ℂ} {u : ℂ → ℝ}
    (hbounded : IsBounded Ω)
    (hC2 : HasC2Boundary Ω)
    (huC2 : ContDiff ℝ 2 u)
    (hequation : ∀ x ∈ Ω, -(Δ u) x = u x)
    (hboundaryValue : ∀ x ∈ frontier Ω, u x = 1)
    (hboundaryGradient : ∀ x ∈ frontier Ω, ∇ u x = 0) :
    ∃ f : ℂ → ℝ,
      Continuous f ∧
      f ≠ 0 ∧
      ∀ rigidMotion : ℂ ≃ᵃⁱ[ℝ] ℂ,
        ∫ x in rigidMotion '' Ω, f x = 0 := by
  sorry

/-- Pompeiu 1: a star-shaped counterexample to the Pompeiu conjecture. -/
theorem Pompeiu_Star_Shaped :
  ∃ Ω : Set ℂ,
    IsBounded Ω ∧
    Nonempty Ω ∧
    StarConvex ℝ 0 Ω ∧
    HasC2Boundary Ω ∧
    ¬ IsEuclideanDisk Ω ∧
    ∃ f : ℂ → ℝ,
      Continuous f ∧
      f ≠ 0 ∧
      ∀ rigidMotion : ℂ ≃ᵃⁱ[ℝ] ℂ,
        ∫ x in rigidMotion '' Ω, f x = 0 := by
  rcases Schiffer_Star_Shaped with ⟨Ω, u, h⟩
  refine ⟨Ω, ?_⟩
  aesop (add unsafe apply SchifferToPompeiu)

/-- Pompeiu 2: the usual simply connected counterexample. -/
theorem Pompeiu_SimplyConnected :
  ∃ Ω : Set ℂ,
    IsBounded Ω ∧
    Nonempty Ω ∧
    IsPathConnected Ω ∧
    IsSimplyConnected Ω ∧
    HasC2Boundary Ω ∧
    ¬ IsEuclideanDisk Ω ∧
    ∃ f : ℂ → ℝ,
      Continuous f ∧
      f ≠ 0 ∧
      ∀ rigidMotion : ℂ ≃ᵃⁱ[ℝ] ℂ,
        ∫ x in rigidMotion '' Ω, f x = 0 := by
  rcases Schiffer_SimplyConnected with ⟨Ω, u, h⟩
  refine ⟨Ω, ?_⟩
  aesop (add unsafe apply SchifferToPompeiu)

end Schiffer.Comparator
