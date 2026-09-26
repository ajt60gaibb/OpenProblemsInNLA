import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Reusable implicit reduction for an already split product map

This file packages the local Lyapunov--Schmidt argument independently of the
cone problem.  The source and target are already written as products
`B × X` and `Y × Z`.  The partial derivative of the `Y` equation in the `X`
direction is assumed invertible.  The implicit-function theorem then solves
that equation for `X`; the remaining `Z` component is the reduced equation.

Import it through `Schiffer.Reusable` when using the project's general-purpose
analysis library.  It is intentionally outside the dependency chain of the
counterexample.
-/

open Filter
open scoped Topology

noncomputable section

namespace Schiffer
namespace ImplicitProductReduction

variable {𝕜 : Type*} [RCLike 𝕜]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [CompleteSpace B]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]

/-- Hypotheses for a local Lyapunov--Schmidt reduction.  `B` contains every
variable retained in the reduced equation (parameters and kernel variables),
`X` is the source complement, `Y` is the range component solved by the
implicit-function theorem, and `Z` is the finite-dimensional obstruction in
the usual applications.  No finite-dimensionality is needed for the abstract
argument. -/
structure Data (n : WithTop ℕ∞) where
  map : B × X → Y × Z
  base : B × X
  map_base : map base = 0
  contDiffAt : ContDiffAt 𝕜 n map base
  order_ne_zero : n ≠ 0
  complementDerivative_invertible :
    (fderiv 𝕜 (fun q : B × X => (map q).1) base ∘L
      ContinuousLinearMap.inr 𝕜 B X).IsInvertible

namespace Data

variable {n : WithTop ℕ∞} (d : Data (𝕜 := 𝕜) (B := B) (X := X) (Y := Y) (Z := Z) n)

/-- The component of the equation eliminated by the implicit-function theorem. -/
def complementEquation (q : B × X) : Y :=
  (d.map q).1

omit [CompleteSpace B] [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z] in
theorem complementEquation_contDiffAt :
    ContDiffAt 𝕜 n d.complementEquation d.base := by
  exact d.contDiffAt.fst

omit [CompleteSpace B] [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z] in
theorem complementEquation_base : d.complementEquation d.base = 0 := by
  rw [complementEquation]
  exact congrArg Prod.fst d.map_base

omit [CompleteSpace B] [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z] in
private theorem complementDerivativeIsInvertible :
    (fderiv 𝕜 d.complementEquation d.base ∘L
      ContinuousLinearMap.inr 𝕜 B X).IsInvertible := by
  simpa only [complementEquation] using d.complementDerivative_invertible

/-- The canonical complement correction supplied by the implicit-function theorem. -/
def complement : B → X :=
  d.complementEquation_contDiffAt.implicitFunction d.order_ne_zero
    d.complementDerivativeIsInvertible

/-- The reduced obstruction map. -/
def reduced (b : B) : Z :=
  (d.map (b, d.complement b)).2

omit [CompleteSpace Z] in
theorem complement_base : d.complement d.base.1 = d.base.2 := by
  exact d.complementEquation_contDiffAt.implicitFunction_apply_self
    d.order_ne_zero d.complementDerivativeIsInvertible

omit [CompleteSpace Z] in
theorem complement_contDiffAt :
    ContDiffAt 𝕜 n d.complement d.base.1 := by
  exact d.complementEquation_contDiffAt.contDiffAt_implicitFunction
    d.order_ne_zero d.complementDerivativeIsInvertible

omit [CompleteSpace Z] in
theorem complement_hasStrictFDerivAt :
    HasStrictFDerivAt d.complement
      (-(fderiv 𝕜 d.complementEquation d.base ∘L
          ContinuousLinearMap.inr 𝕜 B X).inverse ∘L
        (fderiv 𝕜 d.complementEquation d.base ∘L
          ContinuousLinearMap.inl 𝕜 B X)) d.base.1 := by
  exact d.complementEquation_contDiffAt.hasStrictFDerivAt_implicitFunction
    d.order_ne_zero d.complementDerivativeIsInvertible

omit [CompleteSpace Z] in
/-- Near the base point, the canonical graph solves the complement equation. -/
theorem eventually_complementEquation_eq_zero :
    ∀ᶠ b in 𝓝 d.base.1,
      d.complementEquation (b, d.complement b) = 0 := by
  filter_upwards [d.complementEquation_contDiffAt.eventually_apply_implicitFunction
      d.order_ne_zero d.complementDerivativeIsInvertible] with b hb
  simpa only [complement, d.complementEquation_base] using hb

omit [CompleteSpace Z] in
/-- Local uniqueness of the complement correction. -/
theorem eventually_complementEquation_eq_zero_iff :
    ∀ᶠ q in 𝓝 d.base,
      d.complementEquation q = 0 ↔ d.complement q.1 = q.2 := by
  filter_upwards [d.complementEquation_contDiffAt.eventually_apply_eq_iff_implicitFunction
      d.order_ne_zero d.complementDerivativeIsInvertible] with q hq
  simpa only [complement, d.complementEquation_base] using hq

omit [CompleteSpace Z] in
theorem reduced_base : d.reduced d.base.1 = 0 := by
  rw [reduced, d.complement_base]
  exact congrArg Prod.snd d.map_base

omit [CompleteSpace Z] in
theorem reduced_contDiffAt : ContDiffAt 𝕜 n d.reduced d.base.1 := by
  have hgraph : ContDiffAt 𝕜 n (fun b : B => (b, d.complement b)) d.base.1 :=
    contDiffAt_id.prodMk d.complement_contDiffAt
  have hgraph_base : (d.base.1, d.complement d.base.1) = d.base := by
    rw [d.complement_base]
  have hmap : ContDiffAt 𝕜 n d.map (d.base.1, d.complement d.base.1) := by
    simpa only [hgraph_base] using d.contDiffAt
  exact (hmap.comp d.base.1 hgraph).snd

omit [CompleteSpace Z] in
theorem reduced_hasStrictFDerivAt :
    HasStrictFDerivAt d.reduced (fderiv 𝕜 d.reduced d.base.1) d.base.1 :=
  d.reduced_contDiffAt.hasStrictFDerivAt d.order_ne_zero

omit [CompleteSpace Z] in
/-- On the canonical graph, solving the full equation is equivalent to solving
the reduced equation. -/
theorem eventually_map_graph_eq_zero_iff :
    ∀ᶠ b in 𝓝 d.base.1,
      d.map (b, d.complement b) = 0 ↔ d.reduced b = 0 := by
  filter_upwards [d.eventually_complementEquation_eq_zero] with b hb
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro h
    apply Prod.ext
    · simpa only [complementEquation] using hb
    · exact h

omit [CompleteSpace Z] in
/-- Local description of the complete zero set: a point solves the original
equation exactly when it lies on the canonical complement graph and its base
coordinate solves the reduced equation. -/
theorem eventually_map_eq_zero_iff :
    ∀ᶠ q in 𝓝 d.base,
      d.map q = 0 ↔ d.complement q.1 = q.2 ∧ d.reduced q.1 = 0 := by
  filter_upwards [d.eventually_complementEquation_eq_zero_iff] with q hq
  constructor
  · intro h
    have hcomp : d.complementEquation q = 0 := by
      exact congrArg Prod.fst h
    have hgraph : d.complement q.1 = q.2 := hq.mp hcomp
    refine ⟨hgraph, ?_⟩
    rw [reduced, hgraph]
    exact congrArg Prod.snd h
  · rintro ⟨hgraph, hred⟩
    have hcomp : d.complementEquation q = 0 := hq.mpr hgraph
    apply Prod.ext
    · simpa only [complementEquation] using hcomp
    · rw [reduced, hgraph] at hred
      exact hred

end Data

/-- A packaged local Lyapunov--Schmidt reduction. -/
structure Reduction {n : WithTop ℕ∞}
    (d : Data (𝕜 := 𝕜) (B := B) (X := X) (Y := Y) (Z := Z) n) where
  complement : B → X
  reduced : B → Z
  complement_base : complement d.base.1 = d.base.2
  complement_contDiffAt : ContDiffAt 𝕜 n complement d.base.1
  reduced_base : reduced d.base.1 = 0
  reduced_contDiffAt : ContDiffAt 𝕜 n reduced d.base.1
  eventually_complementEquation_eq_zero :
    ∀ᶠ b in 𝓝 d.base.1, d.complementEquation (b, complement b) = 0
  eventually_complementEquation_eq_zero_iff :
    ∀ᶠ q in 𝓝 d.base,
      d.complementEquation q = 0 ↔ complement q.1 = q.2
  eventually_map_graph_eq_zero_iff :
    ∀ᶠ b in 𝓝 d.base.1,
      d.map (b, complement b) = 0 ↔ reduced b = 0
  eventually_map_eq_zero_iff :
    ∀ᶠ q in 𝓝 d.base,
      d.map q = 0 ↔ complement q.1 = q.2 ∧ reduced q.1 = 0

/-- The canonical abstract Lyapunov--Schmidt reduction. -/
def Data.reduction {n : WithTop ℕ∞}
    (d : Data (𝕜 := 𝕜) (B := B) (X := X) (Y := Y) (Z := Z) n) :
    Reduction d where
  complement := d.complement
  reduced := d.reduced
  complement_base := d.complement_base
  complement_contDiffAt := d.complement_contDiffAt
  reduced_base := d.reduced_base
  reduced_contDiffAt := d.reduced_contDiffAt
  eventually_complementEquation_eq_zero := d.eventually_complementEquation_eq_zero
  eventually_complementEquation_eq_zero_iff :=
    d.eventually_complementEquation_eq_zero_iff
  eventually_map_graph_eq_zero_iff := d.eventually_map_graph_eq_zero_iff
  eventually_map_eq_zero_iff := d.eventually_map_eq_zero_iff

omit [CompleteSpace Z] in
/-- Existence of a local Lyapunov--Schmidt reduction under the split derivative
hypothesis. -/
theorem exists_reduction {n : WithTop ℕ∞}
    (d : Data (𝕜 := 𝕜) (B := B) (X := X) (Y := Y) (Z := Z) n) :
    Nonempty (Reduction d) :=
  ⟨d.reduction⟩

end ImplicitProductReduction
end Schiffer
