/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
AI-assisted statement draft; no complete proof or verification is claimed.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Defs

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Set

namespace NLA.TR06

abbrev TensorIndex (d : ℕ) (n : Fin d → ℕ) := (j : Fin d) → Fin (n j)
abbrev Tensor (𝕜 : Type*) (d : ℕ) (n : Fin d → ℕ) :=
  EuclideanSpace 𝕜 (TensorIndex d n)

variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ}

/-- The product is over tensor modes, and the ambient norm is Euclidean. -/
def pureTensor (u : (j : Fin d) → Fin (n j) → 𝕜) : Tensor 𝕜 d n :=
  WithLp.toLp 2 (fun q => ∏ j, u j (q j))

/-- Actual nonzero rank-one tensors, with factor rescaling already quotiented
out by equality of the tensor coordinates. -/
def RankOne (A : Tensor 𝕜 d n) : Prop :=
  A ≠ 0 ∧ ∃ u : (j : Fin d) → Fin (n j) → 𝕜, pureTensor u = A

def Decomposes {r : ℕ} (a : Fin r → Tensor 𝕜 d n) (A : Tensor 𝕜 d n) : Prop :=
  (∀ i, RankOne (a i)) ∧ ∑ i, a i = A

def ExactRank (r : ℕ) (A : Tensor 𝕜 d n) : Prop :=
  (∃ a : Fin r → Tensor 𝕜 d n, Decomposes a A) ∧
  ∀ m < r, ¬ ∃ a : Fin m → Tensor 𝕜 d n, Decomposes a A

/-- Uniqueness of actual tensor summands up to their order. -/
def Identifiable (r : ℕ) (A : Tensor 𝕜 d n) : Prop :=
  ∀ a b : Fin r → Tensor 𝕜 d n, Decomposes a A → Decomposes b A →
    ∃ σ : Equiv.Perm (Fin r), ∀ i, b i = a (σ i)

/-- A nonvacuous principal Zariski-open witness for generic COMPLEX
identifiability. Its equivalence to the source formulation remains an explicit
statement-review and proof obligation. No analytic consequence is a field. -/
def GenericComplexIdentifiable (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Prop :=
  ∃ p : MvPolynomial (TensorIndex d n) ℂ,
    (∃ A : Tensor ℂ d n, ExactRank r A ∧ MvPolynomial.eval (fun q => A q) p ≠ 0) ∧
    ∀ A : Tensor ℂ d n, ExactRank r A → MvPolynomial.eval (fun q => A q) p ≠ 0 →
      Identifiable r A

/-- Dimension expected from generically finite ordered addition. The assertion
that this is the geometric dimension is a proof obligation, not a definition. -/
def expectedDimension (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : ℕ :=
  r * (1 + ∑ j, (n j - 1))

def identifiableRealSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Set (Tensor ℝ d n) :=
  {A | ExactRank r A ∧ Identifiable r A}

/-- Flattening the summand and tensor indices gives the l2 product Frobenius
norm, not the supremum norm of an unadorned function space. -/
abbrev AngularOutput (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  EuclideanSpace ℝ (Fin r × TensorIndex d n)

def normalizedTuple {r : ℕ} (a : Fin r → Tensor ℝ d n) : AngularOutput d n r :=
  WithLp.toLp 2 (fun q => a q.1 q.2 / ‖a q.1‖)

/-- Order-free normalized distance. On identifiable exact-rank inputs the
infimum reduces to the finite minimum over permutations; that reduction must
be proved. Outside that domain this definition is not advertised as a metric. -/
def angularDistance (r : ℕ) (A B : Tensor ℝ d n) : ℝ≥0∞ :=
  ⨅ (a : Fin r → Tensor ℝ d n) (_ : Decomposes a A)
    (b : Fin r → Tensor ℝ d n) (_ : Decomposes b B),
    edist (normalizedTuple a) (normalizedTuple b)

/-- Extended pointwise slope within the actual identifiable real rank-r set.
Its equality to the original intrinsic derivative norm is REQUIRED separately;
this definition alone does not establish correspondence with TR-06. -/
def angularSlope (r : ℕ) (A : Tensor ℝ d n) : ℝ≥0∞ :=
  ⨅ (ε : ℝ) (_ : 0 < ε),
    ⨆ (B : Tensor ℝ d n) (_ : B ∈ identifiableRealSet d n r)
      (_ : B ≠ A) (_ : dist A B < ε), angularDistance r A B / edist A B

def tensorVolume (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (μHE[expectedDimension d n r]).restrict (identifiableRealSet d n r)

def gaussianWeight (A : Tensor ℝ d n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-‖A‖ ^ 2 / 2))

def unnormalizedInput (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (tensorVolume d n r).withDensity gaussianWeight

def normalization (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : ℝ≥0∞ :=
  unnormalizedInput d n r Set.univ

def inputMeasure (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (normalization d n r)⁻¹ • unnormalizedInput d n r

/-- Chart version of the intrinsic operator norm: the input differential uses
its induced ambient Frobenius norm. Injectivity of dφ is a hypothesis of the
correspondence theorem, not hidden in this definition. -/
def derivativeRatio {k r : ℕ}
    (dφ : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (dg : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r) : ℝ≥0∞ :=
  ⨆ v : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (‖dg v‖ / ‖dφ v‖)

/-- The actual continuous linear operator on the input tangent subspace,
obtained by inverting the injective chart differential onto its range. -/
def inducedDerivative {k r : ℕ}
    (dφ : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (dg : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r)
    (hinj : Function.Injective dφ) :
    LinearMap.range dφ.toLinearMap →L[ℝ] AngularOutput d n r :=
  dg.comp (LinearEquiv.ofInjective dφ.toLinearMap hinj).toContinuousLinearEquiv.symm.toContinuousLinearMap

end NLA.TR06

namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- A genuine local embedded smooth chart with a smooth ordered decomposition.
Existence of these charts almost everywhere must be proved from the algebraic
hypothesis. This structure is not a parameter of the main integrability theorem.
The chart target is open in the WHOLE identifiable set, excluding the hidden
extra-sheet problem for merely immersed images. -/
structure DecompositionChart (d : ℕ) (n : Fin d → ℕ) (r : ℕ) where
  chart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (identifiableRealSet d n r)
  summands : EuclideanSpace ℝ (Fin (expectedDimension d n r)) → Fin r → Tensor ℝ d n
  decomposes : ∀ u ∈ chart.source, Decomposes (summands u) (chart u).val
  input_smooth : ContDiffOn ℝ 1 (fun u => (chart u).val) chart.source
  summands_smooth : ∀ i, ContDiffOn ℝ 1 (fun u => summands u i) chart.source
  output_smooth : ContDiffOn ℝ 1 (fun u => normalizedTuple (summands u)) chart.source
  input_injective_derivative : ∀ u ∈ chart.source,
    Function.Injective (fderiv ℝ (fun v => (chart v).val) u)

def regularSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Set (Tensor ℝ d n) :=
  {A | ∃ c : DecompositionChart d n r, ∃ u ∈ c.chart.source, (c.chart u).val = A}

/-- Euclidean induced-volume candidate on the chart-regular locus. Agreement
with chart Jacobian volume is an advertised mandatory proof obligation. -/
def regularVolume (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (μHE[expectedDimension d n r]).restrict (regularSet d n r)

def regularNormalization (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ A, gaussianWeight A ∂(regularVolume d n r)

def regularInputMeasure (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (regularNormalization d n r)⁻¹ • (regularVolume d n r).withDensity gaussianWeight

end NLA.TR06

namespace NLA.TR06

/-- Source genericity: an algebraic exceptional set, given by an arbitrary
family of equations, proper RELATIVE to the complex exact-rank-r tensors.
The nonzero witness is part of properness, not an analytic hypothesis. -/
def SourceGenericComplexIdentifiable (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Prop :=
  ∃ P : Set (MvPolynomial (TensorIndex d n) ℂ),
    (∃ A : Tensor ℂ d n, ExactRank r A ∧
      ∃ p ∈ P, MvPolynomial.eval (fun q => A q) p ≠ 0) ∧
    ∀ A : Tensor ℂ d n, ExactRank r A →
      (∃ p ∈ P, MvPolynomial.eval (fun q => A q) p ≠ 0) → Identifiable r A

/-- The original smooth identifiable input manifold, presented by genuine
embedded smooth charts. No inverse decomposition is included in this notion. -/
structure SourceSmoothChart (d : ℕ) (n : Fin d → ℕ) (r : ℕ) where
  chart : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (identifiableRealSet d n r)
  input_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (chart u).val) chart.source
  input_injective_derivative : ∀ u ∈ chart.source,
    Function.Injective (fderiv ℝ (fun v => (chart v).val) u)

def sourceSmoothSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Set (Tensor ℝ d n) :=
  {A | ∃ c : SourceSmoothChart d n r, ∃ u ∈ c.chart.source, (c.chart u).val = A}

/-- Smooth ordered decompositions over a smooth embedded input chart. A
separate required theorem identifies each branch with a genuine local inverse
of addition on an OPEN subset of the whole ordered rank-one product. -/
structure SmoothDecompositionChart (d : ℕ) (n : Fin d → ℕ) (r : ℕ)
    extends SourceSmoothChart d n r where
  summands : EuclideanSpace ℝ (Fin (expectedDimension d n r)) → Fin r → Tensor ℝ d n
  decomposes : ∀ u ∈ chart.source, Decomposes (summands u) (chart u).val
  summands_smooth : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => summands u i) chart.source
  output_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => normalizedTuple (summands u)) chart.source

def smoothRegularSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Set (Tensor ℝ d n) :=
  {A | ∃ c : SmoothDecompositionChart d n r, ∃ u ∈ c.chart.source, (c.chart u).val = A}

abbrev OrderedRankOne (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :=
  {a : Fin r → Tensor ℝ d n // ∀ i, RankOne (a i)}

/-- Exact local inverse of the source addition map. Both source and target are
open in their actual subspace topologies; the source is not restricted in
advance to already-identifiable tuples. The neighborhood clause identifies the
inverse with the reviewed smooth summand branch near the chosen coordinate. -/
def IsLocalAdditionInverse {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) : Prop :=
  ∃ e : OpenPartialHomeomorph (OrderedRankOne d n r) (sourceSmoothSet d n r),
    (∀ a ∈ e.source, (e a).val = ∑ i, a.val i) ∧
    ∃ W : Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))),
      IsOpen W ∧ u ∈ W ∧ W ⊆ c.chart.source ∧
      ∀ v ∈ W, ∃ a : OrderedRankOne d n r,
        a ∈ e.source ∧ a.val = c.summands v ∧ (e a).val = (c.chart v).val

/-- The original angular derivative norm, represented in all smooth local
charts with the actual induced tangent norm. The supremum avoids a global
ordering choice. At points with no smooth inverse chart it is zero; using that
convention requires the separate full-measure smooth-regular-locus theorem. -/
def sourceAngular (d : ℕ) (n : Fin d → ℕ) (r : ℕ) (A : Tensor ℝ d n) : ℝ≥0∞ :=
  ⨆ (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (hu : u ∈ c.chart.source) (_ : (c.chart u).val = A),
    ENNReal.ofReal ‖inducedDerivative
      (fderiv ℝ (fun v => (c.chart v).val) u)
      (fderiv ℝ (fun v => normalizedTuple (c.summands v)) u)
      (c.input_injective_derivative u hu)‖

def sourceVolume (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (μHE[expectedDimension d n r]).restrict (sourceSmoothSet d n r)

def sourceNormalization (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ A, gaussianWeight A ∂(sourceVolume d n r)

def sourceInputMeasure (d : ℕ) (n : Fin d → ℕ) (r : ℕ) : Measure (Tensor ℝ d n) :=
  (sourceNormalization d n r)⁻¹ • (sourceVolume d n r).withDensity gaussianWeight

end NLA.TR06
