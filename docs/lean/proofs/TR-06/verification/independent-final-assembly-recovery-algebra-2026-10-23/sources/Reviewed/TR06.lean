/- Frozen statement boundary. Changes reopen independent review. -/
import Mathlib
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-! TR-06: finite mean angular condition number of identifiable real tensor
rank decompositions. The original source and exact pre-implementation
specification are retained under `docs/lean/statements/TR-06/`. This is a
statement, not a proof of integrability. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators ENNReal
open MeasureTheory

namespace NLA.ReviewedStatements.TR06

/-- Ordinary entry indices in a tensor product of finite real vector spaces. -/
abbrev Entry {d : ℕ} (dims : Fin d → ℕ) := ∀ j : Fin d, Fin (dims j)
abbrev Tensor {d : ℕ} (dims : Fin d → ℕ) (𝕜 : Type*) [RCLike 𝕜] :=
  EuclideanSpace 𝕜 (Entry dims)

/-- The actual outer product in ordinary entry coordinates. -/
def Outer {d : ℕ} {dims : Fin d → ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (factors : ∀ j : Fin d, Fin (dims j) → 𝕜) : Tensor dims 𝕜 :=
  WithLp.toLp 2 (fun ix : Entry dims => ∏ j : Fin d, factors j (ix j))

/-- Nonzero rank-one tensors, with no normalization or probabilistic law on
its factors. -/
def RankOne {d : ℕ} {dims : Fin d → ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (a : Tensor dims 𝕜) : Prop :=
  a ≠ 0 ∧ ∃ factors : ∀ j : Fin d, Fin (dims j) → 𝕜, a = Outer factors

/-- An actual length-`r` decomposition into nonzero rank-one summands. -/
def Decomposition {d : ℕ} {dims : Fin d → ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {r : ℕ} (A : Tensor dims 𝕜) (summands : Fin r → Tensor dims 𝕜) : Prop :=
  (∀ i : Fin r, RankOne (summands i)) ∧ ∑ i : Fin r, summands i = A

/-- Rank is the smallest possible number of nonzero rank-one summands. -/
def ExactRank {d : ℕ} {dims : Fin d → ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (r : ℕ) (A : Tensor dims 𝕜) : Prop :=
  (∃ summands : Fin r → Tensor dims 𝕜, Decomposition A summands) ∧
    ∀ s : ℕ, s < r →
      ¬∃ summands : Fin s → Tensor dims 𝕜, Decomposition A summands

/-- Uniqueness of the unordered collection of actual summand tensors. -/
def UniqueSummands {d : ℕ} {dims : Fin d → ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (r : ℕ) (A : Tensor dims 𝕜) : Prop :=
  ∀ f g : Fin r → Tensor dims 𝕜,
    Decomposition A f → Decomposition A g →
      ∃ σ : Equiv.Perm (Fin r), ∀ i : Fin r, f i = g (σ i)

/-- The original generic *complex* identifiability condition, expressed by
a proper algebraic exceptional locus on the complex rank-`r` variety. A
single polynomial nonvanishing at some rank-`r` tensor defines a principal
Zariski-open subset contained in the generic identifiable locus. -/
def GenericComplexIdentifiable {d : ℕ} (dims : Fin d → ℕ) (r : ℕ) : Prop :=
  ∃ P : MvPolynomial (Entry dims) ℂ,
    (∃ A : Tensor dims ℂ, ExactRank r A ∧
      MvPolynomial.eval (fun ix => A ix) P ≠ 0) ∧
    ∀ A : Tensor dims ℂ, ExactRank r A →
      MvPolynomial.eval (fun ix => A ix) P ≠ 0 →
        UniqueSummands r A

/-- First variation of an outer product under arbitrary variations of its
factor vectors. This spans the tangent space to the nonzero rank-one cone. -/
def OuterVariation {d : ℕ} {dims : Fin d → ℕ}
    (factors variations : ∀ j : Fin d, Fin (dims j) → ℝ) :
    Tensor dims ℝ :=
  WithLp.toLp 2 (fun ix : Entry dims =>
    ∑ j : Fin d,
      ∏ k : Fin d,
        if k = j then variations k (ix k) else factors k (ix k))

/-- Intrinsic tangent directions at an actual rank-one summand. -/
def RankOneTangent {d : ℕ} {dims : Fin d → ℕ}
    (a v : Tensor dims ℝ) : Prop :=
  ∃ factors variations : ∀ j : Fin d, Fin (dims j) → ℝ,
    a = Outer factors ∧ v = OuterVariation factors variations

/-- The derivative of the addition map on the product of rank-one cones
is injective. Together with uniqueness, this describes the smooth
identifiable real rank-`r` locus. -/
def RegularDecomposition {d : ℕ} {dims : Fin d → ℕ} {r : ℕ}
    (f : Fin r → Tensor dims ℝ) : Prop :=
  ∀ v : Fin r → Tensor dims ℝ,
    (∀ i : Fin r, RankOneTangent (f i) (v i)) →
      (∑ i : Fin r, v i) = 0 → ∀ i : Fin r, v i = 0

/-- The concrete smooth identifiable locus `M_r` of real rank-`r`
tensors. A regular unique decomposition gives a local inverse branch of
the addition map, up to permutation of the summands. -/
def SmoothIdentifiable {d : ℕ} (dims : Fin d → ℕ) (r : ℕ)
    (A : Tensor dims ℝ) : Prop :=
  ExactRank r A ∧ UniqueSummands r A ∧
    ∃ f : Fin r → Tensor dims ℝ,
      Decomposition A f ∧ RegularDecomposition f

/-- The derivative of individual normalization `a ↦ a/‖a‖`, in ambient
Frobenius coordinates. It is applied to each summand before taking the
inverse-map operator norm. -/
noncomputable def NormalizeVariation {d : ℕ} {dims : Fin d → ℕ}
    (a v : Tensor dims ℝ) : Tensor dims ℝ :=
  (‖a‖⁻¹) • v - ((inner ℝ a v / ‖a‖ ^ 3)) • a

/-- Product Frobenius norm of the normalized first variations. -/
noncomputable def AngularProductVariation {d : ℕ} {dims : Fin d → ℕ} {r : ℕ}
    (f v : Fin r → Tensor dims ℝ) : EuclideanSpace ℝ (Fin r × Entry dims) :=
  WithLp.toLp 2 (fun ix : Fin r × Entry dims =>
    NormalizeVariation (f ix.1) (v ix.1) ix.2)

/-- The operator norm of `D(p^{×r} ∘ Ψ)` computed intrinsically: for every
tangent tuple `v`, the derivative of addition is `∑vᵢ`, and the derivative
of individual normalization is the numerator. On the regular locus the
addition derivative is injective, so these quotients are exactly the
inverse derivative's operator norm. The extended supremum handles any
singular exceptional points without falsely returning zero. -/
noncomputable def AngularCondition {d : ℕ} {dims : Fin d → ℕ} (r : ℕ)
    (A : Tensor dims ℝ) : ℝ≥0∞ :=
  sSup {z : ℝ≥0∞ | ∃ (f v : Fin r → Tensor dims ℝ),
    Decomposition A f ∧
    (∀ i : Fin r, RankOneTangent (f i) (v i)) ∧
    (∑ i : Fin r, v i) ≠ 0 ∧
    z = ENNReal.ofReal
      (‖AngularProductVariation f v‖ / ‖∑ i : Fin r, v i‖)}

/-- Dimension of the regular rank-`r` tensor manifold under generic
identifiability: each nonzero rank-one cone has dimension
`1 + ∑(nⱼ−1)`. -/
def ManifoldDimension {d : ℕ} (dims : Fin d → ℕ) (r : ℕ) : ℕ :=
  r * (1 + ∑ j : Fin d, (dims j - 1))

/-- Euclidean Hausdorff measure of the correct intrinsic dimension,
restricted to the concrete smooth identifiable locus. On a smooth
embedded manifold this is its induced Frobenius Riemannian volume. -/
noncomputable def InducedVolume {d : ℕ} (dims : Fin d → ℕ) (r : ℕ) :
    Measure (Tensor dims ℝ) :=
  (Measure.euclideanHausdorffMeasure (ManifoldDimension dims r)).restrict
    {A | SmoothIdentifiable dims r A}

noncomputable def GaussianWeight {d : ℕ} {dims : Fin d → ℕ}
    (A : Tensor dims ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(‖A‖ ^ 2) / 2))

/-- The actual normalizer of the volume-Gaussian law, not the law of
independent random rank-one summands. -/
noncomputable def Normalizer {d : ℕ} (dims : Fin d → ℕ) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ A : Tensor dims ℝ, GaussianWeight A ∂InducedVolume dims r

/-- Exact numerator of the angular expectation. -/
noncomputable def AngularIntegral {d : ℕ} (dims : Fin d → ℕ) (r : ℕ) : ℝ≥0∞ :=
  ∫⁻ A : Tensor dims ℝ,
    AngularCondition r A * GaussianWeight A ∂InducedVolume dims r

/-- Strict finite expectation under the normalized volume-Gaussian law. -/
def FiniteAngularMean {d : ℕ} (dims : Fin d → ℕ) (r : ℕ) : Prop :=
  0 < Normalizer dims r ∧ Normalizer dims r < ⊤ ∧
    AngularIntegral dims r / Normalizer dims r < ⊤

/-- Every admissible generically complex-identifiable format and rank
`r≥3` has finite mean angular inverse-derivative condition number. -/
def Target : Prop :=
  ∀ (d : ℕ) (dims : Fin d → ℕ) (r : ℕ),
    3 ≤ d → (∀ j : Fin d, 2 ≤ dims j) → 3 ≤ r →
      GenericComplexIdentifiable dims r → FiniteAngularMean dims r

#assert_statement Target
#assert_trust kernel Target
#print axioms Target

end NLA.ReviewedStatements.TR06
