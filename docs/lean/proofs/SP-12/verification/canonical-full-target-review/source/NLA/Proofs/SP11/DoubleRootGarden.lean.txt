import NLA.Proofs.SP11.GardenTree
import NLA.Proofs.SP11.GardenColors
import NLA.Proofs.SP11.LSSGarden

/-!
# Paired finite gardens and their actual node occurrences

The two root outputs share one conduit color. Node occurrences remain distinct
in the finite product, but every coefficient is indexed by its original vertex
label and coordinate subset, never by an occurrence-specific variable.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11
namespace GardenTree

variable {V R : Type*} {arity : V → ℕ} [CommRing R] {d : ℕ}

/-- A tree's color choices below its root; the root's output color is omitted. -/
def BelowColoring (d : ℕ) : GardenTree V arity → Type
  | .node _ children => (s : Fin _) → Coloring d (children s)

noncomputable instance belowColoringFintype (d : ℕ) (t : GardenTree V arity) :
    Fintype (BelowColoring d t) := by
  cases t with
  | node v children =>
    change Fintype ((s : Fin (arity v)) → Coloring d (children s))
    infer_instance

/-- Restore one selected root color to the colors below it. -/
def withRootColor : (t : GardenTree V arity) → Fin d → BelowColoring d t → Coloring d t
  | .node _ _, q, c => (q, c)

@[simp] theorem rootColor_withRootColor (t : GardenTree V arity) (q : Fin d)
    (c : BelowColoring d t) : rootColor (withRootColor t q c) = q := by cases t; rfl

/-- One cap-conduit color and all remaining choices in the two trees. -/
abbrev DoubleColoring (d : ℕ) (t u : GardenTree V arity) :=
  Fin d × BelowColoring d t × BelowColoring d u

/-- Coloring of the left tree induced by the shared cap color. -/
def leftColoring {t u : GardenTree V arity} (c : DoubleColoring d t u) : Coloring d t :=
  withRootColor t c.1 c.2.1

/-- Coloring of the right tree induced by that same cap color. -/
def rightColoring {t u : GardenTree V arity} (c : DoubleColoring d t u) : Coloring d u :=
  withRootColor u c.1 c.2.2

/-- An exact finite occurrence index: one root occurrence and all child occurrences. -/
def Occurrence : GardenTree V arity → Type
  | .node _ children => Unit ⊕ ((s : Fin _) × Occurrence (children s))

noncomputable instance occurrenceFintype (t : GardenTree V arity) :
    Fintype (Occurrence t) := by
  induction t with
  | node v children ih =>
    change Fintype (Unit ⊕ ((s : Fin (arity v)) × Occurrence (children s)))
    letI : (s : Fin (arity v)) → Fintype (Occurrence (children s)) := ih
    infer_instance

/-- The original label at an occurrence. Different occurrences may have the same label. -/
def occurrenceLabel : (t : GardenTree V arity) → Occurrence t → V
  | .node v _, .inl _ => v
  | .node _ children, .inr ⟨s, o⟩ => occurrenceLabel (children s) o

/-- All conduit colors incident to an actual node, in the first-output convention. -/
def occurrenceColors : (t : GardenTree V arity) → (c : Coloring d t) →
    (o : Occurrence t) → Fin (arity (occurrenceLabel t o) + 1) → Fin d
  | .node _ _, c, .inl _ => Matrix.vecCons c.1 (fun s => rootColor (c.2 s))
  | .node _ children, c, .inr ⟨s, o⟩ => occurrenceColors (children s) (c.2 s) o

/-- The actual shared tensor coefficient contributed at one node occurrence. -/
noncomputable def occurrenceFactor
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R)
    (t : GardenTree V arity) (c : Coloring d t) (o : Occurrence t) : R :=
  a (occurrenceLabel t o) (fun s => Pi.single (occurrenceColors t c o s) 1)

/-- The recursive weight counts every actual node occurrence exactly once. -/
theorem weight_eq_prod_occurrenceFactor
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R)
    (t : GardenTree V arity) (c : Coloring d t) :
    weight a t c = ∏ o : Occurrence t, occurrenceFactor a t c o := by
  classical
  induction t with
  | node v children ih =>
    rcases c with ⟨q, cs⟩
    change _ = ∏ o : Unit ⊕ ((s : Fin (arity v)) × Occurrence (children s)), _
    simp only [Fintype.prod_sum_type, Fintype.prod_sigma, Fintype.prod_unique,
      occurrenceFactor, occurrenceLabel, occurrenceColors, weight]
    apply congrArg₂ (· * ·)
    · apply congrArg (a v)
      funext i
      cases i using Fin.cases <;> rfl
    · apply Finset.prod_congr rfl
      intro s _
      exact ih s (cs s)

/-- Scalar weight of a double-root coloring; its one cap index is not summed twice. -/
noncomputable def doubleWeight
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R)
    (t u : GardenTree V arity) (c : DoubleColoring d t u) : R :=
  weight a t (leftColoring c) * weight a u (rightColoring c)

/-- The real or polynomial bilinear pairing is the exact sum over shared-cap
colorings. No terms are discarded and identical shared-variable monomials may occur. -/
theorem dotProduct_eq_sum_doubleWeight
    (a : (v : V) → (CoordinateVector R d) [⋀^Fin (arity v + 1)]→ₗ[R] R)
    (t u : GardenTree V arity) :
    value a t ⬝ᵥ value a u = ∑ c : DoubleColoring d t u, doubleWeight a t u c := by
  classical
  rw [value_eq_sum_weight, value_eq_sum_weight]
  simp_rw [sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul]
  cases t with
  | node v children =>
    cases u with
    | node w descendants =>
      simp only [Coloring, Fintype.sum_prod_type, rootColor, doubleWeight,
        leftColoring, rightColoring, withRootColor, BelowColoring]
      simp [Pi.single_apply, smul_eq_mul, mul_comm]
      apply Finset.sum_congr rfl
      intro q _
      exact (Fintype.sum_prod_type (fun c =>
        weight a (node v children) (q, c.1) *
          weight a (node w descendants) (q, c.2))).symm

/-- Only original labels and their increasing coordinate subsets name variables. -/
abbrev SharedVariable (V : Type*) (arity : V → ℕ) (d : ℕ) :=
  (v : V) × CoordinateSubset d (arity v + 1)

/-- The same coefficient family is used at every occurrence of a label. -/
noncomputable def sharedVertexForms (R : Type*) [CommRing R] (V : Type*)
    (arity : V → ℕ) (d : ℕ) :
    (v : V) → (CoordinateVector (MvPolynomial (SharedVariable V arity d) R) d)
      [⋀^Fin (arity v + 1)]→ₗ[MvPolynomial (SharedVariable V arity d) R]
        MvPolynomial (SharedVariable V arity d) R :=
  fun v => polynomialAlternatingForm (fun s => Sigma.mk v s)

/-- The exact shared-variable exponent at one occurrence. -/
noncomputable def occurrenceExponent (t : GardenTree V arity) (c : Coloring d t)
    (o : Occurrence t) : SharedVariable V arity d →₀ ℕ :=
  colorExponent (fun s => Sigma.mk (occurrenceLabel t o) s) (occurrenceColors t c o)

/-- Count every actual occurrence, including repeated copies of the same label. -/
noncomputable def coloringExponent (t : GardenTree V arity) (c : Coloring d t) :
    SharedVariable V arity d →₀ ℕ := ∑ o, occurrenceExponent t c o

/-- Multiply the actual alternating sign or zero at every node occurrence. -/
noncomputable def coloringSign (R : Type*) [CommRing R]
    (t : GardenTree V arity) (c : Coloring d t) : R :=
  ∏ o : Occurrence t, colorSign R (occurrenceColors t c o)

/-- A finite product of literal monomials adds the exponents and multiplies coefficients. -/
theorem prod_monomial {ι σ : Type*} (s : Finset ι) (e : ι → σ →₀ ℕ) (c : ι → R) :
    (∏ i ∈ s, MvPolynomial.monomial (e i) (c i)) =
      MvPolynomial.monomial (∑ i ∈ s, e i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, MvPolynomial.monomial_mul]

/-- Every full-coloring weight is its exact occurrence-count monomial with its sign. -/
theorem weight_sharedVertexForms_eq_monomial (t : GardenTree V arity) (c : Coloring d t) :
    weight (sharedVertexForms R V arity d) t c =
      MvPolynomial.monomial (coloringExponent t c) (coloringSign R t c) := by
  classical
  rw [weight_eq_prod_occurrenceFactor]
  have hf (o : Occurrence t) :
      occurrenceFactor (sharedVertexForms R V arity d) t c o =
        MvPolynomial.monomial (occurrenceExponent t c o)
          (colorSign R (occurrenceColors t c o)) :=
    polynomialAlternatingForm_basis_eq_monomial _ _
  simp_rw [hf]
  exact prod_monomial Finset.univ _ _

/-- Actual nodes of both trees. The shared cap is a conduit, not an extra node. -/
abbrev DoubleOccurrence (t u : GardenTree V arity) := Occurrence t ⊕ Occurrence u

/-- Sum the actual label/subset exponent at every node of the paired tree. -/
noncomputable def doubleColoringExponent (t u : GardenTree V arity)
    (c : DoubleColoring d t u) : SharedVariable V arity d →₀ ℕ :=
  ∑ o : DoubleOccurrence t u,
    match o with
    | .inl o => occurrenceExponent t (leftColoring c) o
    | .inr o => occurrenceExponent u (rightColoring c) o

/-- The product of alternating signs, including zero at any repeated-color node. -/
noncomputable def doubleColoringSign (R : Type*) [CommRing R]
    (t u : GardenTree V arity) (c : DoubleColoring d t u) : R :=
  ∏ o : DoubleOccurrence t u,
    match o with
    | .inl o => colorSign R (occurrenceColors t (leftColoring c) o)
    | .inr o => colorSign R (occurrenceColors u (rightColoring c) o)

/-- The literal paired-coloring weight is one monomial, with shared variables. -/
theorem doubleWeight_sharedVertexForms_eq_monomial
    (t u : GardenTree V arity) (c : DoubleColoring d t u) :
    doubleWeight (sharedVertexForms R V arity d) t u c =
      MvPolynomial.monomial (doubleColoringExponent t u c) (doubleColoringSign R t u c) := by
  classical
  rw [doubleWeight, weight_sharedVertexForms_eq_monomial, weight_sharedVertexForms_eq_monomial,
    MvPolynomial.monomial_mul]
  simp only [doubleColoringExponent, doubleColoringSign, Fintype.sum_sum_type,
    Fintype.prod_sum_type, coloringExponent, coloringSign]

/-- Exact signed monomial expansion for a pair of actual shared-form gardens. -/
theorem dotProduct_sharedVertexForms_eq_sum_monomial (t u : GardenTree V arity) :
    value (sharedVertexForms R V arity d) t ⬝ᵥ value (sharedVertexForms R V arity d) u =
      ∑ c : DoubleColoring d t u,
        MvPolynomial.monomial (doubleColoringExponent t u c) (doubleColoringSign R t u c) := by
  rw [dotProduct_eq_sum_doubleWeight]
  apply Finset.sum_congr rfl
  intro c _
  exact doubleWeight_sharedVertexForms_eq_monomial _ _ _

#assert_trust kernel weight_eq_prod_occurrenceFactor
#assert_trust kernel dotProduct_eq_sum_doubleWeight
#print axioms dotProduct_eq_sum_doubleWeight

end GardenTree

/-- The actual LSS Gram entry, expanded over finite paired occurrence colorings.
The exponent counts nodes at original Sigma(vertex,subset) variables exactly. -/
theorem polynomialGram_eq_sum_signedGardenMonomial {n d : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n) :
    polynomialGram (polynomialLSS G d) i j =
      ∑ c : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j),
        MvPolynomial.monomial
          (GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) c)
          (GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) c) := by
  change uniformLSS G (universalVertexForms G) i ⬝ᵥ
    uniformLSS G (universalVertexForms G) j = _
  rw [← lssGarden_value G (universalVertexForms G) i,
    ← lssGarden_value G (universalVertexForms G) j]
  exact GardenTree.dotProduct_sharedVertexForms_eq_sum_monomial _ _

#assert_trust kernel GardenTree.weight_sharedVertexForms_eq_monomial
#assert_trust kernel GardenTree.doubleWeight_sharedVertexForms_eq_monomial
#assert_trust kernel polynomialGram_eq_sum_signedGardenMonomial
#print axioms polynomialGram_eq_sum_signedGardenMonomial

end NLA.Proofs.SP11
