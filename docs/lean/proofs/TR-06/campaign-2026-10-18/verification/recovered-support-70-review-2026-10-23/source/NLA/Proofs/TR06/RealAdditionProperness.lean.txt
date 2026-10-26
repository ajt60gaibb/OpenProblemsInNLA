import NLA.Proofs.TR06.AdditionProperness
import NLA.TR06.Complexification
import NLA.TR06.RegularChartDefinitions
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06
open NLA.TR06 NLA.TR06.Proposed

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def complexifyLinear : Tensor ℝ d n →ₗ[ℝ] Tensor ℂ d n where
  toFun := complexify
  map_add' := complexify_add
  map_smul' c A := by ext q; simp [complexify]

theorem isClosedEmbedding_complexify :
    Topology.IsClosedEmbedding (complexify (d := d) (n := n)) := by
  change Topology.IsClosedEmbedding (complexifyLinear (d := d) (n := n))
  exact LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr complexify_injective)

def orderedComplexifyLinear : (Fin r → Tensor ℝ d n) →ₗ[ℝ] (Fin r → Tensor ℂ d n) where
  toFun a i := complexify (a i)
  map_add' a b := by funext i; exact complexify_add _ _
  map_smul' c a := by funext i; exact (complexifyLinear (d := d) (n := n)).map_smul c (a i)

theorem isClosedEmbedding_orderedComplexify :
    Topology.IsClosedEmbedding (fun a : Fin r → Tensor ℝ d n => fun i => complexify (a i)) := by
  change Topology.IsClosedEmbedding (orderedComplexifyLinear (d := d) (n := n) (r := r))
  apply LinearMap.isClosedEmbedding_of_injective
  apply LinearMap.ker_eq_bot.mpr
  intro a b hab
  funext i
  exact complexify_injective (congrFun hab i)

/-- The actual nonvanishing ambient polynomial open, restricted to real tensors. -/
def realAdditionGoodSet (t : AdditionImage d n r) : Set (Tensor ℝ d n) :=
  {A | additionBaseValue t (complexify A) ≠ 0}

theorem isOpen_realAdditionGoodSet (t : AdditionImage d n r) :
    IsOpen (realAdditionGoodSet t) :=
  isOpen_ne_fun ((continuous_additionBaseValue t).comp isClosedEmbedding_complexify.continuous)
    continuous_const

/-- Compactness for complete REAL addition preimages follows from proved
complex compactness and the actual closed real embedding. No real tensor is
silently identified with an arbitrary complex tensor. -/
theorem real_addition_preimages_compact (hd : 0 < d) (t : AdditionImage d n r)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))] :
    CompactAdditionPreimagesOn (r := r) (realAdditionGoodSet t) := by
  intro K hK hKU
  have hKC : IsCompact (complexify '' K) := hK.image isClosedEmbedding_complexify.continuous
  have hKCU : complexify '' K ⊆ {A | additionBaseValue t A ≠ 0} := by
    rintro _ ⟨A, hA, rfl⟩
    exact hKU hA
  have hcomplex := complex_addition_preimages_compact hd t (complexify '' K) hKC hKCU
  have hpre := isClosedEmbedding_orderedComplexify.isCompact_preimage hcomplex
  have hclosed : IsClosed {a : Fin r → Tensor ℝ d n |
      a ∈ closedRankOneProduct ℝ d n r ∧ (∑ i, a i) ∈ K} :=
    (isClosed_closedRankOneProduct hd r).inter
      (hK.isClosed.preimage (continuous_finsetSum _ (fun i _ => continuous_apply i)))
  apply hpre.of_isClosed_subset hclosed
  intro a ha
  constructor
  · intro i
    rcases ha.1 i with hz | hRankOne
    · left
      change complexify (a i) = 0
      rw [hz, complexify_zero]
    · exact Or.inr (complexify_rankOne hRankOne)
  · exact ⟨∑ i, a i, ha.2, complexify_sum Finset.univ a⟩

/-- The original generic-complex identifiability hypothesis now supplies an
actual open good base on which the COMPLETE real addition map is proper. The
nonzero denominator and finite-module structure are conclusions, not oracles. -/
theorem generic_identifiability_real_addition_proper (hd : 0 < d)
    (hgen : GenericComplexIdentifiable d n r) :
    ∃ t : AdditionImage d n r, t ≠ 0 ∧ IsOpen (realAdditionGoodSet t) ∧
      CompactAdditionPreimagesOn (r := r) (realAdditionGoodSet t) := by
  rcases hgen with ⟨p, ⟨A, hArank, hpA⟩, hident⟩
  obtain ⟨_hqf, t, ht, hfinite⟩ := addition_finite_localization d n r hd
    ⟨A, hArank, hident A hArank hpA⟩
  let : Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t))) := hfinite
  exact ⟨t, ht, isOpen_realAdditionGoodSet t, real_addition_preimages_compact hd t⟩

/-- The chosen ambient denominator has a genuinely nonzero pullback to the
actual integral source algebra. -/
theorem additionRepresentative_pullback_ne_zero {t : AdditionImage d n r} (ht : t ≠ 0) :
    additionAlgebraHom d n r (additionRepresentative t) ≠ 0 := by
  intro hzero
  apply ht
  apply Subtype.ext
  change t.val = 0
  rw [← additionRepresentative_spec t, hzero]

/-- Polynomial form of the genuine proper good base. The source pullback is
nonzero; homogeneity of this polynomial is not asserted or required. -/
theorem generic_identifiability_real_addition_proper_polynomial (hd : 0 < d)
    (hgen : GenericComplexIdentifiable d n r) :
    ∃ q : MvPolynomial (TensorIndex d n) ℂ,
      additionAlgebraHom d n r q ≠ 0 ∧
      IsOpen {A : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify A k) q ≠ 0} ∧
      CompactAdditionPreimagesOn (r := r)
        {A : Tensor ℝ d n | MvPolynomial.eval (fun k => complexify A k) q ≠ 0} := by
  obtain ⟨t, ht, hopen, hproper⟩ := generic_identifiability_real_addition_proper hd hgen
  exact ⟨additionRepresentative t, additionRepresentative_pullback_ne_zero ht, hopen, hproper⟩

#print axioms additionRepresentative_pullback_ne_zero
#print axioms generic_identifiability_real_addition_proper_polynomial
#assert_trust kernel additionRepresentative_pullback_ne_zero
#assert_trust kernel generic_identifiability_real_addition_proper_polynomial

#print axioms isClosedEmbedding_complexify
#print axioms isClosedEmbedding_orderedComplexify
#print axioms isOpen_realAdditionGoodSet
#print axioms real_addition_preimages_compact
#print axioms generic_identifiability_real_addition_proper
#assert_trust kernel isClosedEmbedding_complexify
#assert_trust kernel isClosedEmbedding_orderedComplexify
#assert_trust kernel isOpen_realAdditionGoodSet
#assert_trust kernel real_addition_preimages_compact
#assert_trust kernel generic_identifiability_real_addition_proper

end NLA.Proofs.TR06
