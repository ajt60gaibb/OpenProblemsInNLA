import NLA.TR06.ClosedCone
import NLA.Proofs.TR06.AdditionPolynomialValues
import NLA.Proofs.TR06.LocalizedCharacterRelations
import NLA.Proofs.TR06.MonicCoefficientFamily
import NLA.Proofs.TR06.FiniteMonicProperness

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06
open NLA.TR06 NLA.TR06.Proposed

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Flatten the actual complex ordered summands into their actual coordinates. -/
def orderedComplexCoordinates : (Fin r → Tensor ℂ d n) ≃ₜ (Fin r × TensorIndex d n → ℂ) where
  toFun a iq := a iq.1 iq.2
  invFun z i := WithLp.toLp 2 (fun q => z (i, q))
  left_inv a := by funext i; ext q; rfl
  right_inv z := by funext iq; rfl
  continuous_toFun := by
    apply continuous_pi
    intro iq
    exact (PiLp.continuous_apply 2 _ iq.2).comp (continuous_apply iq.1)
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun q => continuous_apply (i, q))

/-- Genuine finite localization of actual addition excludes cancellation
escape above every compact base off its denominator. This includes every zero
summand and every branch of the complete closed rank-one product. -/
theorem complex_addition_preimages_compact (hd : 0 < d) (t : AdditionImage d n r)
    [Module.Finite (Localization.Away t)
      (Localization (Algebra.algebraMapSubmonoid (SegreSource d n r) (Submonoid.powers t)))]
    (K : Set (Tensor ℂ d n)) (hK : IsCompact K)
    (hKU : K ⊆ {A | additionBaseValue t A ≠ 0}) :
    IsCompact {a : Fin r → Tensor ℂ d n |
      a ∈ closedRankOneProduct ℂ d n r ∧ (∑ i, a i) ∈ K} := by
  classical
  obtain ⟨p, hp⟩ := addition_coordinate_monic_relations (d := d) (n := n) (r := r) t
  let N : ℕ := Finset.univ.sup (fun iq => (p iq).natDegree)
  let P : Tensor ℂ d n → (Fin r × TensorIndex d n) → Polynomial ℂ := fun A iq =>
    monicCoefficientPolynomial (p iq).natDegree (fun j => additionAwayValue t ((p iq).coeff j) A)
  apply compact_preimage_of_monic_coordinates orderedComplexCoordinates (fun a => ∑ i, a i)
    (continuous_finsetSum _ (fun i _ => continuous_apply i))
    (closedRankOneProduct ℂ d n r) (isClosed_closedRankOneProduct hd r) K hK P N
  · intro A _hA iq
    exact monicCoefficientPolynomial_monic _ _
  · intro A _hA iq
    exact (monicCoefficientPolynomial_natDegree_le _ _).trans
      (Finset.le_sup (f := fun iq => (p iq).natDegree) (Finset.mem_univ iq))
  · intro iq j
    apply continuousOn_monicCoefficientPolynomial_coeff
    intro ℓ _hℓ
    exact (continuousOn_additionAwayValue t ((p iq).coeff ℓ)).mono hKU
  · intro a ha hsum iq
    have harange : a ∈ Set.range (characterTuple (d := d) (n := n) (r := r)) := by
      rw [range_characterTuple hd]
      exact ha
    obtain ⟨f, hf⟩ := harange
    have hden : f t.val ≠ 0 := by
      have h := hKU hsum
      change additionBaseValue t (∑ i, a i) ≠ 0 at h
      rw [← hf, additionBaseValue_characterTuple] at h
      exact h
    have hφden : f.toRingHom (algebraMap (AdditionImage d n r) (SegreSource d n r) t) ≠ 0 := hden
    let α : Localization.Away t →+* ℂ := IsLocalization.Away.lift
      (g := f.toRingHom.comp (algebraMap (AdditionImage d n r) (SegreSource d n r))) t
      (isUnit_iff_ne_zero.mpr hφden)
    have hcoef (j : ℕ) : additionAwayValue t ((p iq).coeff j) (∑ i, a i) = α ((p iq).coeff j) := by
      rw [← hf, additionAwayValue_characterTuple]
      exact (away_lift_eq_coefficientValue t ((p iq).coeff j)
        (f.toRingHom.comp (algebraMap (AdditionImage d n r) (SegreSource d n r))) hφden).symm
    have hpoly : P (∑ i, a i) iq = (p iq).map α := by
      change monicCoefficientPolynomial (p iq).natDegree
        (fun j => additionAwayValue t ((p iq).coeff j) (∑ i, a i)) = _
      rw [show (fun j => additionAwayValue t ((p iq).coeff j) (∑ i, a i)) =
        (fun j => α ((p iq).coeff j)) from funext hcoef]
      exact monicCoefficientPolynomial_eq_map (p iq) (hp iq).1 α
    rw [hpoly]
    have hroot := localized_relation_isRoot t (segreCoordinate iq) (p iq) (hp iq).2 f.toRingHom hφden
    have hcoord : f.toRingHom (segreCoordinate iq) = orderedComplexCoordinates a iq := by
      change characterTuple f iq.1 iq.2 = a iq.1 iq.2
      rw [hf]
    simpa only [hcoord] using hroot

#print axioms complex_addition_preimages_compact
#assert_trust kernel complex_addition_preimages_compact

end NLA.Proofs.TR06
