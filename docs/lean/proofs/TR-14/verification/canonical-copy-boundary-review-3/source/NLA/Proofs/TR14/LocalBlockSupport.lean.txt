import NLA.Proofs.TR14.LocalCRTAlgebra
import NLA.Proofs.TR14.LocalUnitRoot
import NLA.Proofs.TR14.BlockPolynomialImage

/-! Actual primitive moment blocks retain whole truncated local factors.
Nonzero orthogonal idempotents therefore occupy distinct actual root supports. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The actual residue at the nilpotent root's zero coordinate. -/
def localResidue (ℓ : ℕ) (hℓ : 0 < ℓ) : LocalTruncated ℓ →+* ℂ :=
  AdjoinRoot.lift (RingHom.id ℂ) 0 (by simp [Nat.ne_of_gt hℓ])

theorem localResidue_eq_coeff (ℓ : ℕ) (hℓ : 0 < ℓ) (a : LocalTruncated ℓ) :
    localResidue ℓ hℓ a = localCoeffNat ℓ a 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [localResidue, AdjoinRoot.lift_mk, localCoeffNat_mk ℓ p 0 hℓ]
  simp

/-- An actual idempotent in a truncated local factor is zero or one;
derivative coordinates of a repeated root cannot form separate blocks. -/
theorem localTruncated_idempotent_eq_zero_or_one (ℓ : ℕ) (hℓ : 0 < ℓ)
    (e : LocalTruncated ℓ) (he : e * e = e) : e = 0 ∨ e = 1 := by
  let r := localResidue ℓ hℓ
  have hc : r e * r e = r e := by
    simpa only [map_mul] using congrArg r he
  have hprod : r e * (r e - 1) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rcases mul_eq_zero.mp hprod with hz | ho
  · left
    have hnil := local_nilpotent_of_const_zero ℓ hℓ e
      ((localResidue_eq_coeff ℓ hℓ e).symm.trans hz)
    exact (show IsIdempotentElem e from he).eq_zero_of_isNilpotent hnil
  · right
    have hres : r e = 1 := sub_eq_zero.mp ho
    have hconst : localCoeffNat ℓ (1 - e) 0 = 0 := by
      rw [← localResidue_eq_coeff ℓ hℓ (1 - e)]
      change r (1 - e) = 0
      rw [map_sub, map_one, hres, sub_self]
    have hnil := local_nilpotent_of_const_zero ℓ hℓ (1 - e) hconst
    have hzero : 1 - e = 0 :=
      (show IsIdempotentElem e from he).one_sub.eq_zero_of_isNilpotent hnil
    exact (sub_eq_zero.mp hzero).symm

/-- Each component of an actual quotient idempotent is the zero or identity
of the whole local factor with its original positive multiplicity. -/
theorem localCRT_idempotent_eq_zero_or_one (g : ℂ[X]) (hg : g.Monic)
    (e : AdjoinRoot g) (he : e * e = e) (α : LocalRootIndex g) :
    localCRTEquiv g hg e α = 0 ∨ localCRTEquiv g hg e α = 1 := by
  apply localTruncated_idempotent_eq_zero_or_one _ (localRootMultiplicity_pos g α)
  have h := congrArg (fun a : AdjoinRoot g => localCRTEquiv g hg a α) he
  simpa only [map_mul, Pi.mul_apply] using h

/-- Exact finite support of the actual quotient element under the CRT. -/
def idempotentRootSupport (g : ℂ[X]) (hg : g.Monic) (e : AdjoinRoot g) :
    Finset (LocalRootIndex g) := by
  classical
  exact Finset.univ.filter (fun α => localCRTEquiv g hg e α ≠ 0)

/-- Every nonzero quotient element occupies at least one actual local factor. -/
theorem idempotentRootSupport_nonempty (g : ℂ[X]) (hg : g.Monic)
    (e : AdjoinRoot g) (hne : e ≠ 0) : (idempotentRootSupport g hg e).Nonempty := by
  classical
  by_contra hn
  have hall (α : LocalRootIndex g) : localCRTEquiv g hg e α = 0 := by
    by_contra hz
    exact hn ⟨α, by simp [idempotentRootSupport, hz]⟩
  apply hne
  apply (localCRTEquiv g hg).injective
  ext α
  simpa only [map_zero, Pi.zero_apply] using hall α

/-- Membership in an idempotent's support means exactly the identity on
that entire truncated local factor. -/
theorem idempotentRootSupport_eq_one (g : ℂ[X]) (hg : g.Monic)
    (e : AdjoinRoot g) (he : e * e = e) (α : LocalRootIndex g)
    (hα : α ∈ idempotentRootSupport g hg e) : localCRTEquiv g hg e α = 1 := by
  classical
  have hn : localCRTEquiv g hg e α ≠ 0 := (Finset.mem_filter.mp hα).2
  exact (localCRT_idempotent_eq_zero_or_one g hg e he α).resolve_left hn

/-- Distinct nonzero orthogonal quotient idempotents require distinct whole
local root factors. This is the actual support-count bound t≤s. -/
theorem orthogonal_idempotent_card_le_rootSupport {t : ℕ}
    (g : ℂ[X]) (hg : g.Monic) (e : Fin t → AdjoinRoot g)
    (hne : ∀ j, e j ≠ 0) (hidem : ∀ j, e j * e j = e j)
    (horth : ∀ i j, i ≠ j → e i * e j = 0) :
    t ≤ (localRootSupport g).card := by
  classical
  choose f hf using fun j => idempotentRootSupport_nonempty g hg (e j) (hne j)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hneij
    have hi := idempotentRootSupport_eq_one g hg (e i) (hidem i) (f i) (hf i)
    have hj := idempotentRootSupport_eq_one g hg (e j) (hidem j) (f j) (hf j)
    have hj' : localCRTEquiv g hg (e j) (f i) = 1 := hij.symm ▸ hj
    have hprod := congrArg (fun a : AdjoinRoot g => localCRTEquiv g hg a (f i))
      (horth i j hneij)
    simp only [map_mul, Pi.mul_apply, map_zero, Pi.zero_apply, hi, hj', one_mul] at hprod
    have h := congrArg (localResidue _ (localRootMultiplicity_pos g (f i))) hprod
    have h10 : (1 : ℂ) = 0 := by simpa only [map_one, map_zero] using h
    exact one_ne_zero h10
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- A nonzero actual quotient multiplier has positive actual block dimension. -/
theorem blockIdeal_finrank_pos (g : ℂ[X]) (hg : g.Monic)
    (e : AdjoinRoot g) (hne : e ≠ 0) : 0 < Module.finrank ℂ (blockIdeal g e) := by
  let : Module.Finite ℂ (AdjoinRoot g) := hg.finite_adjoinRoot
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨e, ⟨1, by simp⟩⟩, ?_⟩
  intro hzero
  exact hne (congrArg (fun a : blockIdeal g e => (a : AdjoinRoot g)) hzero)

#assert_trust kernel localTruncated_idempotent_eq_zero_or_one
#assert_trust kernel localCRT_idempotent_eq_zero_or_one
#assert_trust kernel idempotentRootSupport_nonempty
#assert_trust kernel orthogonal_idempotent_card_le_rootSupport
#assert_trust kernel blockIdeal_finrank_pos
#print axioms orthogonal_idempotent_card_le_rootSupport
#print axioms blockIdeal_finrank_pos

end
end NLA.Proofs.TR14
