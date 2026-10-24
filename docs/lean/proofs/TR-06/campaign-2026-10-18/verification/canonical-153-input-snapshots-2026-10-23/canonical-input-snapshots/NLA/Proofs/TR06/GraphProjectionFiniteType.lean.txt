/-
Copyright (c) 2026. Released under Apache 2.0 license.
Actual polynomial-coordinate actions and their pointwise quasi-finiteness.
-/
import NLA.Proofs.TR06.GraphQuasiFinite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.GraphProjection
attribute [local instance] RingHom.ker_isPrime

/-- The point-derivation criterion for the actual action of the selected
polynomial-coordinate ring on a genuine finite-type complex algebra. -/
theorem quasiFiniteAt_aeval_of_point_derivations
    {S ι : Type*} [CommRing S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    (f : ι → S) (χ : S →ₐ[ℂ] ℂ)
    (hzero : ∀ δ : S →ₗ[ℂ] ℂ,
      (∀ a b, δ (a*b) = χ a*δ b + χ b*δ a) →
      (∀ j, δ (f j)=0) → δ=0) :
    (MvPolynomial.aeval f : MvPolynomial ι ℂ →ₐ[ℂ] S).toRingHom.QuasiFiniteAt (RingHom.ker χ.toRingHom) := by
  let R := MvPolynomial ι ℂ
  let φ : R →ₐ[ℂ] S := MvPolynomial.aeval f
  let : Algebra R S := φ.toRingHom.toAlgebra
  let : IsScalarTower ℂ R S := IsScalarTower.of_algebraMap_eq
    (fun c => (φ.commutes c).symm)
  let : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R S
  let ψ : R →ₐ[ℂ] ℂ := χ.comp φ
  have hcompat : χ.comp (IsScalarTower.toAlgHom ℂ R S) = ψ := by rfl
  apply GraphQuasiFinite.quasiFiniteAt_of_point_derivations χ ψ hcompat
  intro δ hmul hbase
  apply hzero δ hmul
  intro j
  have h := hbase (MvPolynomial.X j)
  change δ (φ (MvPolynomial.X j)) = 0 at h
  have hX : φ (MvPolynomial.X j) = f j := MvPolynomial.aeval_X f j
  rw [hX] at h
  exact h

#print axioms quasiFiniteAt_aeval_of_point_derivations
#assert_trust kernel quasiFiniteAt_aeval_of_point_derivations
end NLA.Proofs.TR06.GraphProjection
