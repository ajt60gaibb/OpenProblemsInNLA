import NLA.Proofs.TR14.FrobeniusMinimal
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The finite Frobenius-duality step used by the binary upper construction.
No quotient or tensor-rank conclusion is assumed here. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℂ A] [FiniteDimensional ℂ A]

/-- Multiplication transports an algebra element to a functional through a
fixed linear functional `τ`. -/
def frobeniusRepresenterMap (τ : A →ₗ[ℂ] ℂ) :
    A →ₗ[ℂ] (A →ₗ[ℂ] ℂ) where
  toFun u := {
    toFun := fun a => τ (u * a)
    map_add' := by
      intro a b
      simp only [mul_add, map_add]
    map_smul' := by
      intro c a
      change τ (u * (c • a)) = c • τ (u * a)
      simp only [mul_smul_comm, map_smul]
  }
  map_add' := by
    intro u v
    ext a
    change τ ((u + v) * a) = τ (u * a) + τ (v * a)
    simp only [add_mul, map_add]
  map_smul' := by
    intro c u
    ext a
    change τ ((c • u) * a) = c • τ (u * a)
    simp only [smul_mul_assoc, map_smul]

/-- Every functional has a unique multiplier representation through a
nondegenerate Frobenius functional. -/
theorem frobenius_representer_exists_unique (τ : A →ₗ[ℂ] ℂ)
    (hτ : ∀ a : A, (∀ b : A, τ (a * b) = 0) → a = 0)
    (L : A →ₗ[ℂ] ℂ) :
    ∃! u : A, ∀ a : A, L a = τ (u * a) := by
  let Φ := frobeniusRepresenterMap τ
  have hΦinj : Function.Injective Φ := by
    intro u v huv
    have hzero : Φ (u - v) = 0 := by
      rw [map_sub, huv, sub_self]
    have huv0 : u - v = 0 := hτ (u - v) (by
      intro a
      have ha := congrArg (fun f : A →ₗ[ℂ] ℂ => f a) hzero
      simpa [Φ, frobeniusRepresenterMap] using ha)
    exact sub_eq_zero.mp huv0
  have hdim : Module.finrank ℂ A = Module.finrank ℂ (A →ₗ[ℂ] ℂ) :=
    (Subspace.dual_finrank_eq (K := ℂ) (V := A)).symm
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦinj
  obtain ⟨u, hu⟩ := hΦsurj L
  refine ⟨u, ?_, ?_⟩
  · intro a
    exact (congrArg (fun f : A →ₗ[ℂ] ℂ => f a) hu).symm
  · intro v hv
    apply hΦinj
    ext a
    exact (hv a).symm.trans
      (congrArg (fun f : A →ₗ[ℂ] ℂ => f a) hu).symm

/-- If the represented functional is also Frobenius, its representing
element is a unit. -/
theorem frobenius_representer_isUnit (τ L : A →ₗ[ℂ] ℂ)
    (hL : ∀ a : A, (∀ b : A, L (a * b) = 0) → a = 0)
    (u : A) (hu : ∀ a : A, L a = τ (u * a)) : IsUnit u := by
  have hinj : Function.Injective (LinearMap.mulLeft ℂ u) := by
    intro a b hab
    have hab0 : u * (a - b) = 0 := by
      change u * a = u * b at hab
      rw [mul_sub, hab, sub_self]
    apply sub_eq_zero.mp
    apply hL (a - b)
    intro x
    rw [hu ((a - b) * x), ← mul_assoc, hab0, zero_mul, map_zero]
  obtain ⟨v, hv⟩ :=
    (LinearMap.mulLeft ℂ u).surjective_of_injective hinj 1
  change u * v = 1 at hv
  exact isUnit_iff_exists_inv.mpr ⟨v, hv⟩

#assert_trust kernel frobeniusRepresenterMap
#assert_trust kernel frobenius_representer_exists_unique
#assert_trust kernel frobenius_representer_isUnit
#print axioms frobenius_representer_isUnit

end
end NLA.Proofs.TR14
