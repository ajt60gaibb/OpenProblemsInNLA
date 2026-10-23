import NLA.Proofs.TR14.LocalCRTAlgebra
import Mathlib.LinearAlgebra.Pi

/-!
Supported local functionals under the exact complex-algebra CRT. The
insertion map is linear, not generally unital. Global Frobenius passes to
each local component through componentwise multiplication.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

private abbrev LocalCRTPi (g : Polynomial ℂ) :=
  ∀ α : LocalRootIndex g, LocalTruncated (localRootMultiplicity g α)

/-- Insert one local class at its root coordinate and zero elsewhere. -/
def localCRTInsertion (g : Polynomial ℂ) (α : LocalRootIndex g) :
    LocalTruncated (localRootMultiplicity g α) →ₗ[ℂ] LocalCRTPi g := by
  classical
  exact LinearMap.single ℂ
    (fun β : LocalRootIndex g => LocalTruncated (localRootMultiplicity g β)) α

theorem localCRTInsertion_mul (g : Polynomial ℂ) (α : LocalRootIndex g)
    (a : LocalTruncated (localRootMultiplicity g α)) (v : LocalCRTPi g) :
    localCRTInsertion g α a * v =
      localCRTInsertion g α (a * v α) := by
  classical
  ext β
  by_cases h : β = α
  · subst β
    simp [localCRTInsertion]
  · simp [localCRTInsertion, h]

/-- The genuine local functional obtained by supported insertion through CRT. -/
def localCRTComponent (g : Polynomial ℂ) (hg : g.Monic)
    (Λ : AdjoinRoot g →ₗ[ℂ] ℂ) (α : LocalRootIndex g) :
    LocalTruncated (localRootMultiplicity g α) →ₗ[ℂ] ℂ :=
  Λ.comp ((localCRTEquiv g hg).symm.toLinearMap.comp (localCRTInsertion g α))

theorem localCRTComponent_apply (g : Polynomial ℂ) (hg : g.Monic)
    (Λ : AdjoinRoot g →ₗ[ℂ] ℂ) (α : LocalRootIndex g)
    (a : LocalTruncated (localRootMultiplicity g α)) :
    localCRTComponent g hg Λ α a =
      Λ ((localCRTEquiv g hg).symm (localCRTInsertion g α a)) :=
  rfl

/-- Exact sum of all supported local functionals, valid for every quotient class. -/
theorem localCRTComponent_sum (g : Polynomial ℂ) (hg : g.Monic)
    (Λ : AdjoinRoot g →ₗ[ℂ] ℂ) (x : AdjoinRoot g) :
    Λ x = ∑ α : LocalRootIndex g,
      localCRTComponent g hg Λ α (localCRTEquiv g hg x α) := by
  classical
  let E := localCRTEquiv g hg
  have hsum (v : LocalCRTPi g) :
      (∑ α : LocalRootIndex g, localCRTInsertion g α (v α)) = v := by
    simpa only [localCRTInsertion, LinearMap.single_apply] using
      (LinearMap.sum_single_apply
        (fun β : LocalRootIndex g => LocalTruncated (localRootMultiplicity g β)) v)
  calc
    Λ x = Λ (E.symm (E x)) := by rw [E.symm_apply_apply]
    _ = Λ (E.symm (∑ α : LocalRootIndex g,
          localCRTInsertion g α ((E x) α))) := by rw [hsum]
    _ = ∑ α : LocalRootIndex g,
          Λ (E.symm (localCRTInsertion g α ((E x) α))) := by simp
    _ = ∑ α : LocalRootIndex g,
          localCRTComponent g hg Λ α (E x α) := rfl

/-- Global Frobenius nondegeneracy implies genuine Frobenius in every
truncated local factor. -/
theorem localCRTComponent_frobenius (g : Polynomial ℂ) (hg : g.Monic)
    (Λ : AdjoinRoot g →ₗ[ℂ] ℂ)
    (hGF : ∀ x : AdjoinRoot g,
      (∀ y : AdjoinRoot g, Λ (x * y) = 0) → x = 0)
    (α : LocalRootIndex g) (a : LocalTruncated (localRootMultiplicity g α))
    (ha : ∀ b : LocalTruncated (localRootMultiplicity g α),
      localCRTComponent g hg Λ α (a * b) = 0) : a = 0 := by
  classical
  let E := localCRTEquiv g hg
  let u := localCRTInsertion g α a
  have hu : E.symm u = 0 := hGF _ (by
    intro y
    calc
      Λ (E.symm u * y) = Λ (E.symm (u * E y)) := by simp
      _ = Λ (E.symm (localCRTInsertion g α (a * E y α))) := by
        rw [localCRTInsertion_mul]
      _ = localCRTComponent g hg Λ α (a * E y α) := rfl
      _ = 0 := ha _)
  have hu' : u = 0 := by
    have h := congrArg E hu
    simpa using h
  have hα := congrArg (fun v : LocalCRTPi g => v α) hu'
  simpa [u, localCRTInsertion] using hα

#assert_trust kernel localCRTInsertion_mul
#assert_trust kernel localCRTComponent_sum
#assert_trust kernel localCRTComponent_frobenius
#print axioms localCRTComponent_frobenius

end
end NLA.Proofs.TR14
