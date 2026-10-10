import NLA.Proofs.TR14.LocalCRTRootData

/-!
Translation of a single primary root factor `(X-α)^ℓ` to the exact
truncated local algebra `ℂ[z]/z^ℓ`. This is one constituent of the CRT
algebra equivalence, retaining the precise quotient-root image.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped Polynomial
noncomputable section

def localPrimaryFactor (α : ℂ) (ℓ : ℕ) : Polynomial ℂ :=
  ((Polynomial.X : Polynomial ℂ) - Polynomial.C α) ^ ℓ

/-- Send the primary quotient root to `α+z`. -/
def localShiftTo (α : ℂ) (ℓ : ℕ) :
    AdjoinRoot (localPrimaryFactor α ℓ) →ₐ[ℂ] LocalTruncated ℓ :=
  AdjoinRoot.liftAlgHom (localPrimaryFactor α ℓ)
    (Algebra.ofId ℂ (LocalTruncated ℓ))
    (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) (by
      change ((Polynomial.X - Polynomial.C α : Polynomial ℂ) ^ ℓ).eval₂
        (AdjoinRoot.of ((Polynomial.X : Polynomial ℂ) ^ ℓ))
        (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) = 0
      simp [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C, localRoot_pow_eq_zero])

/-- Send the local nilpotent generator to the primary root minus `α`. -/
def localShiftFrom (α : ℂ) (ℓ : ℕ) :
    LocalTruncated ℓ →ₐ[ℂ] AdjoinRoot (localPrimaryFactor α ℓ) :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial ℂ) ^ ℓ)
    (Algebra.ofId ℂ (AdjoinRoot (localPrimaryFactor α ℓ)))
    (AdjoinRoot.root (localPrimaryFactor α ℓ) -
      algebraMap ℂ (AdjoinRoot (localPrimaryFactor α ℓ)) α) (by
      have hz := AdjoinRoot.eval₂_root (localPrimaryFactor α ℓ)
      change ((Polynomial.X - Polynomial.C α : Polynomial ℂ) ^ ℓ).eval₂
        (AdjoinRoot.of (localPrimaryFactor α ℓ))
        (AdjoinRoot.root (localPrimaryFactor α ℓ)) = 0 at hz
      simp only [Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
        Polynomial.eval₂_C] at hz
      simpa [Polynomial.eval₂_X_pow, Algebra.ofId_apply] using hz)

theorem localShiftTo_root (α : ℂ) (ℓ : ℕ) :
    localShiftTo α ℓ (AdjoinRoot.root (localPrimaryFactor α ℓ)) =
      algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ := by
  exact AdjoinRoot.liftAlgHom_root ..

theorem localShiftFrom_root (α : ℂ) (ℓ : ℕ) :
    localShiftFrom α ℓ (localRoot ℓ) =
      AdjoinRoot.root (localPrimaryFactor α ℓ) -
        algebraMap ℂ (AdjoinRoot (localPrimaryFactor α ℓ)) α := by
  exact AdjoinRoot.liftAlgHom_root ..

private theorem localShift_left_inverse (α : ℂ) (ℓ : ℕ) :
    (localShiftFrom α ℓ).comp (localShiftTo α ℓ) =
      AlgHom.id ℂ (AdjoinRoot (localPrimaryFactor α ℓ)) := by
  apply AdjoinRoot.algHom_ext
  rw [AlgHom.comp_apply, localShiftTo_root, map_add, AlgHom.map_algebraMap,
    localShiftFrom_root]
  abel

private theorem localShift_right_inverse (α : ℂ) (ℓ : ℕ) :
    (localShiftTo α ℓ).comp (localShiftFrom α ℓ) =
      AlgHom.id ℂ (LocalTruncated ℓ) := by
  apply AdjoinRoot.algHom_ext
  change (localShiftTo α ℓ) ((localShiftFrom α ℓ) (localRoot ℓ)) = localRoot ℓ
  rw [localShiftFrom_root, map_sub, localShiftTo_root, AlgHom.map_algebraMap]
  abel

/-- Exact complex-algebra equivalence between a primary root factor and the
truncated local algebra. -/
def localShiftEquiv (α : ℂ) (ℓ : ℕ) :
    AdjoinRoot (localPrimaryFactor α ℓ) ≃ₐ[ℂ] LocalTruncated ℓ :=
  AlgEquiv.ofBijective (localShiftTo α ℓ) (by
    constructor
    · exact Function.LeftInverse.injective (fun x =>
        congrArg (fun f : _ →ₐ[ℂ] _ => f x) (localShift_left_inverse α ℓ))
    · exact Function.RightInverse.surjective (fun x =>
        congrArg (fun f : _ →ₐ[ℂ] _ => f x) (localShift_right_inverse α ℓ)))

theorem localShiftEquiv_root (α : ℂ) (ℓ : ℕ) :
    localShiftEquiv α ℓ (AdjoinRoot.root (localPrimaryFactor α ℓ)) =
      algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ :=
  localShiftTo_root α ℓ

#assert_trust kernel localShiftTo
#assert_trust kernel localShiftFrom
#assert_trust kernel localShift_left_inverse
#assert_trust kernel localShift_right_inverse
#assert_trust kernel localShiftEquiv
#assert_trust kernel localShiftEquiv_root
#print axioms localShiftEquiv_root

end
end NLA.Proofs.TR14
