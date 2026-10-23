import NLA.Proofs.TR14.ReducedSubalgebras
import Mathlib.Algebra.Algebra.Pi

/-! Actual primitive scalar blocks of a reduced finite-dimensional complex
algebra and the resulting ambient idempotents in a subalgebra. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
noncomputable section

/-- A reduced finite-dimensional commutative complex algebra is actually
isomorphic, as a complex algebra, to a finite product of copies of ℂ. -/
theorem reduced_complex_exists_equiv_fin (A : Type*) [CommRing A]
    [Algebra ℂ A] [FiniteDimensional ℂ A] [IsReduced A] :
    ∃ t : ℕ, Nonempty (A ≃ₐ[ℂ] (Fin t → ℂ)) := by
  classical
  let : IsArtinianRing A := isArtinian_of_tower ℂ inferInstance
  let ι := MaximalSpectrum A
  let : Fintype ι := Fintype.ofFinite ι
  have hequiv (m : ι) : Nonempty ((A ⧸ m.asIdeal) ≃ₐ[ℂ] ℂ) := by
    let : m.asIdeal.IsMaximal := m.isMaximal
    let : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    let : Module.Finite ℂ (A ⧸ m.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ m.asIdeal).toLinearMap
        (Ideal.Quotient.mkₐ_surjective ℂ m.asIdeal)
    exact ⟨(AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m.asIdeal))
      (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := ℂ) (K := A ⧸ m.asIdeal))).symm⟩
  let f : ∀ m : ι, (A ⧸ m.asIdeal) ≃ₐ[ℂ] ℂ := fun m => Classical.choice (hequiv m)
  let φ : A ≃ₐ[ℂ] (ι → ℂ) :=
    ((IsArtinianRing.equivPi A).restrictScalars ℂ).trans (AlgEquiv.piCongrRight f)
  exact ⟨Fintype.card ι, ⟨φ.trans
    (AlgEquiv.piCongrLeft' ℂ (fun _ : ι => ℂ) (Fintype.equivFin ι))⟩⟩

variable {B : Type*} [CommRing B] [Algebra ℂ B]

/-- The actual ambient indicator of a scalar factor of a subalgebra. -/
def reducedBlockIdempotent (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t) : B :=
  (φ.symm (Pi.single j 1) : S)

@[simp]
theorem reducedBlockIdempotent_mem (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t) : reducedBlockIdempotent S φ j ∈ S :=
  (φ.symm (Pi.single j 1)).property

/-- Each scalar-factor indicator is a nonzero ambient idempotent. -/
theorem reducedBlockIdempotent_ne_zero (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t) :
    reducedBlockIdempotent S φ j ≠ 0 := by
  intro hz
  have hzero : φ.symm (Pi.single j 1) = 0 := Subtype.ext hz
  have h := congrArg (fun x : S => φ x j) hzero
  simp at h

theorem reducedBlockIdempotent_mul_self (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) (j : Fin t) :
    reducedBlockIdempotent S φ j * reducedBlockIdempotent S φ j =
      reducedBlockIdempotent S φ j := by
  have heq : φ.symm (Pi.single j 1) * φ.symm (Pi.single j 1) = φ.symm (Pi.single j 1) := by
    apply φ.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    ext k
    by_cases h : j = k <;> simp [h]
  exact congrArg (fun x : S => (x : B)) heq

/-- Distinct primitive indicators have zero product in the actual ambient
algebra; nilpotents elsewhere in the ambient algebra are allowed. -/
theorem reducedBlockIdempotent_mul_eq_zero (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) {i j : Fin t} (hij : i ≠ j) :
    reducedBlockIdempotent S φ i * reducedBlockIdempotent S φ j = 0 := by
  have heq : φ.symm (Pi.single i 1) * φ.symm (Pi.single j 1) = 0 := by
    apply φ.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply, map_zero]
    ext k
    by_cases hik : i = k
    · subst k
      simp [hij]
    · simp [hik]
  exact congrArg (fun x : S => (x : B)) heq

/-- The primitive indicators partition the actual ambient identity. -/
theorem reducedBlockIdempotent_sum (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) :
    (∑ j, reducedBlockIdempotent S φ j) = 1 := by
  have heq : (∑ j : Fin t, φ.symm (Pi.single j 1)) = 1 := by
    apply φ.injective
    simp only [map_sum, AlgEquiv.apply_symm_apply, map_one]
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h := congrArg S.val heq
  simpa only [map_sum, map_one, Subalgebra.val_apply, reducedBlockIdempotent] using h

/-- Every subalgebra element acts on one primitive block by its actual
scalar coordinate in the constructed product equivalence. -/
theorem reducedBlockIdempotent_scalar_action (S : Subalgebra ℂ B) {t : ℕ}
    (φ : S ≃ₐ[ℂ] (Fin t → ℂ)) (a : S) (j : Fin t) :
    (a : B) * reducedBlockIdempotent S φ j =
      φ a j • reducedBlockIdempotent S φ j := by
  have heq : a * φ.symm (Pi.single j 1) = φ a j • φ.symm (Pi.single j 1) := by
    apply φ.injective
    simp only [map_mul, map_smul, AlgEquiv.apply_symm_apply]
    ext k
    by_cases h : j = k
    · subst k
      simp
    · simp [Pi.single_eq_of_ne' h]
  exact congrArg (fun x : S => (x : B)) heq

#assert_trust kernel reduced_complex_exists_equiv_fin
#assert_trust kernel reducedBlockIdempotent_ne_zero
#assert_trust kernel reducedBlockIdempotent_mul_self
#assert_trust kernel reducedBlockIdempotent_mul_eq_zero
#assert_trust kernel reducedBlockIdempotent_sum
#assert_trust kernel reducedBlockIdempotent_scalar_action
#print axioms reduced_complex_exists_equiv_fin
#print axioms reducedBlockIdempotent_scalar_action

end
end NLA.Proofs.TR14
