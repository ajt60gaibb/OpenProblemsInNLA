import NLA.Proofs.TR14.OrdinaryGraphUnits
import NLA.Proofs.TR14.UnitProductScaling

/-! Separate actual graph units normalize the source's graph spaces to
contain one. The same actual quotient chart is retained, and the full
annihilator, Frobenius constraint and scalar surjectivity are transported
by invertible multiplication. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

noncomputable section
variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The actual separately normalized mode graph. -/
def normalizedGraphSpace {m n r : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] A)
    (u : Fin r → Fin m → Fin n → ℂ) (a : Fin m → (A × (Fin r → ℂ))ˣ)
    (k : Fin m) : Submodule ℂ (A × (Fin r → ℂ)) :=
  unitScale (a k)⁻¹ (ordinaryGraphSpace φ u k)

/-- Source functional after scaling the whole product by the actual units. -/
def normalizedGraphFunctional {m r : ℕ} (Λ : A →ₗ[ℂ] ℂ)
    (a : Fin m → (A × (Fin r → ℂ))ˣ) : (A × (Fin r → ℂ)) →ₗ[ℂ] ℂ :=
  (ordinaryGraphFunctional Λ).comp (unitMultiplication (∏ k, a k)).toLinearMap

@[simp] theorem normalizedGraphFunctional_apply {m r : ℕ} (Λ : A →ₗ[ℂ] ℂ)
    (a : Fin m → (A × (Fin r → ℂ))ˣ) (x : A × (Fin r → ℂ)) :
    normalizedGraphFunctional Λ a x =
      Λ (((∏ k, a k : (A × (Fin r → ℂ))ˣ) : A × (Fin r → ℂ)).1 * x.1) -
        ∑ j, ((∏ k, a k : (A × (Fin r → ℂ))ˣ) : A × (Fin r → ℂ)).2 j * x.2 j := rfl

/-- Every normalized mode genuinely contains one. -/
theorem one_mem_normalizedGraphSpace {m n r : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] A)
    (u : Fin r → Fin m → Fin n → ℂ) (a : Fin m → (A × (Fin r → ℂ))ˣ)
    (ha : ∀ k, (a k : A × (Fin r → ℂ)) ∈ ordinaryGraphSpace φ u k) (k : Fin m) :
    (1 : A × (Fin r → ℂ)) ∈ normalizedGraphSpace φ u a k :=
  one_mem_unitScale_inv (a k) _ (ha k)

/-- Full actual product identity for these independent normalizations. -/
theorem normalizedGraph_product {m n r : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] A)
    (u : Fin r → Fin m → Fin n → ℂ) (a : Fin m → (A × (Fin r → ℂ))ˣ) :
    (∏ k, normalizedGraphSpace φ u a k) =
      unitScale (∏ k, a k)⁻¹ (∏ k, ordinaryGraphSpace φ u k) := by
  simp only [normalizedGraphSpace, unitScale_prod, Finset.prod_inv_distrib]

/-- The actual normalized full graph remains in the actual annihilator. -/
theorem normalizedGraph_product_annihilated {m n r : ℕ}
    (φ : (Fin n → ℂ) →ₗ[ℂ] A) (Λ : A →ₗ[ℂ] ℂ)
    (u : Fin r → Fin m → Fin n → ℂ) (a : Fin m → (A × (Fin r → ℂ))ˣ)
    (H : (Fin m → Fin n) → ℂ) (hH : ∀ i, H i = ∑ j, ordinarySummand u j i)
    (hmoment : ∀ p : Fin m → Fin n → ℂ,
      Λ (∏ k, φ (p k)) = ∑ i, H i * ∏ k, p k (i k)) :
    (∏ k, normalizedGraphSpace φ u a k) ≤ LinearMap.ker (normalizedGraphFunctional Λ a) := by
  intro w hw
  have heq : unitScale (∏ k, a k) (∏ k, normalizedGraphSpace φ u a k) =
      ∏ k, ordinaryGraphSpace φ u k := by rw [normalizedGraph_product, unitScale_scale_inv]
  have hmem : ((∏ k, a k : (A × (Fin r → ℂ))ˣ) : A × (Fin r → ℂ)) * w ∈
      ∏ k, ordinaryGraphSpace φ u k := by
    rw [← heq]
    exact (mem_unitScale _ _ _).mpr ⟨w, hw, rfl⟩
  exact ordinaryGraph_product_annihilated φ Λ u H hH hmoment hmem

/-- Unit scaling preserves the Frobenius nondegeneracy of the actual first
factor restriction. -/
theorem normalizedGraphFunctional_frobenius {m r : ℕ} (Λ : A →ₗ[ℂ] ℂ)
    (hFrob : ∀ x : A, (∀ y : A, Λ (x * y) = 0) → x = 0)
    (a : Fin m → (A × (Fin r → ℂ))ˣ) :
    ∀ x : A, (∀ y : A, normalizedGraphFunctional Λ a (x * y, 0) = 0) → x = 0 := by
  intro x hx
  let v : (A × (Fin r → ℂ))ˣ := ∏ k, a k
  have hz : (v : A × (Fin r → ℂ)).1 * x = 0 := hFrob _ (by
    intro y
    have h := hx y
    simpa only [normalizedGraphFunctional_apply, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, sub_zero, v, mul_assoc] using h)
  exact (v.isUnit.map (RingHom.fst A (Fin r → ℂ))).mul_right_eq_zero.mp hz

/-- Scalar projection surjectivity survives the actual separate unit changes. -/
theorem normalizedGraph_product_snd {m n r : ℕ} (φ : (Fin n → ℂ) →ₗ[ℂ] A)
    (u : Fin r → Fin m → Fin n → ℂ) (a : Fin m → (A × (Fin r → ℂ))ˣ)
    (hind : LinearIndependent ℂ (ordinarySummand u)) :
    (∏ k, normalizedGraphSpace φ u a k).map (AlgHom.snd ℂ A (Fin r → ℂ)).toLinearMap = ⊤ := by
  rw [normalizedGraph_product]
  exact unitScale_map_top _ _ _ (ordinaryGraph_product_snd φ u hind)

/-- Every actual scalar-coordinate coefficient of the normalized functional
is nonzero, as required to exclude scalar-only primitive blocks. -/
theorem normalizedGraphFunctional_scalar_ne_zero {m r : ℕ} (Λ : A →ₗ[ℂ] ℂ)
    (a : Fin m → (A × (Fin r → ℂ))ˣ) (j : Fin r) :
    normalizedGraphFunctional Λ a (0, Pi.single j 1) ≠ 0 := by
  classical
  let v : (A × (Fin r → ℂ))ˣ := ∏ k, a k
  have hnonzero : (v : A × (Fin r → ℂ)).2 j ≠ 0 := by
    intro hz
    have h : (v : A × (Fin r → ℂ)).2 j *
        ((v⁻¹ : (A × (Fin r → ℂ))ˣ) : A × (Fin r → ℂ)).2 j = 1 :=
      congrArg (fun x : A × (Fin r → ℂ) => x.2 j) v.val_inv
    rw [hz, zero_mul] at h
    exact zero_ne_one h
  have heq : normalizedGraphFunctional Λ a (0, Pi.single j 1) =
      - (v : A × (Fin r → ℂ)).2 j := by
    simp [normalizedGraphFunctional_apply, v, Pi.single_apply]
  rw [heq]
  exact neg_ne_zero.mpr hnonzero

#assert_trust kernel normalizedGraph_product_annihilated
#assert_trust kernel normalizedGraphFunctional_frobenius
#assert_trust kernel normalizedGraph_product_snd
#assert_trust kernel normalizedGraphFunctional_scalar_ne_zero
#print axioms normalizedGraph_product_annihilated

end
end NLA.Proofs.TR14
