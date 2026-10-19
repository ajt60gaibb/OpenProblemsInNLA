import NLA.Proofs.TR14.LocalFourierOneFactor

/-!
The exact zero-based mode-vector corollary of the one-factor local Fourier
identity. It is local to one root `α` and does not assume a global CRT.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial Module
open scoped BigOperators Polynomial
noncomputable section

/-- The local class of the zero-based mode polynomial
`p_v(t)=∑_{i=0}^{n-1}v_i t^i` after `t=α+z`. -/
def localModeClass (n ℓ : ℕ) (α : ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] LocalTruncated ℓ where
  toFun v := ∑ i : Fin n,
    v i • (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) ^ i.val
  map_add' v v' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply,
      smul_eq_mul]

theorem localModeClass_apply (n ℓ : ℕ) (α : ℂ) (v : Fin n → ℂ) :
    localModeClass n ℓ α v =
      ∑ i : Fin n,
        v i • (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) ^ i.val := rfl

theorem localModeClass_basis (n ℓ : ℕ) (α : ℂ) (i : Fin n) :
    localModeClass n ℓ α (fun j => if j = i then 1 else 0) =
      (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) ^ i.val := by
  simp [localModeClass]

/-- The one-factor Fourier functional composed with the mode-class map. -/
def localModeFourierFactor (m n ℓ : ℕ) (hℓ : 0 < ℓ)
    (α : ℂ) (w : LocalTruncated ℓ) (ζ : ℂ)
    (j : Fin (localFourierCount m ℓ)) :
    (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (localFourierFunctional m ℓ hℓ w ζ j).comp (localModeClass n ℓ α)

/-- Its exact coordinate vector; no binomial or conjugation factor. -/
def localModeFourierVector (m n ℓ : ℕ) (hℓ : 0 < ℓ)
    (α : ℂ) (w : LocalTruncated ℓ) (ζ : ℂ)
    (j : Fin (localFourierCount m ℓ)) (i : Fin n) : ℂ :=
  localFourierFunctional m ℓ hℓ w ζ j
    ((algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) ^ i.val)

theorem localModeFourierFactor_basis (m n ℓ : ℕ) (hℓ : 0 < ℓ)
    (α : ℂ) (w : LocalTruncated ℓ) (ζ : ℂ)
    (j : Fin (localFourierCount m ℓ)) (i : Fin n) :
    localModeFourierFactor m n ℓ hℓ α w ζ j
      (fun k => if k = i then 1 else 0) =
      localModeFourierVector m n ℓ hℓ α w ζ j i := by
  rw [localModeFourierFactor, LinearMap.comp_apply,
    localModeClass_basis]
  rfl

theorem localModeFourierFactor_apply_eq_sum (m n ℓ : ℕ) (hℓ : 0 < ℓ)
    (α : ℂ) (w : LocalTruncated ℓ) (ζ : ℂ)
    (j : Fin (localFourierCount m ℓ)) (v : Fin n → ℂ) :
    localModeFourierFactor m n ℓ hℓ α w ζ j v =
      ∑ i : Fin n, v i * localModeFourierVector m n ℓ hℓ α w ζ j i := by
  rw [localModeFourierFactor, LinearMap.comp_apply, localModeClass_apply,
    map_sum]
  simp only [map_smul, smul_eq_mul, localModeFourierVector]

/-- At tensor basis coordinates the one-factor local contribution has the
same vector in every mode, with exactly `N=(m-1)(ℓ-1)+1` terms. -/
theorem local_fourier_mode_coordinates (m n ℓ : ℕ)
    (hm : 3 ≤ m) (_hn : 2 ≤ n) (hℓ : 0 < ℓ)
    (α : ℂ) (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ)
    (hFrob : ∀ a : LocalTruncated ℓ,
      (∀ b : LocalTruncated ℓ, Λ (a * b) = 0) → a = 0) :
    ∃ w : LocalTruncated ℓ, ∃ ζ : ℂ,
      IsPrimitiveRoot ζ (localFourierCount m ℓ) ∧
      w ^ m = localFrobeniusElement ℓ hℓ Λ ∧
      ∀ i : Fin m → Fin n,
        Λ (∏ k : Fin m,
          (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) ^ (i k).val) =
          ∑ j : Fin (localFourierCount m ℓ),
            (localFourierCount m ℓ : ℂ)⁻¹ *
              ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ *
              ∏ k : Fin m,
                localModeFourierVector m n ℓ hℓ α w ζ j (i k) := by
  obtain ⟨w, ζ, hζ, hw, hformula⟩ :=
    local_fourier_multilinear m ℓ hm hℓ Λ hFrob
  refine ⟨w, ζ, hζ, hw, ?_⟩
  intro i
  simpa only [localModeFourierVector] using
    hformula (fun k : Fin m =>
      (algebraMap ℂ (LocalTruncated ℓ) α + localRoot ℓ) ^ (i k).val)

#assert_trust kernel localModeClass
#assert_trust kernel localModeClass_basis
#assert_trust kernel localModeFourierFactor
#assert_trust kernel localModeFourierFactor_apply_eq_sum
#assert_trust kernel local_fourier_mode_coordinates
#print axioms local_fourier_mode_coordinates

end
end NLA.Proofs.TR14
