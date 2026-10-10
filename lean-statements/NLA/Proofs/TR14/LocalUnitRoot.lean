import NLA.Proofs.TR14.LocalTopCoefficient
import Mathlib.Dynamics.Newton
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
The nonzero constant coefficient forced by genuine local Frobenius
nondegeneracy, and an exact finite nilpotent lift of every positive integer
root of a local unit in `ℂ[z]/(z^ℓ)`.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial Module
open scoped BigOperators Polynomial
noncomputable section

theorem localRoot_pow_eq_zero_of_le (ℓ k : ℕ) (hk : ℓ ≤ k) :
    localRoot ℓ ^ k = 0 := by
  calc
    localRoot ℓ ^ k = localRoot ℓ ^ ℓ * localRoot ℓ ^ (k - ℓ) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    _ = 0 := by rw [localRoot_pow_eq_zero, zero_mul]

/-- Genuine local Frobenius nondegeneracy forces the first reversed coefficient
to be nonzero, including the length-one quotient. -/
theorem localFrobenius_const_ne_zero (ℓ : ℕ) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ)
    (hFrob : ∀ a : LocalTruncated ℓ,
      (∀ b : LocalTruncated ℓ, Λ (a * b) = 0) → a = 0) :
    localCoeff ℓ (localFrobeniusElement ℓ hℓ Λ) (⟨0, hℓ⟩ : Fin ℓ) ≠ 0 := by
  let u := localFrobeniusElement ℓ hℓ Λ
  let a := localRoot ℓ ^ (ℓ - 1)
  intro hu
  have hu0 : localCoeffNat ℓ u 0 = 0 := by simpa only [u, localCoeff] using hu
  have hua : u * a = 0 := by
    apply local_eq_of_coeff ℓ
    intro j
    change localCoeffNat ℓ (u * localRoot ℓ ^ (ℓ - 1)) j.val =
      localCoeffNat ℓ 0 j.val
    rw [localCoeffNat_mul_root_pow ℓ (ℓ - 1) j.val j.isLt]
    by_cases hj : ℓ - 1 ≤ j.val
    · have hjtop : j.val = ℓ - 1 := by omega
      rw [if_pos hj, hjtop, Nat.sub_self, hu0]
      simp [localCoeffNat]
    · rw [if_neg hj]
      simp [localCoeffNat]
  have ha0 : a ≠ 0 := by
    intro ha
    have hc := congrArg (fun x : LocalTruncated ℓ =>
      localCoeffNat ℓ x (ℓ - 1)) ha
    have hpow : localCoeffNat ℓ (localRoot ℓ ^ (ℓ - 1)) (ℓ - 1) = 1 := by
      simpa using localCoeffNat_root_pow ℓ (ℓ - 1) (ℓ - 1) (by omega)
    have hone : (1 : ℂ) = 0 := by
      calc
        1 = localCoeffNat ℓ a (ℓ - 1) := by simpa only [a] using hpow.symm
        _ = localCoeffNat ℓ 0 (ℓ - 1) := hc
        _ = 0 := by simp [localCoeffNat]
    exact one_ne_zero hone
  apply ha0
  apply hFrob a
  intro b
  rw [localFrobenius_repr ℓ hℓ Λ]
  rw [← mul_assoc, hua, zero_mul]
  simp [localTopCoeff, localCoeffNat]

/-- Vanishing constant coefficient makes a class nilpotent with exponent at
most the truncation length. This is an exact quotient identity. -/
theorem local_nilpotent_of_const_zero (ℓ : ℕ) (_hℓ : 0 < ℓ)
    (a : LocalTruncated ℓ) (ha : localCoeffNat ℓ a 0 = 0) :
    IsNilpotent a := by
  let p := AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow ℓ) a
  have hp0 : p.coeff 0 = 0 := ha
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hp0
  have hae : a = localRoot ℓ * AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) q := by
    calc
      a = AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) p :=
        (AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow ℓ) a).symm
      _ = AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ)
          (Polynomial.X * q) := by rw [hq]
      _ = localRoot ℓ * AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) q := by
        rw [map_mul]
        rfl
  refine ⟨ℓ, ?_⟩
  rw [hae, mul_pow, localRoot_pow_eq_zero, zero_mul]

/-- Every local class with a nonzero constant coefficient has an exact
positive-integer root. Newton lifting stops after finitely many nilpotent
steps; no analytic series or branch selection is used. -/
theorem local_unit_has_nth_root (ℓ m : ℕ) (hℓ : 0 < ℓ) (hm : 0 < m)
    (u : LocalTruncated ℓ)
    (hu0 : localCoeff ℓ u (⟨0, hℓ⟩ : Fin ℓ) ≠ 0) :
    ∃ w : LocalTruncated ℓ, w ^ m = u := by
  let c : ℂ := localCoeffNat ℓ u 0
  have hc : c ≠ 0 := by simpa only [c, localCoeff] using hu0
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq c hm
  have hρ0 : ρ ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Nat.ne_of_gt hm)] at hρ
    exact hc hρ.symm
  let x : LocalTruncated ℓ := algebraMap ℂ (LocalTruncated ℓ) ρ
  let P : Polynomial (LocalTruncated ℓ) := X ^ m - C u
  have hconst (t : ℂ) :
      localCoeffNat ℓ (algebraMap ℂ (LocalTruncated ℓ) t) 0 = t := by
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
    rw [localCoeffNat_mk ℓ (C t) 0 hℓ]
    simp
  have hxP : Polynomial.aeval x P = algebraMap ℂ (LocalTruncated ℓ) c - u := by
    simp only [P, aeval_sub, aeval_X_pow, aeval_C]
    change x ^ m - u = algebraMap ℂ (LocalTruncated ℓ) c - u
    dsimp [x]
    rw [← map_pow, hρ]
  have hnil : IsNilpotent (Polynomial.aeval x P) := by
    rw [hxP]
    apply local_nilpotent_of_const_zero ℓ hℓ
    have hsub : localCoeffNat ℓ (algebraMap ℂ (LocalTruncated ℓ) c - u) 0 =
        localCoeffNat ℓ (algebraMap ℂ (LocalTruncated ℓ) c) 0 -
          localCoeffNat ℓ u 0 := by simp [localCoeffNat]
    rw [hsub, hconst]
    exact sub_self c
  have hscalarunit : IsUnit ((m : ℂ) * ρ ^ (m - 1)) := by
    apply isUnit_iff_ne_zero.mpr
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hm)) (pow_ne_zero _ hρ0)
  have hder : IsUnit (Polynomial.aeval x (Polynomial.derivative P)) := by
    have hmap : IsUnit (algebraMap ℂ (LocalTruncated ℓ)
        ((m : ℂ) * ρ ^ (m - 1))) := hscalarunit.map _
    convert hmap using 1
    simp [P, Polynomial.derivative_X_pow, x, map_mul, map_pow]
  obtain ⟨w, ⟨_, hw⟩, _⟩ :=
    Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
      (P := P) (x := x) hnil hder
  refine ⟨w, ?_⟩
  have hroot : w ^ m - u = 0 := by simpa [P] using hw
  exact sub_eq_zero.mp hroot

#assert_trust kernel localFrobenius_const_ne_zero
#assert_trust kernel local_nilpotent_of_const_zero
#assert_trust kernel local_unit_has_nth_root
#print axioms local_unit_has_nth_root

end
end NLA.Proofs.TR14
