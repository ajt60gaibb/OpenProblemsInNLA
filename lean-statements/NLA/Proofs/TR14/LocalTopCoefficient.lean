import NLA.Proofs.TR14.MomentQuotientModePairing
import Mathlib.LinearAlgebra.Basis.Basic

/-!
Exact power-basis coefficients and Frobenius top-coefficient representation
in the truncated local algebra `ℂ[z]/(z^ℓ)`. The finite root and CRT remain open.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial Module
open scoped BigOperators Polynomial
noncomputable section

abbrev LocalTruncated (ℓ : ℕ) :=
  AdjoinRoot ((Polynomial.X : Polynomial ℂ) ^ ℓ)

private theorem local_monic_X_pow (ℓ : ℕ) :
    ((Polynomial.X : Polynomial ℂ) ^ ℓ).Monic :=
  Polynomial.monic_X_pow ℓ

/-- The nilpotent quotient generator. -/
def localRoot (ℓ : ℕ) : LocalTruncated ℓ :=
  AdjoinRoot.root ((Polynomial.X : Polynomial ℂ) ^ ℓ)

/-- Arbitrary-index coefficient of the canonical monic remainder. -/
def localCoeffNat (ℓ : ℕ) (a : LocalTruncated ℓ) (j : ℕ) : ℂ :=
  (AdjoinRoot.modByMonicHom (local_monic_X_pow ℓ) a).coeff j

/-- Degree-`<ℓ` power-basis coordinate. -/
def localCoeff (ℓ : ℕ) (a : LocalTruncated ℓ) (j : Fin ℓ) : ℂ :=
  localCoeffNat ℓ a j.val

/-- The exact top coefficient of a local quotient class. -/
def localTopCoeff (ℓ : ℕ) (_hℓ : 0 < ℓ) (a : LocalTruncated ℓ) : ℂ :=
  localCoeffNat ℓ a (ℓ - 1)

/-- Mathlib's monic quotient power basis, reindexed to the exact `Fin ℓ`. -/
private theorem localNatDegree_eq (ℓ : ℕ) :
    ((Polynomial.X : Polynomial ℂ) ^ ℓ).natDegree = ℓ := by
  exact Polynomial.natDegree_X_pow ℓ

def localBasis (ℓ : ℕ) : Basis (Fin ℓ) ℂ (LocalTruncated ℓ) := by
  exact (AdjoinRoot.powerBasisAux' (local_monic_X_pow ℓ)).reindex
    (finCongr (localNatDegree_eq ℓ))

theorem localBasis_apply (ℓ : ℕ) (j : Fin ℓ) :
    localBasis ℓ j = localRoot ℓ ^ j.val := by
  simp only [localBasis, Basis.reindex_apply]
  have hb := (AdjoinRoot.powerBasis' (local_monic_X_pow ℓ)).basis_eq_pow
    ((finCongr (localNatDegree_eq ℓ)).symm j)
  change (AdjoinRoot.powerBasisAux' (local_monic_X_pow ℓ))
      ((finCongr (localNatDegree_eq ℓ)).symm j) =
    (AdjoinRoot.root ((Polynomial.X : Polynomial ℂ) ^ ℓ)) ^
      ((finCongr (localNatDegree_eq ℓ)).symm j).val at hb
  simpa only [localRoot, finCongr_symm_apply_coe] using hb

theorem localBasis_repr (ℓ : ℕ) (a : LocalTruncated ℓ) (j : Fin ℓ) :
    (localBasis ℓ).repr a j = localCoeff ℓ a j := by
  rw [localBasis, Basis.repr_reindex_apply]
  change ((AdjoinRoot.powerBasisAux' (local_monic_X_pow ℓ)).repr a)
      ((finCongr (localNatDegree_eq ℓ)).symm j) = localCoeff ℓ a j
  rw [AdjoinRoot.powerBasisAux'_repr_apply_to_fun]
  simp only [localCoeff, localCoeffNat, finCongr_symm_apply_coe]

theorem localRoot_pow_eq_zero (ℓ : ℕ) : localRoot ℓ ^ ℓ = 0 := by
  change (AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) Polynomial.X) ^ ℓ = 0
  rw [← map_pow]
  exact AdjoinRoot.mk_self

/-- Below the truncation degree, quotient coefficients are unchanged. -/
theorem localCoeffNat_mk (ℓ : ℕ) (p : Polynomial ℂ) (j : ℕ) (hj : j < ℓ) :
    localCoeffNat ℓ (AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) p) j =
      p.coeff j := by
  simp only [localCoeffNat, AdjoinRoot.modByMonicHom_mk,
    Polynomial.modByMonic_eq_sub_mul_div, Polynomial.coeff_sub]
  simp [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hj]

/-- Quotient powers below degree `ℓ` are the exact power-basis vectors. -/
theorem localCoeffNat_root_pow (ℓ : ℕ) (i j : ℕ) (hj : j < ℓ) :
    localCoeffNat ℓ (localRoot ℓ ^ i) j = if i = j then 1 else 0 := by
  have hpow : localRoot ℓ ^ i =
      AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) ((Polynomial.X : Polynomial ℂ) ^ i) := by
    change (AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) Polynomial.X) ^ i = _
    rw [← map_pow]
  rw [hpow]
  rw [localCoeffNat_mk ℓ _ j hj]
  simp [Polynomial.coeff_X_pow, eq_comm]

/-- The power-basis coordinates are linear in their local class. -/
theorem localCoeffNat_add (ℓ j : ℕ) (a b : LocalTruncated ℓ) :
    localCoeffNat ℓ (a + b) j = localCoeffNat ℓ a j + localCoeffNat ℓ b j := by
  simp [localCoeffNat]

theorem localCoeffNat_smul (ℓ j : ℕ) (c : ℂ) (a : LocalTruncated ℓ) :
    localCoeffNat ℓ (c • a) j = c * localCoeffNat ℓ a j := by
  simp [localCoeffNat, smul_eq_mul]

/-- Exact truncated convolution, with every summand of degree `j<ℓ`. -/
theorem localCoeffNat_mul (ℓ j : ℕ) (hj : j < ℓ)
    (a b : LocalTruncated ℓ) :
    localCoeffNat ℓ (a * b) j =
      ∑ ij ∈ Finset.antidiagonal j,
        localCoeffNat ℓ a ij.1 * localCoeffNat ℓ b ij.2 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  rw [← map_mul, localCoeffNat_mk ℓ (p * q) j hj, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  rw [localCoeffNat_mk ℓ p ij.1 (by omega),
    localCoeffNat_mk ℓ q ij.2 (by omega)]

/-- Multiplication by a quotient-root power shifts coefficients until the
truncation boundary. -/
theorem localCoeffNat_mul_root_pow (ℓ i j : ℕ) (hj : j < ℓ)
    (a : LocalTruncated ℓ) :
    localCoeffNat ℓ (a * localRoot ℓ ^ i) j =
      if i ≤ j then localCoeffNat ℓ a (j - i) else 0 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  have hpow : localRoot ℓ ^ i =
      AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) ((Polynomial.X : Polynomial ℂ) ^ i) := by
    change (AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) Polynomial.X) ^ i = _
    rw [← map_pow]
  rw [hpow, ← map_mul, localCoeffNat_mk ℓ _ j hj,
    Polynomial.coeff_mul_X_pow']
  split_ifs with hi
  · rw [localCoeffNat_mk ℓ p (j - i) (by omega)]
  · rfl

/-- Coordinates below degree `ℓ` determine every quotient class. -/
theorem local_eq_of_coeff (ℓ : ℕ) (a b : LocalTruncated ℓ)
    (h : ∀ j : Fin ℓ, localCoeff ℓ a j = localCoeff ℓ b j) : a = b := by
  apply (localBasis ℓ).repr.injective
  ext j
  simpa only [localBasis_repr] using h j

/-- The monic power basis reconstructs every local quotient element. -/
theorem local_power_basis_sum (ℓ : ℕ) (a : LocalTruncated ℓ) :
    (∑ j : Fin ℓ, localCoeff ℓ a j • localRoot ℓ ^ j.val) = a := by
  simpa only [localBasis_repr, localBasis_apply] using (localBasis ℓ).sum_repr a

theorem localCoeffNat_sum {α : Type*} (ℓ j : ℕ) (s : Finset α)
    (f : α → LocalTruncated ℓ) :
    localCoeffNat ℓ (∑ i ∈ s, f i) j =
      ∑ i ∈ s, localCoeffNat ℓ (f i) j := by
  simp [localCoeffNat]

/-- The reversed coefficients of the unique local Frobenius element. -/
def localFrobeniusElement (ℓ : ℕ) (_hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ) : LocalTruncated ℓ :=
  ∑ j : Fin ℓ, (Λ (localRoot ℓ ^ (ℓ - 1 - j.val))) • localRoot ℓ ^ j.val

theorem localFrobeniusElement_coeff (ℓ : ℕ) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ) (j : Fin ℓ) :
    localCoeff ℓ (localFrobeniusElement ℓ hℓ Λ) j =
      Λ (localRoot ℓ ^ (ℓ - 1 - j.val)) := by
  simp only [localCoeff, localFrobeniusElement, localCoeffNat_sum,
    localCoeffNat_smul]
  simp_rw [localCoeffNat_root_pow ℓ _ j.val j.isLt]
  simp only [Fin.val_eq_val]
  simp

/-- Top coefficient after multiplication by a fixed local class is linear. -/
def localTopMulLinear (ℓ : ℕ) (hℓ : 0 < ℓ) (u : LocalTruncated ℓ) :
    LocalTruncated ℓ →ₗ[ℂ] ℂ where
  toFun a := localTopCoeff ℓ hℓ (u * a)
  map_add' a b := by simp only [localTopCoeff, mul_add, localCoeffNat_add]
  map_smul' c a := by
    simp only [localTopCoeff, mul_smul_comm, localCoeffNat_smul, smul_eq_mul,
      RingHom.id_apply]

/-- Every linear functional is exactly top-coefficient pairing with its
reversed-coefficient element, for every positive truncation length. -/
theorem localFrobenius_repr (ℓ : ℕ) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ) (a : LocalTruncated ℓ) :
    Λ a = localTopCoeff ℓ hℓ (localFrobeniusElement ℓ hℓ Λ * a) := by
  let u := localFrobeniusElement ℓ hℓ Λ
  have hmaps : Λ = localTopMulLinear ℓ hℓ u := by
    apply (localBasis ℓ).ext
    intro j
    rw [localBasis_apply]
    change Λ (localRoot ℓ ^ j.val) =
      localCoeffNat ℓ (u * localRoot ℓ ^ j.val) (ℓ - 1)
    rw [localCoeffNat_mul_root_pow ℓ j.val (ℓ - 1) (by omega)]
    have hjle : j.val ≤ ℓ - 1 := by omega
    rw [if_pos hjle]
    have hj' : ℓ - 1 - j.val < ℓ := by omega
    have hsub : ℓ - 1 - (ℓ - 1 - j.val) = j.val := by omega
    have hc := localFrobeniusElement_coeff ℓ hℓ Λ
      (⟨ℓ - 1 - j.val, hj'⟩ : Fin ℓ)
    simpa only [u, localCoeff, hsub] using hc.symm
  exact congrArg (fun f : LocalTruncated ℓ →ₗ[ℂ] ℂ => f a) hmaps

/-- No second local element can give the same top-coefficient functional. -/
theorem localFrobenius_unique (ℓ : ℕ) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ) (u : LocalTruncated ℓ)
    (hu : ∀ a : LocalTruncated ℓ,
      Λ a = localTopCoeff ℓ hℓ (u * a)) :
    u = localFrobeniusElement ℓ hℓ Λ := by
  apply local_eq_of_coeff ℓ
  intro j
  have hj' : ℓ - 1 - j.val < ℓ := by omega
  have htop := hu (localRoot ℓ ^ (ℓ - 1 - j.val))
  change Λ (localRoot ℓ ^ (ℓ - 1 - j.val)) =
    localCoeffNat ℓ (u * localRoot ℓ ^ (ℓ - 1 - j.val)) (ℓ - 1) at htop
  rw [localCoeffNat_mul_root_pow ℓ (ℓ - 1 - j.val) (ℓ - 1) (by omega)] at htop
  have hle : ℓ - 1 - j.val ≤ ℓ - 1 := Nat.sub_le _ _
  rw [if_pos hle] at htop
  have hsub : ℓ - 1 - (ℓ - 1 - j.val) = j.val := by omega
  rw [hsub] at htop
  have hcoeff : localCoeff ℓ u j = Λ (localRoot ℓ ^ (ℓ - 1 - j.val)) := by
    simpa only [localCoeff] using htop.symm
  exact hcoeff.trans (localFrobeniusElement_coeff ℓ hℓ Λ j).symm

#assert_trust kernel localRoot_pow_eq_zero
#assert_trust kernel localCoeffNat_mk
#assert_trust kernel localCoeffNat_root_pow
#assert_trust kernel localBasis
#assert_trust kernel localBasis_apply
#assert_trust kernel localBasis_repr
#assert_trust kernel localCoeffNat_mul
#assert_trust kernel localCoeffNat_mul_root_pow
#assert_trust kernel local_eq_of_coeff
#assert_trust kernel local_power_basis_sum
#assert_trust kernel localFrobeniusElement_coeff
#assert_trust kernel localFrobenius_repr
#assert_trust kernel localFrobenius_unique
#print axioms localFrobenius_unique

end
end NLA.Proofs.TR14
