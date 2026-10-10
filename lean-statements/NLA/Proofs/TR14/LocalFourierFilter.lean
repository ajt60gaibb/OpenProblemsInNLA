import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic
import LeanCert.Tactic.Verification

/-!
The finite root-of-unity coefficient filter used in the local interpolation
upper bound for TR-14. This module is independent of CRT, moment quotients,
tensor widths, and the frozen Target.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators Polynomial
noncomputable section

/-- Exactly the number of Fourier nodes for one root of multiplicity `ℓ`. -/
def localFourierCount (m ℓ : ℕ) : ℕ := (m - 1) * (ℓ - 1) + 1

theorem localFourierCount_pos (m ℓ : ℕ) : 0 < localFourierCount m ℓ := by
  simp [localFourierCount]

theorem localFourierCount_one (m : ℕ) : localFourierCount m 1 = 1 := by
  simp [localFourierCount]

/-- Orthogonality of the complete `N`-node geometric sum for a primitive
complex `N`th root, including `N=1`. -/
theorem primitive_fourier_sum {N : ℕ} (_hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (k : ℕ) :
    (∑ j : Fin N, (ζ ^ k) ^ j.val) =
      if N ∣ k then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  by_cases hdiv : N ∣ k
  · have hz : ζ ^ k = 1 := (hζ.pow_eq_one_iff_dvd k).mpr hdiv
    simp [hdiv, hz]
  · have hz : ζ ^ k ≠ 1 := fun he => hdiv ((hζ.pow_eq_one_iff_dvd k).mp he)
    have hpow : (ζ ^ k) ^ N = 1 := by
      rw [← pow_mul, mul_comm k N, pow_mul, hζ.pow_eq_one, one_pow]
    have hgeom := geom_sum_mul (ζ ^ k) N
    rw [hpow, sub_self] at hgeom
    have hzero : (∑ j ∈ Finset.range N, (ζ ^ k) ^ j) = 0 :=
      (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hz)
    simp [hdiv, hzero]

/-- The selected exponent is the sole multiple of `N` in the exact product
degree window after shifting by `N-(ℓ-1)`. -/
theorem local_fourier_cutoff (m ℓ : ℕ) (hm : 3 ≤ m) (_hℓ : 1 ≤ ℓ)
    (k : Fin (m * (ℓ - 1) + 1)) :
    localFourierCount m ℓ ∣
        k.val + (localFourierCount m ℓ - (ℓ - 1)) ↔
      k.val = ℓ - 1 := by
  let t := ℓ - 1
  let N := localFourierCount m ℓ
  have hN : 0 < N := localFourierCount_pos m ℓ
  have hm1 : m - 1 + 1 = m := by omega
  have hcount : N + t = m * t + 1 := by
    dsimp [N, localFourierCount]
    calc
      (m - 1) * t + 1 + t = ((m - 1) + 1) * t + 1 := by ring
      _ = m * t + 1 := by rw [hm1]
  have hNt : t < N := by
    have hmul : t ≤ (m - 1) * t := by
      simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ m - 1 by omega)
    change t < (m - 1) * t + 1
    omega
  have hpos : 0 < k.val + (N - t) := by omega
  have hmax : k.val + (N - t) < 2 * N := by
    have hk := k.isLt
    change k.val < m * t + 1 at hk
    omega
  change N ∣ k.val + (N - t) ↔ k.val = t
  constructor
  · intro hd
    have heq : k.val + (N - t) = N :=
      Nat.eq_of_dvd_of_lt_two_mul (Nat.ne_of_gt hpos) hd hmax
    omega
  · intro hk
    rw [hk, Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hNt)]

/-- The finite Fourier average recovers the coefficient at `ℓ-1` from
every coefficient vector through the full product-degree bound
`m*(ℓ-1)`, with the exact node count and including `ℓ=1`. -/
theorem primitive_fourier_coefficient (m ℓ : ℕ) (hm : 3 ≤ m) (hℓ : 1 ≤ ℓ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localFourierCount m ℓ))
    (a : Fin (m * (ℓ - 1) + 1) → ℂ) :
    (localFourierCount m ℓ : ℂ)⁻¹ *
      (∑ j : Fin (localFourierCount m ℓ),
        (ζ ^ j.val) ^ (localFourierCount m ℓ - (ℓ - 1)) *
          ∑ k : Fin (m * (ℓ - 1) + 1), a k * (ζ ^ j.val) ^ k.val) =
      a ⟨ℓ - 1, by
        have hm1 : 1 ≤ m := by omega
        have hmul := Nat.mul_le_mul_right (ℓ - 1) hm1
        have : ℓ - 1 ≤ m * (ℓ - 1) := by simpa using hmul
        omega⟩ := by
  let t := ℓ - 1
  let N := localFourierCount m ℓ
  let M := m * t
  have hN : 0 < N := localFourierCount_pos m ℓ
  have hNzero : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  let kt : Fin (M + 1) := ⟨t, by
    have hm1 : 1 ≤ m := by omega
    have hmul := Nat.mul_le_mul_right t hm1
    have : t ≤ m * t := by simpa using hmul
    omega⟩
  have hterm (k : Fin (M + 1)) :
      (∑ j : Fin N, (ζ ^ j.val) ^ (N - t) * (ζ ^ j.val) ^ k.val) =
        if k = kt then (N : ℂ) else 0 := by
    calc
      (∑ j : Fin N, (ζ ^ j.val) ^ (N - t) * (ζ ^ j.val) ^ k.val) =
        ∑ j : Fin N, (ζ ^ (k.val + (N - t))) ^ j.val := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (ζ ^ j.val) ^ (N - t) * (ζ ^ j.val) ^ k.val =
                (ζ ^ j.val) ^ ((N - t) + k.val) := by rw [pow_add]
            _ = (ζ ^ (k.val + (N - t))) ^ j.val := by
              simp only [← pow_mul]
              congr 1
              ac_rfl
      _ = if N ∣ k.val + (N - t) then (N : ℂ) else 0 :=
        primitive_fourier_sum hN hζ _
      _ = if k = kt then (N : ℂ) else 0 := by
        have hiff : (N ∣ k.val + (N - t)) ↔ k = kt := by
          constructor
          · intro hd
            apply Fin.ext
            exact (local_fourier_cutoff m ℓ hm hℓ k).mp hd
          · intro hk
            apply (local_fourier_cutoff m ℓ hm hℓ k).mpr
            exact congrArg Fin.val hk
        simp only [hiff]
  have hsum :
      (∑ j : Fin N, (ζ ^ j.val) ^ (N - t) *
          ∑ k : Fin (M + 1), a k * (ζ ^ j.val) ^ k.val) =
        (N : ℂ) * a kt := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      (∑ k : Fin (M + 1),
          ∑ j : Fin N, (ζ ^ j.val) ^ (N - t) *
            (a k * (ζ ^ j.val) ^ k.val)) =
        ∑ k : Fin (M + 1),
          a k * ∑ j : Fin N,
            (ζ ^ j.val) ^ (N - t) * (ζ ^ j.val) ^ k.val := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = ∑ k : Fin (M + 1), a k * (if k = kt then (N : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hterm]
      _ = (N : ℂ) * a kt := by
        rw [Finset.sum_eq_single kt]
        · simp [mul_comm]
        · intro k hk hne
          simp [hne]
        · simp
  change (N : ℂ)⁻¹ *
    (∑ j : Fin N, (ζ ^ j.val) ^ (N - t) *
      ∑ k : Fin (M + 1), a k * (ζ ^ j.val) ^ k.val) = a kt
  rw [hsum]
  simp [hNzero]

/-- The positive exponent used in the finite filter is exactly the inverse
character in the canonical local Fourier formula. -/
theorem local_fourier_phase (m ℓ : ℕ) (hm : 3 ≤ m) (_hℓ : 1 ≤ ℓ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localFourierCount m ℓ))
    (j : Fin (localFourierCount m ℓ)) :
    (ζ ^ j.val) ^ (localFourierCount m ℓ - (ℓ - 1)) =
      ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ := by
  let N := localFourierCount m ℓ
  let t := ℓ - 1
  have htN : t ≤ N := by
    have hmul : t ≤ (m - 1) * t := by
      simpa only [one_mul] using Nat.mul_le_mul_right t (show 1 ≤ m - 1 by omega)
    change t ≤ (m - 1) * t + 1
    omega
  have hpow : (ζ ^ j.val) ^ N = 1 := by
    rw [← pow_mul, mul_comm j.val N, pow_mul, hζ.pow_eq_one, one_pow]
  have hprod : (ζ ^ j.val) ^ (N - t) * (ζ ^ j.val) ^ t = 1 := by
    rw [← pow_add]
    convert hpow using 1
    congr 1
    omega
  exact eq_inv_of_mul_eq_one_left hprod

/-- Canonical inverse-character form of the exact finite Fourier coefficient
filter, for every coefficient vector through degree `m*(ℓ-1)`. -/
theorem primitive_fourier_coefficient_inv (m ℓ : ℕ) (hm : 3 ≤ m) (hℓ : 1 ≤ ℓ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localFourierCount m ℓ))
    (a : Fin (m * (ℓ - 1) + 1) → ℂ) :
    (localFourierCount m ℓ : ℂ)⁻¹ *
      (∑ j : Fin (localFourierCount m ℓ),
        ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ *
          ∑ k : Fin (m * (ℓ - 1) + 1), a k * (ζ ^ j.val) ^ k.val) =
      a ⟨ℓ - 1, by
        have hm1 : 1 ≤ m := by omega
        have hmul := Nat.mul_le_mul_right (ℓ - 1) hm1
        have : ℓ - 1 ≤ m * (ℓ - 1) := by simpa using hmul
        omega⟩ := by
  simpa only [local_fourier_phase m ℓ hm hℓ hζ] using
    primitive_fourier_coefficient m ℓ hm hℓ hζ a

/-- A primitive `N`th root always exists in `ℂ` for the exact positive node
count; its powers indexed by `Fin N` are the `N` Fourier nodes. -/
theorem local_fourier_primitive_exists (m ℓ : ℕ) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ (localFourierCount m ℓ) := by
  let N := localFourierCount m ℓ
  have hN : N ≠ 0 := Nat.ne_of_gt (localFourierCount_pos m ℓ)
  exact ⟨Complex.exp (2 * Real.pi * Complex.I / N),
    Complex.isPrimitiveRoot_exp N hN⟩

#assert_trust kernel localFourierCount
#assert_trust kernel primitive_fourier_sum
#assert_trust kernel local_fourier_cutoff
#assert_trust kernel primitive_fourier_coefficient
#assert_trust kernel local_fourier_phase
#assert_trust kernel primitive_fourier_coefficient_inv
#assert_trust kernel local_fourier_primitive_exists
#print axioms local_fourier_cutoff
#print axioms primitive_fourier_coefficient

end
end NLA.Proofs.TR14
