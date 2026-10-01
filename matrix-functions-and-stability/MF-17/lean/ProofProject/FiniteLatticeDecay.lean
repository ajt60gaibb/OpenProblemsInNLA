import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite sums of inverse-square lattice decay

Rounding the real center leaves five possibly undamped integer sites. Each
remaining side is bounded by a finite telescoping sum. All estimates are for
arbitrary finite subsets; no infinite-series bound is assumed.
-/

noncomputable section

namespace ProofProject

open Finset

private theorem inverse_sq_le_inverse_sub {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have heq : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp
    ring
  rw [heq]
  exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hx hx1) (by nlinarith)

/-- A finite telescoping majorant for either tail of the lattice. -/
theorem sum_range_shifted_inverse_square_le (N : ℕ) {s : ℝ} (hs : 0 < s) :
    (∑ k ∈ range N, 1 / ((k : ℝ) + s + 1) ^ 2) ≤ 1 / s := by
  calc
    _ ≤ ∑ k ∈ range N, (1 / ((k : ℝ) + s) - 1 / (((k + 1 : ℕ) : ℝ) + s)) := by
      apply sum_le_sum
      intro k _
      simpa only [Nat.cast_add, Nat.cast_one, add_right_comm (k : ℝ) 1 s] using
        inverse_sq_le_inverse_sub (by positivity : 0 < (k : ℝ) + s)
    _ = 1 / s - 1 / ((N : ℝ) + s) := by
      rw [sum_range_sub']
      simp
    _ ≤ 1 / s := sub_le_self _ (by positivity)

private def roundedLatticeProfile (k : ℤ) : ℝ :=
  1 / (1 + max 0 (|(k : ℝ)| - 2)) ^ 2

private theorem roundedLatticeProfile_nonneg (k : ℤ) : 0 ≤ roundedLatticeProfile k := by
  unfold roundedLatticeProfile
  positivity

private theorem roundedLatticeProfile_even : Function.Even roundedLatticeProfile := by
  intro k
  simp [roundedLatticeProfile]

private theorem roundedLatticeProfile_nat_shift (k : ℕ) :
    roundedLatticeProfile (↑(k + 3) : ℤ) = 1 / ((k : ℝ) + 2) ^ 2 := by
  unfold roundedLatticeProfile
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _), max_eq_right (by push_cast; linarith)]
  congr 2
  push_cast
  ring

private theorem roundedLatticeProfile_nat_sum_le (N : ℕ) :
    (∑ k ∈ range N, roundedLatticeProfile (k : ℤ)) ≤ 4 := by
  have hsum : (∑ k ∈ range (N + 3), roundedLatticeProfile (k : ℤ)) ≤ 4 := by
    rw [show N + 3 = 3 + N by omega, sum_range_add]
    have hhead : (∑ k ∈ range 3, roundedLatticeProfile (k : ℤ)) = 3 := by
      norm_num [sum_range_succ, roundedLatticeProfile]
    rw [hhead]
    have htail := sum_range_shifted_inverse_square_le N (s := 1) (by norm_num)
    have heq : (∑ k ∈ range N, roundedLatticeProfile ((3 + k : ℕ) : ℤ)) =
        ∑ k ∈ range N, 1 / ((k : ℝ) + 1 + 1) ^ 2 := by
      apply sum_congr rfl
      intro k _
      rw [Nat.add_comm 3 k, roundedLatticeProfile_nat_shift]
      congr 2
      ring
    rw [heq]
    simp only [div_one] at htail
    linarith
  exact (sum_le_sum_of_subset_of_nonneg (range_mono (by omega : N ≤ N + 3))
    (fun k _ _ => roundedLatticeProfile_nonneg k)).trans hsum

private theorem roundedLatticeProfile_sum_le (G : Finset ℤ) :
    (∑ k ∈ G, roundedLatticeProfile k) ≤ 7 := by
  let N := G.sup Int.natAbs
  have hsub : G ⊆ Icc (-(N : ℤ)) (N : ℤ) := by
    intro k hk
    have h : k.natAbs ≤ N := le_sup (f := Int.natAbs) hk
    have hi : (k.natAbs : ℤ) ≤ (N : ℤ) := Int.ofNat_le.mpr h
    rw [Int.natCast_natAbs] at hi
    exact mem_Icc.mpr (abs_le.mp hi)
  calc
    _ ≤ ∑ k ∈ Icc (-(N : ℤ)) (N : ℤ), roundedLatticeProfile k :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => roundedLatticeProfile_nonneg k)
    _ = 2 • (∑ k ∈ range (N + 1), roundedLatticeProfile (k : ℤ)) -
        roundedLatticeProfile 0 := sum_Icc_of_even_eq_range roundedLatticeProfile_even N
    _ ≤ 7 := by
      have h := roundedLatticeProfile_nat_sum_le (N + 1)
      have hz : roundedLatticeProfile 0 = 1 := by norm_num [roundedLatticeProfile]
      rw [hz, nsmul_eq_mul]
      norm_num only [Nat.cast_ofNat]
      linarith

/-- Five central sites and two telescoping tails give an absolute constant
seven, uniformly in the real translation and the finite subset of integers. -/
theorem sum_lattice_decay_le_seven (F : Finset ℤ) (R : ℝ) :
    (∑ n ∈ F, 1 / (1 + max 0 (|R - (n : ℝ)| - 3 / 2)) ^ 2) ≤ 7 := by
  let m : ℤ := round R
  have hm : |R - (m : ℝ)| ≤ 1 / 2 := abs_sub_round R
  have hpoint (n : ℤ) : 1 / (1 + max 0 (|R - (n : ℝ)| - 3 / 2)) ^ 2 ≤
      roundedLatticeProfile (n - m) := by
    have htri := abs_sub_le (n : ℝ) R (m : ℝ)
    rw [abs_sub_comm (n : ℝ) R] at htri
    have hd : |((n - m : ℤ) : ℝ)| - 2 ≤ |R - (n : ℝ)| - 3 / 2 := by
      rw [Int.cast_sub]
      linarith
    have hmax := max_le_max_left (0 : ℝ) hd
    unfold roundedLatticeProfile
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    linarith
  calc
    _ ≤ ∑ n ∈ F, roundedLatticeProfile (n - m) := sum_le_sum (fun n _ => hpoint n)
    _ = ∑ k ∈ F.image (fun n => n - m), roundedLatticeProfile k := by
      rw [sum_image]
      intro n _ k _ h
      dsimp only at h
      omega
    _ ≤ 7 := roundedLatticeProfile_sum_le _

/-- The unshifted natural tail starting at index two has bound one half. -/
theorem sum_nat_inverse_square_le_half (F : Finset ℕ)
    (hF : ∀ n ∈ F, 2 ≤ n) :
    (∑ n ∈ F, 1 / (1 + (n : ℝ)) ^ 2) ≤ 1 / 2 := by
  let G := F.image (fun n => n - 2)
  have heq : (∑ n ∈ F, 1 / (1 + (n : ℝ)) ^ 2) =
      ∑ k ∈ G, 1 / ((k : ℝ) + 2 + 1) ^ 2 := by
    rw [show G = F.image (fun n => n - 2) by rfl, sum_image]
    · apply sum_congr rfl
      intro n hn
      rw [Nat.cast_sub (hF n hn)]
      push_cast
      ring
    · intro n hn k hk he
      have hn' := hF n hn
      have hk' := hF k hk
      dsimp only at he
      omega
  rw [heq]
  have hsub : G ⊆ range (G.sup id + 1) := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup (f := id) hk))
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)).trans
    (sum_range_shifted_inverse_square_le (G.sup id + 1) (s := 2) (by norm_num))

end ProofProject
