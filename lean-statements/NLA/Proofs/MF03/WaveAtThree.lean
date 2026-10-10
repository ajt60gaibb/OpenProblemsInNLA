import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.CosineTail

/-! The exact value-at-three series bound and large-order numerical margin in MF-03. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

private noncomputable def waveTerm (j : ℕ) : ℝ :=
  (3 : ℝ) ^ j / (((2 * j).factorial : ℕ) : ℝ)

/-- The real value at three of the entire series with coefficients `1/(2j)!`. -/
noncomputable def waveAtThree : ℝ :=
  ∑' j : ℕ, (3 : ℝ) ^ j / (((2 * j).factorial : ℕ) : ℝ)

private theorem waveTerm_nonneg (j : ℕ) : 0 ≤ waveTerm j := by
  unfold waveTerm
  positivity

private theorem waveTerm_summable : Summable waveTerm := by
  have h := (Real.hasSum_cosh (Real.sqrt 3)).summable
  apply h.congr
  intro j
  change (Real.sqrt 3) ^ (2 * j) / (((2 * j).factorial : ℕ) : ℝ) =
    (3 : ℝ) ^ j / (((2 * j).factorial : ℕ) : ℝ)
  rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem waveTerm_next (j : ℕ) :
    waveTerm (j + 1) = waveTerm j *
      (3 / (((2 * j + 2 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ))) := by
  have hfac : (((2 * (j + 1)).factorial : ℕ) : ℝ) =
      (((2 * j + 2 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) *
        (((2 * j).factorial : ℕ) : ℝ) := by
    have hidx : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [hidx, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  unfold waveTerm
  rw [hfac, pow_succ]
  have h1 : (0 : ℝ) < (((2 * j).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h2 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) := by positivity
  have h3 : (0 : ℝ) < ((2 * j + 2 : ℕ) : ℝ) := by positivity
  field_simp

private theorem waveTerm_next_le (j : ℕ) (hj : 3 ≤ j) :
    waveTerm (j + 1) ≤ waveTerm j * (3 / 56) := by
  rw [waveTerm_next]
  have hden : (56 : ℝ) ≤
      (((2 * j + 2 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) := by
    have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
    push_cast
    nlinarith
  apply mul_le_mul_of_nonneg_left _ (waveTerm_nonneg j)
  exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3)
    (by norm_num : (0 : ℝ) < 56) hden

private theorem waveTerm_tail_le (k : ℕ) :
    waveTerm (3 + k) ≤ (3 / 80 : ℝ) * (3 / 56 : ℝ) ^ k := by
  induction k with
  | zero => norm_num [waveTerm]
  | succ k ih =>
      have hj : 3 ≤ 3 + k := by omega
      have h := waveTerm_next_le (3 + k) hj
      have hr : (0 : ℝ) ≤ 3 / 56 := by norm_num
      calc
        waveTerm (3 + (k + 1)) = waveTerm ((3 + k) + 1) := by congr 1
        _ ≤ waveTerm (3 + k) * (3 / 56) := h
        _ ≤ ((3 / 80 : ℝ) * (3 / 56 : ℝ) ^ k) * (3 / 56) :=
          mul_le_mul_of_nonneg_right ih hr
        _ = (3 / 80 : ℝ) * (3 / 56 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

/-- The manuscript's exact rational estimate for the value at three. -/
theorem waveAtThree_le_rational :
    waveAtThree ≤ (6179 : ℝ) / 2120 := by
  have hgeom : Summable (fun k : ℕ => (3 / 80 : ℝ) * (3 / 56 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail : (∑' k : ℕ, waveTerm (k + 3)) ≤
      ∑' k : ℕ, (3 / 80 : ℝ) * (3 / 56 : ℝ) ^ k :=
    ((summable_nat_add_iff 3).2 waveTerm_summable).tsum_le_tsum
      (fun k => by simpa [Nat.add_comm] using waveTerm_tail_le k) hgeom
  have hsum : (∑' k : ℕ, (3 / 80 : ℝ) * (3 / 56 : ℝ) ^ k) = 21 / 530 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hsplit := waveTerm_summable.sum_add_tsum_nat_add 3
  have hhead : (∑ i ∈ Finset.range 3, waveTerm i) = 23 / 8 := by
    norm_num [waveTerm, Finset.sum_range_succ]
  change (∑' j : ℕ, waveTerm j) ≤ (6179 : ℝ) / 2120
  rw [← hsplit, hhead]
  nlinarith [htail, hsum]

/-- The exact uniform margin left after the large-order tail estimate. -/
theorem largeOrder_numeric_margin
    (m : ℕ) (hm : 16 ≤ m) :
    (waveAtThree - 1) / (1 - 6 * cosineTail m) ≤
      (2 : ℝ) - 13 / 6095 := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have htail := cosineTail_lt_one_div_nine_mul m (by omega : 1 ≤ m)
  have hsmall : 6 * cosineTail m < (1 : ℝ) / 24 := by
    have hmono : 6 / (9 * (m : ℝ)) ≤ (1 : ℝ) / 24 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * m)).2
      have : (0 : ℝ) ≤ 9 * m := by positivity
      nlinarith
    have hscaled : 6 * cosineTail m < 6 / (9 * (m : ℝ)) := by
      simpa [div_eq_mul_inv, mul_assoc] using
        (mul_lt_mul_of_pos_left htail (by norm_num : (0 : ℝ) < 6))
    exact lt_of_lt_of_le hscaled hmono
  have hden : (0 : ℝ) < 1 - 6 * cosineTail m := by linarith
  have hnum := waveAtThree_le_rational
  apply (div_le_iff₀ hden).2
  have hden23 : (23 : ℝ) / 24 ≤ 1 - 6 * cosineTail m := by linarith
  calc
    waveAtThree - 1 ≤ (6179 : ℝ) / 2120 - 1 := sub_le_sub_right hnum 1
    _ = ((2 : ℝ) - 13 / 6095) * (23 / 24) := by norm_num
    _ ≤ ((2 : ℝ) - 13 / 6095) * (1 - 6 * cosineTail m) :=
      mul_le_mul_of_nonneg_left hden23 (by norm_num)

#print axioms waveAtThree_le_rational
#assert_trust kernel waveAtThree_le_rational
#print axioms largeOrder_numeric_margin
#assert_trust kernel largeOrder_numeric_margin

end NLA.Proofs.MF03
