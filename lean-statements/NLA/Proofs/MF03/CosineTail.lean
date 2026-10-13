import Mathlib
import LeanCert.Tactic.Verification

/-! The exact cosine-product tail estimate used in the large-order MF-03 proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

/-- The factor indexed by the positive integer `ν` in the cosine product. -/
noncomputable def cosineFactor (ν : ℕ) : ℝ :=
  1 / (Real.pi ^ 2 * ((ν : ℝ) - 1 / 2) ^ 2)

/-- The product-factor tail strictly after the first `m` factors. -/
noncomputable def cosineTail (m : ℕ) : ℝ :=
  ∑' k : ℕ, cosineFactor (m + k + 1)

private noncomputable def telescopingTerm (m k : ℕ) : ℝ :=
  1 / ((m + k : ℕ) : ℝ) - 1 / ((m + k + 1 : ℕ) : ℝ)

private theorem telescopingTerm_nonneg (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    0 ≤ telescopingTerm m k := by
  have hn : 0 < ((m + k : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < m + k)
  have hle : ((m + k : ℕ) : ℝ) ≤ ((m + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : m + k ≤ m + k + 1)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hn hle)

private theorem telescopingTerm_hasSum (m : ℕ) (hm : 1 ≤ m) :
    HasSum (telescopingTerm m) (1 / (m : ℝ)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (telescopingTerm_nonneg m hm) _).2
  have hsums (N : ℕ) :
      (∑ k ∈ Finset.range N, telescopingTerm m k) =
        1 / (m : ℝ) - 1 / ((m + N : ℕ) : ℝ) := by
    induction N with
    | zero => simp [telescopingTerm]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp [telescopingTerm]
        push_cast
        ring
  simp only [hsums]
  have hzero :
      Filter.Tendsto (fun N : ℕ => 1 / ((m + N : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat m)
    simpa [Function.comp_def, Nat.add_comm] using h
  simpa using hzero.const_sub (1 / (m : ℝ))

private theorem cosineFactor_le_tel (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    cosineFactor (m + k + 1) ≤ (1 / Real.pi ^ 2) * telescopingTerm m k := by
  let n : ℝ := ((m + k : ℕ) : ℝ)
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (by omega : 0 < m + k)
  have hprod : 0 < n * (n + 1) := mul_pos hn (by linarith)
  have hmid : n * (n + 1) ≤ (n + 1 / 2) ^ 2 := by
    nlinarith
  have hfactor :
      cosineFactor (m + k + 1) = 1 / (Real.pi ^ 2 * (n + 1 / 2) ^ 2) := by
    simp only [cosineFactor, n]
    push_cast
    ring
  have htel : telescopingTerm m k = 1 / (n * (n + 1)) := by
    dsimp [telescopingTerm, n]
    push_cast
    field_simp
    ring
  rw [hfactor, htel]
  rw [one_div_mul_one_div]
  exact one_div_le_one_div_of_le (mul_pos (pow_pos Real.pi_pos _) hprod)
    (mul_le_mul_of_nonneg_left hmid (pow_nonneg Real.pi_pos.le _))

/-- The exact bound on the tail of cosine-product factor reciprocals. -/
theorem cosineTail_lt_one_div_nine_mul
    (m : ℕ) (hm : 1 ≤ m) :
    cosineTail m < 1 / (9 * (m : ℝ)) := by
  have htel := (telescopingTerm_hasSum m hm).summable
  have hscaled : Summable (fun k : ℕ => (1 / Real.pi ^ 2) * telescopingTerm m k) :=
    htel.mul_left _
  have hfactor_nonneg (k : ℕ) : 0 ≤ cosineFactor (m + k + 1) := by
    unfold cosineFactor
    positivity
  have hfactor_sum : Summable (fun k : ℕ => cosineFactor (m + k + 1)) :=
    Summable.of_nonneg_of_le hfactor_nonneg (cosineFactor_le_tel m hm) hscaled
  have hbound : cosineTail m ≤ 1 / (Real.pi ^ 2 * (m : ℝ)) := by
    unfold cosineTail
    calc
      (∑' k : ℕ, cosineFactor (m + k + 1)) ≤
          ∑' k : ℕ, (1 / Real.pi ^ 2) * telescopingTerm m k :=
        hfactor_sum.tsum_le_tsum (cosineFactor_le_tel m hm) hscaled
      _ = 1 / (Real.pi ^ 2 * (m : ℝ)) := by
        rw [tsum_mul_left, (telescopingTerm_hasSum m hm).tsum_eq,
          one_div_mul_one_div]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  exact hbound.trans_lt (one_div_lt_one_div_of_lt (by positivity)
    (mul_lt_mul_of_pos_right hpi hmpos))

#print axioms cosineTail_lt_one_div_nine_mul
#assert_trust kernel cosineTail_lt_one_div_nine_mul

end NLA.Proofs.MF03
