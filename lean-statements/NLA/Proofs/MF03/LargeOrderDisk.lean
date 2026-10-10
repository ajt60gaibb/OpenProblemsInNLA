import Mathlib
import LeanCert.Tactic.Verification
import NLA.Proofs.MF03.Disk
import NLA.Proofs.MF03.CosineTail
import NLA.Proofs.MF03.WaveAtThree

/-! The reviewed conditional large-order disk bridge for MF-03. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

private noncomputable def waveRadiusTerm (k : ℕ) : ℝ :=
  (3 : ℝ) ^ k / (((2 * k).factorial : ℕ) : ℝ)

private theorem waveRadiusTerm_nonneg (k : ℕ) :
    0 ≤ waveRadiusTerm k := by
  unfold waveRadiusTerm
  positivity

private theorem waveRadiusTerm_summable : Summable waveRadiusTerm := by
  have h := (Real.hasSum_cosh (Real.sqrt 3)).summable
  apply h.congr
  intro k
  change (Real.sqrt 3) ^ (2 * k) / (((2 * k).factorial : ℕ) : ℝ) =
    (3 : ℝ) ^ k / (((2 * k).factorial : ℕ) : ℝ)
  rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem waveRadiusTerm_tail_nonneg :
    0 ≤ waveAtThree - 1 := by
  have hs := waveRadiusTerm_summable.sum_add_tsum_nat_add 1
  have htail : 0 ≤ ∑' k : ℕ, waveRadiusTerm (k + 1) :=
    tsum_nonneg (fun k => waveRadiusTerm_nonneg _)
  have hhead : ∑ i ∈ Finset.range 1, waveRadiusTerm i = 1 := by
    norm_num [waveRadiusTerm]
  change (∑' k : ℕ, waveRadiusTerm k) - 1 ≥ 0
  linarith

private theorem cosineTail_nonneg (m : ℕ) : 0 ≤ cosineTail m := by
  unfold cosineTail
  apply tsum_nonneg
  intro k
  unfold cosineFactor
  positivity

private noncomputable def radiusCoeff (Q : Polynomial ℂ) (m i : ℕ) : ℝ :=
  if i ≤ m then ‖Q.coeff i‖ * (3 : ℝ) ^ i else 0

private noncomputable def radiusTail (k : ℕ) : ℝ :=
  waveRadiusTerm (k + 1)

private theorem radiusCoeff_nonneg (Q : Polynomial ℂ) (m i : ℕ) :
    0 ≤ radiusCoeff Q m i := by
  unfold radiusCoeff
  split_ifs <;> positivity

private theorem radiusTail_nonneg (k : ℕ) : 0 ≤ radiusTail k :=
  waveRadiusTerm_nonneg _

private theorem radiusCoeff_summable (Q : Polynomial ℂ) (m : ℕ) :
    Summable (radiusCoeff Q m) := by
  apply summable_of_ne_finset_zero (s := Finset.range (m + 1))
  intro i hi
  have hnot : ¬ i ≤ m := by simpa [Finset.mem_range] using hi
  simp [radiusCoeff, hnot]

private theorem radiusTail_summable : Summable radiusTail := by
  change Summable (fun k => waveRadiusTerm (k + 1))
  exact (summable_nat_add_iff 1).2 waveRadiusTerm_summable

private theorem radiusTail_tsum :
    (∑' k : ℕ, radiusTail k) = waveAtThree - 1 := by
  have hs := waveRadiusTerm_summable.sum_add_tsum_nat_add 1
  have hhead : ∑ i ∈ Finset.range 1, waveRadiusTerm i = 1 := by
    norm_num [waveRadiusTerm]
  change (∑' k : ℕ, waveRadiusTerm (k + 1)) =
    (∑' k : ℕ, waveRadiusTerm k) - 1
  linarith

private theorem radiusCoeff_tsum (Q : Polynomial ℂ) (m : ℕ)
    (hQ0 : Q.coeff 0 = 1) :
    (∑' i : ℕ, radiusCoeff Q m i) =
      1 + ∑ j ∈ Finset.range m, ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1) := by
  have hout : ∀ i ∉ Finset.range (m + 1), radiusCoeff Q m i = 0 := by
    intro i hi
    have hnot : ¬ i ≤ m := by simpa [Finset.mem_range] using hi
    simp [radiusCoeff, hnot]
  have hzero : radiusCoeff Q m 0 = 1 := by simp [radiusCoeff, hQ0]
  calc
    (∑' i : ℕ, radiusCoeff Q m i) =
        ∑ i ∈ Finset.range (m + 1), radiusCoeff Q m i := tsum_eq_sum hout
    _ = radiusCoeff Q m 0 +
        ∑ j ∈ Finset.range m, radiusCoeff Q m (j + 1) :=
      by simpa only [add_comm] using
        (Finset.sum_range_succ' (fun i => radiusCoeff Q m i) m)
    _ = 1 + ∑ j ∈ Finset.range m,
        ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1) := by
      rw [hzero]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < m := Finset.mem_range.mp hj
      have hjle : j + 1 ≤ m := by omega
      simp [radiusCoeff, hjle]

private theorem pade_coeff_difference
    (m : ℕ) (P Q : Polynomial ℂ)
    (hpair : NLA.Statements.MF03.NormalizedPadeRepresentation m P Q)
    (j : ℕ) (hj : j < m) :
    P.coeff (j + 1) - Q.coeff (j + 1) =
      ∑ i ∈ Finset.range (j + 1),
        Q.coeff i / ((2 * (j + 1 - i)).factorial : ℂ) := by
  have hcoeff := hpair.2.2.2 (j + 1) (by omega : j + 1 ≤ 2 * m)
  rw [Finset.sum_range_succ] at hcoeff
  have hlast : Q.coeff (j + 1) /
      ((2 * (j + 1 - (j + 1))).factorial : ℂ) = Q.coeff (j + 1) := by
    norm_num
  rw [hlast] at hcoeff
  linear_combination -hcoeff

private theorem weighted_pade_term
    (Q : Polynomial ℂ) (m j i : ℕ) (hj : j < m) (hi : i ≤ j) :
    ‖Q.coeff i / ((2 * (j + 1 - i)).factorial : ℂ)‖ * (3 : ℝ) ^ (j + 1) =
      radiusCoeff Q m i * radiusTail (j - i) := by
  have hile : i ≤ m := by omega
  have hsub : j + 1 - i = (j - i) + 1 := by omega
  have hsum : i + ((j - i) + 1) = j + 1 := by omega
  simp only [radiusCoeff, if_pos hile, radiusTail, waveRadiusTerm]
  rw [norm_div, Complex.norm_natCast]
  rw [hsub, ← hsum, pow_add]
  ring

private theorem weighted_pade_coeff_le
    (m : ℕ) (P Q : Polynomial ℂ)
    (hpair : NLA.Statements.MF03.NormalizedPadeRepresentation m P Q)
    (j : ℕ) (hj : j < m) :
    ‖P.coeff (j + 1) - Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1) ≤
      ∑ i ∈ Finset.range (j + 1),
        radiusCoeff Q m i * radiusTail (j - i) := by
  rw [pade_coeff_difference m P Q hpair j hj]
  have hnorm := norm_sum_le (Finset.range (j + 1))
    (fun i => Q.coeff i / ((2 * (j + 1 - i)).factorial : ℂ))
  have hpow : 0 ≤ (3 : ℝ) ^ (j + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnorm hpow
  rw [Finset.sum_mul] at hmul
  calc
    ‖∑ i ∈ Finset.range (j + 1),
        Q.coeff i / ((2 * (j + 1 - i)).factorial : ℂ)‖ * (3 : ℝ) ^ (j + 1) ≤
        ∑ i ∈ Finset.range (j + 1),
          ‖Q.coeff i / ((2 * (j + 1 - i)).factorial : ℂ)‖ *
            (3 : ℝ) ^ (j + 1) := hmul
    _ = ∑ i ∈ Finset.range (j + 1),
          radiusCoeff Q m i * radiusTail (j - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hile : i ≤ j := by
        have hilt : i < j + 1 := Finset.mem_range.mp hi
        omega
      exact weighted_pade_term Q m j i hj hile

private theorem pade_numerator_budget
    (m : ℕ) (P Q : Polynomial ℂ)
    (hpair : NLA.Statements.MF03.NormalizedPadeRepresentation m P Q) :
    (∑ j ∈ Finset.range (m + 1),
      ‖P.coeff j - Q.coeff j‖ * (3 : ℝ) ^ j) ≤
      (1 + ∑ j ∈ Finset.range m,
        ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) *
        (waveAtThree - 1) := by
  have hQ0 : Q.coeff 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hpair.2.2.1
  have hP0 : P.coeff 0 = 1 := by
    have h := hpair.2.2.2 0 (by omega : 0 ≤ 2 * m)
    simpa [Finset.sum_range_succ, hQ0] using h.symm
  let b := radiusCoeff Q m
  let g := radiusTail
  let c : ℕ → ℝ := fun j =>
    ∑ i ∈ Finset.range (j + 1), b i * g (j - i)
  have hb : Summable b := radiusCoeff_summable Q m
  have hg : Summable g := radiusTail_summable
  have hbn : ∀ i, 0 ≤ b i := fun i => radiusCoeff_nonneg Q m i
  have hgn : ∀ k, 0 ≤ g k := radiusTail_nonneg
  have hprod : Summable (fun x : ℕ × ℕ => b x.1 * g x.2) :=
    Summable.mul_of_nonneg hb hg hbn hgn
  have hc : Summable c :=
    summable_sum_mul_range_of_summable_mul hprod
  have hcn : ∀ j, 0 ≤ c j := by
    intro j
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hbn i) (hgn (j - i))
  have hCauchy : (∑' i : ℕ, b i) * (∑' k : ℕ, g k) =
      ∑' j : ℕ, c j :=
    hb.tsum_mul_tsum_eq_tsum_sum_range hg hprod
  have hNstart :
      (∑ j ∈ Finset.range (m + 1),
        ‖P.coeff j - Q.coeff j‖ * (3 : ℝ) ^ j) =
      ∑ j ∈ Finset.range m,
        ‖P.coeff (j + 1) - Q.coeff (j + 1)‖ *
          (3 : ℝ) ^ (j + 1) := by
    rw [Finset.sum_range_succ']
    simp [hP0, hQ0]
  rw [hNstart]
  calc
    (∑ j ∈ Finset.range m,
      ‖P.coeff (j + 1) - Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) ≤
      ∑ j ∈ Finset.range m, c j := by
        apply Finset.sum_le_sum
        intro j hj
        exact weighted_pade_coeff_le m P Q hpair j (Finset.mem_range.mp hj)
    _ ≤ ∑' j : ℕ, c j := hc.sum_le_tsum (Finset.range m) (fun j hj => hcn j)
    _ = (∑' i : ℕ, b i) * (∑' k : ℕ, g k) := hCauchy.symm
    _ = (1 + ∑ j ∈ Finset.range m,
          ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) *
          (waveAtThree - 1) := by
      rw [radiusCoeff_tsum Q m hQ0, radiusTail_tsum]

private theorem pade_tail_geometric_budget
    (m : ℕ) (hm : 16 ≤ m) (Q : Polynomial ℂ)
    (hcoeff : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      ‖Q.coeff j‖ ≤ (cosineTail m) ^ j) :
    (∑ j ∈ Finset.range m,
      ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) *
        (1 - 3 * cosineTail m) ≤ 3 * cosineTail m := by
  let S := cosineTail m
  let x := 3 * S
  have hSnonneg : 0 ≤ S := cosineTail_nonneg m
  have hxnonneg : 0 ≤ x := by dsimp [x]; positivity
  have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by positivity
  have htail := cosineTail_lt_one_div_nine_mul m (by omega : 1 ≤ m)
  have htailmul : S * (9 * (m : ℝ)) < 1 := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 9 * m)).mp
    simpa [S] using htail
  have hxlt : x < 1 := by
    have hsmul : 0 ≤ S * ((m : ℝ) - 16) :=
      mul_nonneg hSnonneg (by linarith)
    dsimp [x]
    nlinarith
  have hTle :
      (∑ j ∈ Finset.range m,
        ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) ≤
      ∑ j ∈ Finset.range m, x ^ (j + 1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hbound := hcoeff (j + 1) (by omega) (by omega)
    calc
      ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1) ≤
          S ^ (j + 1) * (3 : ℝ) ^ (j + 1) :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = x ^ (j + 1) := by simp [x, mul_pow, mul_comm]
  have hgeomsum :
      (∑ j ∈ Finset.range m, x ^ (j + 1)) * (1 - x) =
        x * (1 - x ^ m) := by
    have hshift : (∑ j ∈ Finset.range m, x ^ (j + 1)) =
        x * ∑ j ∈ Finset.range m, x ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ]
      ring
    rw [hshift]
    calc
      (x * ∑ j ∈ Finset.range m, x ^ j) * (1 - x) =
          x * ((∑ j ∈ Finset.range m, x ^ j) * (1 - x)) := by ring
      _ = x * (1 - x ^ m) := by rw [geom_sum_mul_neg]
  have hmul := mul_le_mul_of_nonneg_right hTle (by linarith : 0 ≤ 1 - x)
  calc
    (∑ j ∈ Finset.range m,
      ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) *
        (1 - 3 * cosineTail m) ≤
      (∑ j ∈ Finset.range m, x ^ (j + 1)) * (1 - x) := by
        simpa [x, S] using hmul
    _ = x * (1 - x ^ m) := hgeomsum
    _ ≤ 3 * cosineTail m := by
      have hpow : 0 ≤ x ^ m := pow_nonneg hxnonneg m
      dsimp [x, S]
      nlinarith [mul_nonneg hxnonneg hpow]

private theorem largeOrder_budget_arithmetic
    (m : ℕ) (hm : 16 ≤ m) (T N : ℝ)
    (hTnonneg : 0 ≤ T)
    (hTgeom : T * (1 - 3 * cosineTail m) ≤ 3 * cosineTail m)
    (hN : N ≤ (1 + T) * (waveAtThree - 1)) :
    T < 1 ∧ N ≤ 2 * (1 - T) := by
  let S := cosineTail m
  have hSnonneg : 0 ≤ S := cosineTail_nonneg m
  have hSlt : 6 * S < (1 : ℝ) / 24 := by
    have htail := cosineTail_lt_one_div_nine_mul m (by omega : 1 ≤ m)
    have hm16 : (16 : ℝ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < m := by positivity
    have hmono : 6 / (9 * (m : ℝ)) ≤ (1 : ℝ) / 24 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 9 * m)).2
      nlinarith
    have hscaled : 6 * S < 6 / (9 * (m : ℝ)) := by
      simpa [S, div_eq_mul_inv, mul_assoc] using
        (mul_lt_mul_of_pos_left htail (by norm_num : (0 : ℝ) < 6))
    exact lt_of_lt_of_le hscaled hmono
  have hSsmall : 3 * S < 1 / 48 := by nlinarith
  have hden : 0 < 1 - 6 * S := by linarith
  have hTlt : T < 1 := by
    by_contra h
    have hTge : 1 ≤ T := le_of_not_gt h
    nlinarith [hTgeom]
  have hBgeom : (1 + T) * (1 - 6 * S) ≤ 1 - T := by
    nlinarith [hTgeom]
  have hwave := largeOrder_numeric_margin m hm
  have hnum : waveAtThree - 1 ≤
      ((2 : ℝ) - 13 / 6095) * (1 - 6 * S) := by
    apply (div_le_iff₀ hden).mp
    simpa [S] using hwave
  have hBnonneg : 0 ≤ 1 + T := by linarith
  have hCnonneg : 0 ≤ (2 : ℝ) - 13 / 6095 := by norm_num
  have hmiddle : (1 + T) * (waveAtThree - 1) ≤
      ((2 : ℝ) - 13 / 6095) * (1 - T) := by
    calc
      (1 + T) * (waveAtThree - 1) ≤
          (1 + T) * (((2 : ℝ) - 13 / 6095) * (1 - 6 * S)) :=
        mul_le_mul_of_nonneg_left hnum hBnonneg
      _ = ((2 : ℝ) - 13 / 6095) * ((1 + T) * (1 - 6 * S)) := by ring
      _ ≤ ((2 : ℝ) - 13 / 6095) * (1 - T) :=
        mul_le_mul_of_nonneg_left hBgeom hCnonneg
  refine ⟨hTlt, ?_⟩
  have hTpos : 0 ≤ 1 - T := by linarith
  calc
    N ≤ (1 + T) * (waveAtThree - 1) := hN
    _ ≤ ((2 : ℝ) - 13 / 6095) * (1 - T) := hmiddle
    _ ≤ 2 * (1 - T) := by nlinarith

/-- A normalized large-order Padé pair with the manuscript's denominator
coefficient tail bound is pole-free and satisfies the frozen disk inequality. -/
theorem largeOrder_disk_of_tail_coefficients
    (m : ℕ) (hm : 16 ≤ m) (P Q : Polynomial ℂ)
    (hpair : NLA.Statements.MF03.NormalizedPadeRepresentation m P Q)
    (hcoeff : ∀ j : ℕ, 1 ≤ j → j ≤ m →
      ‖Q.coeff j‖ ≤ (cosineTail m) ^ j) :
    ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
      Q.eval z ≠ 0 ∧
        ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) := by
  let T : ℝ := ∑ j ∈ Finset.range m,
    ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)
  let N : ℝ := ∑ j ∈ Finset.range (m + 1),
    ‖P.coeff j - Q.coeff j‖ * (3 : ℝ) ^ j
  have hQ0 : Q.coeff 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hpair.2.2.1
  have hTnonneg : 0 ≤ T := by
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hTgeom : T * (1 - 3 * cosineTail m) ≤ 3 * cosineTail m := by
    simpa only [T] using pade_tail_geometric_budget m hm Q hcoeff
  have hNbudget : N ≤ (1 + T) * (waveAtThree - 1) := by
    simpa only [N, T] using pade_numerator_budget m P Q hpair
  obtain ⟨hTlt, hNbound⟩ :=
    largeOrder_budget_arithmetic m hm T N hTnonneg hTgeom hNbudget
  exact disk_bound_of_coefficient_tail P Q m hpair.1 hpair.2.1 hQ0
    hTlt hNbound

#assert_trust kernel largeOrder_disk_of_tail_coefficients
#print axioms largeOrder_disk_of_tail_coefficients

end NLA.Proofs.MF03
