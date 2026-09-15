/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Heights
import NLA.MF24.Polynomial
import NLA.MF24.NormBasics
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open scoped BigOperators

lemma positive_stride_multiple (m : ℕ) (v : Fin (dimension m))
    (hv : 0 < v.val ∧ stride m ∣ v.val) :
    ∃ j ∈ Finset.Icc 1 m, v.val = stride m * j := by
  obtain ⟨j, hj⟩ := hv.2
  have hj1 : 1 ≤ j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    simp only [hj0, mul_zero] at hj
    omega
  have hjm : j ≤ m := by
    have hb := v.isLt
    rw [dimension_eq] at hb
    by_contra hn
    have hlarge : m + 1 ≤ j := by omega
    have hmul := Nat.mul_le_mul_left (stride m) hlarge
    have hD := stride_pos m
    nlinarith
  exact ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjm⟩, hj⟩

lemma first_support_card (m : ℕ) :
    (Finset.univ.filter (fun v : Fin (dimension m) =>
      0 < v.val ∧ stride m ∣ v.val)).card = m := by
  classical
  let S := Finset.univ.filter (fun v : Fin (dimension m) =>
    0 < v.val ∧ stride m ∣ v.val)
  have heq : S.card = (Finset.Icc 1 m).card := by
    apply Finset.card_bij (fun (v : Fin (dimension m)) (_ : v ∈ S) => v.val / stride m)
    · intro v hv
      have hp : 0 < v.val ∧ stride m ∣ v.val := (Finset.mem_filter.mp hv).2
      obtain ⟨j, hj, he⟩ := positive_stride_multiple m v hp
      rw [he, Nat.mul_div_cancel_left j (stride_pos m)]
      exact hj
    · intro v hv w hw he
      have hpv : stride m ∣ v.val := (Finset.mem_filter.mp hv).2.2
      have hpw : stride m ∣ w.val := (Finset.mem_filter.mp hw).2.2
      apply Fin.ext
      calc v.val = (v.val / stride m) * stride m := (Nat.div_mul_cancel hpv).symm
        _ = (w.val / stride m) * stride m := by rw [he]
        _ = w.val := Nat.div_mul_cancel hpw
    · intro j hj
      have hj1 := (Finset.mem_Icc.mp hj).1
      have hjm := (Finset.mem_Icc.mp hj).2
      let v : Fin (dimension m) := ⟨stride m * j, by
        rw [dimension_eq]
        have hmul := Nat.mul_le_mul_left (stride m) hjm
        nlinarith⟩
      refine ⟨v, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · exact Nat.mul_pos (stride_pos m) (by omega)
        · exact dvd_mul_right _ _
      · exact Nat.mul_div_cancel_left j (stride_pos m)
  simpa [S] using heq

lemma heightX_stride_multiple (m : ℕ) (j : ℕ) (hj : j ∈ Finset.Icc 1 m) :
    heightX m (stride m * j) = 2 := by
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hjm := (Finset.mem_Icc.mp hj).2
  have he : stride m * j = j * (m + 1) + j := by unfold stride; ring
  rw [he, heightX_grid m j j (by omega)]
  simp [hj1]

lemma heightY_terminal (m : ℕ) (hm : 1 ≤ m) :
    heightY m (stride m * m) = 2 := by
  have he : stride m * m = m * (m + 1) + m := by unfold stride; ring
  rw [he, heightY_grid m m m (by omega)]
  simp [hm]

lemma first_row_energy (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : 1 < t)
    (r : Fin (dimension m)) (hr : r.val = 0) :
    ∑ s : Fin (dimension m),
      ‖polyEval (matrixX m t) (testPolynomial m) r s‖ ^ 2 = t ^ 4 * (m : ℝ) := by
  have hh := source_words_eq_height_shifts m hm t ht
  have ht0 : 0 < t := by linarith
  have he : ∀ s : Fin (dimension m),
      ‖polyEval (matrixX m t) (testPolynomial m) r s‖ ^ 2 =
        if 0 < s.val ∧ stride m ∣ s.val then t ^ 4 else 0 := by
    intro s
    rw [hh.1, polynomial_entries m hm (fun v => heightX m v.val) t ht0 r s]
    simp only [hr, Nat.sub_zero]
    by_cases hs : 0 < s.val ∧ stride m ∣ s.val
    · obtain ⟨j, hj, he⟩ := positive_stride_multiple m s hs
      have hs2 : heightX m s.val = 2 := by rw [he]; exact heightX_stride_multiple m j hj
      simp only [if_pos hs]
      simp [hs2, hh.2.2.1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg t), ← pow_mul]
    · simp [hs]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, first_support_card]
  ring

lemma denominator_polynomial_ne_zero (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) : polyEval (matrixY m t) (testPolynomial m) ≠ 0 := by
  have hh := source_words_eq_height_shifts m hm t ht
  have ht0 : 0 < t := by linarith
  let r : Fin (dimension m) := ⟨0, lt_of_lt_of_le Nat.zero_lt_one (dimension_pos m)⟩
  let s : Fin (dimension m) := ⟨stride m * m, by rw [dimension_eq]; nlinarith⟩
  have hentry : polyEval (matrixY m t) (testPolynomial m) r s = (t ^ 2 : ℝ) := by
    rw [hh.2.1, polynomial_entries m hm (fun v => heightY m v.val) t ht0 r s]
    have hpos : 0 < stride m * m := Nat.mul_pos (stride_pos m) (by omega)
    have hdvd : stride m ∣ stride m * m := dvd_mul_right _ _
    simp [r, s, hpos, hdvd, heightY_terminal m (by omega), hh.2.2.2.1]
  intro hz
  have he := congrArg (fun A : Square (dimension m) => A r s) hz
  rw [hentry] at he
  have htne : ((t ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 (ne_of_gt ht0))
  exact htne he

theorem first_row_and_nonzero (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    (∀ r : Fin (dimension m), r.val = 0 →
      ∑ s : Fin (dimension m),
        ‖polyEval (matrixX m t) (testPolynomial m) r s‖ ^ 2 = t ^ 4 * (m : ℝ)) ∧
    polyEval (matrixY m t) (testPolynomial m) ≠ 0 :=
  ⟨first_row_energy m hm t ht, denominator_polynomial_ne_zero m hm t ht⟩

theorem polynomial_numerator_bound (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    t ^ 2 * Real.sqrt (m : ℝ) ≤
      spectralNorm (polyEval (matrixX m t) (testPolynomial m)) := by
  let r : Fin (dimension m) := ⟨0, lt_of_lt_of_le Nat.zero_lt_one (dimension_pos m)⟩
  have he := row_energy_le_spectralNorm_sq (polyEval (matrixX m t) (testPolynomial m)) r
  rw [first_row_energy m hm t ht r rfl] at he
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg t) (Real.sqrt_nonneg _))
    (spectralNorm_nonneg _)).mp
  simpa [mul_pow, Real.sq_sqrt (show 0 ≤ (m : ℝ) by positivity), ← pow_mul] using he

#assert_trust kernel first_row_and_nonzero
#assert_trust kernel polynomial_numerator_bound
#print axioms first_row_and_nonzero
#print axioms polynomial_numerator_bound

end NLA.MF24
