import ProofProject.ScalarEigenvalues
import ProofProject.BasisEnergy

/-!
# Scalar diagonal approximation by elementary patterns

The estimates in this file isolate the finite scalar part of the separated
spectral construction from the Hilbert-space operator-norm estimates.
-/

noncomputable section

open scoped BigOperators

namespace ProofProject

/-- A finite positive sequence that doubles at every step has reciprocal sum
at most twice its first reciprocal. -/
theorem sum_reciprocal_le_of_doubling (n : ℕ) (y : Fin (n + 1) → ℝ)
    (hy : ∀ j, 0 < y j)
    (hd : ∀ j : Fin n, 2 * y j.castSucc ≤ y j.succ) :
    ∑ j, 1 / y j ≤ 2 / y 0 := by
  induction n with
  | zero =>
    simpa using (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (hy 0).le)
  | succ n ih =>
    have ht := ih (fun j => y j.succ) (fun j => hy j.succ)
      (fun j => hd j.succ)
    have hstep : 2 / y (Fin.succ 0) ≤ 1 / y 0 := by
      apply (div_le_div_iff₀ (hy _) (hy _)).2
      simpa using hd 0
    rw [Fin.sum_univ_succ]
    calc
      _ ≤ 1 / y 0 + 2 / y (Fin.succ 0) := add_le_add le_rfl ht
      _ ≤ 1 / y 0 + 1 / y 0 := add_le_add le_rfl hstep
      _ = _ := by ring

/-- The same reciprocal bound starts at any coordinate of the sequence. -/
theorem sum_reciprocal_tail_le_of_doubling (n : ℕ) (y : Fin (n + 1) → ℝ)
    (hy : ∀ j, 0 < y j)
    (hd : ∀ j : Fin n, 2 * y j.castSucc ≤ y j.succ) (i : Fin (n + 1)) :
    ∑ j, (if i ≤ j then 1 / y j else 0) ≤ 2 / y i := by
  induction n with
  | zero =>
    fin_cases i
    simpa using (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (hy 0).le)
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using sum_reciprocal_le_of_doubling (n + 1) y hy hd
    · have ht := ih (fun j => y j.succ) (fun j => hy j.succ)
        (fun j => hd j.succ) k
      simpa [Fin.sum_univ_succ] using ht

/-- At a chosen transition coordinate, early decay and the late reciprocal
sum suffice to approximate one elementary pattern in total scalar error. -/
theorem scalar_pattern_approximation_at_cut {N : ℕ} (y : Fin N → ℝ)
    (hy : ∀ j, 0 < y j) (i : Fin N) (s ε κ : ℝ) (hs : 0 ≤ s)
    (hearly : ∀ j, j < i → ε * κ ≤ s / (1 + (y j) ^ 2))
    (hlate : ∑ j : Fin N, (if i < j then s / y j else 0) ≤ 2 * ε)
    (hsmall : (N : ℝ) * Real.exp (-ε * κ) ≤ ε) :
    ∃ z : ℂ, ‖z‖ ≤ 1 ∧
      ∑ j, ‖Complex.exp ((s : ℂ) * scalarLambda (y j)) -
        elementaryPattern i z (fun _ => 1) j‖ ≤ 3 * ε := by
  let z := Complex.exp ((s : ℂ) * scalarLambda (y i))
  have hz : ‖z‖ ≤ 1 := by
    rw [show z = Complex.exp ((s : ℂ) * scalarLambda (y i)) from rfl,
      scalarLambda_exp_norm]
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs)
      (by positivity))
  refine ⟨z, hz, ?_⟩
  have hpoint (j : Fin N) :
      ‖Complex.exp ((s : ℂ) * scalarLambda (y j)) -
        elementaryPattern i z (fun _ => 1) j‖ ≤
      Real.exp (-ε * κ) + (if i < j then s / y j else 0) := by
    rcases lt_trichotomy j i with hji | hji | hij
    · have hij : ¬i < j := not_lt_of_ge hji.le
      simp only [elementaryPattern, hji, ite_true, sub_zero, hij, ite_false, add_zero]
      rw [scalarLambda_exp_norm]
      apply Real.exp_le_exp.mpr
      simpa only [neg_div, neg_mul] using neg_le_neg (hearly j hji)
    · subst j
      simp only [elementaryPattern, lt_self_iff_false, ite_false, ite_true,
        mul_one, z, sub_self, norm_zero, add_zero]
      exact (Real.exp_pos _).le
    · have hji : ¬j < i := not_lt_of_ge hij.le
      have hne : j ≠ i := ne_of_gt hij
      simp only [elementaryPattern, hji, ite_false, hne, hij, ite_true]
      exact (scalarLambda_exp_sub_one_norm_le (hy j) hs).trans
        (le_add_of_nonneg_left (Real.exp_pos _).le)
  calc
    _ ≤ ∑ j : Fin N, (Real.exp (-ε * κ) + (if i < j then s / y j else 0)) :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = (N : ℝ) * Real.exp (-ε * κ) +
        ∑ j : Fin N, (if i < j then s / y j else 0) := by
      simp [Finset.sum_add_distrib]
    _ ≤ ε + 2 * ε := add_le_add hsmall hlate
    _ = _ := by ring

/-- Before the first transition, the whole diagonal is near the identity. -/
theorem scalar_pattern_approximation_initial {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℝ) (hy : ∀ j, 0 < y j) (s ε : ℝ) (hs : 0 ≤ s)
    (hsmall : s ≤ ε * y ⟨0, hN⟩)
    (hrecip : ∑ j : Fin N, 1 / y j ≤ 2 / y ⟨0, hN⟩) :
    ∑ j, ‖Complex.exp ((s : ℂ) * scalarLambda (y j)) -
      elementaryPattern ⟨0, hN⟩ 1 (fun _ => 1) j‖ ≤ 2 * ε := by
  have hpat (j : Fin N) : elementaryPattern ⟨0, hN⟩ 1 (fun _ => 1) j = 1 := by
    have hnot : ¬j < (⟨0, hN⟩ : Fin N) := by change ¬j.val < 0; omega
    simp [elementaryPattern, hnot]
  calc
    _ ≤ ∑ j : Fin N, s / y j := by
      apply Finset.sum_le_sum
      intro j _
      rw [hpat]
      exact scalarLambda_exp_sub_one_norm_le (hy j) hs
    _ = s * ∑ j : Fin N, 1 / y j := by simp [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ s * (2 / y ⟨0, hN⟩) := mul_le_mul_of_nonneg_left hrecip hs
    _ ≤ 2 * ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (hy ⟨0, hN⟩)).2
      convert mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring

/-- Once time lies below every later transition, geometric separation bounds
all of the late scalar errors at once. -/
theorem scalar_late_sum_le_of_doubling (n : ℕ) (y : Fin (n + 1) → ℝ)
    (hy : ∀ j, 0 < y j)
    (hd : ∀ j : Fin n, 2 * y j.castSucc ≤ y j.succ)
    (i : Fin (n + 1)) (s ε : ℝ) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hlateTime : ∀ j, i < j → s ≤ ε * y j) :
    ∑ j, (if i < j then s / y j else 0) ≤ 2 * ε := by
  by_cases hi : i.val < n
  · let k : Fin n := ⟨i.val, hi⟩
    have hki : k.castSucc = i := Fin.ext rfl
    have hnext : i < k.succ := by rw [← hki]; exact Fin.castSucc_lt_succ
    have hsum : (∑ j, (if i < j then s / y j else 0)) =
        s * ∑ j, (if k.succ ≤ j then 1 / y j else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hiff : i < j ↔ k.succ ≤ j := by
        change i.val < j.val ↔ k.val + 1 ≤ j.val
        dsimp [k]
        omega
      by_cases hj : i < j
      · simp [hj, hiff.mp hj, div_eq_mul_inv]
      · simp [hj, mt hiff.mpr hj]
    rw [hsum]
    calc
      _ ≤ s * (2 / y k.succ) := mul_le_mul_of_nonneg_left
        (sum_reciprocal_tail_le_of_doubling n y hy hd k.succ) hs
      _ ≤ 2 * ε := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (hy k.succ)).2
        have ht := hlateTime k.succ hnext
        nlinarith
  · have hempty (j : Fin (n + 1)) : ¬i < j := by
      change ¬i.val < j.val
      have := i.isLt
      have := j.isLt
      omega
    simp only [hempty, ite_false, Finset.sum_const_zero]
    positivity

/-- Separated positive frequencies supply an elementary pattern at every
nonnegative time. All hypotheses are finite scalar inequalities; no basis or
operator-norm hypothesis is hidden in this statement. -/
theorem scalar_pattern_approximation_of_separation (n : ℕ) (y : Fin (n + 1) → ℝ)
    (hy : ∀ j, 0 < y j) (ε κ : ℝ) (hε : 0 < ε) (hκ : 1 ≤ κ)
    (hgap : ∀ j : Fin n, κ * (1 + (y j.castSucc) ^ 2) ≤ y j.succ)
    (hsmall : (n + 1 : ℝ) * Real.exp (-ε * κ) ≤ ε)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ (i : Fin (n + 1)) (z : ℂ), ‖z‖ ≤ 1 ∧
      ∑ j, ‖Complex.exp ((s : ℂ) * scalarLambda (y j)) -
        elementaryPattern i z (fun _ => 1) j‖ ≤ 3 * ε := by
  have hd (j : Fin n) : 2 * y j.castSucc ≤ y j.succ := by
    have hfactor : 1 + (y j.castSucc) ^ 2 ≤ κ * (1 + (y j.castSucc) ^ 2) := by
      nlinarith [sq_nonneg (y j.castSucc)]
    nlinarith [hgap j, sq_nonneg (y j.castSucc - 1)]
  have hmono : Monotone y := Fin.monotone_iff_le_succ.mpr fun j => by
    have := hy j.castSucc
    have := hd j
    linarith
  by_cases hfirst : s ≤ ε * y 0
  · refine ⟨0, 1, by simp, ?_⟩
    have hi := scalar_pattern_approximation_initial (Nat.succ_pos n) y hy s ε hs hfirst
      (sum_reciprocal_le_of_doubling n y hy hd)
    exact hi.trans (by linarith)
  · let candidates : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => ε * y j ≤ s)
    have hnonempty : candidates.Nonempty := by
      refine ⟨0, ?_⟩
      simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (lt_of_not_ge hfirst).le
    let i := candidates.max' hnonempty
    have hi : ε * y i ≤ s := by
      have hm := Finset.max'_mem candidates hnonempty
      exact (Finset.mem_filter.mp hm).2
    have hlast (j : Fin (n + 1)) (hij : i < j) : s < ε * y j := by
      by_contra h
      have hj : j ∈ candidates := by
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact le_of_not_gt h
      exact (not_le_of_gt hij) (Finset.le_max' candidates j hj)
    have hearly (j : Fin (n + 1)) (hji : j < i) :
        ε * κ ≤ s / (1 + (y j) ^ 2) := by
      let k : Fin n := ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
      have hkj : k.castSucc = j := Fin.ext rfl
      have hki : k.succ ≤ i := by
        change k.val + 1 ≤ i.val
        change j.val < i.val at hji
        exact hji
      apply (le_div_iff₀ (by positivity : 0 < 1 + (y j) ^ 2)).2
      calc
        ε * κ * (1 + (y j) ^ 2) = ε * (κ * (1 + (y k.castSucc) ^ 2)) := by
          rw [hkj]
          ring
        _ ≤ ε * y k.succ := mul_le_mul_of_nonneg_left (hgap k) hε.le
        _ ≤ ε * y i := mul_le_mul_of_nonneg_left (hmono hki) hε.le
        _ ≤ s := hi
    have hlate := scalar_late_sum_le_of_doubling n y hy hd i s ε hs hε.le
      (fun j hj => (hlast j hj).le)
    obtain ⟨z, hz, herr⟩ := scalar_pattern_approximation_at_cut y hy i s ε κ hs
      hearly hlate (by simpa using hsmall)
    exact ⟨i, z, hz, herr⟩

end ProofProject
