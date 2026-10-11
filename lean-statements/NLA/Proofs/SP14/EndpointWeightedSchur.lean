import NLA.Proofs.SP14.EndpointAbsoluteKernel
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
The scalar power-tail comparison used in the endpoint weighted Schur estimate.
The full Schur inequalities and bounded Sobolev operator remain separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open MeasureTheory

/-- A finite decreasing-power comparison, with the first term kept separately. -/
theorem endpointSchurPowerPrefix (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (N : ℕ) (hN : 1 ≤ N) :
    (∑ t ∈ Finset.range N, (((t + 1 : ℕ) : ℝ) ^ (-r))) ≤
      1 + (N : ℝ) ^ (1 - r) / (1 - r) := by
  let f : ℝ → ℝ := fun x => x ^ (-r)
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (by linarith)
  have hcompare :
      (∑ i ∈ Finset.Ico 1 N, f (((i + 1 : ℕ) : ℝ))) ≤
        ∫ x : ℝ in (1 : ℝ)..(N : ℝ), f x := by
    simpa only [Nat.cast_one] using
      (AntitoneOn.sum_le_integral_Ico (f := f) (a := 1) (b := N)
        (by exact_mod_cast hN) (by simpa using hanti))
  have hint : (∫ x : ℝ in (1 : ℝ)..(N : ℝ), f x) =
      ((N : ℝ) ^ (1 - r) - 1) / (1 - r) := by
    dsimp [f]
    rw [integral_rpow (Or.inl (by linarith : -1 < -r))]
    have hpow : (1 : ℝ) ^ (-r + 1) = 1 := by simp
    rw [hpow]
    ring_nf
  have hsum : (∑ t ∈ Finset.range N, (((t + 1 : ℕ) : ℝ) ^ (-r))) =
      1 + ∑ i ∈ Finset.Ico 1 N, (((i + 1 : ℕ) : ℝ) ^ (-r)) := by
    cases N with
    | zero => omega
    | succ n =>
        rw [Finset.sum_range_succ']
        simp only [Finset.sum_Ico_eq_sum_range, Nat.cast_add, Nat.cast_one,
          zero_add, Real.one_rpow]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        ring_nf
  rw [hsum]
  have hden : 0 < 1 - r := by linarith
  calc
    _ ≤ 1 + ((N : ℝ) ^ (1 - r) - 1) / (1 - r) := by
      simp only [f, hint] at hcompare
      linarith
    _ ≤ 1 + (N : ℝ) ^ (1 - r) / (1 - r) := by
      have hdiv := div_le_div_of_nonneg_right
        (sub_le_self ((N : ℝ) ^ (1 - r)) (by norm_num : (0 : ℝ) ≤ 1)) hden.le
      linarith

/-- The power tail begins strictly after `N`, including `N = 1`. -/
theorem endpointSchurPowerTail (r : ℝ) (hr : 0 < r) (N : ℕ) (hN : 1 ≤ N) :
    (∑' t : ℕ, (((t + N + 1 : ℕ) : ℝ) ^ (-r - 1))) ≤
      (N : ℝ) ^ (-r) / r := by
  let f : ℝ → ℝ := fun x => x ^ (-r - 1)
  have hanti : AntitoneOn f (Set.Ici (N : ℝ)) := by
    intro x hx y hy hxy
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    exact Real.rpow_le_rpow_of_nonpos (hNp.trans_le (Set.mem_Ici.mp hx))
      hxy (by linarith)
  have hint : IntegrableOn f (Set.Ioi (N : ℝ)) := by
    exact integrableOn_Ioi_rpow_of_lt (by linarith) (by exact_mod_cast (by omega : 0 < N))
  have hnonneg : ∀ x ∈ Set.Ioi (N : ℝ), 0 ≤ f x := by
    intro x hx
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    exact Real.rpow_nonneg (hNp.trans (Set.mem_Ioi.mp hx)).le _
  have h := hanti.tsum_comp_add_le_integral N hint hnonneg
  have hi : (∫ x : ℝ in Set.Ioi (N : ℝ), f x) = (N : ℝ) ^ (-r) / r := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) (by exact_mod_cast (by omega : 0 < N))]
    have hrn : -r - 1 + 1 = -r := by ring
    rw [hrn]
    field_simp
  simpa only [f, Nat.cast_add, Nat.cast_one, hi] using h

#assert_trust kernel endpointSchurPowerPrefix
#assert_trust kernel endpointSchurPowerTail
#print axioms endpointSchurPowerPrefix
#print axioms endpointSchurPowerTail

end NLA.Proofs.SP14
