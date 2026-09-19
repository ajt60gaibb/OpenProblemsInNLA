import NLA.PF03.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanCert.Tactic

/-!
Exact one-variable Fourier–Motzkin elimination over the reals. The literal
rational row construction is the frozen PF03 definition, including empty and
one-sided systems. No projection oracle or coefficient-sign hypothesis is
added to the exported statement.

Original mathematical argument and seed: Sidney Holden, Center for Computational
Biology, Flatiron Institute, Simons Foundation. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, with Codex assistance. Proof author: /root/recover_lean_sources;
final independent proof reviewers must be different nonauthors.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

/-- The scalar feasibility step uses finite extrema, including no-row systems. -/
private theorem fm_finite_feasible {N : ℕ} (a b : Fin N → ℝ)
    (hz : ∀ i, a i = 0 → 0 ≤ b i)
    (hcross : ∀ p q, 0 < a p → a q < 0 →
      0 ≤ a p * b q - a q * b p) :
    ∃ y : ℝ, ∀ i, 0 ≤ a i * y + b i := by
  classical
  let positive : Finset (Fin N) := Finset.univ.filter (fun i => 0 < a i)
  by_cases hp : positive.Nonempty
  · obtain ⟨p, hp_mem, hmax⟩ :=
      Finset.exists_max_image positive (fun i => -b i / a i) hp
    have hp0 : 0 < a p := (Finset.mem_filter.mp hp_mem).2
    let y : ℝ := -b p / a p
    have hroot : a p * y + b p = 0 := by
      dsimp [y]
      rw [mul_comm (a p) (-b p / a p), div_mul_cancel₀ _ hp0.ne']
      exact neg_add_cancel _
    refine ⟨y, ?_⟩
    intro i
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have hid : a p * (a i * y + b i) =
          a i * (a p * y + b p) + (a p * b i - a i * b p) := by ring
      have hmul : 0 ≤ a p * (a i * y + b i) := by
        rw [hid, hroot, mul_zero, zero_add]
        exact hcross p i hp0 hi
      exact nonneg_of_mul_nonneg_right hmul hp0
    · simpa only [hi, zero_mul, zero_add] using hz i hi
    · have hi_mem : i ∈ positive := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have hle : -b i / a i ≤ y := hmax i hi_mem
      have hbound : -b i ≤ y * a i := (div_le_iff₀ hi).mp hle
      nlinarith only [hbound]
  · have hnoPositive : ∀ i, ¬ 0 < a i := by
      intro i hi
      exact hp ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let negative : Finset (Fin N) := Finset.univ.filter (fun i => a i < 0)
    by_cases hn : negative.Nonempty
    · obtain ⟨q, hq_mem, hmin⟩ :=
        Finset.exists_min_image negative (fun i => -b i / a i) hn
      let y : ℝ := -b q / a q
      refine ⟨y, ?_⟩
      intro i
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · have hi_mem : i ∈ negative := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hle : y ≤ -b i / a i := hmin i hi_mem
        have hbound : -b i ≤ y * a i := (le_div_iff_of_neg hi).mp hle
        nlinarith only [hbound]
      · simpa only [hi, zero_mul, zero_add] using hz i hi
      · exact (hnoPositive i hi).elim
    · refine ⟨0, ?_⟩
      intro i
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · exact (hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩).elim
      · simpa only [hi, zero_mul, zero_add] using hz i hi
      · exact (hnoPositive i hi).elim

private theorem fm_rowHolds_row {N d : ℕ} (A : QMat N d)
    (x : Fin d → ℝ) (i : Fin N) :
    rowHolds (A i) x ↔ 0 ≤ ((castMatrix A).mulVec x) i := Iff.rfl

private theorem fm_pair_value {N d : ℕ} (A : QMat N d) (a : Fin N → ℚ)
    (x : Fin d → ℝ) (p q : Fin N) :
    (∑ j : Fin d, ((a p * A q j - a q * A p j : ℚ) : ℝ) * x j) =
      (a p : ℝ) * ((castMatrix A).mulVec x) q -
        (a q : ℝ) * ((castMatrix A).mulVec x) p := by
  change (∑ j : Fin d, ((a p * A q j - a q * A p j : ℚ) : ℝ) * x j) =
    (a p : ℝ) * (∑ j : Fin d, (A q j : ℝ) * x j) -
      (a q : ℝ) * (∑ j : Fin d, (A p j : ℝ) * x j)
  simp only [Rat.cast_sub, Rat.cast_mul, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, Finset.mul_sum]

private theorem fm_rowHolds_pair {N d : ℕ} (A : QMat N d) (a : Fin N → ℚ)
    (x : Fin d → ℝ) (p q : Fin N) :
    rowHolds (fun j => a p * A q j - a q * A p j) x ↔
      0 ≤ (a p : ℝ) * ((castMatrix A).mulVec x) q -
        (a q : ℝ) * ((castMatrix A).mulVec x) p := by
  unfold rowHolds
  rw [fm_pair_value]

/-- The list has exactly the zero rows and the positive-negative cross rows. -/
private theorem fm_eliminateOne_holds {N d : ℕ} (A : QMat N d)
    (a : Fin N → ℚ) (x : Fin d → ℝ) :
    (∀ r ∈ eliminateOne A a, rowHolds r x) ↔
      (∀ i, a i = 0 → 0 ≤ ((castMatrix A).mulVec x) i) ∧
      (∀ p q, 0 < a p → a q < 0 →
        0 ≤ (a p : ℝ) * ((castMatrix A).mulVec x) q -
          (a q : ℝ) * ((castMatrix A).mulVec x) p) := by
  classical
  constructor
  · intro h
    constructor
    · intro i hi
      apply (fm_rowHolds_row A x i).mp
      apply h (A i)
      apply List.mem_append.mpr
      left
      exact List.mem_filterMap.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩
    · intro p q hp hq
      apply (fm_rowHolds_pair A a x p q).mp
      apply h (fun j => a p * A q j - a q * A p j)
      apply List.mem_append.mpr
      right
      apply List.mem_flatMap.mpr
      refine ⟨p, List.mem_finRange p, ?_⟩
      exact List.mem_filterMap.mpr ⟨q, List.mem_finRange q, by simp [hp, hq]⟩
  · rintro ⟨hz, hcross⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, hi_mem, hrow⟩ := List.mem_filterMap.mp hr
      by_cases hi : a i = 0
      · have heq : A i = r := Option.some.inj (by simpa only [hi, if_true] using hrow)
        rw [← heq]
        exact (fm_rowHolds_row A x i).mpr (hz i hi)
      · simp [hi] at hrow
    · obtain ⟨p, hp_mem, hp_row⟩ := List.mem_flatMap.mp hr
      obtain ⟨q, hq_mem, hrow⟩ := List.mem_filterMap.mp hp_row
      by_cases hsign : 0 < a p ∧ a q < 0
      · have heq : (fun j => a p * A q j - a q * A p j) = r :=
          Option.some.inj (by simpa [hsign] using hrow)
        rw [← heq]
        exact (fm_rowHolds_pair A a x p q).mpr (hcross p q hsign.1 hsign.2)
      · simp [hsign] at hrow

/-- C15: the exact frozen real projection contract, with every degenerate case. -/
theorem one_variable_projection {N d : ℕ} (A : QMat N d) (a : Fin N → ℚ)
    (x : Fin d → ℝ) :
    (∀ r ∈ eliminateOne A a, rowHolds r x) ↔
      ∃ y : ℝ, ∀ i : Fin N,
        0 ≤ (a i : ℝ) * y + ((castMatrix A).mulVec x) i := by
  rw [fm_eliminateOne_holds]
  constructor
  · rintro ⟨hz, hcross⟩
    apply fm_finite_feasible (fun i => (a i : ℝ)) ((castMatrix A).mulVec x)
    · intro i hi
      apply hz i
      exact_mod_cast hi
    · intro p q hp hq
      apply hcross p q
      · exact_mod_cast hp
      · exact_mod_cast hq
  · rintro ⟨y, hy⟩
    constructor
    · intro i hi
      simpa only [hi, Rat.cast_zero, zero_mul, zero_add] using hy i
    · intro p q hp hq
      have hp0 : 0 ≤ (a p : ℝ) := by exact_mod_cast hp.le
      have hq0 : 0 ≤ -(a q : ℝ) := by
        have hq' : (a q : ℝ) < 0 := by exact_mod_cast hq
        exact (neg_pos.mpr hq').le
      have h₁ := mul_nonneg hp0 (hy q)
      have h₂ := mul_nonneg hq0 (hy p)
      nlinarith only [h₁, h₂]

#print axioms one_variable_projection
#assert_trust kernel one_variable_projection

end NLA.PF03
