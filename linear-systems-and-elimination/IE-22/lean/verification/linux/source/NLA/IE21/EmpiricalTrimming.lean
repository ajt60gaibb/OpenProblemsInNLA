import NLA.IE21.FiniteTrimming
import NLA.IE21.QuantileTrimming

/-!
Deterministic fractional trimming bounds. Threshold-dual attainment is used
instead of sorting or a numerical approximation to the retained sample.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

/-- If at least k observations lie below L, a minimizing threshold can be chosen
in the closed interval [0,L], including the empty-retention case. -/
theorem finiteTrim_bounded_threshold {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) (L : ℝ) (hL : 0 ≤ L)
    (hcount : k ≤ (Finset.univ.filter (fun i => y i ≤ L)).card) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ L ∧
      finiteTrim k y = (k : ℝ) * t - ∑ i, max (t - y i) 0 := by
  classical
  obtain ⟨⟨S, hS, hval⟩, hmin⟩ := finiteTrim_minimum k hk y
  have horder : ∀ i ∈ S, ∀ j ∉ S, y i ≤ y j := by
    intro i hi j hj
    apply minimizing_selection_order k y S hS _ i j hi hj
    intro T hT
    simpa [← hval] using hmin T hT
  have hsmall : ∀ i ∈ S, y i ≤ L := by
    intro i hi
    by_contra hil
    have hcard : (S.erase i).card < (Finset.univ.filter (fun j => y j ≤ L)).card := by
      rw [Finset.card_erase_of_mem hi, hS]
      have hkpos : 0 < k := hS ▸ Finset.card_pos.mpr ⟨i, hi⟩
      omega
    obtain ⟨j, hj, hjerase⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hjL := (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by intro h; subst j; exact hil hjL
    have hjS : j ∉ S := fun h => hjerase (Finset.mem_erase.mpr ⟨hji, h⟩)
    exact hil ((horder i hi j hjS).trans hjL)
  obtain ⟨t, ht, htL, hin, hout⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ L ∧
      (∀ i ∈ S, y i ≤ t) ∧ (∀ j ∉ S, t ≤ y j) := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, hL, by simp, fun j _ => hy j⟩
    · refine ⟨S.sup' hne y, ?_, ?_, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne
        exact (hy i).trans (Finset.le_sup' y hi)
      · exact Finset.sup'_le hne y hsmall
      · intro i hi
        exact Finset.le_sup' y hi
      · intro j hj
        obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hne y
        rw [heq]
        exact horder i hi j hj
  refine ⟨t, ht, htL, ?_⟩
  have hsum : (∑ i, max (t - y i) 0) = (k : ℝ) * t - ∑ i ∈ S, y i := by
    calc
      (∑ i, max (t - y i) 0) = ∑ i ∈ S, max (t - y i) 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        exact max_eq_right (sub_nonpos.mpr (hout i hi))
      _ = ∑ i ∈ S, (t - y i) :=
        Finset.sum_congr rfl fun i hi => max_eq_left (sub_nonneg.mpr (hin i hi))
      _ = _ := by simp [Finset.sum_sub_distrib, hS]
  rw [hsum, hval]
  ring

theorem finiteTrim_sum_dual_le {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (y : Fin m → ℝ) (t : ℝ) :
    (k : ℝ) * t - ∑ i, max (t - y i) 0 ≤ finiteTrim k y := by
  obtain ⟨⟨S, hS, hval⟩, _⟩ := finiteTrim_minimum k hk y
  have h := trimDual_le_selection hm k y S hS t
  rw [trimDual_eq_div, ← hval] at h
  exact (div_le_div_iff_of_pos_right (by exact_mod_cast (show 0 < m by omega))).mp h

/-- Comparison with a fractional threshold selector. It is valid at tied
observations and at k=0; no relaxation of the exact retained cardinality occurs. -/
theorem finiteTrim_fractional_error {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (y w : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hbL : b ≤ L)
    (halign : ∀ i, max (b - y i) 0 = (b - y i) * w i)
    (hcount : k ≤ (Finset.univ.filter (fun i => y i ≤ L)).card) :
    |finiteTrim k y - ∑ i, y i * w i| ≤ L * |(k : ℝ) - ∑ i, w i| := by
  obtain ⟨t, ht, htL, hval⟩ := finiteTrim_bounded_threshold k hk y hy L (hb.trans hbL) hcount
  have hupper : finiteTrim k y - ∑ i, y i * w i ≤ t * ((k : ℝ) - ∑ i, w i) := by
    have hsum : (∑ i, (t - y i) * w i) ≤ ∑ i, max (t - y i) 0 := by
      apply Finset.sum_le_sum
      intro i _
      rcases hw i with ⟨hw0, hw1⟩
      by_cases hty : 0 ≤ t - y i
      · rw [max_eq_left hty]
        nlinarith
      · rw [max_eq_right (le_of_not_ge hty)]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hty) hw0
    have heq : (∑ i, (t - y i) * w i) = t * (∑ i, w i) - ∑ i, y i * w i := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heq] at hsum
    rw [hval]
    nlinarith
  have hlower : (∑ i, y i * w i) - finiteTrim k y ≤ b * ((∑ i, w i) - k) := by
    have h := finiteTrim_sum_dual_le hm k hk y b
    have heq : (∑ i, max (b - y i) 0) = b * (∑ i, w i) - ∑ i, y i * w i := by
      simp_rw [halign, sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [heq] at h
    nlinarith
  have hscale (a d : ℝ) (ha : 0 ≤ a) (haL : a ≤ L) : a * d ≤ L * |d| :=
    (mul_le_mul_of_nonneg_left (le_abs_self d) ha).trans
      (mul_le_mul_of_nonneg_right haL (abs_nonneg d))
  have hu := hupper.trans (hscale t _ ht htL)
  have hl := hlower.trans (hscale b _ hb hbL)
  rw [abs_sub_comm (∑ i, w i) (k : ℝ)] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

end NLA.IE21
