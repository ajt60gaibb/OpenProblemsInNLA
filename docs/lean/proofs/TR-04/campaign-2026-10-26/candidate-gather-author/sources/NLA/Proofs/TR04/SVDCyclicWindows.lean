import NLA.Proofs.TR04.SVDSelected
import Mathlib.Algebra.Group.Fin.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

/-- A cyclic window starting at j, expressed in the actual additive finite
cyclic group. The chosen s consecutive directions are j,...,j+s-1. -/
def cyclicWindow {t : ℕ} [NeZero t] (s : ℕ) (j k : Fin t) : Prop :=
  (k - j).val < s

instance {t : ℕ} [NeZero t] (s : ℕ) (j k : Fin t) : Decidable (cyclicWindow s j k) :=
  inferInstanceAs (Decidable ((k - j).val < s))

def cyclicTranslate {t : ℕ} [NeZero t] (j : Fin t) : Fin t ≃ Fin t where
  toFun k := k - j
  invFun k := k + j
  left_inv k := sub_add_cancel k j
  right_inv k := add_sub_cancel_right k j

def cyclicDifference {t : ℕ} [NeZero t] (k : Fin t) : Fin t ≃ Fin t where
  toFun j := k - j
  invFun j := k - j
  left_inv j := sub_sub_cancel k j
  right_inv j := sub_sub_cancel k j

def prefixSubtypeEquiv {t s : ℕ} (hst : s ≤ t) : {k : Fin t // k.val < s} ≃ Fin s where
  toFun k := ⟨k.val.val, k.property⟩
  invFun k := ⟨⟨k.val, lt_of_lt_of_le k.isLt hst⟩, k.isLt⟩
  left_inv k := by apply Subtype.ext; rfl
  right_inv k := rfl

theorem card_cyclicWindow {t : ℕ} [NeZero t] (s : ℕ) (hst : s ≤ t) (j : Fin t) :
    Fintype.card {k // cyclicWindow s j k} = s := by
  classical
  let e : {k // cyclicWindow s j k} ≃ {k : Fin t // k.val < s} :=
    (cyclicTranslate j).subtypeEquiv (by intro k; rfl)
  exact (Fintype.card_congr (e.trans (prefixSubtypeEquiv hst))).trans (Fintype.card_fin s)

/-- Every tied basis direction belongs to exactly s of the t windows. -/
theorem sum_cyclicWindow_indicator {t : ℕ} [NeZero t] (s : ℕ) (hst : s ≤ t) (k : Fin t) :
    (∑ j : Fin t, if cyclicWindow s j k then (1 : ℝ) else 0) = s := by
  have h := (cyclicDifference k).sum_comp (fun i : Fin t => if i.val < s then (1 : ℝ) else 0)
  change (∑ j : Fin t, if (k - j).val < s then (1 : ℝ) else 0) = _ at h
  change (∑ j : Fin t, if (k - j).val < s then (1 : ℝ) else 0) = s
  rw [h]
  exact prefix_count_of_le hst

/-- Exact total selected energy over all windows; this works for signed
weights as well as squared residual coordinates. -/
theorem sum_cyclicWindow_energy {t : ℕ} [NeZero t] (s : ℕ) (hst : s ≤ t) (e : Fin t → ℝ) :
    (∑ j : Fin t, ∑ k : Fin t, if cyclicWindow s j k then e k else 0) =
      (s : ℝ) * ∑ k, e k := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hterm (j : Fin t) : (if cyclicWindow s j k then e k else 0) =
      (if cyclicWindow s j k then (1 : ℝ) else 0) * e k := by split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.sum_mul, sum_cyclicWindow_indicator s hst k]

theorem average_cyclicWindow_energy {t : ℕ} [NeZero t] (s : ℕ) (hst : s ≤ t)
    (e : Fin t → ℝ) :
    (∑ j : Fin t, ∑ k : Fin t, if cyclicWindow s j k then e k else 0) / t =
      ((s : ℝ) / t) * ∑ k, e k := by
  rw [sum_cyclicWindow_energy s hst]
  ring

theorem exists_cyclicWindow_energy_le_average {t : ℕ} [NeZero t]
    (s : ℕ) (hst : s ≤ t) (e : Fin t → ℝ) :
    ∃ j : Fin t, (∑ k, if cyclicWindow s j k then e k else 0) ≤
      ((s : ℝ) / t) * ∑ k, e k := by
  classical
  have ht : 0 < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
  by_contra hn
  push Not at hn
  have hsum : (∑ j : Fin t, ((s : ℝ) / t) * ∑ k, e k) <
      ∑ j : Fin t, ∑ k : Fin t, if cyclicWindow s j k then e k else 0 :=
    Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun j _ => hn j)
  rw [sum_cyclicWindow_energy s hst] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have heq : (t : ℝ) * (((s : ℝ) / t) * ∑ k, e k) = (s : ℝ) * ∑ k, e k := by
    field_simp
  rw [heq] at hsum
  exact (lt_irrefl _) hsum

#assert_trust kernel card_cyclicWindow
#assert_trust kernel sum_cyclicWindow_indicator
#assert_trust kernel sum_cyclicWindow_energy
#assert_trust kernel exists_cyclicWindow_energy_le_average
#print axioms exists_cyclicWindow_energy_le_average
end NLA.Proofs.TR04.SVD
