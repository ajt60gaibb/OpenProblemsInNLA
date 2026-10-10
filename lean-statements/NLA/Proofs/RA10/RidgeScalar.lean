import NLA.Statements.RA10
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! RA-10 ridge-atom scalar gates from source Equations (12) and (20).
These exact finite statements do not prove the matrix transfer target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA10

noncomputable def ridgeAtom (s x : ℝ) : ℝ := x / (s + x)

theorem ridgeAtom_abs_sub_eq {s c a b : ℝ}
    (hs : 0 < s) (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    |ridgeAtom s a - ridgeAtom s b| =
      s * |a - b| / ((s + a) * (s + b)) := by
  have hsa : 0 < s + a := by linarith
  have hsb : 0 < s + b := by linarith
  have hden : 0 < (s + a) * (s + b) := mul_pos hsa hsb
  have hdiff : ridgeAtom s a - ridgeAtom s b =
      s * (a - b) / ((s + a) * (s + b)) := by
    unfold ridgeAtom
    field_simp
    ring
  rw [hdiff, abs_div, abs_mul, abs_of_pos hs, abs_of_pos hden]

theorem ridgeAtom_abs_sub_le {s c a b : ℝ}
    (hs : 0 < s) (hc : 0 < c) (ha : c ≤ a) (hb : 0 ≤ b) :
    |ridgeAtom s a - ridgeAtom s b| ≤ |a - b| / (s + c) := by
  rw [ridgeAtom_abs_sub_eq hs hc ha hb]
  have hsa : 0 < s + a := by linarith
  have hsb : 0 < s + b := by linarith
  have hsc : 0 < s + c := by linarith
  have hden : 0 < (s + a) * (s + b) := mul_pos hsa hsb
  have hprod : (s + c) * s ≤ (s + a) * (s + b) := by
    exact mul_le_mul (by linarith) (by linarith) (le_of_lt hs) (by linarith)
  apply (div_le_div_iff₀ hden hsc).2
  nlinarith [mul_nonneg (abs_nonneg (a - b)) (sub_nonneg.mpr hprod)]

theorem ridgeAtom_tail_lower {s c x : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hx0 : 0 ≤ x) (hxc : x ≤ c) :
    x / (s + c) ≤ ridgeAtom s x := by
  unfold ridgeAtom
  have hsx : 0 < s + x := by linarith
  have hsc : 0 < s + c := by linarith
  apply (div_le_div_iff₀ hsc hsx).2
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxc)]

theorem ridgeAtom_tail_sum_lower {n k : ℕ}
    (a : Fin n → ℝ) {s c : ℝ}
    (hs : 0 < s) (hc : 0 < c)
    (ha0 : ∀ i : Fin n, 0 ≤ a i)
    (hac : ∀ i : Fin n, k ≤ i.val → a i ≤ c) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), ridgeAtom s (a i)) ≥
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i) / (s + c) := by
  let T : Finset (Fin n) := Finset.univ.filter (fun i => k ≤ i.val)
  have hsum :
      (∑ i ∈ T, a i / (s + c)) ≤ (∑ i ∈ T, ridgeAtom s (a i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact ridgeAtom_tail_lower hs hc (ha0 i) (hac i (Finset.mem_filter.mp hi).2)
  simpa only [T, div_eq_mul_inv, Finset.sum_mul] using hsum

#assert_trust kernel ridgeAtom_abs_sub_eq
#assert_trust kernel ridgeAtom_abs_sub_le
#assert_trust kernel ridgeAtom_tail_lower
#assert_trust kernel ridgeAtom_tail_sum_lower
#print axioms ridgeAtom_tail_sum_lower

end NLA.Proofs.RA10
