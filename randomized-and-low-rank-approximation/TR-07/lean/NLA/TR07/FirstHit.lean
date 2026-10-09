import NLA.TR07.FiniteProbability
import Mathlib.Algebra.Ring.GeomSum

/-! Exact first-hit sampling in a finite reservoir chunk. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace NLA.TR07

namespace Law
variable {α : Type*} [Fintype α]

/-- An equal mixture, used to reserve an unconditional zero-state branch. -/
def half (p q : Law α) : Law α where
  wt a := (p.wt a + q.wt a) / 2
  nonneg a := div_nonneg (add_nonneg (p.nonneg a) (q.nonneg a)) (by norm_num)
  sum_eq_one := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, p.sum_eq_one, q.sum_eq_one]
    norm_num

theorem expect_half (p q : Law α) (f : α → ℝ) :
    (half p q).expect f = (p.expect f + q.expect f) / 2 := by
  simp only [expect, half]
  simp_rw [add_div, add_mul, div_mul_eq_mul_div, Finset.sum_add_distrib, Finset.sum_div]

theorem wt_eq_expect (p : Law α) (a : α) : p.wt a = p.expect (fun x => if x = a then 1 else 0) := by
  simp [expect]

theorem expect_ite_const (p : Law α) (P : α → Prop) (f : α → ℝ) (c : ℝ) :
    p.expect (fun a => if P a then f a else c) =
      p.expect (fun a => if P a then f a else 0) + (1 - p.prob P) * c := by
  have he (a : α) : (if P a then f a else c) =
      (if P a then f a else 0) + (1 - if P a then (1 : ℝ) else 0) * c := by
    split_ifs <;> ring
  simp_rw [he]
  rw [expect_add, expect_mul_const, expect_sub, expect_const]
  rfl

end Law

variable {α : Type*} [Fintype α]

/-- The first acceptable indexed sample, or none if the chunk has no hit. -/
def firstHit (P : α → Prop) : {ℓ : ℕ} → (Fin ℓ → α) → Option α
  | 0, _ => none
  | ℓ+1, x => if P (x 0) then some (x 0) else firstHit P (fun i : Fin ℓ => x i.succ)

omit [Fintype α] in
theorem firstHit_mem (P : α → Prop) {ℓ : ℕ} (x : Fin ℓ → α) {a : α}
    (h : firstHit P x = some a) : P a ∧ ∃ i, x i = a := by
  induction ℓ with
  | zero => simp [firstHit] at h
  | succ ℓ ih =>
    simp only [firstHit] at h
    split_ifs at h with hg
    · cases Option.some.inj h
      exact ⟨hg, 0, rfl⟩
    · obtain ⟨ha, i, hi⟩ := ih (fun i => x i.succ) h
      exact ⟨ha, i.succ, hi⟩

theorem firstHit_expect (p : Law α) (P : α → Prop) (ℓ : ℕ) (f : Option α → ℝ) :
    (p.iid ℓ).expect (fun x => f (firstHit P x)) =
      (1 - p.prob P) ^ ℓ * f none +
        (∑ t ∈ Finset.range ℓ, (1 - p.prob P) ^ t) *
          p.expect (fun a => if P a then f (some a) else 0) := by
  induction ℓ with
  | zero => simp [firstHit]
  | succ ℓ ih =>
    rw [Law.expect_iid_succ]
    have he (a : α) : (p.iid ℓ).expect (fun x => f (firstHit P (Fin.cons a x))) =
        if P a then f (some a) else (p.iid ℓ).expect (fun x => f (firstHit P x)) := by
      by_cases h : P a <;> simp [firstHit, h]
    simp_rw [he, ih]
    rw [Law.expect_ite_const, geom_sum_succ, pow_succ]
    ring

def firstHitLaw (p : Law α) (P : α → Prop) (ℓ : ℕ) : Law (Option α) :=
  (p.iid ℓ).map (firstHit P)

theorem firstHitLaw_none (p : Law α) (P : α → Prop) (ℓ : ℕ) :
    (firstHitLaw p P ℓ).wt none = (1 - p.prob P) ^ ℓ := by
  rw [Law.wt_eq_expect, firstHitLaw, Law.expect_map]
  rw [firstHit_expect p P ℓ (fun x => @ite ℝ (x = none) (Classical.propDecidable _) 1 0)]
  simp

theorem firstHitLaw_some (p : Law α) (P : α → Prop) (ℓ : ℕ) (a : α) :
    (firstHitLaw p P ℓ).wt (some a) =
      (∑ t ∈ Finset.range ℓ, (1 - p.prob P) ^ t) * (if P a then p.wt a else 0) := by
  rw [Law.wt_eq_expect, firstHitLaw, Law.expect_map]
  rw [firstHit_expect p P ℓ (fun x => @ite ℝ (x = some a) (Classical.propDecidable _) 1 0)]
  simp only [reduceCtorEq, ↓reduceIte, mul_zero, zero_add, Option.some.injEq]
  congr 1
  rw [Law.expect]
  have hf (b : α) : p.wt b * (if P b then if b = a then 1 else 0 else 0) =
      if b = a then (if P a then p.wt a else 0) else 0 := by
    by_cases he : b = a <;> by_cases hp : P b <;> simp_all
  simp_rw [hf]
  simp

/-- The regularization makes the lower bound uniform even when the incidence
probability is arbitrarily small or zero. -/
theorem geom_regularized_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {k ℓ : ℕ} (hk : 0 < k) (hℓk : ℓ ≤ k) :
    (ℓ : ℝ) / k ≤ (∑ t ∈ Finset.range ℓ, (1 - p) ^ t) * (p + (k : ℝ)⁻¹) := by
  let G := ∑ t ∈ Finset.range ℓ, (1 - p) ^ t
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun _ _ => pow_nonneg hq0 _
  have hG : (ℓ : ℝ) * (1 - p) ^ ℓ ≤ G := by
    calc
      _ = ∑ _t ∈ Finset.range ℓ, (1 - p) ^ ℓ := by simp
      _ ≤ _ := Finset.sum_le_sum fun t ht =>
        pow_le_pow_of_le_one hq0 hq1 (Nat.le_of_lt (Finset.mem_range.mp ht))
  have hGp : G * p = 1 - (1 - p) ^ ℓ := by
    simpa only [sub_sub_cancel] using geom_sum_mul_neg (1 - p) ℓ
  have hkp : (ℓ : ℝ) ≤ k := by exact_mod_cast hℓk
  have hh : (ℓ : ℝ) ≤ G * (1 + (k : ℝ) * p) := by
    nlinarith [mul_nonneg hG0 (mul_nonneg (sub_nonneg.mpr hkp) hp0)]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply (div_le_iff₀ hk').mpr
  calc
    (ℓ : ℝ) ≤ G * (1 + (k : ℝ) * p) := hh
    _ = _ := by field_simp; ring

end NLA.TR07
