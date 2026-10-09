import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic

/-! Finite probability distributions represented by real weights. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07

structure Law (α : Type*) [Fintype α] where
  wt : α → ℝ
  nonneg : ∀ a, 0 ≤ wt a
  sum_eq_one : ∑ a, wt a = 1

namespace Law
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext {p q : Law α} (h : ∀ a, p.wt a = q.wt a) : p = q := by
  cases p; cases q
  simp only [mk.injEq]
  exact funext h

def expect (p : Law α) (f : α → ℝ) : ℝ := ∑ a, p.wt a * f a

def mean {E : Type*} [AddCommMonoid E] [Module ℝ E] (p : Law α) (f : α → E) : E :=
  ∑ a, p.wt a • f a

def prob (p : Law α) (P : α → Prop) : ℝ := by
  classical
  exact p.expect (fun a => if P a then 1 else 0)

def variance (p : Law α) (f : α → ℝ) : ℝ :=
  p.expect (fun a => (f a - p.expect f)^2)

@[simp] theorem expect_const (p : Law α) (c : ℝ) : p.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, p.sum_eq_one]

@[simp] theorem expect_zero (p : Law α) : p.expect (fun _ => 0) = 0 := expect_const p 0

theorem expect_congr (p : Law α) {f g : α → ℝ} (h : ∀ a, f a = g a) :
    p.expect f = p.expect g := by simp_rw [funext h]

theorem expect_add (p : Law α) (f g : α → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (p : Law α) (f g : α → ℝ) :
    p.expect (fun a => f a - g a) = p.expect f - p.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (p : Law α) (f : α → ℝ) (c : ℝ) :
    p.expect (fun a => f a * c) = p.expect f * c := by
  simp only [expect, Finset.sum_mul, mul_assoc]

theorem expect_const_mul (p : Law α) (f : α → ℝ) (c : ℝ) :
    p.expect (fun a => c * f a) = c * p.expect f := by
  simpa [mul_comm] using p.expect_mul_const f c

theorem expect_sum {ι : Type*} (p : Law α) (s : Finset ι) (f : ι → α → ℝ) :
    p.expect (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, p.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_mono (p : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g := by
  exact Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) (p.nonneg a))

theorem expect_nonneg (p : Law α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ p.expect f := by
  simpa using p.expect_mono h

theorem expect_le_const (p : Law α) {f : α → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    p.expect f ≤ c := by simpa using p.expect_mono h

theorem const_le_expect (p : Law α) {f : α → ℝ} {c : ℝ} (h : ∀ a, c ≤ f a) :
    c ≤ p.expect f := by simpa using p.expect_mono h

theorem abs_expect_le (p : Law α) (f : α → ℝ) :
    |p.expect f| ≤ p.expect (fun a => |f a|) := by
  simpa [expect, abs_mul, abs_of_nonneg (p.nonneg _)] using
    Finset.abs_sum_le_sum_abs (fun a => p.wt a * f a) Finset.univ

theorem abs_expect_le_const (p : Law α) {f : α → ℝ} {c : ℝ}
    (h : ∀ a, |f a| ≤ c) : |p.expect f| ≤ c :=
  (p.abs_expect_le f).trans (p.expect_le_const h)

@[simp] theorem prob_true (p : Law α) : p.prob (fun _ => True) = 1 := by simp [prob]
@[simp] theorem prob_false (p : Law α) : p.prob (fun _ => False) = 0 := by simp [prob]

theorem prob_nonneg (p : Law α) (P : α → Prop) : 0 ≤ p.prob P := by
  classical
  exact p.expect_nonneg (fun a => by split_ifs <;> norm_num)

theorem prob_le_one (p : Law α) (P : α → Prop) : p.prob P ≤ 1 := by
  classical
  exact p.expect_le_const (fun a => by split_ifs <;> norm_num)

theorem prob_mono (p : Law α) {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    p.prob P ≤ p.prob Q := by
  classical
  apply p.expect_mono
  intro a
  by_cases hp : P a
  · simp [hp, h a hp]
  · simp [hp]
    split_ifs <;> norm_num

theorem prob_or_le (p : Law α) (P Q : α → Prop) :
    p.prob (fun a => P a ∨ Q a) ≤ p.prob P + p.prob Q := by
  classical
  rw [prob, prob, prob, ← expect_add]
  apply p.expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq]

theorem variance_nonneg (p : Law α) (f : α → ℝ) : 0 ≤ p.variance f :=
  p.expect_nonneg (fun _ => sq_nonneg _)

theorem variance_eq (p : Law α) (f : α → ℝ) :
    p.variance f = p.expect (fun a => f a ^ 2) - (p.expect f)^2 := by
  unfold variance
  have h (a : α) : (f a - p.expect f)^2 = f a^2 - 2 * p.expect f * f a + (p.expect f)^2 := by ring
  simp_rw [h]
  rw [expect_add, expect_sub, expect_const_mul, expect_const]
  ring

theorem sq_expect_le_expect_sq (p : Law α) (f : α → ℝ) :
    (p.expect f)^2 ≤ p.expect (fun a => f a^2) := by
  have := p.variance_nonneg f
  rw [variance_eq] at this
  linarith

theorem markov (p : Law α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    {t : ℝ} (ht : 0 < t) : p.prob (fun a => t ≤ f a) ≤ p.expect f / t := by
  classical
  rw [le_div_iff₀ ht]
  rw [prob, ← expect_mul_const]
  apply p.expect_mono
  intro a
  by_cases h : t ≤ f a <;> simp [h, hf a]

theorem chebyshev (p : Law α) (f : α → ℝ) {t : ℝ} (ht : 0 < t) :
    p.prob (fun a => t ≤ |f a - p.expect f|) ≤ p.variance f / t^2 := by
  apply le_trans (p.prob_mono ?_) (p.markov (fun a => (f a - p.expect f)^2)
    (fun _ => sq_nonneg _) (sq_pos_of_pos ht))
  intro a ha
  nlinarith [sq_abs (f a - p.expect f)]

/-- Uniform law on a finite nonempty type. -/
def uniform (α : Type*) [Fintype α] [Nonempty α] : Law α where
  wt _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_eq_one := by simp [Fintype.card_ne_zero]

@[simp] theorem uniform_wt [Nonempty α] (a : α) : (uniform α).wt a = (Fintype.card α : ℝ)⁻¹ := rfl

theorem uniform_expect [Nonempty α] (f : α → ℝ) :
    (uniform α).expect f = (∑ a, f a) / Fintype.card α := by
  simp only [expect, uniform_wt, div_eq_mul_inv, ← Finset.mul_sum]
  exact mul_comm _ _

theorem uniform_prob [Nonempty α] (P : α → Prop) [DecidablePred P] :
    (uniform α).prob P = ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  classical
  rw [prob, uniform_expect]
  congr 1
  exact_mod_cast (Finset.sum_boole P (Finset.univ : Finset α))

/-- A point mass. -/
def pure (a : α) : Law α := by
  classical
  exact {
    wt := fun b => if b = a then 1 else 0
    nonneg := fun b => by split_ifs <;> norm_num
    sum_eq_one := by simp }

@[simp] theorem expect_pure (a : α) (f : α → ℝ) : (pure a).expect f = f a := by
  classical
  simp [pure, expect]

/-- Finite kernel composition. -/
def bind (p : Law α) (q : α → Law β) : Law β where
  wt b := ∑ a, p.wt a * (q a).wt b
  nonneg b := Finset.sum_nonneg (fun a _ => mul_nonneg (p.nonneg a) ((q a).nonneg b))
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (q _).sum_eq_one, mul_one]
    exact p.sum_eq_one

theorem expect_bind (p : Law α) (q : α → Law β) (f : β → ℝ) :
    (p.bind q).expect f = p.expect (fun a => (q a).expect f) := by
  simp only [expect, bind, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def map (p : Law α) (f : α → β) : Law β := p.bind (fun a => pure (f a))

@[simp] theorem expect_map (p : Law α) (g : α → β) (f : β → ℝ) :
    (p.map g).expect f = p.expect (fun a => f (g a)) := by
  simp [map, expect_bind]

theorem expect_eq_iff (p q : Law α) : (∀ f, p.expect f = q.expect f) ↔ p = q := by
  classical
  refine ⟨fun h => ?_, fun h => h ▸ fun _ => rfl⟩
  ext a
  simpa [expect] using h (fun b => if b = a then 1 else 0)

@[simp] theorem bind_pure (p : Law α) : p.bind pure = p := by
  apply (expect_eq_iff _ _).mp
  intro f
  simp [expect_bind]

@[simp] theorem pure_bind (a : α) (q : α → Law β) : (pure a).bind q = q a := by
  apply (expect_eq_iff _ _).mp
  intro f
  simp [expect_bind]

theorem bind_assoc (p : Law α) (q : α → Law β) (r : β → Law γ) :
    (p.bind q).bind r = p.bind (fun a => (q a).bind r) := by
  apply (expect_eq_iff _ _).mp
  intro f
  simp [expect_bind]

def prod (p : Law α) (q : Law β) : Law (α × β) where
  wt ab := p.wt ab.1 * q.wt ab.2
  nonneg ab := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_eq_one := by
    simp [Fintype.sum_prod_type, ← Finset.mul_sum, q.sum_eq_one, p.sum_eq_one]

theorem expect_prod (p : Law α) (q : Law β) (f : α × β → ℝ) :
    (p.prod q).expect f = p.expect (fun a => q.expect (fun b => f (a,b))) := by
  simp [expect, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

def iid (p : Law α) (r : ℕ) : Law (Fin r → α) where
  wt x := ∏ i, p.wt (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => p.nonneg (x i))
  sum_eq_one := by
    rw [← Fintype.prod_sum]
    simp [p.sum_eq_one]

@[simp] theorem iid_wt (p : Law α) (r : ℕ) (x : Fin r → α) :
    (p.iid r).wt x = ∏ i, p.wt (x i) := rfl

theorem expect_iid_zero (p : Law α) (f : (Fin 0 → α) → ℝ) :
    (p.iid 0).expect f = f Fin.elim0 := by
  simp only [expect, iid, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
  congr 1

theorem expect_iid_succ (p : Law α) (r : ℕ) (f : (Fin (r+1) → α) → ℝ) :
    (p.iid (r+1)).expect f = p.expect (fun a => (p.iid r).expect (fun x => f (Fin.cons a x))) := by
  rw [expect, ← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1) => α))]
  simp only [iid_wt, Fintype.sum_prod_type, Fin.prod_univ_succ,
    Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, expect, Finset.mul_sum, mul_assoc]
  rfl

theorem expect_comm (p : Law α) (q : Law β) (f : α → β → ℝ) :
    p.expect (fun a => q.expect (f a)) = q.expect (fun b => p.expect (fun a => f a b)) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem prob_not (p : Law α) (P : α → Prop) : p.prob (fun a => ¬ P a) = 1 - p.prob P := by
  classical
  calc
    _ = p.expect (fun a => 1 - (if P a then (1:ℝ) else 0)) := by
      apply p.expect_congr
      intro a
      by_cases ha : P a <;> simp [ha]
    _ = _ := by rw [expect_sub, expect_const]; rfl

end Law
end NLA.TR07
