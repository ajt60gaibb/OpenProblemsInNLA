import NLA.IE03.Path
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The order-two Sylvester factor preserves complete pivoting. -/

namespace NLA.IE03

/-- The Kronecker product with the order-two Sylvester matrix, with each
original index expanded into its consecutive even and odd indices. -/
def double {K : Type*} [Neg K] (A : Entries K) : Entries K :=
  fun i j => if i % 2 = 1 ∧ j % 2 = 1 then -A (i / 2) (j / 2) else A (i / 2) (j / 2)

theorem double_embed {K : Type*} [Neg K] (A : Entries K) (i j a b : ℕ)
    (ha : a < 2) (hb : b < 2) :
    double A (2 * i + a) (2 * j + b) = if a = 1 ∧ b = 1 then -A i j else A i j := by
  unfold double
  rw [show (2 * i + a) / 2 = i by omega, show (2 * j + b) / 2 = j by omega,
    show (2 * i + a) % 2 = a by omega, show (2 * j + b) % 2 = b by omega]

@[simp] theorem double00 {K : Type*} [Neg K] (A : Entries K) (i j : ℕ) :
    double A (2 * i) (2 * j) = A i j := by
  simpa using double_embed A i j 0 0 (by decide) (by decide)

@[simp] theorem double01 {K : Type*} [Neg K] (A : Entries K) (i j : ℕ) :
    double A (2 * i) (2 * j + 1) = A i j := by
  simpa using double_embed A i j 0 1 (by decide) (by decide)

@[simp] theorem double10 {K : Type*} [Neg K] (A : Entries K) (i j : ℕ) :
    double A (2 * i + 1) (2 * j) = A i j := by
  simpa using double_embed A i j 1 0 (by decide) (by decide)

@[simp] theorem double11 {K : Type*} [Neg K] (A : Entries K) (i j : ℕ) :
    double A (2 * i + 1) (2 * j + 1) = -A i j := by
  simpa using double_embed A i j 1 1 (by decide) (by decide)

private theorem skip_self (i : ℕ) : skip i i = i + 1 := by
  simp [skip]

private theorem skip_twice (r i : ℕ) :
    skip (2 * r) (skip (2 * r) i) = 2 * skip r (i / 2) + i % 2 := by
  by_cases h : i / 2 < r
  · have h' : i < 2 * r := by omega
    simp only [skip, if_pos h, if_pos h']
    omega
  · have h' : ¬ i < 2 * r := by omega
    have h'' : ¬ i + 1 < 2 * r := by omega
    simp only [skip, if_neg h, if_neg h', if_neg h'']
    omega

noncomputable section

private theorem abs_double (A : Entries ℝ) (i j : ℕ) :
    |double A i j| = |A (i / 2) (j / 2)| := by
  unfold double
  split <;> simp

private theorem pivot_second_value (A : Entries ℝ) {r c : ℕ} (hp : A r c ≠ 0) :
    schur (double A) (2 * r) (2 * c) (2 * r) (2 * c) = -2 * A r c := by
  simp only [schur, skip_self, double11, double10, double01, double00]
  field_simp [hp]
  ring

/-- Deleting both indices of the pivot block leaves the doubled scalar
Schur complement. The four parity cases are the four entries of the block. -/
theorem schur_double_twice (A : Entries ℝ) {r c : ℕ} (hp : A r c ≠ 0) :
    schur (schur (double A) (2 * r) (2 * c)) (2 * r) (2 * c) =
      double (schur A r c) := by
  funext i j
  change schur (schur (double A) (2 * r) (2 * c)) (2 * r) (2 * c) i j =
    if i % 2 = 1 ∧ j % 2 = 1 then -schur A r c (i / 2) (j / 2)
    else schur A r c (i / 2) (j / 2)
  have hi : i % 2 = 0 ∨ i % 2 = 1 := by omega
  have hj : j % 2 = 0 ∨ j % 2 = 1 := by omega
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [schur, skip_twice, skip_self, hi, hj]
  all_goals field_simp [hp]
  all_goals try simp
  all_goals ring

private theorem first_double_pivot {n r c : ℕ} {A : Entries ℝ}
    (h : IsPivot (n + 1) A r c) :
    IsPivot (2 * (n + 1)) (double A) (2 * r) (2 * c) := by
  obtain ⟨hr, hc, hp, hmax⟩ := h
  refine ⟨by omega, by omega, by simpa using hp, ?_⟩
  intro i j hi hj
  rw [abs_double, double00]
  exact hmax _ _ (by omega) (by omega)

private theorem second_double_pivot {n r c : ℕ} {A : Entries ℝ}
    (h : IsPivot (n + 1) A r c) :
    IsPivot (2 * n + 1) (schur (double A) (2 * r) (2 * c)) (2 * r) (2 * c) := by
  obtain ⟨hr, hc, hp, hmax⟩ := h
  have hb (i j : ℕ) (hi : i < 2 * (n + 1)) (hj : j < 2 * (n + 1)) :
      |double A i j| ≤ |A r c| := by
    rw [abs_double]
    exact hmax _ _ (by omega) (by omega)
  have hrc := pivot_second_value A hp
  refine ⟨by omega, by omega, by rw [hrc]; exact mul_ne_zero (by norm_num) hp, ?_⟩
  intro i j hi hj
  have hi' : skip (2 * r) i < 2 * (n + 1) := by
    have := skip_lt (r := 2 * r) hi
    omega
  have hj' : skip (2 * c) j < 2 * (n + 1) := by
    have := skip_lt (r := 2 * c) hj
    omega
  have hrow := hb (skip (2 * r) i) (2 * c) hi' (by omega)
  have hcol := hb (2 * r) (skip (2 * c) j) (by omega) hj'
  have hentry := hb (skip (2 * r) i) (skip (2 * c) j) hi' hj'
  have hcorrection :
      |double A (skip (2 * r) i) (2 * c) * double A (2 * r) (skip (2 * c) j) /
        A r c| ≤ |A r c| := by
    rw [abs_div, abs_mul, div_le_iff₀ (abs_pos.mpr hp)]
    exact mul_le_mul hrow hcol (abs_nonneg _) (abs_nonneg _)
  rw [hrc, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  unfold schur
  rw [double00]
  calc
    |double A (skip (2 * r) i) (skip (2 * c) j) -
        double A (skip (2 * r) i) (2 * c) * double A (2 * r) (skip (2 * c) j) /
          A r c| ≤ _ := abs_sub _ _
    _ ≤ |A r c| + |A r c| := add_le_add hentry hcorrection
    _ = _ := by ring

theorem PivotPrefix.double {n m : ℕ} {A B : Entries ℝ} {g : ℝ}
    (h : PivotPrefix n A m B g) :
    PivotPrefix (2 * n) (IE03.double A) (2 * m) (IE03.double B) (2 * g) := by
  induction h with
  | empty n A => simpa using PivotPrefix.empty (2 * n) (IE03.double A)
  | @step n m A B g r c hp _ ih =>
    have htail : PivotPrefix (2 * n)
        (schur (schur (IE03.double A) (2 * r) (2 * c)) (2 * r) (2 * c))
        (2 * m) (IE03.double B) (2 * g) := by
      rwa [schur_double_twice A hp.2.2.1]
    have h1 := PivotPrefix.step (2 * r) (2 * c) (second_double_pivot hp) htail
    have h0 := PivotPrefix.step (2 * r) (2 * c) (first_double_pivot hp) h1
    have ha : |A r c| ≤ 2 * |A r c| := by linarith [abs_nonneg (A r c)]
    have hpeak : max |A r c| (max (2 * |A r c|) (2 * g)) =
        2 * max |A r c| g := by
      rw [max_eq_right (ha.trans (le_max_left _ _)), mul_max_of_nonneg _ _ (by norm_num)]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simpa only [double00, pivot_second_value A hp.2.2.1, abs_mul,
      show |(-2 : ℝ)| = 2 by norm_num, hpeak] using! h0

theorem Agree.double {n : ℕ} {A B : Entries ℝ} (h : Agree n A B) :
    Agree (2 * n) (IE03.double A) (IE03.double B) := by
  intro i j hi hj
  unfold IE03.double
  rw [h _ _ (by omega) (by omega)]

theorem Trace.double {n m : ℕ} {A B : Entries ℝ} {g : ℝ}
    (h : Trace n A m B g) :
    Trace (2 * n) (IE03.double A) (2 * m) (IE03.double B) (2 * g) := by
  obtain ⟨B', hp, he⟩ := h
  exact ⟨IE03.double B', hp.double, he.double⟩

end

end NLA.IE03
