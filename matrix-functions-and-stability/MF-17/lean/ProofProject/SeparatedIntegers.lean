import Mathlib

/-!
# Separated integer frequencies with prescribed signs

The recursive eigenvalue selection for the finite-dimensional lower bound.
`p j = true` prescribes an odd frequency and hence the sign `-1` at time π.
The construction is entirely in natural numbers; the final logarithmic bound
controls the double-exponential size of the frequencies.
-/

namespace ProofProject

/-- The first integer at least `n` with the prescribed parity. -/
def parityCeil (n : ℕ) (p : Bool) : ℕ :=
  if n % 2 = (if p then 1 else 0) then n else n + 1

lemma le_parityCeil (n : ℕ) (p : Bool) : n ≤ parityCeil n p := by
  unfold parityCeil
  split_ifs <;> omega

lemma parityCeil_le (n : ℕ) (p : Bool) : parityCeil n p ≤ n + 1 := by
  unfold parityCeil
  split_ifs <;> omega

lemma parityCeil_mod_two (n : ℕ) (p : Bool) :
    parityCeil n p % 2 = (if p then 1 else 0) := by
  cases p <;> unfold parityCeil <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    split_ifs <;> omega

/-- Positive, rapidly separated frequencies with arbitrary prescribed parity. -/
def separatedInteger (κ : ℕ) (p : ℕ → Bool) : ℕ → ℕ
  | 0 => parityCeil 2 (p 0)
  | j + 1 => parityCeil (κ * (1 + separatedInteger κ p j ^ 2)) (p (j + 1))

lemma separatedInteger_zero_bounds (κ : ℕ) (p : ℕ → Bool) :
    2 ≤ separatedInteger κ p 0 ∧ separatedInteger κ p 0 ≤ 3 :=
  ⟨le_parityCeil 2 _, parityCeil_le 2 _⟩

lemma separatedInteger_succ_bounds (κ : ℕ) (p : ℕ → Bool) (j : ℕ) :
    κ * (1 + separatedInteger κ p j ^ 2) ≤ separatedInteger κ p (j + 1) ∧
    separatedInteger κ p (j + 1) ≤ κ * (1 + separatedInteger κ p j ^ 2) + 2 := by
  constructor
  · exact le_parityCeil _ _
  · exact (parityCeil_le _ _).trans (by omega)

lemma separatedInteger_mod_two (κ : ℕ) (p : ℕ → Bool) (j : ℕ) :
    separatedInteger κ p j % 2 = (if p j then 1 else 0) := by
  cases j <;> exact parityCeil_mod_two _ _

lemma separatedInteger_odd {κ : ℕ} {p : ℕ → Bool} {j : ℕ} (h : p j = true) :
    Odd (separatedInteger κ p j) := by
  rw [Nat.odd_iff, separatedInteger_mod_two, h]
  rfl

lemma separatedInteger_even {κ : ℕ} {p : ℕ → Bool} {j : ℕ} (h : p j = false) :
    Even (separatedInteger κ p j) := by
  rw [Nat.even_iff, separatedInteger_mod_two, h]
  rfl

lemma separatedInteger_neg_one_pow (κ : ℕ) (p : ℕ → Bool) (j : ℕ) :
    (-1 : ℂ) ^ separatedInteger κ p j = (if p j then -1 else 1) := by
  cases h : p j
  · simpa [h] using (separatedInteger_even h).neg_one_pow (α := ℂ)
  · simpa [h] using (separatedInteger_odd h).neg_one_pow (α := ℂ)

lemma two_le_separatedInteger {κ : ℕ} (hκ : 1 ≤ κ) (p : ℕ → Bool) (j : ℕ) :
    2 ≤ separatedInteger κ p j := by
  induction j with
  | zero => exact (separatedInteger_zero_bounds κ p).1
  | succ j ih =>
    have h := (separatedInteger_succ_bounds κ p j).1
    have hm : 1 + separatedInteger κ p j ^ 2 ≤
        κ * (1 + separatedInteger κ p j ^ 2) := by
      simpa only [one_mul] using Nat.mul_le_mul_right (1 + separatedInteger κ p j ^ 2) hκ
    nlinarith

/-- Each step at least doubles the frequency. -/
lemma two_mul_separatedInteger_le_succ {κ : ℕ} (hκ : 1 ≤ κ)
    (p : ℕ → Bool) (j : ℕ) :
    2 * separatedInteger κ p j ≤ separatedInteger κ p (j + 1) := by
  have h := (separatedInteger_succ_bounds κ p j).1
  have hm : 1 + separatedInteger κ p j ^ 2 ≤
      κ * (1 + separatedInteger κ p j ^ 2) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (1 + separatedInteger κ p j ^ 2) hκ
  nlinarith [sq_nonneg ((separatedInteger κ p j : ℤ) - 1)]

lemma separatedInteger_strictMono {κ : ℕ} (hκ : 1 ≤ κ) (p : ℕ → Bool) :
    StrictMono (separatedInteger κ p) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h₁ := two_mul_separatedInteger_le_succ hκ p j
  have h₂ := two_le_separatedInteger hκ p j
  omega

/-- The sharp additive rounding error is harmless for the quadratic bound. -/
lemma separatedInteger_succ_le {κ : ℕ} (hκ : 1 ≤ κ) (p : ℕ → Bool) (j : ℕ) :
    separatedInteger κ p (j + 1) ≤ 2 * κ * separatedInteger κ p j ^ 2 := by
  have hy := two_le_separatedInteger hκ p j
  have hround : separatedInteger κ p (j + 1) ≤
      κ * (1 + separatedInteger κ p j ^ 2) + 1 := parityCeil_le _ _
  have hsq : 2 ≤ separatedInteger κ p j ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left κ hsq
  nlinarith

/-- An affine log bound that retains the gain in the exact recurrence. -/
lemma separatedInteger_log_add_le {κ : ℕ} (hκ : 1 ≤ κ) (p : ℕ → Bool) (j : ℕ) :
    Real.log (separatedInteger κ p j) + Real.log (2 * (κ : ℝ)) ≤
      (2 : ℝ) ^ j * (Real.log 3 + Real.log (2 * (κ : ℝ))) := by
  have hκr : 0 < (κ : ℝ) := by exact_mod_cast (show 0 < κ by omega)
  have hK : 0 < 2 * (κ : ℝ) := by positivity
  induction j with
  | zero =>
    have h₀ := separatedInteger_zero_bounds κ p
    have hpos : 0 < (separatedInteger κ p 0 : ℝ) := by exact_mod_cast (by omega : 0 < separatedInteger κ p 0)
    have hle : (separatedInteger κ p 0 : ℝ) ≤ 3 := by exact_mod_cast h₀.2
    simpa using add_le_add_right (Real.log_le_log hpos hle) (Real.log (2 * (κ : ℝ)))
  | succ j ih =>
    have hy := two_le_separatedInteger hκ p j
    have hyn := two_le_separatedInteger hκ p (j + 1)
    have hyp : 0 < (separatedInteger κ p j : ℝ) := by exact_mod_cast (by omega : 0 < separatedInteger κ p j)
    have hynp : 0 < (separatedInteger κ p (j + 1) : ℝ) := by exact_mod_cast (by omega : 0 < separatedInteger κ p (j + 1))
    have hstep : (separatedInteger κ p (j + 1) : ℝ) ≤
        (2 * (κ : ℝ)) * (separatedInteger κ p j : ℝ) ^ 2 := by
      exact_mod_cast separatedInteger_succ_le hκ p j
    have hlog := Real.log_le_log hynp hstep
    rw [Real.log_mul (ne_of_gt hK) (pow_ne_zero _ (ne_of_gt hyp)), Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    rw [pow_succ]
    nlinarith

lemma separatedInteger_log_le {κ : ℕ} (hκ : 1 ≤ κ) (p : ℕ → Bool) (j : ℕ) :
    Real.log (separatedInteger κ p j) ≤
      (2 : ℝ) ^ j * (Real.log 3 + Real.log (2 * (κ : ℝ))) := by
  have hlog := separatedInteger_log_add_le hκ p j
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hK : 0 ≤ Real.log (2 * (κ : ℝ)) := Real.log_nonneg (by linarith)
  linarith

end ProofProject
