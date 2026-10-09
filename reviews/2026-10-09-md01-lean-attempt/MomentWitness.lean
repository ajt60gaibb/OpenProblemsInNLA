import Mathlib

/-!
One exactly matched family from the proposed correction to Theorem 3.24
of the MD-01 paper.  The four trace blocks have exterior labels
`a,b,c,d`; the chorded-cycle block reuses `b,a`, and the triangle block
reuses `c`.  Each of the five edge signs consequently occurs twice.
This file does not formalize the graph matrices or the full moment theorem.
-/

namespace MD01Witness

def witnessTerm {n : ℕ} (s : Fin n → Fin n → ℤ) (a b c d : Fin n) : ℤ :=
  s a b * s b c *
    (s c b * s b a * s a d * s c d * s c a) *
    (s d c * s c a * s d a)

theorem witnessTerm_eq_one {n : ℕ} (s : Fin n → Fin n → ℤ)
    (hsym : ∀ x y, s x y = s y x)
    (hsq : ∀ x y, x ≠ y → s x y * s x y = 1)
    (f : Fin 4 ↪ Fin n) :
    witnessTerm s (f 0) (f 1) (f 2) (f 3) = 1 := by
  have hdiff (i j : Fin 4) (h : i ≠ j) : f i ≠ f j := by
    intro heq
    exact h (f.injective heq)
  calc
    witnessTerm s (f 0) (f 1) (f 2) (f 3) =
        (s (f 0) (f 1) * s (f 0) (f 1)) *
        (s (f 1) (f 2) * s (f 1) (f 2)) *
        (s (f 0) (f 3) * s (f 0) (f 3)) *
        (s (f 2) (f 3) * s (f 2) (f 3)) *
        (s (f 2) (f 0) * s (f 2) (f 0)) := by
          unfold witnessTerm
          rw [hsym (f 2) (f 1), hsym (f 1) (f 0),
              hsym (f 3) (f 2), hsym (f 3) (f 0)]
          ring
    _ = 1 := by
      rw [hsq (f 0) (f 1) (hdiff 0 1 (by decide)),
          hsq (f 1) (f 2) (hdiff 1 2 (by decide)),
          hsq (f 0) (f 3) (hdiff 0 3 (by decide)),
          hsq (f 2) (f 3) (hdiff 2 3 (by decide)),
          hsq (f 2) (f 0) (hdiff 2 0 (by decide))]
      norm_num

noncomputable def witnessSum (n : ℕ) (s : Fin n → Fin n → ℤ) : ℤ :=
  ∑ f : Fin 4 ↪ Fin n, witnessTerm s (f 0) (f 1) (f 2) (f 3)

/-- Every injective four-label assignment gives one, so this formal sum
equals `(n)_4`. Its trace interpretation is outside this file. -/
theorem witnessSum_eq_descFactorial (n : ℕ) (s : Fin n → Fin n → ℤ)
    (hsym : ∀ x y, s x y = s y x)
    (hsq : ∀ x y, x ≠ y → s x y * s x y = 1) :
    witnessSum n s = (n.descFactorial 4 : ℤ) := by
  classical
  simp [witnessSum, witnessTerm_eq_one s hsym hsq, Fintype.card_embedding_eq]

theorem descFactorial_four (n : ℕ) :
    n.descFactorial 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
  ring

/-- The matched family grows at least at fourth order; this is the
algebraic growth statement behind its order-`sqrt n` normalized size. -/
theorem witness_family_growth (n : ℕ) (hn : 6 ≤ n) :
    n ^ 4 ≤ 8 * n.descFactorial 4 := by
  have h1 : n ≤ 2 * (n - 1) := by omega
  have h2 : n ≤ 2 * (n - 2) := by omega
  have h3 : n ≤ 2 * (n - 3) := by omega
  rw [descFactorial_four]
  calc
    n ^ 4 = n * n * n * n := by ring
    _ ≤ n * (2 * (n - 1)) * (2 * (n - 2)) * (2 * (n - 3)) := by
      gcongr
    _ = 8 * (n * (n - 1) * (n - 2) * (n - 3)) := by ring

/-- After normalization by `n^(7/2)`, this family's contribution is
unbounded.  We avoid square roots by squaring both numerator and
denominator; `B² n⁷ < ((n)_4)²` is the equivalent natural-number witness. -/
theorem witness_family_unbounded_squared (B : ℕ) :
    ∃ n : ℕ, 6 ≤ n ∧ B ^ 2 * n ^ 7 < (n.descFactorial 4) ^ 2 := by
  let n := 64 * (B + 1) ^ 2 + 6
  have hn : 6 ≤ n := by dsimp [n]; omega
  have hbig : 64 * B ^ 2 < n := by
    have hB : B ^ 2 ≤ (B + 1) ^ 2 := by gcongr; omega
    dsimp [n]
    omega
  have hlow := witness_family_growth n hn
  have hsq : (n ^ 4) ^ 2 ≤ (8 * n.descFactorial 4) ^ 2 := by gcongr
  have hmul : (64 * B ^ 2) * n ^ 7 < n * n ^ 7 :=
    Nat.mul_lt_mul_of_pos_right hbig (pow_pos (by omega) 7)
  refine ⟨n, hn, ?_⟩
  nlinarith [hsq, hmul]

/-- The corrected half-exponent slack identity: when `s` is positive,
`r - d/2` is at most one half.  This is the arithmetic step used when
weakened fixed-moment remainders are substituted for a printed `O(1)`.
-/
theorem corrected_exponent_half (d s r : ℕ)
    (hspos : 0 < s) (hsub : s ≤ d)
    (hrel : 2 * (r - 1) = d - s) :
    (r : ℚ) - (d : ℚ) / 2 ≤ (1 : ℚ) / 2 := by
  have hnat : 2 * r ≤ d + 1 := by omega
  have hq : (2 : ℚ) * (r : ℚ) ≤ (d : ℚ) + 1 := by exact_mod_cast hnat
  linarith

theorem corrected_exponent_identity (d s r : ℕ)
    (hsub : s ≤ d) (hr : 1 ≤ r)
    (hrel : 2 * (r - 1) = d - s) :
    (r : ℚ) - (d : ℚ) / 2 = 1 - (s : ℚ) / 2 := by
  have hnat : 2 * r + s = d + 2 := by omega
  have hq : (2 : ℚ) * (r : ℚ) + (s : ℚ) = (d : ℚ) + 2 := by
    exact_mod_cast hnat
  linarith

/-- If `d` is even, a positive admissible slack must be at least two,
and the same exponent is at most zero. -/
theorem corrected_exponent_even (d s r : ℕ)
    (hspos : 0 < s) (hsub : s ≤ d)
    (hrel : 2 * (r - 1) = d - s) (hdeven : Even d) :
    (r : ℚ) - (d : ℚ) / 2 ≤ 0 := by
  obtain ⟨k, hk⟩ := hdeven
  have hnat : 2 * r ≤ d := by omega
  have hq : (2 : ℚ) * (r : ℚ) ≤ (d : ℚ) := by exact_mod_cast hnat
  linarith

#print axioms witnessTerm_eq_one
#print axioms witnessSum_eq_descFactorial
#print axioms witness_family_growth
#print axioms witness_family_unbounded_squared
#print axioms corrected_exponent_half
#print axioms corrected_exponent_identity
#print axioms corrected_exponent_even

end MD01Witness
