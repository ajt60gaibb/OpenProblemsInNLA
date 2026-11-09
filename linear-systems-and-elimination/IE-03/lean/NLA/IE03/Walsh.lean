import NLA.IE03.Lift

/-! The signs and row Gram matrix of the Sylvester construction. -/

namespace NLA.IE03

/-- The Sylvester matrix of order `2^d`, with even and odd copies
interleaved as in `double`. -/
def walsh {K : Type*} [One K] [Neg K] : ℕ → Entries K
  | 0 => fun _ _ => 1
  | d + 1 => double (walsh d)

theorem walsh_cast (d i j : ℕ) :
    (walsh (K := ℝ) d) i j = ((walsh (K := ℤ) d i j : ℤ) : ℝ) := by
  induction d generalizing i j with
  | zero => simp [walsh]
  | succ d ih =>
    simp only [walsh, double]
    split <;> simp [ih]

private theorem sum_pairs {K : Type*} [AddCommMonoid K] (f : ℕ → K) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n), f k =
      ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [Finset.sum_range_succ, ih]
    ac_rfl

theorem IsHadamard.double {n : ℕ} {A : Entries ℝ} (h : IsHadamard n A) :
    IsHadamard (2 * n) (IE03.double A) := by
  obtain ⟨hsign, hgram⟩ := h
  constructor
  · intro i j hi hj
    obtain h | h := hsign (i / 2) (j / 2) (by omega) (by omega) <;>
      unfold IE03.double <;> split <;> rw [h] <;> norm_num
  · intro i j hi hj
    obtain ⟨i, a, ha, rfl⟩ : ∃ i' a, a < 2 ∧ i = 2 * i' + a :=
      ⟨i / 2, i % 2, by omega, by omega⟩
    obtain ⟨j, b, hb, rfl⟩ : ∃ j' b, b < 2 ∧ j = 2 * j' + b :=
      ⟨j / 2, j % 2, by omega, by omega⟩
    have hG := hgram i j (by omega) (by omega)
    have same0 : (2 * i = 2 * j) ↔ i = j := by omega
    have same : (2 * i + a = 2 * j + a) ↔ i = j := by omega
    have sum_same : (∑ k ∈ Finset.range n, (A i k * A j k + A i k * A j k)) =
        2 * (∑ k ∈ Finset.range n, A i k * A j k) := by
      rw [Finset.sum_add_distrib, two_mul]
    have scale : (2 : ℝ) * (if i = j then (n : ℝ) else 0) =
        if i = j then (↑(2 * n) : ℝ) else 0 := by
      split <;> push_cast <;> simp_all
    have ha' : a = 0 ∨ a = 1 := by omega
    have hb' : b = 0 ∨ b = 1 := by omega
    rw [sum_pairs]
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · simpa only [Nat.add_zero, double00, double01, sum_same, hG, same0] using scale
    · have hne : 2 * i ≠ 2 * j + 1 := by omega
      simp [hne, mul_neg]
    · have hne : 2 * i + 1 ≠ 2 * j := by omega
      simp [hne, neg_mul]
    · simpa only [double10, double11, neg_mul_neg, sum_same, hG, same] using scale

theorem walsh_hadamard (d : ℕ) : IsHadamard (2 ^ d) (walsh d) := by
  induction d with
  | zero =>
    constructor
    · intro i j _ _
      exact Or.inl rfl
    · intro i j hi hj
      have hij : i = j := by omega
      subst j
      norm_num [walsh]
  | succ d ih =>
    rw [pow_succ']
    exact ih.double

end NLA.IE03
