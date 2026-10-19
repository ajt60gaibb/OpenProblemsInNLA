import NLA.Statements.TR14

/-!
Every entry of the moment vector appears as a coordinate of the frozen Hankel
tensor. This is the finite zero/nonzero foundation for TR-14; it does not prove
the equality of ordinary and symmetric widths.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14

open NLA.Statements.TR14

/-- A number at most `m * (n - 1)` is a sum of `m` digits from `Fin n`. -/
private theorem bounded_digit_sum (m n j : ℕ) (hn : 0 < n)
    (hj : j ≤ m * (n - 1)) :
    ∃ i : Fin m → Fin n, (∑ k : Fin m, (i k).val) = j := by
  induction m generalizing j with
  | zero =>
      have hj0 : j = 0 := by simpa using hj
      exact ⟨fun k => Fin.elim0 k, by simp [hj0]⟩
  | succ m ih =>
      let a := min j (n - 1)
      have ha : a < n := by dsimp [a]; omega
      have hrest : j - a ≤ m * (n - 1) := by
        dsimp [a]
        simp only [Nat.succ_mul] at hj
        omega
      obtain ⟨i, hi⟩ := ih (j - a) hrest
      refine ⟨Fin.cons ⟨a, ha⟩ i, ?_⟩
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega

/-- The canonical zero-based Hankel index reaches every moment coordinate. -/
theorem hankelIndex_surjective {m n : ℕ} (_hm : 3 ≤ m) (hn : 2 ≤ n) :
    Function.Surjective (HankelIndex (m := m) (n := n)) := by
  intro j
  obtain ⟨i, hi⟩ := bounded_digit_sum m n j.val (by omega) (by
    have := j.isLt
    omega)
  refine ⟨i, ?_⟩
  apply Fin.ext
  exact hi

/-- The frozen Hankel tensor vanishes precisely when all its moments vanish. -/
theorem hankel_eq_zero_iff {m n : ℕ} (hm : 3 ≤ m) (hn : 2 ≤ n)
    (h : Fin (m * (n - 1) + 1) → ℂ) :
    Hankel h = 0 ↔ h = 0 := by
  constructor
  · intro hz
    funext j
    obtain ⟨i, hi⟩ := hankelIndex_surjective hm hn j
    have hzi := congrArg (fun f : (Fin m → Fin n) → ℂ => f i) hz
    simpa [Hankel, hi] using hzi
  · intro hz
    subst h
    rfl

#assert_trust kernel hankelIndex_surjective
#assert_trust kernel hankel_eq_zero_iff
#print axioms hankelIndex_surjective
#print axioms hankel_eq_zero_iff

end NLA.Proofs.TR14
