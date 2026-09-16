/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Reverse active-block injectivity proves nonsingularity from every nonzero
actual pivot. No determinant assertion is made about zero-padded stages.
-/
import NLA.IE04.GEPP
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.IE04

theorem activeInjective_of_noSwap_schur {n : ℕ} (S : Mat n) (k : Fin n)
    (hp : S k k ≠ 0) (hnext : ActiveInjective (schurStep S k k) (k.val + 1)) :
    ActiveInjective S k.val := by
  intro x hx hrows
  let y : Fin n → ℝ := x - Pi.single k (x k)
  have hysupp : ∀ j : Fin n, j.val < k.val + 1 → y j = 0 := by
    intro j hj
    by_cases hjk : j = k
    · subst j
      simp [y]
    · have hjlt : j.val < k.val := by
        have hne : j.val ≠ k.val := (Fin.ne_iff_vne j k).mp hjk
        omega
      simp [y, hjk, hx j hjlt]
  have hmul : ∀ i, S.mulVec y i = S.mulVec x i - S i k * x k := by
    intro i
    simp [y, Matrix.mulVec_sub, mul_comm]
  have hswap : rowSwap S k k = S := by
    ext i j
    simp [rowSwap]
  have hyrows : ∀ i, k.val + 1 ≤ i.val → (schurStep S k k).mulVec y i = 0 := by
    intro i hi
    have hki : k < i := hi
    rw [schurStep_mulVec_proved S k k i y hysupp hki, hswap]
    rw [hmul, hmul, hrows i hki.le, hrows k le_rfl]
    field_simp
    ring
  have hy : y = 0 := hnext y hysupp hyrows
  have hxprod : S k k * x k = 0 := by
    have hzero : S.mulVec y k = 0 := by simp only [hy, Matrix.mulVec_zero, Pi.zero_apply]
    rw [hmul, hrows k le_rfl] at hzero
    linarith
  have hxk : x k = 0 := (mul_eq_zero.mp hxprod).resolve_left hp
  funext j
  have h := congrFun hy j
  simpa only [y, hxk, Pi.single_zero, sub_zero, Pi.zero_apply] using h

theorem det_ne_zero_of_activeInjective {n : ℕ} (A : Mat n)
    (hA : ActiveInjective A 0) : A.det ≠ 0 := by
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hz : x - y = 0 := hA (x - y) (by intro j hj; omega) (by
      intro i hi
      simp only [Matrix.mulVec_sub, hxy, sub_self, Pi.zero_apply])
    exact sub_eq_zero.mp hz
  have hu : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hu)

theorem noSwap_nonsingular_of_pivots {n : ℕ} (A : Mat n)
    (hp : ∀ k : Fin n, trajectory A (noSwapPath n) k.val k k ≠ 0) :
    A.det ≠ 0 := by
  apply det_ne_zero_of_activeInjective
  have hterminal : ActiveInjective (trajectory A (noSwapPath n) n) n := by
    intro x hx hrows
    funext j
    exact hx j j.isLt
  have hstart := Nat.decreasingInduction
    (motive := fun k _ => ActiveInjective (trajectory A (noSwapPath n) k) k)
    (fun k hk ih => by
      apply activeInjective_of_noSwap_schur _ (⟨k, hk⟩ : Fin n) (hp ⟨k, hk⟩)
      simpa only [trajectory, dif_pos hk, noSwapPath] using ih)
    hterminal (Nat.zero_le n)
  exact hstart

theorem strictNoSwap_admissible {n : ℕ} (A : Mat n) (hs : StrictNoSwapPath A) :
    AdmissiblePath A (noSwapPath n) := by
  intro k
  refine ⟨le_rfl, (hs k).1.ne', ?_⟩
  intro i hi
  rcases eq_or_lt_of_le hi with hik | hki
  · subst i
    exact le_rfl
  · simpa only [noSwapPath, abs_of_pos (hs k).1] using ((hs k).2 i hki).le

theorem strictNoSwap_pivot_unique {n : ℕ} (A : Mat n) (hs : StrictNoSwapPath A)
    (k p : Fin n) (hp : AdmissiblePivot (trajectory A (noSwapPath n) k.val) k p) :
    p = k := by
  by_contra hpk
  have hkp : k < p := lt_of_le_of_ne hp.1 (Ne.symm hpk)
  have hstrict := (hs k).2 p hkp
  have hmax := hp.2.2 k le_rfl
  rw [abs_of_pos (hs k).1] at hmax
  exact (not_lt_of_ge hmax) hstrict

theorem strictNoSwap_path_unique {n : ℕ} (A : Mat n) (hs : StrictNoSwapPath A)
    (path : PivotPath n) (hp : AdmissiblePath A path) : path = noSwapPath n := by
  have hstages : ∀ k : ℕ, trajectory A path k = trajectory A (noSwapPath n) k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        by_cases hk : k < n
        · have hpivot := hp (⟨k, hk⟩ : Fin n)
          rw [ih] at hpivot
          have he := strictNoSwap_pivot_unique A hs ⟨k, hk⟩ (path ⟨k, hk⟩) hpivot
          simp only [trajectory, dif_pos hk, ih, he, noSwapPath]
        · simp only [trajectory, dif_neg hk]
  funext k
  have hpivot := hp k
  rw [hstages k.val] at hpivot
  exact strictNoSwap_pivot_unique A hs k (path k) hpivot

#assert_trust kernel noSwap_nonsingular_of_pivots
#print axioms noSwap_nonsingular_of_pivots
#assert_trust kernel strictNoSwap_path_unique
#print axioms strictNoSwap_path_unique

end NLA.IE04
