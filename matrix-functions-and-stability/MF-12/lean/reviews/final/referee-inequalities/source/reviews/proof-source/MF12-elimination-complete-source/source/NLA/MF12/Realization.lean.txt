/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The final result covers every nonnegative real exponent and all positive
word lengths, with exactly two distinct matrices and the genuine root limit.
-/
import NLA.MF12.Lifted
import NLA.MF12.RootLimit
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Classical Topology
open Filter

namespace NLA.MF12

theorem realizes_every_nonnegative_exponent (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ M : Finset (Square d), M.Nonempty ∧ M.card = 2 ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        (∀ n : ℕ, 1 ≤ n →
          c * Real.rpow (n : ℝ) γ ≤ familyGrowth M n ∧
          familyGrowth M n ≤ C * Real.rpow (n : ℝ) γ) ∧
        Tendsto (fun n : ℕ => Real.rpow (familyGrowth M n) (1 / (n : ℝ))) atTop (𝓝 1) := by
  let m : ℕ := ⌊γ⌋₊
  have hm : (m : ℝ) ≤ γ := Nat.floor_le hγ
  by_cases hγm : γ = (m : ℝ)
  · have hJ := jordan_growth_estimates m
    have hbounds : ∀ n : ℕ, 1 ≤ n →
        jordanLower m * Real.rpow (n : ℝ) γ ≤ familyGrowth (pairFamily (jordanMatrix m) 0) n ∧
        familyGrowth (pairFamily (jordanMatrix m) 0) n ≤
          ((m + 1 : ℕ) : ℝ) * Real.rpow (n : ℝ) γ := by
      intro n hn
      rw [integer_family_growth m n hn]
      simpa only [hγm, Real.rpow_eq_pow, Real.rpow_natCast] using hJ.2.2 n hn
    have hcompare : jordanLower m ≤ ((m + 1 : ℕ) : ℝ) := by
      have h := (hJ.2.2 1 le_rfl).1.trans (hJ.2.2 1 le_rfl).2
      simpa only [Nat.cast_one, one_pow, mul_one] using h
    refine ⟨m + 1, by omega, pairFamily (jordanMatrix m) 0,
      by simp [pairFamily], Finset.card_pair hJ.2.1,
      jordanLower m, ((m + 1 : ℕ) : ℝ), hJ.1, hcompare, hbounds, ?_⟩
    exact roots_of_polynomial_growth _ γ _ _ hγ hJ.1 (by positivity) hbounds
  · let α : ℝ := γ - (m : ℝ)
    have hα : 0 < α := by
      dsimp only [α]
      exact sub_pos.mpr (lt_of_le_of_ne hm (Ne.symm hγm))
    have hα1 : α < 1 := by
      have hlt : γ < (m : ℝ) + 1 := Nat.lt_floor_add_one γ
      dsimp only [α]
      linarith
    have hexp : α + (m : ℝ) = γ := by dsimp only [α]; ring
    have hT := fractional_tensor_growth α hα hα1 m
    have hbounds : ∀ n : ℕ, 1 ≤ n →
        liftedLower α m * Real.rpow (n : ℝ) γ ≤
          familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ∧
        familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ≤
          liftedUpper α m * Real.rpow (n : ℝ) γ := by
      intro n hn
      simpa only [hexp] using hT.2.2.2 n hn
    refine ⟨6 * (m + 1), by omega, pairFamily (liftedA α m) (liftedP m),
      by simp [pairFamily], Finset.card_pair hT.1,
      liftedLower α m, liftedUpper α m, hT.2.1, hT.2.2.1, hbounds, ?_⟩
    exact roots_of_polynomial_growth _ γ _ _ hγ hT.2.1
      (lt_of_lt_of_le hT.2.1 hT.2.2.1) hbounds

#assert_trust kernel realizes_every_nonnegative_exponent
#print axioms realizes_every_nonnegative_exponent

end NLA.MF12
