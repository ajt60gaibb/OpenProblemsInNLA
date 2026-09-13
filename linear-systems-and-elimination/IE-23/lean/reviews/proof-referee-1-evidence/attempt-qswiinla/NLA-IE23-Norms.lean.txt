/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Actual finite-p induced-norm semantics for the IE-23 counterexample.
The direct finite-sum argument avoids introducing a second norm structure.
Colbrook's analytic solution and Dokmanić–Gribonval's example retain their
attribution in SOURCE_CORRESPONDENCE.md. AI-assisted formalization,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA.
-/
import NLA.IE23.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

lemma euclideanNorm_nonneg {n : ℕ} (y : Vec n) : 0 ≤ euclideanNorm y :=
  norm_nonneg _

@[simp] lemma euclideanNorm_zero (n : ℕ) : euclideanNorm (0 : Vec n) = 0 := by
  simp [euclideanNorm]

lemma euclideanNorm_sq {n : ℕ} (y : Vec n) :
    euclideanNorm y ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  exact EuclideanSpace.norm_sq_eq (WithLp.toLp 2 y)

lemma euclideanNorm_sq_normSq {n : ℕ} (y : Vec n) :
    euclideanNorm y ^ 2 = ∑ i, Complex.normSq (y i) := by
  rw [euclideanNorm_sq]
  simp only [Complex.sq_norm]

lemma lpNorm_nonneg {n : ℕ} (p : ℝ) (y : Vec n) : 0 ≤ lpNorm p y := by
  exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

@[simp] lemma lpNorm_zero {n : ℕ} {p : ℝ} (hp : 0 < p) :
    lpNorm p (0 : Vec n) = 0 := by
  simp [lpNorm, Real.zero_rpow hp.ne', Real.zero_rpow (inv_pos.mpr hp).ne']

lemma lpNorm_pos {n : ℕ} {p : ℝ} (_hp : 0 < p) {y : Vec n} (hy : y ≠ 0) :
    0 < lpNorm p y := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra! h
    exact hy (funext h)
  apply Real.rpow_pos_of_pos
  exact Finset.sum_pos' (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos (norm_pos_iff.mpr hi) p⟩

lemma norm_coord_le_lpNorm {n : ℕ} {p : ℝ} (hp : 0 < p) (y : Vec n) (i : Fin n) :
    ‖y i‖ ≤ lpNorm p y := by
  unfold lpNorm
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) hp).mpr
  exact Finset.single_le_sum (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)
    (Finset.mem_univ i)

lemma euclideanNorm_le_sum {n : ℕ} (y : Vec n) :
    euclideanNorm y ≤ ∑ i, ‖y i‖ := by
  have h := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => ‖y i‖) (fun _ _ => norm_nonneg _)
  rw [← euclideanNorm_sq] at h
  exact (sq_le_sq₀ (euclideanNorm_nonneg y)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp h

lemma mulVec_lp_bound {m n : ℕ} {p : ℝ} (hp : 0 < p) (X : Mat n m) (y : Vec m) :
    euclideanNorm (X.mulVec y) ≤ (∑ i, ∑ j, ‖X i j‖) * lpNorm p y := by
  calc
    euclideanNorm (X.mulVec y) ≤ ∑ i, ‖X.mulVec y i‖ := euclideanNorm_le_sum _
    _ ≤ ∑ i, ∑ j, ‖X i j‖ * ‖y j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        norm_sum_le (s := Finset.univ) (f := fun j => X i j * y j)
    _ ≤ ∑ i, ∑ j, ‖X i j‖ * lpNorm p y := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (norm_coord_le_lpNorm hp y j) (norm_nonneg _)
    _ = (∑ i, ∑ j, ‖X i j‖) * lpNorm p y := by
      simp only [Finset.sum_mul]

lemma ratioSet_nonempty {m n : ℕ} (hm : 1 ≤ m) (p : ℝ) (X : Mat n m) :
    (ratioSet p X).Nonempty := by
  let y : Vec m := fun _ => 1
  have hy : y ≠ 0 := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    norm_num [y] at h0
  exact ⟨_, y, hy, rfl⟩

lemma ratioSet_bddAbove {m n : ℕ} {p : ℝ} (hp : 0 < p) (X : Mat n m) :
    BddAbove (ratioSet p X) := by
  refine ⟨∑ i, ∑ j, ‖X i j‖, ?_⟩
  rintro r ⟨y, hy, rfl⟩
  exact (div_le_iff₀ (lpNorm_pos hp hy)).mpr (mulVec_lp_bound hp X y)

lemma ratio_le_inducedNorm {m n : ℕ} {p : ℝ} (hp : 0 < p)
    (X : Mat n m) {y : Vec m} (hy : y ≠ 0) :
    euclideanNorm (X.mulVec y) / lpNorm p y ≤ inducedNorm p X := by
  exact le_csSup (ratioSet_bddAbove hp X) ⟨y, hy, rfl⟩

lemma inducedNorm_nonneg {m n : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p)
    (X : Mat n m) : 0 ≤ inducedNorm p X := by
  obtain ⟨r, y, hy, rfl⟩ := ratioSet_nonempty hm p X
  exact (div_nonneg (euclideanNorm_nonneg _) (lpNorm_nonneg _ _)).trans
    (ratio_le_inducedNorm hp X hy)

lemma mulVec_le_inducedNorm {m n : ℕ} {p : ℝ} (hp : 0 < p)
    (X : Mat n m) (y : Vec m) :
    euclideanNorm (X.mulVec y) ≤ inducedNorm p X * lpNorm p y := by
  by_cases hy : y = 0
  · subst y
    simp [lpNorm_zero hp]
  · exact (div_le_iff₀ (lpNorm_pos hp hy)).mp (ratio_le_inducedNorm hp X hy)

lemma inducedNorm_le_of_bound {m n : ℕ} (hm : 1 ≤ m) {p c : ℝ} (hp : 0 < p)
    (X : Mat n m) (h : ∀ y, euclideanNorm (X.mulVec y) ≤ c * lpNorm p y) :
    inducedNorm p X ≤ c := by
  apply csSup_le (ratioSet_nonempty hm p X)
  rintro r ⟨y, hy, rfl⟩
  exact (div_le_iff₀ (lpNorm_pos hp hy)).mpr (h y)

end NLA.IE23
