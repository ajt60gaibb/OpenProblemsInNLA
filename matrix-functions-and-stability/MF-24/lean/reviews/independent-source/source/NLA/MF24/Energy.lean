/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

Full complex-vector energy bound. Every residue class contains all of its
coordinates. Its upper-triangular operator is bounded by the full positive
outer product, then a single finite Cauchy--Schwarz inequality is applied.
-/
import NLA.MF24.Weights
import NLA.MF24.NormBasics
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24
open scoped BigOperators

lemma sum_residue_classes (m : ℕ) (f : Fin (dimension m) → ℝ) :
    (∑ c : Fin (stride m), ∑ v ∈ residueClass m c, f v) = ∑ v, f v := by
  simp only [residueClass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  let c : Fin (stride m) := ⟨v.val % stride m, Nat.mod_lt _ (stride_pos m)⟩
  rw [Finset.sum_eq_single c]
  · simp [c]
  · intro d _ hdc
    have hd : v.val % stride m ≠ d.val := by
      intro he
      exact hdc (Fin.ext he.symm)
    simp [hd]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

lemma inverseHeightWeight_nonneg (m : ℕ) (t : ℝ) (ht : 0 < t)
    (v : Fin (dimension m)) : 0 ≤ inverseHeightWeight m t v := by
  unfold inverseHeightWeight heightWeight
  positivity

lemma heightWeight_nonneg (m : ℕ) (t : ℝ) (ht : 0 < t)
    (v : Fin (dimension m)) : 0 ≤ heightWeight m t v := by
  unfold heightWeight
  positivity

lemma denominator_entry_bound (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : 1 < t)
    (r s : Fin (dimension m)) :
    ‖polyEval (matrixY m t) (testPolynomial m) r s‖ ≤
      inverseHeightWeight m t r * heightWeight m t s := by
  have ht0 : 0 < t := by linarith
  rw [(source_words_eq_height_shifts m hm t ht).2.1,
    polynomial_entries m hm (fun v => heightY m v.val) t ht0 r s]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (pow_pos ht0 _) (pow_pos ht0 _))]
    unfold inverseHeightWeight heightWeight
    simp only [div_eq_mul_inv]
    exact le_of_eq (mul_comm _ _)
  · simp only [norm_zero]
    exact mul_nonneg (inverseHeightWeight_nonneg m t ht0 r) (heightWeight_nonneg m t ht0 s)

lemma denominator_entry_zero_off_class (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) (c : Fin (stride m))
    (r s : Fin (dimension m)) (hr : r ∈ residueClass m c) (hs : s ∉ residueClass m c) :
    polyEval (matrixY m t) (testPolynomial m) r s = 0 := by
  rw [(source_words_eq_height_shifts m hm t ht).2.1,
    polynomial_entries m hm (fun v => heightY m v.val) t (by linarith) r s]
  apply if_neg
  intro hf
  have hmod : Nat.ModEq (stride m) r.val s.val := (Nat.modEq_iff_dvd' hf.1.le).mpr hf.2
  apply hs
  exact (mem_residueClass m c s).mpr (hmod.symm.trans ((mem_residueClass m c r).mp hr))

lemma denominator_row_bound (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : 1 < t)
    (c : Fin (stride m)) (x : EuclideanVector (dimension m))
    (r : Fin (dimension m)) (hr : r ∈ residueClass m c) :
    ‖(Matrix.toEuclideanCLM (n := Fin (dimension m)) (𝕜 := ℂ)
      (polyEval (matrixY m t) (testPolynomial m)) x) r‖ ≤
      inverseHeightWeight m t r * ∑ s ∈ residueClass m c, heightWeight m t s * ‖x s‖ := by
  change ‖∑ s, polyEval (matrixY m t) (testPolynomial m) r s * x s‖ ≤ _
  calc
    _ ≤ ∑ s, ‖polyEval (matrixY m t) (testPolynomial m) r s * x s‖ := norm_sum_le _ _
    _ = ∑ s ∈ residueClass m c,
        ‖polyEval (matrixY m t) (testPolynomial m) r s‖ * ‖x s‖ := by
      rw [residueClass, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : s ∈ residueClass m c
      · have hsmod := (mem_residueClass m c s).mp hs
        simp [hsmod, norm_mul]
      · have hsmod : s.val % stride m ≠ c.val := (mem_residueClass m c s).not.mp hs
        rw [denominator_entry_zero_off_class m hm t ht c r s hr hs]
        simp [hsmod]
    _ ≤ ∑ s ∈ residueClass m c,
        (inverseHeightWeight m t r * heightWeight m t s) * ‖x s‖ := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_right (denominator_entry_bound m hm t ht r s) (norm_nonneg _)
    _ = inverseHeightWeight m t r * ∑ s ∈ residueClass m c,
        heightWeight m t s * ‖x s‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring

lemma denominator_class_energy (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : 1 < t)
    (c : Fin (stride m)) (x : EuclideanVector (dimension m)) :
    (∑ r ∈ residueClass m c,
      ‖(Matrix.toEuclideanCLM (n := Fin (dimension m)) (𝕜 := ℂ)
        (polyEval (matrixY m t) (testPolynomial m)) x) r‖ ^ 2) ≤
      (t ^ 2 + (m : ℝ)) ^ 2 * ∑ s ∈ residueClass m c, ‖x s‖ ^ 2 := by
  let U := ∑ r ∈ residueClass m c, inverseHeightWeight m t r ^ 2
  let V := ∑ s ∈ residueClass m c, heightWeight m t s ^ 2
  let E := ∑ s ∈ residueClass m c, ‖x s‖ ^ 2
  let T := Matrix.toEuclideanCLM (n := Fin (dimension m)) (𝕜 := ℂ)
    (polyEval (matrixY m t) (testPolynomial m))
  have ht0 : 0 < t := by linarith
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hw := residue_weight_bounds m hm t ht c
  have hUV : U * V ≤ (t ^ 2 + (m : ℝ)) ^ 2 := by
    calc U * V ≤ (1 + (m : ℝ) / t ^ 2) * (t ^ 4 + (m : ℝ) * t ^ 2) :=
        mul_le_mul hw.1 hw.2 hV (by positivity)
      _ = (t ^ 2 + (m : ℝ)) ^ 2 := by field_simp [ne_of_gt ht0] <;> ring
  have hCS : (∑ s ∈ residueClass m c, heightWeight m t s * ‖x s‖) ^ 2 ≤ V * E :=
    Finset.sum_mul_sq_le_sq_mul_sq (residueClass m c) (heightWeight m t) (fun s => ‖x s‖)
  have hrow : ∀ r ∈ residueClass m c,
      ‖(T x) r‖ ^ 2 ≤ inverseHeightWeight m t r ^ 2 * V * E := by
    intro r hr
    have hbound := denominator_row_bound m hm t ht c x r hr
    have hsum : 0 ≤ ∑ s ∈ residueClass m c, heightWeight m t s * ‖x s‖ :=
      Finset.sum_nonneg (fun s _ => mul_nonneg (heightWeight_nonneg m t ht0 s) (norm_nonneg _))
    have hsquare := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (inverseHeightWeight_nonneg m t ht0 r) hsum)).mpr hbound
    have hprod := mul_le_mul_of_nonneg_left hCS (sq_nonneg (inverseHeightWeight m t r))
    dsimp only [T]
    nlinarith
  calc
    _ ≤ ∑ r ∈ residueClass m c, inverseHeightWeight m t r ^ 2 * V * E := Finset.sum_le_sum hrow
    _ = U * V * E := by rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ (t ^ 2 + (m : ℝ)) ^ 2 * E := mul_le_mul_of_nonneg_right hUV hE

theorem polynomial_denominator_energy (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) (x : EuclideanVector (dimension m)) :
    ‖Matrix.toEuclideanCLM (n := Fin (dimension m)) (𝕜 := ℂ)
        (polyEval (matrixY m t) (testPolynomial m)) x‖ ^ 2 ≤
      (t ^ 2 + (m : ℝ)) ^ 2 * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [← sum_residue_classes m (fun r =>
    ‖(Matrix.toEuclideanCLM (n := Fin (dimension m)) (𝕜 := ℂ)
      (polyEval (matrixY m t) (testPolynomial m)) x) r‖ ^ 2)]
  calc
    _ ≤ ∑ c : Fin (stride m),
        (t ^ 2 + (m : ℝ)) ^ 2 * ∑ s ∈ residueClass m c, ‖x s‖ ^ 2 :=
      Finset.sum_le_sum (fun c _ => denominator_class_energy m hm t ht c x)
    _ = (t ^ 2 + (m : ℝ)) ^ 2 * ∑ s, ‖x s‖ ^ 2 := by
      rw [← Finset.mul_sum, sum_residue_classes]

theorem polynomial_denominator_bound (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    spectralNorm (polyEval (matrixY m t) (testPolynomial m)) ≤ t ^ 2 + (m : ℝ) :=
  spectralNorm_le_of_energy _ _ (by positivity) (polynomial_denominator_energy m hm t ht)

#assert_trust kernel polynomial_denominator_energy
#assert_trust kernel polynomial_denominator_bound
#print axioms polynomial_denominator_energy
#print axioms polynomial_denominator_bound

end NLA.MF24
