/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The Euclidean single-vector and energy arguments also reuse the structure of
this campaign's MF-24 norm lemmas; the real square-matrix bounds are proved here.
-/
import NLA.MF12.Definitions
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical

namespace NLA.MF12

lemma spectralNorm_nonneg {d : ℕ} (A : Square d) : 0 ≤ spectralNorm A := norm_nonneg _

lemma abs_entry_le_spectralNorm {d : ℕ} (A : Square d) (r s : Fin d) :
    |A r s| ≤ spectralNorm A := by
  let e : EuclideanVector d := PiLp.single 2 s (1 : ℝ)
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hentry : (T e) r = A r s := by
    change (Matrix.mulVec A (Pi.single s (1 : ℝ))) r = A r s
    simp [Matrix.mulVec_single_one]
  calc
    |A r s| = ‖(T e) r‖ := by rw [hentry, Real.norm_eq_abs]
    _ ≤ ‖T e‖ := PiLp.norm_apply_le (T e) r
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = spectralNorm A := by rw [he, mul_one]; rfl

lemma spectralNorm_le_entry_bound {d : ℕ} (A : Square d) (E : ℝ) (hE : 0 ≤ E)
    (hentry : ∀ r s : Fin d, |A r s| ≤ E) : spectralNorm A ≤ (d : ℝ) * E := by
  let T := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A
  have hC : 0 ≤ (d : ℝ) * E := mul_nonneg (Nat.cast_nonneg d) hE
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  have hrow (r : Fin d) : ((T x) r) ^ 2 ≤ ((d : ℝ) * E ^ 2) * ‖x‖ ^ 2 := by
    have hA : (∑ s : Fin d, (A r s) ^ 2) ≤ (d : ℝ) * E ^ 2 := by
      calc
        (∑ s : Fin d, (A r s) ^ 2) ≤ ∑ _s : Fin d, E ^ 2 := by
          apply Finset.sum_le_sum
          intro s _
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (A r s)) hE).mpr (hentry r s)
        _ = (d : ℝ) * E ^ 2 := by simp
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun s : Fin d => A r s)
      (fun s : Fin d => x s)
    rw [← EuclideanSpace.real_norm_sq_eq x] at hcs
    change (∑ s : Fin d, A r s * x s) ^ 2 ≤ ((d : ℝ) * E ^ 2) * ‖x‖ ^ 2
    exact hcs.trans (mul_le_mul_of_nonneg_right hA (sq_nonneg ‖x‖))
  calc
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x‖ ^ 2 =
        ∑ r : Fin d, ((T x) r) ^ 2 := EuclideanSpace.real_norm_sq_eq (T x)
    _ ≤ ∑ _r : Fin d, ((d : ℝ) * E ^ 2) * ‖x‖ ^ 2 :=
      Finset.sum_le_sum (fun r _ => hrow r)
    _ = ((d : ℝ) * E * ‖x‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma entryMax_finite {d : ℕ} (A : Square d) :
    ({0} ∪ Set.range (fun ij : Fin d × Fin d => |A ij.1 ij.2|)).Finite :=
  (Set.finite_singleton 0).union (Set.finite_range _)

lemma entryMax_nonneg {d : ℕ} (A : Square d) : 0 ≤ entryMax A := by
  apply le_csSup (entryMax_finite A).bddAbove
  exact Or.inl (by rfl)

lemma abs_entry_le_entryMax {d : ℕ} (A : Square d) (r s : Fin d) :
    |A r s| ≤ entryMax A := by
  apply le_csSup (entryMax_finite A).bddAbove
  exact Or.inr ⟨(r, s), rfl⟩

lemma entryMax_le_of_entry_bound {d : ℕ} (A : Square d) (E : ℝ) (hE : 0 ≤ E)
    (hentry : ∀ r s : Fin d, |A r s| ≤ E) : entryMax A ≤ E := by
  apply csSup_le (show ({0} ∪ Set.range (fun ij : Fin d × Fin d => |A ij.1 ij.2|)).Nonempty
    from ⟨0, Or.inl (by rfl)⟩)
  intro r hr
  rcases hr with hr | ⟨⟨i, j⟩, rfl⟩
  · have hr0 : r = 0 := hr
    simpa only [hr0] using hE
  · exact hentry i j

lemma entryMax_attained (d : ℕ) (hd : 1 ≤ d) (A : Square d) :
    ∃ r s : Fin d, |A r s| = entryMax A := by
  have hne : ({0} ∪ Set.range (fun ij : Fin d × Fin d => |A ij.1 ij.2|)).Nonempty :=
    ⟨0, Or.inl (by rfl)⟩
  have hmem := hne.csSup_mem (entryMax_finite A)
  change entryMax A ∈ {0} ∪ Set.range (fun ij : Fin d × Fin d => |A ij.1 ij.2|) at hmem
  rcases hmem with hz | ⟨⟨r, s⟩, he⟩
  · have hz0 : entryMax A = 0 := hz
    let r : Fin d := ⟨0, by omega⟩
    refine ⟨r, r, le_antisymm (abs_entry_le_entryMax A r r) ?_⟩
    rw [hz0]
    exact abs_nonneg _
  · exact ⟨r, s, he⟩

theorem entry_maximum_norm_comparison (d : ℕ) (hd : 1 ≤ d) (A : Square d) :
    (∃ r s : Fin d, |A r s| = entryMax A) ∧
    (∀ r s : Fin d, |A r s| ≤ entryMax A) ∧
    0 ≤ entryMax A ∧ entryMax A ≤ spectralNorm A ∧
    spectralNorm A ≤ (d : ℝ) * entryMax A := by
  refine ⟨entryMax_attained d hd A, abs_entry_le_entryMax A, entryMax_nonneg A, ?_, ?_⟩
  · exact entryMax_le_of_entry_bound A _ (spectralNorm_nonneg A) (abs_entry_le_spectralNorm A)
  · exact spectralNorm_le_entry_bound A _ (entryMax_nonneg A) (abs_entry_le_entryMax A)

#assert_trust kernel entry_maximum_norm_comparison
#print axioms entry_maximum_norm_comparison

end NLA.MF12
