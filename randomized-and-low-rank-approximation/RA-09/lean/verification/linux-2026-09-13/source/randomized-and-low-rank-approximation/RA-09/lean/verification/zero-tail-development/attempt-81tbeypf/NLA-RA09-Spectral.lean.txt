/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical transfer theorem: Matthew J. Colbrook.
Selected-basis semantics adapted from the separately reviewed RA08 Spectral
module; actual Frobenius identities and full truncation bridges are local.
-/
import NLA.RA09.Frobenius
import NLA.RA09.SpectralCFC
import NLA.RA09.OrderedExistence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA09

theorem orderedSpectral_semantics_proved {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) :
    A.PosSemidef ∧ spectralCombination d d.eigenvalues = A ∧
      (∀ i j : Fin n,
        (fun r => (d.orthogonal : RealMatrix n) r i) ⬝ᵥ
          (fun r => (d.orthogonal : RealMatrix n) r j) = if i = j then 1 else 0) ∧
      (∀ i : Fin n,
        A *ᵥ (fun r => (d.orthogonal : RealMatrix n) r i) =
          d.eigenvalues i • (fun r => (d.orthogonal : RealMatrix n) r i)) := by
  refine ⟨?_, d.reconstruct.symm, ?_, ?_⟩
  · have h := (Matrix.PosSemidef.diagonal d.nonnegative).mul_mul_conjTranspose_same
      (d.orthogonal : RealMatrix n)
    simpa only [conjTranspose_eq_transpose_of_trivial, ← d.reconstruct] using h
  · intro i j
    have h := congrArg (fun M : RealMatrix n => M i j) (orthogonal_transpose_mul d.orthogonal)
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, dotProduct] using h
  · intro i
    have hc : (fun r => (d.orthogonal : RealMatrix n) r i) =
        (d.orthogonal : RealMatrix n) *ᵥ Pi.single i 1 :=
      (Matrix.mulVec_single_one (d.orthogonal : RealMatrix n) i).symm
    rw [hc]
    conv_lhs => arg 1; rw [d.reconstruct]
    calc
      _ = (d.orthogonal : RealMatrix n) *ᵥ (diagonal d.eigenvalues *ᵥ
          (((d.orthogonal : RealMatrix n).transpose * (d.orthogonal : RealMatrix n)) *ᵥ
            Pi.single i 1)) := by simp only [mulVec_mulVec, mul_assoc]
      _ = _ := by
        rw [orthogonal_transpose_mul,  one_mulVec, diagonal_mulVec_single]
        simp only [mul_one, mulVec_single, op_smul_eq_smul, one_smul]

theorem spectralCombination_sub {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v w : Fin n → ℝ) :
    spectralCombination d v - spectralCombination d w =
      spectralCombination d (fun i => v i - w i) := by
  have hd : diagonal (fun i => v i - w i) = diagonal v - diagonal w :=
    (Matrix.diagonal_sub v w).symm
  simp only [spectralCombination, hd, mul_sub, sub_mul]

theorem spectralCombination_posSemidef {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (spectralCombination d v).PosSemidef := by
  simpa only [spectralCombination, conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosSemidef.diagonal hv).mul_mul_conjTranspose_same (d.orthogonal : RealMatrix n)

theorem spectralCombination_le {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v w : Fin n → ℝ) (h : ∀ i, v i ≤ w i) :
    spectralCombination d v ≤ spectralCombination d w := by
  apply sub_nonneg.mp
  rw [spectralCombination_sub]
  exact (spectralCombination_posSemidef d _ (fun i => sub_nonneg.mpr (h i))).nonneg

theorem spectralCombination_conjugate {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v : Fin n → ℝ) :
    (d.orthogonal : RealMatrix n).transpose * spectralCombination d v *
      (d.orthogonal : RealMatrix n) = diagonal v := by
  calc
    _ = ((d.orthogonal : RealMatrix n).transpose * (d.orthogonal : RealMatrix n)) *
        diagonal v * ((d.orthogonal : RealMatrix n).transpose * (d.orthogonal : RealMatrix n)) := by
      simp only [spectralCombination, mul_assoc]
    _ = _ := by rw [orthogonal_transpose_mul]; simp only [one_mul, mul_one]

theorem spectralCombination_injective {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) : Function.Injective (spectralCombination d) := by
  intro v w h
  have he := congrArg (fun M : RealMatrix n =>
    (d.orthogonal : RealMatrix n).transpose * M * (d.orthogonal : RealMatrix n)) h
  rw [spectralCombination_conjugate, spectralCombination_conjugate] at he
  funext i
  simpa only [diagonal_apply_eq] using congrArg (fun M : RealMatrix n => M i i) he

theorem frobeniusSquared_diagonal {n : ℕ} (v : Fin n → ℝ) :
    frobeniusSquared (diagonal v) = ∑ i, v i ^ 2 := by
  simp [frobeniusSquared, Matrix.diagonal]

theorem spectralCombination_frobenius {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (v : Fin n → ℝ) :
    frobeniusSquared (spectralCombination d v) = ∑ i, v i ^ 2 := by
  have ht : (d.orthogonal : RealMatrix n).transpose =
      ((star d.orthogonal : Matrix.unitaryGroup (Fin n) ℝ) : RealMatrix n) := by
    simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  unfold spectralCombination
  rw [ht, frobenius_orthogonal_invariance_proved, frobeniusSquared_diagonal]

theorem tail_square_sum {n : ℕ} (v : Fin n → ℝ) (k : ℕ) :
    (∑ i, (v i - if i.val < k then v i else 0)^2) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), v i ^ 2 := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi]

theorem truncation_semantics_proved {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (_hk : k ≤ n) (f : ℝ → ℝ) :
    (truncation d k).PosSemidef ∧ truncation d k ≤ A ∧
    frobeniusSquared (A - truncation d k) = spectralTail d k ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation d f k) =
      functionTail d f k ∧
    (truncation d k = A ↔ ∀ i : Fin n, k ≤ i.val → d.eigenvalues i = 0) := by
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply spectralCombination_posSemidef
    intro i
    split_ifs
    · exact d.nonnegative i
    · exact le_rfl
  · apply LE.le.trans_eq (b := spectralCombination d d.eigenvalues) ?_ hA.symm
    apply spectralCombination_le
    intro i
    split_ifs
    · exact le_rfl
    · exact d.nonnegative i
  · calc
      _ = frobeniusSquared (spectralCombination d d.eigenvalues - truncation d k) := by rw [← hA]
      _ = _ := by
        rw [truncation, spectralCombination_sub, spectralCombination_frobenius]
        exact tail_square_sum d.eigenvalues k
  · rw [selected_cfc_eq, functionTruncation, spectralCombination_sub, spectralCombination_frobenius]
    exact tail_square_sum _ k
  · constructor
    · intro h i hi
      have hv := congrFun (spectralCombination_injective d (h.trans hA)) i
      simpa only [Nat.not_lt.mpr hi, ↓reduceIte] using hv.symm
    · intro h
      apply Eq.trans (b := spectralCombination d d.eigenvalues) ?_ hA.symm
      apply congrArg (spectralCombination d)
      funext i
      by_cases hi : i.val < k
      · simp [hi]
      · simp [hi, h i (Nat.le_of_not_gt hi)]

#assert_trust kernel orderedSpectral_semantics_proved
#assert_trust kernel truncation_semantics_proved
#print axioms orderedSpectral_semantics_proved
#print axioms truncation_semantics_proved

end NLA.RA09
