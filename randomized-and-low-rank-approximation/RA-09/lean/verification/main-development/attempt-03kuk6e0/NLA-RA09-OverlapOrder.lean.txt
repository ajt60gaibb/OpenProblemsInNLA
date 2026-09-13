/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical transfer theorem: Matthew J. Colbrook.
Actual PSD order gives every harmonic constraint on the overlap columns.
-/
import NLA.RA09.Overlap
import NLA.RA09.Harmonic

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA09

theorem spectralCombination_single {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (j : Fin n) (b : ℝ) :
    spectralCombination d (Pi.single j b) =
      b • outerSquare (fun i => (d.orthogonal : RealMatrix n) i j) := by
  ext i l
  rw [spectralCombination_entry]
  simp [Pi.single_apply, outerSquare, Matrix.smul_apply, smul_eq_mul, mul_comm, mul_assoc]

theorem selected_rankOne_le {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (j : Fin n) :
    d.eigenvalues j • outerSquare (fun i => (d.orthogonal : RealMatrix n) i j) ≤ A := by
  have hs : spectralCombination d (Pi.single j (d.eigenvalues j)) ≤
      spectralCombination d d.eigenvalues := by
    apply spectralCombination_le
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi, d.nonnegative i]
  rw [spectralCombination_single] at hs
  exact hs.trans_eq d.reconstruct.symm

theorem outerSquare_conjugate {n : ℕ} (Q : RealMatrix n) (v : Fin n → ℝ) :
    Q.transpose * outerSquare v * Q = outerSquare (Q.transpose *ᵥ v) := by
  change Q.transpose * vecMulVec v v * Q =
    vecMulVec (Q.transpose *ᵥ v) (Q.transpose *ᵥ v)
  rw [mul_vecMulVec, vecMulVec_mul]
  congr 1
  ext i
  simp only [vecMul, mulVec, dotProduct, transpose_apply, mul_comm]

theorem overlap_rankOne_order {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (horder : Ahat ≤ A) (j : Fin n) :
    (diagonal dA.eigenvalues - dHat.eigenvalues j •
      outerSquare (fun i => overlapMatrix dA dHat i j)).PosSemidef := by
  have hless := (selected_rankOne_le dHat j).trans horder
  have hp := (sub_nonneg.mpr hless).posSemidef
  have hc := hp.conjTranspose_mul_mul_same (dA.orthogonal : RealMatrix n)
  have hA : (dA.orthogonal : RealMatrix n).transpose * A * (dA.orthogonal : RealMatrix n) =
      diagonal dA.eigenvalues := by
    exact (congrArg (fun M : RealMatrix n =>
      (dA.orthogonal : RealMatrix n).transpose * M * (dA.orthogonal : RealMatrix n))
        dA.reconstruct).trans (spectralCombination_conjugate dA dA.eigenvalues)
  have hv : (dA.orthogonal : RealMatrix n).transpose *ᵥ
      (fun i => (dHat.orthogonal : RealMatrix n) i j) =
        (fun i => overlapMatrix dA dHat i j) := by
    funext i
    simp only [overlapMatrix, mul_apply, mulVec, dotProduct, transpose_apply]
  have he : (dA.orthogonal : RealMatrix n).transpose *
      (A - dHat.eigenvalues j • outerSquare (fun i => (dHat.orthogonal : RealMatrix n) i j)) *
        (dA.orthogonal : RealMatrix n) =
      diagonal dA.eigenvalues - dHat.eigenvalues j • outerSquare (fun i => overlapMatrix dA dHat i j) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hA, outerSquare_conjugate, hv]
  simpa only [conjTranspose_eq_transpose_of_trivial, he] using hc

theorem overlap_semantics_proved {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (horder : Ahat ≤ A) (k : ℕ) (_hk : k ≤ n) :
    (∀ i j, 0 ≤ overlapWeights dA dHat i j) ∧
    (∀ j, ∑ i, overlapWeights dA dHat i j = 1) ∧
    (∀ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      overlapWeights dA dHat i j ≤ 1) ∧
    (∀ j : Fin n, 0 < dHat.eigenvalues j →
      (∀ i, dA.eigenvalues i = 0 → overlapWeights dA dHat i j = 0) ∧
      dHat.eigenvalues j *
        (∑ i, overlapWeights dA dHat i j / dA.eigenvalues i) ≤ 1) := by
  refine ⟨fun i j => sq_nonneg _, overlap_column_sum dA dHat, ?_, ?_⟩
  · intro i
    calc
      _ ≤ ∑ j, overlapWeights dA dHat i j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => sq_nonneg _)
      _ = 1 := overlap_row_sum dA dHat i
  · intro j hj
    have h := harmonic_constraint_proved dA.eigenvalues
      (fun i => overlapMatrix dA dHat i j) (dHat.eigenvalues j)
      dA.nonnegative (overlap_column_sum dA dHat j) hj (overlap_rankOne_order dA dHat horder j)
    refine ⟨?_, h.2⟩
    intro i hi
    simp only [overlapWeights, h.1 i hi, zero_pow (by decide : 2 ≠ 0)]

#assert_trust kernel overlap_semantics_proved
#print axioms overlap_semantics_proved

end NLA.RA09
