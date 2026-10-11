import NLA.Proofs.MF03.PadeToeplitzCramer
import Mathlib.GroupTheory.Perm.Fin

/-! MF-03 exact all-order Cramer numerator/augmented determinant identity. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

private noncomputable def augMatrix (m j : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun r v => cosineElementaryCoeff
    (m + (if r.val < j then 1 else 0) + v.val - r.val)

private theorem cramer_permuted_matrix (n : ℕ) (c : Fin (n + 1)) :
    (Matrix.transpose ((cosinePadeToeplitz (n + 1)).updateCol c
        (cosinePadeRHS (n + 1)))).submatrix
          c.cycleRange.symm (Equiv.refl _) =
      (augMatrix (n + 1) (c.val + 1)).updateRow 0
        ((-1 : ℝ) • (augMatrix (n + 1) (c.val + 1)) 0) := by
  ext r v
  cases r using Fin.cases with
  | zero =>
      simp [Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.updateRow_apply,
        Fin.cycleRange_symm_zero, cosinePadeRHS, augMatrix,
        add_comm, add_left_comm]
  | succ i =>
      have hz : (Fin.succ i : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
      rw [Matrix.submatrix_apply, Matrix.transpose_apply,
        Fin.cycleRange_symm_succ]
      by_cases h : i.castSucc < c
      · rw [Fin.succAbove_of_castSucc_lt c i h]
        have hne : (i.castSucc : Fin (n + 1)) ≠ c := ne_of_lt h
        have hrow : (Fin.succ i).val < c.val + 1 := by
          have hv := Fin.lt_def.mp h
          simp only [Fin.val_castSucc, Fin.val_succ] at hv ⊢
          omega
        simp only [Matrix.updateCol_apply, if_neg hne,
          Matrix.updateRow_apply, if_neg hz, cosinePadeToeplitz,
          augMatrix, hrow, if_pos, Equiv.refl_apply]
        congr 1
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      · have hle : c ≤ i.castSucc := le_of_not_gt h
        rw [Fin.succAbove_of_le_castSucc c i hle]
        have hne : (Fin.succ i : Fin (n + 1)) ≠ c := by
          intro heq
          have hv := Fin.le_iff_val_le_val.mp hle
          have heqv := congrArg Fin.val heq
          simp only [Fin.val_castSucc, Fin.val_succ] at hv heqv
          omega
        have hrow : ¬ (Fin.succ i).val < c.val + 1 := by
          have hv := Fin.le_iff_val_le_val.mp hle
          simp only [Fin.val_castSucc, Fin.val_succ] at hv ⊢
          omega
        simp only [Matrix.updateCol_apply, if_neg hne,
          Matrix.updateRow_apply, if_neg hz, cosinePadeToeplitz,
          augMatrix, hrow, Equiv.refl_apply]
        rfl

/-- Exact original augmented determinant for each unnormalized Cramer
coordinate, including the negative right-hand-side sign. -/
theorem cosinePadeToeplitz_cramer_eq_augDet (m : ℕ) (c : Fin m) :
    (cosinePadeToeplitz m).cramer (cosinePadeRHS m) c =
      (-1 : ℝ) ^ (c.val + 1) * cosineAugDet m (c.val + 1) := by
  cases m with
  | zero => exact Fin.elim0 c
  | succ n =>
      let A := augMatrix (n + 1) (c.val + 1)
      have hmat := cramer_permuted_matrix n c
      have hdet := congrArg Matrix.det hmat
      change ((Matrix.transpose ((cosinePadeToeplitz (n + 1)).updateCol c
        (cosinePadeRHS (n + 1)))).submatrix c.cycleRange.symm id).det =
        ((augMatrix (n + 1) (c.val + 1)).updateRow 0
          ((-1 : ℝ) • (augMatrix (n + 1) (c.val + 1)) 0)).det at hdet
      rw [Matrix.det_permute] at hdet
      rw [Matrix.det_updateRow_smul, Matrix.updateRow_eq_self] at hdet
      rw [Matrix.det_transpose] at hdet
      rw [← Matrix.cramer_apply] at hdet
      rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange] at hdet
      norm_num at hdet
      change (-1 : ℝ) ^ c.val *
          (cosinePadeToeplitz (n + 1)).cramer (cosinePadeRHS (n + 1)) c =
        -cosineAugDet (n + 1) (c.val + 1) at hdet
      have hs : ((-1 : ℝ) ^ c.val) * ((-1 : ℝ) ^ c.val) = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (cosinePadeToeplitz (n + 1)).cramer (cosinePadeRHS (n + 1)) c =
            1 * (cosinePadeToeplitz (n + 1)).cramer (cosinePadeRHS (n + 1)) c :=
          (one_mul _).symm
        _ = ((-1 : ℝ) ^ c.val * (-1 : ℝ) ^ c.val) *
            (cosinePadeToeplitz (n + 1)).cramer (cosinePadeRHS (n + 1)) c := by
          rw [hs]
        _ = (-1 : ℝ) ^ c.val *
            ((-1 : ℝ) ^ c.val *
              (cosinePadeToeplitz (n + 1)).cramer (cosinePadeRHS (n + 1)) c) := by
          ring
        _ = (-1 : ℝ) ^ c.val * -cosineAugDet (n + 1) (c.val + 1) := by
          rw [hdet]
        _ = (-1 : ℝ) ^ (c.val + 1) * cosineAugDet (n + 1) (c.val + 1) := by
          rw [pow_succ]
          ring

#assert_trust kernel cosinePadeToeplitz_cramer_eq_augDet
#print axioms cosinePadeToeplitz_cramer_eq_augDet

end NLA.Proofs.MF03
