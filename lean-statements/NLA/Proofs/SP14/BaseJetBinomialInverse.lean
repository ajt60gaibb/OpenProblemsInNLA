import NLA.Proofs.SP14.BaseJetTriangular
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
The source's explicit finite binomial inverse for the base triangular
Jacobian. This finite preconditioner alone supplies no analytic background
operator or Sobolev bounds.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

noncomputable def baseInverseCoeff (n : ℕ) : ℝ :=
  Ring.choose (-1 / 2 : ℝ) n

noncomputable def baseJetInverseMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  fun d k => if d ≤ k then
    -(1 / 2 : ℝ) * baseInverseCoeff (k.val - d.val) / (k.val + 1 : ℝ)
  else 0

theorem baseCoeffReal_inverse_convolution (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n,
      baseCoeffReal p.1 * baseInverseCoeff p.2) =
      if n = 0 then 1 else 0 := by
  have hseries :
      PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) *
        PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) = 1 := by
    rw [← PowerSeries.binomialSeries_add]
    norm_num
  have h := congrArg (PowerSeries.coeff n) hseries
  simpa [baseCoeffReal, baseInverseCoeff, PowerSeries.coeff_mul,
    PowerSeries.coeff_one] using h

private theorem baseCoeffReal_inverse_convolution_rev (n : ℕ) :
    (∑ r ∈ Finset.range (n + 1),
      baseInverseCoeff r * baseCoeffReal (n - r)) =
      if n = 0 then 1 else 0 := by
  have hseries :
      PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) *
        PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) = 1 := by
    rw [← PowerSeries.binomialSeries_add]
    norm_num
  have h := congrArg (PowerSeries.coeff n) hseries
  have hconv :
      (∑ p ∈ Finset.antidiagonal n,
        baseInverseCoeff p.1 * baseCoeffReal p.2) =
        if n = 0 then 1 else 0 := by
    simpa [baseCoeffReal, baseInverseCoeff, PowerSeries.coeff_mul,
      PowerSeries.coeff_one] using h
  simpa only [Nat.succ_eq_add_one] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun r s => baseInverseCoeff r * baseCoeffReal s) n).symm.trans hconv

theorem baseJetInverseMatrix_mul_baseJetMatrix (q : ℕ) :
    baseJetInverseMatrix q * baseJetMatrix q = 1 := by
  ext d e
  by_cases hde : d.val ≤ e.val
  · let f : ℕ → ℝ := fun k =>
      (if d.val ≤ k then
        -(1 / 2 : ℝ) * baseInverseCoeff (k - d.val) / (k + 1 : ℝ)
       else 0) *
      (if k ≤ e.val then
        -2 * (k + 1 : ℝ) * baseCoeffReal (e.val - k)
       else 0)
    have hsum : (baseJetInverseMatrix q * baseJetMatrix q) d e =
        ∑ r ∈ Finset.range (e.val - d.val + 1),
          baseInverseCoeff r * baseCoeffReal (e.val - d.val - r) := by
      calc
        (baseJetInverseMatrix q * baseJetMatrix q) d e =
            ∑ k ∈ Finset.range q, f k := by
          rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          have hkq : k < q := Finset.mem_range.mp hk
          by_cases hdk : d.val ≤ k <;> by_cases hke : k ≤ e.val <;>
            simp [f, baseJetInverseMatrix, baseJetMatrix, hkq,
              Fin.le_iff_val_le_val, hdk, hke]
        _ = ∑ k ∈ Finset.Ico d.val (e.val + 1), f k := by
          symm
          apply Finset.sum_subset
          · intro k hk
            simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
            omega
          · intro k hk hk'
            have hnot : k < d.val ∨ e.val < k := by
              simp only [Finset.mem_Ico, not_and, not_lt] at hk'
              omega
            rcases hnot with hleft | hright
            · simp [f, show ¬ d.val ≤ k by omega]
            · simp [f, show ¬ k ≤ e.val by omega]
        _ = ∑ k ∈ Finset.Ico d.val (e.val + 1),
              baseInverseCoeff (k - d.val) * baseCoeffReal (e.val - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hdk : d.val ≤ k := (Finset.mem_Ico.mp hk).1
          have hke : k ≤ e.val := by have := (Finset.mem_Ico.mp hk).2; omega
          have hk1 : (k + 1 : ℝ) ≠ 0 := by positivity
          simp only [f, if_pos hdk, if_pos hke]
          field_simp
        _ = ∑ r ∈ Finset.range (e.val - d.val + 1),
              baseInverseCoeff r * baseCoeffReal (e.val - d.val - r) := by
          rw [Finset.sum_Ico_eq_sum_range]
          have hlen : e.val + 1 - d.val = e.val - d.val + 1 := by omega
          rw [hlen]
          apply Finset.sum_congr rfl
          intro r hr
          have hrle : r ≤ e.val - d.val := by
            have := Finset.mem_range.mp hr
            omega
          have hfirst : d.val + r - d.val = r := by omega
          have hsecond : e.val - (d.val + r) = e.val - d.val - r := by omega
          simp [hfirst, hsecond]
    rw [hsum, baseCoeffReal_inverse_convolution_rev]
    have hzero : e.val - d.val = 0 ↔ d.val = e.val := by omega
    simp [Matrix.one_apply, Fin.ext_iff, hzero]
  · have hleft : (baseJetInverseMatrix q * baseJetMatrix q) d e = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hdk : d.val ≤ k.val
      · have hke : ¬ k.val ≤ e.val := by omega
        have hz : baseJetMatrix q k e = 0 := by
          simp [baseJetMatrix, Fin.le_iff_val_le_val, hke]
        simp [hz]
      · have hz : baseJetInverseMatrix q d k = 0 := by
          simp [baseJetInverseMatrix, Fin.le_iff_val_le_val, hdk]
        simp [hz]
    rw [hleft]
    have hne : d ≠ e := by intro h; exact hde (Fin.ext_iff.mp h).le
    simp [hne]

theorem baseJetMatrix_mul_inverseMatrix (q : ℕ) :
    baseJetMatrix q * baseJetInverseMatrix q = 1 := by
  have hunit : IsUnit (baseJetMatrix q).det :=
    isUnit_iff_ne_zero.mpr (baseJetMatrix_det_ne_zero q)
  have hN : baseJetInverseMatrix q = (baseJetMatrix q)⁻¹ := by
    calc
      baseJetInverseMatrix q = baseJetInverseMatrix q * 1 := (Matrix.mul_one _).symm
      _ = baseJetInverseMatrix q *
          (baseJetMatrix q * (baseJetMatrix q)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hunit]
      _ = (baseJetInverseMatrix q * baseJetMatrix q) *
          (baseJetMatrix q)⁻¹ := by rw [Matrix.mul_assoc]
      _ = (baseJetMatrix q)⁻¹ := by
            rw [baseJetInverseMatrix_mul_baseJetMatrix, Matrix.one_mul]
  rw [hN]
  exact Matrix.mul_nonsing_inv _ hunit

theorem baseJetSolve_eq_explicit (q : ℕ) (x : Fin q → ℝ) :
    baseJetSolve q x = (baseJetInverseMatrix q).mulVec x := by
  have hunit : IsUnit (baseJetMatrix q).det :=
    isUnit_iff_ne_zero.mpr (baseJetMatrix_det_ne_zero q)
  have hN : baseJetInverseMatrix q = (baseJetMatrix q)⁻¹ := by
    calc
      baseJetInverseMatrix q = baseJetInverseMatrix q * 1 := (Matrix.mul_one _).symm
      _ = baseJetInverseMatrix q *
          (baseJetMatrix q * (baseJetMatrix q)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ hunit]
      _ = (baseJetInverseMatrix q * baseJetMatrix q) *
          (baseJetMatrix q)⁻¹ := by rw [Matrix.mul_assoc]
      _ = (baseJetMatrix q)⁻¹ := by
            rw [baseJetInverseMatrix_mul_baseJetMatrix, Matrix.one_mul]
  simp [baseJetSolve, hN]

#assert_trust kernel baseCoeffReal_inverse_convolution
#assert_trust kernel baseJetInverseMatrix_mul_baseJetMatrix
#assert_trust kernel baseJetMatrix_mul_inverseMatrix
#assert_trust kernel baseJetSolve_eq_explicit
#print axioms baseJetSolve_eq_explicit

end NLA.Proofs.SP14
