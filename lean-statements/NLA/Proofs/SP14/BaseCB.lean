import NLA.Proofs.SP14.BaseCoefficient
import NLA.Proofs.SP14.BaseProductBlock

/-!
The unconditional finite matrix product for the SP-14 exterior square-root
base coefficients. This is finite algebra only; the analytic Fourier
identification with the actual Toeplitz sections is still separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The upper triangular Toeplitz matrix of the normalized square-root
binomial coefficients. -/
noncomputable def baseG (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => if i.val ≤ j.val then baseCoeff (j.val - i.val) else 0

/-- Its selected last columns are the even-row/odd-column block. -/
noncomputable def baseB (m : ℕ) : Matrix (Fin (m + 1)) (Fin m) ℂ :=
  (baseG m).submatrix id Fin.succ

/-- Its selected first rows are the odd-row/even-column block. -/
noncomputable def baseC (m : ℕ) : Matrix (Fin m) (Fin (m + 1)) ℂ :=
  (baseG m).submatrix Fin.castSucc id

private theorem baseCoeff_convolution_range (n : ℕ) :
    (∑ r ∈ Finset.range (n + 1), baseCoeff r * baseCoeff (n - r)) =
      (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0) := by
  calc
    (∑ r ∈ Finset.range (n + 1), baseCoeff r * baseCoeff (n - r)) =
        ∑ p ∈ Finset.antidiagonal n, baseCoeff p.1 * baseCoeff p.2 := by
      simpa only [Nat.succ_eq_add_one] using
        (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun r s => baseCoeff r * baseCoeff s) n).symm
    _ = _ := baseCoeff_convolution n

/-- The finite upper Toeplitz coefficient matrix squares to `I+U`. -/
theorem baseG_square (m : ℕ) :
    baseG m * baseG m = 1 + baseUpperShift m := by
  ext i j
  by_cases hij : i.val ≤ j.val
  · let f : ℕ → ℂ := fun k =>
      (if i.val ≤ k then baseCoeff (k - i.val) else 0) *
        (if k ≤ j.val then baseCoeff (j.val - k) else 0)
    have hsum : (baseG m * baseG m) i j =
        ∑ r ∈ Finset.range (j.val - i.val + 1),
          baseCoeff r * baseCoeff (j.val - i.val - r) := by
      calc
        (baseG m * baseG m) i j = ∑ k ∈ Finset.range (m + 1), f k := by
          rw [Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
          apply Finset.sum_congr rfl
          intro k hk
          have hkm : k < m + 1 := Finset.mem_range.mp hk
          simp [f, baseG, hkm]
        _ = ∑ k ∈ Finset.Ico i.val (j.val + 1), f k := by
          symm
          apply Finset.sum_subset
          · intro k hk
            simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
            omega
          · intro k hk hk'
            have hnot : k < i.val ∨ j.val < k := by
              simp only [Finset.mem_Ico, not_and, not_lt] at hk'
              omega
            rcases hnot with hleft | hright
            · simp [f, show ¬ i.val ≤ k by omega]
            · simp [f, show ¬ k ≤ j.val by omega]
        _ = ∑ k ∈ Finset.Ico i.val (j.val + 1),
              baseCoeff (k - i.val) * baseCoeff (j.val - k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hik : i.val ≤ k := (Finset.mem_Ico.mp hk).1
          have hkj : k ≤ j.val := by have := (Finset.mem_Ico.mp hk).2; omega
          simp [f, hik, hkj]
        _ = ∑ r ∈ Finset.range (j.val - i.val + 1),
              baseCoeff r * baseCoeff (j.val - i.val - r) := by
          rw [Finset.sum_Ico_eq_sum_range]
          have hlen : j.val + 1 - i.val = j.val - i.val + 1 := by omega
          rw [hlen]
          apply Finset.sum_congr rfl
          intro r hr
          have hrle : r ≤ j.val - i.val := by
            have := Finset.mem_range.mp hr
            omega
          have hfirst : i.val + r - i.val = r := by omega
          have hsecond : j.val - (i.val + r) = j.val - i.val - r := by omega
          simp [hfirst, hsecond]
    rw [hsum, baseCoeff_convolution_range]
    have hzero : j.val - i.val = 0 ↔ i.val = j.val := by omega
    have hone : j.val - i.val = 1 ↔ j.val = i.val + 1 := by omega
    simp [Matrix.add_apply, Matrix.one_apply, baseUpperShift,
      Fin.ext_iff, hzero, hone]
  · have hleft : (baseG m * baseG m) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hik : i.val ≤ k.val
      · have hkj : ¬ k.val ≤ j.val := by omega
        simp [baseG, hik, hkj]
      · simp [baseG, hik]
    rw [hleft]
    have hdiag : i ≠ j := by intro h; exact hij (Fin.ext_iff.mp h).le
    have hshift : j.val ≠ i.val + 1 := by omega
    simp [Matrix.add_apply, baseUpperShift,
      hdiag, hshift]

/-- The reviewed unconditional finite `C*B` product, including `m=0`. -/
theorem baseC_mul_baseB (m : ℕ) : baseC m * baseB m = baseBlock m := by
  exact base_selected_product m (baseG m) (baseG_square m)

#assert_trust kernel baseG_square
#assert_trust kernel baseC_mul_baseB
#print axioms baseC_mul_baseB

end NLA.Proofs.SP14
