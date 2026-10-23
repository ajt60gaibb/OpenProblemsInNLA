import NLA.Proofs.PF05.ZeroPair

/-! Explicit congruence normal form for nonzero orthogonal PSD pairs in size two.
The primal and dual use the same invertible matrix, as in the frozen PF-05 target. -/
set_option autoImplicit false
namespace NLA.Proofs.PF05

private theorem primal_normalization_algebra
    (a b c r s : ℝ) (ha : a ≠ 0) (hr : r * r = a)
    (hdet : a * c = b * b) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![1/r, -(b*s/a); 0,s]
     S.transpose * !![a,b;b,c] * S = !![1,0;0,0]) := by
  have hrne : r ≠ 0 := by
    intro hz
    apply ha
    rw [← hr, hz]
    ring
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hrne] <;>
    field_simp [ha, hrne] <;> nlinarith [hr, hdet]

private theorem dual_factorization_algebra
    (a b d e f r s : ℝ) (ha : a ≠ 0) (hr : r * r = a)
    (hs : s * s = d) (h01 : a * e + b * d = 0)
    (h00 : a * f + b * e = 0) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![1/r, -(b*s/a); 0,s]
     S * !![0,0;0,1] * S.transpose = !![f,e;e,d]) := by
  have hrne : r ≠ 0 := by
    intro hz
    apply ha
    rw [← hr, hz]
    ring
  have hff : a * a * f = b * b * d := by
    linear_combination a * h00 - b * h01
  have hffS : a * a * f = b * b * (s * s) := by rw [hs]; exact hff
  have h01S : a * e + b * (s * s) = 0 := by rw [hs]; exact h01
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [ha, hrne] <;> nlinarith [hs, h01S, hffS]

private theorem dual_normalize_of_congruence
    (S B Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hdet : S.det ≠ 0) (hB : B = S * Q * S.transpose) :
    S⁻¹ * B * (S⁻¹).transpose = Q := by
  have hunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hdet
  have hleft : S⁻¹ * S = 1 := S.nonsing_inv_mul hunit
  have hright : S.transpose * (S⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
  calc
    S⁻¹ * B * (S⁻¹).transpose
        = (S⁻¹ * S) * Q * (S.transpose * (S⁻¹).transpose) := by
            rw [hB]
            simp [Matrix.mul_assoc]
    _ = Q := by rw [hleft, hright]; simp

theorem normalize_zero_pair_of_A00_pos
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : NLA.Statements.PF05.PositiveSemidefinite A)
    (hB : NLA.Statements.PF05.PositiveSemidefinite B)
    (hB0 : B ≠ 0) (htrace : Matrix.trace (A * B) = 0)
    (ha : 0 < A 0 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ,
      S.det ≠ 0 ∧
      S.transpose * A * S = !![1,0;0,0] ∧
      S⁻¹ * B * (S⁻¹).transpose = !![0,0;0,1] := by
  obtain ⟨hd, hdetA, h01, h00⟩ :=
    zero_pair_coordinates_of_A00_pos A B hA hB hB0 htrace ha
  let r := Real.sqrt (A 0 0)
  let s := Real.sqrt (B 1 1)
  have hrpos : 0 < r := Real.sqrt_pos.2 ha
  have hspos : 0 < s := Real.sqrt_pos.2 hd
  have hr : r * r = A 0 0 := by
    simpa [pow_two] using Real.sq_sqrt ha.le
  have hs : s * s = B 1 1 := by
    simpa [pow_two] using Real.sq_sqrt hd.le
  let S : Matrix (Fin 2) (Fin 2) ℝ :=
    !![1/r, -(A 0 1 * s / A 0 0); 0,s]
  have hAeta : A = !![A 0 0, A 0 1; A 0 1, A 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA.1 1 0]
  have hBeta : B = !![B 0 0, B 0 1; B 0 1, B 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB.1 1 0]
  have hdetS : S.det ≠ 0 := by
    simp [S, Matrix.det_fin_two_of, ne_of_gt hrpos, ne_of_gt hspos]
  have hprimal : S.transpose * A * S = !![1,0;0,0] := by
    rw [hAeta]
    exact primal_normalization_algebra _ _ _ r s (ne_of_gt ha) hr (by simpa [sq] using hdetA)
  have hBfact : B = S * !![0,0;0,1] * S.transpose := by
    rw [hBeta]
    exact (dual_factorization_algebra _ _ _ _ _ r s (ne_of_gt ha) hr hs h01 h00).symm
  exact ⟨S, hdetS, hprimal,
    dual_normalize_of_congruence S B !![0,0;0,1] hdetS hBfact⟩

private theorem primal_normalization_algebra_swap
    (a b c r s : ℝ) (hc : c ≠ 0) (hr : r * r = c)
    (hdet : a * c = b * b) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![0,s;1/r,-(b*s/c)]
     S.transpose * !![a,b;b,c] * S = !![1,0;0,0]) := by
  have hrne : r ≠ 0 := by
    intro hz
    apply hc
    rw [← hr, hz]
    ring
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hrne] <;>
    field_simp [hc, hrne] <;> nlinarith [hr, hdet]

private theorem dual_factorization_algebra_swap
    (b c d e f r s : ℝ) (hc : c ≠ 0) (hr : r * r = c)
    (hs : s * s = d) (h01 : b * d + c * e = 0)
    (h11 : b * e + c * f = 0) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![0,s;1/r,-(b*s/c)]
     S * !![0,0;0,1] * S.transpose = !![d,e;e,f]) := by
  have hrne : r ≠ 0 := by
    intro hz
    apply hc
    rw [← hr, hz]
    ring
  have hff : c * c * f = b * b * d := by
    linear_combination c * h11 - b * h01
  have hffS : c * c * f = b * b * (s * s) := by rw [hs]; exact hff
  have h01S : b * (s * s) + c * e = 0 := by rw [hs]; exact h01
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hc, hrne] <;> nlinarith [hs, h01S, hffS]

theorem normalize_zero_pair_of_A11_pos
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : NLA.Statements.PF05.PositiveSemidefinite A)
    (hB : NLA.Statements.PF05.PositiveSemidefinite B)
    (hB0 : B ≠ 0) (htrace : Matrix.trace (A * B) = 0)
    (hc : 0 < A 1 1) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ,
      S.det ≠ 0 ∧
      S.transpose * A * S = !![1,0;0,0] ∧
      S⁻¹ * B * (S⁻¹).transpose = !![0,0;0,1] := by
  obtain ⟨hd, hdetA, h01, h11⟩ :=
    zero_pair_coordinates_of_A11_pos A B hA hB hB0 htrace hc
  let r := Real.sqrt (A 1 1)
  let s := Real.sqrt (B 0 0)
  have hrpos : 0 < r := Real.sqrt_pos.2 hc
  have hspos : 0 < s := Real.sqrt_pos.2 hd
  have hr : r * r = A 1 1 := by
    simpa [pow_two] using Real.sq_sqrt hc.le
  have hs : s * s = B 0 0 := by
    simpa [pow_two] using Real.sq_sqrt hd.le
  let S : Matrix (Fin 2) (Fin 2) ℝ :=
    !![0,s;1/r,-(A 0 1 * s / A 1 1)]
  have hAeta : A = !![A 0 0, A 0 1; A 0 1, A 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hA.1 1 0]
  have hBeta : B = !![B 0 0, B 0 1; B 0 1, B 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hB.1 1 0]
  have hdetS : S.det ≠ 0 := by
    simp [S, Matrix.det_fin_two_of, ne_of_gt hrpos, ne_of_gt hspos]
  have hprimal : S.transpose * A * S = !![1,0;0,0] := by
    rw [hAeta]
    exact primal_normalization_algebra_swap _ _ _ r s (ne_of_gt hc) hr
      (by simpa [sq] using hdetA)
  have hBfact : B = S * !![0,0;0,1] * S.transpose := by
    rw [hBeta]
    exact (dual_factorization_algebra_swap _ _ _ _ _ r s (ne_of_gt hc) hr hs h01 h11).symm
  exact ⟨S, hdetS, hprimal,
    dual_normalize_of_congruence S B !![0,0;0,1] hdetS hBfact⟩

/-- The normal form for a nonzero zero-trace PSD pair in size two. -/
theorem normalize_nonzero_zero_pair
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : NLA.Statements.PF05.PositiveSemidefinite A)
    (hB : NLA.Statements.PF05.PositiveSemidefinite B)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (htrace : Matrix.trace (A * B) = 0) :
    ∃ S : Matrix (Fin 2) (Fin 2) ℝ,
      S.det ≠ 0 ∧
      S.transpose * A * S = !![1,0;0,0] ∧
      S⁻¹ * B * (S⁻¹).transpose = !![0,0;0,1] := by
  rcases nonzero_psd_two_positive_diagonal A hA hA0 with ha | hc
  · exact normalize_zero_pair_of_A00_pos A B hA hB hB0 htrace ha
  · exact normalize_zero_pair_of_A11_pos A B hA hB hB0 htrace hc

end NLA.Proofs.PF05
