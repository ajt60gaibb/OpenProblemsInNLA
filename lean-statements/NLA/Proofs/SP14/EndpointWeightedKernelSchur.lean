import NLA.Proofs.SP14.EndpointSchurBounds

/-!
Finite Schur inequalities for the actual Fourier-defined endpoint extension
kernel. This does not yet construct a bounded infinite-dimensional operator.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The actual absolute Fourier kernel in the square-root majorant form. -/
theorem endpointKernelAbs_le_sqrt (j k : ℕ) (hj : 1 ≤ j) :
    endpointKernelAbs j k ≤
      Real.sqrt (((k + 1 : ℕ) : ℝ)) / (((j + k : ℕ) : ℝ)) /
        Real.sqrt (j : ℝ) := by
  have hn : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hjp : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hd : (0 : ℝ) < (((j + k : ℕ) : ℝ)) := by exact_mod_cast (by omega : 0 < j + k)
  have hsn : 0 < Real.sqrt (((k + 1 : ℕ) : ℝ)) := Real.sqrt_pos.2 hn
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.2 hjp
  have hnum : (k : ℝ) + 1 / 2 ≤ (((k + 1 : ℕ) : ℝ)) := by
    push_cast
    linarith
  calc
    endpointKernelAbs j k ≤
        ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
          (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
          (1 / Real.sqrt (j : ℝ)) := endpointKernelAbs_le k j hj
    _ ≤ (((k + 1 : ℕ) : ℝ)) / ((j + k : ℕ) : ℝ) *
          (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
          (1 / Real.sqrt (j : ℝ)) := by
      have hratio : ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) ≤
          (((k + 1 : ℕ) : ℝ)) / ((j + k : ℕ) : ℝ) := by
        rw [Nat.add_comm k j]
        exact div_le_div_of_nonneg_right hnum hd.le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hratio (by positivity)) (by positivity)
    _ = Real.sqrt (((k + 1 : ℕ) : ℝ)) / (((j + k : ℕ) : ℝ)) /
          Real.sqrt (j : ℝ) := by
      field_simp
      nlinarith [Real.sq_sqrt hn.le]

/-- Sobolev-weighted entry of the actual Fourier-defined kernel. -/
noncomputable def endpointWeightedKernel (r : ℝ) (j k : ℕ) : ℝ :=
  (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) * endpointKernelAbs j k

theorem endpointWeightedKernel_le_row (r : ℝ) (j k : ℕ) (hj : 1 ≤ j) :
    endpointWeightedKernel r j k ≤
      endpointSchurRowTerm r j k *
        Real.sqrt (((k + 1 : ℕ) : ℝ)) / Real.sqrt (j : ℝ) := by
  have hK := endpointKernelAbs_le_sqrt j k hj
  have hfac : 0 ≤ (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) := by positivity
  unfold endpointWeightedKernel endpointSchurRowTerm
  calc
    _ ≤ (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) *
          (Real.sqrt (((k + 1 : ℕ) : ℝ)) / (((j + k : ℕ) : ℝ)) /
            Real.sqrt (j : ℝ)) := mul_le_mul_of_nonneg_left hK hfac
    _ = (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) /
          (((j + k : ℕ) : ℝ)) *
            Real.sqrt (((k + 1 : ℕ) : ℝ)) / Real.sqrt (j : ℝ) := by ring

theorem endpointWeightedKernel_row_pointwise (r : ℝ) (j k : ℕ) (hj : 1 ≤ j) :
    endpointWeightedKernel r j k *
        (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) ≤
      (1 / Real.sqrt (j : ℝ)) * endpointSchurRowTerm r j k := by
  have hn : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hsn : 0 < Real.sqrt (((k + 1 : ℕ) : ℝ)) := Real.sqrt_pos.2 hn
  have hM := endpointWeightedKernel_le_row r j k hj
  have hmul := mul_le_mul_of_nonneg_right hM (by positivity :
    0 ≤ 1 / Real.sqrt (((k + 1 : ℕ) : ℝ)))
  calc
    _ ≤ (endpointSchurRowTerm r j k *
          Real.sqrt (((k + 1 : ℕ) : ℝ)) / Real.sqrt (j : ℝ)) *
          (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) := hmul
    _ = (1 / Real.sqrt (j : ℝ)) * endpointSchurRowTerm r j k := by
      field_simp

/-- The finite row Schur inequality, with arbitrary cutoff including zero. -/
theorem endpointWeightedKernel_row_sum_le (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (j N : ℕ) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.range N,
      endpointWeightedKernel r j k *
        (1 / Real.sqrt (((k + 1 : ℕ) : ℝ)))) ≤
      endpointSchurConstant r * (1 / Real.sqrt (j : ℝ)) := by
  have hjp : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hfac : 0 ≤ 1 / Real.sqrt (j : ℝ) := by positivity
  have hsum := summable_endpointSchurRowTerm r hr j hj
  have hnonneg (k : ℕ) : 0 ≤ endpointSchurRowTerm r j k := by
    unfold endpointSchurRowTerm
    positivity
  calc
    _ ≤ (1 / Real.sqrt (j : ℝ)) *
          (∑ k ∈ Finset.range N, endpointSchurRowTerm r j k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k hk => endpointWeightedKernel_row_pointwise r j k hj)
    _ ≤ (1 / Real.sqrt (j : ℝ)) *
          (∑' k : ℕ, endpointSchurRowTerm r j k) :=
      mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum (Finset.range N) (fun k hk => hnonneg k)) hfac
    _ ≤ (1 / Real.sqrt (j : ℝ)) * endpointSchurConstant r :=
      mul_le_mul_of_nonneg_left (endpointSchurRow_tsum_le r hr hr1 j hj) hfac
    _ = endpointSchurConstant r * (1 / Real.sqrt (j : ℝ)) := by ring

/-- The matching pointwise column weight uses `j=t+1`. -/
theorem endpointWeightedKernel_column_pointwise (r : ℝ) (k t : ℕ) :
    endpointWeightedKernel r (t + 1) k *
        (1 / Real.sqrt (((t + 1 : ℕ) : ℝ))) ≤
      (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
        endpointSchurColumnTerm r k t := by
  have hn : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hj : (0 : ℝ) < (((t + 1 : ℕ) : ℝ)) := by positivity
  have hsn := Real.sqrt_pos.2 hn
  have hsj := Real.sqrt_pos.2 hj
  have hd : (0 : ℝ) < (((t + 1 + k : ℕ) : ℝ)) := by positivity
  have hM := endpointWeightedKernel_le_row r (t + 1) k (by omega)
  have hmul := mul_le_mul_of_nonneg_right hM (by positivity :
    0 ≤ 1 / Real.sqrt (((t + 1 : ℕ) : ℝ)))
  calc
    _ ≤ (endpointSchurRowTerm r (t + 1) k *
          Real.sqrt (((k + 1 : ℕ) : ℝ)) /
          Real.sqrt (((t + 1 : ℕ) : ℝ))) *
          (1 / Real.sqrt (((t + 1 : ℕ) : ℝ))) := hmul
    _ = (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
          endpointSchurColumnTerm r k t := by
      unfold endpointSchurRowTerm endpointSchurColumnTerm
      rw [Real.rpow_sub_one hj.ne']
      have hpow : (((k + 1 : ℕ) : ℝ) ^ (1 - r)) =
          (((k + 1 : ℕ) : ℝ) ^ (-r)) * (((k + 1 : ℕ) : ℝ)) := by
        calc
          _ = (((k + 1 : ℕ) : ℝ) ^ (-r + 1)) := by congr 1; ring
          _ = (((k + 1 : ℕ) : ℝ) ^ (-r)) *
                (((k + 1 : ℕ) : ℝ) ^ (1 : ℝ)) := Real.rpow_add hn _ _
          _ = _ := by simp
      rw [hpow]
      field_simp
      nlinarith [Real.sq_sqrt hn.le, Real.sq_sqrt hj.le]

/-- The finite column Schur inequality, with arbitrary cutoff including zero. -/
theorem endpointWeightedKernel_column_sum_le (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (k N : ℕ) :
    (∑ t ∈ Finset.range N,
      endpointWeightedKernel r (t + 1) k *
        (1 / Real.sqrt (((t + 1 : ℕ) : ℝ)))) ≤
      endpointSchurConstant r *
        (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) := by
  have hn : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hfac : 0 ≤ 1 / Real.sqrt (((k + 1 : ℕ) : ℝ)) := by positivity
  have hsum := summable_endpointSchurColumnTerm r hr1 k
  have hnonneg (t : ℕ) : 0 ≤ endpointSchurColumnTerm r k t := by
    unfold endpointSchurColumnTerm
    positivity
  calc
    _ ≤ (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
          (∑ t ∈ Finset.range N, endpointSchurColumnTerm r k t) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun t ht => endpointWeightedKernel_column_pointwise r k t)
    _ ≤ (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
          (∑' t : ℕ, endpointSchurColumnTerm r k t) :=
      mul_le_mul_of_nonneg_left
        (hsum.sum_le_tsum (Finset.range N) (fun t ht => hnonneg t)) hfac
    _ ≤ (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) * endpointSchurConstant r :=
      mul_le_mul_of_nonneg_left (endpointSchurColumn_tsum_le r hr hr1 k) hfac
    _ = endpointSchurConstant r *
          (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) := by ring

#assert_trust kernel endpointKernelAbs_le_sqrt
#assert_trust kernel endpointWeightedKernel_row_sum_le
#assert_trust kernel endpointWeightedKernel_column_sum_le
#print axioms endpointWeightedKernel_row_sum_le
#print axioms endpointWeightedKernel_column_sum_le

end NLA.Proofs.SP14
