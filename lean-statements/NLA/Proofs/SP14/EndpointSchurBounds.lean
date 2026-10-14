import NLA.Proofs.SP14.EndpointSchurSums

/-!
The two exact scalar Schur sums for the endpoint-extension kernel. Finite
kernel-weighted Schur inequalities remain a separate gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The source's row sum is bounded for every `j ≥ 1`, including `j = 1`. -/
theorem endpointSchurRow_tsum_le (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (j : ℕ) (hj : 1 ≤ j) :
    (∑' k : ℕ, endpointSchurRowTerm r j k) ≤ endpointSchurConstant r := by
  have hjp : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hsum := summable_endpointSchurRowTerm r hr j hj
  have hshift : Summable (fun t : ℕ => endpointSchurRowTerm r j (t + j)) :=
    (summable_nat_add_iff j).2 hsum
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-r - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htailSummable : Summable
      (fun t : ℕ => (((t + j + 1 : ℕ) : ℝ) ^ (-r - 1))) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff (j + 1)).2 hbase
  have hmajor : Summable (fun t : ℕ =>
      (j : ℝ) ^ r * (((t + j + 1 : ℕ) : ℝ) ^ (-r - 1))) :=
    htailSummable.mul_left _
  have hpre :
      (∑ k ∈ Finset.range j, endpointSchurRowTerm r j k) ≤
        (j : ℝ) ^ (r - 1) *
          (∑ k ∈ Finset.range j, (((k + 1 : ℕ) : ℝ) ^ (-r))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => endpointSchurRowTerm_le_prefix r j k hj)
  have htail :
      (∑' t : ℕ, endpointSchurRowTerm r j (t + j)) ≤
        (j : ℝ) ^ r *
          (∑' t : ℕ, (((t + j + 1 : ℕ) : ℝ) ^ (-r - 1))) := by
    rw [← tsum_mul_left]
    exact hshift.tsum_le_tsum (fun t => endpointSchurRowTerm_le_power r j (t + j) hj)
      hmajor
  have hprePower := endpointSchurPowerPrefix r hr hr1 j hj
  have htailPower := endpointSchurPowerTail r hr j hj
  have hsmall : (j : ℝ) ^ (r - 1) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos (x := (1 : ℝ))
      (y := (j : ℝ)) (z := r - 1) zero_lt_one (by exact_mod_cast hj) (by linarith)
  have hcancelPre : (j : ℝ) ^ (r - 1) * (j : ℝ) ^ (1 - r) = 1 := by
    rw [← Real.rpow_add hjp]
    simp
  have hcancelTail : (j : ℝ) ^ r * (j : ℝ) ^ (-r) = 1 := by
    rw [← Real.rpow_add hjp]
    simp
  have hden1 : 0 ≤ (j : ℝ) ^ (r - 1) := Real.rpow_nonneg hjp.le _
  have hden2 : 0 ≤ (j : ℝ) ^ r := Real.rpow_nonneg hjp.le _
  calc
    (∑' k : ℕ, endpointSchurRowTerm r j k) =
        (∑ k ∈ Finset.range j, endpointSchurRowTerm r j k) +
          (∑' t : ℕ, endpointSchurRowTerm r j (t + j)) :=
      (hsum.sum_add_tsum_nat_add j).symm
    _ ≤ (j : ℝ) ^ (r - 1) *
          (∑ k ∈ Finset.range j, (((k + 1 : ℕ) : ℝ) ^ (-r))) +
        (j : ℝ) ^ r *
          (∑' t : ℕ, (((t + j + 1 : ℕ) : ℝ) ^ (-r - 1))) :=
      add_le_add hpre htail
    _ ≤ (j : ℝ) ^ (r - 1) *
          (1 + (j : ℝ) ^ (1 - r) / (1 - r)) +
        (j : ℝ) ^ r * ((j : ℝ) ^ (-r) / r) :=
      add_le_add (mul_le_mul_of_nonneg_left hprePower hden1)
        (mul_le_mul_of_nonneg_left htailPower hden2)
    _ ≤ endpointSchurConstant r := by
      rw [endpointSchurConstant]
      calc
        _ = (j : ℝ) ^ (r - 1) +
            ((j : ℝ) ^ (r - 1) * (j : ℝ) ^ (1 - r)) / (1 - r) +
            ((j : ℝ) ^ r * (j : ℝ) ^ (-r)) / r := by ring
        _ = (j : ℝ) ^ (r - 1) + 1 / (1 - r) + 1 / r := by
          rw [hcancelPre, hcancelTail]
        _ ≤ 1 + 1 / r + 1 / (1 - r) := by linarith

#assert_trust kernel endpointSchurRow_tsum_le
#print axioms endpointSchurRow_tsum_le

/-- The column sum is the row sum at the dual exponent `1-r`. -/
theorem endpointSchurColumn_tsum_le (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (k : ℕ) :
    (∑' t : ℕ, endpointSchurColumnTerm r k t) ≤ endpointSchurConstant r := by
  have hdual : 0 < 1 - r := by linarith
  have hdual1 : 1 - r < 1 := by linarith
  have hrow := endpointSchurRow_tsum_le (1 - r) hdual hdual1 (k + 1) (by omega)
  have hterm (t : ℕ) :
      endpointSchurColumnTerm r k t =
        endpointSchurRowTerm (1 - r) (k + 1) t := by
    unfold endpointSchurColumnTerm endpointSchurRowTerm
    have hexp : -(1 - r) = r - 1 := by ring
    rw [hexp]
    simp [Nat.add_comm, Nat.add_left_comm]
  have hconst : endpointSchurConstant (1 - r) = endpointSchurConstant r := by
    unfold endpointSchurConstant
    have : 1 - (1 - r) = r := by ring
    rw [this]
    ring
  simpa only [hterm, hconst] using hrow

#assert_trust kernel endpointSchurColumn_tsum_le
#print axioms endpointSchurColumn_tsum_le

end NLA.Proofs.SP14
