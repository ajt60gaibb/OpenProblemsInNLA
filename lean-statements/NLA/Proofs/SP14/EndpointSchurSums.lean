import NLA.Proofs.SP14.EndpointWeightedSchur
import Mathlib.Analysis.PSeries

/-!
The exact scalar row and column sums associated with the endpoint-extension
kernel. The finite Schur inequalities remain in a subsequent module.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The literal constant in the canonical two-sided weighted Schur estimate. -/
noncomputable def endpointSchurConstant (r : ℝ) : ℝ :=
  1 + 1 / r + 1 / (1 - r)

/-- Row summand, with row index `j ≥ 1` and column index `k ≥ 0`. -/
noncomputable def endpointSchurRowTerm (r : ℝ) (j k : ℕ) : ℝ :=
  (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) / ((j + k : ℕ) : ℝ)

/-- Column summand, indexed by `t ≥ 0` so that the source's `j=t+1`. -/
noncomputable def endpointSchurColumnTerm (r : ℝ) (k t : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
    (((t + 1 : ℕ) : ℝ) ^ (r - 1)) / (((t + 1 + k : ℕ) : ℝ))

private theorem endpointSchurRowTerm_nonneg (r : ℝ) (j k : ℕ) :
    0 ≤ endpointSchurRowTerm r j k := by
  unfold endpointSchurRowTerm
  positivity

private theorem endpointSchurColumnTerm_nonneg (r : ℝ) (k t : ℕ) :
    0 ≤ endpointSchurColumnTerm r k t := by
  unfold endpointSchurColumnTerm
  positivity

/-- The part of a row before the split at `k=j`. -/
theorem endpointSchurRowTerm_le_prefix (r : ℝ) (j k : ℕ) (hj : 1 ≤ j) :
    endpointSchurRowTerm r j k ≤
      (j : ℝ) ^ (r - 1) * (((k + 1 : ℕ) : ℝ) ^ (-r)) := by
  have hjp : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hden : (j : ℝ) ≤ ((j + k : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ j + k)
  have hnum : 0 ≤ (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) := by positivity
  calc
    endpointSchurRowTerm r j k =
        (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) / ((j + k : ℕ) : ℝ) := rfl
    _ ≤ (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) / (j : ℝ) :=
      div_le_div_of_nonneg_left hnum hjp hden
    _ = (j : ℝ) ^ (r - 1) * (((k + 1 : ℕ) : ℝ) ^ (-r)) := by
      rw [Real.rpow_sub_one hjp.ne']
      ring_nf

/-- The row summand has a summable power-tail majorant at every index. -/
theorem endpointSchurRowTerm_le_power (r : ℝ) (j k : ℕ) (hj : 1 ≤ j) :
    endpointSchurRowTerm r j k ≤
      (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r - 1)) := by
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hden : (((k + 1 : ℕ) : ℝ)) ≤ (((j + k : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : k + 1 ≤ j + k)
  have hnum : 0 ≤ (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) := by positivity
  calc
    endpointSchurRowTerm r j k =
        (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) / ((j + k : ℕ) : ℝ) := rfl
    _ ≤ (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r)) / ((k + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hnum hk hden
    _ = (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r - 1)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc]
      rw [← Real.rpow_add hk]
      ring_nf

/-- The column summand has a summable power-tail majorant at every index. -/
theorem endpointSchurColumnTerm_le_power (r : ℝ) (k t : ℕ) :
    endpointSchurColumnTerm r k t ≤
      (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
        (((t + 1 : ℕ) : ℝ) ^ (r - 2)) := by
  have ht : (0 : ℝ) < (((t + 1 : ℕ) : ℝ)) := by positivity
  have hden : (((t + 1 : ℕ) : ℝ)) ≤ (((t + 1 + k : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : t + 1 ≤ t + 1 + k)
  have hnum : 0 ≤ (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
      (((t + 1 : ℕ) : ℝ) ^ (r - 1)) := by positivity
  calc
    endpointSchurColumnTerm r k t =
        (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
          (((t + 1 : ℕ) : ℝ) ^ (r - 1)) / (((t + 1 + k : ℕ) : ℝ)) := rfl
    _ ≤ (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
          (((t + 1 : ℕ) : ℝ) ^ (r - 1)) / (((t + 1 : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left hnum ht hden
    _ = (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
          (((t + 1 : ℕ) : ℝ) ^ (r - 2)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc]
      rw [← Real.rpow_add ht]
      ring_nf

/-- The part of a column before the split at `j=k+1`. -/
theorem endpointSchurColumnTerm_le_prefix (r : ℝ) (k t : ℕ) :
    endpointSchurColumnTerm r k t ≤
      (((k + 1 : ℕ) : ℝ) ^ (-r)) *
        (((t + 1 : ℕ) : ℝ) ^ (r - 1)) := by
  have hk : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hden : (((k + 1 : ℕ) : ℝ)) ≤ (((t + 1 + k : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : k + 1 ≤ t + 1 + k)
  have hnum : 0 ≤ (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
      (((t + 1 : ℕ) : ℝ) ^ (r - 1)) := by positivity
  calc
    endpointSchurColumnTerm r k t =
        (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
          (((t + 1 : ℕ) : ℝ) ^ (r - 1)) / (((t + 1 + k : ℕ) : ℝ)) := rfl
    _ ≤ (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
          (((t + 1 : ℕ) : ℝ) ^ (r - 1)) / (((k + 1 : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left hnum hk hden
    _ = (((k + 1 : ℕ) : ℝ) ^ (-r)) *
          (((t + 1 : ℕ) : ℝ) ^ (r - 1)) := by
      have hexp : 1 - r - 1 = -r := by ring
      rw [← hexp, Real.rpow_sub_one hk.ne']
      ring_nf

theorem summable_endpointSchurRowTerm (r : ℝ) (hr : 0 < r)
    (j : ℕ) (hj : 1 ≤ j) :
    Summable (endpointSchurRowTerm r j) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-r - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-r - 1))) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).2 hbase
  have hmajor : Summable
      (fun k : ℕ => (j : ℝ) ^ r * (((k + 1 : ℕ) : ℝ) ^ (-r - 1))) :=
    hshift.mul_left _
  exact Summable.of_nonneg_of_le
    (fun k => endpointSchurRowTerm_nonneg r j k)
    (fun k => endpointSchurRowTerm_le_power r j k hj) hmajor

theorem summable_endpointSchurColumnTerm (r : ℝ) (hr1 : r < 1) (k : ℕ) :
    Summable (endpointSchurColumnTerm r k) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (r - 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun t : ℕ => (((t + 1 : ℕ) : ℝ) ^ (r - 2))) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff 1).2 hbase
  have hmajor : Summable
      (fun t : ℕ => (((k + 1 : ℕ) : ℝ) ^ (1 - r)) *
        (((t + 1 : ℕ) : ℝ) ^ (r - 2))) :=
    hshift.mul_left _
  exact Summable.of_nonneg_of_le
    (fun t => endpointSchurColumnTerm_nonneg r k t)
    (fun t => endpointSchurColumnTerm_le_power r k t) hmajor

#assert_trust kernel endpointSchurRowTerm_le_prefix
#assert_trust kernel endpointSchurRowTerm_le_power
#assert_trust kernel endpointSchurColumnTerm_le_prefix
#assert_trust kernel endpointSchurColumnTerm_le_power
#assert_trust kernel summable_endpointSchurRowTerm
#assert_trust kernel summable_endpointSchurColumnTerm
#print axioms summable_endpointSchurRowTerm
#print axioms summable_endpointSchurColumnTerm

end NLA.Proofs.SP14
