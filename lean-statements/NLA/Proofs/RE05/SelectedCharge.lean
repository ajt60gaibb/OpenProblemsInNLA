import NLA.Proofs.RE05.LeveragePSD
import NLA.Proofs.RE05.PositiveSVDTrace
import NLA.Proofs.RE05.QueryCount

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
open scoped BigOperators Matrix

/-- Trace identity for the actual chosen exact SVD, not a promised response. -/
theorem exactSVD_posSemidef_trace {n : ℕ} (B : Square n) (hB : B.PosSemidef) :
    B.trace = ∑ j : Fin n, (exactSVD B).sigma (Fin.cast (Nat.min_self n).symm j) :=
  validSVD_posSemidef_trace (svd_total n n B) hB

theorem exactSVD_leverage_sum {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ j : Fin n, (exactSVD (leverage P)).sigma
      (Fin.cast (Nat.min_self n).symm j)) = (q + 1 : ℝ) := by
  rw [← exactSVD_posSemidef_trace _ (leverage_posSemidef P)]
  exact leverage_trace P hP

/-- A finite selected list charges at most the sum of all nonnegative
singular values. The threshold may be any real number. -/
theorem filter_selected_charge {n : ℕ} (sigma : Fin n → ℝ)
    (hsigma : ∀ j, 0 ≤ sigma j) (t : ℝ) :
    (((List.finRange n).filter fun j => t < sigma j).length : ℝ) * t ≤
      ∑ j : Fin n, sigma j := by
  let S : Finset (Fin n) := Finset.univ.filter (fun j => t < sigma j)
  have hlen : S.card = ((List.finRange n).filter fun j => t < sigma j).length := by
    simpa only [S, List.toFinset_finRange, List.countP_eq_length_filter] using
      (List.nodup_finRange n).card_eq_countP (P := fun j => t < sigma j)
  calc
    (((List.finRange n).filter fun j => t < sigma j).length : ℝ) * t =
        (S.card : ℝ) * t := by rw [hlen]
    _ = ∑ j ∈ S, t := by simp
    _ ≤ ∑ j ∈ S, sigma j := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Finset.mem_filter.mp hj).2.le
    _ ≤ ∑ j : Fin n, sigma j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j _ _
      exact hsigma j

/-- Exact charge of the actual selected columns, with no additional
spectral, basis, or positivity promise. -/
theorem selectedCount_charge {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ) :
    (selectedCount P ε : ℝ) * threshold q (squaredAccuracy ε) ≤ (q + 1 : ℕ) := by
  have hsvd := svd_total n n (leverage P)
  have h := filter_selected_charge
    (fun j : Fin n => (exactSVD (leverage P)).sigma (Fin.cast (Nat.min_self n).symm j))
    (fun j => hsvd.2.2.1 _) (threshold q (squaredAccuracy ε))
  rw [exactSVD_leverage_sum P hP] at h
  simpa only [selectedCount, Nat.cast_add, Nat.cast_one] using h

/-- The complete unchanged deterministic source query-count companion. -/
theorem sourceQueryBound {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ε : ℝ) (hε : 0 < ε) : NLA.Statements.RE05.SourceQueryBound P ε :=
  sourceQueryBound_of_selected_charge P ε hε (selectedCount_charge P hP ε)

#assert_trust kernel exactSVD_posSemidef_trace
#assert_trust kernel exactSVD_leverage_sum
#assert_trust kernel filter_selected_charge
#assert_trust kernel selectedCount_charge
#assert_trust kernel sourceQueryBound
#print axioms selectedCount_charge
#print axioms sourceQueryBound
end NLA.Proofs.RE05
