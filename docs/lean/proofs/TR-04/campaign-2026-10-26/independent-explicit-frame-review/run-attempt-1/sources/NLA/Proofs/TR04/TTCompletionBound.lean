import NLA.Proofs.TR04.TTCompletion

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Matrix

namespace NLA.Proofs.TR04.TensorFormat
open NLA.Computation.SVDMachine

/-- The ordinary tensor-train SVD comparator estimate holds for every actual
recursive legal response, with no condition on tied or zero singular bases. -/
theorem completion_comparator_bound {ns : List ℕ} {r : ℕ → ℕ} {A X : Tensor ns}
    (h : Completion ns r A X) (Y : Tensor ns) (hY : RankFeasible ns r Y) :
    error ns A X ≤ ((ns.length - 1 : ℕ) : ℝ) * error ns A Y := by
  induction h with
  | nil r A => simp [error, energy]
  | single m r A => simp [error, energy]
  | @step m n ns r A U sigma V hSVD Z hchild ih =>
    let k := stepRank m (n :: ns) r
    let Q := stepFrame (n :: ns) r U
    have hQ : SVD.OrthonormalColumns Q := prefixFrame_orthonormal hSVD (r 0)
    have hY' := rankFeasible_merge_contract r Q hY
    have hrec := ih (stepInput r U Y) hY'
    have hfirst : Matrix.rank (firstMatrix Y) ≤ r 0 := by
      rw [← rank_unfold_one]
      exact hY 1 (by omega) (by simp)
    have hbest := error_prefix_projection_le hSVD (r 0) Y hfirst
    change error (m :: n :: ns) A (lift Q (contract Q A)) ≤ error (m :: n :: ns) A Y at hbest
    have hcontract := error_contract_le hQ A Y
    have hpyth := error_lift_decomposition hQ A ((merge k n ns).symm Z)
    have hmerge : error (k :: n :: ns) (contract Q A) ((merge k n ns).symm Z) =
        error ((k * n) :: ns) (stepInput r U A) Z := by
      rw [← error_merge k n ns (contract Q A) ((merge k n ns).symm Z),
        LinearEquiv.apply_symm_apply]
      rfl
    have hcomp : error ((k * n) :: ns) (stepInput r U A) (stepInput r U Y) =
        error (k :: n :: ns) (contract Q A) (contract Q Y) :=
      error_merge k n ns (contract Q A) (contract Q Y)
    rw [hcomp] at hrec
    simp only [List.length_cons, Nat.add_sub_cancel] at hrec ⊢
    change error (m :: n :: ns) A (lift Q ((merge k n ns).symm Z)) ≤ _
    rw [hpyth, hmerge]
    have hcoef : (0 : ℝ) ≤ (ns.length : ℝ) := Nat.cast_nonneg _
    have hrec' : error ((k * n) :: ns) (stepInput r U A) Z ≤
        (ns.length : ℝ) * error (m :: n :: ns) A Y :=
      hrec.trans (mul_le_mul_of_nonneg_left hcontract hcoef)
    push_cast
    linarith

/-- The stronger completion estimate after any arbitrary orthonormal first
projection retains the full projected comparator, as required by TR-04. -/
theorem projected_completion_bound {m k n : ℕ} {ns : List ℕ} {r : ℕ → ℕ}
    {U : Matrix (Fin m) (Fin k) ℝ} (hU : SVD.OrthonormalColumns U)
    (A Y : Tensor (m :: n :: ns)) (hY : RankFeasible (m :: n :: ns) r Y)
    {Z : Tensor ((k * n) :: ns)}
    (hZ : Completion ((k * n) :: ns) (fun j => r (j + 1))
      (merge k n ns (contract U A)) Z) :
    error (m :: n :: ns) A (lift U ((merge k n ns).symm Z)) ≤
      error (m :: n :: ns) A (lift U (contract U A)) +
        (ns.length : ℝ) * energy (m :: n :: ns) (lift U (contract U (A - Y))) := by
  have hY' := rankFeasible_merge_contract r U hY
  have hrec := completion_comparator_bound hZ (merge k n ns (contract U Y)) hY'
  simp only [List.length_cons, Nat.add_sub_cancel] at hrec
  rw [error_merge k n ns (contract U A) (contract U Y)] at hrec
  rw [projected_error_eq hU]
  rw [error_lift_decomposition hU]
  have hmerge := error_merge k n ns (contract U A) ((merge k n ns).symm Z)
  rw [LinearEquiv.apply_symm_apply] at hmerge
  rw [hmerge] at hrec
  exact add_le_add le_rfl hrec

#assert_trust kernel completion_comparator_bound
#assert_trust kernel projected_completion_bound
#print axioms completion_comparator_bound
#print axioms projected_completion_bound
end NLA.Proofs.TR04.TensorFormat
