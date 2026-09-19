import NLA.PF03.Definitions
import Mathlib.Analysis.SpecificLimits.Basic
import LeanCert.Tactic

/-!
C23: the boundary is the frontier in the symmetric-matrix subtype. A path
decreasing one zero diagonal entry remains symmetric and leaves the CP set.
This avoids a closedness theorem for the completely positive cone.

Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. Author: /root.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix Topology
open Filter
noncomputable section
namespace NLA.PF03

lemma cp_diagonal_nonneg {n : ℕ} (A : SymMatrix ℝ n)
    (hA : CompletelyPositive A) (j : Fin n) : 0 ≤ A.val j j := by
  obtain ⟨m, _hm, B, _hB, hAB⟩ := hA
  rw [hAB, Matrix.mul_apply]
  exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (B j k))

theorem cp_zero_diagonal_frontier {n : ℕ} (hn : 0 < n) (A : SymMatrix ℝ n)
    (hA : CompletelyPositive A) (j : Fin n) (hdiag : A.val j j = 0) :
    A ∈ frontier (CPSet n) := by
  let f : ℝ → SymMatrix ℝ n := fun t =>
    ⟨A.val - Matrix.diagonal (Pi.single j t),
      A.property.sub (Matrix.isSymm_diagonal _)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    change Continuous (fun t : ℝ => A.val - Matrix.diagonal (Pi.single j t))
    apply continuous_matrix
    intro r s
    simp only [Matrix.sub_apply, Matrix.diagonal_apply, Pi.single_apply]
    split_ifs <;> fun_prop
  have hzero : f 0 = A := by
    apply Subtype.ext
    simp [f]
  have hbad (k : ℕ) : f (1 / ((k : ℝ) + 1)) ∉ CPSet n := by
    intro hk
    have hnonneg := cp_diagonal_nonneg _ hk j
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have hval : (f (1 / ((k : ℝ) + 1))).val j j = -(1 / ((k : ℝ) + 1)) := by
      simp [f, hdiag]
    rw [hval] at hnonneg
    linarith
  have hseq : Tendsto (fun k : ℕ => f (1 / ((k : ℝ) + 1))) atTop (𝓝 A) := by
    simpa only [hzero, Function.comp_def] using (hf.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0))
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hA, mem_closure_of_tendsto hseq (Eventually.of_forall hbad)⟩

#print axioms cp_zero_diagonal_frontier
#assert_trust kernel cp_zero_diagonal_frontier

end NLA.PF03
