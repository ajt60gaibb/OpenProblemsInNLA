/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original question: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. The trace order and real scalar trace
identities reuse George Stepaniants's accepted MI24 TraceHolder and PowerScaling
proofs, developed with Codex agent /root/nm04_final_referee1. Those modules and
their prior mathematical/code credits remain unchanged. The operator-norm
identification follows the accepted MI24 OperatorNorm bridge to Mathlib.
-/
import NLA.MI27.Definitions

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- The frozen map norm is exactly the scoped Euclidean operator matrix norm. -/
lemma opNorm_eq_l2 {n : ℕ} (X : Mat n) : opNorm X = ‖X‖ :=
  Matrix.l2_opNorm_toEuclideanCLM X

lemma opNorm_nonneg {n : ℕ} (X : Mat n) : 0 ≤ opNorm X := norm_nonneg _

lemma trR_nonneg {n : ℕ} (X : Mat n) (hX : X.PosSemidef) : 0 ≤ trR X :=
  (Complex.nonneg_iff.mp hX.trace_nonneg).1

lemma trR_mul_comm {n : ℕ} (X Y : Mat n) : trR (X * Y) = trR (Y * X) := by
  unfold trR
  rw [Matrix.trace_mul_comm]

lemma trR_neg {n : ℕ} (X : Mat n) : trR (-X) = -trR X := by
  simp only [trR, Matrix.trace_neg, Complex.neg_re]

/-- Transport the already proved PSD trace order across the two real-trace names. -/
lemma trR_mul_order {n : ℕ} (A B D : Mat n) (hAB : A ≤ B) (hD : D.PosSemidef) :
    trR (A * D) ≤ trR (B * D) := by
  simpa only [trR, NLA.MI24.traceReal] using
    NLA.MI24.traceReal_mul_order A B D hAB hD

/-- A real scalar identity matrix acts by the ordinary real scalar on the trace. -/
lemma trR_algebraMap_mul {n : ℕ} (c : ℝ) (X : Mat n) :
    trR (algebraMap ℝ (Mat n) c * X) = c * trR X := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  simpa only [trR, NLA.MI24.traceReal] using NLA.MI24.traceReal_smul_real X c

/-- C04. The C-star sandwich and actual PSD trace order give the bound.
The proof also works in zero dimension; the frozen size hypothesis is retained. -/
theorem positive_trace_operator_bound {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosSemidef) (hY : Y.IsHermitian) :
    |trR (X * Y)| ≤ trR X * opNorm Y := by
  have hu := trR_mul_order Y (algebraMap ℝ (Mat n) ‖Y‖) X
    hY.isSelfAdjoint.le_algebraMap_norm_self hX
  have hl := trR_mul_order (-(algebraMap ℝ (Mat n) ‖Y‖)) Y X
    hY.isSelfAdjoint.neg_algebraMap_norm_le_self hX
  rw [trR_algebraMap_mul] at hu
  rw [neg_mul, trR_neg, trR_algebraMap_mul] at hl
  calc
    |trR (X * Y)| = |trR (Y * X)| := congrArg abs (trR_mul_comm X Y)
    _ ≤ ‖Y‖ * trR X := abs_le.mpr ⟨hl, hu⟩
    _ = trR X * opNorm Y := by rw [opNorm_eq_l2, mul_comm]

#print axioms positive_trace_operator_bound

end NLA.MI27
