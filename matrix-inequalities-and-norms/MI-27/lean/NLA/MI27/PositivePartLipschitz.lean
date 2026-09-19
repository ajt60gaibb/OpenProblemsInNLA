/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original question: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. The local regularity estimate uses the
attained positive spectral projection, the accepted PSD trace-order route and
the C04 operator bound. Its dimension factor is confined to C07; it is absent
from the frozen gamma-independent unitary estimate and the final MI27 target.
-/
import NLA.MI27.PositivePart

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma effect_trR_le_dim {n : ℕ} (P : Mat n) (hP1 : P ≤ 1) : trR P ≤ (n : ℝ) := by
  have ht := trR_mul_order P (1 : Mat n) (1 : Mat n) hP1 Matrix.PosSemidef.one
  simpa only [mul_one, trR, Matrix.trace_one, Fintype.card_fin, Complex.natCast_re] using ht

/-- Use one attained optimizer to control a one-sided positive-part difference. -/
lemma positive_part_trace_sub_le {n : ℕ} (hn : 1 ≤ n) (M N : Mat n)
    (hM : M.IsHermitian) (hN : N.IsHermitian) :
    tracePos M - tracePos N ≤ (n : ℝ) * opNorm (M - N) := by
  obtain ⟨P, hP, hP2, hP0, hP1, hcomm, hvalue⟩ :=
    (positive_part_variational hn M hM).2.1
  have hPN := (positive_part_variational hn N hN).1 P hP0 hP1
  have hdiff : tracePos M - tracePos N ≤ trR (P * (M - N)) := by
    have heval : trR (P * (M - N)) = trR (P * M) - trR (P * N) := by
      simp only [mul_sub, trR, Matrix.trace_sub, Complex.sub_re]
    rw [heval, hvalue]
    exact sub_le_sub_left hPN (tracePos M)
  calc
    tracePos M - tracePos N ≤ |trR (P * (M - N))| := hdiff.trans (le_abs_self _)
    _ ≤ trR P * opNorm (M - N) := positive_trace_operator_bound hn P (M - N)
      (Matrix.nonneg_iff_posSemidef.mp hP0) (hM.sub hN)
    _ ≤ (n : ℝ) * opNorm (M - N) :=
      mul_le_mul_of_nonneg_right (effect_trR_le_dim P hP1) (opNorm_nonneg _)

/-- C07: reversing the optimizer argument yields the absolute difference bound. -/
theorem positive_part_trace_lipschitz {n : ℕ} (hn : 1 ≤ n) (M N : Mat n)
    (hM : M.IsHermitian) (hN : N.IsHermitian) :
    |tracePos M - tracePos N| ≤ (n : ℝ) * opNorm (M - N) := by
  have hu := positive_part_trace_sub_le hn M N hM hN
  have hl := positive_part_trace_sub_le hn N M hN hM
  have hreverse : opNorm (N - M) = opNorm (M - N) := by
    simpa only [opNorm_eq_l2] using norm_sub_rev N M
  rw [hreverse] at hl
  refine abs_le.mpr ⟨?_, hu⟩
  simpa only [neg_sub] using neg_le_neg hl

#print axioms positive_part_trace_lipschitz

end NLA.MI27
