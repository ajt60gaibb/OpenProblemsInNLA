/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The imported literal Gram
identity and spectral-sign trace-norm witness retain their prior credits.

Exact frozen C20, the unchanged coefficient-one original target. The sign
witness includes a zero commutator and kernel eigenvalues. No division by
the trace norm is used. This author runs no Lean or Comparator.
-/
import NLA.MI27.LogarithmicCommutatorDual
import NLA.MI27.SkewRotation
import NLA.MI27.TraceNormWitness
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

theorem logarithmic_commutator_bound (n : ℕ) (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (htrace : Matrix.trace (A + B) = 1) :
    traceNorm (B * logM (A + B) - logM (A + B) * B) ≤
      -(trR A) * Real.log (trR A) - (trR B) * Real.log (trR B) := by
  let K : Mat n := (-Complex.I) • comm B (logM (A + B))
  obtain ⟨hK, _, hnorm⟩ :=
    skew_commutator_trace_norm hn (A + B) B (hA.add hB) hB.isHermitian
  change K.IsHermitian at hK
  change traceNorm (comm B (logM (A + B))) = traceNorm K at hnorm
  obtain ⟨H, hH, hHnorm, hvalue⟩ := hermitian_trace_norm_witness hn K hK
  obtain ⟨hh, hdual⟩ := logarithmic_commutator_dual_bound hn A B H hA hB htrace hH
  change |trR (H * K)| ≤ opNorm H * h (trR A) (trR B) at hdual
  change traceNorm (comm B (logM (A + B))) ≤ h (trR A) (trR B)
  calc
    traceNorm (comm B (logM (A + B))) = traceNorm K := hnorm
    _ = trR (H * K) := hvalue.symm
    _ ≤ |trR (H * K)| := le_abs_self _
    _ ≤ opNorm H * h (trR A) (trR B) := hdual
    _ ≤ 1 * h (trR A) (trR B) := mul_le_mul_of_nonneg_right hHnorm hh
    _ = h (trR A) (trR B) := one_mul _

#print axioms logarithmic_commutator_bound
#assert_trust kernel logarithmic_commutator_bound

end NLA.MI27
