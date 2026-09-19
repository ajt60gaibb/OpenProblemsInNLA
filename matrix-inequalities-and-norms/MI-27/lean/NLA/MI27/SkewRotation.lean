/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original problem: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. The rotation by -i is handled by its exact
Gram matrix, so the frozen square-root trace norm needs no norm-duality axiom.
-/
import NLA.MI27.SpectralSemantics

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- The commutator of two Hermitian matrices is skew Hermitian. -/
lemma comm_conjTranspose {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (comm X Y)ᴴ = -(comm X Y) := by
  simp only [comm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    hX.eq, hY.eq, neg_sub]

/-- Multiplication by -i preserves the literal Gram matrix, for any matrix. -/
lemma neg_I_smul_gram {n : ℕ} (X : Mat n) :
    ((-Complex.I) • X)ᴴ * ((-Complex.I) • X) = Xᴴ * X := by
  have hc : star (-Complex.I) * (-Complex.I) = (1 : ℂ) := by
    simp only [Complex.star_def, Complex.conj_neg_I, mul_neg, Complex.I_mul_I, neg_neg]
  calc
    ((-Complex.I) • X)ᴴ * ((-Complex.I) • X) =
        (star (-Complex.I) * (-Complex.I)) • (Xᴴ * X) := by
      rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = Xᴴ * X := by rw [hc, one_smul]

/-- C17. The Hermitian logarithm suffices for this algebraic identity; the
positive-definite and dimension hypotheses remain exactly as frozen. -/
theorem skew_commutator_trace_norm {n : ℕ} (hn : 1 ≤ n) (T B : Mat n)
    (hT : T.PosDef) (hB : B.IsHermitian) :
    let K := (-Complex.I) • comm B (logM T)
    K.IsHermitian ∧
      Kᴴ * K = (comm B (logM T))ᴴ * comm B (logM T) ∧
      traceNorm (comm B (logM T)) = traceNorm K := by
  dsimp only
  have hcomm := comm_conjTranspose B (logM T) hB (logM_isHermitian T)
  have hK : ((-Complex.I) • comm B (logM T)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hcomm]
    simp only [Complex.star_def, Complex.conj_neg_I, smul_neg, neg_smul]
  refine ⟨hK, neg_I_smul_gram _, ?_⟩
  unfold traceNorm
  rw [neg_I_smul_gram]

#print axioms skew_commutator_trace_norm

end NLA.MI27
