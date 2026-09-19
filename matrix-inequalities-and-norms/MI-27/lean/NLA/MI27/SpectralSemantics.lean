/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original problem: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. The spectral decomposition and cyclic
trace argument follow George Stepaniants's accepted MI24 TraceSpectral module,
developed with Codex agent /root/nm04_final_referee1 and itself credited to the
accepted MI22 FunctionalCalculus bridge. All seven MI24 source files are retained
unchanged. The underlying finite Hermitian calculus is Mathlib's.
-/
import NLA.MI27.Definitions

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- Hermitian matrices have the actual complex trace represented by `trR`. -/
lemma trace_eq_ofReal_trR {n : ℕ} (M : Mat n) (hM : M.IsHermitian) :
    Matrix.trace M = (trR M : ℂ) := by
  have htrace := Matrix.trace_conjTranspose M
  rw [hM.eq] at htrace
  exact (Complex.conj_eq_iff_re.mp htrace.symm).symm

/-- The totalized real CFC logarithm is Hermitian; the final target uses PD inputs. -/
lemma logM_isHermitian {n : ℕ} (M : Mat n) : (logM M).IsHermitian := by
  simpa only [logM] using (IsSelfAdjoint.log (a := M)).isHermitian

/-- C02. The library result applies to every function on the finite spectrum.
The size and continuity hypotheses are retained verbatim from the frozen contract. -/
theorem spectral_function_semantics {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ M)) :
    cfc f M =
        (hM.eigenvectorUnitary : Mat n) *
          Matrix.diagonal (fun i => (f (hM.eigenvalues i) : ℂ)) *
            (hM.eigenvectorUnitary : Mat n)ᴴ ∧
      trR (cfc f M) = ∑ i : Fin n, f (hM.eigenvalues i) ∧
      (logM M).IsHermitian ∧ (Matrix.trace M).im = 0 := by
  have hspec : cfc f M =
      (hM.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => (f (hM.eigenvalues i) : ℂ)) *
          (hM.eigenvectorUnitary : Mat n)ᴴ := by
    rw [hM.cfc_eq]
    rfl
  refine ⟨hspec, ?_, logM_isHermitian M, ?_⟩
  · rw [hspec]
    unfold trR
    rw [Matrix.trace_mul_cycle]
    -- Expose the cyclically permuted trace and identify matrix star with
    -- conjugate transpose so the adjacent unitary factors match the library lemma.
    change (star (hM.eigenvectorUnitary : Mat n) *
      (hM.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => (f (hM.eigenvalues i) : ℂ))).trace.re = _
    rw [Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
    simp only [Complex.re_sum, Complex.ofReal_re]
  · rw [trace_eq_ofReal_trR M hM]
    exact Complex.ofReal_im _

#print axioms spectral_function_semantics

end NLA.MI27
