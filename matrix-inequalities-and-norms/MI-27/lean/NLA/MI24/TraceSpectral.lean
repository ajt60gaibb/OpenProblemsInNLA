/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

The spectral decomposition bridge follows George Stepaniants's accepted MI22
FunctionalCalculus.lean, specialized here to MI24's frozen concrete definition
and extended to positive semidefinite matrices, including singular matrices.
The real trace is derived from that decomposition rather than postulated.
-/
import NLA.MI24.SpectralPowers

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

lemma spectralPower_spectral_decomposition {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (r : ℝ) :
    spectralPower A r =
      (hA.isHermitian.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ)) *
          (hA.isHermitian.eigenvectorUnitary : Mat n)ᴴ := by
  have hc : CFC.rpow A r = cfc (fun x : ℝ => x ^ r) A :=
    CFC.rpow_eq_cfc_real hA.nonneg
  rw [spectralPower, hc, hA.isHermitian.cfc_eq]
  rfl

lemma traceReal_spectralPower {n : ℕ} (A : Mat n) (hA : A.PosSemidef) (r : ℝ) :
    traceReal (spectralPower A r) = ∑ i : Fin n, hA.isHermitian.eigenvalues i ^ r := by
  rw [spectralPower_spectral_decomposition A hA r]
  unfold traceReal
  rw [Matrix.trace_mul_cycle]
  -- Expose Matrix.trace after the cyclic permutation and normalize
  -- matrix star/conjugate-transpose notation so the adjacent unitary factors
  -- match Unitary.coe_star_mul_self.
  change (star (hA.isHermitian.eigenvectorUnitary : Mat n) *
    (hA.isHermitian.eigenvectorUnitary : Mat n) *
      Matrix.diagonal (fun i => ((hA.isHermitian.eigenvalues i ^ r : ℝ) : ℂ))).trace.re = _
  rw [Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

lemma traceReal_spectralPower_sorted {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (r : ℝ) :
    traceReal (spectralPower A r) =
      ∑ i : Fin (Fintype.card (Fin n)), hA.isHermitian.eigenvalues₀ i ^ r := by
  rw [traceReal_spectralPower A hA r]
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  symm
  apply Fintype.sum_equiv e
  intro i
  simp only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply]

lemma posSemidef_eigenvalues₀_nonneg {n : ℕ} (A : Mat n) (hA : A.PosSemidef)
    (i : Fin (Fintype.card (Fin n))) : 0 ≤ hA.isHermitian.eigenvalues₀ i := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  simpa only [Matrix.IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
    hA.eigenvalues_nonneg (e i)

lemma traceReal_spectralPower_nonneg {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (r : ℝ) : 0 ≤ traceReal (spectralPower A r) := by
  rw [traceReal_spectralPower A hA r]
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hA.eigenvalues_nonneg i) r

end NLA.MI24
