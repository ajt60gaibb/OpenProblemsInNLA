/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/recover_published_coverage.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Identity-shift method: Péter E. Frenkel,
Lemma 5 of arXiv:2208.12194v4. Actual overlap code retains MI24/MI22 credits.

UNCOMPILED partial C11 development. Ordinary relative entropy along identity
shifts is expanded in two distinct fixed eigenbases. Only scalar logarithms
in those fixed bases are differentiated. This is not a proof of the general
hockey-stick identity and introduces no assumption of that identity.
-/
import NLA.MI27.TraceTangent
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- An ordinary shift by a real scalar times the identity matrix. -/
def c11_identityShift {n : ℕ} (X : Mat n) (r : ℝ) : Mat n := X + (r : ℂ) • 1

lemma c11_cfc_identityShift {n : ℕ} (X : Mat n) (hX : X.IsHermitian) (r : ℝ) :
    cfc (fun x : ℝ => x + r) X = c11_identityShift X r := by
  have halg : algebraMap ℝ (Mat n) r = (r : ℂ) • (1 : Mat n) := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) r (1 : Mat n)
  simpa only [c11_identityShift, cfc_id ℝ X hX.isSelfAdjoint, id_eq, halg] using
    cfc_add_const r (id : ℝ → ℝ) X (X.finite_real_spectrum.continuousOn _) hX.isSelfAdjoint

/-- This is finite-spectrum composition, valid even at repeated or zero shifted eigenvalues. -/
lemma c11_log_identityShift {n : ℕ} (X : Mat n) (hX : X.IsHermitian) (r : ℝ) :
    logM (c11_identityShift X r) = cfc (fun x : ℝ => Real.log (x + r)) X := by
  have hc := cfc_comp' Real.log (fun x : ℝ => x + r) X
    ((X.finite_real_spectrum.image (fun x : ℝ => x + r)).continuousOn _)
    (X.finite_real_spectrum.continuousOn _) hX.isSelfAdjoint
  rw [c11_cfc_identityShift X hX r] at hc
  simpa only [logM, CFC.log] using hc.symm

/-- Actual ordinary relative entropy in two fixed individual eigenbases.
No pointwise positive-part formula or simultaneous diagonalization is asserted. -/
lemma c11_relative_entropy_shift_spectral {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (r : ℝ) :
    relEntropy (c11_identityShift X r) (c11_identityShift Y r) =
      ∑ i : Fin n, ∑ j : Fin n,
        (hX.eigenvalues i + r) *
          (Real.log (hX.eigenvalues i + r) - Real.log (hY.eigenvalues j + r)) *
            NLA.MI24.unitaryOverlapWeight
              (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j := by
  have hself := c16_trR_cfc_product_same hn X hX
    (fun x : ℝ => x + r) (fun x : ℝ => Real.log (x + r))
  have hcross := c16_trR_cfc_product hn X Y hX hY
    (fun x : ℝ => x + r) (fun x : ℝ => Real.log (x + r))
  have hrow :
      (∑ i : Fin n, ∑ j : Fin n,
        (hX.eigenvalues i + r) * Real.log (hX.eigenvalues i + r) *
          NLA.MI24.unitaryOverlapWeight
            (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j) =
      ∑ i : Fin n, (hX.eigenvalues i + r) * Real.log (hX.eigenvalues i + r) := by
    simp_rw [← Finset.mul_sum, NLA.MI24.unitaryOverlapWeight_row, mul_one]
  calc
    relEntropy (c11_identityShift X r) (c11_identityShift Y r) =
        trR (cfc (fun x : ℝ => x + r) X * cfc (fun x : ℝ => Real.log (x + r)) X) -
          trR (cfc (fun x : ℝ => x + r) X * cfc (fun x : ℝ => Real.log (x + r)) Y) := by
      rw [relEntropy, c11_log_identityShift X hX r, c11_log_identityShift Y hY r,
        ← c11_cfc_identityShift X hX r]
      simp only [mul_sub, trR, Matrix.trace_sub, Complex.sub_re]
    _ = (∑ i : Fin n, (hX.eigenvalues i + r) * Real.log (hX.eigenvalues i + r)) -
        ∑ i : Fin n, ∑ j : Fin n,
          (hX.eigenvalues i + r) * Real.log (hY.eigenvalues j + r) *
            NLA.MI24.unitaryOverlapWeight
              (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j := by
      rw [hself, hcross]
    _ = _ := by
      rw [← hrow]
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma c11_hasDerivAt_scalar_shift (x y r : ℝ) (hx : 0 < x + r) (hy : 0 < y + r) :
    HasDerivAt (fun u : ℝ => (x + u) * (Real.log (x + u) - Real.log (y + u)))
      (Real.log (x + r) - Real.log (y + r) + (y - x) / (y + r)) r := by
  have hdx : HasDerivAt (fun u : ℝ => x + u) 1 r := (hasDerivAt_id r).const_add x
  have hdy : HasDerivAt (fun u : ℝ => y + u) 1 r := (hasDerivAt_id r).const_add y
  have hd := hdx.mul ((hdx.log hx.ne').sub (hdy.log hy.ne'))
  have he : 1 * (Real.log (x + r) - Real.log (y + r)) +
        (x + r) * (1 / (x + r) - 1 / (y + r)) =
      Real.log (x + r) - Real.log (y + r) + (y - x) / (y + r) := by
    field_simp [hx.ne', hy.ne']
    <;> ring
  exact hd.congr_deriv he

/-- The noncommuting identity-shift derivative uses only the two fixed scalar spectra.
Strict positivity excludes singular logarithm arguments, but eigenvalue repetitions remain. -/
lemma c11_hasDerivAt_relative_entropy_shift_spectral {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    HasDerivAt (fun u : ℝ => relEntropy (c11_identityShift X u) (c11_identityShift Y u))
      (∑ i : Fin n, ∑ j : Fin n,
        (Real.log (hX.isHermitian.eigenvalues i + r) -
          Real.log (hY.isHermitian.eigenvalues j + r) +
            (hY.isHermitian.eigenvalues j - hX.isHermitian.eigenvalues i) /
              (hY.isHermitian.eigenvalues j + r)) *
                NLA.MI24.unitaryOverlapWeight
                  (star hX.isHermitian.eigenvectorUnitary * hY.isHermitian.eigenvectorUnitary)
                  i j) r := by
  have heq : (fun u : ℝ => relEntropy (c11_identityShift X u) (c11_identityShift Y u)) =
      fun u : ℝ => ∑ i : Fin n, ∑ j : Fin n,
        (hX.isHermitian.eigenvalues i + u) *
          (Real.log (hX.isHermitian.eigenvalues i + u) -
            Real.log (hY.isHermitian.eigenvalues j + u)) *
              NLA.MI24.unitaryOverlapWeight
                (star hX.isHermitian.eigenvectorUnitary * hY.isHermitian.eigenvectorUnitary) i j := by
    funext u
    exact c11_relative_entropy_shift_spectral hn X Y hX.isHermitian hY.isHermitian u
  rw [heq]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  exact (c11_hasDerivAt_scalar_shift (hX.isHermitian.eigenvalues i)
    (hY.isHermitian.eigenvalues j) r
    (add_pos_of_pos_of_nonneg (hX.eigenvalues_pos i) hr)
    (add_pos_of_pos_of_nonneg (hY.eigenvalues_pos j) hr)).mul_const _

#print axioms c11_relative_entropy_shift_spectral
#print axioms c11_hasDerivAt_relative_entropy_shift_spectral

end NLA.MI27
