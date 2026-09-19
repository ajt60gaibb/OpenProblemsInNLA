/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nm04_final_referee1.

Nonnegative scalar scaling for actual CFC powers. Finite matrix spectra make
the scalar functions continuous on the exact spectral sets, including zero.
The proof also covers scalar zero; no inverse or strict positivity is used.
-/
import NLA.MI24.TraceSpectral

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI24

lemma spectralPower_smul_nonneg {n : ℕ} (A : Mat n) (hA : A.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) (r : ℝ) :
    spectralPower ((c : ℂ) • A) r = (c ^ r : ℝ) • spectralPower A r := by
  have hscaled : 0 ≤ c • A := smul_nonneg hc hA.nonneg
  have hcast : (c : ℂ) • A = c • A := by
    ext i j
    -- After matrix extensionality, expose entrywise complex versus real
    -- scalar multiplication so Complex.real_smul supplies the scalar-tower bridge.
    change (c : ℂ) * A i j = c • A i j
    exact Complex.real_smul.symm
  have hcf (B : Mat n) (hB : 0 ≤ B) :
      spectralPower B r = cfc (fun x : ℝ => x ^ r) B := by
    simpa only [spectralPower, CFC.rpow_eq_pow] using
      CFC.rpow_eq_cfc_real (a := B) (y := r) hB
  rw [hcast, hcf _ hscaled]
  rw [← cfc_comp_const_mul c (fun x : ℝ => x ^ r) A
    ((A.finite_real_spectrum.image (fun x : ℝ => c * x)).continuousOn _)
    hA.isHermitian.isSelfAdjoint]
  calc
    cfc (fun x : ℝ => (c * x) ^ r) A = cfc (fun x : ℝ => c ^ r * x ^ r) A := by
      apply cfc_congr
      intro x hx
      exact Real.mul_rpow hc (spectrum_nonneg_of_nonneg hA.nonneg hx)
    _ = (c ^ r : ℝ) • cfc (fun x : ℝ => x ^ r) A :=
      cfc_const_mul _ _ _ (A.finite_real_spectrum.continuousOn _)
    _ = (c ^ r : ℝ) • spectralPower A r := by rw [hcf A hA.nonneg]

lemma traceReal_smul_real {n : ℕ} (A : Mat n) (c : ℝ) :
    traceReal (c • A) = c * traceReal A := by
  unfold traceReal
  rw [Matrix.trace_smul]
  exact Complex.smul_re c A.trace

lemma matrixModulus_of_posSemidef {n : ℕ} (A : Mat n) (hA : A.PosSemidef) :
    matrixModulus A = A := CFC.abs_of_nonneg A hA.nonneg

lemma finiteSchattenNorm_of_posSemidef {n : ℕ} (A : Mat n)
    (hA : A.PosSemidef) (p : ℝ) :
    finiteSchattenNorm p A = (traceReal (spectralPower A p)) ^ (1 / p) := by
  unfold finiteSchattenNorm
  rw [matrixModulus_of_posSemidef A hA]
  rfl

lemma finiteSchattenNorm_nonneg {n : ℕ} (A : Mat n) (p : ℝ) :
    0 ≤ finiteSchattenNorm p A := by
  exact Real.rpow_nonneg
    (traceReal_spectralPower_nonneg _
      (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)) p) _

theorem positive_schatten_smul {n : ℕ} (hn : 1 ≤ n) (U : Mat n)
    (hU : U.PosSemidef) (p : ℝ) (hp : 1 ≤ p) (c : ℝ) (hc : 0 ≤ c) :
    finiteSchattenNorm p ((c : ℂ) • U) = c * finiteSchattenNorm p U := by
  clear hn
  have hscaled : ((c : ℂ) • U).PosSemidef := hU.smul (by exact_mod_cast hc)
  have hp0 : p ≠ 0 := by linarith
  calc
    _ = (c ^ p * traceReal (spectralPower U p)) ^ (1 / p) := by
      rw [finiteSchattenNorm_of_posSemidef _ hscaled,
        spectralPower_smul_nonneg U hU c hc, traceReal_smul_real]
    _ = (c ^ p) ^ (1 / p) * (traceReal (spectralPower U p)) ^ (1 / p) :=
      Real.mul_rpow (Real.rpow_nonneg hc p) (traceReal_spectralPower_nonneg U hU p)
    _ = c * finiteSchattenNorm p U := by
      rw [finiteSchattenNorm_of_posSemidef U hU]
      simp only [one_div, Real.rpow_rpow_inv hc hp0]

end NLA.MI24
