/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Proof-only CFC and limit helpers for Colbrook's MI-07 counterexample.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI07.Definitions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FunProp

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Topology
open Filter Matrix
noncomputable section

namespace NLA.MI07

/-- Positive powers of a projection retain the nullspace. The exponent-zero
unital power is deliberately not used to compute this limit. -/
theorem rpow_projection {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosSemidef) (hidem : IsIdempotentElem P) (q : ℝ) (hq : 0 < q) :
    CFC.rpow P q = P := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hP.nonneg]
  conv_rhs => rw [← cfc_id' ℝ P hP.isHermitian]
  apply cfc_congr
  intro x hx
  have hx01 := (isIdempotentElem_iff_spectrum_subset ℝ P hP.isHermitian).mp hidem hx
  rcases hx01 with hx | hx
  · simpa [Set.mem_singleton_iff] using hx ▸ Real.zero_rpow hq.ne'
  · simp only [Set.mem_singleton_iff] at hx
    simp [hx]

set_option backward.isDefEq.respectTransparency false in
/-- Positive real scaling commutes with the genuine CFC positive power. -/
theorem rpow_real_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 < q) :
    CFC.rpow (a • H) q = (a ^ q) • CFC.rpow H q := by
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real (hH.smul ha).nonneg,
    ← cfc_comp_smul (R := ℝ) (p := IsSelfAdjoint) a (fun x : ℝ => x ^ q) H
      (by exact (Real.continuous_rpow_const hq.le).continuousOn) hH.isHermitian,
    CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hH.nonneg,
    ← cfc_smul (a ^ q) (fun x : ℝ => x ^ q) H
      (by exact (Real.continuous_rpow_const hq.le).continuousOn)]
  apply cfc_congr
  intro x hx
  exact Real.mul_rpow ha (spectrum_nonneg_of_nonneg hH.nonneg hx)

set_option backward.isDefEq.respectTransparency false in
/-- Continuity at exponent zero is used only for a positive definite matrix. -/
theorem posDef_rpow_tendsto_one {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosDef) : Tendsto (fun q : ℝ => CFC.rpow H q) (𝓝 0) (𝓝 1) := by
  let hHerm := hH.isHermitian
  have hd : Tendsto
      (fun q : ℝ => Matrix.diagonal
        (fun i => ((hHerm.eigenvalues i ^ q : ℝ) : ℂ))) (𝓝 0)
      (𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    by_cases hij : i = j
    · subst j
      have hr := (Real.continuousAt_const_rpow (b := 0) (hH.eigenvalues_pos i).ne').tendsto
      simpa only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Real.rpow_zero,
        Complex.ofReal_one] using! Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    · simp only [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      exact tendsto_const_nhds
  have hc : Continuous (Unitary.conjStarAlgAut ℂ _ hHerm.eigenvectorUnitary :
      Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
    change Continuous (fun M : Matrix (Fin n) (Fin n) ℂ =>
      (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * M *
        (hHerm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose)
    fun_prop
  have ht := (hc.tendsto (1 : Matrix (Fin n) (Fin n) ℂ)).comp hd
  simpa only [map_one, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hH.posSemidef.nonneg,
    hHerm.cfc_eq, Matrix.IsHermitian.cfc, Function.comp_def] using! ht

end NLA.MI07
