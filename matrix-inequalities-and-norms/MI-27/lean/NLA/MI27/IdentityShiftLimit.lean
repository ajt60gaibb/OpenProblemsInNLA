/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Identity-shift argument: Péter E. Frenkel.
The imported fixed-eigenbasis expansion and MI24 overlap code retain their credits.

The exact logarithmic remainder tends to zero by a scalar sandwich. The two
individual eigenbases are fixed separately; no simultaneous diagonalization
or eigenvector-continuity assertion is used. This is one C11 helper, not the
noncommutative hockey-stick identity. Exact headers preceded all proof bodies.
Local compilation belongs to root; this source author has not run Lean.
-/
import NLA.MI27.IdentityShift
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open Filter
open scoped BigOperators Classical Topology ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- A direct exact remainder bound, including x = y and both signs of x - y. -/
lemma c11_scalar_shift_error_bounds (x y r : ℝ)
    (hx : 0 < x + r) (hy : 0 < y + r) :
    0 ≤ (x + r) * (Real.log (x + r) - Real.log (y + r)) - (x - y) ∧
      (x + r) * (Real.log (x + r) - Real.log (y + r)) - (x - y) ≤
        (x - y) ^ 2 / (y + r) := by
  have hlo := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le
  rw [Real.log_div hy.ne' hx.ne'] at hlo
  have hlo_rhs : (x + r) * ((y + r) / (x + r) - 1) = y - x := by
    field_simp [hx.ne']
    <;> ring
  rw [hlo_rhs] at hlo
  have hup := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx hy)) hx.le
  rw [Real.log_div hx.ne' hy.ne'] at hup
  have hup_rhs : (x + r) * ((x + r) / (y + r) - 1) =
      (x - y) + (x - y) ^ 2 / (y + r) := by
    field_simp [hy.ne']
    <;> ring
  rw [hup_rhs] at hup
  constructor <;> nlinarith

/-- Large positive shifts make both scalar log arguments positive; no assumptions on x,y. -/
lemma c11_tendsto_scalar_shift (x y : ℝ) :
    Filter.Tendsto
      (fun r : ℝ => (x + r) * (Real.log (x + r) - Real.log (y + r)))
      Filter.atTop (nhds (x - y)) := by
  have hb : ∀ᶠ r : ℝ in atTop,
      0 ≤ (x + r) * (Real.log (x + r) - Real.log (y + r)) - (x - y) ∧
        (x + r) * (Real.log (x + r) - Real.log (y + r)) - (x - y) ≤
          (x - y) ^ 2 / (y + r) := by
    filter_upwards [eventually_ge_atTop (max (1 - x) (1 - y))] with r hr
    have hx : 0 < x + r := by
      have := le_max_left (1 - x) (1 - y)
      linarith
    have hy : 0 < y + r := by
      have := le_max_right (1 - x) (1 - y)
      linarith
    exact c11_scalar_shift_error_bounds x y r hx hy
  have hden : Tendsto (fun r : ℝ => y + r) atTop atTop :=
    tendsto_atTop_add_const_left atTop y tendsto_id
  have hzero : Tendsto (fun r : ℝ => (x - y) ^ 2 / (y + r)) atTop (𝓝 0) :=
    hden.const_div_atTop ((x - y) ^ 2)
  have herr := squeeze_zero' (hb.mono fun _ hr => hr.1) (hb.mono fun _ hr => hr.2) hzero
  have hadd := herr.add (tendsto_const_nhds (x := x - y))
  simpa only [sub_add_cancel, zero_add] using hadd

/-- Both true unitary-overlap marginals give the literal trace difference. -/
lemma c11_overlap_trace_difference {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (∑ i : Fin n, ∑ j : Fin n,
      (hX.eigenvalues i - hY.eigenvalues j) *
        NLA.MI24.unitaryOverlapWeight
          (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j) =
      trR (X - Y) := by
  have hm := NLA.MI24.unitaryOverlapWeight_marginals
    (star hX.eigenvectorUnitary * hY.eigenvectorUnitary)
    hX.eigenvalues hY.eigenvalues (1 : ℝ) (-1 : ℝ)
  have htrX := (spectral_function_semantics hn X hX (id : ℝ → ℝ)
    (X.finite_real_spectrum.continuousOn _)).2.1
  have htrY := (spectral_function_semantics hn Y hY (id : ℝ → ℝ)
    (Y.finite_real_spectrum.continuousOn _)).2.1
  simp only [cfc_id ℝ X hX.isSelfAdjoint, id_eq] at htrX
  simp only [cfc_id ℝ Y hY.isSelfAdjoint, id_eq] at htrY
  have ht : trR (X - Y) =
      (∑ i : Fin n, hX.eigenvalues i) - ∑ j : Fin n, hY.eigenvalues j := by
    calc
      trR (X - Y) = trR X - trR Y := by
        simp only [trR, Matrix.trace_sub, Complex.sub_re]
      _ = _ := by rw [htrX, htrY]
  rw [ht]
  simpa only [one_mul, neg_one_mul, ← sub_eq_add_neg] using hm

/-- Actual noncommuting relative entropy has the correct boundary term at infinity. -/
lemma c11_tendsto_relative_entropy_identityShift {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    Filter.Tendsto
      (fun r : ℝ => relEntropy (c11_identityShift X r) (c11_identityShift Y r))
      Filter.atTop (nhds (trR (X - Y))) := by
  have heq :
      (fun r : ℝ => relEntropy (c11_identityShift X r) (c11_identityShift Y r)) =
        fun r : ℝ => ∑ i : Fin n, ∑ j : Fin n,
          (hX.eigenvalues i + r) *
            (Real.log (hX.eigenvalues i + r) - Real.log (hY.eigenvalues j + r)) *
              NLA.MI24.unitaryOverlapWeight
                (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j := by
    funext r
    exact c11_relative_entropy_shift_spectral hn X Y hX hY r
  rw [heq, ← c11_overlap_trace_difference hn X Y hX hY]
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (c11_tendsto_scalar_shift (hX.eigenvalues i) (hY.eigenvalues j)).mul_const _

/-- Trace-one inputs cancel the boundary term without a commutativity premise. -/
lemma c11_tendsto_density_relative_entropy_identityShift {n : ℕ} (hn : 1 ≤ n)
    (ρ σ : Mat n) (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    Filter.Tendsto
      (fun r : ℝ => relEntropy (c11_identityShift ρ r) (c11_identityShift σ r))
      Filter.atTop (nhds 0) := by
  have htrace : trR (ρ - σ) = 0 := by
    simp only [trR, Matrix.trace_sub, hρ.2, hσ.2, sub_self, Complex.zero_re]
  simpa only [htrace] using
    c11_tendsto_relative_entropy_identityShift hn ρ σ hρ.1.isHermitian hσ.1.isHermitian

#print axioms c11_scalar_shift_error_bounds
#assert_trust kernel c11_scalar_shift_error_bounds
#print axioms c11_tendsto_relative_entropy_identityShift
#assert_trust kernel c11_tendsto_relative_entropy_identityShift
#print axioms c11_tendsto_density_relative_entropy_identityShift
#assert_trust kernel c11_tendsto_density_relative_entropy_identityShift

end NLA.MI27
