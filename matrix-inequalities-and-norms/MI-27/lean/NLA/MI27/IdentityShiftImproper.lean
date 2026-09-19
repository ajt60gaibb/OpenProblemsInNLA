/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Identity-shift argument: Péter E. Frenkel.
The imported matrix spectral and unitary overlap sources retain prior credits.

Nonnegativity of the explicitly expanded negative shift derivative and its
finite boundary limit imply actual Bochner integrability on the half-line.
This establishes the identity-shift integral, including the necessary trace
correction for unnormalized positive definite pairs. Its relation to the
positive-part/layer-cake integral is a separate remaining C11 obligation.
The exact extension headers were root-reviewed before these proof bodies.
This source author has not run Lean; root alone compiles locally.
-/
import NLA.MI27.IdentityShiftFTC
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open Filter
open scoped BigOperators Classical Topology ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- The scalar negative shift derivative is nonnegative, with equality when x = y. -/
lemma c11_scalar_shiftKernel_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ -(Real.log x - Real.log y + (y - x) / y) := by
  have hlog := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne'] at hlog
  have hratio : (y - x) / y = 1 - x / y := by
    field_simp [hy.ne']
  rw [hratio]
  linarith

/-- Actual unitary overlap weights preserve the sign of every scalar summand. -/
lemma c11_shiftKernel_nonneg {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ c11_shiftKernel X Y hX.isHermitian hY.isHermitian r := by
  unfold c11_shiftKernel
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i _
  apply Finset.sum_nonpos
  intro j _
  have hterm := c11_scalar_shiftKernel_nonneg
    (hX.isHermitian.eigenvalues i + r) (hY.isHermitian.eigenvalues j + r)
    (add_pos_of_pos_of_nonneg (hX.eigenvalues_pos i) hr)
    (add_pos_of_pos_of_nonneg (hY.eigenvalues_pos j) hr)
  have hdiff : hY.isHermitian.eigenvalues j + r -
      (hX.isHermitian.eigenvalues i + r) =
      hY.isHermitian.eigenvalues j - hX.isHermitian.eigenvalues i := by ring
  rw [hdiff] at hterm
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonneg.mp hterm)
    (NLA.MI24.unitaryOverlapWeight_nonneg _ i j)

/-- The actual improper integral has a trace correction for general positive inputs. -/
lemma c11_shiftKernel_integral_Ioi {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.IntegrableOn
      (c11_shiftKernel X Y hX.isHermitian hY.isHermitian) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), c11_shiftKernel X Y hX.isHermitian hY.isHermitian r) =
        relEntropy X Y - trR (X - Y) := by
  have hd : ∀ r ∈ Set.Ici (0 : ℝ),
      HasDerivAt
        (fun u : ℝ => -relEntropy (c11_identityShift X u) (c11_identityShift Y u))
        (c11_shiftKernel X Y hX.isHermitian hY.isHermitian r) r := by
    intro r hr
    unfold c11_shiftKernel
    convert! (c11_hasDerivAt_relative_entropy_shift_spectral hn X Y hX hY r hr).neg
      using 1 <;> rfl
  have hpos : ∀ r ∈ Set.Ioi (0 : ℝ),
      0 ≤ c11_shiftKernel X Y hX.isHermitian hY.isHermitian r := by
    intro r hr
    exact c11_shiftKernel_nonneg X Y hX hY r hr.le
  have hlim : Tendsto
      (fun r : ℝ => -relEntropy (c11_identityShift X r) (c11_identityShift Y r))
      atTop (𝓝 (-trR (X - Y))) :=
    (c11_tendsto_relative_entropy_identityShift hn X Y hX.isHermitian hY.isHermitian).neg
  have hi := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim
  have he := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hlim
  have hX0 : c11_identityShift X 0 = X := by simp [c11_identityShift]
  have hY0 : c11_identityShift Y 0 = Y := by simp [c11_identityShift]
  refine ⟨hi, ?_⟩
  simpa only [hX0, hY0, neg_sub_neg] using he

/-- For strict density matrices the ordinary Umegaki entropy is recovered exactly. -/
lemma c11_density_shiftKernel_integral_Ioi {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    MeasureTheory.IntegrableOn
      (c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian r) =
        relEntropy ρ σ := by
  have htrace : trR (ρ - σ) = 0 := by
    simp only [trR, Matrix.trace_sub, hρ.2, hσ.2, sub_self, Complex.zero_re]
  simpa only [htrace, sub_zero] using c11_shiftKernel_integral_Ioi hn ρ σ hρ.1 hσ.1

#print axioms c11_scalar_shiftKernel_nonneg
#assert_trust kernel c11_scalar_shiftKernel_nonneg
#print axioms c11_shiftKernel_nonneg
#assert_trust kernel c11_shiftKernel_nonneg
#print axioms c11_shiftKernel_integral_Ioi
#assert_trust kernel c11_shiftKernel_integral_Ioi
#print axioms c11_density_shiftKernel_integral_Ioi
#assert_trust kernel c11_density_shiftKernel_integral_Ioi

end NLA.MI27
