/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 resolution: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Identity-shift argument: Péter E. Frenkel.
The imported matrix spectral and overlap code retains its prior credits.

This finite FTC bridge integrates the actual, already established derivative
along identity shifts. Its integral limit uses the literal trace-one boundary
term. It does not equate this scalar kernel with any positive-part integral,
nor assert an unproved improper-integrability or layer-cake theorem.
Exact headers were recorded and root-reviewed before proof development.
Root alone runs the serial local compiler; this author has not run Lean.
-/
import NLA.MI27.IdentityShiftLimit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open Filter
open scoped BigOperators Classical Topology ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- The negative derivative from the two fixed individual spectra, explicitly expanded. -/
def c11_shiftKernel {n : ℕ} (X Y : Mat n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (r : ℝ) : ℝ :=
  -(∑ i : Fin n, ∑ j : Fin n,
    (Real.log (hX.eigenvalues i + r) - Real.log (hY.eigenvalues j + r) +
      (hY.eigenvalues j - hX.eigenvalues i) / (hY.eigenvalues j + r)) *
        NLA.MI24.unitaryOverlapWeight
          (star hX.eigenvectorUnitary * hY.eigenvectorUnitary) i j)

/-- Strict positivity excludes every denominator/log singularity on the closed half-line. -/
lemma c11_shiftKernel_continuousOn {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    ContinuousOn (c11_shiftKernel X Y hX.isHermitian hY.isHermitian) (Set.Ici 0) := by
  unfold c11_shiftKernel
  apply ContinuousOn.neg
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  have hx : ContinuousOn (fun r : ℝ => hX.isHermitian.eigenvalues i + r) (Set.Ici 0) :=
    continuousOn_const.add continuousOn_id
  have hy : ContinuousOn (fun r : ℝ => hY.isHermitian.eigenvalues j + r) (Set.Ici 0) :=
    continuousOn_const.add continuousOn_id
  have hxne : ∀ r ∈ Set.Ici (0 : ℝ), hX.isHermitian.eigenvalues i + r ≠ 0 := by
    intro r hr
    exact (add_pos_of_pos_of_nonneg (hX.eigenvalues_pos i) hr).ne'
  have hyne : ∀ r ∈ Set.Ici (0 : ℝ), hY.isHermitian.eigenvalues j + r ≠ 0 := by
    intro r hr
    exact (add_pos_of_pos_of_nonneg (hY.eigenvalues_pos j) hr).ne'
  exact (((hx.log hxne).sub (hy.log hyne)).add
    (continuousOn_const.div hy hyne)).mul continuousOn_const

/-- The exact finite FTC identity includes R = 0; no improper integral is introduced. -/
lemma c11_shiftKernel_finite_integral {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (R : ℝ) (hR : 0 ≤ R) :
    IntervalIntegrable (c11_shiftKernel X Y hX.isHermitian hY.isHermitian)
      MeasureTheory.volume 0 R ∧
      (∫ r in (0 : ℝ)..R, c11_shiftKernel X Y hX.isHermitian hY.isHermitian r) =
        relEntropy X Y - relEntropy (c11_identityShift X R) (c11_identityShift Y R) := by
  have hi : IntervalIntegrable (c11_shiftKernel X Y hX.isHermitian hY.isHermitian)
      MeasureTheory.volume 0 R :=
    ((c11_shiftKernel_continuousOn X Y hX hY).mono
      (show Set.Icc (0 : ℝ) R ⊆ Set.Ici 0 from fun _ hr => hr.1)).intervalIntegrable_of_Icc hR
  have hd : ∀ r ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt
        (fun u : ℝ => -relEntropy (c11_identityShift X u) (c11_identityShift Y u))
        (c11_shiftKernel X Y hX.isHermitian hY.isHermitian r) r := by
    intro r hr
    have hr0 : 0 ≤ r := (Set.uIcc_of_le hR ▸ hr).1
    unfold c11_shiftKernel
    convert! (c11_hasDerivAt_relative_entropy_shift_spectral hn X Y hX hY r hr0).neg
      using 1 <;> rfl
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hX0 : c11_identityShift X 0 = X := by simp [c11_identityShift]
  have hY0 : c11_identityShift Y 0 = Y := by simp [c11_identityShift]
  refine ⟨hi, ?_⟩
  simpa only [hX0, hY0, neg_sub_neg] using he

/-- The limits of finite integrals recover ordinary entropy after the density boundary cancels. -/
lemma c11_tendsto_shiftKernel_integral {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    Filter.Tendsto
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian r)
      Filter.atTop (nhds (relEntropy ρ σ)) := by
  have hlim : Tendsto
      (fun R : ℝ => relEntropy ρ σ -
        relEntropy (c11_identityShift ρ R) (c11_identityShift σ R))
      atTop (𝓝 (relEntropy ρ σ)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := relEntropy ρ σ)).sub
        (c11_tendsto_density_relative_entropy_identityShift hn ρ σ hρ hσ)
  have heq :
      (fun R : ℝ => ∫ r in (0 : ℝ)..R,
        c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian r) =ᶠ[atTop]
      (fun R : ℝ => relEntropy ρ σ -
        relEntropy (c11_identityShift ρ R) (c11_identityShift σ R)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (c11_shiftKernel_finite_integral hn ρ σ hρ.1 hσ.1 R hR).2
  exact hlim.congr' heq.symm

#print axioms c11_shiftKernel_continuousOn
#assert_trust kernel c11_shiftKernel_continuousOn
#print axioms c11_shiftKernel_finite_integral
#assert_trust kernel c11_shiftKernel_finite_integral
#print axioms c11_tendsto_shiftKernel_integral
#assert_trust kernel c11_tendsto_shiftKernel_integral

end NLA.MI27
