# Proposed C11 identity-shift improper-integral extension

These exact additional helper headers are recorded before proof bodies. They
do not amend the already approved first plan. Source author remains
`/root/nr04_mf14_final_referee_a`; only root runs Lean.

Pinned Mathlib has `integrableOn_Ioi_deriv_of_nonneg'` and
`integral_Ioi_of_hasDerivAt_of_tendsto'`. The explicit shift kernel is
nonnegative by log(u) <= u-1, weighted by nonnegative actual unitary overlaps.
Together with the boundary limit this permits a genuine Bochner integral on
(0,infinity), removing that remaining identity-shift interface. It still
does not identify the kernel with the positive-part/layer-cake expression.

The new module would be `NLA/MI27/IdentityShiftImproper.lean`, importing
IdentityShiftFTC and Mathlib.MeasureTheory.Integral.IntegralEqImproper.
All declarations are in namespace `NLA.MI27`.

```lean
lemma c11_scalar_shiftKernel_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ -(Real.log x - Real.log y + (y - x) / y)

lemma c11_shiftKernel_nonneg {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ c11_shiftKernel X Y hX.isHermitian hY.isHermitian r

lemma c11_shiftKernel_integral_Ioi {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.IntegrableOn
      (c11_shiftKernel X Y hX.isHermitian hY.isHermitian) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), c11_shiftKernel X Y hX.isHermitian hY.isHermitian r) =
        relEntropy X Y - trR (X - Y)

lemma c11_density_shiftKernel_integral_Ioi {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) :
    MeasureTheory.IntegrableOn
      (c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), c11_shiftKernel ρ σ hρ.1.isHermitian hσ.1.isHermitian r) =
        relEntropy ρ σ
```

The general-PD trace correction is necessary. Omitting it before trace-one
normalization would be false. Finite dimension, repeated spectra, and
noncommutativity are all preserved, and no new assumption enters frozen C11.
