import ProofProject.BesselKernelODE
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The actual Bessel kernel transformed to the oscillator equation

For positive radius this is `r^(3/2) b(r²/4) / 2`, the source's
`sqrt(r) J₁(r)`. The slope is explicit, so the second-order equation is
available as a first-order system without an assumed solution.
-/

noncomputable section

namespace ProofProject

def besselOscillator (r : ℝ) : ℝ :=
  r * Real.sqrt r / 2 * besselKernel (r ^ 2 / 4)

def besselOscillatorSlope (r : ℝ) : ℝ :=
  Real.sqrt r / 4 *
    (3 * besselKernel (r ^ 2 / 4) + r ^ 2 * deriv besselKernel (r ^ 2 / 4))

theorem besselOscillator_eq_rpow {r : ℝ} (hr : 0 < r) :
    besselOscillator r = r ^ (3 / 2 : ℝ) * besselKernel (r ^ 2 / 4) / 2 := by
  have hp : r * Real.sqrt r = r ^ (3 / 2 : ℝ) := by
    calc
      _ = r ^ (1 : ℝ) * r ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = r ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hr _ _).symm
      _ = _ := by norm_num
  rw [besselOscillator, hp]
  ring

theorem besselOscillator_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt besselOscillator (besselOscillatorSlope r) r := by
  have ha := (hasDerivAt_pow 2 r).div_const 4
  have hb := ((besselKernel_hasDerivAt (r ^ 2 / 4)).differentiableAt.hasDerivAt).comp r ha
  have hs := Real.hasDerivAt_sqrt hr.ne'
  have hd := (((hasDerivAt_id r).mul hs).div_const 2).mul hb
  have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hsq := Real.sq_sqrt hr.le
  convert! hd using 1
  dsimp [besselOscillatorSlope]
  simp only [pow_one]
  field_simp
  ring_nf
  simp only [hsq]
  ring

theorem besselOscillatorSlope_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt besselOscillatorSlope
      (-besselOscillator r + 3 * besselOscillator r / (4 * r ^ 2)) r := by
  have ha := (hasDerivAt_pow 2 r).div_const 4
  have hb := ((besselKernel_hasDerivAt (r ^ 2 / 4)).differentiableAt.hasDerivAt).comp r ha
  have hb' := ((besselKernel_deriv_hasDerivAt (r ^ 2 / 4)).differentiableAt.hasDerivAt).comp r ha
  have hd := ((Real.hasDerivAt_sqrt hr.ne').div_const 4).mul
    ((hb.const_mul 3).add ((hasDerivAt_pow 2 r).mul hb'))
  have hs0 : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hsq := Real.sq_sqrt hr.le
  have hz : r ^ 2 / 4 ≠ 0 := by positivity
  have hdd : deriv (deriv besselKernel) (r ^ 2 / 4) =
      -(2 * deriv besselKernel (r ^ 2 / 4) + besselKernel (r ^ 2 / 4)) / (r ^ 2 / 4) := by
    apply (eq_div_iff hz).mpr
    nlinarith [besselKernel_ode (r ^ 2 / 4)]
  convert! hd using 1
  dsimp [besselOscillator]
  simp only [pow_one]
  rw [hdd]
  field_simp
  ring_nf
  simp only [hsq]
  ring

end ProofProject
