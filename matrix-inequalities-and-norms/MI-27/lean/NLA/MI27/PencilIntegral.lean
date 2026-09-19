/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The negative-count pencil
representation and identity-shift method follow Peter E. Frenkel. The
imported spectral, overlap, and congruence proofs retain their authorship.

Both exact headers were approved by root and independent referee B before
bodies in PENCIL-INTEGRAL-STATEMENTS.md. Product integrability is proved
before the order of integration is changed. The trace correction for
general positive-definite matrices is retained. Full finite hockey-stick
C11 is not asserted here. This source author runs no Lean or Comparator.
-/
import NLA.MI27.PencilCount
import NLA.MI27.NegativeCountMeasurable
import NLA.MI27.NegativeCountLayerCake
import NLA.MI27.IdentityShiftImproper
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_pencil_count_integrable_prod {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.Integrable
      (fun z : ℝ × ℝ => c11_pencilWeight z.2 *
        c11_negativeCount (c11_identityShift (X + (z.2 : ℂ) • (Y - X)) z.1))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod MeasureTheory.volume) := by
  let G : ℝ × ℝ → ℝ := fun z => c11_pencilWeight z.2 *
    c11_negativeCount (c11_identityShift (X + (z.2 : ℂ) • (Y - X)) z.1)
  have hcount : Measurable (fun z : ℝ × ℝ =>
      c11_negativeCount (c11_identityShift (X + (z.2 : ℂ) • (Y - X)) z.1)) := by
    convert! (c11_negativeCount_pencil_measurable hn X Y hX.isHermitian hY.isHermitian).comp
      measurable_swap using 1 <;> rfl
  have hweight : Measurable (fun z : ℝ × ℝ => c11_pencilWeight z.2) := by
    unfold c11_pencilWeight
    fun_prop
  have hG : Measurable G := hweight.mul hcount
  have hnorm (z : ℝ × ℝ) : ‖G z‖ = G z := by
    have hz : (c11_identityShift (X + (z.2 : ℂ) • (Y - X)) z.1).IsHermitian :=
      (hX.isHermitian.add ((hY.isHermitian.sub hX.isHermitian).smul
        (by simp [IsSelfAdjoint]))).add
          (Matrix.isHermitian_one.smul (by simp [IsSelfAdjoint]))
    exact Real.norm_of_nonneg (mul_nonneg (c11_pencilWeight_nonneg z.2)
      (c11_negativeCount_bounds hn _ hz).1)
  have hsection (r : ℝ) (hr : 0 < r) :
      (∫ t : ℝ, ‖G (r, t)‖) = c11_shiftKernel X Y hX.isHermitian hY.isHermitian r := by
    simp_rw [hnorm]
    exact (c11_shifted_pencil_count_integral hn X Y hX hY r hr.le).2
  change Integrable G ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume)
  refine (integrable_prod_iff hG.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (c11_shifted_pencil_count_integral hn X Y hX hY r hr.le).1
  · apply (c11_shiftKernel_integral_Ioi hn X Y hX hY).1.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hsection r hr).symm

lemma c11_relative_entropy_pencil_integral {n : ℕ} (hn : 1 ≤ n)
    (X Y : Mat n) (hX : X.PosDef) (hY : Y.PosDef) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X)))) ∧
      relEntropy X Y - trR (X - Y) =
        ∫ t : ℝ, c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X))) := by
  let G : ℝ → ℝ → ℝ := fun r t => c11_pencilWeight t *
    c11_negativeCount (c11_identityShift (X + (t : ℂ) • (Y - X)) r)
  have hG : Integrable (Function.uncurry G)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) :=
    c11_pencil_count_integrable_prod hn X Y hX hY
  have hinner (t : ℝ) : (∫ r in Set.Ioi (0 : ℝ), G r t) =
      c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X))) := by
    have ht : (X + (t : ℂ) • (Y - X)).IsHermitian :=
      hX.isHermitian.add ((hY.isHermitian.sub hX.isHermitian).smul
        (by simp [IsSelfAdjoint]))
    dsimp only [G]
    rw [integral_const_mul, (c11_negativeCount_shift_integral hn _ ht).2]
  have hi : Integrable (fun t : ℝ => ∫ r in Set.Ioi (0 : ℝ), G r t) :=
    hG.integral_prod_right
  refine ⟨?_, ?_⟩
  · simpa only [hinner] using hi
  · calc
      relEntropy X Y - trR (X - Y) =
          ∫ r in Set.Ioi (0 : ℝ), c11_shiftKernel X Y hX.isHermitian hY.isHermitian r :=
        (c11_shiftKernel_integral_Ioi hn X Y hX hY).2.symm
      _ = ∫ r in Set.Ioi (0 : ℝ), ∫ t : ℝ, G r t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact (c11_shifted_pencil_count_integral hn X Y hX hY r hr.le).2.symm
      _ = ∫ t : ℝ, ∫ r in Set.Ioi (0 : ℝ), G r t := integral_integral_swap hG
      _ = ∫ t : ℝ, c11_pencilWeight t * tracePos (-(X + (t : ℂ) • (Y - X))) := by
        apply integral_congr_ae
        filter_upwards with t
        exact hinner t

#print axioms c11_pencil_count_integrable_prod
#assert_trust kernel c11_pencil_count_integrable_prod
#print axioms c11_relative_entropy_pencil_integral
#assert_trust kernel c11_relative_entropy_pencil_integral

end NLA.MI27
