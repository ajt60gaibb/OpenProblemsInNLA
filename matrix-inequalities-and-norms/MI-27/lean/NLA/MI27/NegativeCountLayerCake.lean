/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The C11 identity-shift route
is based on Peter E. Frenkel's integral representation. This module supplies
only the finite-spectrum layer-cake step, using actual Bochner integrals.
It preserves the spectral and trace-code attribution in the imported files.
Exact headers approved before bodies in NEGATIVE-COUNT-LAYERCAKE-STATEMENTS.md.
-/
import NLA.MI27.NegativeCount
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
open MeasureTheory Set
noncomputable section
namespace NLA.MI27

/-- The strict indicator occupies the interval `(0,-x)`, with no endpoint atoms. -/
lemma c11_integral_negative_indicator (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => if x + r < 0 then (1 : ℝ) else 0) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), if x + r < 0 then (1 : ℝ) else 0) = max (-x) 0 := by
  have hfun : (fun r : ℝ => if x + r < 0 then (1 : ℝ) else 0) =
      (Iio (-x)).indicator (fun _ : ℝ => (1 : ℝ)) := by
    funext r
    have hr : x + r < 0 ↔ r < -x := by constructor <;> intro h <;> linarith
    simp only [Set.indicator_apply, Set.mem_Iio, hr]
  have hset : Iio (-x) ∩ Ioi (0 : ℝ) = Ioo 0 (-x) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
    exact and_comm
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 (-x)) :=
    integrableOn_const (by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top)
  refine ⟨?_, ?_⟩
  · rw [hfun, integrableOn_indicator_iff measurableSet_Iio, hset]
    exact hi
  · rw [hfun, integral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, hset, setIntegral_const]
    simp only [Real.volume_real_Ioo, sub_zero, smul_eq_mul, mul_one]

/-- The negative trace is the actual integral of strict negative counts of identity shifts.
Finite spectra make this valid without simplicity, invertibility, or sign assumptions on M. -/
lemma c11_negativeCount_shift_integral {n : ℕ} (hn : 1 ≤ n) (M : Mat n)
    (hM : M.IsHermitian) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => c11_negativeCount (c11_identityShift M r)) (Set.Ioi 0) ∧
      (∫ r in Set.Ioi (0 : ℝ), c11_negativeCount (c11_identityShift M r)) =
        tracePos (-M) := by
  have heq : (fun r : ℝ => c11_negativeCount (c11_identityShift M r)) =
      fun r : ℝ => ∑ i : Fin n,
        if hM.eigenvalues i + r < 0 then (1 : ℝ) else 0 := by
    funext r
    exact c11_negativeCount_identityShift hn M hM r
  have hi (i : Fin n) : Integrable
      (fun r : ℝ => if hM.eigenvalues i + r < 0 then (1 : ℝ) else 0)
      (volume.restrict (Ioi 0)) :=
    (c11_integral_negative_indicator (hM.eigenvalues i)).1
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact integrable_finsetSum Finset.univ (fun i _ => hi i)
  · calc
      (∫ r in Ioi (0 : ℝ), c11_negativeCount (c11_identityShift M r)) =
          ∫ r in Ioi (0 : ℝ), ∑ i : Fin n,
            if hM.eigenvalues i + r < 0 then (1 : ℝ) else 0 := by rw [heq]
      _ = ∑ i : Fin n, ∫ r in Ioi (0 : ℝ),
          if hM.eigenvalues i + r < 0 then (1 : ℝ) else 0 :=
        integral_finsetSum Finset.univ (fun i _ => hi i)
      _ = ∑ i : Fin n, max (-hM.eigenvalues i) 0 :=
        Finset.sum_congr rfl (fun i _ => (c11_integral_negative_indicator _).2)
      _ = tracePos (-M) := by
        simpa only [c11_identityShift, Complex.ofReal_zero, zero_smul, add_zero] using
          (c11_tracePos_neg_identityShift hn M hM 0).symm

#print axioms c11_integral_negative_indicator
#print axioms c11_negativeCount_shift_integral

end NLA.MI27
