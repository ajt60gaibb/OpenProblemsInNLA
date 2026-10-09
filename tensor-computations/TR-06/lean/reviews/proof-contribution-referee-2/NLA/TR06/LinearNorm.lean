/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal

namespace NLA.TR06

/-- The chart derivative ratio is the operator norm on the input tangent range
with its induced Frobenius norm. No numerical certificate is needed. -/
theorem derivativeRatio_eq_operatorNorm {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
    (dφ : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (dg : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r)
    (hinj : Function.Injective dφ) :
    derivativeRatio dφ dg = ENNReal.ofReal ‖inducedDerivative dφ dg hinj‖ := by
  let e := LinearEquiv.ofInjective dφ.toLinearMap hinj
  let T := inducedDerivative dφ dg hinj
  have hT (v : EuclideanSpace ℝ (Fin k)) : T (e v) = dg v := by
    simp [T, inducedDerivative, e]
  have he_norm (v : EuclideanSpace ℝ (Fin k)) : ‖e v‖ = ‖dφ v‖ := rfl
  have hupper : derivativeRatio dφ dg ≤ ENNReal.ofReal ‖T‖ := by
    unfold derivativeRatio
    refine iSup_le fun v => ?_
    simpa only [hT, he_norm] using
      ENNReal.ofReal_le_ofReal (T.ratio_le_opNorm (e v))
  have hfinite : derivativeRatio dφ dg ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  apply le_antisymm hupper
  apply (ENNReal.ofReal_le_iff_le_toReal hfinite).2
  apply T.opNorm_le_bound ENNReal.toReal_nonneg
  intro w
  obtain ⟨v, rfl⟩ := e.surjective w
  by_cases hzero : e v = 0
  · simp [hzero]
  · have hpos : 0 < ‖e v‖ := norm_pos_iff.mpr hzero
    have hratio : ‖T (e v)‖ / ‖e v‖ ≤ (derivativeRatio dφ dg).toReal := by
      simpa only [hT, he_norm] using
        (ENNReal.ofReal_le_iff_le_toReal hfinite).1
          (le_iSup (fun z : EuclideanSpace ℝ (Fin k) =>
            ENNReal.ofReal (‖dg z‖ / ‖dφ z‖)) v)
    exact (div_le_iff₀ hpos).1 hratio

end NLA.TR06

#print axioms NLA.TR06.derivativeRatio_eq_operatorNorm
#assert_trust kernel NLA.TR06.derivativeRatio_eq_operatorNorm
