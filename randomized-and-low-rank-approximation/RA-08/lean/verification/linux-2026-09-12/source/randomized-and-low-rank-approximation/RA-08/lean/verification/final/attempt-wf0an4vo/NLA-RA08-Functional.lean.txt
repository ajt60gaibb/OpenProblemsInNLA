/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
-/
import NLA.RA08.Location
import NLA.RA08.Polynomial
import Mathlib.Tactic.FunProp

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped MatrixOrder
noncomputable section
namespace NLA.RA08

theorem minorant_functional_calculus_proved :
    functionalCalculus minorantFunction witnessMatrix = minorantMatrix witnessMatrix ∧
      minorantMatrix witnessMatrix ≤ functionalCalculus witnessFunction witnessMatrix := by
  refine ⟨minorant_cfc _ witnessMatrix_psd.isHermitian, ?_⟩
  rw [← minorant_cfc _ witnessMatrix_psd.isHermitian]
  apply cfc_mono
  · intro x hx
    rcases witness_spectral_location_proved hx with h | h
    · exact minorant_scalar_proved x h.1 (Or.inl h.2)
    · have h0 : 0 ≤ x := by norm_num [Set.mem_Ici, witnessA] at h; linarith
      exact minorant_scalar_proved x h0 (Or.inr h)
  · change ContinuousOn minorantFunction (spectrum ℝ witnessMatrix)
    unfold minorantFunction
    fun_prop
  · change ContinuousOn witnessFunction (spectrum ℝ witnessMatrix)
    unfold witnessFunction
    fun_prop

#assert_trust kernel minorant_functional_calculus_proved
#print axioms minorant_functional_calculus_proved

end NLA.RA08
