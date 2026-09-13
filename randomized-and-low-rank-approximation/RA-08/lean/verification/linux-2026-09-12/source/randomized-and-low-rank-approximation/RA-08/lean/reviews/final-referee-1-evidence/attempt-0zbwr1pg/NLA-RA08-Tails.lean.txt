/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

All-basis truncation identities for the original witness and kink image.
-/
import NLA.RA08.Fourth
import NLA.RA08.ProjectionNorm
import NLA.RA08.Spectral

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08

theorem approximation_tail_zero (d : OrderedSpectralData witnessApproximation)
    (i : Fin 6) (hi : 3 ≤ i.val) : d.eigenvalues i = 0 := by
  apply le_antisymm _ (d.nonnegative i)
  have h := d.decreasing (show (3 : Fin 6) ≤ i from hi)
  rwa [approximation_fourth d] at h

theorem approximation_truncation (d : OrderedSpectralData witnessApproximation) :
    truncation d 3 = witnessApproximation := by
  have hv : (fun i : Fin 6 => if i.val < 3 then d.eigenvalues i else 0) = d.eigenvalues := by
    funext i
    by_cases hi : i.val < 3
    · simp [hi]
    · simp [hi, approximation_tail_zero d i (Nat.le_of_not_gt hi)]
  rw [truncation, hv]
  exact d.reconstruct.symm

theorem approximation_function_truncation (d : OrderedSpectralData witnessApproximation) :
    functionTruncation d witnessFunction 3 =
      functionalCalculus witnessFunction witnessApproximation := by
  have hv : (fun i : Fin 6 => if i.val < 3 then witnessFunction (d.eigenvalues i) else 0) =
      (fun i => witnessFunction (d.eigenvalues i)) := by
    funext i
    by_cases hi : i.val < 3
    · simp [hi]
    · simp [hi, approximation_tail_zero d i (Nat.le_of_not_gt hi), witnessFunction]
  rw [functionTruncation, hv]
  exact (functionalCalculus_spectral_proved d witnessFunction).1.symm

theorem witness_tail_data_proved
    (dA : OrderedSpectralData witnessMatrix)
    (dAhat : OrderedSpectralData witnessApproximation) :
    spectralNorm (witnessMatrix - witnessApproximation) = witnessT ∧
    dA.eigenvalues 3 = witnessT ∧
    truncation dAhat 3 = witnessApproximation ∧
    functionTruncation dAhat witnessFunction 3 =
      functionalCalculus witnessFunction witnessApproximation ∧
    spectralNorm (witnessMatrix - truncation dA 3) = witnessT ∧
    spectralNorm (functionalCalculus witnessFunction witnessMatrix -
      functionTruncation dA witnessFunction 3) = witnessT := by
  have h := spectral_tail_norms_proved dA 3 (by decide) witnessFunction witnessFunction_admissible
  have hEig : dA.eigenvalues ⟨3, by decide⟩ = witnessT := witness_fourth dA
  rw [hEig] at h
  have hf : witnessFunction witnessT = witnessT := by norm_num [witnessFunction, witnessT]
  exact ⟨witness_residual_norm, witness_fourth dA, approximation_truncation dAhat,
    approximation_function_truncation dAhat, h.1, h.2.trans hf⟩

#assert_trust kernel approximation_truncation
#assert_trust kernel approximation_function_truncation
#assert_trust kernel witness_tail_data_proved
#print axioms approximation_truncation
#print axioms approximation_function_truncation
#print axioms witness_tail_data_proved

end NLA.RA08
