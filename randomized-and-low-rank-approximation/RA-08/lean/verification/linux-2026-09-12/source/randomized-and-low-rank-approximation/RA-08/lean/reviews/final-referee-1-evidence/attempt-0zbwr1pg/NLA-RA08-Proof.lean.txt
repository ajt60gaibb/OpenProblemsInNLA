/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Full RA-08 counterexample from the reviewed source witness and the actual
ordered spectral/CFC/Euclidean-norm semantics. The mathematical source is
Matthew J. Colbrook; formalization affiliation is the Department of Computing
and Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA.
-/
import NLA.RA08.Tails
import NLA.RA08.Certificate
import NLA.RA08.Functional
import NLA.RA08.Numerical
import NLA.RA08.OrderedExistence

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08

theorem witness_functional_rayleigh_lower :
    26 * witnessT * (1 + witnessGap) ≤
      witnessVector ⬝ᵥ ((functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) *ᵥ witnessVector) := by
  have h := minorant_functional_calculus_proved.2
  change (functionalCalculus witnessFunction witnessMatrix - minorantMatrix witnessMatrix).PosSemidef at h
  have hq := h.dotProduct_mulVec_nonneg witnessVector
  have hc := witness_minorant_quadratic
  simp only [star_trivial, sub_mulVec, dotProduct_sub] at hq hc ⊢
  linarith

theorem counterexample_proved
    (dA : OrderedSpectralData witnessMatrix)
    (dAhat : OrderedSpectralData witnessApproximation) :
    spectralNorm (witnessMatrix - truncation dAhat 3) ≤
      spectralNorm (witnessMatrix - truncation dA 3) ∧
    ¬ (spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionTruncation dAhat witnessFunction 3) ≤
        spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionTruncation dA witnessFunction 3)) := by
  obtain ⟨hres, _hEig, htr, hftr, hta, htf⟩ := witness_tail_data_proved dA dAhat
  constructor
  · rw [htr, hres, hta]
  · intro hbad
    rw [hftr, htf] at hbad
    have hq := operator_rayleigh_bound_proved
      (functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) witnessVector
    rw [witness_vector_length] at hq
    have hu := mul_le_mul_of_nonneg_right hbad (by norm_num : (0 : ℝ) ≤ 26)
    have hl := witness_functional_rayleigh_lower
    have ha := le_abs_self (witnessVector ⬝ᵥ
      ((functionalCalculus witnessFunction witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) *ᵥ witnessVector))
    have hg := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 26) witnessT_pos)
      numerical_gap_positive_proved
    nlinarith

theorem not_concaveSpectralTransferConjecture_proved : ¬ ConcaveSpectralTransferConjecture := by
  intro h
  obtain ⟨dA⟩ := orderedSpectral_exists_proved witnessMatrix witnessMatrix_psd
  obtain ⟨dAhat⟩ := orderedSpectral_exists_proved witnessApproximation witnessApproximation_psd
  have hc := counterexample_proved dA dAhat
  have hp := h 6 (by decide) 3 (by decide) (by decide) witnessMatrix witnessApproximation
    witnessMatrix_psd witnessApproximation_psd witness_order witnessFunction
    witnessFunction_admissible dA dAhat 0 le_rfl
  apply hc.2
  simpa only [add_zero, one_mul] using hp (by simpa only [add_zero, one_mul] using hc.1)

#assert_trust kernel witness_functional_rayleigh_lower
#assert_trust kernel counterexample_proved
#assert_trust kernel not_concaveSpectralTransferConjecture_proved
#print axioms witness_functional_rayleigh_lower
#print axioms counterexample_proved
#print axioms not_concaveSpectralTransferConjecture_proved

end NLA.RA08
