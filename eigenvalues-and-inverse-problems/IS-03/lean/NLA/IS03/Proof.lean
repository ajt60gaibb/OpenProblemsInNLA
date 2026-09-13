/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's IS-03 counterexample.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.IS03.Witness
import NLA.IS03.Spectral
import NLA.IS03.Newton
import NLA.IS03.Numerical

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.IS03

/-- The eigenbasis was derived for every B; the finite Newton theorem has no
distinctness premise. Together they identify every actual matrix-power trace. -/
theorem trace_moment_certificate_proved (B : RealMatrix 6)
    (hB : B.charpoly = derivativePolynomial) :
    ∀ i : Fin 7, Matrix.trace (B^(i.val + 1)) = traceMoments i := by
  obtain ⟨hprod, htrace⟩ := root_product_and_trace B hB
  have hs := power_sums_of_derivative_product (fun r : ComplexRoots => (r : ℂ))
    complexRoots_card hprod
  intro i
  apply Complex.ofReal_injective
  exact (htrace (i.val + 1)).trans (hs i)

/-- The retained kernel-certified negative moment contradicts nonnegative trace. -/
theorem counterexample_proved :
    EntrywiseNonnegative witnessMatrix ∧
    ∀ B : RealMatrix 6, EntrywiseNonnegative B →
      B.charpoly ≠ normalizedDerivative 7 witnessMatrix.charpoly := by
  refine ⟨witness_admissible_proved.1, ?_⟩
  intro B hB heq
  have hchar : B.charpoly = derivativePolynomial :=
    heq.trans witness_polynomials_proved.2.1
  have htrace : Matrix.trace (B^7) = traceMoments 6 :=
    trace_moment_certificate_proved B hchar 6
  have hnonnegative : 0 ≤ traceMoments 6 :=
    htrace ▸ (nonnegative_power_trace_proved B hB 7).2
  exact (not_lt_of_ge hnonnegative) negative_moment_proved.2

theorem not_derivativeRealizabilityConjecture_proved :
    ¬ DerivativeRealizabilityConjecture := by
  intro h
  obtain ⟨B, hB, heq⟩ := h 7 (by decide) witnessMatrix witness_admissible_proved.1
  exact counterexample_proved.2 B hB heq

#assert_trust kernel nonnegative_power_trace_proved
#assert_trust kernel witness_admissible_proved
#assert_trust kernel witness_polynomials_proved
#assert_trust kernel trace_moment_certificate_proved
#assert_trust kernel negative_moment_proved
#assert_trust kernel counterexample_proved
#assert_trust kernel not_derivativeRealizabilityConjecture_proved
#print axioms nonnegative_power_trace_proved
#print axioms witness_admissible_proved
#print axioms witness_polynomials_proved
#print axioms trace_moment_certificate_proved
#print axioms negative_moment_proved
#print axioms counterexample_proved
#print axioms not_derivativeRealizabilityConjecture_proved
end NLA.IS03
