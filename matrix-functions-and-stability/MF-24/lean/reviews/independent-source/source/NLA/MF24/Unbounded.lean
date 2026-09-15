/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.FamilySpectrum
import NLA.MF24.Ratios
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

theorem arbitrarily_large_ratios (C : ℝ) (hC : 0 ≤ C) :
    ∃ m : ℕ, 2 ≤ m ∧
      SuperIdentical (matrixX m (m : ℝ)) (matrixY m (m : ℝ)) ∧
      polyEval (matrixY m (m : ℝ)) (testPolynomial m) ≠ 0 ∧
      C * spectralNorm (polyEval (matrixY m (m : ℝ)) (testPolynomial m)) <
        spectralNorm (polyEval (matrixX m (m : ℝ)) (testPolynomial m)) := by
  obtain ⟨m, hm, hY, hlarge⟩ := arbitrarily_large_norm_ratios C hC
  have ht : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  exact ⟨m, hm, family_super_identical m hm (m : ℝ) ht, hY, hlarge⟩

theorem no_uniform_comparison : ¬ UniformComparison := by
  rintro ⟨C, hC, hall⟩
  obtain ⟨m, hm, hSIP, _, hlarge⟩ := arbitrarily_large_ratios C hC.le
  have hbound := hall (dimension m) (dimension_pos m) (matrixX m (m : ℝ))
    (matrixY m (m : ℝ)) hSIP (testPolynomial m)
  exact not_lt_of_ge hbound hlarge

#assert_trust kernel arbitrarily_large_ratios
#assert_trust kernel no_uniform_comparison
#print axioms arbitrarily_large_ratios
#print axioms no_uniform_comparison

end NLA.MF24
