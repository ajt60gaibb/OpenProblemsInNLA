/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical counterexample: Matthew J. Colbrook. This helper applies the
actual matrix Cayley–Hamilton theorem to the reviewed twelfth-power formula.
-/
import NLA.MF16.Definitions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF16
open Polynomial

/-- Exact polynomial division by the degree-two characteristic polynomial.
Only scalar polynomial algebra is expanded, never the entries of a matrix power. -/
private theorem twelfth_polynomial_remainder (s : ℝ) :
    ∃ q : ℝ[X], X^12 =
      C (linearCoefficient s) * X - C (identityCoefficient s) +
        (X^2 - C s * X + C 3) * q := by
  refine ⟨X^10 + C s * X^9 + ((C s)^2 - 3) * X^8 +
    ((C s)^3 - 6 * C s) * X^7 +
    ((C s)^4 - 9 * (C s)^2 + 9) * X^6 +
    ((C s)^5 - 12 * (C s)^3 + 27 * C s) * X^5 +
    ((C s)^6 - 15 * (C s)^4 + 54 * (C s)^2 - 27) * X^4 +
    ((C s)^7 - 18 * (C s)^5 + 90 * (C s)^3 - 108 * C s) * X^3 +
    ((C s)^8 - 21 * (C s)^6 + 135 * (C s)^4 - 270 * (C s)^2 + 81) * X^2 +
    ((C s)^9 - 24 * (C s)^7 + 189 * (C s)^5 - 540 * (C s)^3 + 405 * C s) * X +
    ((C s)^10 - 27 * (C s)^8 + 252 * (C s)^6 - 945 * (C s)^4 +
      1215 * (C s)^2 - 243), ?_⟩
  simp only [linearCoefficient, identityCoefficient, map_mul, map_sub, map_add,
    map_ofNat]
  ring

/-- The actual matrix power formula holds for every real two-by-two matrix
with determinant three, without a symmetry or diagonalization assumption. -/
theorem matrix_twelfth_power_of_det_three (S : RealMatrix) (hdet : S.det = 3) :
    S^12 = linearCoefficient (Matrix.trace S) • S -
      identityCoefficient (Matrix.trace S) • (1 : RealMatrix) := by
  have hchar : aeval S (X^2 - C (Matrix.trace S) * X + C (3 : ℝ)) = 0 := by
    simpa [Matrix.charpoly_fin_two, hdet] using Matrix.aeval_self_charpoly S
  obtain ⟨q, hq⟩ := twelfth_polynomial_remainder (Matrix.trace S)
  have he := congrArg (aeval S) hq
  rw [map_add, map_mul, hchar, zero_mul, add_zero] at he
  simpa only [map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using he

/-- Exactly the frozen MF-16 twelfth-power reduction contract. -/
theorem twelfth_power_reduction_proved (v : Fin 3 → ℝ)
    (hdet : (symmetricMatrix v).det = 3) :
    (symmetricMatrix v)^12 =
      linearCoefficient (Matrix.trace (symmetricMatrix v)) • symmetricMatrix v -
      identityCoefficient (Matrix.trace (symmetricMatrix v)) • (1 : RealMatrix) :=
  matrix_twelfth_power_of_det_three (symmetricMatrix v) hdet

#assert_trust kernel twelfth_polynomial_remainder
#assert_trust kernel matrix_twelfth_power_of_det_three
#assert_trust kernel twelfth_power_reduction_proved
#print axioms twelfth_polynomial_remainder
#print axioms matrix_twelfth_power_of_det_three
#print axioms twelfth_power_reduction_proved

end NLA.MF16
