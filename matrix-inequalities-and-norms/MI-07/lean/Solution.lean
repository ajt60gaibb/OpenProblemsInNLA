/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-07.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA.

All seven statements below are copied from the independently reviewed challenge.
Their proofs use the genuine complex matrix modulus and root-sequence limits.
-/
import NLA.MI07.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped ComplexOrder MatrixOrder Topology

namespace NLA.MI07

/-- The modulus is the genuine positive square root, for every complex matrix. -/
theorem modulus_eq_sqrt {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModulus X = CFC.sqrt (X.conjTranspose * X) ∧
    (matrixModulus X).PosSemidef := by
  exact modulus_eq_sqrt_proved X

/-- A proved convergence identifies the actual limit; no default is presumed. -/
theorem maximalModulus_eq_of_tendsto {n : ℕ}
    (X L : Matrix (Fin n) (Fin n) ℂ)
    (h : Filter.Tendsto (rootSequence X) Filter.atTop (𝓝 L)) :
    maximalModulus X = L := by
  exact maximalModulus_eq_of_tendsto_proved X L h

/-- The finite-dimensional limit is equivalently convergence in the actual spectral norm. -/
theorem root_limit_iff_spectralNorm {n : ℕ} (X L : Matrix (Fin n) (Fin n) ℂ) :
    Filter.Tendsto (rootSequence X) Filter.atTop (𝓝 L) ↔
    Filter.Tendsto (fun r => spectralNorm (rootSequence X r - L))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  exact root_limit_iff_spectralNorm_proved X L

/-- All finite polar identities and positivity facts are conclusions. -/
theorem witness_moduli :
    witnessA.PosSemidef ∧ directionProjector.PosSemidef ∧ spanningSum.PosDef ∧
    witnessA ^ (2 : ℕ) = witnessA ∧
    directionProjector ^ (2 : ℕ) = directionProjector ∧
    matrixModulus witnessA = witnessA ∧
    matrixModulus witnessA.conjTranspose = witnessA ∧
    matrixModulus witnessB = (5 / 12 : ℂ) • (1 - witnessA) ∧
    matrixModulus witnessB.conjTranspose = (5 / 12 : ℂ) • witnessA ∧
    matrixModulus (witnessA + witnessB) = (13 / 12 : ℂ) • directionProjector ∧
    matrixModulus (witnessA + witnessB).conjTranspose = (13 / 12 : ℂ) • witnessA := by
  exact witness_moduli_proved

/-- The actual CFC sequences converge at every matrix used in the counterexample. -/
theorem witness_root_limits :
    Filter.Tendsto (rootSequence witnessA) Filter.atTop (𝓝 witnessA) ∧
    Filter.Tendsto (rootSequence witnessB) Filter.atTop (𝓝 ((5 / 12 : ℂ) • 1)) ∧
    Filter.Tendsto (rootSequence (witnessA + witnessB)) Filter.atTop
      (𝓝 ((13 / 12 : ℂ) • 1)) := by
  exact witness_root_limits_proved

/-- Actual maximal moduli and all-unitary trace obstruction to ordinary PSD domination. -/
theorem counterexample :
    maximalModulus witnessA = witnessA ∧
    maximalModulus witnessB = (5 / 12 : ℂ) • 1 ∧
    maximalModulus (witnessA + witnessB) = (13 / 12 : ℂ) • 1 ∧
    (maximalModulus (witnessA + witnessB)).trace = (13 / 6 : ℂ) ∧
    ∀ U V : Matrix.unitaryGroup (Fin 2) ℂ,
      (unitaryConjugate U (maximalModulus witnessA) +
        unitaryConjugate V (maximalModulus witnessB)).trace = (11 / 6 : ℂ) ∧
      (unitaryConjugate U (maximalModulus witnessA) +
        unitaryConjugate V (maximalModulus witnessB) -
        maximalModulus (witnessA + witnessB)).trace = (-1 / 3 : ℂ) ∧
      ¬ (maximalModulus (witnessA + witnessB) ≤
        unitaryConjugate U (maximalModulus witnessA) +
        unitaryConjugate V (maximalModulus witnessB)) := by
  exact counterexample_proved

/-- The complete original universal constant-one assertion is false. -/
theorem not_triangleConjecture : ¬ TriangleConjecture := by
  exact not_triangleConjecture_proved

#assert_trust kernel modulus_eq_sqrt
#assert_trust kernel maximalModulus_eq_of_tendsto
#assert_trust kernel root_limit_iff_spectralNorm
#assert_trust kernel witness_moduli
#assert_trust kernel witness_root_limits
#assert_trust kernel counterexample
#assert_trust kernel not_triangleConjecture

#print axioms modulus_eq_sqrt
#print axioms maximalModulus_eq_of_tendsto
#print axioms root_limit_iff_spectralNorm
#print axioms witness_moduli
#print axioms witness_root_limits
#print axioms counterexample
#print axioms not_triangleConjecture

end NLA.MI07
