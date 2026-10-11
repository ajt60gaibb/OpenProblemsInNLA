import NLA.Statements.SP14
import Mathlib.RingTheory.PowerSeries.Binomial

/-!
The exact finite convolution of the exterior square-root branch coefficients
used by the SP-14 base Toeplitz symbol. This is one algebraic component of
the odd-order characteristic-polynomial identity; it does not identify any
Fourier integral or prove the final counterexample.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The complex coefficients of the branch `sqrt(1+x)` normalized to `1`
at `x=0`. -/
noncomputable def baseCoeff (k : ℕ) : ℂ := Ring.choose (1 / 2 : ℂ) k

/-- The formal square of the normalized square-root series is `1+X`. -/
theorem baseSeries_square :
    PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) *
      PowerSeries.binomialSeries ℂ (1 / 2 : ℂ) = 1 + PowerSeries.X := by
  rw [← PowerSeries.binomialSeries_add]
  convert (PowerSeries.binomialSeries_nat (A := ℂ) (R := ℂ) 1) using 1 <;> norm_num

/-- Exact coefficient convolution, including orders zero and one. -/
theorem baseCoeff_convolution (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, baseCoeff p.1 * baseCoeff p.2) =
      (if n = 0 then 1 else 0) + (if n = 1 then 1 else 0) := by
  have h := congrArg (PowerSeries.coeff n) baseSeries_square
  simpa [baseCoeff, PowerSeries.coeff_mul, PowerSeries.coeff_X,
    PowerSeries.coeff_one] using h

#assert_trust kernel baseSeries_square
#assert_trust kernel baseCoeff_convolution
#print axioms baseCoeff_convolution

end NLA.Proofs.SP14
