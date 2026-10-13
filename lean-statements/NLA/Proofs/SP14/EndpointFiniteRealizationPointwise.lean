import NLA.Proofs.SP14.EndpointFiniteFourierUniqueness
import NLA.Proofs.SP14.EndpointCircleFourier

/-!
The canonical finite endpoint extension agrees pointwise with the continuous
circle realization. This is the finite-input identity in the independently
reviewed source contract; no infinite inverse polynomial is asserted.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem continuous_endpointFiniteInverse
    (r : ℝ) (y : SobolevCoeff r) (N : ℕ) :
    Continuous (endpointFiniteInverse r y N) := by
  unfold endpointFiniteInverse
  apply continuous_finsetSum
  intro k hk
  apply continuous_const.mul
  unfold endpointInverseMonomial
  apply continuous_finsetSum
  intro l hl
  fun_prop

/-- For a finitely supported weighted input, the manuscript's finite inverse
polynomial gives the actual continuous endpoint extension at every point. -/
theorem endpointCircleRealization_eq_finiteInverse
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (N : ℕ)
    (hy : ∀ k : ℕ, N ≤ k → y k = 0) (z : Circle) :
    endpointCircleRealization r hrHalf hr1 y z =
      endpointBaseSymbol z * endpointFiniteInverse r y N z := by
  have hfinite : Continuous
      (fun z : Circle => endpointBaseSymbol z * endpointFiniteInverse r y N z) :=
    continuous_endpointBaseSymbol.mul (continuous_endpointFiniteInverse r y N)
  have hcoeff : ∀ p : ℤ,
      FourierCoefficient (endpointCircleRealization r hrHalf hr1 y) p =
        FourierCoefficient
          (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z) p := by
    intro p
    cases p with
    | ofNat k =>
        exact (endpointCircleRealization_fourier_nonneg r hrHalf hr1 y k).trans
          (endpointFiniteInverse_fourier_nonneg r y N hy k).symm
    | negSucc t =>
        exact (endpointCircleRealization_fourier_neg r hrHalf hr1 y t).trans
          (endpointFiniteInverse_fourier_neg r hrHalf hr1 y N hy t).symm
  have heq := continuous_eq_of_forall_FourierCoefficient_eq
    (endpointCircleRealization r hrHalf hr1 y)
    (fun z => endpointBaseSymbol z * endpointFiniteInverse r y N z)
    (continuous_endpointCircleRealization r hrHalf hr1 y)
    hfinite hcoeff
  exact congrFun heq z

#assert_trust kernel endpointCircleRealization_eq_finiteInverse
#print axioms endpointCircleRealization_eq_finiteInverse

end NLA.Proofs.SP14
