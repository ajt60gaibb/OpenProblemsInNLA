import NLA.Proofs.SP14.WienerAdd

/-!
Multiplication by the actual positive circle mode s costs exactly the
weight 2^(9/8) in the literal Wiener norm.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private def unitPositiveCoeff : Fin 1 → ℝ := fun _ => 1

private theorem positiveLaurent_unit (s : Circle) :
    positiveLaurent 1 unitPositiveCoeff s = (s : ℂ) := by
  simp [positiveLaurent, unitPositiveCoeff]

private theorem finitePositiveWienerSize_unit :
    finitePositiveWienerSize 1 unitPositiveCoeff =
      (2 : ℝ) ^ (9 / 8 : ℝ) := by
  simp [finitePositiveWienerSize, unitPositiveCoeff, wienerWeight]
  norm_num

theorem summable_wiener_mul_s
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖)) :
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient (fun s : Circle => (s : ℂ) * f s) k‖) := by
  have hfun : (fun s : Circle => (s : ℂ) * f s) =
      (fun s => f s * positiveLaurent 1 unitPositiveCoeff s) := by
    funext s
    rw [positiveLaurent_unit]
    ring
  rw [hfun]
  exact summable_mul_positiveLaurent_wiener f hf hfs 1 unitPositiveCoeff

theorem weightedWienerSize_mul_s_le
    (f : Circle → ℂ) (hf : Continuous f)
    (hfs : Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient f k‖)) :
    weightedWienerSize (fun s : Circle => (s : ℂ) * f s) ≤
      (2 : ℝ) ^ (9 / 8 : ℝ) * weightedWienerSize f := by
  have hfun : (fun s : Circle => (s : ℂ) * f s) =
      (fun s => f s * positiveLaurent 1 unitPositiveCoeff s) := by
    funext s
    rw [positiveLaurent_unit]
    ring
  rw [hfun]
  have h := weightedWienerSize_mul_positiveLaurent_le
    f hf hfs 1 unitPositiveCoeff
  rw [finitePositiveWienerSize_unit] at h
  convert h using 1
  ring

#assert_trust kernel summable_wiener_mul_s
#assert_trust kernel weightedWienerSize_mul_s_le

end NLA.Proofs.SP14
