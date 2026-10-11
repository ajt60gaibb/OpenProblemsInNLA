import NLA.Proofs.SP14.BaseFourierMode

/-!
The positive Laurent packet from the SP-14 source has frequencies strictly
above the diagonals of its matching odd Toeplitz section. The background
symbol is continuous so that the frozen interval-integral Fourier coefficient
is additive without any totalization issue.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- The source packet `τ s^m (1+s)` in the symbol `a(z)=z g(z²)`. -/
noncomputable def positivePacket (τ : ℂ) (m : ℕ) (z : Circle) : ℂ :=
  τ * ((z : ℂ) ^ (2 * m + 1) + (z : ℂ) ^ (2 * m + 3))

private theorem continuous_circle_nat_mode (r : ℕ) :
    Continuous (fun z : Circle => (z : ℂ) ^ r) := by
  fun_prop

private theorem continuous_positivePacket (τ : ℂ) (m : ℕ) :
    Continuous (positivePacket τ m) := by
  unfold positivePacket
  fun_prop

private theorem FourierCoefficient_add_of_continuous
    (a b : Circle → ℂ) (ha : Continuous a) (hb : Continuous b) (k : ℤ) :
    FourierCoefficient (fun z => a z + b z) k =
      FourierCoefficient a k + FourierCoefficient b k := by
  have hca : Continuous (fun t : ℝ =>
      a (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcb : Continuous (fun t : ℝ =>
      b (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hca.intervalIntegrable 0 (2 * Real.pi))
    (hcb.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem FourierCoefficient_const_mul (c : ℂ) (b : Circle → ℂ) (k : ℤ) :
    FourierCoefficient (fun z => c * b z) k = c * FourierCoefficient b k := by
  unfold FourierCoefficient
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

private theorem FourierCoefficient_nat_mode (r : ℕ) (k : ℤ) :
    FourierCoefficient (fun z : Circle => (z : ℂ) ^ r) k =
      if (r : ℤ) = k then 1 else 0 := by
  convert FourierCoefficient_circle_mode (r : ℤ) k using 1
  simp

/-- Exact Fourier support of the positive packet under the frozen sign and
real-interval normalization. -/
theorem positivePacket_fourier (τ : ℂ) (m : ℕ) (k : ℤ) :
    FourierCoefficient (positivePacket τ m) k =
      τ * (if (((2 * m + 1 : ℕ) : ℤ) = k) then 1 else 0) +
      τ * (if (((2 * m + 3 : ℕ) : ℤ) = k) then 1 else 0) := by
  have hpacket : positivePacket τ m =
      fun z : Circle => τ * (z : ℂ) ^ (2 * m + 1) + τ * (z : ℂ) ^ (2 * m + 3) := by
    funext z
    simp [positivePacket, mul_add]
  rw [hpacket]
  rw [FourierCoefficient_add_of_continuous
    (fun z => τ * (z : ℂ) ^ (2 * m + 1))
    (fun z => τ * (z : ℂ) ^ (2 * m + 3))
    (by fun_prop) (by fun_prop) k]
  rw [FourierCoefficient_const_mul, FourierCoefficient_const_mul]
  rw [FourierCoefficient_nat_mode, FourierCoefficient_nat_mode]

/-- Adding the positive packet changes no entry of a Toeplitz section up to
and including its matching odd order. -/
theorem toeplitz_add_positivePacket_invisible (a : Circle → ℂ)
    (ha : Continuous a) (τ : ℂ) (m n : ℕ) (hn : n ≤ 2 * m + 1) :
    Toeplitz (fun z => a z + positivePacket τ m z) n = Toeplitz a n := by
  ext i j
  change FourierCoefficient (fun z => a z + positivePacket τ m z)
      ((i.val : ℤ) - (j.val : ℤ)) =
    FourierCoefficient a ((i.val : ℤ) - (j.val : ℤ))
  rw [FourierCoefficient_add_of_continuous a (positivePacket τ m)
    ha (continuous_positivePacket τ m)]
  rw [positivePacket_fourier]
  have hmode1 : ((2 * m + 1 : ℕ) : ℤ) ≠ (i.val : ℤ) - (j.val : ℤ) := by
    have hi := i.isLt
    omega
  have hmode2 : ((2 * m + 3 : ℕ) : ℤ) ≠ (i.val : ℤ) - (j.val : ℤ) := by
    have hi := i.isLt
    omega
  have hmode1' : 2 * (m : ℤ) + 1 ≠ (i.val : ℤ) - (j.val : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hmode1
  have hmode2' : 2 * (m : ℤ) + 3 ≠ (i.val : ℤ) - (j.val : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hmode2
  simp [hmode1', hmode2']

#assert_trust kernel positivePacket_fourier
#assert_trust kernel toeplitz_add_positivePacket_invisible
#print axioms positivePacket_fourier
#print axioms toeplitz_add_positivePacket_invisible

end NLA.Proofs.SP14
