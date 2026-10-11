import NLA.Proofs.SP14.BaseJetBinomialInverse
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
The canonical finite partial convolution underlying the negative-frequency
kernel of the square-root endpoint extension. Analytic matrix/Sobolev bounds
remain separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem baseInverseCoeff_recurrence (n : ℕ) :
    (n + 1 : ℝ) * baseInverseCoeff (n + 1) =
      (-(1 / 2 : ℝ) - n) * baseInverseCoeff n := by
  have h := Ring.choose_smul_choose (r := (-1 / 2 : ℝ))
    (n := n + 1) (k := n) (Nat.le_succ n)
  simp [Nat.choose_succ_self_right, Ring.choose_one_right,
    nsmul_eq_mul] at h
  dsimp [baseInverseCoeff]
  convert h using 1 <;> ring

private theorem baseCoeffReal_derivative_coeff (n : ℕ) :
    (n + 1 : ℝ) * baseCoeffReal (n + 1) =
      (1 / 2 : ℝ) * baseInverseCoeff n := by
  have h := Ring.choose_smul_choose (r := (1 / 2 : ℝ))
    (n := n + 1) (k := 1) (by omega : 1 ≤ n + 1)
  simp [Nat.choose_one_right, nsmul_eq_mul] at h
  dsimp [baseCoeffReal, baseInverseCoeff]
  convert h using 1 <;> ring

private theorem endpointBinomial_derivative :
    PowerSeries.derivative ℝ (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ)) =
      PowerSeries.C (1 / 2 : ℝ) *
        PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) := by
  ext n
  rw [PowerSeries.coeff_derivative, PowerSeries.binomialSeries_coeff]
  rw [mul_comm (PowerSeries.C (1 / 2 : ℝ)),
    PowerSeries.coeff_mul_C, PowerSeries.binomialSeries_coeff]
  simpa only [smul_eq_mul, mul_one, one_mul, baseCoeffReal, baseInverseCoeff,
    mul_comm] using (baseCoeffReal_derivative_coeff n)

private theorem endpointBinomial_factor :
    PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) =
      (1 + PowerSeries.X) * PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) := by
  calc
    PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) =
        PowerSeries.binomialSeries ℝ ((-1 / 2 : ℝ) + 1) := by
      congr 1
      ring
    _ = PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) *
          PowerSeries.binomialSeries ℝ (1 : ℝ) := by
      rw [PowerSeries.binomialSeries_add]
    _ = _ := by
      have hOne : PowerSeries.binomialSeries ℝ (1 : ℝ) =
          1 + PowerSeries.X := by
        simpa using (PowerSeries.binomialSeries_nat (R := ℝ) (A := ℝ) 1)
      rw [hOne]
      ring

private noncomputable def endpointTrunc (k : ℕ) : Polynomial ℝ :=
  ∑ l ∈ Finset.range (k + 1),
    Polynomial.C (baseInverseCoeff l) * Polynomial.X ^ l

private theorem endpointTrunc_succ (k : ℕ) :
    endpointTrunc (k + 1) = endpointTrunc k +
      Polynomial.C (baseInverseCoeff (k + 1)) * Polynomial.X ^ (k + 1) := by
  simp [endpointTrunc, Finset.sum_range_succ]

private theorem endpointTrunc_derivative (k : ℕ) :
    ((1 : Polynomial ℝ) + Polynomial.X) * (endpointTrunc k).derivative +
      Polynomial.C (1 / 2 : ℝ) * endpointTrunc k =
    Polynomial.C (((k : ℝ) + 1 / 2) * baseInverseCoeff k) *
      Polynomial.X ^ k := by
  induction k with
  | zero =>
      simp [endpointTrunc, baseInverseCoeff]
  | succ k ih =>
      rw [endpointTrunc_succ]
      simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
        mul_add]
      have hrec := baseInverseCoeff_recurrence k
      have hzero :
          ((k : ℝ) + 1 / 2) * baseInverseCoeff k +
            ((k : ℝ) + 1) * baseInverseCoeff (k + 1) = 0 := by
        nlinarith [hrec]
      calc
        _ = ((1 + Polynomial.X) * (endpointTrunc k).derivative +
                Polynomial.C (1 / 2 : ℝ) * endpointTrunc k) +
              (Polynomial.C (((k : ℝ) + 1) * baseInverseCoeff (k + 1)) *
                  Polynomial.X ^ k +
                Polynomial.C (((k : ℝ) + 3 / 2) * baseInverseCoeff (k + 1)) *
                  Polynomial.X ^ (k + 1)) := by
          rw [show k + 1 - 1 = k by omega]
          simp only [Polynomial.C_mul]
          push_cast
          have hc :
              Polynomial.C ((k : ℝ) + 3 / 2) =
                Polynomial.C ((k : ℝ) + 1) + Polynomial.C (1 / 2 : ℝ) := by
            rw [← Polynomial.C_add]
            congr 1
            ring
          rw [hc]
          ring
        _ = Polynomial.C
              (((k : ℝ) + 1 / 2) * baseInverseCoeff k +
                ((k : ℝ) + 1) * baseInverseCoeff (k + 1)) * Polynomial.X ^ k +
            Polynomial.C
              (((k : ℝ) + 3 / 2) * baseInverseCoeff (k + 1)) *
                Polynomial.X ^ (k + 1) := by
          rw [ih, Polynomial.C_add]
          ring
        _ = _ := by
          rw [hzero]
          simp
          have hc : Polynomial.C (3 / 2 : ℝ) =
              (1 : Polynomial ℝ) + Polynomial.C (1 / 2 : ℝ) := by
            rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
              Polynomial.C_add]
            simp
          rw [hc]
          simp [add_assoc]

private theorem endpointTrunc_derivative_series (k : ℕ) :
    (1 + PowerSeries.X) *
        PowerSeries.derivative ℝ (endpointTrunc k : PowerSeries ℝ) +
      PowerSeries.C (1 / 2 : ℝ) * (endpointTrunc k : PowerSeries ℝ) =
    PowerSeries.C (((k : ℝ) + 1 / 2) * baseInverseCoeff k) *
      PowerSeries.X ^ k := by
  have h := congrArg (fun p : Polynomial ℝ => (p : PowerSeries ℝ))
    (endpointTrunc_derivative k)
  simpa only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_pow,
    PowerSeries.derivative_coe] using h

private theorem endpointBinomial_trunc_derivative (k : ℕ) :
    PowerSeries.derivative ℝ
        (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) *
          (endpointTrunc k : PowerSeries ℝ)) =
      PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) *
        (PowerSeries.C (((k : ℝ) + 1 / 2) * baseInverseCoeff k) *
          PowerSeries.X ^ k) := by
  let A := PowerSeries.binomialSeries ℝ (1 / 2 : ℝ)
  let B := PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ)
  let T : PowerSeries ℝ := endpointTrunc k
  have hder := endpointTrunc_derivative_series k
  have hA := endpointBinomial_derivative
  have hfactor := endpointBinomial_factor
  change PowerSeries.derivative ℝ (A * T) = _
  rw [(PowerSeries.derivative ℝ).leibniz A T]
  simp only [smul_eq_mul]
  dsimp [A, B, T] at *
  rw [hA, hfactor]
  calc
    _ = PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) *
        ((1 + PowerSeries.X) * PowerSeries.derivative ℝ (endpointTrunc k : PowerSeries ℝ) +
          PowerSeries.C (1 / 2 : ℝ) * (endpointTrunc k : PowerSeries ℝ)) := by ring
    _ = _ := by rw [hder]

private theorem endpointTrunc_product_coeff (k j : ℕ) :
    PowerSeries.coeff (k + j)
        (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) *
          (endpointTrunc k : PowerSeries ℝ)) =
      ∑ d ∈ Finset.range (k + 1),
        baseCoeffReal (d + j) * baseInverseCoeff (k - d) := by
  let A := PowerSeries.binomialSeries ℝ (1 / 2 : ℝ)
  have hterm (l : ℕ) (hl : l ∈ Finset.range (k + 1)) :
      PowerSeries.coeff (k + j)
          (A * (PowerSeries.C (baseInverseCoeff l) * PowerSeries.X ^ l)) =
        baseCoeffReal (k + j - l) * baseInverseCoeff l := by
    have hle : l ≤ k + j := by
      have := Finset.mem_range.mp hl
      omega
    rw [← mul_assoc, PowerSeries.coeff_mul_X_pow', if_pos hle,
      PowerSeries.coeff_mul_C, PowerSeries.binomialSeries_coeff]
    simp [baseCoeffReal]
  calc
    PowerSeries.coeff (k + j) (A * (endpointTrunc k : PowerSeries ℝ)) =
        ∑ l ∈ Finset.range (k + 1),
          baseCoeffReal (k + j - l) * baseInverseCoeff l := by
      have hcast : (endpointTrunc k : PowerSeries ℝ) =
          ∑ l ∈ Finset.range (k + 1),
            PowerSeries.C (baseInverseCoeff l) * PowerSeries.X ^ l := by
        calc
          (endpointTrunc k : PowerSeries ℝ) =
              Polynomial.coeToPowerSeries.ringHom (endpointTrunc k) := rfl
          _ = ∑ l ∈ Finset.range (k + 1),
                Polynomial.coeToPowerSeries.ringHom
                  (Polynomial.C (baseInverseCoeff l) * Polynomial.X ^ l) := by
              simp only [endpointTrunc, map_sum]
          _ = _ := by simp
      rw [hcast, Finset.mul_sum]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l hl
    _ = ∑ d ∈ Finset.range (k + 1),
          baseCoeffReal (k + j - (k - d)) * baseInverseCoeff (k - d) := by
      rw [← Finset.sum_range_reflect]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdk : d ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
      have heq : k + j - (k - d) = d + j := by omega
      rw [heq]

private theorem endpointBinomial_rhs_coeff (k j : ℕ) (hj : 1 ≤ j) :
    PowerSeries.coeff (k + j - 1)
        (PowerSeries.binomialSeries ℝ (-1 / 2 : ℝ) *
          (PowerSeries.C (((k : ℝ) + 1 / 2) * baseInverseCoeff k) *
            PowerSeries.X ^ k)) =
      ((k : ℝ) + 1 / 2) * baseInverseCoeff k *
        baseInverseCoeff (j - 1) := by
  have hk : k ≤ k + j - 1 := by omega
  rw [← mul_assoc, PowerSeries.coeff_mul_X_pow', if_pos hk,
    PowerSeries.coeff_mul_C, PowerSeries.binomialSeries_coeff]
  have heq : k + j - 1 - k = j - 1 := by omega
  rw [heq]
  simp only [baseInverseCoeff]
  ring

/-- The exact finite partial convolution in the canonical endpoint projection. -/
theorem baseEndpoint_partialConvolution (k j : ℕ) (hj : 1 ≤ j) :
    (∑ d ∈ Finset.range (k + 1),
      baseCoeffReal (d + j) * baseInverseCoeff (k - d)) =
      ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
        baseInverseCoeff k * baseInverseCoeff (j - 1) := by
  have hcoeff := congrArg (PowerSeries.coeff (k + j - 1))
    (endpointBinomial_trunc_derivative k)
  rw [PowerSeries.coeff_derivative] at hcoeff
  have hindex : k + j - 1 + 1 = k + j := by omega
  rw [hindex, endpointTrunc_product_coeff,
    endpointBinomial_rhs_coeff k j hj] at hcoeff
  have hpos : (0 : ℝ) < ((k + j : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + j)
  rw [show ((k + j - 1 : ℕ) : ℝ) + 1 = ((k + j : ℕ) : ℝ) by
    exact_mod_cast hindex] at hcoeff
  field_simp
  nlinarith [hcoeff]

#assert_trust kernel baseEndpoint_partialConvolution

end NLA.Proofs.SP14
