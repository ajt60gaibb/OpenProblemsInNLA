import NLA.Proofs.SP14.EndpointExtensionPositive
import Mathlib.Data.Nat.Choose.Central

/-!
The exact absolute endpoint-extension kernel and a central-binomial decay
bound. Infinite Schur sums and Sobolev operator bounds remain separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- Positive coefficients of the inverse endpoint square-root series. -/
noncomputable def endpointCentralCoeff (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * baseInverseCoeff n

theorem endpointCentralCoeff_zero : endpointCentralCoeff 0 = 1 := by
  simp [endpointCentralCoeff, baseInverseCoeff]

private theorem inverseCoeff_recurrence (n : ℕ) :
    (n + 1 : ℝ) * baseInverseCoeff (n + 1) =
      (-(1 / 2 : ℝ) - n) * baseInverseCoeff n := by
  have h := Ring.choose_smul_choose (r := (-1 / 2 : ℝ))
    (n := n + 1) (k := n) (Nat.le_succ n)
  simp [Nat.choose_succ_self_right, nsmul_eq_mul] at h
  dsimp [baseInverseCoeff]
  convert h using 1 <;> ring

theorem endpointCentralCoeff_recurrence (n : ℕ) :
    endpointCentralCoeff (n + 1) =
      ((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ) *
        endpointCentralCoeff n := by
  have h := inverseCoeff_recurrence n
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  unfold endpointCentralCoeff
  rw [pow_succ]
  push_cast at h ⊢
  field_simp
  nlinarith [h]

theorem endpointCentralCoeff_pos (n : ℕ) :
    0 < endpointCentralCoeff n := by
  induction n with
  | zero => simp [endpointCentralCoeff_zero]
  | succ n ih =>
      rw [endpointCentralCoeff_recurrence]
      positivity

theorem endpointCentralCoeff_eq_centralBinom (n : ℕ) :
    endpointCentralCoeff n =
      (Nat.centralBinom n : ℝ) / (4 : ℝ) ^ n := by
  induction n with
  | zero => simp [endpointCentralCoeff_zero, Nat.centralBinom]
  | succ n ih =>
      rw [endpointCentralCoeff_recurrence, ih, pow_succ]
      have hnat := Nat.succ_mul_centralBinom_succ n
      have hcast :
          ((n + 1 : ℕ) : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
            2 * ((2 * n + 1 : ℕ) : ℝ) * (Nat.centralBinom n : ℝ) := by
        exact_mod_cast hnat
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hp : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
      push_cast at hcast ⊢
      field_simp
      nlinarith [hcast]

theorem endpointCentralCoeff_sq_bound (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * endpointCentralCoeff n ^ 2 ≤ 1 := by
  induction n with
  | zero => simp [endpointCentralCoeff_zero]
  | succ n ih =>
      rw [endpointCentralCoeff_recurrence]
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have hn2 : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      have hA : endpointCentralCoeff n ^ 2 ≤
          1 / ((n + 1 : ℕ) : ℝ) := (le_div_iff₀ hn).2 (by nlinarith [ih])
      have hr :
          (((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) ^ 2 *
              endpointCentralCoeff n ^ 2 ≤
          (((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) ^ 2 *
              (1 / ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg _)
      have hratio :
          ((n + 2 : ℕ) : ℝ) *
            ((((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) ^ 2 *
              (1 / ((n + 1 : ℕ) : ℝ))) ≤ 1 := by
        push_cast
        field_simp
        nlinarith
      push_cast
      calc
        _ = ((n + 2 : ℕ) : ℝ) *
            ((((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) ^ 2 *
              endpointCentralCoeff n ^ 2) := by
          push_cast
          ring
        _ ≤ ((n + 2 : ℕ) : ℝ) *
            ((((2 * n + 1 : ℕ) : ℝ) / ((2 * n + 2 : ℕ) : ℝ)) ^ 2 *
              (1 / ((n + 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hr hn2.le
        _ ≤ 1 := hratio

theorem endpointCentralCoeff_le_sqrt (n : ℕ) :
    endpointCentralCoeff n ≤ 1 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hs : 0 < Real.sqrt (((n + 1 : ℕ) : ℝ)) := Real.sqrt_pos.2 hn
  have hsq : Real.sqrt (((n + 1 : ℕ) : ℝ)) ^ 2 =
      (((n + 1 : ℕ) : ℝ)) := Real.sq_sqrt hn.le
  have hA := endpointCentralCoeff_sq_bound n
  have hprod : (endpointCentralCoeff n *
      Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 ≤ 1 := by
    nlinarith [hA]
  have hle : endpointCentralCoeff n *
      Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤ 1 := by
    have hp := endpointCentralCoeff_pos n
    nlinarith [hprod]
  exact (le_div_iff₀ hs).2 hle

private theorem endpointCentralCoeff_sign (n : ℕ) :
    baseInverseCoeff n = (-1 : ℝ) ^ n * endpointCentralCoeff n := by
  unfold endpointCentralCoeff
  have hsign : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    calc
      ((-1 : ℝ) ^ n) ^ 2 = (-1 : ℝ) ^ (2 * n) := by
        rw [← pow_mul]
        congr 1
        omega
      _ = ((-1 : ℝ) ^ 2) ^ n := pow_mul (-1 : ℝ) 2 n
      _ = 1 := by norm_num
  calc
    baseInverseCoeff n = 1 * baseInverseCoeff n := by ring
    _ = ((-1 : ℝ) ^ n) ^ 2 * baseInverseCoeff n := by rw [hsign]
    _ = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * baseInverseCoeff n) := by ring

/-- Absolute value of the actual negative Fourier coefficient, for j≥1. -/
noncomputable def endpointKernelAbs (j k : ℕ) : ℝ :=
  ‖FourierCoefficient
      (fun z => endpointBaseSymbol z * endpointInverseMonomial k z)
      (-(j : ℤ))‖

theorem endpointKernelAbs_eq (k j : ℕ) (hj : 1 ≤ j) :
    endpointKernelAbs j k =
      ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
        endpointCentralCoeff k * endpointCentralCoeff (j - 1) := by
  have hden : (0 : ℝ) < ((k + j : ℕ) : ℝ) := by positivity
  have hnum : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
  rw [endpointKernelAbs, endpointExtension_fourier_neg k j hj]
  have hcast :
      (((k : ℂ) + 1 / 2) / ((k : ℂ) + (j : ℂ)) *
          (baseInverseCoeff k : ℂ) * (baseInverseCoeff (j - 1) : ℂ)) =
        ((((k : ℝ) + 1 / 2) / ((k : ℝ) + (j : ℝ)) *
          baseInverseCoeff k * baseInverseCoeff (j - 1) : ℝ) : ℂ) := by
    push_cast
    ring
  push_cast at ⊢
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [endpointCentralCoeff_sign k, endpointCentralCoeff_sign (j - 1)]
  have hratio : 0 ≤ ((k : ℝ) + 1 / 2) / ((k : ℝ) + (j : ℝ)) := by
    apply div_nonneg hnum.le
    simpa only [Nat.cast_add] using hden.le
  simp only [abs_mul, abs_pow, abs_neg, abs_one,
    abs_of_nonneg hratio,
    abs_of_pos (endpointCentralCoeff_pos k),
    abs_of_pos (endpointCentralCoeff_pos (j - 1))]
  ring

theorem endpointKernelAbs_le (k j : ℕ) (hj : 1 ≤ j) :
    endpointKernelAbs j k ≤
      ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) *
        (1 / Real.sqrt (((k + 1 : ℕ) : ℝ))) *
        (1 / Real.sqrt (j : ℝ)) := by
  rw [endpointKernelAbs_eq k j hj]
  have hj' : j - 1 + 1 = j := by omega
  have hA := endpointCentralCoeff_le_sqrt k
  have hB := endpointCentralCoeff_le_sqrt (j - 1)
  rw [hj'] at hB
  have hratio : (0 : ℝ) ≤
      ((k : ℝ) + 1 / 2) / ((k + j : ℕ) : ℝ) := by positivity
  have hApos := (endpointCentralCoeff_pos k).le
  have hBpos := (endpointCentralCoeff_pos (j - 1)).le
  gcongr

#assert_trust kernel endpointCentralCoeff_eq_centralBinom
#assert_trust kernel endpointCentralCoeff_sq_bound
#assert_trust kernel endpointCentralCoeff_le_sqrt
#assert_trust kernel endpointKernelAbs_eq
#assert_trust kernel endpointKernelAbs_le
#print axioms endpointKernelAbs_le

end NLA.Proofs.SP14
