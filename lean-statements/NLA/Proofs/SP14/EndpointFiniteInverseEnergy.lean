import NLA.Proofs.SP14.EndpointFiniteInverseFourier
import NLA.Proofs.SP14.EndpointInverseHSScalar
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
Finite square-energy estimate for the actual triangular inverse coefficients.
The circle Parseval identity and L² completion are separate gates.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 4000000

namespace NLA.Proofs.SP14

private theorem endpointInverseCoeff_norm (n : ℕ) :
    ‖(baseInverseCoeff n : ℂ)‖ = endpointCentralCoeff n := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h : |baseInverseCoeff n| = |endpointCentralCoeff n| := by
    simp [endpointCentralCoeff, abs_mul]
  rw [h, abs_of_pos (endpointCentralCoeff_pos n)]

private theorem physicalCoeff_norm (r : ℝ) (y : SobolevCoeff r) (k : ℕ) :
    ‖physicalCoeff r y k‖ =
      (((k + 1 : ℕ) : ℝ) ^ (-r)) * ‖y k‖ := by
  rw [physicalCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

private theorem endpointFiniteInverse_row_energy (r : ℝ) (y : SobolevCoeff r)
    (N d : ℕ) :
    ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 ≤
      (∑ k ∈ Finset.Ico d N,
        (endpointCentralCoeff (k - d) *
          (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) *
      (∑ k ∈ Finset.Ico d N, ‖y k‖ ^ 2) := by
  let w : ℕ → ℝ := fun k => endpointCentralCoeff (k - d) *
    (((k + 1 : ℕ) : ℝ) ^ (-r))
  have hterm (k : ℕ) :
      ‖(baseInverseCoeff (k - d) : ℂ) * physicalCoeff r y k‖ =
        w k * ‖y k‖ := by
    rw [norm_mul, endpointInverseCoeff_norm, physicalCoeff_norm]
    dsimp [w]
    ring
  have htriangle : ‖endpointFiniteInverseCoeff r y N d‖ ≤
      ∑ k ∈ Finset.Ico d N, w k * ‖y k‖ := by
    unfold endpointFiniteInverseCoeff
    calc
      _ ≤ ∑ k ∈ Finset.Ico d N,
          ‖(baseInverseCoeff (k - d) : ℂ) * physicalCoeff r y k‖ :=
        norm_sum_le _ _
      _ = ∑ k ∈ Finset.Ico d N, w k * ‖y k‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k
  have hsum : 0 ≤ ∑ k ∈ Finset.Ico d N, w k * ‖y k‖ :=
    Finset.sum_nonneg (fun k hk => mul_nonneg
      (mul_nonneg (endpointCentralCoeff_pos _).le
        (Real.rpow_nonneg (by positivity) _)) (norm_nonneg _))
  have hsq : ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 ≤
      (∑ k ∈ Finset.Ico d N, w k * ‖y k‖) ^ 2 := by
    nlinarith [norm_nonneg (endpointFiniteInverseCoeff r y N d)]
  calc
    _ ≤ (∑ k ∈ Finset.Ico d N, w k * ‖y k‖) ^ 2 := hsq
    _ ≤ (∑ k ∈ Finset.Ico d N, w k ^ 2) *
        (∑ k ∈ Finset.Ico d N, ‖y k‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ w (fun k => ‖y k‖)
    _ = _ := rfl

private theorem endpointFiniteInverse_input_prefix (r : ℝ)
    (y : SobolevCoeff r) (d N : ℕ) :
    (∑ k ∈ Finset.Ico d N, ‖y k‖ ^ 2) ≤ ‖y‖ ^ 2 := by
  have hs : Summable (fun k : ℕ => ‖y k‖ ^ 2) := by
    simpa using ((lp.memℓp y).summable
      (by norm_num : 0 < (2 : ENNReal).toReal))
  have hnorm : ‖y‖ ^ 2 = ∑' k : ℕ, ‖y k‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ENNReal).toReal) y
    calc
      ‖y‖ ^ 2 = ‖y‖ ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = ∑' k : ℕ, ‖y k‖ ^ 2 := by simpa using h
  rw [hnorm]
  exact hs.sum_le_tsum (Finset.Ico d N) (fun k hk => sq_nonneg _)

private theorem endpointFiniteInverse_columns (r : ℝ) (N : ℕ) :
    (∑ d ∈ Finset.range N,
      ∑ k ∈ Finset.Ico d N,
        (endpointCentralCoeff (k - d) *
          (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) =
      ∑ k ∈ Finset.range N, endpointInverseHSColumn r k := by
  rw [← Nat.Ico_zero_eq_range N, Finset.sum_Ico_Ico_comm]
  rw [Nat.Ico_zero_eq_range]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.Ico_zero_eq_range]
  have hreflect :
      (∑ d ∈ Finset.range (k + 1), endpointCentralCoeff (k - d) ^ 2) =
        ∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2 := by
    simpa only [Nat.add_sub_cancel_right] using
      (Finset.sum_range_reflect (fun l => endpointCentralCoeff l ^ 2) (k + 1))
  unfold endpointInverseHSColumn
  have hx : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by positivity
  calc
    (∑ d ∈ Finset.range (k + 1),
        (endpointCentralCoeff (k - d) * (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) =
      (∑ d ∈ Finset.range (k + 1), endpointCentralCoeff (k - d) ^ 2) *
        (((k + 1 : ℕ) : ℝ) ^ (-r)) ^ 2 := by
          simp_rw [mul_pow]
          rw [Finset.sum_mul]
    _ = (((k + 1 : ℕ) : ℝ) ^ (-2 * r)) *
        (∑ l ∈ Finset.range (k + 1), endpointCentralCoeff l ^ 2) := by
          rw [hreflect, ← Real.rpow_mul_natCast hx.le (-r) 2]
          rw [show (-r) * (((2 : ℕ) : ℝ)) = -2 * r by norm_num; ring]
          ring

/-- The exact finite triangular inverse coefficient energy is controlled by
the reviewed squared Hilbert–Schmidt scalar and the actual weighted input norm. -/
theorem endpointFiniteInverse_coeff_energy_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    (∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2) ≤
      endpointInverseHSSquare r * ‖y‖ ^ 2 := by
  have hrows : (∑ d ∈ Finset.range N,
      ‖endpointFiniteInverseCoeff r y N d‖ ^ 2) ≤
      (∑ d ∈ Finset.range N,
        (∑ k ∈ Finset.Ico d N,
          (endpointCentralCoeff (k - d) *
            (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) * ‖y‖ ^ 2) := by
    calc
      _ ≤ ∑ d ∈ Finset.range N,
          (∑ k ∈ Finset.Ico d N,
            (endpointCentralCoeff (k - d) *
              (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) *
            (∑ k ∈ Finset.Ico d N, ‖y k‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro d hd
        exact endpointFiniteInverse_row_energy r y N d
      _ ≤ ∑ d ∈ Finset.range N,
          (∑ k ∈ Finset.Ico d N,
            (endpointCentralCoeff (k - d) *
              (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) * ‖y‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact mul_le_mul_of_nonneg_left
          (endpointFiniteInverse_input_prefix r y d N)
          (Finset.sum_nonneg (fun k hk => sq_nonneg _))
  have hsum : (∑ d ∈ Finset.range N,
      ∑ k ∈ Finset.Ico d N,
        (endpointCentralCoeff (k - d) *
          (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) ≤ endpointInverseHSSquare r := by
    rw [endpointFiniteInverse_columns]
    exact (summable_endpointInverseHSColumn r hrHalf).sum_le_tsum
      (Finset.range N) (fun k hk => by
        unfold endpointInverseHSColumn
        positivity)
  calc
    _ ≤ (∑ d ∈ Finset.range N,
        ∑ k ∈ Finset.Ico d N,
          (endpointCentralCoeff (k - d) *
            (((k + 1 : ℕ) : ℝ) ^ (-r))) ^ 2) * ‖y‖ ^ 2 := by
      simpa only [Finset.sum_mul] using hrows
    _ ≤ endpointInverseHSSquare r * ‖y‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsum (sq_nonneg _)

#assert_trust kernel endpointFiniteInverse_coeff_energy_le
#print axioms endpointFiniteInverse_coeff_energy_le

end NLA.Proofs.SP14
