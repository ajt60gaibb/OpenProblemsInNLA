import NLA.Proofs.SP14.RegularizedBaseFactorFourier
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
The literal bilateral weighted Wiener size of the actual endpoint-regularized
exterior factor. Its Fourier coefficients are the frozen normalized integrals.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def wienerWeight (k : ℤ) : ℝ :=
  (1 + (k.natAbs : ℝ)) ^ (9 / 8 : ℝ)

noncomputable def weightedWienerSize (f : Circle → ℂ) : ℝ :=
  ∑' k : ℤ, wienerWeight k * ‖FourierCoefficient f k‖

private noncomputable def regularizedWienerTerm (k : ℤ) : ℝ :=
  wienerWeight k * ‖FourierCoefficient regularizedBaseFactor k‖

private theorem regularizedWienerTerm_pos (n : ℕ) :
    regularizedWienerTerm ((n + 1 : ℕ) : ℤ) =
      if n = 0 then (2 : ℝ) ^ (9 / 8 : ℝ) else 0 := by
  rw [regularizedWienerTerm, regularizedBaseFactor_fourier]
  by_cases hn : n = 0
  · subst n
    norm_num [wienerWeight]
  · have hnotone : ((n + 1 : ℕ) : ℤ) ≠ 1 := by omega
    have hnotnonpos : ¬ (((n + 1 : ℕ) : ℤ) ≤ 0) := by omega
    simp [hn]

private theorem regularizedWienerTerm_nonpos (n : ℕ) :
    regularizedWienerTerm (-(n : ℤ)) =
      ((n + 1 : ℝ) ^ (9 / 8 : ℝ)) * ‖regularizedBaseCoeff n‖ := by
  have hnotone : -(n : ℤ) ≠ 1 := by omega
  have hnonpos : -(n : ℤ) ≤ 0 := by omega
  simp [regularizedWienerTerm, regularizedBaseFactor_fourier, wienerWeight,
    hnotone, hnonpos, Int.natAbs_neg, add_comm]

private theorem regularizedWienerTerm_zero :
    regularizedWienerTerm 0 = ‖regularizedBaseCoeff 0‖ := by
  simpa using regularizedWienerTerm_nonpos 0

private theorem summable_regularizedWienerTerm_pos :
    Summable (fun n : ℕ => regularizedWienerTerm ((n + 1 : ℕ) : ℤ)) := by
  simp_rw [regularizedWienerTerm_pos]
  apply summable_of_ne_finset_zero (s := {0})
  intro n hn
  have hn0 : n ≠ 0 := by simpa using hn
  simp [hn0]

private theorem summable_regularizedWienerTerm_neg :
    Summable (fun n : ℕ => regularizedWienerTerm (-((n + 1 : ℕ) : ℤ))) := by
  have hshift := (summable_nat_add_iff 1).mpr
    summable_regularizedBaseCoeff_weighted
  apply hshift.congr
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using
    (regularizedWienerTerm_nonpos (n + 1)).symm

theorem summable_regularizedBaseFactor_wiener :
    Summable (fun k : ℤ =>
      wienerWeight k * ‖FourierCoefficient regularizedBaseFactor k‖) := by
  change Summable regularizedWienerTerm
  exact Summable.of_add_one_of_neg_add_one
    summable_regularizedWienerTerm_pos summable_regularizedWienerTerm_neg

theorem regularizedBaseFactor_wiener_eq :
    weightedWienerSize regularizedBaseFactor =
      (2 : ℝ) ^ (9 / 8 : ℝ) +
        ∑' n : ℕ,
          ((n + 1 : ℝ) ^ (9 / 8 : ℝ)) * ‖regularizedBaseCoeff n‖ := by
  have hpos : (∑' n : ℕ, regularizedWienerTerm ((n + 1 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (9 / 8 : ℝ) := by
    simp_rw [regularizedWienerTerm_pos]
    simp
  have hneg : (∑' n : ℕ, regularizedWienerTerm (-((n + 1 : ℕ) : ℤ))) =
      ∑' n : ℕ,
        (((n + 1 : ℕ) + 1 : ℕ) : ℝ) ^ (9 / 8 : ℝ) *
          ‖regularizedBaseCoeff (n + 1)‖ := by
    apply tsum_congr
    intro n
    simpa using regularizedWienerTerm_nonpos (n + 1)
  have hfull := tsum_of_add_one_of_neg_add_one
    summable_regularizedWienerTerm_pos summable_regularizedWienerTerm_neg
  change weightedWienerSize regularizedBaseFactor = _
  unfold weightedWienerSize
  change (∑' k : ℤ, regularizedWienerTerm k) = _
  simp only [Nat.cast_add, Nat.cast_one] at hpos hneg
  rw [hfull, hpos, regularizedWienerTerm_zero, hneg]
  have hsplit := summable_regularizedBaseCoeff_weighted.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, Real.one_rpow, one_mul,
    Nat.cast_add, Nat.cast_one] at hsplit
  calc
    (2 : ℝ) ^ (9 / 8 : ℝ) + ‖regularizedBaseCoeff 0‖ +
        ∑' n : ℕ, (↑n + 1 + 1) ^ (9 / 8 : ℝ) *
          ‖regularizedBaseCoeff (n + 1)‖ =
      (2 : ℝ) ^ (9 / 8 : ℝ) +
        (‖regularizedBaseCoeff 0‖ +
          ∑' n : ℕ, (↑n + 1 + 1) ^ (9 / 8 : ℝ) *
            ‖regularizedBaseCoeff (n + 1)‖) := by ring
    _ = _ := by rw [hsplit]

#assert_trust kernel summable_regularizedBaseFactor_wiener
#assert_trust kernel regularizedBaseFactor_wiener_eq

end NLA.Proofs.SP14
