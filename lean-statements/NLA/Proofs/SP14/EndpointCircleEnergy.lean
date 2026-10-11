import NLA.Proofs.SP14.EndpointCircleFourier
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
The conventional full-circle weighted Fourier energy of the actual endpoint
circle realization. Its negative weight differs from the two-block model by
one index, and the exact comparison factor is `2^(2*r)`.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- The conventional two-sided circle Sobolev energy at integer mode `p`. -/
noncomputable def endpointCircleEnergyTerm (r : ℝ)
    (f : Circle → ℂ) (p : ℤ) : ℝ :=
  (((p.natAbs + 1 : ℕ) : ℝ) ^ (2 * r)) * ‖FourierCoefficient f p‖ ^ 2

private theorem endpointCircleEnergyTerm_nonneg (r : ℝ)
    (f : Circle → ℂ) (p : ℤ) :
    0 ≤ endpointCircleEnergyTerm r f p := by
  unfold endpointCircleEnergyTerm
  positivity

private theorem endpointCircleEnergy_nonneg_formula (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (k : ℕ) :
    endpointCircleEnergyTerm r (endpointCircleRealization r hrHalf hr1 y) (k : ℤ) =
      ‖y k‖ ^ 2 := by
  have h := weightedCoord_norm_sq r (physicalCoeff r y) k
  rw [weightedCoord_physicalCoeff] at h
  unfold endpointCircleEnergyTerm
  rw [endpointCircleRealization_fourier_nonneg r hrHalf hr1 y k]
  simp only [Int.natAbs_natCast]
  exact h.symm

private theorem endpointCircleEnergy_neg_formula (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (t : ℕ) :
    endpointCircleEnergyTerm r (endpointCircleRealization r hrHalf hr1 y)
        (-((t + 1 : ℕ) : ℤ)) =
      (((t + 2 : ℕ) : ℝ) ^ (2 * r)) *
        ‖physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t‖ ^ 2 := by
  unfold endpointCircleEnergyTerm
  rw [endpointCircleRealization_fourier_neg r hrHalf hr1 y t]
  have hnat : (-(↑(t + 1) : ℤ)).natAbs = t + 1 := by omega
  rw [hnat]

private theorem endpointCircleEnergy_neg_bounds (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (t : ℕ) :
    ‖endpointNegativeOperator r (by linarith : 0 < r) hr1 y t‖ ^ 2 ≤
      endpointCircleEnergyTerm r (endpointCircleRealization r hrHalf hr1 y)
        (-((t + 1 : ℕ) : ℤ)) ∧
      endpointCircleEnergyTerm r (endpointCircleRealization r hrHalf hr1 y)
        (-((t + 1 : ℕ) : ℤ)) ≤
          (2 : ℝ) ^ (2 * r) *
            ‖endpointNegativeOperator r (by linarith : 0 < r) hr1 y t‖ ^ 2 := by
  let v := endpointNegativeOperator r (by linarith : 0 < r) hr1 y
  have hcoord := weightedCoord_norm_sq r (physicalCoeff r v) t
  rw [weightedCoord_physicalCoeff] at hcoord
  have htpos : 0 ≤ (((t + 1 : ℕ) : ℝ)) := by positivity
  have hlow : (((t + 1 : ℕ) : ℝ) ^ (2 * r)) ≤
      (((t + 2 : ℕ) : ℝ) ^ (2 * r)) := by
    apply Real.rpow_le_rpow htpos
    · exact_mod_cast (Nat.le_succ (t + 1))
    · linarith
  have hhi : (((t + 2 : ℕ) : ℝ) ^ (2 * r)) ≤
      (2 : ℝ) ^ (2 * r) * (((t + 1 : ℕ) : ℝ) ^ (2 * r)) := by
    have ht : (((t + 2 : ℕ) : ℝ)) ≤ 2 * (((t + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (by omega : t + 2 ≤ 2 * (t + 1))
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (((t + 2 : ℕ) : ℝ)))
      ht (by linarith : 0 ≤ 2 * r)
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htpos] at hp
  rw [endpointCircleEnergy_neg_formula]
  constructor
  · calc
      ‖v t‖ ^ 2 = (((t + 1 : ℕ) : ℝ) ^ (2 * r)) *
          ‖physicalCoeff r v t‖ ^ 2 := hcoord
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (sq_nonneg _)
  · calc
      (((t + 2 : ℕ) : ℝ) ^ (2 * r)) * ‖physicalCoeff r v t‖ ^ 2 ≤
          ((2 : ℝ) ^ (2 * r) * (((t + 1 : ℕ) : ℝ) ^ (2 * r))) *
            ‖physicalCoeff r v t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hhi (sq_nonneg _)
      _ = (2 : ℝ) ^ (2 * r) *
          ((((t + 1 : ℕ) : ℝ) ^ (2 * r)) * ‖physicalCoeff r v t‖ ^ 2) := by ring
      _ = _ := by rw [← hcoord]

private theorem endpointCircleEnergy_pos_summable (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    Summable (fun k : ℕ => endpointCircleEnergyTerm r
      (endpointCircleRealization r hrHalf hr1 y) (k : ℤ)) := by
  have hy : Summable (fun k : ℕ => ‖y k‖ ^ 2) := by
    simpa using ((lp.memℓp y).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  simpa only [endpointCircleEnergy_nonneg_formula r hrHalf hr1 y] using hy

private theorem endpointCircleEnergy_neg_summable (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    Summable (fun t : ℕ => endpointCircleEnergyTerm r
      (endpointCircleRealization r hrHalf hr1 y) (-((t + 1 : ℕ) : ℤ))) := by
  let v := endpointNegativeOperator r (by linarith : 0 < r) hr1 y
  have hv : Summable (fun t : ℕ => ‖v t‖ ^ 2) := by
    simpa using ((lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  apply Summable.of_nonneg_of_le
  · intro t
    exact endpointCircleEnergyTerm_nonneg r _ _
  · intro t
    exact (endpointCircleEnergy_neg_bounds r hrHalf hr1 y t).2
  · exact hv.mul_left _

/-- The realized continuous circle function has finite conventional full
`H^r` Fourier energy. -/
theorem summable_endpointCircleEnergy (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    Summable (endpointCircleEnergyTerm r
      (endpointCircleRealization r hrHalf hr1 y)) := by
  exact Summable.of_nat_of_neg_add_one
    (endpointCircleEnergy_pos_summable r hrHalf hr1 y)
    (endpointCircleEnergy_neg_summable r hrHalf hr1 y)

private theorem endpointCoeff_norm_sq_tsum (r : ℝ) (v : SobolevCoeff r) :
    ‖v‖ ^ 2 = ∑' n : ℕ, ‖v n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ENNReal).toReal) v
  calc
    ‖v‖ ^ 2 = ‖v‖ ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = ∑' n : ℕ, ‖v n‖ ^ 2 := by simpa using h

/-- Exact comparison between the conventional full-circle Sobolev energy
and the already proved orthogonal two-block coefficient norm. -/
theorem endpointCircleEnergy_bounds (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) :
    ‖endpointTwoSidedCoeffOperator r (by linarith : 0 < r) hr1 y‖ ^ 2 ≤
      ∑' p : ℤ, endpointCircleEnergyTerm r
        (endpointCircleRealization r hrHalf hr1 y) p ∧
    (∑' p : ℤ, endpointCircleEnergyTerm r
      (endpointCircleRealization r hrHalf hr1 y) p) ≤
        (2 : ℝ) ^ (2 * r) *
          ‖endpointTwoSidedCoeffOperator r (by linarith : 0 < r) hr1 y‖ ^ 2 := by
  let v := endpointNegativeOperator r (by linarith : 0 < r) hr1 y
  let e : ℤ → ℝ := endpointCircleEnergyTerm r
    (endpointCircleRealization r hrHalf hr1 y)
  have hpos := endpointCircleEnergy_pos_summable r hrHalf hr1 y
  have hneg := endpointCircleEnergy_neg_summable r hrHalf hr1 y
  have hsplit : (∑' p : ℤ, e p) =
      (∑' k : ℕ, e (k : ℤ)) + (∑' t : ℕ, e (-((t + 1 : ℕ) : ℤ))) := by
    exact tsum_of_nat_of_neg_add_one hpos hneg
  have hpossum : (∑' k : ℕ, e (k : ℤ)) = ‖y‖ ^ 2 := by
    calc
      _ = ∑' k : ℕ, ‖y k‖ ^ 2 := by
        apply tsum_congr
        intro k
        exact endpointCircleEnergy_nonneg_formula r hrHalf hr1 y k
      _ = ‖y‖ ^ 2 := (endpointCoeff_norm_sq_tsum r y).symm
  have hv : Summable (fun t : ℕ => ‖v t‖ ^ 2) := by
    simpa using ((lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal))
  have hneglo : ‖v‖ ^ 2 ≤ (∑' t : ℕ, e (-((t + 1 : ℕ) : ℤ))) := by
    calc
      ‖v‖ ^ 2 = ∑' t : ℕ, ‖v t‖ ^ 2 := endpointCoeff_norm_sq_tsum r v
      _ ≤ ∑' t : ℕ, e (-((t + 1 : ℕ) : ℤ)) :=
        Summable.tsum_le_tsum
          (fun t => (endpointCircleEnergy_neg_bounds r hrHalf hr1 y t).1) hv hneg
  have hneghi : (∑' t : ℕ, e (-((t + 1 : ℕ) : ℤ))) ≤
      (2 : ℝ) ^ (2 * r) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ∑' t : ℕ, (2 : ℝ) ^ (2 * r) * ‖v t‖ ^ 2 :=
        Summable.tsum_le_tsum
          (fun t => (endpointCircleEnergy_neg_bounds r hrHalf hr1 y t).2)
          hneg (hv.mul_left _)
      _ = (2 : ℝ) ^ (2 * r) * ‖v‖ ^ 2 := by
        rw [tsum_mul_left, ← endpointCoeff_norm_sq_tsum r v]
  have hmodel := endpointTwoSidedCoeffOperator_norm_sq r
    (by linarith : 0 < r) hr1 y
  have hfac : 1 ≤ (2 : ℝ) ^ (2 * r) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  constructor
  · change ‖endpointTwoSidedCoeffOperator r (by linarith : 0 < r) hr1 y‖ ^ 2 ≤
      ∑' p : ℤ, e p
    rw [hmodel, hsplit, hpossum]
    nlinarith [hneglo]
  · change (∑' p : ℤ, e p) ≤
      (2 : ℝ) ^ (2 * r) *
        ‖endpointTwoSidedCoeffOperator r (by linarith : 0 < r) hr1 y‖ ^ 2
    rw [hmodel, hsplit, hpossum]
    nlinarith [hneghi, mul_nonneg (sub_nonneg.mpr hfac) (sq_nonneg ‖y‖)]

#assert_trust kernel summable_endpointCircleEnergy
#assert_trust kernel endpointCircleEnergy_bounds
#print axioms endpointCircleEnergy_bounds

end NLA.Proofs.SP14
