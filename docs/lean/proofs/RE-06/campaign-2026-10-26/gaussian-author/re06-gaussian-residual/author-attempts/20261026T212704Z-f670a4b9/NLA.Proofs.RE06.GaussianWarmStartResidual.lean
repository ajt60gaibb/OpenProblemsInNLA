import NLA.Proofs.RE06.GaussianResidualTails
import NLA.Proofs.RE06.Transcript

/-! Actual finite-family warm-start bound for the unscaled prequeried Gaussian
block, with a pointwise identity to the unchanged sketch branch. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

theorem squaredFrobenius_residual {n q : ℕ}
    (A B : Matrix (Fin n) (Fin q) ℝ) :
    squaredFrobenius (A - B) 0 = squaredFrobenius A B := by
  simp only [squaredFrobenius, Matrix.sub_apply, Matrix.zero_apply, sub_zero]

theorem squaredFrobenius_mul_residual {n q : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin q) ℝ) :
    squaredFrobenius ((A - B) * G) 0 = squaredFrobenius (A * G) (B * G) := by
  rw [Matrix.sub_mul, squaredFrobenius_residual]

/-- This is literally the first minimum of the actual unscaled Gaussian scores. -/
def gaussianWarmIndex {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ)
    (q offset : ℕ) (ω : ℕ → ℝ) : Fin (m + 2) :=
  minimumIndex (fun b => squaredFrobenius (A * gaussianBlock n q offset ω)
    (F b * gaussianBlock n q offset ω))

theorem optimum_sq {n m : ℕ} (F : Family n m) (A : Matrix (Fin n) (Fin n) ℝ) :
    (optimum A F) ^ 2 =
      squaredFrobenius A (F (minimumIndex (fun b => squaredFrobenius A (F b)))) := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-- Uniform source warm-start failure bound under the exact countable stream law. -/
theorem gaussianWarmIndex_tail_bound {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (q offset r : ℕ) (hq : 0 < q) (hr : r < n)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    GaussianLaw.real {ω | ((1 + η) / (1 - η)) * (optimum A F) ^ 2 <
      residualTailEnergy (A - F (gaussianWarmIndex F A q offset ω)) r} ≤
      (m + 2 : ℝ) * Real.exp (-(q : ℝ) * (r : ℝ) * η / 4) +
        Real.exp (-(q : ℝ) * η ^ 2 / 8) := by
  let opt := minimumIndex (fun b => squaredFrobenius A (F b))
  have hl (b : Fin (m + 2)) := residualGaussian_lower_tail (A - F b) q offset r hr η hη0 hη1.le
  have hu := residualGaussian_upper_tail (A - F opt) q offset η hη0 hη1.le
  simp only [squaredFrobenius_mul_residual] at hl hu
  rw [squaredFrobenius_residual] at hu
  have h := warmStart_failure_bound_from_tails
    (fun b ω => squaredFrobenius (A * gaussianBlock n q offset ω)
      (F b * gaussianBlock n q offset ω))
    (fun b => residualTailEnergy (A - F b) r) (gaussianWarmIndex F A q offset) opt
    (fun ω => minimumIndex_score_le _ opt) (q : ℝ) η (squaredFrobenius A (F opt))
    (Real.exp (-(q : ℝ) * (r : ℝ) * η / 4)) (Real.exp (-(q : ℝ) * η ^ 2 / 8))
    (Nat.cast_pos.mpr hq) hη1 hl hu
  simpa only [optimum_sq, Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] using h

/-- The actual program uses precisely this minimum in its sketch branch. -/
theorem gaussianWarmIndex_eq_sketchWarmIndex {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n) (ω : ℕ → ℝ) :
    gaussianWarmIndex F A (firstWidth m ε) 0 ω =
      sketchWarmIndex F A (makePlan n m ε ω) := by
  rw [makePlan_sketch_blocks n m ε hsketch ω]
  rfl

/-- The literal program warm-start index inherits the actual-law tail bound. -/
theorem sketchWarmIndex_tail_bound {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n)
    (hq : 0 < firstWidth m ε) (r : ℕ) (hr : r < n)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    GaussianLaw.real {ω | ((1 + η) / (1 - η)) * (optimum A F) ^ 2 <
      residualTailEnergy (A - F (sketchWarmIndex F A (makePlan n m ε ω))) r} ≤
      (m + 2 : ℝ) * Real.exp (-(firstWidth m ε : ℝ) * (r : ℝ) * η / 4) +
        Real.exp (-(firstWidth m ε : ℝ) * η ^ 2 / 8) := by
  simpa only [gaussianWarmIndex_eq_sketchWarmIndex F A ε hsketch] using
    gaussianWarmIndex_tail_bound F A (firstWidth m ε) 0 r hq hr η hη0 hη1

#assert_trust kernel squaredFrobenius_residual
#assert_trust kernel squaredFrobenius_mul_residual
#assert_trust kernel optimum_sq
#assert_trust kernel gaussianWarmIndex_tail_bound
#assert_trust kernel gaussianWarmIndex_eq_sketchWarmIndex
#assert_trust kernel sketchWarmIndex_tail_bound
#print axioms squaredFrobenius_residual
#print axioms squaredFrobenius_mul_residual
#print axioms optimum_sq
#print axioms gaussianWarmIndex_tail_bound
#print axioms gaussianWarmIndex_eq_sketchWarmIndex
#print axioms sketchWarmIndex_tail_bound
end NLA.Proofs.RE06
