import NLA.Proofs.RE06.PseudoInverseTikhonovCore

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Filter
open scoped BigOperators Topology

namespace NLA.Proofs.RE06.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery

def regularizationParameter (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem regularizationParameter_pos (j : ℕ) : 0 < regularizationParameter j := by
  unfold regularizationParameter
  positivity

theorem regularizationParameter_tendsto : Tendsto regularizationParameter atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem regularizedSigma_tendsto {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (k : Fin (min a b)) :
    Tendsto (fun j => regularizedSigma B (regularizationParameter j) k) atTop (𝓝 (sigmaInv B k)) := by
  by_cases h : sigma B k = 0
  · simp only [regularizedSigma, h, zero_div, sigmaInv, if_pos rfl]
    exact tendsto_const_nhds
  · have hden : (sigma B k) ^ 2 + (0 : ℝ) ≠ 0 := by simpa using pow_ne_zero 2 h
    have hlim : Tendsto (fun j => sigma B k / ((sigma B k) ^ 2 + regularizationParameter j))
        atTop (𝓝 (sigma B k / ((sigma B k) ^ 2 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add regularizationParameter_tendsto) hden
    convert hlim using 1
    simp only [sigmaInv, if_neg h, add_zero]
    field_simp
    <;> ring

theorem tikhonov_entry {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) (t : ℝ) (ht : 0 < t)
    (i : Fin b) (j : Fin a) :
    tikhonov B t i j = ∑ k, thinV B i k * regularizedSigma B t k * thinU B j k := by
  rw [tikhonov_decomposition B t ht]
  change (∑ k, (thinV B * Matrix.diagonal (regularizedSigma B t)) i k * thinU B j k) = _
  simp only [Matrix.mul_diagonal]

theorem pseudoinverse_entry {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ)
    (i : Fin b) (j : Fin a) :
    pseudoInverse B i j = ∑ k, thinV B i k * sigmaInv B k * thinU B j k := by
  rw [pseudoinverse_decomposition B]
  change (∑ k, (thinV B * Matrix.diagonal (sigmaInv B)) i k * thinU B j k) = _
  simp only [Matrix.mul_diagonal]

theorem tikhonov_tendsto {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Tendsto (fun j => tikhonov B (regularizationParameter j)) atTop (𝓝 (pseudoInverse B)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have heq : (fun n => tikhonov B (regularizationParameter n) i j) =
      (fun n => ∑ k, thinV B i k * regularizedSigma B (regularizationParameter n) k * thinU B j k) := by
    funext n
    exact tikhonov_entry B _ (regularizationParameter_pos n) i j
  rw [heq, pseudoinverse_entry]
  exact tendsto_finset_sum _ (fun k _ =>
    (tendsto_const_nhds.mul (regularizedSigma_tendsto B k)).mul tendsto_const_nhds)

#assert_trust kernel tikhonov_tendsto
#print axioms tikhonov_tendsto
end NLA.Proofs.RE06.Pseudo
