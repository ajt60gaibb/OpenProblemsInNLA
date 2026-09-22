import NLA.IE21.QuadraticNet

/-!
Exact finite-minimum scaling and the matrix-to-row-energy bridge for IE-21.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace NLA.IE21

theorem finiteTrim_smul_nonneg {m : ℕ} (k : ℕ) (hk : k ≤ m)
    (c : ℝ) (hc : 0 ≤ c) (y : Fin m → ℝ) :
    finiteTrim k (fun i => c * y i) = c * finiteTrim k y := by
  classical
  obtain ⟨⟨S, hS, heqS⟩, hmin⟩ := finiteTrim_minimum k hk y
  obtain ⟨⟨T, hT, heqT⟩, hminC⟩ := finiteTrim_minimum k hk (fun i => c * y i)
  apply le_antisymm
  · calc
      _ ≤ ∑ i ∈ S, c * y i := hminC S hS
      _ = c * finiteTrim k y := by rw [heqS, Finset.mul_sum]
  · rw [heqT]
    simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left (hmin T hT) hc

theorem directionalTrim_eq_energy_trim {m n : ℕ} (θ : ℝ)
    (hθ : 0 < θ ∧ θ < 1) (A : Mat m n) (x : Space n) :
    directionalTrim θ A x =
      finiteTrim (retainedRows θ m) (fun i => directionalEnergy x (matrixRow A i)) / m := by
  have heq : (fun i => directionalEnergy x (matrixRow A i)) =
      (fun i => (n : ℝ) * (matrixMap A x i) ^ 2) := by
    funext i
    rw [directionalEnergy, matrixMap_eq_inner_row]
  rw [heq, finiteTrim_smul_nonneg _ (retainedRows_le θ hθ m) _ (Nat.cast_nonneg n)]
  unfold directionalTrim
  ring

end NLA.IE21
