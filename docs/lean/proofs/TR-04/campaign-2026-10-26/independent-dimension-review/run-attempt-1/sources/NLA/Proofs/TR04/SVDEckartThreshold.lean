import NLA.Proofs.TR04.SVDEckartEquality
import NLA.Proofs.TR04.SVDThresholdWeights

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators InnerProductSpace
namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

/-- Equality classification at any positive threshold separating the retained
prefix from its complement. The threshold may be the last retained value,
including when a whole repeated-value block is retained. -/
theorem validSVD_eckartYoung_eq_threshold {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (hr : r ≤ min m l) (tau : ℝ) (htau : 0 < tau)
    (habove : ∀ k, k.val < r → tau ≤ sigma k)
    (hbelow : ∀ k, r ≤ k.val → sigma k ≤ tau)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma r) :
    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = r ∧
      (∀ k, tau < sigma k → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =
          matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧
      (∀ k, sigma k < tau → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) := by
  let S := columnSpace Y
  let w : Fin (min m l) → ℝ := fun k =>
    projectionWeight S U (Fin.castLE (Nat.min_le_left m l) k)
  have hsum : ∑ k, w k ≤ r :=
    (sum_svd_projectionWeight_le S h.1).trans (by exact_mod_cast
      ((finrank_columnSpace Y).trans_le hY))
  have hab (k : Fin (min m l)) (hk : k.val < r) : tau^2 ≤ (sigma k)^2 := by
    have := habove k hk
    have := h.2.2.1 k
    nlinarith
  have hbe (k : Fin (min m l)) (hk : r ≤ k.val) : (sigma k)^2 ≤ tau^2 := by
    have := hbelow k hk
    have := h.2.2.1 k
    nlinarith
  have hcapture := weighted_threshold_le hr (sq_nonneg tau) hab hbe
    (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _) hsum
  have hcap : matrixEnergy (projectMatrix S B) ≤
      prefixEnergy (fun k => (sigma k)^2) r := by
    rw [validSVD_project_energy h]
    exact hcapture
  have hpy := projectMatrix_energy_decomposition S B
  have herr := projectMatrix_error_le S B Y (matrixColumn_mem_columnSpace Y)
  have htot := validSVD_energy h
  have htail := prefix_add_tail sigma r
  have hpEq : matrixEnergy (B - Y) = matrixEnergy (B - projectMatrix S B) := by linarith
  have hcapEq : (∑ k, (sigma k)^2 * w k) =
      prefixEnergy (fun k => (sigma k)^2) r := by
    rw [← validSVD_project_energy h S]
    linarith
  have hsupp := weighted_threshold_eq_support hr (sq_pos_of_pos htau) hab hbe
    (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _)
    hsum hcapEq
  have hrank : Matrix.rank Y = r := by
    have hle := sum_svd_projectionWeight_le (l := l) S h.1
    change ∑ k, w k ≤ (Module.finrank ℝ S : ℝ) at hle
    rw [hsupp.1] at hle
    have hle' : r ≤ Module.finrank ℝ S := by exact_mod_cast hle
    rw [finrank_columnSpace] at hle'
    exact Nat.le_antisymm hY hle'
  refine ⟨(projectMatrix_error_eq_iff S B Y (matrixColumn_mem_columnSpace Y)).mp hpEq,
    hrank, ?_, ?_⟩
  · intro k hk
    apply (projectionWeight_eq_one_iff S h.1 _).mp
    apply hsupp.2.1
    have := h.2.2.1 k
    nlinarith
  · intro k hk
    apply (projectionWeight_eq_zero_iff S U _).mp
    apply hsupp.2.2
    have := h.2.2.1 k
    nlinarith

theorem validSVD_eckartYoung_eq_last_retained {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (a : Fin (min m l)) (ha : 0 < sigma a)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ a.val + 1)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma (a.val + 1)) :
    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = a.val + 1 ∧
      (∀ k, sigma a < sigma k → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =
          matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧
      (∀ k, sigma k < sigma a → (columnSpace Y).starProjection
        (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) := by
  refine validSVD_eckartYoung_eq_threshold h (a.val + 1) (by omega) (sigma a) ha
      ?_ ?_ Y hY heq
  · intro k hk
    exact h.2.2.2.1 k a (Fin.le_iff_val_le_val.mpr (by omega))
  · intro k hk
    exact h.2.2.2.1 a k (Fin.le_iff_val_le_val.mpr (by omega))

#assert_trust kernel validSVD_eckartYoung_eq_threshold
#assert_trust kernel validSVD_eckartYoung_eq_last_retained
#print axioms validSVD_eckartYoung_eq_last_retained
end NLA.Proofs.TR04.SVD
