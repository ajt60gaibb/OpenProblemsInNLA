import NLA.Proofs.TR04.SVDEckartYoung

/-! Equality in the actual Frobenius best-approximation bound. These results
hold for every legal full SVD, including repeated boundary singular values. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators InnerProductSpace

namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem projectionWeight_eq_one_iff {m : ℕ} (S : Submodule ℝ (Space m))
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U) (i : Fin m) :
    projectionWeight S U i = 1 ↔ S.starProjection (matrixColumn U i) = matrixColumn U i := by
  obtain ⟨b, hb⟩ := exists_basis_of_orthonormalColumns hU
  have hu : ‖matrixColumn U i‖ = 1 := by rw [← hb]; exact b.norm_eq_one i
  constructor
  · intro h
    apply S.starProjection_eq_self_iff.mpr
    apply (S.mem_iff_norm_starProjection _).mpr
    rw [hu]
    unfold projectionWeight at h
    nlinarith [norm_nonneg (S.starProjection (matrixColumn U i))]
  · intro h
    unfold projectionWeight
    rw [h, hu]
    norm_num

theorem projectionWeight_eq_zero_iff {m : ℕ} (S : Submodule ℝ (Space m))
    (U : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) :
    projectionWeight S U i = 0 ↔ S.starProjection (matrixColumn U i) = 0 := by
  unfold projectionWeight
  constructor
  · intro h
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S.starProjection (matrixColumn U i))]
  · rintro h
    simp [h]

/-- In a positive, nontrivial tail equality case the comparator is the actual
column-space projection, its rank is exactly the allowance, and the supplied
singular directions strictly above and strictly below the boundary have
projection weights one and zero respectively. -/
theorem validSVD_eckartYoung_eq {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : Fin (min m l)) (hrpos : 0 < sigma r)
    (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r.val)
    (heq : matrixEnergy (B - Y) = tailEnergy sigma r.val) :
    Y = projectMatrix (columnSpace Y) B ∧ Matrix.rank Y = r.val ∧
      (∀ k, sigma r < sigma k →
        (columnSpace Y).starProjection
          (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) =
            matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) ∧
      (∀ k, sigma k < sigma r →
        (columnSpace Y).starProjection
          (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) = 0) := by
  let S := columnSpace Y
  let w : Fin (min m l) → ℝ := fun k =>
    projectionWeight S U (Fin.castLE (Nat.min_le_left m l) k)
  have hsum : ∑ k, w k ≤ r.val :=
    (sum_svd_projectionWeight_le S h.1).trans (by exact_mod_cast
      ((finrank_columnSpace Y).trans_le hY))
  have hcapture := weighted_prefix_le r
    (singularSquares_antitone h.2.2.1 h.2.2.2.1) (sq_nonneg _)
    (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _) hsum
  have hcap : matrixEnergy (projectMatrix S B) ≤
      prefixEnergy (fun k => (sigma k)^2) r.val := by
    rw [validSVD_project_energy h]
    exact hcapture
  have hpy := projectMatrix_energy_decomposition S B
  have herr := projectMatrix_error_le S B Y (matrixColumn_mem_columnSpace Y)
  have htot := validSVD_energy h
  have htail := prefix_add_tail sigma r.val
  have hpEq : matrixEnergy (B - Y) = matrixEnergy (B - projectMatrix S B) := by linarith
  have hcapEq : (∑ k, (sigma k)^2 * w k) =
      prefixEnergy (fun k => (sigma k)^2) r.val := by
    rw [← validSVD_project_energy h S]
    linarith
  have hsupp := weighted_prefix_eq_support r
    (singularSquares_antitone h.2.2.1 h.2.2.2.1) (sq_pos_of_pos hrpos)
    (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _)
    hsum hcapEq
  have hrank : Matrix.rank Y = r.val := by
    have hle := sum_svd_projectionWeight_le (l := l) S h.1
    change ∑ k, w k ≤ (Module.finrank ℝ S : ℝ) at hle
    rw [hsupp.1] at hle
    have hle' : r.val ≤ Module.finrank ℝ S := by exact_mod_cast hle
    rw [finrank_columnSpace] at hle'
    exact Nat.le_antisymm hY hle'
  refine ⟨(projectMatrix_error_eq_iff S B Y (matrixColumn_mem_columnSpace Y)).mp hpEq,
    hrank, ?_, ?_⟩
  · intro k hk
    apply (projectionWeight_eq_one_iff S h.1 _).mp
    apply hsupp.2.1
    have hk0 := h.2.2.1 k
    have hr0 := h.2.2.1 r
    nlinarith
  · intro k hk
    apply (projectionWeight_eq_zero_iff S U _).mp
    apply hsupp.2.2
    have hk0 := h.2.2.1 k
    have hr0 := h.2.2.1 r
    nlinarith

#assert_trust kernel validSVD_eckartYoung_eq
#print axioms validSVD_eckartYoung_eq

end NLA.Proofs.TR04.SVD
