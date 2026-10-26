import NLA.Proofs.TR04.SVDProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators InnerProductSpace Matrix

namespace NLA.Proofs.TR04.SVD
open NLA.Computation.SVDMachine

theorem right_synthesis_energy {m l p : ℕ}
    (L : Matrix (Fin m) (Fin p) ℝ) {R : Matrix (Fin l) (Fin p) ℝ}
    (hR : OrthonormalColumns R) (c : Fin p → ℝ) :
    matrixEnergy (fun i j => ∑ k, L i k * c k * R j k) =
      ∑ k, (c k)^2 * ∑ i, (L i k)^2 := by
  unfold matrixEnergy
  have hi (i : Fin m) : (∑ j, (∑ k, L i k * c k * R j k)^2) =
      ∑ k, (L i k * c k)^2 := by
    simpa only [mul_comm] using orthonormalColumns_sum_sq hR (fun k => L i k * c k)
  simp_rw [hi, mul_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem matrixColumn_synthesis {m l : ℕ}
    (U : Matrix (Fin m) (Fin m) ℝ) (c : Fin (min m l) → ℝ)
    (V : Matrix (Fin l) (Fin l) ℝ) (j : Fin l) :
    matrixColumn (synthesis U c V) j = ∑ k,
      (c k * V j (Fin.castLE (Nat.min_le_right m l) k)) •
        matrixColumn U (Fin.castLE (Nat.min_le_left m l) k) := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  simp only [matrixColumn, synthesis, WithLp.ofLp_toLp, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem validSVD_project_energy {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (S : Submodule ℝ (Space m)) :
    matrixEnergy (projectMatrix S B) = ∑ k, (sigma k)^2 *
      projectionWeight S U (Fin.castLE (Nat.min_le_left m l) k) := by
  let L : Matrix (Fin m) (Fin (min m l)) ℝ := fun i k =>
    S.starProjection (matrixColumn U (Fin.castLE (Nat.min_le_left m l) k)) i
  let R := V.submatrix id (Fin.castLE (Nat.min_le_right m l))
  have hR : OrthonormalColumns R := orthonormalColumns_submatrix h.2.1 _
    (fun _ _ he => Fin.ext (congrArg (fun i : Fin l => i.val) he))
  have hp : projectMatrix S B = fun i j => ∑ k, L i k * sigma k * R j k := by
    rw [validSVD_eq_synthesis h]
    ext i j
    change S.starProjection (matrixColumn (synthesis U sigma V) j) i = _
    rw [matrixColumn_synthesis, map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [L, R]
    ring
  rw [hp, right_synthesis_energy L hR]
  apply Finset.sum_congr rfl
  intro k _
  rw [projectionWeight, EuclideanSpace.real_norm_sq_eq]

theorem sum_fin_prefix_le {a b : ℕ} (hab : a ≤ b) (f : Fin b → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ i : Fin a, f (Fin.castLE hab i)) ≤ ∑ i : Fin b, f i := by
  classical
  let e : Fin a → Fin b := Fin.castLE hab
  have he : Function.Injective e := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin b => k.val) h)
  have hs : ∑ i ∈ Finset.univ.image e, f i = ∑ i : Fin a, f (e i) := by
    rw [Finset.sum_image]
    exact fun i _ j _ h => he h
  rw [← hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => hf i)

theorem sum_svd_projectionWeight_le {m l : ℕ} (S : Submodule ℝ (Space m))
    {U : Matrix (Fin m) (Fin m) ℝ} (hU : OrthonormalColumns U) :
    (∑ k : Fin (min m l), projectionWeight S U (Fin.castLE (Nat.min_le_left m l) k)) ≤
      Module.finrank ℝ S := by
  rw [← sum_projectionWeight S hU]
  exact sum_fin_prefix_le _ _ (projectionWeight_nonneg S U)

theorem singularSquares_antitone {p : ℕ} {sigma : Fin p → ℝ}
    (h0 : ∀ i, 0 ≤ sigma i) (hord : Antitone sigma) : Antitone (fun i => (sigma i)^2) := by
  intro i j hij
  exact sq_le_sq₀ (h0 j) (h0 i) |>.mpr (hord hij)

theorem prefix_add_tail {p : ℕ} (sigma : Fin p → ℝ) (r : ℕ) :
    prefixEnergy (fun k => (sigma k)^2) r + tailEnergy sigma r = ∑ k, (sigma k)^2 := by
  rw [prefixEnergy, tailEnergy, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < r
  · simp [hk, Nat.not_le.mpr hk]
  · simp [hk, Nat.le_of_not_gt hk]

theorem tailEnergy_eq_zero_of_length_le {p : ℕ} (sigma : Fin p → ℝ) {r : ℕ}
    (hr : p ≤ r) : tailEnergy sigma r = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hk : ¬ r ≤ k.val := by omega
  simp [hk]

def columnSpace {m l : ℕ} (Y : Matrix (Fin m) (Fin l) ℝ) : Submodule ℝ (Space m) :=
  (Matrix.toEuclideanLin Y).range

theorem matrixColumn_mem_columnSpace {m l : ℕ} (Y : Matrix (Fin m) (Fin l) ℝ)
    (j : Fin l) : matrixColumn Y j ∈ columnSpace Y := by
  refine ⟨EuclideanSpace.single j 1, ?_⟩
  apply (WithLp.ext_iff 2).mpr
  funext i
  simp [Matrix.toLpLin_apply, matrixColumn]

set_option backward.isDefEq.respectTransparency false in
theorem finrank_columnSpace {m l : ℕ} (Y : Matrix (Fin m) (Fin l) ℝ) :
    Module.finrank ℝ (columnSpace Y) = Matrix.rank Y := by
  symm
  simpa only [columnSpace, Space, Matrix.toEuclideanLin_eq_toLin_orthonormal] using
    Matrix.rank_eq_finrank_range_toLin Y
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin l) ℝ).toBasis

/-- Eckart--Young's squared Frobenius lower bound for every legal full SVD
tuple and every actual rank-bounded comparator, including zero and oversized
rank bounds. -/
theorem validSVD_eckartYoung {m l : ℕ} {B : Matrix (Fin m) (Fin l) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m l) → ℝ}
    {V : Matrix (Fin l) (Fin l) ℝ} (h : ValidSVD B U sigma V)
    (r : ℕ) (Y : Matrix (Fin m) (Fin l) ℝ) (hY : Matrix.rank Y ≤ r) :
    tailEnergy sigma r ≤ matrixEnergy (B - Y) := by
  by_cases hr : r < min m l
  · let S := columnSpace Y
    let w : Fin (min m l) → ℝ := fun k =>
      projectionWeight S U (Fin.castLE (Nat.min_le_left m l) k)
    have hsum : ∑ k, w k ≤ r :=
      (sum_svd_projectionWeight_le S h.1).trans (by exact_mod_cast
        ((finrank_columnSpace Y).trans_le hY))
    have hcapture := weighted_prefix_le (⟨r, hr⟩ : Fin (min m l))
      (singularSquares_antitone h.2.2.1 h.2.2.2.1) (sq_nonneg _) 
      (fun k => projectionWeight_nonneg S U _) (fun k => projectionWeight_le_one S h.1 _) hsum
    have hcaptured : matrixEnergy (projectMatrix S B) ≤
        prefixEnergy (fun k => (sigma k)^2) r := by
      rw [validSVD_project_energy h]
      exact hcapture
    have hpy := projectMatrix_energy_decomposition S B
    have herr := projectMatrix_error_le S B Y (matrixColumn_mem_columnSpace Y)
    have htot := validSVD_energy h
    have htail := prefix_add_tail sigma r
    linarith
  · rw [tailEnergy_eq_zero_of_length_le sigma (Nat.le_of_not_gt hr)]
    exact matrixEnergy_nonneg _

#assert_trust kernel validSVD_project_energy
#assert_trust kernel finrank_columnSpace
#assert_trust kernel validSVD_eckartYoung
#print axioms validSVD_eckartYoung

end NLA.Proofs.TR04.SVD
