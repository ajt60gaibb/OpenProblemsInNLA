import NLA.IE21.QuadraticNet

/-!
Deterministic norm and all-direction control for the frozen IE-21 statistics.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
namespace NLA.IE21

theorem normalizedOperator_nonneg {m n : ℕ} (A : Mat m n) :
    0 ≤ normalizedOperator A := by
  unfold normalizedOperator
  positivity

theorem normalizedOperator_eq_norm {m n : ℕ} (A : Mat m n) :
    normalizedOperator A =
      ‖((n : ℝ) / m) • ((matrixMap A).adjoint.comp (matrixMap A))‖ := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)),
    ContinuousLinearMap.norm_adjoint_comp_self]
  simp only [normalizedOperator, operatorNorm, pow_two]

theorem normalizedOperator_le_covarianceError_add_one {m n : ℕ} (A : Mat m n) :
    normalizedOperator A ≤ covarianceError A + 1 := by
  let C : Space n →L[ℝ] Space n :=
    ((n : ℝ) / m) • ((matrixMap A).adjoint.comp (matrixMap A))
  have h := norm_le_norm_sub_add C (ContinuousLinearMap.id ℝ (Space n))
  have hi : ‖ContinuousLinearMap.id ℝ (Space n)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  rw [normalizedOperator_eq_norm]
  change ‖C‖ ≤ ‖C - ContinuousLinearMap.id ℝ (Space n)‖ + 1
  linarith

theorem normalizedOperator_le_of_covariance {m n : ℕ} (A : Mat m n)
    (t : ℝ) (hcov : covarianceError A ≤ t) : normalizedOperator A ≤ 1 + t := by
  have h := normalizedOperator_le_covarianceError_add_one A
  linarith

theorem abs_normalizedOperator_sub_one_le_covarianceError {m n : ℕ}
    (A : Mat m n) (hn : 1 ≤ n) :
    |normalizedOperator A - 1| ≤ covarianceError A := by
  let : NeZero n := ⟨by omega⟩
  have hi : ‖ContinuousLinearMap.id ℝ (Space n)‖ = 1 := ContinuousLinearMap.norm_id
  rw [normalizedOperator_eq_norm, ← hi]
  exact abs_norm_sub_norm_le _ _

def retainedLinearMap {m n : ℕ} (A : Mat m n) (S : Finset (Fin m)) :
    Space n →L[ℝ] EuclideanSpace ℝ S :=
  (Matrix.toEuclideanLin (retainedMatrix A S)).toContinuousLinearMap

theorem retainedNorm_le_matrixNorm {m n : ℕ} (A : Mat m n)
    (S : Finset (Fin m)) (x : Space n) : retainedNorm A S x ≤ ‖matrixMap A x‖ := by
  have hs : (∑ i ∈ S, (matrixMap A x i) ^ 2) ≤ ∑ i, (matrixMap A x i) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => sq_nonneg _)
  rw [← retainedNorm_sq, ← EuclideanSpace.real_norm_sq_eq] at hs
  have h0 : 0 ≤ retainedNorm A S x := norm_nonneg _
  nlinarith [norm_nonneg (matrixMap A x)]

theorem retainedLinearMap_norm_le {m n : ℕ} (A : Mat m n) (S : Finset (Fin m)) :
    ‖retainedLinearMap A S‖ ≤ operatorNorm A := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  exact (retainedNorm_le_matrixNorm A S x).trans ((matrixMap A).le_opNorm x)

theorem retainedNorm_sq_lipschitz {m n : ℕ} (A : Mat m n) (S : Finset (Fin m))
    (x y : Space n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |retainedNorm A S x ^ 2 - retainedNorm A S y ^ 2| ≤
      2 * operatorNorm A ^ 2 * ‖x - y‖ := by
  let F := retainedLinearMap A S
  have h := quadratic_lipschitz (F.adjoint.comp F) x y hx hy
  have hform (z : Space n) : inner ℝ ((F.adjoint.comp F) z) z = retainedNorm A S z ^ 2 := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K]
    rfl
  rw [hform, hform, ContinuousLinearMap.norm_adjoint_comp_self, ← pow_two] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (retainedLinearMap_norm_le A S) 2) (by norm_num)

theorem directionalTrim_lipschitz {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (x y : Space n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |directionalTrim θ A x - directionalTrim θ A y| ≤
      2 * normalizedOperator A * ‖x - y‖ := by
  have hforward (x y : Space n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
      directionalTrim θ A x - directionalTrim θ A y ≤
        2 * normalizedOperator A * ‖x - y‖ := by
    obtain ⟨⟨S, hS, hval⟩, _⟩ := finiteTrim_minimum (retainedRows θ m)
      (retainedRows_le θ hθ m) (fun i => (matrixMap A y i) ^ 2)
    have hxmin := (finiteTrim_minimum (retainedRows θ m)
      (retainedRows_le θ hθ m) (fun i => (matrixMap A x i) ^ 2)).2 S hS
    have hd := (le_abs_self _).trans (retainedNorm_sq_lipschitz A S x y hx hy)
    rw [retainedNorm_sq, retainedNorm_sq] at hd
    have hraw : finiteTrim (retainedRows θ m) (fun i => (matrixMap A x i) ^ 2) -
        finiteTrim (retainedRows θ m) (fun i => (matrixMap A y i) ^ 2) ≤
          2 * operatorNorm A ^ 2 * ‖x - y‖ := by
      rw [hval]
      linarith
    have h := mul_le_mul_of_nonneg_left hraw
      (div_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) m))
    dsimp [directionalTrim, normalizedOperator]
    nlinarith [h]
  apply abs_le.mpr
  constructor
  · have h := hforward y x hy hx
    rw [norm_sub_rev] at h
    linarith
  · exact hforward x y hx hy

theorem directionalTrim_lipschitz_of_covariance {m n : ℕ} (θ : ℝ)
    (hθ : 0 < θ ∧ θ < 1) (A : Mat m n) (t : ℝ) (hcov : covarianceError A ≤ t)
    (x y : Space n) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |directionalTrim θ A x - directionalTrim θ A y| ≤ 2 * (1 + t) * ‖x - y‖ := by
  apply (directionalTrim_lipschitz θ hθ A x y hx hy).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (normalizedOperator_le_of_covariance A t hcov) (by norm_num))
    (norm_nonneg _)

theorem goodEvent_of_net {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (t ε δ : ℝ) (ht : 0 ≤ t) (C : Finset (Space n))
    (hC : ∀ y ∈ C, ‖y‖ = 1)
    (hcover : ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ δ)
    (hcov : covarianceError A ≤ t)
    (hpopulation : ∀ y ∈ C,
      |populationTrim θ (sphereLaw n) (directionalEnergy y) - gaussianTrim θ| ≤
        Real.sqrt (2 / (n : ℝ)))
    (hpoint : ∀ y ∈ C,
      |directionalTrim θ A y - populationTrim θ (sphereLaw n) (directionalEnergy y)| ≤
        2 * truncationScale θ * ε + truncationScale θ / m) :
    A ∈ GoodEvent θ m n t ε δ := by
  refine ⟨hcov, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hcover x hx
  have hdist := (directionalTrim_lipschitz_of_covariance θ hθ A t hcov x y hx (hC y hy)).trans
    (mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ 2 * (1 + t)))
  have hmiddle := abs_sub_le (directionalTrim θ A y)
    (populationTrim θ (sphereLaw n) (directionalEnergy y)) (gaussianTrim θ)
  have htotal := abs_sub_le (directionalTrim θ A x) (directionalTrim θ A y) (gaussianTrim θ)
  have hpointy := hpoint y hy
  have hpopy := hpopulation y hy
  dsimp [trimmingError]
  linarith

end NLA.IE21
