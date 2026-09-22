import NLA.IE22.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Actual isometric restriction and the sorted spectral tail for IE-22.
Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

theorem matrixMap_eq_row_inner {m n : ℕ} (A : Mat m n) (x : Space n) (i : Fin m) :
    matrixMap A x i = inner ℝ (matrixRow A i) x := by
  simp [matrixMap_apply, matrixRow, PiLp.inner_apply, mul_comm]

theorem projected_matrixMap {m n d : ℕ} (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) (g : Space d) :
    matrixMap (projectedMatrix A J) g = matrixMap A (J g) := by
  have hg : (∑ j, g j • EuclideanSpace.single j 1) = g := by
    simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr g
  ext i
  rw [matrixMap_apply, matrixMap_eq_row_inner]
  nth_rw 2 [← hg]
  simp [projectedMatrix, map_sum, inner_sum, inner_smul_right, mul_comm]

theorem projected_row_norm_le {m n d : ℕ} (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) (i : Fin m) :
    ‖matrixRow (projectedMatrix A J) i‖ ≤ ‖matrixRow A i‖ := by
  have ho := (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin d)).comp_linearIsometry J
  have h := ho.sum_inner_products_le (s := Finset.univ) (matrixRow A i)
  have hs : ‖matrixRow (projectedMatrix A J) i‖ ^ 2 ≤ ‖matrixRow A i‖ ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq, matrixRow, projectedMatrix,
      real_inner_comm, Real.norm_eq_abs, sq_abs] using h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem projection_semantics (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) :
    (∀ g : Space d, matrixMap (projectedMatrix A J) g = matrixMap A (J g)) ∧
    (∀ i, ‖matrixRow (projectedMatrix A J) i‖ ≤ ‖matrixRow A i‖) ∧
    deletionSingular θ A ≤ deletionSingular θ (projectedMatrix A J) := by
  refine ⟨projected_matrixMap A J, projected_row_norm_le A J, ?_⟩
  obtain ⟨S, g, hS, hg, hmin⟩ := (deletion_minimum θ hθ (projectedMatrix A J) hd).2.1
  have h := (deletion_minimum θ hθ A hn).2.2 S (J g) hS (by simpa using hg)
  have heq : retainedNorm A S (J g) = retainedNorm (projectedMatrix A J) S g := by
    have hs : retainedNorm A S (J g)^2 = retainedNorm (projectedMatrix A J) S g^2 := by
      simp only [retainedNorm_sq, projected_matrixMap]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  simpa [hmin, heq] using h

/-- The synthesis map of an orthonormal family is an actual linear isometry. -/
def orthonormalSynthesis {n d : ℕ} (v : Fin d → Space n) (hv : Orthonormal ℝ v) :
    Space d →ₗᵢ[ℝ] Space n where
  toFun x := ∑ i, x i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]
  norm_map' x := by
    have hs : ‖∑ i, x i • v i‖^2 = ‖x‖^2 := by
      conv_rhs => rw [EuclideanSpace.real_norm_sq_eq]
      simpa [pow_two] using hv.inner_sum x x Finset.univ
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- Row norms exactly account for the Gram trace. -/
theorem gram_trace_row_norms {m d : ℕ} (B : Mat m d) :
    Matrix.trace (gramMatrix B) = ∑ i, ‖matrixRow B i‖^2 := by
  simp only [gramMatrix, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp [matrixRow, pow_two]

/-- The sorted spectral tail has the precise source bound m/(r+1). -/
theorem spectral_projection (m n r : ℕ) (_hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (A : Mat m n) (hA : UnitRows A) :
    ∃ J : Space (n - r) →ₗᵢ[ℝ] Space n,
      operatorNorm (projectedMatrix A J)^2 ≤ (m:ℝ)/((r:ℝ)+1) ∧
      (∀ i, ‖matrixRow (projectedMatrix A J) i‖ ≤ 1) ∧
      Matrix.trace (gramMatrix (projectedMatrix A J)) ≤ m := by
  classical
  change ∀ i, ‖matrixRow A i‖ = 1 at hA
  let L := matrixMap A
  let T : Space n →ₗ[ℝ] Space n := (L.adjoint.comp L).toLinearMap
  have hT : T.IsSymmetric := by
    intro x y
    change inner ℝ (L.adjoint (L x)) y = inner ℝ x (L.adjoint (L y))
    rw [L.adjoint_inner_left, L.adjoint_inner_right]
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  let b := hT.eigenvectorBasis hdim
  let eig := hT.eigenvalues hdim
  have heigen (i : Fin n) : T (b i) = eig i • b i := hT.apply_eigenvectorBasis hdim i
  have henergy (x : Space n) : ‖L x‖^2 = inner ℝ (T x) x := by
    simpa [T] using L.apply_norm_sq_eq_inner_adjoint_left x
  have heig (i : Fin n) : eig i = ‖L (b i)‖^2 := by
    rw [henergy, heigen]
    simp [inner_smul_left, b.orthonormal.1 i]
  have heig0 (i : Fin n) : 0 ≤ eig i := by rw [heig]; positivity
  have hsum : ∑ i, eig i = (m : ℝ) := by
    simp_rw [heig, EuclideanSpace.real_norm_sq_eq]
    change (∑ i, ∑ j, (matrixMap A (b i) j)^2) = _
    simp_rw [matrixMap_eq_row_inner]
    rw [Finset.sum_comm]
    simp_rw [b.sum_sq_inner_left]
    simp [hA]
  let k : Fin n := ⟨r, hr.2⟩
  have hk : ((r : ℝ) + 1) * eig k ≤ m := by
    calc
      ((r : ℝ) + 1) * eig k = ∑ i ∈ Finset.Iic k, eig k := by
        simp [Fin.card_Iic, k, Nat.cast_add, Nat.cast_one]
      _ ≤ ∑ i ∈ Finset.Iic k, eig i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hT.eigenvalues_antitone hdim (Finset.mem_Iic.mp hi)
      _ ≤ ∑ i, eig i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => heig0 i)
      _ = m := hsum
  have hk' : eig k ≤ (m : ℝ) / ((r : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hk]
  let e : Fin (n - r) → Fin n := fun i => ⟨r + i, by omega⟩
  have he : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    dsimp [e] at hh
    omega
  have hv : Orthonormal ℝ (fun i => b (e i)) := b.orthonormal.comp e he
  let J := orthonormalSynthesis (fun i => b (e i)) hv
  have hJ (g : Space (n-r)) : J g = ∑ i, g i • b (e i) := rfl
  have hbound (g : Space (n-r)) : ‖L (J g)‖^2 ≤ eig k * ‖g‖^2 := by
    have heq : ‖L (J g)‖^2 = ∑ i, eig (e i) * (g i)^2 := by
      rw [henergy, hJ, map_sum]
      simp_rw [map_smul, heigen, smul_smul]
      have h := hv.inner_sum (fun i => g i * eig (e i)) (fun i => g i) Finset.univ
      simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using h
    rw [heq]
    conv_rhs => rw [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hT.eigenvalues_antitone hdim
    change r ≤ r + i.val
    omega
  refine ⟨J, ?_, ?_, ?_⟩
  · obtain ⟨g, hg, hgmax⟩ := (matrix_semantics (projectedMatrix A J) (by omega)).2.1
    have h := hbound g
    rw [hg, one_pow, mul_one] at h
    rw [← projected_matrixMap A J, hgmax] at h
    exact h.trans hk'
  · intro i
    exact (projected_row_norm_le A J i).trans (hA i).le
  · rw [gram_trace_row_norms]
    calc
      (∑ i, ‖matrixRow (projectedMatrix A J) i‖^2) ≤ ∑ _ : Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := (projected_row_norm_le A J i).trans (hA i).le
        nlinarith [norm_nonneg (matrixRow (projectedMatrix A J) i)]
      _ = m := by simp

end NLA.IE22
