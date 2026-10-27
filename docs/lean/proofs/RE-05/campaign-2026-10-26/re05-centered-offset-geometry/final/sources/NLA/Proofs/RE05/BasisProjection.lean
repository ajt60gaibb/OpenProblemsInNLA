import NLA.Proofs.RE05.ResidualLeverage

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix

theorem matrix_inner_trace {n : ℕ} (A B : Square n) :
    NLA.Computation.LinearFamilyQuery.inner A B = (A.transpose * B).trace := by
  simp only [NLA.Computation.LinearFamilyQuery.inner, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

theorem matrix_inner_comm {n : ℕ} (A B : Square n) :
    NLA.Computation.LinearFamilyQuery.inner A B = NLA.Computation.LinearFamilyQuery.inner B A := by
  simp [NLA.Computation.LinearFamilyQuery.inner, mul_comm]

theorem matrix_inner_add_left {n : ℕ} (A B C : Square n) :
    NLA.Computation.LinearFamilyQuery.inner (A + B) C =
      NLA.Computation.LinearFamilyQuery.inner A C + NLA.Computation.LinearFamilyQuery.inner B C := by
  simp [NLA.Computation.LinearFamilyQuery.inner, add_mul, Finset.sum_add_distrib]

theorem matrix_inner_add_right {n : ℕ} (A B C : Square n) :
    NLA.Computation.LinearFamilyQuery.inner A (B + C) =
      NLA.Computation.LinearFamilyQuery.inner A B + NLA.Computation.LinearFamilyQuery.inner A C := by
  simp [NLA.Computation.LinearFamilyQuery.inner, mul_add, Finset.sum_add_distrib]

theorem matrix_inner_self_nonnegative {n : ℕ} (A : Square n) :
    0 ≤ NLA.Computation.LinearFamilyQuery.inner A A := by
  rw [← matrixVector_inner, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem projection_matrix_inner_cross {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) (E F : Square n) :
    NLA.Computation.LinearFamilyQuery.inner (selectedProjection plan * E)
      (residualProjection plan * F) = 0 := by
  rw [matrix_inner_trace]
  have hm : (selectedProjection plan * E).transpose * (residualProjection plan * F) = 0 := by
    rw [Matrix.transpose_mul, (selectedProjection_symmetric plan).eq]
    calc
      E.transpose * selectedProjection plan * (residualProjection plan * F) =
          E.transpose * ((selectedProjection plan * residualProjection plan) * F) := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [selected_residual_mul_zero plan hF]; simp
  rw [hm, Matrix.trace_zero]

/-- Exact Frobenius splitting by the actual two complementary blocks. -/
theorem projection_matrix_inner_split {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) (E F : Square n) :
    NLA.Computation.LinearFamilyQuery.inner E F =
      NLA.Computation.LinearFamilyQuery.inner (selectedProjection plan * E) (selectedProjection plan * F) +
        NLA.Computation.LinearFamilyQuery.inner (residualProjection plan * E) (residualProjection plan * F) := by
  have he := (projection_basis_split plan E).symm
  have hf := (projection_basis_split plan F).symm
  calc
    NLA.Computation.LinearFamilyQuery.inner E F =
        NLA.Computation.LinearFamilyQuery.inner
          (selectedProjection plan * E + residualProjection plan * E)
          (selectedProjection plan * F + residualProjection plan * F) := congrArg₂ _ he hf
    _ = _ := by
      rw [matrix_inner_add_left, matrix_inner_add_right, matrix_inner_add_right,
        projection_matrix_inner_cross plan hF,
        matrix_inner_comm (residualProjection plan * E) (selectedProjection plan * F),
        projection_matrix_inner_cross plan hF]
      ring

theorem makePlan_residualBasis_inner_le_one {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (j : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.inner
      (residualBasisBlock P (makePlan P ξ ω copy) j)
      (residualBasisBlock P (makePlan P ξ ω copy) j) ≤ 1 := by
  have h := projection_matrix_inner_split (makePlan P ξ ω copy)
    (makePlan_frame_gram P ξ ω copy) (orthonormalMember P j) (orthonormalMember P j)
  have hu : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) (orthonormalMember P j) = 1 := by
    simpa using orthonormalMember_inner P hP j j
  have hn := matrix_inner_self_nonnegative
    (selectedProjection (makePlan P ξ ω copy) * orthonormalMember P j)
  rw [hu] at h
  change NLA.Computation.LinearFamilyQuery.inner
    (residualProjection (makePlan P ξ ω copy) * orthonormalMember P j)
    (residualProjection (makePlan P ξ ω copy) * orthonormalMember P j) ≤ 1
  linarith

theorem makePlan_residualBasis_norm_le_one {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (j : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.norm n (residualBasisBlock P (makePlan P ξ ω copy) j) ≤ 1 := by
  apply Real.sqrt_le_one.mpr
  exact makePlan_residualBasis_inner_le_one P hP ξ ω copy j

/-- Coefficient Gram matrix of an explicitly supplied family of matrices. -/
def matrixFamilyGram {n q : ℕ} (F : Basis n q) : Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  fun i j => NLA.Computation.LinearFamilyQuery.inner (F i) (F j)

theorem matrixFamilyGram_posSemidef {n q : ℕ} (F : Basis n q) :
    (matrixFamilyGram F).PosSemidef := by
  let M : Matrix (Fin n × Fin n) (Fin (q + 1)) ℝ := fun p j => F j p.1 p.2
  have heq : matrixFamilyGram F = M.transpose * M := by
    ext i j
    change (∑ a : Fin n, ∑ b : Fin n, F i a b * F j a b) =
      ∑ p : Fin n × Fin n, F i p.1 p.2 * F j p.1 p.2
    rw [Fintype.sum_prod_type]
  rw [heq]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self M

def selectedBasisGram {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  matrixFamilyGram (fun j => selectedProjection plan * orthonormalMember P j)

def residualBasisGram {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) ℝ :=
  matrixFamilyGram (residualBasisBlock P plan)

theorem selectedBasisGram_posSemidef {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (selectedBasisGram P plan).PosSemidef := matrixFamilyGram_posSemidef _

theorem residualBasisGram_posSemidef {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (residualBasisGram P plan).PosSemidef := matrixFamilyGram_posSemidef _

/-- The selected and residual coefficient Gram blocks of the actual fold
basis sum to the identity, with no extra basis promise. -/
theorem makePlan_basisGram_split {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedBasisGram P (makePlan P ξ ω copy) + residualBasisGram P (makePlan P ξ ω copy) = 1 := by
  ext i j
  change NLA.Computation.LinearFamilyQuery.inner
      (selectedProjection (makePlan P ξ ω copy) * orthonormalMember P i)
      (selectedProjection (makePlan P ξ ω copy) * orthonormalMember P j) +
    NLA.Computation.LinearFamilyQuery.inner
      (residualProjection (makePlan P ξ ω copy) * orthonormalMember P i)
      (residualProjection (makePlan P ξ ω copy) * orthonormalMember P j) =
      if i = j then 1 else 0
  exact (projection_matrix_inner_split (makePlan P ξ ω copy)
    (makePlan_frame_gram P ξ ω copy) (orthonormalMember P i) (orthonormalMember P j)).symm.trans
      (orthonormalMember_inner P hP i j)

theorem makePlan_residualBasisGram_le_one {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    (1 - residualBasisGram P (makePlan P ξ ω copy)).PosSemidef := by
  rw [← makePlan_basisGram_split P hP ξ ω copy, add_sub_cancel_right]
  exact selectedBasisGram_posSemidef _ _

theorem makePlan_selectedBasisGram_le_one {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    (1 - selectedBasisGram P (makePlan P ξ ω copy)).PosSemidef := by
  rw [← makePlan_basisGram_split P hP ξ ω copy, add_sub_cancel_left]
  exact residualBasisGram_posSemidef _ _

end NLA.Proofs.RE05
