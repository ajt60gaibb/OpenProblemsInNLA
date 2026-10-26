import NLA.Proofs.RE05.Attained

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators

/-- Inverse coordinates of the fixed Frobenius flattening. -/
def vectorMatrix {n : ℕ} (v : EuclideanSpace ℝ (Fin n × Fin n)) : Square n :=
  fun i j => v (i, j)

@[simp] theorem vectorMatrix_matrixVector {n : ℕ} (A : Square n) :
    vectorMatrix (matrixVector A) = A := rfl

@[simp] theorem matrixVector_vectorMatrix {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n × Fin n)) : matrixVector (vectorMatrix v) = v := by
  ext p
  rfl

theorem matrixVector_injective {n : ℕ} :
    Function.Injective (matrixVector (n := n)) := by
  intro A B h
  exact congrArg vectorMatrix h

/-- The fixed entry flattening as a linear map, without choosing a basis. -/
def matrixVectorMap (n : ℕ) : Square n →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n) where
  toFun := matrixVector
  map_add' A B := by ext p; rfl
  map_smul' t A := by ext p; rfl

theorem matrixVector_inner {n : ℕ} (A B : Square n) :
    inner ℝ (matrixVector A) (matrixVector B) =
      NLA.Computation.LinearFamilyQuery.inner A B := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, matrixVector,
    NLA.Computation.LinearFamilyQuery.inner, dotProduct, Fintype.sum_prod_type, mul_comm]

theorem matrixVector_norm {n : ℕ} (A : Square n) :
    ‖matrixVector A‖ = NLA.Computation.LinearFamilyQuery.norm n A := by
  rw [NLA.Computation.LinearFamilyQuery.norm, ← matrixVector_inner,
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem independent_matrixVector {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : LinearIndependent ℝ (fun j => matrixVector (P j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  apply hP c
  intro i j
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n) => v (i, j)) hc
  simpa [matrixVector] using h

/-- Fixed-order normalized Gram--Schmidt coordinates, used only to identify
the entries produced by the model's actual fold. -/
def orderedMember {n q : ℕ} (P : Basis n q) (j : Fin (q + 1)) : Square n :=
  vectorMatrix (InnerProductSpace.gramSchmidtNormed ℝ (fun a => matrixVector (P a)) j)

theorem orderedMember_orthonormal {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : Orthonormal ℝ (fun j => matrixVector (orderedMember P j)) := by
  simpa [orderedMember] using
    InnerProductSpace.gramSchmidtNormed_orthonormal (independent_matrixVector P hP)

theorem orderedMember_injective {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : Function.Injective (orderedMember P) := by
  intro a b hab
  exact (orderedMember_orthonormal P hP).linearIndependent.injective
    (congrArg matrixVector hab)

theorem normalized_starProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    (ℝ ∙ v).starProjection w = inner ℝ w (‖v‖⁻¹ • v) • (‖v‖⁻¹ • v) := by
  rw [Submodule.starProjection_singleton]
  simp only [inner_smul_right, real_inner_comm w v, smul_smul]
  congr 1
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

/-- The unnormalized residual is a sum over earlier normalized vectors. -/
theorem ordered_residual {n q : ℕ} (P : Basis n q) (j : Fin (q + 1)) :
    InnerProductSpace.gramSchmidt ℝ (fun a => matrixVector (P a)) j =
      matrixVector (fun i k => P j i k -
        ∑ a ∈ Finset.Iio j,
          NLA.Computation.LinearFamilyQuery.inner (P j) (orderedMember P a) *
            orderedMember P a i k) := by
  rw [InnerProductSpace.gramSchmidt_def]
  simp_rw [normalized_starProjection]
  change matrixVector (P j) - ∑ a ∈ Finset.Iio j,
    inner ℝ (matrixVector (P j)) (matrixVector (orderedMember P a)) •
      matrixVector (orderedMember P a) = _
  simp_rw [matrixVector_inner]
  ext p
  simp [matrixVector]

end NLA.Proofs.RE05
