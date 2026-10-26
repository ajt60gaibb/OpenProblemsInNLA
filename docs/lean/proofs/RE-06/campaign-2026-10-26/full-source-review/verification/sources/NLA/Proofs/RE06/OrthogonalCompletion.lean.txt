import NLA.Proofs.RE06.SVDPartition

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Classical
namespace NLA.Proofs.RE06.Repair

def matrixColumn {n d : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => Q i j)

theorem matrix_columns_orthonormal {n d : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) : Orthonormal ℝ (matrixColumn Q) := by
  rw [orthonormal_iff_ite]
  intro i j
  have h := congrFun (congrFun hQ i) j
  change (∑ k, Q k j*Q k i) = _
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, mul_comm] using h

/-- A fixed rectangular isometry extends to an actual full orthogonal matrix.
No measurability of this auxiliary fixed-matrix choice is asserted. -/
theorem exists_orthogonal_completion {n d : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (hd : d ≤ n) :
    ∃ O : Matrix (Fin n) (Fin n) ℝ,
      O.transpose*O=1 ∧ O*O.transpose=1 ∧ O*headEmbedding n d hd=Q := by
  let s : Set (Fin n) := {i | i.val < d}
  let v : Fin n → EuclideanSpace ℝ (Fin n) := fun i =>
    if h : i.val < d then matrixColumn Q ⟨i.val,h⟩ else 0
  let f : s → Fin d := fun i => ⟨i.val.val,i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin d => z.val) hij
  have heq : s.domRestrict v = fun i => matrixColumn Q (f i) := by
    funext i
    exact dif_pos i.property
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [heq]
    exact (matrix_columns_orthonormal Q hQ).comp f hf
  obtain ⟨b,hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=Fintype.card (Fin n)) hv
  let O : Matrix (Fin n) (Fin n) ℝ := fun i j => b j i
  have hO : O.transpose*O=1 := by
    ext i j
    have h := b.inner_eq_ite i j
    change (∑ k, b j k*b i k)=_ at h
    change (∑ k, b i k*b j k) = if i=j then (1:ℝ) else 0
    simpa only [mul_comm] using h
  refine ⟨O,hO,mul_eq_one_comm.mp hO,?_⟩
  ext i j
  have hj := hb (Fin.castLE hd j) (show Fin.castLE hd j ∈ s by exact j.isLt)
  have hcol : b (Fin.castLE hd j)=matrixColumn Q j := by
    simpa only [v, Fin.val_castLE, dif_pos j.isLt] using hj
  simp only [Matrix.mul_apply, headEmbedding]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) hcol

#assert_trust kernel matrix_columns_orthonormal
#assert_trust kernel exists_orthogonal_completion
#print axioms exists_orthogonal_completion
end NLA.Proofs.RE06.Repair
