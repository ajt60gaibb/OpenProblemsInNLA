import NLA.Proofs.RE05.OrthonormalFold

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators

theorem orthonormalList_length {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (orthonormalList P).length = q + 1 := by
  rw [orthonormalList_eq_orderedPrefix P hP]
  simp [orderedPrefix]

/-- The model's optional list lookup is in bounds and returns exactly the
normalized vector at the same supplied index. -/
theorem orthonormalMember_eq_orderedMember {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (j : Fin (q + 1)) :
    orthonormalMember P j = orderedMember P j := by
  unfold orthonormalMember
  rw [orthonormalList_eq_orderedPrefix P hP]
  simp only [orderedPrefix, List.getElem?_ofFn]
  simp only [j.isLt, ↓reduceDIte, Option.getD_some]
  rfl

/-- Orthonormality of the members produced by the actual custom fold. -/
theorem orthonormalMember_orthonormal {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : Orthonormal ℝ (fun j => matrixVector (orthonormalMember P j)) := by
  simpa only [orthonormalMember_eq_orderedMember P hP] using
    orderedMember_orthonormal P hP

/-- Actual fold members retain exactly the supplied matrix span. -/
theorem orthonormalMember_span {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Submodule.span ℝ (Set.range (fun j => matrixVector (orthonormalMember P j))) =
      Submodule.span ℝ (Set.range (fun j => matrixVector (P j))) := by
  simp only [orthonormalMember_eq_orderedMember P hP, orderedMember,
    matrixVector_vectorMatrix]
  exact (InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) _).trans
    (InnerProductSpace.span_gramSchmidt ℝ _)

/-- The same span statement in the model's literal matrix vector space. -/
theorem orthonormalMember_matrix_span {n q : ℕ} (P : Basis n q)
    (hP : Independent P) :
    Submodule.span ℝ (Set.range (orthonormalMember P)) =
      Submodule.span ℝ (Set.range P) := by
  apply Submodule.map_injective_of_injective (f := matrixVectorMap n) matrixVector_injective
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    LinearMap.coe_mk, AddHom.coe_mk, matrixVectorMap] using orthonormalMember_span P hP

theorem orthonormalMember_inner {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (a b : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P a)
      (orthonormalMember P b) = if a = b then 1 else 0 := by
  rw [← matrixVector_inner]
  have h := orthonormalMember_orthonormal P hP
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl, real_inner_self_eq_norm_sq, h.1]
    norm_num
  · rw [if_neg hab]
    exact h.2 hab

/-- Exact trace of the literal leverage matrix, computed from the actual
fold outputs. Independence is the only mathematical hypothesis. -/
theorem leverage_trace {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ i : Fin n, leverage P i i) = (q + 1 : ℝ) := by
  unfold leverage
  rw [Finset.sum_comm]
  change (∑ j : Fin (q + 1),
    NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j)
      (orthonormalMember P j)) = _
  simp [orthonormalMember_inner P hP]

#assert_trust kernel orthonormalList_length
#assert_trust kernel orthonormalMember_eq_orderedMember
#assert_trust kernel orthonormalMember_orthonormal
#assert_trust kernel orthonormalMember_span
#assert_trust kernel orthonormalMember_matrix_span
#assert_trust kernel orthonormalMember_inner
#assert_trust kernel leverage_trace
#print axioms orthonormalMember_orthonormal
#print axioms orthonormalMember_span
#print axioms leverage_trace
end NLA.Proofs.RE05
