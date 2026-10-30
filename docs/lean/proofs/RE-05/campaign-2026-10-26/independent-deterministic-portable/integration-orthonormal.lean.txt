import NLA.Proofs.RE05.OrthonormalFamily
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace RE05OrthonormalGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators

theorem actual_member_orthonormal {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Orthonormal ℝ (fun j : Fin (q + 1) =>
      (WithLp.toLp 2 (fun p : Fin n × Fin n => orthonormalMember P j p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin n))) :=
  NLA.Proofs.RE05.orthonormalMember_orthonormal P hP

theorem actual_member_span {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Submodule.span ℝ (Set.range (orthonormalMember P)) =
      Submodule.span ℝ (Set.range P) :=
  NLA.Proofs.RE05.orthonormalMember_matrix_span P hP

theorem actual_member_inner {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (a b : Fin (q + 1)) :
    (∑ i : Fin n, ∑ k : Fin n, orthonormalMember P a i k * orthonormalMember P b i k) =
      if a = b then 1 else 0 := NLA.Proofs.RE05.orthonormalMember_inner P hP a b

theorem literal_leverage_trace {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ i : Fin n, ∑ j : Fin (q + 1), ∑ h : Fin n,
      orthonormalMember P j i h * orthonormalMember P j i h) = (q + 1 : ℝ) :=
  NLA.Proofs.RE05.leverage_trace P hP

theorem literal_supplied_fold_lookup {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (j : Fin (q + 1)) :
    (((List.finRange (q + 1)).foldl (fun accepted a =>
      let v : Square n := fun i k => P a i k -
        ∑ E ∈ accepted.toFinset, NLA.Computation.LinearFamilyQuery.inner (P a) E * E i k
      let scale := NLA.Computation.LinearFamilyQuery.norm n v
      accepted ++ [if scale = 0 then (0 : Square n) else fun i k => v i k / scale]) [])[j.val]?).getD 0 =
        NLA.Proofs.RE05.orderedMember P j :=
  NLA.Proofs.RE05.orthonormalMember_eq_orderedMember P hP j

theorem zero_normalization (n : ℕ) :
    NLA.Proofs.RE05.normalizeMatrix (0 : Square n) = 0 := by
  simp [NLA.Proofs.RE05.normalizeMatrix, NLA.Computation.LinearFamilyQuery.norm,
    NLA.Computation.LinearFamilyQuery.inner]

def unitFamily : Basis 1 0 := fun _ _ _ => 1

theorem unitFamily_independent : Independent unitFamily := by
  intro c hc a
  have ha : a = 0 := by
    apply Fin.ext
    have hlt := a.isLt
    change a.val < 1 at hlt
    change a.val = 0
    omega
  subst a
  have h := hc 0 0
  simpa [unitFamily] using h

theorem unitFamily_trace : (∑ i : Fin 1, leverage unitFamily i i) = 1 := by
  simpa using NLA.Proofs.RE05.leverage_trace unitFamily unitFamily_independent

theorem preserved_target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel actual_member_orthonormal
#assert_trust kernel actual_member_span
#assert_trust kernel actual_member_inner
#assert_trust kernel literal_leverage_trace
#assert_trust kernel literal_supplied_fold_lookup
#assert_trust kernel zero_normalization
#assert_trust kernel unitFamily
#assert_trust kernel unitFamily_independent
#assert_trust kernel unitFamily_trace
#assert_trust kernel preserved_target_identity
#print axioms actual_member_orthonormal
#print axioms actual_member_span
#print axioms actual_member_inner
#print axioms literal_leverage_trace
#print axioms literal_supplied_fold_lookup
#print axioms zero_normalization
#print axioms unitFamily_trace
#print axioms preserved_target_identity
end RE05OrthonormalGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.vectorMatrix
#print axioms NLA.Proofs.RE05.vectorMatrix
#assert_trust kernel NLA.Proofs.RE05.vectorMatrix_matrixVector
#print axioms NLA.Proofs.RE05.vectorMatrix_matrixVector
#assert_trust kernel NLA.Proofs.RE05.matrixVector_vectorMatrix
#print axioms NLA.Proofs.RE05.matrixVector_vectorMatrix
#assert_trust kernel NLA.Proofs.RE05.matrixVector_injective
#print axioms NLA.Proofs.RE05.matrixVector_injective
#assert_trust kernel NLA.Proofs.RE05.matrixVectorMap
#print axioms NLA.Proofs.RE05.matrixVectorMap
#assert_trust kernel NLA.Proofs.RE05.matrixVector_inner
#print axioms NLA.Proofs.RE05.matrixVector_inner
#assert_trust kernel NLA.Proofs.RE05.matrixVector_norm
#print axioms NLA.Proofs.RE05.matrixVector_norm
#assert_trust kernel NLA.Proofs.RE05.independent_matrixVector
#print axioms NLA.Proofs.RE05.independent_matrixVector
#assert_trust kernel NLA.Proofs.RE05.orderedMember
#print axioms NLA.Proofs.RE05.orderedMember
#assert_trust kernel NLA.Proofs.RE05.orderedMember_orthonormal
#print axioms NLA.Proofs.RE05.orderedMember_orthonormal
#assert_trust kernel NLA.Proofs.RE05.orderedMember_injective
#print axioms NLA.Proofs.RE05.orderedMember_injective
#assert_trust kernel NLA.Proofs.RE05.normalized_starProjection
#print axioms NLA.Proofs.RE05.normalized_starProjection
#assert_trust kernel NLA.Proofs.RE05.ordered_residual
#print axioms NLA.Proofs.RE05.ordered_residual
#assert_trust kernel NLA.Proofs.RE05.normalizeMatrix
#print axioms NLA.Proofs.RE05.normalizeMatrix
#assert_trust kernel NLA.Proofs.RE05.matrixVector_normalize
#print axioms NLA.Proofs.RE05.matrixVector_normalize
#assert_trust kernel NLA.Proofs.RE05.orthonormalStep
#print axioms NLA.Proofs.RE05.orthonormalStep
#assert_trust kernel NLA.Proofs.RE05.orthonormalList_eq_fold
#print axioms NLA.Proofs.RE05.orthonormalList_eq_fold
#assert_trust kernel NLA.Proofs.RE05.orderedPrefix
#print axioms NLA.Proofs.RE05.orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.inputPrefix
#print axioms NLA.Proofs.RE05.inputPrefix
#assert_trust kernel NLA.Proofs.RE05.orderedPrefix_nodup
#print axioms NLA.Proofs.RE05.orderedPrefix_nodup
#assert_trust kernel NLA.Proofs.RE05.sum_orderedPrefix
#print axioms NLA.Proofs.RE05.sum_orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.orthonormalStep_orderedPrefix
#print axioms NLA.Proofs.RE05.orthonormalStep_orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.inputPrefix_succ
#print axioms NLA.Proofs.RE05.inputPrefix_succ
#assert_trust kernel NLA.Proofs.RE05.orderedPrefix_succ
#print axioms NLA.Proofs.RE05.orderedPrefix_succ
#assert_trust kernel NLA.Proofs.RE05.orthonormal_fold_prefix
#print axioms NLA.Proofs.RE05.orthonormal_fold_prefix
#assert_trust kernel NLA.Proofs.RE05.orthonormalList_eq_orderedPrefix
#print axioms NLA.Proofs.RE05.orthonormalList_eq_orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.orthonormalList_length
#print axioms NLA.Proofs.RE05.orthonormalList_length
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_eq_orderedMember
#print axioms NLA.Proofs.RE05.orthonormalMember_eq_orderedMember
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_orthonormal
#print axioms NLA.Proofs.RE05.orthonormalMember_orthonormal
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_span
#print axioms NLA.Proofs.RE05.orthonormalMember_span
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_matrix_span
#print axioms NLA.Proofs.RE05.orthonormalMember_matrix_span
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_inner
#print axioms NLA.Proofs.RE05.orthonormalMember_inner
#assert_trust kernel NLA.Proofs.RE05.leverage_trace
#print axioms NLA.Proofs.RE05.leverage_trace
