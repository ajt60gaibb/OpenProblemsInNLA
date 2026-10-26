import NLA.Proofs.RE05.SelectedCharge
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace RE05SpectralGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
open NLA.Computation.SVDMachine
open scoped BigOperators Matrix

theorem literal_leverage_symmetric {n q : ℕ} (P : Basis n q) :
    Matrix.IsSymm (fun i k => ∑ j : Fin (q + 1), ∑ h : Fin n,
      orthonormalMember P j i h * orthonormalMember P j k h : Square n) :=
  NLA.Proofs.RE05.leverage_symmetric P

theorem literal_leverage_psd {n q : ℕ} (P : Basis n q) :
    Matrix.PosSemidef (fun i k => ∑ j : Fin (q + 1), ∑ h : Fin n,
      orthonormalMember P j i h * orthonormalMember P j k h : Square n) :=
  NLA.Proofs.RE05.leverage_posSemidef P

theorem literal_actual_singular_sum {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ j : Fin n, (exactSVD (leverage P)).sigma
      (Fin.cast (Nat.min_self n).symm j)) = (q + 1 : ℝ) :=
  NLA.Proofs.RE05.exactSVD_leverage_sum P hP

theorem literal_actual_selected_charge {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (ε : ℝ) :
    (((List.finRange n).filter (fun j => threshold q (squaredAccuracy ε) <
      (exactSVD (leverage P)).sigma (Fin.cast (Nat.min_self n).symm j))).length : ℝ) *
        threshold q (squaredAccuracy ε) ≤ (q + 1 : ℕ) :=
  NLA.Proofs.RE05.selectedCount_charge P hP ε

theorem literal_source_query_bound {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ ω : ℕ → ℝ, ((batchQueries (plans P ε ω)).length : ℝ) ≤
      15 * (2 * Real.sqrt ((q + 1 : ℕ) *
        (16 * Real.log (20 * (q + 1 : ℕ)) + 160 / (ε / 9))) +
        8 * Real.log (20 * (q + 1 : ℕ)) + 1) :=
  NLA.Proofs.RE05.sourceQueryBound P hP ε hε

theorem arbitrary_valid_psd_trace {n : ℕ} (B U V : Square n)
    (sigma : Fin (min n n) → ℝ) (h : ValidSVD B U sigma V) (hB : B.PosSemidef) :
    (∑ i : Fin n, B i i) =
      ∑ j : Fin n, sigma (Fin.cast (Nat.min_self n).symm j) :=
  NLA.Proofs.RE05.validSVD_posSemidef_trace h hB

theorem actual_zero_singular_sum (n : ℕ) :
    (∑ j : Fin n, (exactSVD (0 : Square n)).sigma
      (Fin.cast (Nat.min_self n).symm j)) = 0 := by
  have h := NLA.Proofs.RE05.exactSVD_posSemidef_trace (0 : Square n)
    (Matrix.PosSemidef.zero)
  simpa using h.symm

/-- Opposite full bases at zero singular values are permitted by the actual
relation; the spectral theorem must not force their equality. -/
theorem zero_opposite_valid (n : ℕ) :
    ValidSVD (0 : Square n) (1 : Square n) (fun _ => 0) (-1 : Square n) := by
  have hI (i j : Fin n) :
      (∑ a : Fin n, (1 : Square n) a i * (1 : Square n) a j) =
        if i = j then 1 else 0 := by simp [Matrix.one_apply, eq_comm]
  refine ⟨hI, ?_, fun _ => le_rfl, fun _ _ _ => le_rfl, ?_⟩
  · intro i j
    simpa only [Matrix.neg_apply, neg_mul_neg] using hI i j
  · intro i j
    simp

theorem zero_opposite_trace (n : ℕ) :
    (0 : Square n).trace =
      ∑ j : Fin n, (fun _ : Fin (min n n) => (0 : ℝ))
        (Fin.cast (Nat.min_self n).symm j) :=
  NLA.Proofs.RE05.validSVD_posSemidef_trace (zero_opposite_valid n) Matrix.PosSemidef.zero

theorem arbitrary_negative_threshold {n : ℕ} (sigma : Fin n → ℝ)
    (hs : ∀ j, 0 ≤ sigma j) :
    (((List.finRange n).filter fun j => (-1 : ℝ) < sigma j).length : ℝ) * (-1) ≤
      ∑ j : Fin n, sigma j := NLA.Proofs.RE05.filter_selected_charge sigma hs (-1)

theorem preserved_full_target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel literal_leverage_symmetric
#assert_trust kernel literal_leverage_psd
#assert_trust kernel literal_actual_singular_sum
#assert_trust kernel literal_actual_selected_charge
#assert_trust kernel literal_source_query_bound
#assert_trust kernel arbitrary_valid_psd_trace
#assert_trust kernel actual_zero_singular_sum
#assert_trust kernel zero_opposite_valid
#assert_trust kernel zero_opposite_trace
#assert_trust kernel arbitrary_negative_threshold
#assert_trust kernel preserved_full_target_identity
#print axioms literal_leverage_symmetric
#print axioms literal_leverage_psd
#print axioms literal_actual_singular_sum
#print axioms literal_actual_selected_charge
#print axioms literal_source_query_bound
#print axioms arbitrary_valid_psd_trace
#print axioms actual_zero_singular_sum
#print axioms zero_opposite_valid
#print axioms zero_opposite_trace
#print axioms arbitrary_negative_threshold
#print axioms preserved_full_target_identity
end RE05SpectralGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.leverage_eq_sum_gram
#print axioms NLA.Proofs.RE05.leverage_eq_sum_gram
#assert_trust kernel NLA.Proofs.RE05.leverage_symmetric
#print axioms NLA.Proofs.RE05.leverage_symmetric
#assert_trust kernel NLA.Proofs.RE05.leverage_posSemidef
#print axioms NLA.Proofs.RE05.leverage_posSemidef
#assert_trust kernel NLA.Proofs.RE05.squareSingularValues
#print axioms NLA.Proofs.RE05.squareSingularValues
#assert_trust kernel NLA.Proofs.RE05.validSVD_square_reconstruct
#print axioms NLA.Proofs.RE05.validSVD_square_reconstruct
#assert_trust kernel NLA.Proofs.RE05.validSVD_square_mulVec_right
#print axioms NLA.Proofs.RE05.validSVD_square_mulVec_right
#assert_trust kernel NLA.Proofs.RE05.validSVD_square_transpose_mulVec_left
#print axioms NLA.Proofs.RE05.validSVD_square_transpose_mulVec_left
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_weighted_column
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_weighted_column
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_trace
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_trace
#assert_trust kernel NLA.Proofs.RE05.exactSVD_posSemidef_trace
#print axioms NLA.Proofs.RE05.exactSVD_posSemidef_trace
#assert_trust kernel NLA.Proofs.RE05.exactSVD_leverage_sum
#print axioms NLA.Proofs.RE05.exactSVD_leverage_sum
#assert_trust kernel NLA.Proofs.RE05.filter_selected_charge
#print axioms NLA.Proofs.RE05.filter_selected_charge
#assert_trust kernel NLA.Proofs.RE05.selectedCount_charge
#print axioms NLA.Proofs.RE05.selectedCount_charge
#assert_trust kernel NLA.Proofs.RE05.sourceQueryBound
#print axioms NLA.Proofs.RE05.sourceQueryBound
