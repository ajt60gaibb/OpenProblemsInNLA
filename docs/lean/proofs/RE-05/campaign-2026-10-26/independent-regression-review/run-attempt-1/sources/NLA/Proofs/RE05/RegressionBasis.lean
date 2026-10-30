import NLA.Proofs.RE05.RegressionNormal
import NLA.Proofs.RE05.OrthonormalFamily

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

theorem represent_mem_span_iff {n q : ℕ} (P : Basis n q) (M : Square n) :
    M ∈ Submodule.span ℝ (Set.range P) ↔ ∃ c, represent P c = M := by
  simpa only [represent_eq_sum] using
    (Submodule.mem_span_range_iff_exists_fun ℝ (v := P) (x := M))

theorem represent_mem_span {n q : ℕ} (P : Basis n q) (c : Fin (q + 1) → ℝ) :
    represent P c ∈ Submodule.span ℝ (Set.range P) :=
  (represent_mem_span_iff P _).mpr ⟨c, rfl⟩

theorem represent_injective {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Function.Injective (represent P) := by
  intro c d h
  have hz : represent P (c - d) = 0 := by
    change (matrixRepresentationMap P) (c - d) = 0
    rw [map_sub]
    change represent P c - represent P d = 0
    rw [h, sub_self]
  have he := hP (c - d) (by
    intro i j
    change represent P (c - d) i j = 0
    rw [hz]
    rfl)
  funext j
  exact sub_eq_zero.mp (he j)

theorem matrixVector_represent_sum {n q : ℕ} (P : Basis n q) (c : Fin (q + 1) → ℝ) :
    matrixVector (represent P c) = ∑ j, c j • matrixVector (P j) := by
  change (matrixVectorMap n) (represent P c) = _
  rw [represent_eq_sum, map_sum]
  simp only [map_smul]
  rfl

/-- Coordinates of a matrix in the actual fold basis, derived from its literal
Frobenius inner products. This is analysis, not a replacement query basis. -/
def orthonormalCoordinates {n q : ℕ} (P : Basis n q) (M : Square n) :
    Fin (q + 1) → ℝ :=
  fun j => NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) M

theorem orthonormalCoordinates_represent {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (d : Fin (q + 1) → ℝ) :
    orthonormalCoordinates P (represent (orthonormalMember P) d) = d := by
  funext j
  unfold orthonormalCoordinates
  rw [← matrixVector_inner, matrixVector_represent_sum]
  exact (orthonormalMember_orthonormal P hP).inner_right_fintype d j

/-- Equality of spans is unconditional in the plan and random draw. -/
theorem represent_in_orthonormal_span {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (c : Fin (q + 1) → ℝ) :
    ∃ d, represent (orthonormalMember P) d = represent P c := by
  apply (represent_mem_span_iff (orthonormalMember P) _).mp
  rw [orthonormalMember_matrix_span P hP]
  exact represent_mem_span P c

theorem orthonormal_represent_in_supplied_span {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (d : Fin (q + 1) → ℝ) :
    ∃ c, represent P c = represent (orthonormalMember P) d := by
  apply (represent_mem_span_iff P _).mp
  rw [← orthonormalMember_matrix_span P hP]
  exact represent_mem_span (orthonormalMember P) d

theorem orthonormalCoordinates_reconstruct {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (M : Square n) (hM : M ∈ Submodule.span ℝ (Set.range P)) :
    represent (orthonormalMember P) (orthonormalCoordinates P M) = M := by
  have hE : M ∈ Submodule.span ℝ (Set.range (orthonormalMember P)) := by
    rw [orthonormalMember_matrix_span P hP]
    exact hM
  rcases (represent_mem_span_iff (orthonormalMember P) M).mp hE with ⟨d, hd⟩
  rw [← hd, orthonormalCoordinates_represent P hP]

theorem orthonormal_representation_inner {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (c d : Fin (q + 1) → ℝ) :
    NLA.Computation.LinearFamilyQuery.inner (represent (orthonormalMember P) c)
      (represent (orthonormalMember P) d) = dot c d := by
  rw [← matrixVector_inner, matrixVector_represent_sum, matrixVector_represent_sum]
  rw [sum_inner]
  simp only [real_inner_smul_left,
    (orthonormalMember_orthonormal P hP).inner_right_fintype d]
  rfl

theorem orthonormalCoordinates_inner {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (M N : Square n) (hM : M ∈ Submodule.span ℝ (Set.range P))
    (hN : N ∈ Submodule.span ℝ (Set.range P)) :
    dot (orthonormalCoordinates P M) (orthonormalCoordinates P N) =
      NLA.Computation.LinearFamilyQuery.inner M N := by
  rw [← orthonormal_representation_inner P hP,
    orthonormalCoordinates_reconstruct P hP M hM,
    orthonormalCoordinates_reconstruct P hP N hN]

/-- Exact congruence of the measured quadratic in the supplied and actual
fold coordinates; it needs no probability or nonsingularity event. -/
theorem gram_orthonormal_transport {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (c d : Fin (q + 1) → ℝ) :
    dot c (gram P plan *ᵥ d) =
      dot (orthonormalCoordinates P (represent P c))
        (gram (orthonormalMember P) plan *ᵥ orthonormalCoordinates P (represent P d)) := by
  rw [gram_quadratic, gram_quadratic]
  simp only [coefficientMeasurement_apply,
    orthonormalCoordinates_reconstruct P hP _ (represent_mem_span P _)]

theorem rhs_orthonormal_transport {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    dot c (rhs P plan responses) =
      dot (orthonormalCoordinates P (represent P c))
        (rhs (orthonormalMember P) plan responses) := by
  rw [rhs_linear, rhs_linear]
  simp only [coefficientMeasurement_apply,
    orthonormalCoordinates_reconstruct P hP _ (represent_mem_span P _)]

/-- An explicit lower-tail event for the literal measured Gram in the actual
fold basis. Its probability is not asserted here. -/
def OrthonormalMeasurementLowerBound {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (α : ℝ) : Prop :=
  ∀ d : Fin (q + 1) → ℝ,
    α * dot d d ≤ dot d (gram (orthonormalMember P) plan *ᵥ d)

theorem measurement_lower_bound_supplied {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (α : ℝ)
    (hLower : OrthonormalMeasurementLowerBound P plan α) (c : Fin (q + 1) → ℝ) :
    α * NLA.Computation.LinearFamilyQuery.inner (represent P c) (represent P c) ≤
      dot c (gram P plan *ᵥ c) := by
  have h := hLower (orthonormalCoordinates P (represent P c))
  rw [orthonormalCoordinates_inner P hP _ _ (represent_mem_span P c)
    (represent_mem_span P c), ← gram_orthonormal_transport P hP plan c c] at h
  exact h

/-- Full rank of the original supplied-basis Gram is derived on a positive
lower-tail event, rather than assumed as a new algorithm or Target premise. -/
theorem gram_posDef_of_lower_bound {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (α : ℝ) (hα : 0 < α)
    (hLower : OrthonormalMeasurementLowerBound P plan α) : (gram P plan).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (gram_hermitian P plan)
  intro c hc
  change 0 < dot c (gram P plan *ᵥ c)
  have hM : represent P c ≠ 0 := by
    intro hz
    apply hc
    apply represent_injective P hP
    rw [show represent P 0 = 0 by ext i j; simp [represent]]
    exact hz
  have hv : matrixVector (represent P c) ≠ 0 := by
    intro hz
    apply hM
    apply matrixVector_injective
    rw [show matrixVector (0 : Square n) = 0 by ext p; rfl]
    exact hz
  have he : 0 < NLA.Computation.LinearFamilyQuery.inner (represent P c) (represent P c) := by
    rw [← matrixVector_inner, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hv)
  exact (mul_pos hα he).trans_le (measurement_lower_bound_supplied P hP plan α hLower c)

theorem gram_full_rank_of_lower_bound {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (α : ℝ) (hα : 0 < α)
    (hLower : OrthonormalMeasurementLowerBound P plan α) :
    Matrix.rank (gram P plan) = q + 1 := by
  simpa using Matrix.rank_of_isUnit (gram P plan)
    (gram_posDef_of_lower_bound P hP plan α hα hLower).isUnit

theorem singleOutput_unique_of_lower_bound {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (responses : List (Fin n → ℝ))
    (α : ℝ) (hα : 0 < α) (hLower : OrthonormalMeasurementLowerBound P plan α)
    (c : Fin (q + 1) → ℝ) (hc : gram P plan *ᵥ c = rhs P plan responses) :
    c = singleOutput P plan responses := by
  apply Matrix.mulVec_injective_of_isUnit
    (gram_posDef_of_lower_bound P hP plan α hα hLower).isUnit
  exact hc.trans (singleOutput_normal P plan responses).symm

end NLA.Proofs.RE05
