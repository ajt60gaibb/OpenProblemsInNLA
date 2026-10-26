import NLA.Statements.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
open scoped BigOperators

/-- The actual matrix, flattened with its Frobenius Euclidean norm. -/
def matrixVector {n : ℕ} (A : Square n) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 (fun p => A p.1 p.2)

/-- The supplied coefficient representation is a genuine linear map. -/
def representationMap {n q : ℕ} (P : Basis n q) :
    (Fin (q + 1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n) where
  toFun c := matrixVector (represent P c)
  map_add' c d := by
    ext p
    simp [matrixVector, represent, add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    ext p
    simp [matrixVector, represent, Finset.mul_sum, mul_assoc]

/-- The shared exact Frobenius error is the flattened Euclidean distance. -/
theorem frobenius_eq_norm {n : ℕ} (A B : Square n) :
    frobenius A B = ‖matrixVector A - matrixVector B‖ := by
  have h : ‖matrixVector A - matrixVector B‖ ^ 2 = squaredFrobenius A B := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [matrixVector, squaredFrobenius, Fintype.sum_prod_type]
  rw [NLA.Computation.NonadaptiveMatrixQuery.frobenius, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- A finite supplied linear matrix family has a Frobenius minimizer, even
without independence of its supplied generators. -/
theorem exists_frobenius_minimum {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ, ∀ d : Fin (q + 1) → ℝ,
      frobenius A (represent P c) ≤ frobenius A (represent P d) := by
  let L := representationMap P
  let K := LinearMap.range L
  have hK : IsComplete (K : Set (EuclideanSpace ℝ (Fin n × Fin n))) :=
    K.closed_of_finiteDimensional.isComplete
  rcases K.exists_norm_eq_iInf_of_complete_subspace hK (matrixVector A) with
    ⟨v, hv, hmin⟩
  rcases hv with ⟨c, hc⟩
  refine ⟨c, fun d => ?_⟩
  rw [frobenius_eq_norm, frobenius_eq_norm]
  change ‖matrixVector A - L c‖ ≤ ‖matrixVector A - L d‖
  rw [hc, hmin]
  exact ciInf_le (bddBelow_def.mpr ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩)
    (⟨L d, ⟨d, rfl⟩⟩ : K)

/-- The literal shared sInf is attained and is below every actual family
error. No compact coefficient set or positive residual is assumed. -/
theorem attained_optimum {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.optimum P A ≤ frobenius A (represent P d) := by
  rcases exists_frobenius_minimum P A with ⟨c, hc⟩
  have hb : BddBelow {r : ℝ | ∃ d : Fin (q + 1) → ℝ,
      r = frobenius A (represent P d)} :=
    ⟨0, by rintro _ ⟨d, rfl⟩; exact Real.sqrt_nonneg _⟩
  have hm : frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A := by
    apply le_antisymm
    · exact le_csInf ⟨_, c, rfl⟩ (by rintro _ ⟨d, rfl⟩; exact hc d)
    · exact csInf_le hb ⟨c, rfl⟩
  exact ⟨c, hm, fun d => hm ▸ hc d⟩

/-- The complete unchanged attained-optimum clause of RE05. -/
theorem attainedOptimum : NLA.Statements.RE05.AttainedOptimum := by
  intro n q P A _
  exact attained_optimum P A

#assert_trust kernel frobenius_eq_norm
#assert_trust kernel exists_frobenius_minimum
#assert_trust kernel attained_optimum
#assert_trust kernel attainedOptimum
#print axioms attainedOptimum
end NLA.Proofs.RE05
