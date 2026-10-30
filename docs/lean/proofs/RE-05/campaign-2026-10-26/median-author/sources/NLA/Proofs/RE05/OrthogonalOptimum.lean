import NLA.Proofs.RE05.Attained

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
open scoped BigOperators InnerProductSpace

/-- Flattening preserves subtraction of actual matrices. -/
theorem matrixVector_sub {n : ℕ} (A B : Square n) :
    matrixVector (A - B) = matrixVector A - matrixVector B := by
  ext p
  rfl

/-- The actual Frobenius error distinguishes matrices, including empty ones. -/
theorem frobenius_eq_zero_iff {n : ℕ} (A B : Square n) :
    frobenius A B = 0 ↔ A = B := by
  rw [frobenius_eq_norm, norm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    ext i j
    exact congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin n) => v (i, j)) h
  · rintro rfl
    rfl

/-- The exact shared Frobenius metric satisfies the triangle inequality. -/
theorem frobenius_triangle {n : ℕ} (A B C : Square n) :
    frobenius A C ≤ frobenius A B + frobenius B C := by
  simp only [frobenius_eq_norm]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- A true minimizer has residual orthogonal to the entire actual supplied
linear matrix family. Generator independence is unnecessary. -/
theorem exists_orthogonal_optimum {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        ⟪matrixVector A - representationMap P c, representationMap P d⟫_ℝ = 0 := by
  let L := representationMap P
  let K := LinearMap.range L
  have hK : IsComplete (K : Set (EuclideanSpace ℝ (Fin n × Fin n))) :=
    K.closed_of_finiteDimensional.isComplete
  rcases K.exists_norm_eq_iInf_of_complete_subspace hK (matrixVector A) with
    ⟨v, hv, hmin⟩
  have horth := (K.norm_eq_iInf_iff_real_inner_eq_zero hv).mp hmin
  rcases hv with ⟨c, hc⟩
  rcases attained_optimum P A with ⟨c0, hc0, hmin0⟩
  have hle : frobenius A (represent P c) ≤ frobenius A (represent P c0) := by
    rw [frobenius_eq_norm, frobenius_eq_norm]
    change ‖matrixVector A - L c‖ ≤ ‖matrixVector A - L c0‖
    rw [hc, hmin]
    exact ciInf_le (bddBelow_def.mpr ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩)
      (⟨L c0, ⟨c0, rfl⟩⟩ : K)
  refine ⟨c, le_antisymm (hle.trans_eq hc0) (hmin0 c), ?_⟩
  intro d
  change ⟪matrixVector A - L c, L d⟫_ℝ = 0
  rw [hc]
  exact horth (L d) ⟨d, rfl⟩

/-- The genuine optimal matrix satisfies the exact squared-error Pythagorean
identity against every supplied coefficient vector. This keeps the norm/square
conversion explicit for the later pure relative approximation guarantee. -/
theorem exists_pythagorean_optimum {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        frobenius A (represent P d) ^ 2 =
          NLA.Computation.LinearFamilyQuery.optimum P A ^ 2 +
          frobenius (represent P c) (represent P d) ^ 2 := by
  rcases exists_orthogonal_optimum P A with ⟨c, hc, horth⟩
  refine ⟨c, hc, fun d => ?_⟩
  have h := horth (c - d)
  rw [map_sub] at h
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (matrixVector A - representationMap P c)
    (representationMap P c - representationMap P d) h
  rw [show matrixVector A - representationMap P c +
      (representationMap P c - representationMap P d) =
      matrixVector A - representationMap P d by abel] at hp
  rw [← hc]
  simpa [frobenius_eq_norm, representationMap, pow_two] using hp

/-- Zero genuine optimum is equivalent to exact membership in the actual
supplied linear family; no conditioning or nonzero residual is imposed. -/
theorem optimum_eq_zero_iff {n q : ℕ} (P : Basis n q) (A : Square n) :
    NLA.Computation.LinearFamilyQuery.optimum P A = 0 ↔
      ∃ c : Fin (q + 1) → ℝ, A = represent P c := by
  rcases attained_optimum P A with ⟨c, hc, hmin⟩
  constructor
  · intro hz
    exact ⟨c, (frobenius_eq_zero_iff A _).mp (hc.trans hz)⟩
  · rintro ⟨d, hd⟩
    have hzero := (frobenius_eq_zero_iff A (represent P d)).mpr hd
    have hnonneg : 0 ≤ NLA.Computation.LinearFamilyQuery.optimum P A := by
      rw [← hc]
      exact Real.sqrt_nonneg _
    exact le_antisymm ((hmin d).trans_eq hzero) hnonneg

#assert_trust kernel matrixVector_sub
#assert_trust kernel frobenius_eq_zero_iff
#assert_trust kernel frobenius_triangle
#assert_trust kernel exists_orthogonal_optimum
#assert_trust kernel exists_pythagorean_optimum
#assert_trust kernel optimum_eq_zero_iff
#print axioms exists_pythagorean_optimum
#print axioms optimum_eq_zero_iff
end NLA.Proofs.RE05
