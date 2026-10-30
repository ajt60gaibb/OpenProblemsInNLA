import NLA.Proofs.RE05.CoefficientError
import NLA.Proofs.RE05.OrthogonalOptimum

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

theorem represent_sub {n q : ℕ} (P : Basis n q) (c d : Fin (q + 1) → ℝ) :
    represent P (c - d) = represent P c - represent P d :=
  (matrixRepresentationMap P).map_sub c d

/-- Exact Frobenius coefficient isometry in the actual fold basis. -/
theorem orthonormal_frobenius_sq {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (c d : Fin (q + 1) → ℝ) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius
      (represent (orthonormalMember P) c) (represent (orthonormalMember P) d) ^ 2 =
      dot (d - c) (d - c) := by
  rw [frobenius_eq_norm, norm_sub_rev, ← matrixVector_sub, ← represent_sub,
    ← real_inner_self_eq_norm_sq, matrixVector_inner, orthonormal_representation_inner P hP]

/-- An analysis optimum is chosen from P and A before any plan or random
draw. It is not algorithm input. Its residual is truly Frobenius-orthogonal
to every actual fold combination, and its Pythagorean error uses actual Opt. -/
theorem exists_orthonormal_analysis_optimum {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) c) = optimum P A ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.inner (A - represent (orthonormalMember P) c)
          (represent (orthonormalMember P) d) = 0) ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent (orthonormalMember P) d) ^ 2 =
            optimum P A ^ 2 + dot (d - c) (d - c) := by
  rcases exists_orthogonal_optimum P A with ⟨cP, hcP, horthP⟩
  rcases represent_in_orthonormal_span P hP cP with ⟨c, hc⟩
  have hmin : NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent (orthonormalMember P) c) = optimum P A := by rw [hc]; exact hcP
  have horth (d : Fin (q + 1) → ℝ) :
      NLA.Computation.LinearFamilyQuery.inner (A - represent (orthonormalMember P) c)
        (represent (orthonormalMember P) d) = 0 := by
    rcases orthonormal_represent_in_supplied_span P hP d with ⟨e, he⟩
    have h := horthP e
    change ⟪matrixVector A - matrixVector (represent P cP), matrixVector (represent P e)⟫_ℝ = 0 at h
    rw [← hc, he, ← matrixVector_sub, matrixVector_inner] at h
    exact h
  refine ⟨c, hmin, horth, fun d => ?_⟩
  have h := horth (c - d)
  rw [← matrixVector_inner, matrixVector_sub, represent_sub, matrixVector_sub] at h
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (matrixVector A - matrixVector (represent (orthonormalMember P) c))
    (matrixVector (represent (orthonormalMember P) c) -
      matrixVector (represent (orthonormalMember P) d)) h
  rw [show matrixVector A - matrixVector (represent (orthonormalMember P) c) +
      (matrixVector (represent (orthonormalMember P) c) -
        matrixVector (represent (orthonormalMember P) d)) =
          matrixVector A - matrixVector (represent (orthonormalMember P) d) by abel] at hp
  have hdist : NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 +
        NLA.Computation.NonadaptiveMatrixQuery.frobenius (represent (orthonormalMember P) c)
          (represent (orthonormalMember P) d) ^ 2 := by
    rw [← hmin]
    simpa only [frobenius_eq_norm, pow_two] using hp
  rwa [orthonormal_frobenius_sq P hP] at hdist

end NLA.Proofs.RE05
