import NLA.Proofs.RE05.Attained
import NLA.Proofs.RE05.SVDTotal
import Reviewed.RE05
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace IndependentRE05PrerequisitesGeometry
open scoped BigOperators
open NLA.Computation.LinearFamilyQuery NLA.Computation.NonadaptiveMatrixQuery

theorem literal_attainment {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q+1) → ℝ,
      Real.sqrt (∑ i,∑ j,(A i j-(∑ h,c h*P h i j))^2)=
        sInf {v : ℝ | ∃ d : Fin (q+1) → ℝ,v=Real.sqrt (∑ i,∑ j,(A i j-(∑ h,d h*P h i j))^2)} ∧
      ∀ d : Fin (q+1) → ℝ,
        sInf {v : ℝ | ∃ e : Fin (q+1) → ℝ,v=Real.sqrt (∑ i,∑ j,(A i j-(∑ h,e h*P h i j))^2)}≤
          Real.sqrt (∑ i,∑ j,(A i j-(∑ h,d h*P h i j))^2) :=
  NLA.Proofs.RE05.attained_optimum P A

theorem zero_dimension {q : ℕ} (P : Basis 0 q) (A : Square 0) :
    NLA.Computation.LinearFamilyQuery.optimum P A=0 := by
  obtain ⟨c,hc,_⟩ := NLA.Proofs.RE05.attained_optimum P A
  have hz : NLA.Computation.NonadaptiveMatrixQuery.frobenius A (represent P c)=0 := by simp [NLA.Computation.NonadaptiveMatrixQuery.frobenius,squaredFrobenius]
  exact hc.symm.trans hz

theorem dependent_zero_generators {n q : ℕ} (A : Square n) :
    NLA.Computation.LinearFamilyQuery.optimum (fun _ : Fin (q+1) => (0 : Square n)) A=NLA.Computation.NonadaptiveMatrixQuery.frobenius A 0 := by
  obtain ⟨c,hc,_⟩ := NLA.Proofs.RE05.attained_optimum (fun _ : Fin (q+1) => (0 : Square n)) A
  have hz : represent (fun _ : Fin (q+1) => (0 : Square n)) c=0 := by
    ext i j;simp [represent]
  rw [hz] at hc
  exact hc.symm

theorem zero_residual {n q : ℕ} (P : Basis n q) (c0 : Fin (q+1) → ℝ) :
    NLA.Computation.LinearFamilyQuery.optimum P (represent P c0)=0 := by
  obtain ⟨c,hc,hmin⟩ := NLA.Proofs.RE05.attained_optimum P (represent P c0)
  have hnonneg : 0≤NLA.Computation.LinearFamilyQuery.optimum P (represent P c0) := by
    rw [←hc];exact Real.sqrt_nonneg _
  have hbound := hmin c0
  have hz : NLA.Computation.NonadaptiveMatrixQuery.frobenius (represent P c0) (represent P c0)=0 := by
    simp [NLA.Computation.NonadaptiveMatrixQuery.frobenius,squaredFrobenius]
  rw [hz] at hbound
  exact le_antisymm hbound hnonneg

theorem literal_actual_chosen_SVD (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ) :
    NLA.Computation.SVDMachine.ValidSVD B (exactSVD B).U (exactSVD B).sigma (exactSVD B).V :=
  NLA.Proofs.RE05.svd_total a b B

theorem literal_reviewed_attained : NLA.ReviewedStatements.RE05.AttainedOptimum :=
  NLA.Proofs.RE05.attainedOptimum

theorem preserved_full_target_identity :
    NLA.Statements.RE05.Target=NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel literal_attainment
#assert_trust kernel zero_dimension
#assert_trust kernel dependent_zero_generators
#assert_trust kernel zero_residual
#assert_trust kernel literal_actual_chosen_SVD
#assert_trust kernel literal_reviewed_attained
#assert_trust kernel preserved_full_target_identity
#print axioms literal_attainment
#print axioms zero_dimension
#print axioms dependent_zero_generators
#print axioms zero_residual
#print axioms literal_actual_chosen_SVD
#print axioms literal_reviewed_attained
#print axioms preserved_full_target_identity
end IndependentRE05PrerequisitesGeometry
#assert_trust kernel NLA.Proofs.RE05.matrixVector
#assert_trust kernel NLA.Proofs.RE05.representationMap
#assert_trust kernel NLA.Proofs.RE05.frobenius_eq_norm
#assert_trust kernel NLA.Proofs.RE05.exists_frobenius_minimum
#assert_trust kernel NLA.Proofs.RE05.attained_optimum
#assert_trust kernel NLA.Proofs.RE05.attainedOptimum
#assert_trust kernel NLA.Proofs.RE05.svd_total
#print axioms NLA.Proofs.RE05.matrixVector
#print axioms NLA.Proofs.RE05.representationMap
#print axioms NLA.Proofs.RE05.frobenius_eq_norm
#print axioms NLA.Proofs.RE05.exists_frobenius_minimum
#print axioms NLA.Proofs.RE05.attained_optimum
#print axioms NLA.Proofs.RE05.attainedOptimum
#print axioms NLA.Proofs.RE05.svd_total
