import NLA.Proofs.TR26.FamilyDiscriminantNonzero
import NLA.Proofs.TR26.IsotropicFamilyFactor
import NLA.Proofs.TR26.HomogeneousQuotient

/-! A genuine nonzero homogeneous quotient after removing the actual reduced
isotropic factor. This is an exact algebraic degree result. It does not assert
squarefreeness or identify its zero set with the nonisotropic closure. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem exists_nonzero_homogeneous_complementary_factor {d : ℕ} (hd : 2 ≤ d) :
    ∃ Q : ParameterRing d,
      Q ≠ 0 ∧ Q.IsHomogeneous (6 * (d - 1)) ∧
      Q.totalDegree = 6 * (d - 1) ∧
      wronskianFamilyDiscriminant d = isotropicEvaluationFactor d * Q := by
  obtain ⟨Q, hQ⟩ := isotropicEvaluationFactor_dvd_wronskianFamilyDiscriminant (by omega : 1 ≤ d)
  have hQne : Q ≠ 0 := by
    intro hz
    apply wronskianFamilyDiscriminant_ne_zero hd
    rw [hQ, hz, mul_zero]
  have hdegree : 8 * d - 6 = 2 * d + 6 * (d - 1) := by omega
  have hhom : Q.IsHomogeneous (6 * (d - 1)) := by
    apply homogeneous_quotient (isotropicEvaluationFactor_homogeneous d)
      (isotropicEvaluationFactor_ne_zero d)
    rw [← hQ, ← hdegree]
    exact wronskianFamilyDiscriminant_homogeneous (by omega)
  exact ⟨Q, hQne, hhom, hhom.totalDegree hQne, hQ⟩

#assert_trust kernel exists_nonzero_homogeneous_complementary_factor
#print axioms exists_nonzero_homogeneous_complementary_factor
end NLA.Proofs.TR26
