import NLA.Proofs.TR26.NonisotropicTransverseWitness
import NLA.Proofs.TR26.IsotropicMultiplicity

/-! The actual nonisotropic component occurs with multiplicity one. Any
polynomial vanishing on the finite Taylor image cannot divide the family
discriminant to second order, by its explicit transverse ordinary-double point. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem finiteImageIdeal_square_not_dvd_family {d : ℕ} (hd : 2 ≤ d)
    (P : ParameterRing d)
    (hP : P ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d)) :
    ¬ P ^ 2 ∣ wronskianFamilyDiscriminant d := by
  obtain ⟨H, K, δ, hfinite, _, hder, hδ⟩ := exists_nonisotropic_family_transverse hd
  intro hdiv
  have hzero := hasDerivAt_eval_line_zero_of_square_dvd P (wronskianFamilyDiscriminant d)
    H K hdiv (hP H hfinite)
  exact hδ (hder.unique hzero)

theorem exists_simple_nonisotropic_irreducible_familyFactor {d : ℕ} (hd : 2 ≤ d) :
    ∃ P : ParameterRing d, Irreducible P ∧ P ∣ wronskianFamilyDiscriminant d ∧
      P ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) ∧
      ¬ P ∣ isotropicEvaluationFactor d ∧ ¬ P ^ 2 ∣ wronskianFamilyDiscriminant d := by
  obtain ⟨P, hP, hPF, hPI, hPE⟩ := exists_nonisotropic_irreducible_familyFactor hd
  exact ⟨P, hP, hPF, hPI, hPE, finiteImageIdeal_square_not_dvd_family hd P hPI⟩

#assert_trust kernel finiteImageIdeal_square_not_dvd_family
#assert_trust kernel exists_simple_nonisotropic_irreducible_familyFactor
#print axioms exists_simple_nonisotropic_irreducible_familyFactor
end NLA.Proofs.TR26
