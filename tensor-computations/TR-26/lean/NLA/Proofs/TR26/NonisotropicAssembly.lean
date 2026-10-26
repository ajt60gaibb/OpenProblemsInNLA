import NLA.Proofs.TR26.DiscriminantImageBounds
import NLA.Proofs.TR26.ComplementaryIrreducible
import NLA.Proofs.TR26.ProjectiveHypersurfaceClosure

/-! The complementary equation has the required reduced degree once the
finite-chart and full projective image ideals are identified. This geometric
identification is explicit here and is discharged separately. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem isotropicEvaluationFactor_eval_zero {d : ℕ} (hd : 1 ≤ d) :
    MvPolynomial.eval (0 : Parameter d) (isotropicEvaluationFactor d) = 0 := by
  obtain ⟨r,hr⟩ := Finset.card_pos.mp (by rw [denominatorRoots_card]; omega :
    0 < (denominatorRoots d).card)
  apply (eval_isotropicEvaluationFactor_eq_zero_iff d 0).mpr
  refine ⟨r,hr,?_⟩
  have hN : affineNumerator (0 : Parameter d) = 0 := (affineNumeratorLinear d).map_zero
  rw [hN,Polynomial.eval_zero]

theorem exists_fullImage_unique_nonisotropic_factor_of_ideal_eq {d : ℕ} (hd : 2 ≤ d)
    (hI : MvPolynomial.vanishingIdeal ℂ (NonisotropicImage d) =
      MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d)) :
    ∃ P : ParameterRing d, Irreducible P ∧ P ∣ wronskianFamilyDiscriminant d ∧
      ¬ P ∣ isotropicEvaluationFactor d ∧
      MvPolynomial.vanishingIdeal ℂ (NonisotropicImage d) = Ideal.span {P} ∧
      ∀ A : ParameterRing d, Irreducible A → A ∣ wronskianFamilyDiscriminant d →
        ¬ A ∣ isotropicEvaluationFactor d → Associated P A := by
  apply exists_unique_nonisotropic_irreducible_factor (NonisotropicImage d)
    (wronskianFamilyDiscriminant d) (isotropicEvaluationFactor d)
    (wronskianFamilyDiscriminant_ne_zero hd)
  · rw [hI]
    exact finiteDoubleWronskianImage_vanishingIdeal_isPrime hd
  · rw [hI]
    exact familyDiscriminant_mem_finiteDoubleWronskianImage_vanishingIdeal hd
  · rw [hI]
    exact isotropicFactor_not_mem_finiteDoubleWronskianImage_vanishingIdeal hd
  · exact isotropicEvaluationFactor_eval_zero (by omega)
  · exact familyDiscriminant_zero_away_isotropic_mem_nonisotropicImage hd

theorem nonisotropic_degree_of_fullImage_ideal_eq {d : ℕ} (hd : 2 ≤ d)
    (hI : MvPolynomial.vanishingIdeal ℂ (NonisotropicImage d) =
      MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d)) :
    HasReducedDegree d (6*(d-1)) (NonisotropicClosure d) := by
  obtain ⟨Q,hQ0,hQhom,hQdegree,hF⟩ := exists_nonzero_homogeneous_complementary_factor hd
  obtain ⟨P,hP,hPF,hPE,hspan,hunique⟩ :=
    exists_fullImage_unique_nonisotropic_factor_of_ideal_eq hd hI
  have hPI : P ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) := by
    rw [← hI,hspan]
    exact Ideal.subset_span (Set.mem_singleton P)
  have hQirr := complementaryFactor_irreducible_of_unique_factors hd Q P hF hP hPF hPI hPE hunique
  have hQI : Q ∈ MvPolynomial.vanishingIdeal ℂ (NonisotropicImage d) := by
    rw [hI]
    exact complementaryFactor_mem_finiteDoubleWronskianImage_vanishingIdeal hd Q hF
  have hclosure : NonisotropicClosure d =
      {H : Parameter d | H ≠ 0 ∧ MvPolynomial.eval H Q = 0} := by
    change polynomialProjectiveClosure (NonisotropicImage d) = _
    apply polynomialProjectiveClosure_eq_of_hypersurface_bounds Q
      (isotropicEvaluationFactor d) (NonisotropicImage d)
      (isotropicEvaluationFactor_isRelPrime_complementary hd Q hF).symm
      (isotropicEvaluationFactor_eval_zero (by omega))
    · intro H hH
      exact complementary_zero_away_isotropic_mem_nonisotropicImage hd Q hF H hH.1 hH.2.1 hH.2.2
    · intro H hH
      exact ⟨((nonisotropicImage_iff_binary_partials hd H).mp hH).1,hQI H hH⟩
  refine ⟨Q,hQ0,hQirr.squarefree,hQhom,?_⟩
  intro H hH
  rw [hclosure]
  exact and_iff_right hH

#assert_trust kernel isotropicEvaluationFactor_eval_zero
#assert_trust kernel exists_fullImage_unique_nonisotropic_factor_of_ideal_eq
#assert_trust kernel nonisotropic_degree_of_fullImage_ideal_eq
#print axioms nonisotropic_degree_of_fullImage_ideal_eq
end NLA.Proofs.TR26
