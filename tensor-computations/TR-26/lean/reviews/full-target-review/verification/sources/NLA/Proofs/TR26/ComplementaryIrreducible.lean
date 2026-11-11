import NLA.Proofs.TR26.NonisotropicMultiplicity
import NLA.Proofs.TR26.PrimeHypersurfaceFactor

/-! Factor algebra turning uniqueness and actual multiplicity one into an
irreducible complementary quotient. Every geometric premise is kept explicit
in this support theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem quotient_associated_irreducible_of_unique_factors
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (F E Q P : R) (hF : F = E * Q) (hQ0 : Q ≠ 0) (hrel : IsRelPrime E Q)
    (hP : Irreducible P) (hPF : P ∣ F) (hPE : ¬ P ∣ E) (hP2 : ¬ P ^ 2 ∣ F)
    (hunique : ∀ A : R, Irreducible A → A ∣ F → ¬ A ∣ E → Associated P A) :
    Associated P Q := by
  have hQF : Q ∣ F := by rw [hF]; exact dvd_mul_left Q E
  have hPQ : P ∣ Q := by
    rw [hF] at hPF
    exact (hP.prime.dvd_or_dvd hPF).resolve_left hPE
  obtain ⟨T, hQT⟩ := hPQ
  have hT0 : T ≠ 0 := by
    intro hz
    exact hQ0 (by rw [hQT, hz, mul_zero])
  have hT : IsUnit T := by
    by_contra hT
    obtain ⟨A, hA, hAT⟩ := WfDvdMonoid.exists_irreducible_factor hT hT0
    have hAQ : A ∣ Q := hAT.trans (by rw [hQT]; exact dvd_mul_left T P)
    have hAF : A ∣ F := hAQ.trans hQF
    have hAE : ¬ A ∣ E := by
      intro hAE
      exact hA.not_isUnit (hrel hAE hAQ)
    have hPT : P ∣ T := (hunique A hA hAF hAE).dvd.trans hAT
    obtain ⟨U, hTU⟩ := hPT
    have hP2Q : P ^ 2 ∣ Q := by
      refine ⟨U, ?_⟩
      rw [hQT, hTU, pow_two]
      ring
    exact hP2 (hP2Q.trans hQF)
  obtain ⟨u, hu⟩ := hT
  refine ⟨u, ?_⟩
  rw [hu]
  exact hQT.symm

theorem complementaryFactor_irreducible_of_unique_factors {d : ℕ} (hd : 2 ≤ d)
    (Q P : ParameterRing d)
    (hF : wronskianFamilyDiscriminant d = isotropicEvaluationFactor d * Q)
    (hP : Irreducible P) (hPF : P ∣ wronskianFamilyDiscriminant d)
    (hPI : P ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d))
    (hPE : ¬ P ∣ isotropicEvaluationFactor d)
    (hunique : ∀ A : ParameterRing d, Irreducible A → A ∣ wronskianFamilyDiscriminant d →
      ¬ A ∣ isotropicEvaluationFactor d → Associated P A) : Irreducible Q := by
  have hQ0 : Q ≠ 0 := by
    intro hz
    exact wronskianFamilyDiscriminant_ne_zero hd (by rw [hF, hz, mul_zero])
  have hassoc := quotient_associated_irreducible_of_unique_factors
    (wronskianFamilyDiscriminant d) (isotropicEvaluationFactor d) Q P hF hQ0
    (isotropicEvaluationFactor_isRelPrime_complementary hd Q hF) hP hPF hPE
    (finiteImageIdeal_square_not_dvd_family hd P hPI) hunique
  exact Associated.irreducible hassoc hP

#assert_trust kernel quotient_associated_irreducible_of_unique_factors
#assert_trust kernel complementaryFactor_irreducible_of_unique_factors
#print axioms complementaryFactor_irreducible_of_unique_factors
end NLA.Proofs.TR26
