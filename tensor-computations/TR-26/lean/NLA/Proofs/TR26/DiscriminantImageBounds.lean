import NLA.Proofs.TR26.ProjectiveRamification
import NLA.Proofs.TR26.IsotropicDegree
import NLA.Proofs.TR26.FamilyDiscriminantEvaluation

/-! Exact raw-image bounds for the actual fixed-degree family discriminant.
These do not identify a reduced complementary equation or its closure. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem familyDiscriminant_zero_iff_exists_ramification {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (hH : H ≠ 0) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0 ↔
      ∃ z : CurveVector d, Ramification d z H := by
  constructor
  · intro hf
    apply (exists_ramification_iff_binary_partials hd H).mpr
    exact ⟨hH,(eval_wronskianFamilyDiscriminant_eq_zero_iff (by omega) H).mp hf⟩
  · intro hR
    apply (eval_wronskianFamilyDiscriminant_eq_zero_iff (by omega) H).mpr
    exact ((exists_ramification_iff_binary_partials hd H).mp hR).2

theorem familyDiscriminant_zero_iff_raw_images {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (hH : H ≠ 0) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0 ↔
      H ∈ IsotropicImage d ∨ H ∈ NonisotropicImage d := by
  rw [familyDiscriminant_zero_iff_exists_ramification hd H hH]
  constructor
  · rintro ⟨z,hR⟩
    by_cases hD : denominator z = 0
    · exact Or.inl ⟨z,hR,hD⟩
    · exact Or.inr ⟨z,hR,hD⟩
  · rintro (⟨z,hR,_⟩ | ⟨z,hR,_⟩) <;> exact ⟨z,hR⟩

theorem nonisotropicImage_familyDiscriminant_zero {d : ℕ} (hd : 2 ≤ d)
    (H : Parameter d) (hH : H ∈ NonisotropicImage d) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0 := by
  obtain ⟨z,hR,hD⟩ := hH
  exact (familyDiscriminant_zero_iff_exists_ramification hd H hR.1.2.1).mpr ⟨z,hR⟩

theorem familyDiscriminant_zero_away_isotropic_mem_nonisotropicImage
    {d : ℕ} (hd : 2 ≤ d) (H : Parameter d) (hH : H ≠ 0)
    (hf : MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0)
    (hE : MvPolynomial.eval H (isotropicEvaluationFactor d) ≠ 0) :
    H ∈ NonisotropicImage d := by
  obtain ⟨z,hR⟩ := (familyDiscriminant_zero_iff_exists_ramification hd H hH).mp hf
  refine ⟨z,hR,?_⟩
  intro hD
  exact hE (isotropicImage_evaluationFactor_zero d (by omega) H ⟨z,hR,hD⟩)

theorem complementary_zero_away_isotropic_mem_nonisotropicImage
    {d : ℕ} (hd : 2 ≤ d) (Q : ParameterRing d)
    (hfactor : wronskianFamilyDiscriminant d = isotropicEvaluationFactor d * Q)
    (H : Parameter d) (hH : H ≠ 0) (hQ : MvPolynomial.eval H Q = 0)
    (hE : MvPolynomial.eval H (isotropicEvaluationFactor d) ≠ 0) :
    H ∈ NonisotropicImage d := by
  apply familyDiscriminant_zero_away_isotropic_mem_nonisotropicImage hd H hH _ hE
  rw [hfactor,map_mul,hQ,mul_zero]

#assert_trust kernel familyDiscriminant_zero_iff_exists_ramification
#assert_trust kernel familyDiscriminant_zero_iff_raw_images
#assert_trust kernel nonisotropicImage_familyDiscriminant_zero
#assert_trust kernel familyDiscriminant_zero_away_isotropic_mem_nonisotropicImage
#assert_trust kernel complementary_zero_away_isotropic_mem_nonisotropicImage
#print axioms familyDiscriminant_zero_iff_raw_images
end NLA.Proofs.TR26
