import NLA.Proofs.TR26.FiniteJetPrimeImage
import NLA.Proofs.TR26.ComplementaryFactor
import NLA.Proofs.TR26.IsotropicFamilyFactor

/-! Actual nonisotropic factor consequences of the prime finite Taylor image.
Reduced multiplicity is deliberately not inferred from these facts. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem exists_finiteDoubleWronskianImage_isotropicFactor_ne_zero {d : ℕ} (hd : 2 ≤ d) :
    ∃ H : Parameter d, H ∈ finiteDoubleWronskianImage d ∧
      MvPolynomial.eval H (isotropicEvaluationFactor d) ≠ 0 := by
  obtain ⟨H, hN⟩ := affineNumerator_surjective_degreeLE d (X ^ 3)
    (by simp only [Polynomial.natDegree_X_pow]; omega)
  have hH : H ≠ 0 := by
    intro hz
    have hnz : affineNumerator H = 0 := by
      rw [hz]
      exact (affineNumeratorLinear d).map_zero
    exact (pow_ne_zero 3 (Polynomial.X_ne_zero : (X : Polynomial ℂ) ≠ 0)) (hN.symm.trans hnz)
  have hW : (affineWronskian H).eval 0 = 0 := by
    change ((affineNumerator H).derivative * affineDenominator d -
      affineNumerator H * (affineDenominator d).derivative).eval 0 = 0
    rw [hN]
    simp [Polynomial.derivative_pow]
  have hW' : (affineWronskian H).derivative.eval 0 = 0 := by
    change (polynomialWronskian (affineNumerator H) (affineDenominator d)).derivative.eval 0 = 0
    rw [polynomialWronskian_derivative, hN]
    simp [Polynomial.derivative_pow]
  refine ⟨H, ⟨hH, 0, ?_, hW, hW'⟩, ?_⟩
  · rw [affineDenominator_eval_zero]
    exact one_ne_zero
  · intro hz
    obtain ⟨r, hr, hNr⟩ := (eval_isotropicEvaluationFactor_eq_zero_iff d H).mp hz
    rw [hN] at hNr
    have hrne := denominator_root_nonzero hr
    exact (pow_ne_zero 3 hrne) (by simpa using hNr)

theorem isotropicFactor_not_mem_finiteDoubleWronskianImage_vanishingIdeal {d : ℕ} (hd : 2 ≤ d) :
    isotropicEvaluationFactor d ∉ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) := by
  obtain ⟨H, hH, hi⟩ := exists_finiteDoubleWronskianImage_isotropicFactor_ne_zero hd
  exact fun h => hi (h H hH)

theorem familyDiscriminant_mem_finiteDoubleWronskianImage_vanishingIdeal {d : ℕ} (hd : 2 ≤ d) :
    wronskianFamilyDiscriminant d ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) := by
  intro H hH
  obtain ⟨_, r, _, hW, hW'⟩ := hH
  apply (eval_wronskianFamilyDiscriminant_eq_zero_iff (by omega : 1 ≤ d) H).mpr
  have hb : binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) 1 r = 0 := by
    rw [binaryWronskian_affine_derivative_eval (by omega : 0 < d)]
    exact hW'
  have hv : binaryEval (binaryWronskian H) 1 r = 0 := by
    rw [binaryWronskian_affine_eval (by omega : 0 < d)]
    exact hW
  have ha := binary_euler_eval (binaryWronskian H) (binaryWronskianOver_homogeneous H) 1 r
  rw [hb, hv] at ha
  refine ⟨1, r, Or.inl one_ne_zero, ?_, hb⟩
  simpa using ha

theorem complementaryFactor_mem_finiteDoubleWronskianImage_vanishingIdeal {d : ℕ} (hd : 2 ≤ d)
    (Q : ParameterRing d)
    (hQ : wronskianFamilyDiscriminant d = isotropicEvaluationFactor d * Q) :
    Q ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) := by
  have hF := familyDiscriminant_mem_finiteDoubleWronskianImage_vanishingIdeal hd
  rw [hQ] at hF
  exact ((finiteDoubleWronskianImage_vanishingIdeal_isPrime hd).mem_or_mem hF).resolve_left
    (isotropicFactor_not_mem_finiteDoubleWronskianImage_vanishingIdeal hd)

theorem exists_irreducible_factor_mem_primeIdeal {R : Type*} [CommRing R] [IsDomain R]
    [WfDvdMonoid R] (I : Ideal R) (hI : I.IsPrime) (F : R) (hF0 : F ≠ 0) (hF : F ∈ I) :
    ∃ P : R, Irreducible P ∧ P ∣ F ∧ P ∈ I := by
  induction F using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hF0 rfl).elim
  | unit u hu => exact (hI.ne_top (I.eq_top_of_isUnit_mem hF hu)).elim
  | mul a p ha hp ih =>
    rcases hI.mem_or_mem hF with hpI | haI
    · exact ⟨p, hp, dvd_mul_right p a, hpI⟩
    · obtain ⟨q, hq, hqa, hqI⟩ := ih ha haI
      exact ⟨q, hq, hqa.trans (dvd_mul_left a p), hqI⟩

theorem exists_nonisotropic_irreducible_familyFactor {d : ℕ} (hd : 2 ≤ d) :
    ∃ P : ParameterRing d, Irreducible P ∧ P ∣ wronskianFamilyDiscriminant d ∧
      P ∈ MvPolynomial.vanishingIdeal ℂ (finiteDoubleWronskianImage d) ∧
      ¬ P ∣ isotropicEvaluationFactor d := by
  obtain ⟨Q, hQ0, _, _, hQ⟩ := exists_nonzero_homogeneous_complementary_factor hd
  have hQI := complementaryFactor_mem_finiteDoubleWronskianImage_vanishingIdeal hd Q hQ
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_irreducible_factor_mem_primeIdeal _
    (finiteDoubleWronskianImage_vanishingIdeal_isPrime hd) Q hQ0 hQI
  refine ⟨P, hP, hPQ.trans ?_, hPI, ?_⟩
  · rw [hQ]
    exact dvd_mul_left Q (isotropicEvaluationFactor d)
  · rintro ⟨R, hR⟩
    apply isotropicFactor_not_mem_finiteDoubleWronskianImage_vanishingIdeal hd
    rw [hR]
    exact Ideal.mul_mem_right _ _ hPI

#assert_trust kernel exists_finiteDoubleWronskianImage_isotropicFactor_ne_zero
#assert_trust kernel isotropicFactor_not_mem_finiteDoubleWronskianImage_vanishingIdeal
#assert_trust kernel familyDiscriminant_mem_finiteDoubleWronskianImage_vanishingIdeal
#assert_trust kernel complementaryFactor_mem_finiteDoubleWronskianImage_vanishingIdeal
#assert_trust kernel exists_irreducible_factor_mem_primeIdeal
#assert_trust kernel exists_nonisotropic_irreducible_familyFactor
#print axioms exists_nonisotropic_irreducible_familyFactor
end NLA.Proofs.TR26
