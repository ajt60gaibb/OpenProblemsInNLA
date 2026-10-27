import NLA.Proofs.TR26.FamilyDiscriminantEvaluation
import NLA.Proofs.TR26.IsotropicDivisibility
import NLA.Proofs.TR26.CommonRootWronskian

/-! The actual reduced isotropic evaluation product divides the actual family
discriminant. Exact multiplicity one in that discriminant remains a separate
obligation; it is not inferred merely from this divisibility statement. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem binaryDenominator_eval_one_eq_affine (d : ℕ) (r : ℂ) :
    binaryEval (binaryDenominator d) 1 r = (affineDenominator d).eval r := by
  simp [binaryEvalOver, binaryDenominatorOver, binaryVeroneseOver,
    affineDenominatorOver, Polynomial.eval_finsetSum, two_mul, pow_add]

theorem binaryNumerator_eval_one_eq_affine {d : ℕ} (H : Parameter d) (r : ℂ) :
    binaryEval (binaryNumerator H) 1 r = (affineNumerator H).eval r := by
  simp [binaryEvalOver, binaryNumeratorOver, binaryVeroneseOver,
    affineNumeratorOver, Polynomial.eval_finsetSum, pow_add, mul_assoc]

theorem binaryWronskian_partials_zero_at_common_root {d : ℕ} (H : Parameter d)
    (r : ℂ) (hD : (affineDenominator d).eval r = 0)
    (hN : (affineNumerator H).eval r = 0) :
    binaryEval (pderiv 0 (binaryWronskian H)) 1 r = 0 ∧
      binaryEval (pderiv 1 (binaryWronskian H)) 1 r = 0 := by
  have hPr : binaryEval (binaryNumerator H) 1 r = 0 :=
    (binaryNumerator_eval_one_eq_affine H r).trans hN
  have hQr : binaryEval (binaryDenominator d) 1 r = 0 :=
    (binaryDenominator_eval_one_eq_affine d r).trans hD
  have hJ := binaryJacobian_double_root_of_common_root (binaryNumerator H) (binaryDenominator d)
    (binaryNumeratorOver_homogeneous H) (binaryDenominatorOver_homogeneous ℂ d) r hPr hQr
  have hscale (i : Fin 2) (hi : binaryEval
      (pderiv i (binaryJacobian (binaryNumerator H) (binaryDenominator d))) 1 r = 0) :
      binaryEval (pderiv i (binaryWronskian H)) 1 r = 0 := by
    change binaryEval (pderiv i (C ((2 * d : ℂ)⁻¹) *
      binaryJacobian (binaryNumerator H) (binaryDenominator d))) 1 r = 0
    rw [pderiv_C_mul]
    change binaryEvalOver (C ((2 * d : ℂ)⁻¹) *
      pderiv i (binaryJacobian (binaryNumerator H) (binaryDenominator d))) 1 r = 0
    simp only [binaryEvalOver, map_mul, eval_C]
    change (2 * d : ℂ)⁻¹ * binaryEval
      (pderiv i (binaryJacobian (binaryNumerator H) (binaryDenominator d))) 1 r = 0
    rw [hi, mul_zero]
  exact ⟨hscale 0 hJ.1, hscale 1 hJ.2⟩

theorem wronskianFamilyDiscriminant_vanishes_on_isotropic_hyperplane {d : ℕ}
    (hd : 1 ≤ d) {r : ℂ} (hr : r ∈ denominatorRoots d) (H : Parameter d)
    (hN : (affineNumerator H).eval r = 0) :
    MvPolynomial.eval H (wronskianFamilyDiscriminant d) = 0 := by
  apply (eval_wronskianFamilyDiscriminant_eq_zero_iff hd H).mpr
  exact ⟨1, r, Or.inl one_ne_zero,
    binaryWronskian_partials_zero_at_common_root H r ((mem_denominatorRoots_iff d r).mp hr) hN⟩

theorem isotropicEvaluationFactor_dvd_wronskianFamilyDiscriminant {d : ℕ} (hd : 1 ≤ d) :
    isotropicEvaluationFactor d ∣ wronskianFamilyDiscriminant d := by
  apply isotropicEvaluationFactor_dvd_of_vanishing hd
  intro r hr H hN
  exact wronskianFamilyDiscriminant_vanishes_on_isotropic_hyperplane hd hr H hN

#assert_trust kernel binaryWronskian_partials_zero_at_common_root
#assert_trust kernel wronskianFamilyDiscriminant_vanishes_on_isotropic_hyperplane
#assert_trust kernel isotropicEvaluationFactor_dvd_wronskianFamilyDiscriminant
#print axioms isotropicEvaluationFactor_dvd_wronskianFamilyDiscriminant
end NLA.Proofs.TR26
