import NLA.Proofs.TR26.IsotropicImageContainment
import NLA.Proofs.TR26.WronskianCharts

/-! The literal reduced-degree endpoint for the raw isotropic image. The
other (nonisotropic closure) endpoint of TR-26 remains a separate theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem numerator_root_mem_isotropicImage (d : ℕ) (hd : 1 ≤ d)
    (H : Parameter d) (hH : H ≠ 0) (t : ℂ)
    (hD : (affineDenominator d).eval t = 0)
    (hN : (affineNumerator H).eval t = 0) : H ∈ IsotropicImage d := by
  have hW : (affineWronskian H).eval t = 0 := by
    simp [affineWronskianOver,hD,hN]
  have hW' : (affineWronskian H).derivative.eval t = 0 := by
    have hh := (binaryWronskian_partials_zero_at_common_root H t hD hN).2
    rwa [binaryWronskian_affine_derivative_eval (by omega : 0 < d)] at hh
  refine ⟨affineChartVector d 1 t,
    affineChart_ramification_of_double_root (by omega : 0 < d) 1 t one_ne_zero H hH hW hW',?_⟩
  rw [denominator_affineChartVector,one_pow,one_mul,hD]

theorem isotropicImage_iff_evaluationFactor_zero (d : ℕ) (hd : 1 ≤ d)
    (H : Parameter d) (hH : H ≠ 0) :
    H ∈ IsotropicImage d ↔ MvPolynomial.eval H (isotropicEvaluationFactor d) = 0 := by
  constructor
  · exact isotropicImage_evaluationFactor_zero d hd H
  · intro hzero
    obtain ⟨t,ht,hN⟩ := (eval_isotropicEvaluationFactor_eq_zero_iff d H).mp hzero
    exact numerator_root_mem_isotropicImage d hd H hH t
      ((mem_denominatorRoots_iff d t).mp ht) hN

theorem isotropic_degree (d : ℕ) (hd : 2 ≤ d) :
    HasReducedDegree d (2*d) (IsotropicImage d) := by
  refine ⟨isotropicEvaluationFactor d,isotropicEvaluationFactor_ne_zero d,
    isotropicEvaluationFactor_squarefree d,isotropicEvaluationFactor_homogeneous d,?_⟩
  intro H hH
  exact isotropicImage_iff_evaluationFactor_zero d (by omega) H hH

#assert_trust kernel numerator_root_mem_isotropicImage
#assert_trust kernel isotropicImage_iff_evaluationFactor_zero
#assert_trust kernel isotropic_degree
#print axioms isotropic_degree
end NLA.Proofs.TR26
