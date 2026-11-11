import NLA.Proofs.TR26.CriticalEquation
import NLA.Proofs.TR26.IsotropicChartCover

/-! Every point of the literal raw isotropic image lies on an actual
numerator-evaluation hyperplane at a denominator root. This direction uses
the full incidence ideal and does not insert a projection closure. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem isotropicImage_has_numerator_root (d : ℕ) (hd : 1 ≤ d)
    (H : Parameter d) (hH : H ∈ IsotropicImage d) :
    ∃ t : ℂ, t ∈ denominatorRoots d ∧ (affineNumerator H).eval t = 0 := by
  rcases hH with ⟨z,hR,hiso⟩
  obtain ⟨c,t,hc,hz,hD⟩ := isotropic_onCurve_affine_cover d z hR.1.2.2.1 hiso
  rw [hz] at hR
  have hW := incidence_affine_wrRoot d hd c t hc H hR.1
  have ht : t ∈ denominatorRoots d := (mem_denominatorRoots_iff d t).mpr hD
  have hD' := denominator_derivative_at_root_ne_zero ht
  have hN : (affineNumerator H).eval t = 0 := by
    simp only [affineWronskianOver,Polynomial.eval_sub,Polynomial.eval_mul,hD,
      mul_zero,zero_sub] at hW
    exact (mul_eq_zero.mp (neg_eq_zero.mp hW)).resolve_right hD'
  exact ⟨t,ht,hN⟩

theorem isotropicImage_evaluationFactor_zero (d : ℕ) (hd : 1 ≤ d)
    (H : Parameter d) (hH : H ∈ IsotropicImage d) :
    MvPolynomial.eval H (isotropicEvaluationFactor d) = 0 := by
  apply (eval_isotropicEvaluationFactor_eq_zero_iff d H).mpr
  exact isotropicImage_has_numerator_root d hd H hH

#assert_trust kernel isotropicImage_has_numerator_root
#assert_trust kernel isotropicImage_evaluationFactor_zero
#print axioms isotropicImage_has_numerator_root
end NLA.Proofs.TR26
