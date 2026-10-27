import NLA.Proofs.TR26.CurveDifferentiation
import NLA.Proofs.TR26.CriticalEquation
import NLA.Proofs.TR26.ReverseWronskianCharts

/-! The derivative of each actual global critical equation, holding the
original symmetric matrix fixed, is the corresponding chart Wronskian
 derivative times its nonzero cone scaling factor. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem affineCriticalEquation_tangent_pairing (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (H : Parameter d) :
    (∑ i, partialGradient (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates (affineChartVector d c t) H)
      (affineCriticalEquation d hd) i * affineChartVelocity d c t i) =
        c^(4*d-2) * (affineWronskian H).derivative.eval t := by
  have h1 := hasDerivAt_eval_fixed_parameter (affineCriticalEquation d hd)
    (affineChartVector d c) H (affineChartVelocity d c t) t
    (hasDerivAt_affineChartVector d c t)
  have h2 : HasDerivAt
      (fun s => MvPolynomial.eval (incidenceCoordinates (affineChartVector d c s) H)
        (affineCriticalEquation d hd))
      (c^(4*d-2) * (affineWronskian H).derivative.eval t) t := by
    simpa only [affineCriticalEquation_affine_eval] using
      ((affineWronskian H).hasDerivAt t).const_mul (c^(4*d-2))
  exact h1.unique h2

theorem reverseCriticalEquation_reverse_eval (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (H : Parameter d) :
    MvPolynomial.eval (incidenceCoordinates (reverseChartVector d c t) H)
      (reverseCriticalEquation d hd) = c^(4*d-2) * (reverseWronskian H).eval t := by
  rw [reverseCriticalEquation_eval]
  have he : d-(d-1)=1 := by omega
  simp only [reverseChartVector,chartPenultimateIndex,he,pow_one,
    Fin.val_last,Nat.sub_self,pow_zero,mul_one]
  rw [reverseWronskian_eval]
  simpa only [mul_one] using binaryEval_homogeneous_smul (4*d-2)
    (binaryWronskian H) (binaryWronskianOver_homogeneous H) t 1 c

theorem reverseCriticalEquation_tangent_pairing (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (H : Parameter d) :
    (∑ i, partialGradient (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates (reverseChartVector d c t) H)
      (reverseCriticalEquation d hd) i * reverseChartVelocity d c t i) =
        c^(4*d-2) * (reverseWronskian H).derivative.eval t := by
  have h1 := hasDerivAt_eval_fixed_parameter (reverseCriticalEquation d hd)
    (reverseChartVector d c) H (reverseChartVelocity d c t) t
    (hasDerivAt_reverseChartVector d c t)
  have h2 : HasDerivAt
      (fun s => MvPolynomial.eval (incidenceCoordinates (reverseChartVector d c s) H)
        (reverseCriticalEquation d hd))
      (c^(4*d-2) * (reverseWronskian H).derivative.eval t) t := by
    simpa only [reverseCriticalEquation_reverse_eval] using
      ((reverseWronskian H).hasDerivAt t).const_mul (c^(4*d-2))
  exact h1.unique h2

theorem affineNormalVector_tangent_pairing (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (k : Fin (d-1)) :
    ∑ i, affineNormalVector d hd (affineChartVector d c t) H k i *
      affineChartVelocity d c t i = 0 := by
  apply gradient_annihilates_of_eval_identically_zero
    (affineCurveEquation d hd (normalCurveIndex d hd k)) (affineChartVector d c) H
    (affineChartVelocity d c t) t (hasDerivAt_affineChartVector d c t)
  intro s
  exact affineCurveEquation_vanishes_onCurve d hd _ (by simp [normalCurveIndex])
    _ H (affineChartVector_onCurve d c s hc)

theorem ramification_affine_tangent_annihilates (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d)
    (hR : Ramification d (affineChartVector d c t) H) :
    ∀ g ∈ JacobianSpace d (affineChartVector d c t) H,
      ∑ i, g i * affineChartVelocity d c t i = 0 := by
  have hspan := submodule_eq_span_of_rank_bound
    (JacobianSpace d (affineChartVector d c t) H)
    (affineNormalVector d hd (affineChartVector d c t) H)
    (affineNormalVectors_independent d hd _ H (by simpa [affineChartVector] using hc))
    (affineNormalVector_mem_jacobianSpace d hd _ H)
    (by simpa only [Fintype.card_fin] using hR.2)
  rw [hspan]
  exact span_annihilates_pairing _ _ (affineNormalVector_tangent_pairing d hd c t hc H)

theorem ramification_affine_wrDerivative (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d)
    (hR : Ramification d (affineChartVector d c t) H) :
    (affineWronskian H).derivative.eval t = 0 := by
  have hg : partialGradient (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates (affineChartVector d c t) H) (affineCriticalEquation d hd) ∈
      JacobianSpace d (affineChartVector d c t) H := by
    rw [jacobianSpace_eq_conormal]
    exact gradient_mem_conormal _ _ _ (affineCriticalEquation_mem_openVanishingIdeal d hd)
  have hh := ramification_affine_tangent_annihilates d hd c t hc H hR _ hg
  rw [affineCriticalEquation_tangent_pairing] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hc)

#assert_trust kernel affineCriticalEquation_tangent_pairing
#assert_trust kernel reverseCriticalEquation_reverse_eval
#assert_trust kernel reverseCriticalEquation_tangent_pairing
#assert_trust kernel affineNormalVector_tangent_pairing
#assert_trust kernel ramification_affine_tangent_annihilates
#assert_trust kernel ramification_affine_wrDerivative
#print axioms ramification_affine_wrDerivative
end NLA.Proofs.TR26
