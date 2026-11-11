import NLA.Proofs.TR26.CriticalEquationDerivative
import NLA.Proofs.TR26.ReverseCurveNormalRank

/-! Exact chart characterizations for the original full-ideal incidence and
ramification predicates. In both charts the rank condition is equivalent to
an actual double root of the fixed-degree binary Wronskian. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem affineChart_incidence_iff {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0) :
    Incidence d (affineChartVector d c t) H ↔ (affineWronskian H).eval t = 0 := by
  exact ⟨incidence_affine_wrRoot d (by omega) c t hc H,
    affineChart_incidence_of_root (by omega) c t hc H hH⟩

theorem affineChart_ramification_iff {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0) :
    Ramification d (affineChartVector d c t) H ↔
      (affineWronskian H).eval t = 0 ∧ (affineWronskian H).derivative.eval t = 0 := by
  constructor
  · intro hR
    exact ⟨(affineChart_incidence_iff hd c t hc H hH).mp hR.1,
      ramification_affine_wrDerivative d (by omega) c t hc H hR⟩
  · rintro ⟨hW,hW'⟩
    exact affineChart_ramification_of_double_root (by omega) c t hc H hH hW hW'

theorem incidence_reverse_wrRoot (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d)
    (hI : Incidence d (reverseChartVector d c t) H) :
    (reverseWronskian H).eval t = 0 := by
  have hh := hI.2.2.2 (reverseCriticalEquation d hd)
    ((mem_openVanishingIdeal_iff d _).mp (reverseCriticalEquation_mem_openVanishingIdeal d hd))
  rw [reverseCriticalEquation_reverse_eval] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hc)

theorem ramification_reverse_tangent_annihilates (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d)
    (hR : Ramification d (reverseChartVector d c t) H) :
    ∀ g ∈ JacobianSpace d (reverseChartVector d c t) H,
      ∑ i, g i * reverseChartVelocity d c t i = 0 := by
  have hspan := submodule_eq_span_of_rank_bound
    (JacobianSpace d (reverseChartVector d c t) H)
    (reverseNormalVector d hd (reverseChartVector d c t) H)
    (reverseNormalVectors_independent d hd _ H (by simpa [reverseChartVector] using hc))
    (reverseNormalVector_mem_jacobianSpace d hd _ H)
    (by simpa only [Fintype.card_fin] using hR.2)
  rw [hspan]
  exact span_annihilates_pairing _ _ (reverseNormalVector_tangent_pairing d hd c t hc H)

theorem ramification_reverse_wrDerivative (d : ℕ) (hd : 1 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d)
    (hR : Ramification d (reverseChartVector d c t) H) :
    (reverseWronskian H).derivative.eval t = 0 := by
  have hg : partialGradient (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates (reverseChartVector d c t) H) (reverseCriticalEquation d hd) ∈
      JacobianSpace d (reverseChartVector d c t) H := by
    rw [jacobianSpace_eq_conormal]
    exact gradient_mem_conormal _ _ _ (reverseCriticalEquation_mem_openVanishingIdeal d hd)
  have hh := ramification_reverse_tangent_annihilates d hd c t hc H hR _ hg
  rw [reverseCriticalEquation_tangent_pairing] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hc)

theorem reverseChart_incidence_iff {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0) :
    Incidence d (reverseChartVector d c t) H ↔ (reverseWronskian H).eval t = 0 := by
  exact ⟨incidence_reverse_wrRoot d (by omega) c t hc H,
    reverseChart_incidence_of_root hd c t hc H hH⟩

theorem reverseChart_ramification_iff {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0) :
    Ramification d (reverseChartVector d c t) H ↔
      (reverseWronskian H).eval t = 0 ∧ (reverseWronskian H).derivative.eval t = 0 := by
  constructor
  · intro hR
    exact ⟨(reverseChart_incidence_iff hd c t hc H hH).mp hR.1,
      ramification_reverse_wrDerivative d (by omega) c t hc H hR⟩
  · rintro ⟨hW,hW'⟩
    exact reverseChart_ramification_of_double_root hd c t hc H hH hW hW'

theorem binaryWronskian_root_of_partials {d : ℕ} (hd : 2 ≤ d) (H : Parameter d)
    (a b : ℂ)
    (ha : binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) a b = 0)
    (hb : binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) a b = 0) :
    binaryEval (binaryWronskian H) a b = 0 := by
  have hh := binary_euler_eval (binaryWronskian H) (binaryWronskianOver_homogeneous H) a b
  rw [ha,hb,mul_zero,mul_zero,zero_add] at hh
  have hk : (4*d-2 : ℕ) ≠ 0 := by omega
  exact (mul_eq_zero.mp hh.symm).resolve_left (by exact_mod_cast hk)

theorem affineChart_ramification_iff_binary_partials {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0) :
    Ramification d (affineChartVector d c t) H ↔
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) 1 t = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) 1 t = 0 := by
  rw [affineChart_ramification_iff hd c t hc H hH]
  constructor
  · rintro ⟨hW,hW'⟩
    have hroot : binaryEval (binaryWronskian H) 1 t = 0 := by
      rwa [binaryWronskian_affine_eval (by omega)]
    have hb : binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) 1 t = 0 := by
      rwa [binaryWronskian_affine_derivative_eval (by omega)]
    have ha := binary_euler_eval (binaryWronskian H) (binaryWronskianOver_homogeneous H) 1 t
    exact ⟨by simpa only [one_mul,hb,mul_zero,add_zero,hroot] using ha,hb⟩
  · rintro ⟨ha,hb⟩
    constructor
    · have hh := binaryWronskian_root_of_partials hd H 1 t ha hb
      rwa [binaryWronskian_affine_eval (by omega)] at hh
    · rwa [← binaryWronskian_affine_derivative_eval (by omega)]

theorem reverseChart_ramification_iff_binary_partials {d : ℕ} (hd : 2 ≤ d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0) :
    Ramification d (reverseChartVector d c t) H ↔
      binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) t 1 = 0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) t 1 = 0 := by
  rw [reverseChart_ramification_iff hd c t hc H hH]
  constructor
  · rintro ⟨hW,hW'⟩
    have hroot : binaryEval (binaryWronskian H) t 1 = 0 := by rwa [← reverseWronskian_eval]
    have ha : binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) t 1 = 0 := by
      rwa [← reverseWronskian_derivative_eval]
    have hb := binary_euler_eval (binaryWronskian H) (binaryWronskianOver_homogeneous H) t 1
    refine ⟨ha,?_⟩
    simpa only [ha,mul_zero,zero_add,one_mul,hroot] using hb
  · rintro ⟨ha,hb⟩
    constructor
    · have hh := binaryWronskian_root_of_partials hd H t 1 ha hb
      rwa [← reverseWronskian_eval] at hh
    · rwa [reverseWronskian_derivative_eval]

#assert_trust kernel affineChart_incidence_iff
#assert_trust kernel affineChart_ramification_iff
#assert_trust kernel reverseChart_incidence_iff
#assert_trust kernel reverseChart_ramification_iff
#assert_trust kernel affineChart_ramification_iff_binary_partials
#assert_trust kernel reverseChart_ramification_iff_binary_partials
#print axioms affineChart_ramification_iff
#print axioms reverseChart_ramification_iff
end NLA.Proofs.TR26
