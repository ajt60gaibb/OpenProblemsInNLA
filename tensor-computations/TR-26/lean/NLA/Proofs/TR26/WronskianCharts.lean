import NLA.Proofs.TR26.WronskianLinear
import NLA.Proofs.TR26.ChartIncidence

/-! The actual affine Wronskian supplies the coefficient family and every
pivot in the local full-ideal incidence argument. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

/-- Coefficients of the actual critical polynomial in the original symmetric
matrix coordinates. -/
def affineCriticalCoefficients (d : ℕ) (j : SymIndex d) : Polynomial ℂ :=
  affineWronskian (Pi.single j 1)

theorem linearCriticalPolynomial_affine {d : ℕ} (H : Parameter d) :
    linearCriticalPolynomial (affineCriticalCoefficients d) H =
      affineWronskian H := by
  classical
  have hrep : H = ∑ j : SymIndex d, H j • Pi.single j 1 := by
    ext j
    simp [Pi.single_apply]
  have hh := congrArg (affineWronskianLinear d) hrep
  rw [map_sum] at hh
  simp only [map_smul, affineWronskianLinear_apply] at hh
  simpa only [linearCriticalPolynomial, affineCriticalCoefficients,
    Polynomial.smul_eq_C_mul] using hh.symm

theorem linearCriticalValue_affine {d : ℕ} (t : ℂ) (H : Parameter d) :
    linearCriticalValue (affineCriticalCoefficients d) t H =
      (affineWronskian H).eval t := by
  rw [← linearCriticalPolynomial_eval, linearCriticalPolynomial_affine]

theorem exists_affineCriticalCoefficients_pivot {d : ℕ} (hd : 0 < d) (t : ℂ) :
    ∃ j : SymIndex d, (affineCriticalCoefficients d j).eval t ≠ 0 := by
  obtain ⟨j,hj⟩ := exists_affineCritical_pivot hd t
  exact ⟨j,by simpa only [affineCriticalLinear_apply, affineCriticalCoefficients] using hj⟩

theorem affineDenominator_eval_eq_source (d : ℕ) (t : ℂ) :
    (affineDenominator d).eval t = denominator (veronese d 1 t) := by
  change (affineDenominatorOver ℂ d).eval t = _
  rw [← binaryDehomogenize_denominator ℂ d, binaryDehomogenize_eval,
    binaryDenominator_eval]

theorem affineChart_openCritical_of_root {d : ℕ} (hd : 0 < d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0)
    (hD : (affineDenominator d).eval t ≠ 0)
    (hW : linearCriticalValue (affineCriticalCoefficients d) t H = 0) :
    OpenCritical (affineChartVector d c t) H := by
  refine ⟨hH,1,t,c,Or.inl one_ne_zero,hc,?_,?_,?_⟩
  · intro i
    simp [affineChartVector,veronese]
  · rwa [← affineDenominator_eval_eq_source]
  · apply (parameterCritical_iff hd H (Or.inl one_ne_zero)).mpr
    rw [binaryWronskian_affine_eval hd, ← linearCriticalValue_affine]
    exact hW

theorem affineChart_incidence_of_root {d : ℕ} (hd : 0 < d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0)
    (hW : (affineWronskian H).eval t = 0) :
    Incidence d (affineChartVector d c t) H := by
  obtain ⟨j,hj⟩ := exists_affineCriticalCoefficients_pivot hd t
  apply chart_incidence_of_root d (affineChartVector d c)
    (by unfold affineChartVector; fun_prop) (affineCriticalCoefficients d) (affineDenominator d)
    (affineDenominator_ne_zero d)
    (fun s A hA hD hroot => affineChart_openCritical_of_root hd c s hc A hA hD hroot)
    t H hH (affineChartVector_onCurve d c t hc) j hj
  rwa [linearCriticalValue_affine]

theorem affineChart_ramification_of_double_root {d : ℕ} (hd : 0 < d)
    (c t : ℂ) (hc : c ≠ 0) (H : Parameter d) (hH : H ≠ 0)
    (hW : (affineWronskian H).eval t = 0)
    (hW' : (affineWronskian H).derivative.eval t = 0) :
    Ramification d (affineChartVector d c t) H := by
  obtain ⟨j,hj⟩ := exists_affineCriticalCoefficients_pivot hd t
  apply chart_ramification_of_double_root d (affineChartVector d c)
    (by unfold affineChartVector; fun_prop) (affineCriticalCoefficients d) (affineDenominator d)
    (affineDenominator_ne_zero d)
    (fun s A hA hD hroot => affineChart_openCritical_of_root hd c s hc A hA hD hroot)
    t H hH (affineChartVector_onCurve d c t hc) j hj
    (by rwa [linearCriticalValue_affine])
    (by rwa [linearCriticalPolynomial_affine])
    (affineChartVelocity d c t) (hasDerivAt_affineChartVector d c t)
    (affineChart_tangents_independent d (by omega) c t hc)

#assert_trust kernel linearCriticalPolynomial_affine
#assert_trust kernel linearCriticalValue_affine
#assert_trust kernel exists_affineCriticalCoefficients_pivot
#assert_trust kernel affineChart_openCritical_of_root
#assert_trust kernel affineChart_incidence_of_root
#assert_trust kernel affineChart_ramification_of_double_root
#print axioms affineChart_ramification_of_double_root
end NLA.Proofs.TR26
