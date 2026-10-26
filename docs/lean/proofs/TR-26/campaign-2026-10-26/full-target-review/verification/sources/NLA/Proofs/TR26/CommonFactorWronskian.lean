import NLA.Proofs.TR26.WronskianPencilDegree
import NLA.Proofs.TR26.Denominator
import NLA.Proofs.TR26.Numerator

/-! A common linear numerator/denominator factor produces an exact square
factor in the actual Wronskian. Constant numerator perturbations have a
nonzero value at every simple denominator root. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 Polynomial

theorem polynomialWronskian_common_factor (L M E : Polynomial ℂ) :
    polynomialWronskian (L*M) (L*E)=L^2*polynomialWronskian M E := by
  simp only [polynomialWronskian,Polynomial.derivative_mul]
  ring

theorem polynomialWronskian_add_C_mul (N V D : Polynomial ℂ) (ε : ℂ) :
    polynomialWronskian (N+C ε*V) D =
      polynomialWronskian N D+C ε*polynomialWronskian V D := by
  simp only [polynomialWronskian,Polynomial.derivative_add,Polynomial.derivative_C_mul]
  ring

theorem polynomialWronskian_one (D : Polynomial ℂ) :
    polynomialWronskian 1 D = -D.derivative := by
  simp [polynomialWronskian]

theorem denominator_root_linear_factor {d : ℕ} {r : ℂ} (hr : r ∈ denominatorRoots d) :
    ∃ E : Polynomial ℂ, affineDenominator d=(X-C r)*E ∧ E.Monic ∧ E.Separable ∧
      E.natDegree=2*d-1 ∧ E.eval r ≠ 0 := by
  have hroot := (mem_denominatorRoots_iff d r).mp hr
  have hdiv : X-C r ∣ affineDenominator d := (Polynomial.dvd_iff_isRoot).mpr hroot
  obtain ⟨E,hE⟩ := hdiv
  have hE0 : E ≠ 0 := by
    intro hz
    exact affineDenominator_ne_zero d (by rw [hE,hz,mul_zero])
  have hmon : E.Monic := by
    change E.leadingCoeff=1
    have hh := affineDenominator_monic d
    change (affineDenominator d).leadingCoeff=1 at hh
    rw [hE,Polynomial.leadingCoeff_mul] at hh
    simpa using hh
  have hsep : E.Separable := by
    apply (affineDenominator_separable d).of_dvd
    rw [hE]
    exact dvd_mul_left _ _
  have hdeg : E.natDegree=2*d-1 := by
    have hh := affineDenominator_natDegree d
    rw [hE,Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hE0,
      Polynomial.natDegree_X_sub_C] at hh
    omega
  have hval : (affineDenominator d).derivative.eval r=E.eval r := by
    rw [hE]
    simp
  exact ⟨E,hE,hmon,hsep,hdeg,by simpa only [← hval] using denominator_derivative_at_root_ne_zero hr⟩

theorem exists_parameter_linear_factor_numerator {d : ℕ} (r : ℂ)
    (M : Polynomial ℂ) (hM : M.natDegree ≤ 2*d-1) (hd : 1 ≤ d) :
    ∃ H : Parameter d, affineNumerator H=(X-C r)*M := by
  apply affineNumerator_surjective_degreeLE d
  have hh : ((X-C r)*M).natDegree ≤ (X-C r).natDegree+M.natDegree := natDegree_mul_le
  rw [natDegree_X_sub_C] at hh
  omega

#assert_trust kernel polynomialWronskian_common_factor
#assert_trust kernel polynomialWronskian_add_C_mul
#assert_trust kernel denominator_root_linear_factor
#assert_trust kernel exists_parameter_linear_factor_numerator
#print axioms denominator_root_linear_factor
end NLA.Proofs.TR26
