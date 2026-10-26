import NLA.Proofs.TR26.IsotropicTransverseWitness
import NLA.Proofs.TR26.ComplementaryFactor
import NLA.Proofs.TR26.AnalyticConormal

/-! A nonzero actual line derivative rules out a square factor. Applied to
every denominator root this proves exact isotropic multiplicity one in the
family determinant and coprimality of the genuine complementary quotient. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem hasDerivAt_eval_line {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℂ) (H K : ι → ℂ) :
    HasDerivAt (fun (ε : ℂ) => MvPolynomial.eval (H+ε • K) P)
      (∑ i, MvPolynomial.eval H (MvPolynomial.pderiv i P)*K i) 0 := by
  have hh := hasDerivAt_eval_curve P (fun (ε : ℂ) => H+ε • K) K 0 (by
    intro i
    convert! (hasDerivAt_const (0:ℂ) (H i)).add
      ((hasDerivAt_id (0:ℂ)).mul_const (K i)) using 1; simp)
  simpa only [zero_smul,add_zero] using hh

theorem hasDerivAt_eval_line_zero_of_square_dvd {ι : Type*} [Fintype ι]
    (P F : MvPolynomial ι ℂ) (H K : ι → ℂ)
    (hdiv : P^2 ∣ F) (hP : MvPolynomial.eval H P=0) :
    HasDerivAt (fun (ε : ℂ) => MvPolynomial.eval (H+ε • K) F) 0 0 := by
  obtain ⟨Q,hF⟩ := hdiv
  have h1 := hasDerivAt_eval_line P H K
  have h2 := hasDerivAt_eval_line Q H K
  convert! (h1.pow 2).mul h2 using 1
  · ext ε
    rw [hF,map_mul,map_pow]
    rfl
  · simp [hP]

theorem numeratorEvaluationPolynomial_sq_not_dvd_family {d : ℕ} (hd : 2 ≤ d)
    {r : ℂ} (hr : r ∈ denominatorRoots d) :
    ¬ (numeratorEvaluationPolynomial d r)^2 ∣ wronskianFamilyDiscriminant d := by
  obtain ⟨H,K,δ,hH,_hK,hder,hδ⟩ := exists_isotropic_family_transverse hd hr
  intro hdiv
  have hz := hasDerivAt_eval_line_zero_of_square_dvd
    (numeratorEvaluationPolynomial d r) (wronskianFamilyDiscriminant d) H K hdiv hH
  exact hδ (hder.unique hz)

theorem numeratorEvaluationPolynomial_not_dvd_complementary {d : ℕ} (hd : 2 ≤ d)
    (Q : ParameterRing d)
    (hF : wronskianFamilyDiscriminant d=isotropicEvaluationFactor d*Q)
    {r : ℂ} (hr : r ∈ denominatorRoots d) :
    ¬ numeratorEvaluationPolynomial d r ∣ Q := by
  classical
  intro hQ
  have hE : numeratorEvaluationPolynomial d r ∣ isotropicEvaluationFactor d :=
    Finset.dvd_prod_of_mem (numeratorEvaluationPolynomial d) hr
  apply numeratorEvaluationPolynomial_sq_not_dvd_family hd hr
  rw [hF,pow_two]
  exact mul_dvd_mul hE hQ

theorem isotropicEvaluationFactor_isRelPrime_complementary {d : ℕ} (hd : 2 ≤ d)
    (Q : ParameterRing d)
    (hF : wronskianFamilyDiscriminant d=isotropicEvaluationFactor d*Q) :
    IsRelPrime (isotropicEvaluationFactor d) Q := by
  classical
  apply IsRelPrime.prod_left
  intro r hr
  exact (numeratorEvaluationPolynomial_irreducible d r).isRelPrime_iff_not_dvd.mpr
    (numeratorEvaluationPolynomial_not_dvd_complementary hd Q hF hr)

#assert_trust kernel hasDerivAt_eval_line
#assert_trust kernel hasDerivAt_eval_line_zero_of_square_dvd
#assert_trust kernel numeratorEvaluationPolynomial_sq_not_dvd_family
#assert_trust kernel numeratorEvaluationPolynomial_not_dvd_complementary
#assert_trust kernel isotropicEvaluationFactor_isRelPrime_complementary
#print axioms isotropicEvaluationFactor_isRelPrime_complementary
end NLA.Proofs.TR26
