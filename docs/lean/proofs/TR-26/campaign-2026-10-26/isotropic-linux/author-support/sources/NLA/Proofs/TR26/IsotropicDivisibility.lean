import NLA.Proofs.TR26.IsotropicFactor
import Mathlib.RingTheory.Nullstellensatz

/-! Divisibility in the actual parameter ring from vanishing on the explicit
numerator-evaluation hyperplanes. The linear factors are proved prime and their
product reduced; this adds no geometric or family-vanishing assumption to Target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem numeratorEvaluationPolynomial_dvd_of_vanishing (d : ℕ) (r : ℂ)
    (P : ParameterRing d)
    (hvanish : ∀ H : Parameter d, (affineNumerator H).eval r = 0 → MvPolynomial.eval H P = 0) :
    numeratorEvaluationPolynomial d r ∣ P := by
  let I : Ideal (ParameterRing d) := Ideal.span {numeratorEvaluationPolynomial d r}
  have hprime : I.IsPrime := Ideal.isPrime_span_singleton_of_prime
    (numeratorEvaluationPolynomial_irreducible d r).prime
  have hmem : P ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ I) := by
    intro H hH
    apply hvanish H
    have hzero := hH (numeratorEvaluationPolynomial d r)
      (Ideal.subset_span (Set.mem_singleton _))
    simpa only [MvPolynomial.aeval_eq_eval, eval_numeratorEvaluationPolynomial] using hzero
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hprime.radical] at hmem
  exact Ideal.mem_span_singleton.mp hmem

theorem isotropicEvaluationFactor_dvd_of_vanishing {d : ℕ} (hd : 1 ≤ d)
    (P : ParameterRing d)
    (hvanish : ∀ r ∈ denominatorRoots d, ∀ H : Parameter d,
      (affineNumerator H).eval r = 0 → MvPolynomial.eval H P = 0) :
    isotropicEvaluationFactor d ∣ P := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro r _ s _ hrs
    exact (numeratorEvaluationPolynomial_irreducible d r).isRelPrime_iff_not_dvd.mpr
      (numeratorEvaluationPolynomial_not_dvd hd hrs)
  · intro r hr
    exact numeratorEvaluationPolynomial_dvd_of_vanishing d r P (hvanish r hr)

#assert_trust kernel numeratorEvaluationPolynomial_dvd_of_vanishing
#assert_trust kernel isotropicEvaluationFactor_dvd_of_vanishing
#print axioms isotropicEvaluationFactor_dvd_of_vanishing
end NLA.Proofs.TR26
