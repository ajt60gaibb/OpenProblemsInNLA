import NLA.Proofs.TR26.Denominator
import NLA.Proofs.TR26.Numerator
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! The actual 2d numerator-evaluation hyperplanes above the simple roots of
the fixed denominator. Their product is reduced; identification with the full
incidence/Jacobian isotropic image is a separate geometric proof obligation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

/-- The actual numerator evaluated at a fixed affine point, as a parameter polynomial. -/
def numeratorEvaluationPolynomial (d : ℕ) (r : ℂ) : ParameterRing d :=
  ∑ i : Index d, ∑ j : Index d,
    coordinateEntry (fun ij : SymIndex d => X ij : SymIndex d → ParameterRing d) i j *
      C (r ^ (i.val + j.val))

theorem eval_numeratorEvaluationPolynomial (d : ℕ) (r : ℂ) (H : Parameter d) :
    MvPolynomial.eval H (numeratorEvaluationPolynomial d r) = (affineNumerator H).eval r := by
  change MvPolynomial.eval H (numeratorEvaluationPolynomial d r) =
    Polynomial.eval r (affineNumeratorOver H)
  unfold numeratorEvaluationPolynomial affineNumeratorOver
  simp only [map_sum, map_mul, eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  unfold coordinateEntry
  split_ifs <;> simp

theorem numeratorEvaluationPolynomial_homogeneous (d : ℕ) (r : ℂ) :
    (numeratorEvaluationPolynomial d r).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  have hentry : (coordinateEntry (fun ij : SymIndex d => X ij : SymIndex d → ParameterRing d)
      i j).IsHomogeneous 1 := by
    unfold coordinateEntry
    split_ifs <;> exact isHomogeneous_X ℂ _
  simpa only [add_zero] using hentry.mul (isHomogeneous_C _ _)

theorem numeratorEvaluationPolynomial_ne_zero (d : ℕ) (r : ℂ) :
    numeratorEvaluationPolynomial d r ≠ 0 := by
  obtain ⟨H, hH⟩ := affineNumerator_surjective_degreeLE d (1 : Polynomial ℂ) (by simp)
  intro hz
  have h := eval_numeratorEvaluationPolynomial d r H
  rw [hz, map_zero, hH, Polynomial.eval_one] at h
  exact zero_ne_one h

theorem numeratorEvaluationPolynomial_irreducible (d : ℕ) (r : ℂ) :
    Irreducible (numeratorEvaluationPolynomial d r) := by
  have hne := numeratorEvaluationPolynomial_ne_zero d r
  apply MvPolynomial.irreducible_of_totalDegree_eq_one
    ((numeratorEvaluationPolynomial_homogeneous d r).totalDegree hne)
  intro x hx
  by_cases hzero : x = 0
  · exfalso
    apply hne
    ext m
    have h := hx m
    rw [hzero, zero_dvd_iff] at h
    exact h
  · exact isUnit_iff_ne_zero.mpr hzero

theorem numeratorEvaluationPolynomial_not_dvd {d : ℕ} (hd : 1 ≤ d)
    {r s : ℂ} (hrs : r ≠ s) :
    ¬ numeratorEvaluationPolynomial d r ∣ numeratorEvaluationPolynomial d s := by
  have hdeg : (Polynomial.X - Polynomial.C r : Polynomial ℂ).natDegree ≤ 2 * d := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_X, Polynomial.natDegree_C]
    norm_num
    omega
  obtain ⟨H, hH⟩ := affineNumerator_surjective_degreeLE d
    (Polynomial.X - Polynomial.C r) hdeg
  rintro ⟨Q, hQ⟩
  have h := congrArg (MvPolynomial.eval H) hQ
  simp only [map_mul, eval_numeratorEvaluationPolynomial, hH,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul] at h
  exact hrs (sub_eq_zero.mp h).symm

/-- The product of all actual denominator-root numerator evaluations. -/
def isotropicEvaluationFactor (d : ℕ) : ParameterRing d :=
  ∏ r ∈ denominatorRoots d, numeratorEvaluationPolynomial d r

theorem isotropicEvaluationFactor_ne_zero (d : ℕ) : isotropicEvaluationFactor d ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun r _ => numeratorEvaluationPolynomial_ne_zero d r)

theorem isotropicEvaluationFactor_homogeneous (d : ℕ) :
    (isotropicEvaluationFactor d).IsHomogeneous (2 * d) := by
  classical
  simpa [isotropicEvaluationFactor, denominatorRoots_card] using
    IsHomogeneous.prod (denominatorRoots d) (numeratorEvaluationPolynomial d)
      (fun _ : ℂ => (1 : ℕ)) (fun r _ => numeratorEvaluationPolynomial_homogeneous d r)

theorem isotropicEvaluationFactor_squarefree (d : ℕ) : Squarefree (isotropicEvaluationFactor d) := by
  classical
  by_cases hd : 1 ≤ d
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro r _ s _ hrs
      exact (numeratorEvaluationPolynomial_irreducible d r).isRelPrime_iff_not_dvd.mpr
        (numeratorEvaluationPolynomial_not_dvd hd hrs)
    · intro r _
      exact (numeratorEvaluationPolynomial_irreducible d r).squarefree
  · have hd0 : d = 0 := by omega
    have hroots : denominatorRoots d = ∅ := Finset.card_eq_zero.mp (by rw [denominatorRoots_card, hd0])
    simp [isotropicEvaluationFactor, hroots]

theorem isotropicEvaluationFactor_totalDegree (d : ℕ) :
    (isotropicEvaluationFactor d).totalDegree = 2 * d :=
  (isotropicEvaluationFactor_homogeneous d).totalDegree (isotropicEvaluationFactor_ne_zero d)

theorem eval_isotropicEvaluationFactor_eq_zero_iff (d : ℕ) (H : Parameter d) :
    MvPolynomial.eval H (isotropicEvaluationFactor d) = 0 ↔
      ∃ r ∈ denominatorRoots d, (affineNumerator H).eval r = 0 := by
  classical
  simp only [isotropicEvaluationFactor, map_prod, Finset.prod_eq_zero_iff,
    eval_numeratorEvaluationPolynomial]

#assert_trust kernel eval_numeratorEvaluationPolynomial
#assert_trust kernel numeratorEvaluationPolynomial_irreducible
#assert_trust kernel numeratorEvaluationPolynomial_not_dvd
#assert_trust kernel isotropicEvaluationFactor_ne_zero
#assert_trust kernel isotropicEvaluationFactor_homogeneous
#assert_trust kernel isotropicEvaluationFactor_squarefree
#assert_trust kernel isotropicEvaluationFactor_totalDegree
#assert_trust kernel eval_isotropicEvaluationFactor_eq_zero_iff
#print axioms isotropicEvaluationFactor_squarefree
#print axioms isotropicEvaluationFactor_totalDegree
end NLA.Proofs.TR26
