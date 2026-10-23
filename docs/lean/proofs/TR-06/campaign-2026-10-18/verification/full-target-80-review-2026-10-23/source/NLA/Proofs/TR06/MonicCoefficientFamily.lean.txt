import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set

namespace NLA.Proofs.TR06

/-- Total monic family from lower coefficient functions. Fixing the leading
coefficient to one avoids imposing algebraic-image relations off that image. -/
def monicCoefficientPolynomial (N : ℕ) (c : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ N + ∑ j ∈ Finset.range N, Polynomial.C (c j) * Polynomial.X ^ j

theorem monicCoefficientPolynomial_coeff (N : ℕ) (c : ℕ → ℂ) (j : ℕ) :
    (monicCoefficientPolynomial N c).coeff j =
      (if j = N then 1 else 0) + (if j < N then c j else 0) := by
  classical
  simp [monicCoefficientPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    eq_comm]

theorem monicCoefficientPolynomial_natDegree_le (N : ℕ) (c : ℕ → ℂ) :
    (monicCoefficientPolynomial N c).natDegree ≤ N := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [monicCoefficientPolynomial_coeff]
  simp [ne_of_gt hj, not_lt.mpr (le_of_lt hj)]

theorem monicCoefficientPolynomial_monic (N : ℕ) (c : ℕ → ℂ) :
    (monicCoefficientPolynomial N c).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one N
    (monicCoefficientPolynomial_natDegree_le N c)
  simp [monicCoefficientPolynomial_coeff]

/-- On an actual character, reconstruction from lower coefficients agrees
exactly with mapping the original monic polynomial through that character. -/
theorem monicCoefficientPolynomial_eq_map {R : Type*} [CommRing R]
    (p : Polynomial R) (hp : p.Monic) (φ : R →+* ℂ) :
    monicCoefficientPolynomial p.natDegree (fun j => φ (p.coeff j)) = p.map φ := by
  ext j
  rw [monicCoefficientPolynomial_coeff, Polynomial.coeff_map]
  by_cases hj : j = p.natDegree
  · subst j
    simp [hp.coeff_natDegree]
  · by_cases hjlt : j < p.natDegree
    · simp [hj, hjlt]
    · have hgt : p.natDegree < j := lt_of_le_of_ne (not_lt.mp hjlt) (Ne.symm hj)
      simp [hj, hjlt, Polynomial.coeff_eq_zero_of_natDegree_lt hgt]

theorem continuousOn_monicCoefficientPolynomial_coeff {Y : Type*}
    [TopologicalSpace Y] (U : Set Y) (N : ℕ) (c : Y → ℕ → ℂ)
    (hc : ∀ j < N, ContinuousOn (fun y => c y j) U) (j : ℕ) :
    ContinuousOn (fun y => (monicCoefficientPolynomial N (c y)).coeff j) U := by
  simp only [monicCoefficientPolynomial_coeff]
  by_cases hj : j < N
  · simp only [if_pos hj]
    exact continuousOn_const.add (hc j hj)
  · simp only [if_neg hj, add_zero]
    exact continuousOn_const

#print axioms monicCoefficientPolynomial_coeff
#print axioms monicCoefficientPolynomial_natDegree_le
#print axioms monicCoefficientPolynomial_monic
#print axioms monicCoefficientPolynomial_eq_map
#print axioms continuousOn_monicCoefficientPolynomial_coeff
#assert_trust kernel monicCoefficientPolynomial_coeff
#assert_trust kernel monicCoefficientPolynomial_natDegree_le
#assert_trust kernel monicCoefficientPolynomial_monic
#assert_trust kernel monicCoefficientPolynomial_eq_map
#assert_trust kernel continuousOn_monicCoefficientPolynomial_coeff

end NLA.Proofs.TR06
