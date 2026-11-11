import NLA.Statements.TR26

/-! Homogeneous cancellation for genuine polynomial factors. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26

theorem homogeneousComponent_mul_homogeneous_left {ι : Type*} [Fintype ι]
    {f g : MvPolynomial ι ℂ} {r s : ℕ} (hf : f.IsHomogeneous r) :
    homogeneousComponent (r + s) (f * g) = f * homogeneousComponent s g := by
  classical
  have hdegree {e a b : ι →₀ ℕ} (hab : a + b = e) : a.degree + b.degree = e.degree := by
    rw [← hab]
    simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]
  have hfa {a : ι →₀ ℕ} (ha : coeff a f ≠ 0) : a.degree = r := by
    by_contra hne
    exact ha (hf.coeff_eq_zero hne)
  ext e
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  simp only [coeff_homogeneousComponent]
  by_cases he : e.degree = r + s
  · rw [if_pos he]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hzero : coeff z.1 f = 0
    · simp [hzero]
    · have hzdeg := hdegree (Finset.HasAntidiagonal.mem_antidiagonal.mp hz)
      have ha := hfa hzero
      have hb : z.2.degree = s := by omega
      rw [if_pos hb]
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hzero : coeff z.1 f = 0
    · simp [hzero]
    · have hzdeg := hdegree (Finset.HasAntidiagonal.mem_antidiagonal.mp hz)
      have ha := hfa hzero
      have hb : z.2.degree ≠ s := by omega
      rw [if_neg hb, mul_zero]

theorem homogeneous_quotient {ι : Type*} [Fintype ι]
    {f g : MvPolynomial ι ℂ} {r s : ℕ} (hf : f.IsHomogeneous r) (hfne : f ≠ 0)
    (hfg : (f * g).IsHomogeneous (r + s)) : g.IsHomogeneous s := by
  have heq : f * homogeneousComponent s g = f * g := by
    rw [← homogeneousComponent_mul_homogeneous_left hf, homogeneousComponent_eq_self hfg]
  have hg : homogeneousComponent s g = g := mul_left_cancel₀ hfne heq
  rw [← hg]
  exact homogeneousComponent_isHomogeneous _ _

#assert_trust kernel homogeneous_quotient
#print axioms homogeneous_quotient
end NLA.Proofs.TR26
