import NLA.Proofs.TR26.AnalyticConormal

/-! A local graph for a critical equation linear in its matrix parameter.
Only a coefficient that is nonzero at the chart point may be used as pivot.
The graph keeps the original parameter at a root; at a double root its
parameter velocity is zero. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
universe u
namespace NLA.Proofs.TR26

def linearCriticalPolynomial {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) : Polynomial ℂ :=
  ∑ i, Polynomial.C (H i) * L i

def linearCriticalValue {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (t : ℂ) (H : ι → ℂ) : ℂ :=
  ∑ i, (L i).eval t * H i

theorem linearCriticalPolynomial_eval {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) (t : ℂ) :
    (linearCriticalPolynomial L H).eval t = linearCriticalValue L t H := by
  simp [linearCriticalPolynomial,linearCriticalValue,Polynomial.eval_finsetSum,mul_comm]

def criticalGraphParameter {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) (j : ι) (t : ℂ) : ι → ℂ := by
  classical
  exact fun i => H i - (linearCriticalValue L t H / (L j).eval t) *
    Pi.single (M := fun _ : ι => ℂ) j 1 i

theorem criticalGraphParameter_at_root {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) (j : ι) (t : ℂ)
    (ht : linearCriticalValue L t H = 0) : criticalGraphParameter L H j t = H := by
  classical
  ext i
  simp [criticalGraphParameter,ht]

theorem criticalGraphParameter_is_root {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) (j : ι) (t : ℂ)
    (hj : (L j).eval t ≠ 0) :
    linearCriticalValue L t (criticalGraphParameter L H j t) = 0 := by
  classical
  simp only [linearCriticalValue,criticalGraphParameter,mul_sub,
    Finset.sum_sub_distrib]
  have hs : ∑ i, (L i).eval t *
      ((linearCriticalValue L t H / (L j).eval t) *
        Pi.single (M := fun _ : ι => ℂ) j 1 i) =
      linearCriticalValue L t H := by
    simp only [Pi.single_apply]
    simp only [mul_ite,mul_one,mul_zero]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
    exact mul_div_cancel₀ _ hj
  change linearCriticalValue L t H -
    (∑ i, (L i).eval t * ((linearCriticalValue L t H / (L j).eval t) *
      Pi.single (M := fun _ : ι => ℂ) j 1 i)) = 0
  rw [hs]
  exact sub_self _

theorem criticalGraphParameter_continuousAt {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) (j : ι) (t : ℂ)
    (hj : (L j).eval t ≠ 0) : ContinuousAt (criticalGraphParameter L H j) t := by
  apply continuousAt_pi.mpr
  intro i
  have hf : ContinuousAt (fun s => linearCriticalValue L s H) t := by
    simpa only [← linearCriticalPolynomial_eval] using
      (linearCriticalPolynomial L H).continuousAt
  exact continuousAt_const.sub ((hf.div (L j).continuousAt hj).mul continuousAt_const)

theorem hasDerivAt_criticalGraphParameter_of_double_root
    {ι : Type u} [Fintype ι]
    (L : ι → Polynomial ℂ) (H : ι → ℂ) (j : ι) (t : ℂ)
    (hj : (L j).eval t ≠ 0) (ht : linearCriticalValue L t H = 0)
    (hderiv : (linearCriticalPolynomial L H).derivative.eval t = 0) (i : ι) :
    HasDerivAt (fun s => criticalGraphParameter L H j s i) 0 t := by
  classical
  have hf : HasDerivAt (fun s => linearCriticalValue L s H) 0 t := by
    simpa only [linearCriticalPolynomial_eval,hderiv] using
      (linearCriticalPolynomial L H).hasDerivAt t
  have hq := hf.div ((L j).hasDerivAt t) hj
  convert! (hasDerivAt_const t (H i)).sub
    (hq.mul_const (Pi.single (M := fun _ : ι => ℂ) j 1 i)) using 1 <;>
    simp [criticalGraphParameter,ht]

#assert_trust kernel linearCriticalPolynomial_eval
#assert_trust kernel criticalGraphParameter_at_root
#assert_trust kernel criticalGraphParameter_is_root
#assert_trust kernel criticalGraphParameter_continuousAt
#assert_trust kernel hasDerivAt_criticalGraphParameter_of_double_root
#print axioms criticalGraphParameter_is_root
#print axioms hasDerivAt_criticalGraphParameter_of_double_root
end NLA.Proofs.TR26
