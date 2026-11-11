import NLA.Statements.TR26
import Mathlib.RingTheory.Nullstellensatz

/-! Deleting a relatively prime hypersurface does not change the polynomial
closure of a projective hypersurface. Relative primeness is an explicit
algebraic obligation; it is not asserted here for TR-26's two factors. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
universe u
namespace NLA.Proofs.TR26
open MvPolynomial

def polynomialProjectiveClosure {ι : Type u} (S : Set (ι → ℂ)) : Set (ι → ℂ) :=
  {x | x ≠ 0 ∧ ∀ f : MvPolynomial ι ℂ,
    (∀ y ∈ S, MvPolynomial.eval y f = 0) → MvPolynomial.eval x f = 0}

theorem eval_zero_of_vanishing_away_hypersurface
    {ι : Type u} [Finite ι] (G Q f : MvPolynomial ι ℂ)
    (hrel : IsRelPrime G Q) (hQ0 : MvPolynomial.eval (0 : ι → ℂ) Q = 0)
    (hf : ∀ y : ι → ℂ, y ≠ 0 → MvPolynomial.eval y G = 0 →
      MvPolynomial.eval y Q ≠ 0 → MvPolynomial.eval y f = 0)
    (x : ι → ℂ) (hx : MvPolynomial.eval x G = 0) : MvPolynomial.eval x f = 0 := by
  have hvan : f*Q ∈ MvPolynomial.vanishingIdeal ℂ
      (MvPolynomial.zeroLocus ℂ (Ideal.span {G})) := by
    intro y hy
    have hG : MvPolynomial.eval y G = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using
        hy G (Ideal.subset_span (Set.mem_singleton G))
    change MvPolynomial.eval y (f*Q) = 0
    rw [map_mul]
    by_cases hy0 : y=0
    · rw [hy0,hQ0,mul_zero]
    by_cases hyQ : MvPolynomial.eval y Q=0
    · rw [hyQ,mul_zero]
    rw [hf y hy0 hG hyQ,zero_mul]
  have hrad : f*Q ∈ (Ideal.span {G}).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
    exact hvan
  obtain ⟨n,hn⟩ := Ideal.mem_radical_iff.mp hrad
  have hdiv : G ∣ f^n * Q^n := by
    rw [← mul_pow]
    exact Ideal.mem_span_singleton.mp hn
  have hdivf : G ∣ f^n := hrel.pow_right.dvd_of_dvd_mul_right hdiv
  obtain ⟨g,hg⟩ := hdivf
  have heval : (MvPolynomial.eval x f)^n = 0 := by
    have hh := congrArg (MvPolynomial.eval x) hg
    simpa only [map_pow,map_mul,hx,zero_mul] using hh
  exact eq_zero_of_pow_eq_zero heval

theorem polynomialProjectiveClosure_hypersurface_away
    {ι : Type u} [Finite ι] (G Q : MvPolynomial ι ℂ)
    (hrel : IsRelPrime G Q) (hQ0 : MvPolynomial.eval (0 : ι → ℂ) Q = 0) :
    polynomialProjectiveClosure
      {x : ι → ℂ | x ≠ 0 ∧ MvPolynomial.eval x G = 0 ∧ MvPolynomial.eval x Q ≠ 0} =
      {x : ι → ℂ | x ≠ 0 ∧ MvPolynomial.eval x G = 0} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1,hx.2 G (fun _ hy => hy.2.1)⟩
  · rintro ⟨hx0,hxG⟩
    refine ⟨hx0,?_⟩
    intro f hf
    apply eval_zero_of_vanishing_away_hypersurface G Q f hrel hQ0 _ x hxG
    intro y hy0 hyG hyQ
    exact hf y ⟨hy0,hyG,hyQ⟩

theorem polynomialProjectiveClosure_mono {ι : Type u} {S T : Set (ι → ℂ)}
    (hST : S ⊆ T) : polynomialProjectiveClosure S ⊆ polynomialProjectiveClosure T := by
  intro x hx
  exact ⟨hx.1,fun f hf => hx.2 f (fun y hy => hf y (hST hy))⟩

theorem mem_polynomialProjectiveClosure {ι : Type u} {S : Set (ι → ℂ)}
    {x : ι → ℂ} (hx : x ∈ S) (hx0 : x ≠ 0) : x ∈ polynomialProjectiveClosure S :=
  ⟨hx0,fun _ hf => hf x hx⟩

theorem polynomialProjectiveClosure_eq_of_hypersurface_bounds
    {ι : Type u} [Finite ι] (G Q : MvPolynomial ι ℂ) (S : Set (ι → ℂ))
    (hrel : IsRelPrime G Q) (hQ0 : MvPolynomial.eval (0 : ι → ℂ) Q = 0)
    (hlower : {x : ι → ℂ | x ≠ 0 ∧ MvPolynomial.eval x G = 0 ∧
      MvPolynomial.eval x Q ≠ 0} ⊆ S)
    (hupper : S ⊆ {x : ι → ℂ | x ≠ 0 ∧ MvPolynomial.eval x G = 0}) :
    polynomialProjectiveClosure S = {x : ι → ℂ | x ≠ 0 ∧ MvPolynomial.eval x G = 0} := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hx.1,hx.2 G (fun y hy => (hupper hy).2)⟩
  · have hh := polynomialProjectiveClosure_mono hlower
    rwa [polynomialProjectiveClosure_hypersurface_away G Q hrel hQ0] at hh

#assert_trust kernel eval_zero_of_vanishing_away_hypersurface
#assert_trust kernel polynomialProjectiveClosure_hypersurface_away
#assert_trust kernel polynomialProjectiveClosure_mono
#assert_trust kernel mem_polynomialProjectiveClosure
#assert_trust kernel polynomialProjectiveClosure_eq_of_hypersurface_bounds
#print axioms polynomialProjectiveClosure_hypersurface_away
end NLA.Proofs.TR26
