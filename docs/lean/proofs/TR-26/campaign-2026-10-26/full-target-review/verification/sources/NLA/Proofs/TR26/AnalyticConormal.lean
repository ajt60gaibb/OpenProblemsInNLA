import NLA.Proofs.TR26.LocalConormal

/-! Analytic tests for the full polynomial conormal. A curve on which every
element of an ideal vanishes annihilates that ideal's evaluated gradients.
The polynomial exclusion lemma permits filling a finite set of omitted
parameter values without changing the ideal being tested. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Filter
universe u v
namespace NLA.Proofs.TR26

theorem hasDerivAt_eval_curve {σ : Type u} [Fintype σ]
    (f : MvPolynomial σ ℂ) (γ : ℂ → σ → ℂ) (v : σ → ℂ) (t : ℂ)
    (hγ : ∀ i, HasDerivAt (fun s => γ s i) (v i) t) :
    HasDerivAt (fun s => MvPolynomial.eval (γ s) f)
      (∑ i, MvPolynomial.eval (γ t) (MvPolynomial.pderiv i f) * v i) t := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.pderiv_C] using hasDerivAt_const t a
  | add f g hf hg =>
      convert! hf.add hg using 1
      · ext s
        simp
      · simp [Finset.sum_add_distrib,add_mul]
  | mul_X f j hf =>
      convert! hf.mul (hγ j) using 1
      · ext s
        simp
      · simp only [MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.eval_X]
        have hx : ∑ i, MvPolynomial.eval (γ t)
            (MvPolynomial.pderiv i (MvPolynomial.X j)) * v i = v j := by
          simp [MvPolynomial.pderiv_X,Pi.single_apply]
        calc
          _ = (∑ i, MvPolynomial.eval (γ t) (MvPolynomial.pderiv i f) * v i) *
              γ t j + MvPolynomial.eval (γ t) f *
              (∑ i, MvPolynomial.eval (γ t) (MvPolynomial.pderiv i (MvPolynomial.X j)) *
                v i) := by
            rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [hx]

theorem continuousAt_zero_of_polynomial_exclusion
    (f : ℂ → ℂ) (t : ℂ) (hf : ContinuousAt f t)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hzero : ∀ᶠ s in 𝓝 t, P.eval s ≠ 0 → f s = 0) : f t = 0 := by
  have hnonroot : ∀ᶠ s in 𝓝[≠] t, P.eval s ≠ 0 :=
    (Polynomial.eventually_cofinite_not_isRoot hP).filter_mono (nhdsNE_le_cofinite t)
  have hz : f =ᶠ[𝓝[≠] t] fun _ => 0 := by
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds,hnonroot] with s hs hp
    exact hs hp
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' hz.symm)

theorem continuousOn_zero_of_polynomial_exclusion
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hf : ContinuousOn f U)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hzero : ∀ s ∈ U, P.eval s ≠ 0 → f s = 0) :
    ∀ s ∈ U, f s = 0 := by
  intro s hs
  apply continuousAt_zero_of_polynomial_exclusion f s
    ((hf s hs).continuousAt (hU.mem_nhds hs)) P hP
  filter_upwards [hU.mem_nhds hs] with r hr
  exact hzero r hr

theorem eventually_zero_of_polynomial_exclusion
    (f : ℂ → ℂ) (t : ℂ) (hf : ∀ᶠ s in 𝓝 t, ContinuousAt f s)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hzero : ∀ᶠ s in 𝓝 t, P.eval s ≠ 0 → f s = 0) :
    f =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [hf,hzero.eventually_nhds] with s hs hz
  exact continuousAt_zero_of_polynomial_exclusion f s hs P hP hz

theorem idealConormal_annihilates_curve
    {σ : Type u} {τ : Type v} [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial (σ ⊕ τ) ℂ))
    (γ : ℂ → (σ ⊕ τ) → ℂ) (v : σ → ℂ) (t : ℂ)
    (hγz : ∀ i, HasDerivAt (fun s => γ s (.inl i)) (v i) t)
    (hγH : ∀ i, HasDerivAt (fun s => γ s (.inr i)) 0 t)
    (hzero : ∀ f ∈ I, (fun s => MvPolynomial.eval (γ s) f) =ᶠ[𝓝 t] fun _ => 0) :
    ∀ g ∈ idealConormal (Sum.inl : σ → σ ⊕ τ) (γ t) I,
      ∑ i, g i * v i = 0 := by
  classical
  have hgen (f : MvPolynomial (σ ⊕ τ) ℂ) (hf : f ∈ I) :
      ∑ i, partialGradient (Sum.inl : σ → σ ⊕ τ) (γ t) f i * v i = 0 := by
    have hd := hasDerivAt_eval_curve f γ (Sum.elim v 0) t (by
      intro i
      cases i with
      | inl i => exact hγz i
      | inr i => exact hγH i)
    have hdz : HasDerivAt (fun s => MvPolynomial.eval (γ s) f) 0 t :=
      (hasDerivAt_const t (0 : ℂ)).congr_of_eventuallyEq (hzero f hf)
    have h := hd.unique hdz
    simpa [Fintype.sum_sum_type,partialGradient] using h
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      rcases hg with ⟨f,hf,rfl⟩
      exact hgen f hf
  | zero => simp
  | add g h _ _ hg hh => simp [add_mul,Finset.sum_add_distrib,hg,hh]
  | smul a g _ hg => simpa [mul_assoc,← Finset.mul_sum] using congrArg (a * ·) hg

theorem idealConormal_annihilates_curve_excluding_polynomial
    {σ : Type u} {τ : Type v} [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial (σ ⊕ τ) ℂ)) (S : Set ((σ ⊕ τ) → ℂ))
    (hIS : ∀ f ∈ I, ∀ q ∈ S, MvPolynomial.eval q f = 0)
    (γ : ℂ → (σ ⊕ τ) → ℂ) (v : σ → ℂ) (t : ℂ)
    (hγz : ∀ i, HasDerivAt (fun s => γ s (.inl i)) (v i) t)
    (hγH : ∀ i, HasDerivAt (fun s => γ s (.inr i)) 0 t)
    (hcont : ∀ᶠ s in 𝓝 t, ContinuousAt γ s)
    (P : Polynomial ℂ) (hP : P ≠ 0)
    (hS : ∀ᶠ s in 𝓝 t, P.eval s ≠ 0 → γ s ∈ S) :
    ∀ g ∈ idealConormal (Sum.inl : σ → σ ⊕ τ) (γ t) I,
      ∑ i, g i * v i = 0 := by
  apply idealConormal_annihilates_curve I γ v t hγz hγH
  intro f hf
  refine eventually_zero_of_polynomial_exclusion _ t ?_ P hP ?_
  · filter_upwards [hcont] with s hs
    exact f.continuous_eval.continuousAt.comp hs
  · filter_upwards [hS] with s hs hp
    exact hIS f hf (γ s) (hs hp)

#assert_trust kernel hasDerivAt_eval_curve
#assert_trust kernel continuousAt_zero_of_polynomial_exclusion
#assert_trust kernel continuousOn_zero_of_polynomial_exclusion
#assert_trust kernel eventually_zero_of_polynomial_exclusion
#assert_trust kernel idealConormal_annihilates_curve
#assert_trust kernel idealConormal_annihilates_curve_excluding_polynomial
#print axioms hasDerivAt_eval_curve
#print axioms idealConormal_annihilates_curve
end NLA.Proofs.TR26
