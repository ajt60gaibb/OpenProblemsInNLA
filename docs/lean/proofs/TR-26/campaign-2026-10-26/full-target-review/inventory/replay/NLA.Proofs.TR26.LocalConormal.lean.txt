import NLA.Proofs.TR26.ConormalLemmas

/-! A localization criterion for conormal spaces. The hypothesis quantifies
over every element of the actual ideal. It records an obligation that must
be proved in each chart; it does not assert that TR-26 satisfies it. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
universe u v
namespace NLA.Proofs.TR26

theorem idealConormal_eq_of_local_generators {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (I : Ideal (MvPolynomial σ ℂ))
    (S : Set (MvPolynomial σ ℂ)) (hSI : ∀ f ∈ S, f ∈ I)
    (hIx : ∀ f ∈ I, MvPolynomial.eval x f = 0)
    (hlocal : ∀ f ∈ I, ∃ u : MvPolynomial σ ℂ,
      MvPolynomial.eval x u ≠ 0 ∧ u*f ∈ Ideal.span S) :
    idealConormal index x I = Submodule.span ℂ (partialGradient index x '' S) := by
  have hS : ∀ f ∈ S, MvPolynomial.eval x f = 0 := fun f hf => hIx f (hSI f hf)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f,hf,rfl⟩
    obtain ⟨u,hu,huf⟩ := hlocal f hf
    apply (gradient_mem_iff_mul_at_zero index x f u (hIx f hf) hu _).mp
    rw [← idealConormal_span index x S hS]
    exact gradient_mem_conormal index x (Ideal.span S) huf
  · apply Submodule.span_le.mpr
    rintro _ ⟨f,hf,rfl⟩
    exact gradient_mem_conormal index x I (hSI f hf)

#assert_trust kernel idealConormal_eq_of_local_generators
#print axioms idealConormal_eq_of_local_generators
end NLA.Proofs.TR26
