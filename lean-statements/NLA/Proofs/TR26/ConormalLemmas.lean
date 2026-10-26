import NLA.Statements.TR26

/-! Evaluated partial conormal spaces of actual polynomial ideals.
The generator theorem requires equality with the full ideal, and vanishing
at the evaluation point; it does not replace either obligation in TR-26. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
universe u v
namespace NLA.Proofs.TR26
open MvPolynomial

def partialGradient {σ : Type u} {ι : Type v} (index : ι → σ) (x : σ → ℂ)
    (f : MvPolynomial σ ℂ) : ι → ℂ :=
  fun i => MvPolynomial.eval x (MvPolynomial.pderiv (index i) f)

theorem partialGradient_zero {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) : partialGradient index x 0 = 0 := by
  ext i
  simp [partialGradient]

theorem partialGradient_add {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (f g : MvPolynomial σ ℂ) :
    partialGradient index x (f+g) = partialGradient index x f + partialGradient index x g := by
  ext i
  simp [partialGradient]

theorem partialGradient_mul {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (f g : MvPolynomial σ ℂ) :
    partialGradient index x (f*g) =
      MvPolynomial.eval x f • partialGradient index x g +
      MvPolynomial.eval x g • partialGradient index x f := by
  ext i
  simp [partialGradient]

def idealConormal {σ : Type u} {ι : Type v} (index : ι → σ) (x : σ → ℂ)
    (I : Ideal (MvPolynomial σ ℂ)) : Submodule ℂ (ι → ℂ) :=
  Submodule.span ℂ (partialGradient index x '' (I : Set (MvPolynomial σ ℂ)))

theorem gradient_mem_conormal {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (I : Ideal (MvPolynomial σ ℂ))
    {f : MvPolynomial σ ℂ} (hf : f ∈ I) : partialGradient index x f ∈ idealConormal index x I :=
  Submodule.subset_span ⟨f,hf,rfl⟩

theorem idealConormal_mono {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) {I J : Ideal (MvPolynomial σ ℂ)} (h : I ≤ J) :
    idealConormal index x I ≤ idealConormal index x J := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f,hf,rfl⟩
  exact gradient_mem_conormal index x J (h hf)

theorem idealConormal_span {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (S : Set (MvPolynomial σ ℂ))
    (hS : ∀ f ∈ S, MvPolynomial.eval x f = 0) :
    idealConormal index x (Ideal.span S) =
      Submodule.span ℂ (partialGradient index x '' S) := by
  let V := Submodule.span ℂ (partialGradient index x '' S)
  have hmem {f : MvPolynomial σ ℂ} (hf : f ∈ Ideal.span S) :
      MvPolynomial.eval x f = 0 ∧ partialGradient index x f ∈ V := by
    induction hf using Submodule.span_induction with
    | mem f hf => exact ⟨hS f hf, Submodule.subset_span ⟨f,hf,rfl⟩⟩
    | zero => exact ⟨by simp, by rw [partialGradient_zero]; exact V.zero_mem⟩
    | add f g _ _ hf hg =>
        constructor
        · simp [hf.1,hg.1]
        · rw [partialGradient_add]
          exact V.add_mem hf.2 hg.2
    | smul a f _ hf =>
        constructor
        · simp [smul_eq_mul,hf.1]
        · simpa only [smul_eq_mul, partialGradient_mul, hf.1, zero_smul, add_zero] using
            V.smul_mem (MvPolynomial.eval x a) hf.2
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f,hf,rfl⟩
    exact (hmem hf).2
  · apply Submodule.span_le.mpr
    rintro _ ⟨f,hf,rfl⟩
    exact gradient_mem_conormal index x (Ideal.span S) (Ideal.subset_span hf)

theorem gradient_mul_at_zero {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (f u : MvPolynomial σ ℂ)
    (hf : MvPolynomial.eval x f = 0) :
    partialGradient index x (u*f) = MvPolynomial.eval x u • partialGradient index x f := by
  rw [partialGradient_mul, hf, zero_smul, add_zero]

theorem gradient_mem_iff_mul_at_zero {σ : Type u} {ι : Type v}
    (index : ι → σ) (x : σ → ℂ) (f u : MvPolynomial σ ℂ)
    (hf : MvPolynomial.eval x f = 0) (hu : MvPolynomial.eval x u ≠ 0)
    (V : Submodule ℂ (ι → ℂ)) :
    partialGradient index x (u*f) ∈ V ↔ partialGradient index x f ∈ V := by
  rw [gradient_mul_at_zero index x f u hf]
  exact V.smul_mem_iff hu

#assert_trust kernel partialGradient_zero
#assert_trust kernel partialGradient_add
#assert_trust kernel partialGradient_mul
#assert_trust kernel gradient_mem_conormal
#assert_trust kernel idealConormal_mono
#assert_trust kernel idealConormal_span
#assert_trust kernel gradient_mul_at_zero
#assert_trust kernel gradient_mem_iff_mul_at_zero
#print axioms idealConormal_span
#print axioms gradient_mem_iff_mul_at_zero
end NLA.Proofs.TR26
