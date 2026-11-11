import NLA.Proofs.TR26.CurveNormalRank

/-! Differentiation at fixed matrix parameters and the exact finite-dimensional
span argument used for the rank converse. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem hasDerivAt_eval_fixed_parameter {d : ℕ} (f : IncidenceRing d)
    (ζ : ℂ → CurveVector d) (H : Parameter d) (v : CurveVector d) (t : ℂ)
    (hζ : ∀ i, HasDerivAt (fun s => ζ s i) (v i) t) :
    HasDerivAt (fun s => MvPolynomial.eval (incidenceCoordinates (ζ s) H) f)
      (∑ i, partialGradient (Sum.inl : Index d → IncidenceVariable d)
        (incidenceCoordinates (ζ t) H) f i * v i) t := by
  have hh := hasDerivAt_eval_curve f (fun s => incidenceCoordinates (ζ s) H)
    (Sum.elim v 0) t (by
      intro i
      cases i with
      | inl i => exact hζ i
      | inr i => exact hasDerivAt_const t (H i))
  simpa [Fintype.sum_sum_type,partialGradient] using hh

theorem gradient_annihilates_of_eval_identically_zero {d : ℕ}
    (f : IncidenceRing d) (ζ : ℂ → CurveVector d) (H : Parameter d)
    (v : CurveVector d) (t : ℂ)
    (hζ : ∀ i, HasDerivAt (fun s => ζ s i) (v i) t)
    (hzero : ∀ s, MvPolynomial.eval (incidenceCoordinates (ζ s) H) f = 0) :
    ∑ i, partialGradient (Sum.inl : Index d → IncidenceVariable d)
      (incidenceCoordinates (ζ t) H) f i * v i = 0 := by
  have hh := hasDerivAt_eval_fixed_parameter f ζ H v t hζ
  have hz : HasDerivAt (fun s => MvPolynomial.eval (incidenceCoordinates (ζ s) H) f) 0 t := by
    simpa only [hzero] using hasDerivAt_const t (0 : ℂ)
  exact hh.unique hz

theorem span_annihilates_pairing {ι κ : Type*} [Fintype ι]
    (w : κ → ι → ℂ) (v : ι → ℂ)
    (hw : ∀ j, ∑ i, w j i * v i = 0) :
    ∀ g ∈ Submodule.span ℂ (Set.range w), ∑ i, g i * v i = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg => rcases hg with ⟨j,rfl⟩; exact hw j
  | zero => simp
  | add g h _ _ hg hh => simp [add_mul,Finset.sum_add_distrib,hg,hh]
  | smul a g _ hg => simpa [mul_assoc,← Finset.mul_sum] using congrArg (a * ·) hg

theorem submodule_eq_span_of_rank_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Submodule ℂ (ι → ℂ)) (w : κ → ι → ℂ)
    (hw : LinearIndependent ℂ w) (hmem : ∀ j, w j ∈ S)
    (hrank : Module.finrank ℂ S ≤ Fintype.card κ) :
    S = Submodule.span ℂ (Set.range w) := by
  have hle : Submodule.span ℂ (Set.range w) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hmem j
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_span_eq_card hw]
  exact le_antisymm (by simpa only [finrank_span_eq_card hw] using Submodule.finrank_mono hle) hrank

#assert_trust kernel hasDerivAt_eval_fixed_parameter
#assert_trust kernel gradient_annihilates_of_eval_identically_zero
#assert_trust kernel span_annihilates_pairing
#assert_trust kernel submodule_eq_span_of_rank_bound
#print axioms submodule_eq_span_of_rank_bound
end NLA.Proofs.TR26
