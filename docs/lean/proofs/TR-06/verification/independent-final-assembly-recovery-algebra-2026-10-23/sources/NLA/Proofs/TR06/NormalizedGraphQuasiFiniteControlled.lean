import NLA.Proofs.TR06.NormalizedGraphQuasiFiniteRows

/-! Actual controlled graph points give genuine algebraic quasi-finite
characters for the exact selected real rows. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Topology BigOperators NNReal
namespace NLA.Proofs.TR06
open Set Filter NLA.TR06 NLA.TR06.Segre NLA.TR06.Area.Proposed
open GraphAlgebra GraphCharacter GraphProjection NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r k : ℕ}
attribute [local instance] RingHom.ker_isPrime

/-- The actual open projection-inverse witness controls the tangent of any
whole-graph smooth chart, in the ambient Hilbert product's Euclidean coordinates. -/
theorem controlled_normalizedGraph_chart_derivative_injective
    {K : ℝ≥0} (σ : Fin k ↪ Fin (graphAmbientDimension d n r))
    (e : OpenPartialHomeomorph (Euclid k) (normalizedAnnularGraph d n r))
    (u : Euclid k) (hu : u ∈ e.source)
    (hsm : DifferentiableAt ℝ (fun v => (e v).val) u)
    (hinj : Function.Injective (fderiv ℝ (fun v => (e v).val) u))
    (hctl : graphEuclideanEquiv d n r (e u).val ∈
      ControlledProjectionSet K (euclideanNormalizedGraph d n r) σ) :
    Function.Injective (fderiv ℝ
      (fun v => coordProjection σ (graphEuclideanEquiv d n r (e v).val)) u) := by
  let c := e.transHomeomorph (graphSetHomeomorph d n r)
  have hce : DifferentiableAt ℝ (fun v => (c v).val) u :=
    (graphEuclideanEquiv d n r).toContinuousLinearEquiv.differentiableAt.comp u hsm
  have hcj : Function.Injective (fderiv ℝ (fun v => (c v).val) u) := by
    have hchain := ((graphEuclideanEquiv d n r).toContinuousLinearEquiv.hasFDerivAt.comp u
      hsm.hasFDerivAt).fderiv
    change fderiv ℝ (fun v => (c v).val) u =
      (graphEuclideanEquiv d n r).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fun v => (e v).val) u) at hchain
    rw [hchain]
    exact (graphEuclideanEquiv d n r).injective.comp hinj
  exact controlled_projection_chart_derivative_injective σ c u hu hce hcj hctl

/-- Every actual controlled point has nonzero genuine pivot data whose exact
normalized graph point is that point and whose actual row map is quasi-finite.
No finite-fiber or algebraic regularity premise is assumed. -/
theorem controlled_normalizedGraph_exists_quasiFinite_character
    (hd : 0 < d) {K : ℝ≥0}
    (σ : Fin (expectedDimension d n r) ↪ Fin (graphAmbientDimension d n r))
    (z : normalizedAnnularGraph d n r)
    (hctl : graphEuclideanEquiv d n r z.val ∈
      ControlledProjectionSet K (euclideanNormalizedGraph d n r) σ) :
    ∃ (q : Fin r → TensorIndex d n) (p : Parameter ℝ q)
      (hp : ∀ i, p ⟨i,none⟩ ≠ 0),
      normalizedPivotGraph q p = z.val ∧
      Function.Injective (fderiv ℝ (rowProjectedValues q (graphProjectionRows σ)) p) ∧
      (rowProjectionHom q (graphProjectionRows σ)).toRingHom.QuasiFiniteAt
        (RingHom.ker (character q p hp).toRingHom) := by
  classical
  obtain ⟨e,u,hu,he,hsm,_hinput,hfull,c,hsub,hformula⟩ :=
    exists_normalizedGraph_chart hd z
  have hdiff : DifferentiableAt ℝ (fun v => (e v).val) u :=
    ((hsm.of_le (by simp)).contDiffAt (e.open_source.mem_nhds hu)).differentiableAt one_ne_zero
  have hproj := controlled_normalizedGraph_chart_derivative_injective σ e u hu hdiff
    (hfull u hu) (by simpa only [he] using hctl)
  have hlocal : (fun v => (e v).val) =ᶠ[𝓝 u] branchMap c := by
    filter_upwards [e.open_source.mem_nhds hu] with v hv
    exact hformula v hv
  have hrowslocal :
      (fun v => coordProjection σ (graphEuclideanEquiv d n r (e v).val)) =ᶠ[𝓝 u]
      (fun v => coordProjection σ (graphEuclideanEquiv d n r (branchMap c v))) :=
    hlocal.mono (fun _ h => congrArg (fun a => coordProjection σ (graphEuclideanEquiv d n r a)) h)
  rw [hrowslocal.fderiv_eq] at hproj
  have hpivot : ∀ i, ∃ q : TensorIndex d n, c.summands u i q ≠ 0 := by
    intro i
    by_contra! h
    exact ((c.decomposes u (hsub hu)).1 i).1 (by ext q; exact h q)
  choose q hpivot using hpivot
  let p := chartGraphParameter c q u
  have hp : ∀ i, p ⟨i,none⟩ ≠ 0 := fun i => hpivot i
  have hpinj := chart_rowProjected_derivative_injective σ c q u (hsub hu) hpivot hproj
  refine ⟨q,p,hp,?_,hpinj,quasiFiniteAt_rowProjection_of_fderiv_injective q
    (graphProjectionRows σ) p hp hpinj⟩
  have hparam := (normalizedPivotGraph_chart_eventuallyEq c q u (hsub hu) hpivot).self_of_nhds
  exact hparam.trans ((hformula u hu).symm.trans (congrArg Subtype.val he))

#assert_trust kernel controlled_normalizedGraph_chart_derivative_injective
#assert_trust kernel controlled_normalizedGraph_exists_quasiFinite_character
#print axioms controlled_normalizedGraph_exists_quasiFinite_character
end NLA.Proofs.TR06
