import NLA.Proofs.TR06.NormalizedGraphChartsBasic

/-! Genuine smooth embedded charts in the whole normalized annular graph.
All finite ordered permutation branches are retained and locally separated. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphCharts
open scoped Topology
open Set Filter NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem lift_chart (c : SmoothDecompositionChart d n r) (j₀ : Fin d)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (hann : (1/2 : ℝ) < ‖(c.chart u).val‖ ∧ ‖(c.chart u).val‖ < 3) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
        (normalizedAnnularGraph d n r),
      u ∈ e.source ∧ e.source ⊆ c.chart.source ∧
      (∀ v ∈ e.source, (e v).val = branchMap c v) ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (e v).val) e.source ∧
      (∀ v ∈ e.source, Function.Injective (fderiv ℝ (fun w => (e w).val.ofLp.1) v)) ∧
      (∀ v ∈ e.source, Function.Injective (fderiv ℝ (fun w => (e w).val) v)) := by
  classical
  let E := EuclideanSpace ℝ (Fin (expectedDimension d n r))
  let out := fun v : E => normalizedTuple (c.summands v)
  have hcont : ContinuousAt out u := c.output_smooth.continuousOn.continuousAt
    (c.chart.open_source.mem_nhds hu)
  have hfree : ∀ σ : Equiv.Perm (Fin r), permuteAngular σ (out u) = out u → σ = Equiv.refl _ :=
    fun σ heq => chart_normalizedTuple_permutation_stabilizer c j₀ u hu σ heq
  obtain ⟨N,hN,huN,hchosen,hother⟩ := exists_open_separating_neighborhood out u hcont hfree
  let V : Set E := c.chart.source ∩
    {v | (1/2 : ℝ) < ‖(c.chart v).val‖ ∧ ‖(c.chart v).val‖ < 3}
  have hV : IsOpen V := c.input_smooth.continuousOn.isOpen_inter_preimage c.chart.open_source
    ((isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const))
  let W := N ∩ V
  have hW : IsOpen W := hN.inter hV
  have huW : u ∈ W := ⟨huN,hu,hann⟩
  have hWs : W ⊆ c.chart.source := fun _ h => h.2.1
  have hannW (v : E) (hv : v ∈ W) : (1/2 : ℝ) < ‖(c.chart v).val‖ ∧ ‖(c.chart v).val‖ < 3 := hv.2.2
  let I : Set (identifiableRealSet d n r) := c.chart '' W
  have hI : IsOpen I := c.chart.isOpen_image_of_subset_source hW hWs
  let T : Set (normalizedAnnularGraph d n r) := graphInput ⁻¹' I ∩
    (fun z => z.val.ofLp.2) ⁻¹' outputCell (out u)
  have hT : IsOpen T := (hI.preimage continuous_graphInput).inter
    ((isOpen_outputCell _).preimage continuous_graphOutput)
  have htarget (z : normalizedAnnularGraph d n r) (hz : z ∈ T) :
      ∃ v ∈ W, branchMap c v = z.val := by
    obtain ⟨v,hv,hinput⟩ := hz.1
    have hinputval : (c.chart v).val = z.val.ofLp.1 := congrArg Subtype.val hinput
    obtain ⟨a,ha,hout⟩ := z.property.2.2.2
    have ha' : Decomposes a (c.chart v).val := by rwa [hinputval]
    obtain ⟨σ,hσ⟩ := (c.chart v).property.2 (c.summands v) a (c.decomposes v (hWs hv)) ha'
    have heq : z.val.ofLp.2 = permuteAngular σ (out v) := by
      rw [hout,← normalizedTuple_perm]
      congr 1
      exact funext hσ
    have hσid : σ = Equiv.refl _ := by
      by_contra hσne
      apply hother v hv.1 σ hσne
      rw [← heq]
      exact hz.2
    refine ⟨v,hv,?_⟩
    apply WithLp.ofLp_injective (p := 2)
    apply Prod.ext hinputval
    change out v = z.val.ofLp.2
    rw [heq,hσid]
    rfl
  let z₀ : normalizedAnnularGraph d n r :=
    ⟨branchMap c u,branchMap_mem_graph c u hu hann⟩
  let φ : E → normalizedAnnularGraph d n r := fun v =>
    if hv : v ∈ W then ⟨branchMap c v,branchMap_mem_graph c v (hWs hv) (hannW v hv)⟩ else z₀
  have hφval (v : E) (hv : v ∈ W) : (φ v).val = branchMap c v := by simp only [φ,dif_pos hv]
  have hφinput (v : E) (hv : v ∈ W) : graphInput (φ v) = c.chart v := by
    apply Subtype.ext
    change (φ v).val.ofLp.1 = (c.chart v).val
    rw [hφval v hv]
    rfl
  have hφtarget (v : E) (hv : v ∈ W) : φ v ∈ T := by
    constructor
    · change graphInput (φ v) ∈ I
      rw [hφinput v hv]
      exact ⟨v,hv,rfl⟩
    · change (φ v).val.ofLp.2 ∈ outputCell (out u)
      rw [hφval v hv]
      exact hchosen v hv.1
  let ψ : normalizedAnnularGraph d n r → E := fun z => c.chart.symm (graphInput z)
  have hψφ (v : E) (hv : v ∈ W) : ψ (φ v) = v := by
    change c.chart.symm (graphInput (φ v)) = v
    rw [hφinput v hv]
    exact c.chart.left_inv (hWs hv)
  have hψtarget (z : normalizedAnnularGraph d n r) (hz : z ∈ T) : ψ z ∈ W := by
    obtain ⟨v,hv,hvz⟩ := htarget z hz
    have hzφ : z = φ v := Subtype.ext (hvz.symm.trans (hφval v hv).symm)
    rw [hzφ,hψφ v hv]
    exact hv
  have hφψ (z : normalizedAnnularGraph d n r) (hz : z ∈ T) : φ (ψ z) = z := by
    obtain ⟨v,hv,hvz⟩ := htarget z hz
    have hzφ : z = φ v := Subtype.ext (hvz.symm.trans (hφval v hv).symm)
    rw [hzφ,hψφ v hv]
  have hφsmooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (φ v).val) W :=
    ((contDiffOn_branchMap c).mono hWs).congr hφval
  have hφcont : ContinuousOn φ W :=
    Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hφsmooth.continuousOn
  have hψcont : ContinuousOn ψ T := by
    apply c.chart.continuousOn_symm.comp continuous_graphInput.continuousOn
    intro z hz
    obtain ⟨v,hv,hinput⟩ := hz.1
    rw [← hinput]
    exact c.chart.map_source (hWs hv)
  let e : OpenPartialHomeomorph E (normalizedAnnularGraph d n r) :=
    { toFun := φ
      invFun := ψ
      source := W
      target := T
      map_source' := hφtarget
      map_target' := hψtarget
      left_inv' := hψφ
      right_inv' := hφψ
      continuousOn_toFun := hφcont
      continuousOn_invFun := hψcont
      open_source := hW
      open_target := hT }
  have hinputinj (v : E) (hv : v ∈ W) :
      Function.Injective (fderiv ℝ (fun y => (φ y).val.ofLp.1) v) := by
    have heq : (fun y => (φ y).val.ofLp.1) =ᶠ[𝓝 v] fun y => (c.chart y).val := by
      filter_upwards [hW.mem_nhds hv] with y hy
      rw [hφval y hy]
      rfl
    rw [heq.fderiv_eq]
    exact c.input_injective_derivative v (hWs hv)
  refine ⟨e,huW,hWs,hφval,hφsmooth,hinputinj,?_⟩
  intro v hv
  have hdiff : DifferentiableAt ℝ (fun y => (φ y).val) v :=
    ((hφsmooth.of_le (by simp)).contDiffAt (hW.mem_nhds hv)).differentiableAt one_ne_zero
  have hchain := ((inputProjection (d := d) (n := n) (r := r)).hasFDerivAt.comp v hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => (φ y).val.ofLp.1) v =
    inputProjection.comp (fderiv ℝ (fun y => (φ y).val) v) at hchain
  intro x y hxy
  apply hinputinj v hv
  rw [hchain]
  exact congrArg inputProjection hxy

theorem exists_normalizedGraph_chart (hd : 0 < d) (z : normalizedAnnularGraph d n r) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
        (normalizedAnnularGraph d n r))
      (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))),
      u ∈ e.source ∧ e u = z ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (e v).val) e.source ∧
      (∀ v ∈ e.source, Function.Injective (fderiv ℝ (fun w => (e w).val.ofLp.1) v)) ∧
      (∀ v ∈ e.source, Function.Injective (fderiv ℝ (fun w => (e w).val) v)) ∧
      ∃ c : SmoothDecompositionChart d n r, e.source ⊆ c.chart.source ∧
        ∀ v ∈ e.source, (e v).val = normalizedGraphPoint (c.chart v).val (c.summands v) := by
  obtain ⟨c,u,hu,hcu⟩ := exists_aligned_chart z
  have hann : (1/2 : ℝ) < ‖(c.chart u).val‖ ∧ ‖(c.chart u).val‖ < 3 := by
    have hinput := congrArg (fun X : NormalizedGraphAmbient d n r => X.ofLp.1) hcu
    change (c.chart u).val = z.val.ofLp.1 at hinput
    rw [hinput]
    exact ⟨z.property.2.1,z.property.2.2.1⟩
  obtain ⟨e,hue,hes,heq,hsm,hproj,hfull⟩ := lift_chart c ⟨0,hd⟩ u hu hann
  exact ⟨e,u,hue,Subtype.ext ((heq u hue).trans hcu),hsm,hproj,hfull,c,hes,heq⟩

#assert_trust kernel lift_chart
#assert_trust kernel exists_normalizedGraph_chart
#print axioms lift_chart
#print axioms exists_normalizedGraph_chart
end NLA.Proofs.TR06.NormalizedGraphCharts
