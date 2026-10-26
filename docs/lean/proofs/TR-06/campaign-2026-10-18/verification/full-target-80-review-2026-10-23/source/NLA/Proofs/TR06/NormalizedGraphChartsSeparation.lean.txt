import NLA.Proofs.TR06.NormalizedGraphChartsRadial

/-! Finite normalized permutation branches separate near every actual regular
point. The separating output cell and coordinate neighborhood are open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphCharts
open scoped Topology
open Set Filter NLA.TR06
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def outputCell (b : AngularOutput d n r) : Set (AngularOutput d n r) :=
  ⋂ σ : {σ : Equiv.Perm (Fin r) // σ ≠ Equiv.refl _},
    {y | dist y b < dist y (permuteAngular σ.val b)}

theorem isOpen_outputCell (b : AngularOutput d n r) : IsOpen (outputCell b) := by
  apply isOpen_iInter_of_finite
  intro σ
  exact isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)

theorem self_mem_outputCell (b : AngularOutput d n r)
    (hfree : ∀ σ : Equiv.Perm (Fin r), permuteAngular σ b = b → σ = Equiv.refl _) :
    b ∈ outputCell b := by
  apply mem_iInter.mpr
  intro σ
  change dist b b < dist b (permuteAngular σ.val b)
  rw [dist_self]
  exact dist_pos.mpr (fun h => σ.property (hfree σ.val h.symm))

theorem exists_open_separating_neighborhood {H : Type*} [TopologicalSpace H]
    (f : H → AngularOutput d n r) (u : H) (hf : ContinuousAt f u)
    (hfree : ∀ σ : Equiv.Perm (Fin r), permuteAngular σ (f u) = f u → σ = Equiv.refl _) :
    ∃ W : Set H, IsOpen W ∧ u ∈ W ∧
      (∀ v ∈ W, f v ∈ outputCell (f u)) ∧
      (∀ v ∈ W, ∀ σ : Equiv.Perm (Fin r), σ ≠ Equiv.refl _ →
        permuteAngular σ (f v) ∉ outputCell (f u)) := by
  have hchosen : ∀ᶠ v in 𝓝 u, f v ∈ outputCell (f u) :=
    hf.preimage_mem_nhds ((isOpen_outputCell _).mem_nhds (self_mem_outputCell _ hfree))
  have hother : ∀ σ : {σ : Equiv.Perm (Fin r) // σ ≠ Equiv.refl _},
      ∀ᶠ v in 𝓝 u,
        dist (permuteAngular σ.val (f v)) (permuteAngular σ.val (f u)) <
          dist (permuteAngular σ.val (f v)) (f u) := by
    intro σ
    have hc := (permuteAngular σ.val).continuous.continuousAt.comp hf
    apply (hc.dist continuousAt_const).eventually_lt (hc.dist continuousAt_const)
    simpa only [Function.comp_apply,dist_self] using dist_pos.mpr (fun h => σ.property (hfree σ.val h))
  have hnear : {v | f v ∈ outputCell (f u) ∧
      ∀ σ : {σ : Equiv.Perm (Fin r) // σ ≠ Equiv.refl _},
        dist (permuteAngular σ.val (f v)) (permuteAngular σ.val (f u)) <
          dist (permuteAngular σ.val (f v)) (f u)} ∈ 𝓝 u :=
    hchosen.and (Filter.eventually_all.mpr hother)
  obtain ⟨W,hWsubset,hWopen,huW⟩ := mem_nhds_iff.mp hnear
  refine ⟨W,hWopen,huW,fun v hv => (hWsubset hv).1,?_⟩
  intro v hv σ hσ hcell
  have hcellσ := mem_iInter.mp hcell ⟨σ,hσ⟩
  exact (not_lt_of_gt ((hWsubset hv).2 ⟨σ,hσ⟩)) hcellσ

def permuteSmoothChart (c : SmoothDecompositionChart d n r) (σ : Equiv.Perm (Fin r)) :
    SmoothDecompositionChart d n r where
  chart := c.chart
  input_smooth := c.input_smooth
  input_injective_derivative := c.input_injective_derivative
  summands u := c.summands u ∘ σ
  decomposes u hu := decomposes_perm (c.decomposes u hu) σ
  summands_smooth i := c.summands_smooth (σ i)
  output_smooth := by
    simp only [normalizedTuple_perm]
    exact (permuteAngular σ).toContinuousLinearEquiv.contDiff.comp_contDiffOn c.output_smooth

#assert_trust kernel outputCell
#assert_trust kernel isOpen_outputCell
#assert_trust kernel self_mem_outputCell
#assert_trust kernel exists_open_separating_neighborhood
#assert_trust kernel permuteSmoothChart
#print axioms exists_open_separating_neighborhood
#print axioms permuteSmoothChart
end NLA.Proofs.TR06.NormalizedGraphCharts
