import NLA.Proofs.TR06.NormalizedGraphAreaVolume
import NLA.Proofs.TR06.NormalizedGraphCharts
import Mathlib.Topology.Compactness.Lindelof

/-! A countable measurable disjoint partition of the actual input annulus,
subordinate to actual normalized graph branches. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.NormalizedGraphArea
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set Function NLA.TR06 NormalizedGraphCharts
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

structure InputGraphChart (d : ℕ) (n : Fin d → ℕ) (r : ℕ) where
  graph : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
    (normalizedAnnularGraph d n r)
  original : SmoothDecompositionChart d n r
  source_subset : graph.source ⊆ original.chart.source
  formula : ∀ v ∈ graph.source, (graph v).val = branchMap original v
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun v => (graph v).val) graph.source
  input_injective : ∀ v ∈ graph.source,
    Function.Injective (fderiv ℝ (fun w => (graph w).val.ofLp.1) v)
  derivative_injective : ∀ v ∈ graph.source,
    Function.Injective (fderiv ℝ (fun w => (graph w).val) v)

def InputGraphChart.input (C : InputGraphChart d n r)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) : Tensor ℝ d n :=
  (C.original.chart v).val

def InputGraphChart.inputImage (C : InputGraphChart d n r) : Set (Tensor ℝ d n) :=
  C.input '' C.graph.source

theorem InputGraphChart.input_continuousOn (C : InputGraphChart d n r) :
    ContinuousOn C.input C.graph.source :=
  C.original.input_smooth.continuousOn.mono C.source_subset

theorem InputGraphChart.input_injOn (C : InputGraphChart d n r) :
    InjOn C.input C.graph.source := by
  intro x hx y hy hxy
  exact C.original.chart.injOn (C.source_subset hx) (C.source_subset hy) (Subtype.ext hxy)

theorem InputGraphChart.inputImage_measurable (C : InputGraphChart d n r) :
    MeasurableSet C.inputImage :=
  C.graph.open_source.measurableSet.image_of_continuousOn_injOn C.input_continuousOn C.input_injOn

theorem InputGraphChart.inputImage_relatively_open (C : InputGraphChart d n r) :
    IsOpen {A : identifiableRealSet d n r | A.val ∈ C.inputImage} := by
  have heq : {A : identifiableRealSet d n r | A.val ∈ C.inputImage} =
      C.original.chart '' C.graph.source := by
    ext A
    constructor
    · rintro ⟨v,hv,hval⟩
      exact ⟨v,hv,Subtype.ext hval⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨v,hv,rfl⟩
  rw [heq]
  exact C.original.chart.isOpen_image_of_subset_source C.graph.open_source C.source_subset

theorem exists_inputGraphChart (hd : 0 < d)
    (A : Tensor ℝ d n) (hA : A ∈ HomogeneousGaussian.annulus (smoothRegularSet d n r)) :
    ∃ C : InputGraphChart d n r, A ∈ C.inputImage := by
  obtain ⟨c,u,hu,hcu⟩ := hA.1
  have hdec : Decomposes (c.summands u) A := by
    have h := c.decomposes u hu
    rwa [hcu] at h
  let z : normalizedAnnularGraph d n r := ⟨normalizedGraphPoint A (c.summands u),
    hA.1,lt_of_lt_of_le (by norm_num : (1/2 : ℝ) < 1) hA.2.1,
    hA.2.2.trans (by norm_num),c.summands u,hdec,rfl⟩
  obtain ⟨e,v,hv,hev,hsm,hproj,hfull,c',hsub,hformula⟩ := exists_normalizedGraph_chart hd z
  let C : InputGraphChart d n r := ⟨e,c',hsub,hformula,hsm,hproj,hfull⟩
  refine ⟨C,v,hv,?_⟩
  have h := congrArg (fun X : NormalizedGraphAmbient d n r => X.ofLp.1)
    ((hformula v hv).symm.trans (congrArg Subtype.val hev))
  exact h

theorem exists_countable_input_partition (hd : 0 < d)
    (hne : (HomogeneousGaussian.annulus (smoothRegularSet d n r)).Nonempty) :
    ∃ (C : ℕ → InputGraphChart d n r) (P : ℕ → Set (Tensor ℝ d n)),
      (∀ j, MeasurableSet (P j)) ∧ Pairwise (Disjoint on P) ∧
      HomogeneousGaussian.annulus (smoothRegularSet d n r) = ⋃ j, P j ∧
      ∀ j, P j ⊆ (C j).inputImage := by
  classical
  let S := HomogeneousGaussian.annulus (smoothRegularSet d n r)
  have hS : MeasurableSet S := (measurableSet_smoothRegularSet d n r).inter
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const))
  choose chart hchart using fun A : S => exists_inputGraphChart hd A.val A.property
  let inclusion : S → identifiableRealSet d n r := fun A =>
    ⟨A.val,smoothRegularSet_subset_identifiable A.property.1⟩
  have hc : Continuous inclusion := continuous_subtype_val.subtype_mk _
  let U : S → Set S := fun A => {B | B.val ∈ (chart A).inputImage}
  have hU : ∀ A, IsOpen (U A) := fun A =>
    (chart A).inputImage_relatively_open.preimage hc
  obtain ⟨q,hqcount,hqcover⟩ := isLindelof_univ.elim_countable_subcover U hU (by
    intro A _
    exact mem_iUnion.mpr ⟨A,hchart A⟩)
  obtain ⟨A₀,hA₀⟩ := hne
  have hqne : q.Nonempty := by
    obtain ⟨A,hA,_⟩ := mem_iUnion₂.mp (hqcover (mem_univ (⟨A₀,hA₀⟩ : S)))
    exact ⟨A,hA⟩
  obtain ⟨enumerate,henumerate⟩ := hqcount.exists_surjective hqne
  let C : ℕ → InputGraphChart d n r := fun j => chart (enumerate j).val
  let W : ℕ → Set (Tensor ℝ d n) := fun j => (C j).inputImage
  have hW : ∀ j, MeasurableSet (W j) := fun j => (C j).inputImage_measurable
  have hcover : S ⊆ ⋃ j, W j := by
    intro A hA
    obtain ⟨B,hB,hAB⟩ := mem_iUnion₂.mp (hqcover (mem_univ (⟨A,hA⟩ : S)))
    obtain ⟨j,hj⟩ := henumerate ⟨B,hB⟩
    refine mem_iUnion.mpr ⟨j,?_⟩
    simpa only [W,C,hj,U,mem_ofPred_eq] using hAB
  let P : ℕ → Set (Tensor ℝ d n) := fun j => S ∩ disjointed W j
  refine ⟨C,P,fun j => hS.inter (MeasurableSet.disjointed hW j),?_,?_,?_⟩
  · intro i j hij
    exact (disjoint_disjointed W hij).mono inter_subset_right inter_subset_right
  · change S = ⋃ j, S ∩ disjointed W j
    rw [← inter_iUnion,iUnion_disjointed,inter_eq_left.mpr hcover]
  · intro j A hA
    exact disjointed_subset W j hA.2

#assert_trust kernel InputGraphChart
#assert_trust kernel InputGraphChart.input
#assert_trust kernel InputGraphChart.inputImage
#assert_trust kernel InputGraphChart.input_continuousOn
#assert_trust kernel InputGraphChart.input_injOn
#assert_trust kernel InputGraphChart.inputImage_measurable
#assert_trust kernel InputGraphChart.inputImage_relatively_open
#assert_trust kernel exists_inputGraphChart
#assert_trust kernel exists_countable_input_partition
#print axioms exists_countable_input_partition
end NLA.Proofs.TR06.NormalizedGraphArea
