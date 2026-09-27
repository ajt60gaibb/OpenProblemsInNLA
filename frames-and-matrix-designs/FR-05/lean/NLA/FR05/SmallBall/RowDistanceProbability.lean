import NLA.FR05.Geometry.LeastSingular
import Mathlib.MeasureTheory.Constructions.Pi
import NLA.FR05.Measure.ProductSections

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory Matrix WithLp Set
open scoped BigOperators RealInnerProductSpace ENNReal

namespace NLA.FR05

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem otherRowSpan_eq_span_subtype (A : Matrix ι ι ℝ) (i : ι) :
    otherRowSpan A i = Submodule.span ℝ (Set.range
      (fun j : {j : ι // j ≠ i} ↦ toLp 2 (A j))) := by
  unfold otherRowSpan
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.property, rfl⟩

theorem exists_unit_otherRowNormal (A : Matrix ι ι ℝ) (i : ι) :
    ∃ v : EuclideanSpace ℝ ι, ‖v‖ = 1 ∧
      ∀ j : ι, j ≠ i → inner ℝ v (toLp 2 (A j)) = 0 := by
  have hc : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    simp [Fintype.card_subtype_compl]
  have hd : Module.finrank ℝ (otherRowSpan A i) ≤ Fintype.card ι - 1 := by
    rw [otherRowSpan_eq_span_subtype]
    simpa [Set.finrank, hc] using (finrank_range_le_card (R := ℝ)
      (fun j : {j : ι // j ≠ i} ↦ toLp 2 (A j)))
  have hsum := (otherRowSpan A i).finrank_add_finrank_orthogonal
  have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := by simp
  have hpos : 0 < Module.finrank ℝ (otherRowSpan A i)ᗮ := by
    by_contra h
    rw [Nat.eq_zero_of_not_pos h, add_zero, hdim] at hsum
    lia
  let : Nontrivial (otherRowSpan A i)ᗮ := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨w, hw⟩ := exists_norm_eq (otherRowSpan A i)ᗮ (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨w, hw, fun j hj ↦ ?_⟩
  exact (Submodule.mem_orthogonal' _ _).mp w.property (toLp 2 (A j))
    (Submodule.subset_span ⟨j, hj, rfl⟩)

def rowNearSpan (A : Matrix ι ι ℝ) (i : ι) (t : ℝ) : Prop :=
  ∃ c : {j : ι // j ≠ i} → ℝ,
    ‖toLp 2 (A i) - ∑ j, c j • toLp 2 (A j)‖ < t

theorem isOpen_rowNearSpan (i : ι) (t : ℝ) :
    IsOpen {A : ι → ι → ℝ | rowNearSpan A i t} := by
  change IsOpen {A | ∃ c : {j : ι // j ≠ i} → ℝ, _}
  simp only [Set.ofPred_exists]
  apply isOpen_iUnion
  intro c
  apply isOpen_lt _ continuous_const
  fun_prop

theorem rowSpanDistanceBad_implies_rowNearSpan {A : Matrix ι ι ℝ} {i : ι} {t : ℝ}
    (h : RowSpanDistanceBad A i t) : rowNearSpan A i t := by
  obtain ⟨d, ⟨⟨z, hz, he⟩, _⟩, hd⟩ := h
  rw [otherRowSpan_eq_span_subtype, Submodule.mem_span_range_iff_exists_fun] at hz
  obtain ⟨c, rfl⟩ := hz
  exact ⟨c, he ▸ hd⟩

theorem rowNearSpan_inner_lt {A : Matrix ι ι ℝ} {i : ι} {t : ℝ}
    {v : EuclideanSpace ℝ ι} (hv : ‖v‖ = 1)
    (horth : ∀ j : ι, j ≠ i → inner ℝ v (toLp 2 (A j)) = 0)
    (h : rowNearSpan A i t) :
    |inner ℝ v (toLp 2 (A i))| < t := by
  obtain ⟨c, hc⟩ := h
  have hz : inner ℝ v (∑ j : {j : ι // j ≠ i}, c j • toLp 2 (A j)) = 0 := by
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [inner_smul_right, horth j j.property, mul_zero]
  have he : inner ℝ v (toLp 2 (A i) - ∑ j : {j : ι // j ≠ i}, c j • toLp 2 (A j)) =
      inner ℝ v (toLp 2 (A i)) := by rw [inner_sub_right, hz, sub_zero]
  have h := abs_real_inner_le_norm v (toLp 2 (A i) - ∑ j : {j : ι // j ≠ i}, c j • toLp 2 (A j))
  rw [he, hv, one_mul] at h
  exact h.trans_lt hc

variable {α : Type*} [MeasurableSpace α]

def rowSampleSplit (i : ι) :
    (ι → α) ≃ᵐ (({j : ι // j ≠ i} → α) × α) :=
  ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι ↦ α) (fun j ↦ j = i)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} ↦ α)).prodCongr
      (MeasurableEquiv.refl _))).trans MeasurableEquiv.prodComm

theorem measurePreserving_rowSampleSplit (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
    MeasurePreserving (rowSampleSplit (α := α) i) (Measure.pi fun _ : ι ↦ μ)
      ((Measure.pi fun _ : {j : ι // j ≠ i} ↦ μ).prod μ) := by
  exact (Measure.measurePreserving_swap).comp
    (((measurePreserving_piUnique (fun _ : {j : ι // j = i} ↦ μ)).prod
      (MeasurePreserving.id _)).comp
        (by
          convert (measurePreserving_piEquivPiSubtypeProd (fun _ : ι ↦ μ) (fun j ↦ j = i)) using 1
          · rfl
          · congr 2
            exact Subsingleton.elim _ _))

omit [Fintype ι] in
theorem rowSampleSplit_symm_self (i : ι) (p : ({j : ι // j ≠ i} → α) × α) :
    (rowSampleSplit i).symm p i = p.2 := by
  simp [rowSampleSplit, MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm, MeasurableEquiv.piUnique, MeasurableEquiv.refl, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd]

omit [Fintype ι] in
theorem rowSampleSplit_symm_other (i : ι) (p : ({j : ι // j ≠ i} → α) × α)
    (j : ι) (hj : j ≠ i) :
    (rowSampleSplit i).symm p j = p.1 ⟨j, hj⟩ := by
  simp [rowSampleSplit, MeasurableEquiv.prodCongr, MeasurableEquiv.prodComm, MeasurableEquiv.piUnique, MeasurableEquiv.refl, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]

/-- Pointwise normals suffice after taking measurable product sections. -/
theorem iid_rowNearSpan_le (μ : Measure α) [IsProbabilityMeasure μ]
    (r : α → ι → ℝ) (hr : Measurable r) (i : ι) (t : ℝ) (p : ℝ≥0∞)
    (hsmall : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      μ {x | |inner ℝ v (toLp 2 (r x))| ≤ t} ≤ p) :
    (Measure.pi fun _ : ι ↦ μ) {x | rowNearSpan (fun j ↦ r (x j)) i t} ≤ p := by
  let s := {x : ι → α | rowNearSpan (fun j ↦ r (x j)) i t}
  have hm : Measurable (fun x : ι → α ↦ (fun j : ι ↦ r (x j))) :=
    measurable_pi_lambda _ (fun j ↦ hr.comp (measurable_pi_apply j))
  have hs0 : MeasurableSet {A : ι → ι → ℝ | rowNearSpan A i t} :=
    (isOpen_rowNearSpan i t).measurableSet
  have hs : MeasurableSet s :=
    MeasurableSet.preimage (f := fun x : ι → α ↦ fun j : ι ↦ r (x j)) hs0 hm
  rw [← (MeasurePreserving.symm (rowSampleSplit i) (measurePreserving_rowSampleSplit μ i)).measure_preimage hs.nullMeasurableSet]
  apply prod_measure_le_of_sections_le _ _ (hs.preimage (rowSampleSplit i).symm.measurable) p
  intro others
  let A : Matrix ι ι ℝ := fun j ↦ if h : j = i then 0 else r (others ⟨j, h⟩)
  obtain ⟨v, hv, ho⟩ := exists_unit_otherRowNormal A i
  apply (measure_mono _).trans (hsmall v hv)
  intro x hx
  have hx' : rowNearSpan (fun j ↦ r ((rowSampleSplit i).symm (others, x) j)) i t := hx
  have hh := rowNearSpan_inner_lt hv (A := fun j ↦ r ((rowSampleSplit i).symm (others, x) j))
    (fun j hj ↦ by simpa [A, hj, rowSampleSplit_symm_other i _ j hj] using ho j hj) hx'
  simpa [rowSampleSplit_symm_self] using hh.le


theorem iid_rowNearSpan_reindex_le {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (μ : Measure α) [IsProbabilityMeasure μ]
    (r : α → ι → ℝ) (hr : Measurable r) (i : ι) (t : ℝ) (p : ℝ≥0∞)
    (hsmall : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      μ {x | |inner ℝ v (toLp 2 (r x))| ≤ t} ≤ p) :
    (Measure.pi fun _ : κ ↦ μ) {x | rowNearSpan (fun j ↦ r (x (e j))) i t} ≤ p := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ α) e.symm
  have hE : MeasurePreserving E (Measure.pi fun _ : κ ↦ μ) (Measure.pi fun _ : ι ↦ μ) :=
    measurePreserving_piCongrLeft (fun _ : ι ↦ μ) e.symm
  have hs : MeasurableSet {x : ι → α | rowNearSpan (fun j ↦ r (x j)) i t} :=
    MeasurableSet.preimage (f := fun x : ι → α ↦ fun j : ι ↦ r (x j))
      (isOpen_rowNearSpan i t).measurableSet
      (measurable_pi_lambda _ fun j ↦ hr.comp (measurable_pi_apply j))
  have he : {x : κ → α | rowNearSpan (fun j ↦ r (x (e j))) i t} =
      E ⁻¹' {x : ι → α | rowNearSpan (fun j ↦ r (x j)) i t} := by
    have heval (x : κ → α) : E x = fun j ↦ x (e j) := by
      funext j
      simpa only [Equiv.symm_apply_apply] using
        MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι ↦ α) e.symm x (e j)
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, heval]
  rw [he, hE.measure_preimage hs.nullMeasurableSet]
  exact iid_rowNearSpan_le μ r hr i t p hsmall

end NLA.FR05
