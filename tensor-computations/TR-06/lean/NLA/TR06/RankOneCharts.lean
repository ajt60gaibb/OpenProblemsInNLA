/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Data.Fintype.Sigma
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal Topology
open Filter Set

namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ}

/-- At a nonzero tensor pivot every factor's pivot coordinate is nonzero. -/
theorem pureTensor_factor_pivot_ne_zero
    (u : (j : Fin d) → Fin (n j) → ℝ) (q₀ : TensorIndex d n)
    (h : pureTensor u q₀ ≠ 0) (j : Fin d) : u j (q₀ j) ≠ 0 := by
  change (∏ k, u k (q₀ k)) ≠ 0 at h
  exact (Finset.prod_ne_zero_iff.mp h) j (Finset.mem_univ j)

/-- A coordinate slice divided by a nonzero tensor pivot recovers the normalized
factor, independently of all factor-rescaling choices. -/
theorem pureTensor_slice_div_pivot
    (u : (j : Fin d) → Fin (n j) → ℝ) (q₀ : TensorIndex d n)
    (h : pureTensor u q₀ ≠ 0) (j : Fin d) (i : Fin (n j)) :
    pureTensor u (Function.update q₀ j i) / pureTensor u q₀ =
      u j i / u j (q₀ j) := by
  change (∏ k, u k ((Function.update q₀ j i) k)) / (∏ k, u k (q₀ k)) = _
  rw [← Finset.prod_div_distrib]
  calc
    ∏ k, u k ((Function.update q₀ j i) k) / u k (q₀ k) =
        ∏ k : Fin d, if k = j then u j i / u j (q₀ j) else 1 := by
      apply Finset.prod_congr rfl
      intro k hk
      by_cases hkj : k = j
      · subst k
        simp
      · simp [hkj,
          pureTensor_factor_pivot_ne_zero u q₀ h k]
    _ = u j i / u j (q₀ j) := by simp

/-- The canonical factor coordinates of a rank-one tensor on a nonzero pivot
chart. Their pivot entries equal one. -/
def pivotFactors (q₀ : TensorIndex d n) (A : Tensor ℝ d n)
    (j : Fin d) (i : Fin (n j)) : ℝ :=
  A (Function.update q₀ j i) / A q₀

theorem pivotFactors_pivot (q₀ : TensorIndex d n) (A : Tensor ℝ d n)
    (h : A q₀ ≠ 0) (j : Fin d) : pivotFactors q₀ A j (q₀ j) = 1 := by
  simp [pivotFactors, h]

/-- Exact Segre pivot reconstruction, with no floating-point or root choices.
The amplitude is the actual tensor pivot and each factor is normalized there. -/
theorem rankOne_pivot_reconstruction (q₀ : TensorIndex d n) (A : Tensor ℝ d n)
    (hA : RankOne A) (hp : A q₀ ≠ 0) :
    A = (A q₀) • pureTensor (pivotFactors q₀ A) := by
  obtain ⟨_, u, rfl⟩ := hA
  ext q
  change (∏ j, u j (q j)) =
    (∏ j, u j (q₀ j)) * ∏ j, pivotFactors q₀ (pureTensor u) j (q j)
  have hslice (j : Fin d) : pivotFactors q₀ (pureTensor u) j (q j) =
      u j (q j) / u j (q₀ j) :=
    pureTensor_slice_div_pivot u q₀ hp j (q j)
  simp_rw [hslice]
  rw [Finset.prod_div_distrib]
  exact (mul_div_cancel₀ (∏ j, u j (q j)) hp).symm

/-- Scalar multiplication can be absorbed into any chosen tensor mode. -/
theorem pureTensor_smul_factor
    (u : (j : Fin d) → Fin (n j) → ℝ) (j₀ : Fin d) (amplitude : ℝ) :
    pureTensor (Function.update u j₀ (fun i => amplitude * u j₀ i)) = amplitude • pureTensor u := by
  ext q
  change (∏ j, (Function.update u j₀ (fun i => amplitude * u j₀ i)) j (q j)) =
    amplitude * ∏ j, u j (q j)
  calc
    _ = ∏ j, (if j = j₀ then amplitude else 1) * u j (q j) := by
      apply Finset.prod_congr rfl
      intro j hj
      by_cases h : j = j₀
      · subst j; simp
      · simp [h]
    _ = amplitude * ∏ j, u j (q j) := by rw [Finset.prod_mul_distrib]; simp

/-- Free normalized-factor coordinates exclude the pivot entry in each mode. -/
abbrev PivotIndex (q₀ : TensorIndex d n) :=
  (j : Fin d) × {i : Fin (n j) // i ≠ q₀ j}

abbrev PivotData (q₀ : TensorIndex d n) := ℝ × (PivotIndex q₀ → ℝ)

def expandedPivotFactors (q₀ : TensorIndex d n) (w : PivotIndex q₀ → ℝ)
    (j : Fin d) (i : Fin (n j)) : ℝ :=
  if h : i = q₀ j then 1 else w ⟨j, ⟨i, h⟩⟩

def tensorFromPivotData (q₀ : TensorIndex d n) (p : PivotData q₀) : Tensor ℝ d n :=
  p.1 • pureTensor (expandedPivotFactors q₀ p.2)

def tensorToPivotData (q₀ : TensorIndex d n) (A : Tensor ℝ d n) : PivotData q₀ :=
  (A q₀, fun t => pivotFactors q₀ A t.1 t.2.val)

theorem expandedPivotFactors_pivot (q₀ : TensorIndex d n) (w : PivotIndex q₀ → ℝ)
    (j : Fin d) : expandedPivotFactors q₀ w j (q₀ j) = 1 := by
  simp [expandedPivotFactors]

theorem pureTensor_expandedPivotFactors_pivot (q₀ : TensorIndex d n)
    (w : PivotIndex q₀ → ℝ) : pureTensor (expandedPivotFactors q₀ w) q₀ = 1 := by
  change (∏ j, expandedPivotFactors q₀ w j (q₀ j)) = 1
  simp [expandedPivotFactors_pivot]

theorem tensorFromPivotData_pivot (q₀ : TensorIndex d n) (p : PivotData q₀) :
    tensorFromPivotData q₀ p q₀ = p.1 := by
  change p.1 * pureTensor (expandedPivotFactors q₀ p.2) q₀ = p.1
  rw [pureTensor_expandedPivotFactors_pivot, mul_one]

theorem tensorFromPivotData_rankOne (q₀ : TensorIndex d n) (j₀ : Fin d)
    (p : PivotData q₀) (hp : p.1 ≠ 0) : RankOne (tensorFromPivotData q₀ p) := by
  refine ⟨?_, ?_⟩
  · intro hzero
    have := congrArg (fun A : Tensor ℝ d n => A q₀) hzero
    exact hp (by simpa [tensorFromPivotData_pivot] using this)
  · exact ⟨Function.update (expandedPivotFactors q₀ p.2) j₀
      (fun i => p.1 * expandedPivotFactors q₀ p.2 j₀ i),
      pureTensor_smul_factor _ j₀ p.1⟩

theorem tensorToPivotData_from (q₀ : TensorIndex d n) (p : PivotData q₀)
    (hp : p.1 ≠ 0) : tensorToPivotData q₀ (tensorFromPivotData q₀ p) = p := by
  apply Prod.ext
  · exact tensorFromPivotData_pivot q₀ p
  · funext t
    change tensorFromPivotData q₀ p (Function.update q₀ t.1 t.2.val) /
      tensorFromPivotData q₀ p q₀ = p.2 t
    rw [tensorFromPivotData_pivot]
    change (p.1 * pureTensor (expandedPivotFactors q₀ p.2)
      (Function.update q₀ t.1 t.2.val)) / p.1 = p.2 t
    have hpure : pureTensor (expandedPivotFactors q₀ p.2) q₀ ≠ 0 := by
      rw [pureTensor_expandedPivotFactors_pivot]; exact one_ne_zero
    have hslice := pureTensor_slice_div_pivot (expandedPivotFactors q₀ p.2)
      q₀ hpure t.1 t.2.val
    simp only [pureTensor_expandedPivotFactors_pivot, div_one,
      expandedPivotFactors_pivot] at hslice
    rw [hslice]
    simp [expandedPivotFactors, t.2.property, hp]

theorem tensorFromPivotData_to (q₀ : TensorIndex d n) (A : Tensor ℝ d n)
    (hA : RankOne A) (hp : A q₀ ≠ 0) :
    tensorFromPivotData q₀ (tensorToPivotData q₀ A) = A := by
  have hf : expandedPivotFactors q₀ (tensorToPivotData q₀ A).2 = pivotFactors q₀ A := by
    funext j i
    by_cases hi : i = q₀ j
    · subst i
      simp [expandedPivotFactors, pivotFactors_pivot, hp]
    · simp [expandedPivotFactors, tensorToPivotData, hi]
  change (A q₀) • pureTensor (expandedPivotFactors q₀ (tensorToPivotData q₀ A).2) = A
  rw [hf]
  exact (rankOne_pivot_reconstruction q₀ A hA hp).symm

theorem continuous_tensorFromPivotData (q₀ : TensorIndex d n) :
    Continuous (tensorFromPivotData q₀) := by
  change Continuous (fun p : PivotData q₀ =>
    WithLp.toLp 2 (fun q : TensorIndex d n => p.1 * ∏ j, expandedPivotFactors q₀ p.2 j (q j)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro q
  apply continuous_fst.mul
  apply continuous_finsetProd
  intro j hj
  unfold expandedPivotFactors
  split_ifs <;> fun_prop

theorem continuousOn_tensorToPivotData (q₀ : TensorIndex d n) :
    ContinuousOn (tensorToPivotData q₀) {A | A q₀ ≠ 0} := by
  apply (PiLp.continuous_apply 2 _ q₀).continuousOn.prodMk
  apply continuousOn_pi.2
  intro t
  exact (PiLp.continuous_apply 2 _ (Function.update q₀ t.1 t.2.val)).continuousOn.div
    (PiLp.continuous_apply 2 _ q₀).continuousOn (fun A hA => hA)

/-- An actual coordinate homeomorphism of the nonzero-pivot rank-one locus
with a nonzero amplitude and freely varying normalized factor coordinates. -/
def rankOnePivotHomeomorph (q₀ : TensorIndex d n) (j₀ : Fin d) :
    {A : Tensor ℝ d n // RankOne A ∧ A q₀ ≠ 0} ≃ₜ
      {p : PivotData q₀ // p.1 ≠ 0} where
  toFun A := ⟨tensorToPivotData q₀ A.val, A.property.2⟩
  invFun p := ⟨tensorFromPivotData q₀ p.val,
    tensorFromPivotData_rankOne q₀ j₀ p.val p.property,
    by rw [tensorFromPivotData_pivot]; exact p.property⟩
  left_inv A := by
    apply Subtype.ext
    exact tensorFromPivotData_to q₀ A.val A.property.1 A.property.2
  right_inv p := by
    apply Subtype.ext
    exact tensorToPivotData_from q₀ p.val p.property
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hcont : ContinuousOn (tensorToPivotData q₀)
        {A : Tensor ℝ d n | RankOne A ∧ A q₀ ≠ 0} :=
      (continuousOn_tensorToPivotData q₀).mono (fun A hA => hA.2)
    exact hcont.domRestrict
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_tensorFromPivotData q₀).comp continuous_subtype_val

theorem isOpen_rankOnePivotSet (q₀ : TensorIndex d n) :
    IsOpen {A : {A : Tensor ℝ d n // RankOne A} | A.val q₀ ≠ 0} := by
  exact isOpen_ne_fun ((PiLp.continuous_apply 2 _ q₀).comp continuous_subtype_val)
    continuous_const

theorem isOpen_nonzeroPivotData (q₀ : TensorIndex d n) :
    IsOpen {p : PivotData q₀ | p.1 ≠ 0} :=
  isOpen_ne_fun continuous_fst continuous_const

theorem card_pivotIndex (q₀ : TensorIndex d n) :
    Fintype.card (PivotIndex q₀) = ∑ j, (n j - 1) := by
  simp only [PivotIndex, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fintype.card_subtype_compl]
  simp

theorem contDiff_tensorFromPivotData (q₀ : TensorIndex d n)
    (smoothness : WithTop ℕ∞) : ContDiff ℝ smoothness (tensorFromPivotData q₀) := by
  apply (contDiff_piLp 2).2
  intro q
  change ContDiff ℝ smoothness (fun p : PivotData q₀ =>
    p.1 * ∏ j, expandedPivotFactors q₀ p.2 j (q j))
  apply contDiff_fst.mul
  apply contDiff_prod
  intro j hj
  unfold expandedPivotFactors
  split_ifs <;> fun_prop

theorem contDiffOn_tensorToPivotData (q₀ : TensorIndex d n)
    (smoothness : WithTop ℕ∞) :
    ContDiffOn ℝ smoothness (tensorToPivotData q₀) {A | A q₀ ≠ 0} := by
  apply (contDiff_piLp_apply 2 (i := q₀)).contDiffOn.prodMk
  apply contDiffOn_pi.2
  intro t
  exact (contDiff_piLp_apply 2 (i := Function.update q₀ t.1 t.2.val)).contDiffOn.div
    (contDiff_piLp_apply 2 (i := q₀)).contDiffOn (fun A hA => hA)

theorem finrank_pivotData (q₀ : TensorIndex d n) :
    Module.finrank ℝ (PivotData q₀) = 1 + ∑ j, (n j - 1) := by
  change Module.finrank ℝ (ℝ × (PivotIndex q₀ → ℝ)) = _
  rw [Module.finrank_prod, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, card_pivotIndex]

theorem finrank_orderedPivotData {r : ℕ} (q₀ : Fin r → TensorIndex d n) :
    Module.finrank ℝ ((i : Fin r) → PivotData (q₀ i)) = expectedDimension d n r := by
  rw [Module.finrank_pi_fintype]
  simp [expectedDimension]

abbrev OrderedPivotData {r : ℕ} (q₀ : Fin r → TensorIndex d n) :=
  (i : Fin r) → PivotData (q₀ i)

def orderedTensorToPivotData {r : ℕ} (q₀ : Fin r → TensorIndex d n)
    (a : Fin r → Tensor ℝ d n) : OrderedPivotData q₀ :=
  fun i => tensorToPivotData (q₀ i) (a i)

def orderedTensorFromPivotData {r : ℕ} (q₀ : Fin r → TensorIndex d n)
    (p : OrderedPivotData q₀) : Fin r → Tensor ℝ d n :=
  fun i => tensorFromPivotData (q₀ i) (p i)

def orderedRankOnePivotHomeomorph {r : ℕ} (q₀ : Fin r → TensorIndex d n)
    (j₀ : Fin d) :
    {a : OrderedRankOne d n r // ∀ i, a.val i (q₀ i) ≠ 0} ≃ₜ
      {p : OrderedPivotData q₀ // ∀ i, (p i).1 ≠ 0} where
  toFun a := ⟨orderedTensorToPivotData q₀ a.val.val, a.property⟩
  invFun p := ⟨⟨orderedTensorFromPivotData q₀ p.val,
      fun i => tensorFromPivotData_rankOne (q₀ i) j₀ (p.val i) (p.property i)⟩,
    by intro i; exact (tensorFromPivotData_pivot (q₀ i) (p.val i)).trans_ne (p.property i)⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact tensorFromPivotData_to (q₀ i) (a.val.val i) (a.val.property i) (a.property i)
  right_inv p := by
    apply Subtype.ext
    funext i
    exact tensorToPivotData_from (q₀ i) (p.val i) (p.property i)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hcoord : Continuous (fun a : {a : OrderedRankOne d n r // ∀ i, a.val i (q₀ i) ≠ 0} =>
        (⟨a.val.val i, a.val.property i, a.property i⟩ :
          {A : Tensor ℝ d n // RankOne A ∧ A (q₀ i) ≠ 0})) := by
      apply Continuous.subtype_mk
      exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)
    exact continuous_subtype_val.comp ((rankOnePivotHomeomorph (q₀ i) j₀).continuous.comp hcoord)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (continuous_tensorFromPivotData (q₀ i)).comp
      ((continuous_apply i).comp continuous_subtype_val)

theorem isOpen_orderedRankOnePivotSet {r : ℕ} (q₀ : Fin r → TensorIndex d n) :
    IsOpen {a : OrderedRankOne d n r | ∀ i, a.val i (q₀ i) ≠ 0} := by
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_ne_fun ((PiLp.continuous_apply 2 _ (q₀ i)).comp
    ((continuous_apply i).comp continuous_subtype_val)) continuous_const

theorem isOpen_orderedNonzeroPivotData {r : ℕ} (q₀ : Fin r → TensorIndex d n) :
    IsOpen {p : OrderedPivotData q₀ | ∀ i, (p i).1 ≠ 0} := by
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_ne_fun (continuous_fst.comp (continuous_apply i)) continuous_const

theorem contDiff_orderedTensorFromPivotData {r : ℕ}
    (q₀ : Fin r → TensorIndex d n) (smoothness : WithTop ℕ∞) :
    ContDiff ℝ smoothness (orderedTensorFromPivotData q₀) := by
  apply contDiff_pi.2
  intro i
  exact (contDiff_tensorFromPivotData (q₀ i) smoothness).comp
    (contDiff_pi.mp contDiff_id i)

theorem contDiffOn_orderedTensorToPivotData {r : ℕ}
    (q₀ : Fin r → TensorIndex d n) (smoothness : WithTop ℕ∞) :
    ContDiffOn ℝ smoothness (orderedTensorToPivotData q₀)
      {a | ∀ i, a i (q₀ i) ≠ 0} := by
  apply contDiffOn_pi.2
  intro i
  exact (contDiffOn_tensorToPivotData (q₀ i) smoothness).comp
    (contDiff_apply ℝ (Tensor ℝ d n) i).contDiffOn
    (fun a ha => ha i)

theorem isOpen_orderedTensorPivotSet {r : ℕ} (q₀ : Fin r → TensorIndex d n) :
    IsOpen {a : Fin r → Tensor ℝ d n | ∀ i, a i (q₀ i) ≠ 0} := by
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_ne_fun ((PiLp.continuous_apply 2 _ (q₀ i)).comp
    (continuous_apply i)) continuous_const

def chartPivotMap {r : ℕ} (c : SmoothDecompositionChart d n r)
    (q₀ : Fin r → TensorIndex d n)
    (v : EuclideanSpace ℝ (Fin (expectedDimension d n r))) : OrderedPivotData q₀ :=
  orderedTensorToPivotData q₀ (c.summands v)

def pivotSum {r : ℕ} (q₀ : Fin r → TensorIndex d n) (p : OrderedPivotData q₀) :
    Tensor ℝ d n := ∑ i, tensorFromPivotData (q₀ i) (p i)

theorem contDiff_pivotSum {r : ℕ} (q₀ : Fin r → TensorIndex d n)
    (smoothness : WithTop ℕ∞) : ContDiff ℝ smoothness (pivotSum q₀) := by
  apply ContDiff.sum
  intro i hi
  exact (contDiff_tensorFromPivotData (q₀ i) smoothness).comp
    (contDiff_pi.mp contDiff_id i)

theorem chart_summands_contDiffAt {r : ℕ} (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    ContDiffAt ℝ 1 c.summands u := by
  have hsum : ContDiffOn ℝ 1 c.summands c.chart.source :=
    contDiffOn_pi.2 (fun i => (c.summands_smooth i).of_le (by simp))
  exact hsum.contDiffAt (c.chart.open_source.mem_nhds hu)

theorem chartPivotMap_contDiffAt {r : ℕ} (c : SmoothDecompositionChart d n r)
    (q₀ : Fin r → TensorIndex d n)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (hp : ∀ i, c.summands u i (q₀ i) ≠ 0) :
    ContDiffAt ℝ 1 (chartPivotMap c q₀) u := by
  exact ((contDiffOn_orderedTensorToPivotData q₀ 1).contDiffAt
    ((isOpen_orderedTensorPivotSet q₀).mem_nhds hp)).comp u
    (chart_summands_contDiffAt c u hu)

theorem pivotSum_chartPivotMap_eventuallyEq {r : ℕ}
    (c : SmoothDecompositionChart d n r) (q₀ : Fin r → TensorIndex d n)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (hp : ∀ i, c.summands u i (q₀ i) ≠ 0) :
    (fun v => pivotSum q₀ (chartPivotMap c q₀ v)) =ᶠ[𝓝 u] fun v => (c.chart v).val := by
  have hnear : ∀ᶠ v in 𝓝 u, ∀ i, c.summands v i (q₀ i) ≠ 0 :=
    (chart_summands_contDiffAt c u hu).continuousAt.preimage_mem_nhds
      ((isOpen_orderedTensorPivotSet q₀).mem_nhds hp)
  filter_upwards [c.chart.open_source.mem_nhds hu, hnear] with v hv hpv
  change (∑ i, tensorFromPivotData (q₀ i) (tensorToPivotData (q₀ i) (c.summands v i))) = _
  calc
    _ = ∑ i, c.summands v i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact tensorFromPivotData_to (q₀ i) (c.summands v i) ((c.decomposes v hv).1 i) (hpv i)
    _ = (c.chart v).val := (c.decomposes v hv).2

theorem chartPivotMap_injective_derivative {r : ℕ}
    (c : SmoothDecompositionChart d n r) (q₀ : Fin r → TensorIndex d n)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (hp : ∀ i, c.summands u i (q₀ i) ≠ 0) :
    Function.Injective (fderiv ℝ (chartPivotMap c q₀) u) := by
  have hchain := fderiv_comp u
    ((contDiff_pivotSum q₀ 1).differentiable (by norm_num)).differentiableAt
    ((chartPivotMap_contDiffAt c q₀ u hu hp).differentiableAt (by norm_num))
  have heq := (pivotSum_chartPivotMap_eventuallyEq c q₀ u hu hp).fderiv_eq (𝕜 := ℝ)
  simp only [Function.comp_def] at hchain
  rw [hchain] at heq
  intro x y hxy
  apply c.input_injective_derivative u hu
  rw [← heq]
  exact congrArg (fderiv ℝ (pivotSum q₀) (chartPivotMap c q₀ u)) hxy

theorem chartPivotMap_exists_localHomeomorph {r : ℕ}
    (c : SmoothDecompositionChart d n r) (q₀ : Fin r → TensorIndex d n)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source)
    (hp : ∀ i, c.summands u i (q₀ i) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (expectedDimension d n r)))
        (OrderedPivotData q₀),
      u ∈ e.source ∧ (e : _ → _) = chartPivotMap c q₀ := by
  have hcont := chartPivotMap_contDiffAt c q₀ u hu hp
  have hinj := chartPivotMap_injective_derivative c q₀ u hu hp
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (expectedDimension d n r))) =
      Module.finrank ℝ (OrderedPivotData q₀) := by
    rw [finrank_euclideanSpace_fin, finrank_orderedPivotData]
  let L := ((fderiv ℝ (chartPivotMap c q₀) u).toLinearMap.linearEquivOfInjective
    hinj hdim).toContinuousLinearEquiv
  have hderiv : HasFDerivAt (chartPivotMap c q₀) (L : _ →L[ℝ] _) u :=
    hcont.differentiableAt (by norm_num) |>.hasFDerivAt
  exact ⟨hcont.toOpenPartialHomeomorph _ hderiv (by norm_num),
    hcont.mem_toOpenPartialHomeomorph_source hderiv (by norm_num), rfl⟩

theorem sourceSmoothSet_subset_identifiable {r : ℕ} :
    sourceSmoothSet d n r ⊆ identifiableRealSet d n r := by
  rintro A ⟨c, u, hu, rfl⟩
  exact (c.chart u).property

theorem sourceSmoothSet_relatively_open {r : ℕ} :
    IsOpen {A : identifiableRealSet d n r | A.val ∈ sourceSmoothSet d n r} := by
  rw [isOpen_iff_mem_nhds]
  rintro A ⟨c, u, hu, heq⟩
  have heq' : c.chart u = A := Subtype.ext heq
  have htarget : A ∈ c.chart.target := heq' ▸ c.chart.map_source hu
  filter_upwards [c.chart.open_target.mem_nhds htarget] with B hB
  exact ⟨c, c.chart.symm B, c.chart.map_target hB,
    congrArg Subtype.val (c.chart.right_inv hB)⟩

theorem isOpenEmbedding_sourceSmoothInclusion {r : ℕ} :
    Topology.IsOpenEmbedding
      (Set.inclusion (sourceSmoothSet_subset_identifiable (d := d) (n := n) (r := r))) := by
  apply Topology.IsOpenEmbedding.inclusion
  exact sourceSmoothSet_relatively_open

theorem isOpenEmbedding_restrict_open_source
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (W : Set X) (hW : IsOpen W) (hsub : W ⊆ e.source) :
    Topology.IsOpenEmbedding (fun v : W => e v.val) := by
  exact e.isOpenEmbedding_restrict.comp
    (Topology.IsOpenEmbedding.inclusion hsub (hW.preimage continuous_subtype_val))

/-- Smooth summand coordinates are locally an open embedding into the entire
ordered rank-one product. The proof uses explicit Segre coordinates and the
inverse function theorem, rather than an unformalized invariance-of-domain claim. -/
theorem smooth_summands_local_open_embedding {r : ℕ}
    (c : SmoothDecompositionChart d n r) (j₀ : Fin d)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    ∃ W : Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))),
      ∃ _hW : IsOpen W, ∃ _huW : u ∈ W, ∃ hsub : W ⊆ c.chart.source,
        Topology.IsOpenEmbedding (fun v : W =>
          (⟨c.summands v.val, (c.decomposes v.val (hsub v.property)).1⟩ :
            OrderedRankOne d n r)) := by
  have hnonzero (i : Fin r) : c.summands u i ≠ 0 := (c.decomposes u hu).1 i |>.1
  have hpiv (i : Fin r) : ∃ q : TensorIndex d n, c.summands u i q ≠ 0 := by
    by_contra h
    push Not at h
    apply hnonzero i
    ext q
    exact h q
  choose q₀ hp using hpiv
  obtain ⟨e, hue, he⟩ := chartPivotMap_exists_localHomeomorph c q₀ u hu hp
  let V : Set (OrderedPivotData q₀) := {p | ∀ i, (p i).1 ≠ 0}
  have hV : IsOpen V := isOpen_orderedNonzeroPivotData q₀
  let e₁ := e.restrOpen c.chart.source c.chart.open_source
  let e₂ := e₁.trans (OpenPartialHomeomorph.ofSet V hV)
  have he₁ (v) : e₁ v = chartPivotMap c q₀ v := by
    change e v = _
    exact congrFun he v
  have he₂ (v) : e₂ v = chartPivotMap c q₀ v := he₁ v
  have hu₂ : u ∈ e₂.source := by
    change u ∈ e.source ∩ c.chart.source ∧ e₁ u ∈ V
    exact ⟨⟨hue, hu⟩, by rw [he₁]; exact hp⟩
  have hsub : e₂.source ⊆ c.chart.source := fun v hv => hv.1.2
  have hmaps (v : e₂.source) : e₂ v.val ∈ V := by
    change e₁ v.val ∈ V
    exact v.property.2
  let F : e₂.source → V := fun v => ⟨e₂ v.val, hmaps v⟩
  have hF : Topology.IsOpenEmbedding F :=
    Topology.IsOpenEmbedding.of_comp F hV.isOpenEmbedding_subtypeVal
      e₂.isOpenEmbedding_restrict
  let H := orderedRankOnePivotHomeomorph q₀ j₀
  let decoder : V → OrderedRankOne d n r := fun p => (H.symm p).val
  have hdecoder : Topology.IsOpenEmbedding decoder :=
    (isOpen_orderedRankOnePivotSet q₀).isOpenEmbedding_subtypeVal.comp H.symm.isOpenEmbedding
  have hbranch : (fun v : e₂.source => decoder (F v)) =
      (fun v : e₂.source =>
        (⟨c.summands v.val, (c.decomposes v.val (hsub v.property)).1⟩ : OrderedRankOne d n r)) := by
    funext v
    apply Subtype.ext
    funext i
    change tensorFromPivotData (q₀ i) (e₂ v.val i) = c.summands v.val i
    rw [he₂]
    exact tensorFromPivotData_to (q₀ i) (c.summands v.val i)
      ((c.decomposes v.val (hsub v.property)).1 i)
      (by have hh := hmaps v; rw [he₂] at hh; exact hh i)
  refine ⟨e₂.source, e₂.open_source, hu₂, hsub, ?_⟩
  rw [← hbranch]
  exact hdecoder.comp hF

/-- Every smooth decomposition branch is the actual local inverse of tensor
addition on an open subset of the entire ordered rank-one product. -/
theorem smooth_chart_is_local_addition_inverse {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (hd : 3 ≤ d) (_hn : ∀ j, 2 ≤ n j) (_hr : 3 ≤ r)
    (c : SmoothDecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    IsLocalAdditionInverse c u := by
  let j₀ : Fin d := ⟨0, by omega⟩
  obtain ⟨W, hW, huW, hsub, hb⟩ := smooth_summands_local_open_embedding c j₀ u hu
  let b : W → OrderedRankOne d n r := fun v =>
    ⟨c.summands v.val, (c.decomposes v.val (hsub v.property)).1⟩
  let f : W → sourceSmoothSet d n r := fun v =>
    ⟨(c.chart v.val).val, ⟨c.toSourceSmoothChart, v.val, hsub v.property, rfl⟩⟩
  have hf : Topology.IsOpenEmbedding f :=
    Topology.IsOpenEmbedding.of_comp f isOpenEmbedding_sourceSmoothInclusion
      (isOpenEmbedding_restrict_open_source c.chart W hW hsub)
  let : Nonempty W := ⟨⟨u, huW⟩⟩
  let eB := hb.toOpenPartialHomeomorph b
  let eF := hf.toOpenPartialHomeomorph f
  let e := eB.symm.trans eF
  refine ⟨e, ?_, W, hW, huW, hsub, ?_⟩
  · intro a ha
    change a ∈ eB.target ∧ eB.symm a ∈ eF.source at ha
    have hbwa : b (eB.symm a) = a := eB.right_inv ha.1
    change (f (eB.symm a)).val = ∑ i, a.val i
    calc
      (f (eB.symm a)).val = ∑ i, (b (eB.symm a)).val i :=
        (c.decomposes (eB.symm a).val (hsub (eB.symm a).property)).2.symm
      _ = ∑ i, a.val i := by rw [hbwa]
  · intro v hv
    let w : W := ⟨v, hv⟩
    have hwB : w ∈ eB.source := by simp [eB]
    have hwF : w ∈ eF.source := by simp [eF]
    have hleft : eB.symm (b w) = w := eB.left_inv hwB
    refine ⟨b w, ?_, rfl, ?_⟩
    · change b w ∈ eB.target ∧ eB.symm (b w) ∈ eF.source
      exact ⟨eB.map_source hwB, hleft ▸ hwF⟩
    · change (f (eB.symm (b w))).val = (c.chart v).val
      rw [hleft]

end NLA.TR06

#print axioms NLA.TR06.rankOne_pivot_reconstruction
#assert_trust kernel NLA.TR06.rankOne_pivot_reconstruction

#print axioms NLA.TR06.rankOnePivotHomeomorph
#assert_trust kernel NLA.TR06.rankOnePivotHomeomorph

#print axioms NLA.TR06.contDiffOn_tensorToPivotData
#assert_trust kernel NLA.TR06.contDiffOn_tensorToPivotData
#print axioms NLA.TR06.finrank_orderedPivotData
#assert_trust kernel NLA.TR06.finrank_orderedPivotData

#print axioms NLA.TR06.orderedRankOnePivotHomeomorph
#assert_trust kernel NLA.TR06.orderedRankOnePivotHomeomorph

#print axioms NLA.TR06.chartPivotMap_exists_localHomeomorph
#assert_trust kernel NLA.TR06.chartPivotMap_exists_localHomeomorph

#print axioms NLA.TR06.smooth_summands_local_open_embedding
#assert_trust kernel NLA.TR06.smooth_summands_local_open_embedding

#print axioms NLA.TR06.smooth_chart_is_local_addition_inverse
#assert_trust kernel NLA.TR06.smooth_chart_is_local_addition_inverse
