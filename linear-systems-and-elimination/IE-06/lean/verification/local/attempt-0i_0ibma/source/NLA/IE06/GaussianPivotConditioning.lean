import NLA.IE06.PivotFiltration
import NLA.IE06.GaussianRestriction
import NLA.IE06.GaussianTies

/-! Original-row pivot partitions and the Gaussian truncation fibers.
Exact preimplementation contract: reviews/gaussian-pivot-conditioning-contract.md.
The canonical scan remains unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators ENNReal
namespace NLA.IE06.GaussianPivotConditioning

/-- Current row positions to original row labels after the first k swaps. -/
def rowLabels {n : ℕ} (p : PivotPath n) : ℕ → Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | k+1 => if h : k < n then (Equiv.swap ⟨k,h⟩ (p ⟨k,h⟩)).trans (rowLabels p k)
      else rowLabels p k

theorem rowLabels_succ {n : ℕ} (p : PivotPath n) (k : Fin n) (i : Fin n) :
    rowLabels p (k.val+1) i = rowLabels p k.val (Equiv.swap k (p k) i) := by
  simp only [rowLabels, dif_pos k.isLt, Equiv.trans_apply]

theorem rowLabels_prefix_congr {n : ℕ} (p q : PivotPath n) (k : ℕ)
    (hpq : ∀ j : Fin n, j.val < k → p j = q j) : rowLabels p k = rowLabels q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hr := ih (fun j hj => hpq j (by omega))
      by_cases hk : k < n
      · simp only [rowLabels, dif_pos hk, hr, hpq ⟨k,hk⟩ (by simp)]
      · simp only [rowLabels, dif_neg hk, hr]

theorem rowLabels_earlier {n : ℕ} (p : PivotPath n) (hp : ∀ j, j ≤ p j)
    (k s : ℕ) (hks : k ≤ s) (i : Fin n) (hi : i.val < k) :
    rowLabels p s i = rowLabels p k i := by
  induction s with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      rfl
  | succ s ih =>
      by_cases hk : k = s+1
      · subst k; rfl
      have hks' : k ≤ s := by omega
      by_cases hs : s < n
      · have his : i ≠ (⟨s,hs⟩ : Fin n) := by
          intro h
          have he : i.val = s := congrArg Fin.val h
          omega
        have hip : i ≠ p ⟨s,hs⟩ := by
          have hactive := hp ⟨s,hs⟩
          intro h
          have he := congrArg Fin.val h
          change s ≤ (p ⟨s,hs⟩).val at hactive
          omega
        rw [rowLabels_succ p ⟨s,hs⟩, Equiv.swap_apply_of_ne_of_ne his hip]
        exact ih hks'
      · simpa only [rowLabels, dif_neg hs] using ih hks'

/-- Selected original row labels, encoded as an injection by restricting the
actual accumulated permutation. Valid also for singular input matrices. -/
def pivotOrder {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Fin t ↪ Fin n where
  toFun j := rowLabels (firstPath A) t (Fin.castLE ht j)
  inj' := (rowLabels (firstPath A) t).injective.comp (Fin.castLE_injective ht)

theorem pivotOrder_stage {n t : ℕ} (ht : t ≤ n) (A : Mat n) (j : Fin t) :
    pivotOrder ht A j = rowLabels (firstPath A) j.val
      (firstPath A (Fin.castLE ht j)) := by
  have hp : ∀ k : Fin n, k ≤ firstPath A k := fun k =>
    (firstPivotIndex_spec_proved (firstTrajectory A k.val) k).1
  change rowLabels (firstPath A) t (Fin.castLE ht j) = _
  rw [rowLabels_earlier (firstPath A) hp (j.val+1) t (by omega)
    (Fin.castLE ht j) (by simp)]
  exact (rowLabels_succ (firstPath A) (Fin.castLE ht j) (Fin.castLE ht j)).trans
    (by simp only [Equiv.swap_apply_left]; rfl)

theorem pivotOrder_columns_congr {n t : ℕ} (ht : t ≤ n) (A B : Mat n)
    (hAB : ColumnsAgree A B t) : pivotOrder ht A = pivotOrder ht B := by
  have hp := rowLabels_prefix_congr (firstPath A) (firstPath B) t
    (PivotFiltration.firstPath_prefix_congr A B t hAB)
  apply DFunLike.ext
  intro j
  exact congrArg (fun e : Equiv.Perm (Fin n) => e (Fin.castLE ht j)) hp

theorem measurable_pivotOrder_coordinate {n t : ℕ} (ht : t ≤ n) (j : Fin t) :
    Measurable (fun A : Mat n => pivotOrder ht A j) := by
  exact (measurable_of_countable (fun p : PivotPath n =>
    rowLabels p t (Fin.castLE ht j))).comp (PivotFiltration.measurable_firstPath n)

/-- The exact finite pivot-order partition; no null-set modification. -/
def orderEvent {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) : Set (Mat n) :=
  {A | pivotOrder ht A = π}

theorem measurableSet_orderEvent {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    MeasurableSet (orderEvent ht π) := by
  have he : orderEvent ht π = ⋂ j : Fin t, {A | pivotOrder ht A j = π j} := by
    ext A
    simp only [orderEvent, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h j => congrArg (fun q : Fin t ↪ Fin n => q j) h,
      fun h => DFunLike.ext _ _ h⟩
  rw [he]
  exact MeasurableSet.iInter (fun j => measurableSet_eq_fun
    (measurable_pivotOrder_coordinate ht j) measurable_const)

theorem orderEvent_partition {n t : ℕ} (ht : t ≤ n) :
    (⋃ π : Fin t ↪ Fin n, orderEvent ht π) = Set.univ := by
  ext A
  simp only [mem_iUnion, orderEvent, mem_ofPred_eq, mem_univ, iff_true]
  exact ⟨pivotOrder ht A, rfl⟩

theorem orderEvent_disjoint {n t : ℕ} (ht : t ≤ n) {π σ : Fin t ↪ Fin n}
    (h : π ≠ σ) : Disjoint (orderEvent ht π) (orderEvent ht σ) := by
  apply Set.disjoint_left.mpr
  intro A hA hB
  exact h (hA.symm.trans hB)


/-- Unselected original row labels for a prescribed pivot order. -/
abbrev RemainingRows {n t : ℕ} (π : Fin t ↪ Fin n) := {i : Fin n // i ∉ Set.range π}

def prefixRows {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Fin n → Fin t → ℝ :=
  fun i j => A i (Fin.castLE ht j)

def selectedBlock {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (A : Mat n) : Mat t :=
  fun i j => A (π i) (Fin.castLE ht j)

def remainingBlock {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (A : Mat n) :
    RemainingRows π → Fin t → ℝ := fun i j => A i.val (Fin.castLE ht j)

theorem gaussian_coordinates_map {n : ℕ} {ι : Type*} [Fintype ι] (e : ι ↪ Fin n) :
    (GaussianQuadratic.gaussianVector n).map (fun x i => x (e i)) =
      Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have hi : iIndepFun (fun i : Fin n => fun x : Fin n → ℝ => x i)
      (GaussianQuadratic.gaussianVector n) :=
    iIndepFun_pi (X := fun _ : Fin n => id) (fun _ => aemeasurable_id)
  have hm := (hi.precomp e.injective).map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (e i)).aemeasurable)
  have he (i : ι) : (GaussianQuadratic.gaussianVector n).map (fun x => x (e i)) =
      gaussianReal 0 1 := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) (e i)).map_eq
  simpa only [he] using hm

theorem gaussian_prefixRows_map {n t : ℕ} (ht : t ≤ n) :
    (gaussianMatrix n).map (prefixRows ht) =
      Measure.pi (fun _ : Fin n => GaussianQuadratic.gaussianVector t) := by
  let e : Fin t ↪ Fin n := ⟨Fin.castLE ht, Fin.castLE_injective ht⟩
  have hm : Measurable (fun x : Fin n → ℝ => fun j : Fin t => x (e j)) := by fun_prop
  change (Measure.pi (fun _ : Fin n => GaussianQuadratic.gaussianVector n)).map
    (fun A i => fun j => A i (e j)) = _
  rw [Measure.pi_map_pi (fun _ => hm.aemeasurable)]
  congr 1
  funext i
  exact gaussian_coordinates_map e

/-- The literal fixed-coordinate decomposition has the product Gaussian law.
It does not condition on which order the adaptive pivot rule actually selects. -/
theorem fixed_blocks_joint_law {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    (gaussianMatrix n).map (fun A => (selectedBlock ht π A, remainingBlock ht π A)) =
      (gaussianMatrix t).prod
        (Measure.pi (fun _ : RemainingRows π => GaussianQuadratic.gaussianVector t)) := by
  classical
  let : Fintype (Set.range π) := Subtype.fintype _
  let e : Fin t ≃ {i : Fin n // i ∈ Set.range π} := Equiv.ofInjective π π.injective
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => GaussianQuadratic.gaussianVector t) (fun i => i ∈ Set.range π)
  have hreindex := measurePreserving_piCongrLeft
    (fun _ : Fin t => GaussianQuadratic.gaussianVector t) e.symm
  have hid : MeasurePreserving (id : (RemainingRows π → Fin t → ℝ) → _)
      (Measure.pi (fun _ : RemainingRows π => GaussianQuadratic.gaussianVector t))
      (Measure.pi (fun _ : RemainingRows π => GaussianQuadratic.gaussianVector t)) :=
    ⟨measurable_id, Measure.map_id⟩
  have hcollect := (hreindex.prod hid).comp hsplit
  have hprefix : MeasurePreserving (prefixRows ht) (gaussianMatrix n)
      (Measure.pi (fun _ : Fin n => GaussianQuadratic.gaussianVector t)) :=
    ⟨by unfold prefixRows; fun_prop, gaussian_prefixRows_map ht⟩
  have hh := (hcollect.comp hprefix).map_eq
  have hf : ((Prod.map (MeasurableEquiv.piCongrLeft (fun _ : Fin t => Fin t → ℝ) e.symm) id ∘
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Fin t → ℝ)
        (fun i => i ∈ Set.range π)) ∘ prefixRows ht) =
      (fun A => (selectedBlock ht π A, remainingBlock ht π A)) := by
    funext A
    apply Prod.ext
    · funext i j
      have hr := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin t => Fin t → ℝ) e.symm
        (fun x : Set.range π => prefixRows ht A x.val) (e i)
      have hrr := congrArg (fun row : Fin t → ℝ => row j) hr
      simp only [Equiv.symm_apply_apply] at hrr
      simpa only [Function.comp_def, Prod.map,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
        Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, prefixRows, selectedBlock,
        e, Equiv.ofInjective_apply] using hrr
    · rfl
  rw [hf] at hh
  exact hh

/-- The no-pivot Schur row used in the fixed selected-row block. -/
def upperRow {t : ℕ} (T : Mat t) (j : Fin t) : Fin t → ℝ :=
  trajectory T id j.val j

def pivotValue {t : ℕ} (T : Mat t) (j : Fin t) : ℝ := upperRow T j j

/-- The residual of an arbitrary original row after eliminating the first s
selected rows. All divisions are the ordinary totalized real divisions. -/
def residualMap {t : ℕ} (T : Mat t) : ℕ → ((Fin t → ℝ) →L[ℝ] (Fin t → ℝ))
  | 0 => ContinuousLinearMap.id ℝ _
  | s+1 => if h : s < t then
      residualMap T s -
        (((pivotValue T ⟨s,h⟩)⁻¹ •
          ((ContinuousLinearMap.proj ⟨s,h⟩).comp (residualMap T s))).smulRight
            (upperRow T ⟨s,h⟩))
      else residualMap T s

def multiplier {t : ℕ} (T : Mat t) (j : Fin t) : (Fin t → ℝ) →L[ℝ] ℝ :=
  (pivotValue T j)⁻¹ • ((ContinuousLinearMap.proj j).comp (residualMap T j.val))

theorem residualMap_succ {t : ℕ} (T : Mat t) (j : Fin t) (x : Fin t → ℝ) :
    residualMap T (j.val+1) x = residualMap T j.val x - multiplier T j x • upperRow T j := by
  simp only [residualMap, dif_pos j.isLt, _root_.sub_apply,
    ContinuousLinearMap.smulRight_apply, multiplier]

def truncationBody {t : ℕ} (T : Mat t) : Set (Fin t → ℝ) :=
  {x | ∀ j : Fin t, |multiplier T j x| ≤ 1}

def strictTruncationBody {t : ℕ} (T : Mat t) : Set (Fin t → ℝ) :=
  {x | ∀ j : Fin t, |multiplier T j x| < 1}

theorem truncationBody_closed {t : ℕ} (T : Mat t) : IsClosed (truncationBody T) := by
  have he : truncationBody T = ⋂ j : Fin t, {x | |multiplier T j x| ≤ 1} := by
    ext x; simp [truncationBody]
  rw [he]
  exact isClosed_iInter fun j => isClosed_le (multiplier T j).continuous.abs continuous_const

theorem truncationBody_convex {t : ℕ} (T : Mat t) : Convex ℝ (truncationBody T) := by
  have he : truncationBody T = ⋂ j : Fin t, (multiplier T j) ⁻¹' Set.Icc (-1) 1 := by
    ext x; simp [truncationBody, abs_le]
  rw [he]
  exact convex_iInter fun j => (convex_Icc (-1 : ℝ) 1).linear_preimage
    (multiplier T j).toLinearMap

theorem truncationBody_symmetric {t : ℕ} (T : Mat t) :
    GaussianShiftGeometry.CentrallySymmetric (truncationBody T) := by
  intro x
  simp only [truncationBody, mem_ofPred_eq, map_neg, abs_neg]

theorem strictTruncationBody_open {t : ℕ} (T : Mat t) :
    IsOpen (strictTruncationBody T) := by
  have he : strictTruncationBody T = ⋂ j : Fin t, {x | |multiplier T j x| < 1} := by
    ext x; simp [strictTruncationBody]
  rw [he]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (multiplier T j).continuous.abs continuous_const

theorem zero_mem_strictTruncationBody {t : ℕ} (T : Mat t) :
    (0 : Fin t → ℝ) ∈ strictTruncationBody T := by
  simp [strictTruncationBody]

theorem strictTruncationBody_subset {t : ℕ} (T : Mat t) :
    strictTruncationBody T ⊆ truncationBody T := fun _ h j => (h j).le


theorem measurable_upperRow {t : ℕ} (j : Fin t) : Measurable (fun T : Mat t => upperRow T j) := by
  exact (measurable_pi_apply j).comp (measurable_trajectory_fixed id j.val)

theorem measurable_pivotValue {t : ℕ} (j : Fin t) : Measurable (fun T : Mat t => pivotValue T j) :=
  (measurable_pi_apply j).comp (measurable_upperRow j)

theorem measurable_residualMap_apply {t : ℕ} (s : ℕ) :
    Measurable (fun z : Mat t × (Fin t → ℝ) => residualMap z.1 s z.2) := by
  induction s with
  | zero => exact measurable_snd
  | succ s ih =>
      by_cases hs : s < t
      · have hp : Measurable (fun z : Mat t × (Fin t → ℝ) => pivotValue z.1 ⟨s,hs⟩) := (measurable_pivotValue (⟨s,hs⟩ : Fin t)).comp measurable_fst
        have hu : Measurable (fun z : Mat t × (Fin t → ℝ) => upperRow z.1 ⟨s,hs⟩) := (measurable_upperRow (⟨s,hs⟩ : Fin t)).comp measurable_fst
        have he := (measurable_pi_apply (⟨s,hs⟩ : Fin t)).comp ih
        have hrec (z : Mat t × (Fin t → ℝ)) := residualMap_succ z.1 (⟨s,hs⟩ : Fin t) z.2
        simp_rw [hrec]
        apply measurable_pi_iff.mpr
        intro j
        change Measurable (fun z : Mat t × (Fin t → ℝ) =>
          residualMap z.1 s z.2 j -
            ((pivotValue z.1 ⟨s,hs⟩)⁻¹ * residualMap z.1 s z.2 ⟨s,hs⟩) * upperRow z.1 ⟨s,hs⟩ j)
        exact ((measurable_pi_apply j).comp ih).sub
          ((hp.inv.mul he).mul ((measurable_pi_apply j).comp hu))
      · simpa only [residualMap, dif_neg hs] using ih

theorem measurable_multiplier {t : ℕ} (j : Fin t) :
    Measurable (fun z : Mat t × (Fin t → ℝ) => multiplier z.1 j z.2) := by
  exact ((measurable_pivotValue j).comp measurable_fst).inv.mul
    ((measurable_pi_apply j).comp (measurable_residualMap_apply j.val))

theorem measurableSet_truncationBody_joint (t : ℕ) :
    MeasurableSet {z : Mat t × (Fin t → ℝ) | z.2 ∈ truncationBody z.1} := by
  have he : {z : Mat t × (Fin t → ℝ) | z.2 ∈ truncationBody z.1} =
      ⋂ j : Fin t, {z | |multiplier z.1 j z.2| ≤ 1} := by
    ext z; simp [truncationBody]
  rw [he]
  exact MeasurableSet.iInter fun j => measurableSet_le (measurable_multiplier j).abs measurable_const

theorem gaussianVector_open_positive (t : ℕ) :
    (GaussianQuadratic.gaussianVector t).IsOpenPosMeasure := by
  have hw : (volume : Measure (Fin t → ℝ)) ≪ volume.withDensity GaussianShift.gaussianWeight :=
    withDensity_absolutelyContinuous' (GaussianShift.gaussianWeight_measurable t).aemeasurable
      (ae_of_all _ fun _ => by unfold GaussianShift.gaussianWeight; positivity)
  let : (volume.withDensity (@GaussianShift.gaussianWeight t)).IsOpenPosMeasure :=
    hw.isOpenPosMeasure
  rw [GaussianShift.gaussianVector_eq_weight]
  exact Measure.isOpenPosMeasure_smul _ (GaussianShift.normalizer_ne_zero t)

/-- The fiber has strictly positive Gaussian mass for every T, even singular T. -/
theorem truncationBody_mass_pos {t : ℕ} (T : Mat t) :
    0 < GaussianQuadratic.gaussianVector t (truncationBody T) := by
  let := gaussianVector_open_positive t
  exact lt_of_lt_of_le ((strictTruncationBody_open T).measure_pos _
    ⟨0, zero_mem_strictTruncationBody T⟩) (measure_mono (strictTruncationBody_subset T))

/-- A level c≠0 of any linear functional is Gaussian-null, including the zero functional. -/
theorem linear_nonzero_level_null {t : ℕ} (f : (Fin t → ℝ) →L[ℝ] ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    GaussianQuadratic.gaussianVector t {x | f x = c} = 0 := by
  classical
  let P : MvPolynomial (Fin t) ℝ :=
    (∑ i : Fin t, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i) - MvPolynomial.C c
  have hev (x : Fin t → ℝ) : MvPolynomial.eval x P = f x - c := by
    have hex : (∑ i : Fin t, x i • Pi.single i (1 : ℝ)) = x := by
      ext j
      simp [Pi.single_apply]
    have hlin := congrArg f hex
    simp only [map_sum, map_smul, smul_eq_mul] at hlin
    simp only [P, MvPolynomial.eval_sub, map_sum, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X]
    rw [show (∑ i : Fin t, f (Pi.single i 1) * x i) = f x by
      simpa only [mul_comm] using hlin]
  have hP : P ≠ 0 := by
    intro h
    have hz := hev 0
    simp only [h, MvPolynomial.eval_zero, map_zero, zero_sub] at hz
    exact hc (neg_eq_zero.mp hz.symm)
  let _ : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hae := GaussianNull.polynomial_ne_zero_ae t (fun _ => gaussianReal 0 1) P hP
  change (Measure.pi (fun _ : Fin t => gaussianReal 0 1)) {x | f x = c} = 0
  have hn : ∀ᵐ x ∂Measure.pi (fun _ : Fin t => gaussianReal 0 1), f x ≠ c := by
    filter_upwards [hae] with x hx
    simpa only [hev, sub_ne_zero] using hx
  simpa only [ae_iff, not_not] using hn

theorem truncationBody_boundary_null {t : ℕ} (T : Mat t) :
    GaussianQuadratic.gaussianVector t (truncationBody T \ strictTruncationBody T) = 0 := by
  have hsub : truncationBody T \ strictTruncationBody T ⊆
      ⋃ j : Fin t, {x | multiplier T j x = 1} ∪ {x | multiplier T j x = -1} := by
    intro x hx
    have hex : ∃ j : Fin t, ¬ |multiplier T j x| < 1 := by
      simpa only [strictTruncationBody, mem_ofPred_eq, not_forall] using hx.2
    obtain ⟨j,hj⟩ := hex
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    have he : |multiplier T j x| = 1 := le_antisymm (hx.1 j) (le_of_not_gt hj)
    simpa only [mem_union, mem_ofPred_eq] using (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp he
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro j
  exact measure_union_null (linear_nonzero_level_null _ 1 (by norm_num))
    (linear_nonzero_level_null _ (-1) (by norm_num))


/-- The exact number of as-yet unselected original rows. -/
theorem remainingRows_card {n t : ℕ} (π : Fin t ↪ Fin n) :
    Fintype.card (RemainingRows π) = n-t := by
  classical
  change Fintype.card ((Set.range π)ᶜ : Set (Fin n)) = n-t
  rw [Fintype.card_compl_set, Fintype.card_fin, Fintype.card_range π, Fintype.card_fin]

/-- Exact normalization for all independent remaining rows, including none. -/
theorem product_restriction_normalized {t : ℕ} {ι : Type*} [Fintype ι] (T : Mat t) :
    (Measure.pi (fun _ : ι => GaussianQuadratic.gaussianVector t)).restrict
      (Set.univ.pi (fun _ : ι => truncationBody T)) =
    (GaussianQuadratic.gaussianVector t (truncationBody T)) ^ Fintype.card ι •
      Measure.pi (fun _ : ι => GaussianRestriction.restrictedGaussian (truncationBody T)) := by
  classical
  let _ := GaussianRestriction.restrictedGaussian_probability (ne_of_gt (truncationBody_mass_pos T))
  rw [Measure.restrict_pi_pi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp only [GaussianRestriction.restrictedGaussian, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel (ne_of_gt (truncationBody_mass_pos T)) (measure_ne_top _ _),
    one_pow, one_mul]

theorem product_restriction_lintegral {t : ℕ} {ι : Type*} [Fintype ι]
    (T : Mat t) (F : (ι → Fin t → ℝ) → ℝ≥0∞) :
    (∫⁻ z in Set.univ.pi (fun _ : ι => truncationBody T), F z
      ∂Measure.pi (fun _ : ι => GaussianQuadratic.gaussianVector t)) =
    (GaussianQuadratic.gaussianVector t (truncationBody T)) ^ Fintype.card ι *
      ∫⁻ z, F z ∂Measure.pi
        (fun _ : ι => GaussianRestriction.restrictedGaussian (truncationBody T)) := by
  rw [product_restriction_normalized, lintegral_smul_measure, smul_eq_mul]

theorem fiber_directional_subGaussian {t : ℕ} (T : Mat t) :
    SubGaussianQuadratic.DirectionalSubGaussian
      (GaussianRestriction.restrictedGaussian (truncationBody T)) id :=
  GaussianRestriction.restricted_directional_subGaussian
    (truncationBody_closed T).measurableSet (truncationBody_convex T)
    (truncationBody_symmetric T) (ne_of_gt (truncationBody_mass_pos T))

theorem fiber_quadratic_tail {t b : ℕ} (T : Mat t) (M : Matrix (Fin t) (Fin b) ℝ)
    (x : ℝ) (hx : 0 ≤ x) :
    GaussianRestriction.restrictedGaussian (truncationBody T)
      {z | (2+4*x) * SubGaussianQuadratic.frobeniusSq M <
        SubGaussianQuadratic.quadratic M z} ≤ ENNReal.ofReal (Real.exp (-x)) :=
  GaussianRestriction.restricted_quadratic_tail
    (truncationBody_closed T).measurableSet (truncationBody_convex T)
    (truncationBody_symmetric T) (ne_of_gt (truncationBody_mass_pos T)) M x hx

/-- Active coordinates of a selected row follow the literal no-pivot trajectory,
even before any nonzero-pivot hypothesis is imposed. -/
theorem residualMap_row_eq_trajectory {t : ℕ} (T : Mat t) (s : ℕ) (i j : Fin t)
    (hi : s ≤ i.val) (hj : s ≤ j.val) :
    residualMap T s (T i) j = trajectory T id s i j := by
  induction s generalizing i j with
  | zero => rfl
  | succ s ih =>
      have hs : s < t := lt_of_lt_of_le (by omega : s < i.val+1) (Nat.succ_le_of_lt i.isLt)
      have his : s ≤ i.val := by omega
      have hjs : s ≤ j.val := by omega
      have hss : s ≤ (⟨s,hs⟩ : Fin t).val := le_rfl
      have hrec := congrArg (fun y : Fin t → ℝ => y j)
        (residualMap_succ T (⟨s,hs⟩ : Fin t) (T i))
      rw [hrec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, multiplier,
        _root_.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
      rw [ih i j his hjs, ih i ⟨s,hs⟩ his hss]
      rw [trajectory, dif_pos hs]
      simp only [id_eq, schurStep, rowSwap, Equiv.swap_self, Equiv.refl_apply]
      rw [if_pos (by constructor <;> change s < _ <;> omega)]
      dsimp [pivotValue, upperRow]
      ring


theorem measurable_truncationBody_mass (t : ℕ) :
    Measurable (fun T : Mat t => GaussianQuadratic.gaussianVector t (truncationBody T)) :=
  measurable_measure_prodMk_left (measurableSet_truncationBody_joint t)

/-- The literal fixed path and the selected-row residual recursion coincide on
all active coordinates when the original pivot labels are prescribed. -/
theorem trajectory_prefix_residual {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (A : Mat n) (p : PivotPath n) (hp : ∀ k, k ≤ p k)
    (s : ℕ) (hs : s ≤ t)
    (horder : ∀ k : Fin t, k.val < s → rowLabels p k.val (p (Fin.castLE ht k)) = π k)
    (i : Fin n) (j : Fin t)
    (hi : s ≤ i.val) (hj : s ≤ j.val) :
    trajectory A p s i (Fin.castLE ht j) =
      residualMap (selectedBlock ht π A) s (prefixRows ht A (rowLabels p s i)) j := by
  induction s generalizing i j with
  | zero => rfl
  | succ s ih =>
      have hst : s < t := by omega
      let k : Fin t := ⟨s,hst⟩
      let kn : Fin n := Fin.castLE ht k
      have hsn : s < n := kn.isLt
      have hactive : s ≤ (p kn).val := hp kn
      have hs' : s ≤ t := by omega
      have hir : s ≤ (Equiv.swap kn (p kn) i).val := by
        by_cases hi1 : i = kn
        · simpa only [hi1, Equiv.swap_apply_left] using hactive
        by_cases hi2 : i = p kn
        · simp only [hi2, Equiv.swap_apply_right]; exact le_rfl
        · simpa only [Equiv.swap_apply_of_ne_of_ne hi1 hi2] using (by omega : s ≤ i.val)
      have hpiv (c : Fin t) (hc : s ≤ c.val) :
          trajectory A p s (p kn) (Fin.castLE ht c) = upperRow (selectedBlock ht π A) k c := by
        rw [ih hs' (fun k hk => horder k (by omega)) (p kn) c hactive hc]
        have ho := horder k (by change s < s+1; omega)
        change rowLabels p s (p kn) = π k at ho
        rw [ho]
        exact residualMap_row_eq_trajectory (selectedBlock ht π A) s k c le_rfl hc
      have hrow (c : Fin t) (hc : s ≤ c.val) :=
        ih hs' (fun k hk => horder k (by omega)) (Equiv.swap kn (p kn) i) c hir hc
      have hlab : rowLabels p (s+1) i = rowLabels p s (Equiv.swap kn (p kn) i) :=
        rowLabels_succ p kn i
      rw [hlab]
      have hrec := congrArg (fun y : Fin t → ℝ => y j)
        (residualMap_succ (selectedBlock ht π A) k
          (prefixRows ht A (rowLabels p s (Equiv.swap kn (p kn) i))))
      rw [hrec]
      rw [trajectory, dif_pos hsn]
      change schurStep (trajectory A p s) kn (p kn) i (Fin.castLE ht j) = _
      simp only [schurStep, rowSwap, Equiv.swap_apply_left]
      rw [if_pos (by
        constructor
        · change s < i.val; omega
        · change s < j.val; omega)]
      rw [hrow j (by omega), hpiv j (by omega)]
      have hrowk := hrow k le_rfl
      have hpivk := hpiv k le_rfl
      change trajectory A p s (Equiv.swap kn (p kn) i) kn = _ at hrowk
      change trajectory A p s (p kn) kn = _ at hpivk
      rw [hrowk, hpivk]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, multiplier,
        _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
        pivotValue, div_eq_mul_inv]
      ring

/-- Applying the preceding identity to the actual canonical order adds no
success-event or nonsingularity conditioning. -/
theorem firstTrajectory_prefix_residual {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (s : ℕ) (hs : s ≤ t) (i : Fin n) (j : Fin t) (hi : s ≤ i.val) (hj : s ≤ j.val) :
    firstTrajectory A s i (Fin.castLE ht j) =
      residualMap (selectedBlock ht (pivotOrder ht A) A) s
        (prefixRows ht A (rowLabels (firstPath A) s i)) j := by
  rw [← trajectory_firstPath_eq_proved]
  apply trajectory_prefix_residual ht (pivotOrder ht A) A (firstPath A)
    (fun k => (firstPivotIndex_spec_proved (firstTrajectory A k.val) k).1)
    s hs (fun k _ => (pivotOrder_stage ht A k).symm) i j hi hj


theorem multiplier_apply {t : ℕ} (T : Mat t) (j : Fin t) (x : Fin t → ℝ) :
    multiplier T j x = residualMap T j.val x j / pivotValue T j := by
  simp [multiplier, div_eq_mul_inv, mul_comm]

/-- An original row not previously selected remains at an active position. -/
theorem unselected_position_active {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (p : PivotPath n) (hp : ∀ k, k ≤ p k) (s : ℕ) (hs : s ≤ t)
    (horder : ∀ k : Fin t, k.val < s → rowLabels p k.val (p (Fin.castLE ht k)) = π k)
    (r : Fin n) (hr : ∀ k : Fin t, k.val < s → π k ≠ r) :
    s ≤ ((rowLabels p s).symm r).val := by
  by_contra! hq
  let q := (rowLabels p s).symm r
  have hqt : q.val < t := by dsimp [q]; omega
  let k : Fin t := ⟨q.val,hqt⟩
  have hk : k.val < s := hq
  have he : rowLabels p s q = π k := by
    rw [rowLabels_earlier p hp (q.val+1) s (by dsimp [q]; omega) q (by omega),
      rowLabels_succ p q, Equiv.swap_apply_left]
    exact horder k hk
  have heq : π k = r := he.symm.trans ((rowLabels p s).apply_symm_apply r)
  exact hr k hk heq

theorem firstTrajectory_pivot_entry {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (j c : Fin t) (hc : j.val ≤ c.val) :
    firstTrajectory A j.val (firstPath A (Fin.castLE ht j)) (Fin.castLE ht c) =
      upperRow (selectedBlock ht (pivotOrder ht A) A) j c := by
  have hp : j.val ≤ (firstPath A (Fin.castLE ht j)).val :=
    (firstPivotIndex_spec_proved (firstTrajectory A j.val) (Fin.castLE ht j)).1
  rw [firstTrajectory_prefix_residual ht A j.val j.isLt.le _ c hp hc]
  rw [← pivotOrder_stage ht A j]
  exact residualMap_row_eq_trajectory (selectedBlock ht (pivotOrder ht A) A)
    j.val j c le_rfl hc

/-- The actual unselected rows always lie in the closed multiplier body.
This uses maximum-magnitude pivoting but requires no nonsingularity assumption. -/
theorem actual_remaining_mem_truncationBody {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (r : RemainingRows (pivotOrder ht A)) :
    remainingBlock ht (pivotOrder ht A) A r ∈
      truncationBody (selectedBlock ht (pivotOrder ht A) A) := by
  intro j
  let p := firstPath A
  let q := (rowLabels p j.val).symm r.val
  have hp : ∀ k : Fin n, k ≤ p k := fun k =>
    (firstPivotIndex_spec_proved (firstTrajectory A k.val) k).1
  have hq : j.val ≤ q.val := unselected_position_active ht (pivotOrder ht A) p hp
    j.val j.isLt.le (fun k _ => (pivotOrder_stage ht A k).symm) r.val
    (fun k _ h => r.property ⟨k,h⟩)
  have hrow := firstTrajectory_prefix_residual ht A j.val j.isLt.le q j hq le_rfl
  have hl : rowLabels (firstPath A) j.val q = r.val := (rowLabels p j.val).apply_symm_apply r.val
  rw [hl] at hrow
  have hmax := (firstPivotIndex_spec_proved (firstTrajectory A j.val) (Fin.castLE ht j)).2.1 q hq
  have hpiv := firstTrajectory_pivot_entry ht A j j le_rfl
  change |firstTrajectory A j.val q (Fin.castLE ht j)| ≤
    |firstTrajectory A j.val (firstPath A (Fin.castLE ht j)) (Fin.castLE ht j)| at hmax
  rw [hrow, hpiv] at hmax
  rw [multiplier_apply, abs_div]
  by_cases hz : pivotValue (selectedBlock ht (pivotOrder ht A) A) j = 0
  · simp [hz]
  · exact (div_le_one (abs_pos.mpr hz)).mpr hmax


/-- Internal consistency of the proposed selected-row block. -/
def Good {t : ℕ} (T : Mat t) : Prop :=
  (∀ j : Fin t, pivotValue T j ≠ 0) ∧
    ∀ j k : Fin t, j < k → |multiplier T j (T k)| < 1

theorem measurableSet_good (t : ℕ) : MeasurableSet {T : Mat t | Good T} := by
  have h1 : MeasurableSet {T : Mat t | ∀ j : Fin t, pivotValue T j ≠ 0} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_eq_fun (measurable_pivotValue j) measurable_const).compl
  have h2 : MeasurableSet {T : Mat t | ∀ j k : Fin t, j < k → |multiplier T j (T k)| < 1} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro _hjk
    have hm := (measurable_multiplier j).comp (measurable_id.prodMk (measurable_pi_apply k))
    exact measurableSet_lt hm.abs measurable_const
  exact h1.inter h2

theorem selected_label_position {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (p : PivotPath n) (hp : ∀ k, k ≤ p k) (s : ℕ)
    (horder : ∀ k : Fin t, k.val < s → rowLabels p k.val (p (Fin.castLE ht k)) = π k)
    (k : Fin t) (hk : k.val < s) : rowLabels p s (Fin.castLE ht k) = π k := by
  rw [rowLabels_earlier p hp (k.val+1) s (by omega) (Fin.castLE ht k) (by change k.val < k.val+1; omega)]
  have hh := rowLabels_succ p (Fin.castLE ht k) (Fin.castLE ht k)
  rw [Equiv.swap_apply_left] at hh
  exact hh.trans (horder k hk)

/-- The strict fiber constraints force the actual canonical pivot prefix, with
no appeal to any tie convention on a boundary. -/
theorem strict_fiber_implies_order {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (A : Mat n) (hgood : Good (selectedBlock ht π A))
    (hrows : ∀ r : RemainingRows π, remainingBlock ht π A r ∈
      strictTruncationBody (selectedBlock ht π A)) : pivotOrder ht A = π := by
  let T := selectedBlock ht π A
  let p := firstPath A
  have hp : ∀ k : Fin n, k ≤ p k := fun k =>
    (firstPivotIndex_spec_proved (firstTrajectory A k.val) k).1
  have hprefix : ∀ s : ℕ, s ≤ t → ∀ k : Fin t, k.val < s →
      rowLabels p k.val (p (Fin.castLE ht k)) = π k := by
    intro s
    induction s with
    | zero => intro _ k hk; omega
    | succ s ih =>
        intro hs
        have hs' : s ≤ t := by omega
        have hst : s < t := by omega
        have hprev := ih hs'
        let k : Fin t := ⟨s,hst⟩
        let kn := Fin.castLE ht k
        let q := (rowLabels p s).symm (π k)
        have hq : s ≤ q.val := unselected_position_active ht π p hp s hs' hprev (π k)
          (fun l hl h => by have := π.injective h; have := congrArg Fin.val this; change l.val = s at this; omega)
        have hstate (i : Fin n) (hi : s ≤ i.val) :
            firstTrajectory A s i kn = residualMap T s
              (prefixRows ht A (rowLabels p s i)) k := by
          rw [← trajectory_firstPath_eq_proved]
          exact trajectory_prefix_residual ht π A p hp s hs' hprev i k hi le_rfl
        have hqstate : firstTrajectory A s q kn = pivotValue T k := by
          rw [hstate q hq, show rowLabels p s q = π k from (rowLabels p s).apply_symm_apply _]
          exact residualMap_row_eq_trajectory T s k k le_rfl le_rfl
        have hstrict (i : Fin n) (hi : s ≤ i.val) (hiq : i ≠ q) :
            |firstTrajectory A s i kn| < |pivotValue T k| := by
          have hmult : |multiplier T k (prefixRows ht A (rowLabels p s i))| < 1 := by
            by_cases hr : rowLabels p s i ∈ Set.range π
            · obtain ⟨l,hl⟩ := hr
              have hls : s < l.val := by
                by_contra! hh
                rcases lt_or_eq_of_le hh with hlt | heq
                · have hselected := selected_label_position ht π p hp s hprev l hlt
                  have hieq := (rowLabels p s).injective (hl.symm.trans hselected.symm)
                  have hval := congrArg Fin.val hieq
                  change i.val = l.val at hval
                  omega
                · have hlk : l = k := Fin.ext heq
                  have he : rowLabels p s i = π k := by simpa only [hlk] using hl.symm
                  have hiq' : i = q := (rowLabels p s).injective
                    (he.trans ((rowLabels p s).apply_symm_apply (π k)).symm)
                  exact hiq hiq'
              rw [← hl]
              exact hgood.2 k l hls
            · exact hrows ⟨rowLabels p s i,hr⟩ k
          rw [multiplier_apply, abs_div] at hmult
          have hu : 0 < |pivotValue T k| := abs_pos.mpr (hgood.1 k)
          rw [hstate i hi]
          exact (div_lt_one hu).mp hmult
        have hpchoice : p kn = q := by
          by_contra hne
          have hh := (firstPivotIndex_spec_proved (firstTrajectory A s) kn).2.1 q hq
          change |firstTrajectory A s q kn| ≤ |firstTrajectory A s (p kn) kn| at hh
          rw [hqstate] at hh
          exact (not_lt_of_ge hh) (hstrict (p kn) (hp kn) hne)
        have hkorder : rowLabels p s (p kn) = π k := by
          rw [hpchoice]
          exact (rowLabels p s).apply_symm_apply _
        intro l hl
        by_cases hls : l.val < s
        · exact hprev l hls
        · have hls : l = k := Fin.ext (by dsimp [k]; omega)
          subst l
          exact hkorder
  apply DFunLike.ext
  intro k
  exact (pivotOrder_stage ht A k).trans (hprefix t le_rfl k k.isLt)


theorem actual_good_of_nonsingular_separated {n t : ℕ} (ht : t ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) (hsep : GaussianTies.ColumnsSeparated A) :
    Good (selectedBlock ht (pivotOrder ht A) A) := by
  let T := selectedBlock ht (pivotOrder ht A) A
  let p := firstPath A
  have hpath : AdmissiblePath A p := firstPath_admissible_proved A hA
  have hnonzero (j : Fin t) : pivotValue T j ≠ 0 := by
    have hv := firstTrajectory_pivot_entry ht A j j le_rfl
    rw [← trajectory_firstPath_eq_proved] at hv
    intro hz
    apply (hpath (Fin.castLE ht j)).2.1
    exact hv.trans hz
  refine ⟨hnonzero, ?_⟩
  intro j l hjl
  let kn := Fin.castLE ht j
  let q := (rowLabels p j.val).symm (pivotOrder ht A l)
  have hq : j.val ≤ q.val := unselected_position_active ht (pivotOrder ht A) p
    (fun k => (hpath k).1) j.val j.isLt.le (fun k _ => (pivotOrder_stage ht A k).symm)
    (pivotOrder ht A l) (fun k hk h => by
      have he := congrArg Fin.val ((pivotOrder ht A).injective h)
      have hjl' : j.val < l.val := hjl
      omega)
  have hrow := firstTrajectory_prefix_residual ht A j.val j.isLt.le q j hq le_rfl
  have hl : rowLabels (firstPath A) j.val q = pivotOrder ht A l :=
    (rowLabels p j.val).apply_symm_apply _
  rw [hl] at hrow
  have hqne : q ≠ p kn := by
    intro he
    have hh := congrArg (rowLabels p j.val) he
    rw [hl, ← pivotOrder_stage ht A j] at hh
    exact (ne_of_lt hjl) ((pivotOrder ht A).injective hh).symm
  have hknval : kn.val = j.val := rfl
  have hsneq : |firstTrajectory A j.val q kn| ≠ |firstTrajectory A j.val (p kn) kn| := by
    simpa only [p, trajectory_firstPath_eq_proved, hknval] using
      hsep p hpath kn q (p kn) hq (hpath kn).1 hqne
  have hmax := (firstPivotIndex_spec_proved (firstTrajectory A j.val) kn).2.1 q hq
  have hlt : |firstTrajectory A j.val q kn| < |firstTrajectory A j.val (p kn) kn| :=
    lt_of_le_of_ne hmax hsneq
  rw [hrow, firstTrajectory_pivot_entry ht A j j le_rfl] at hlt
  rw [multiplier_apply, abs_div]
  exact (div_lt_one (abs_pos.mpr (hnonzero j))).mpr hlt

/-- Goodness is asserted for the actual selected block, not for every fixed
Gaussian t by t block. This is the null-exception input to fiber Fubini. -/
theorem actual_good_ae {n t : ℕ} (ht : t ≤ n) :
    ∀ᵐ A ∂gaussianMatrix n, Good (selectedBlock ht (pivotOrder ht A) A) := by
  have hnonzero : ∀ᵐ A ∂gaussianMatrix n, A.det ≠ 0 := by
    simpa only [ae_iff, not_not] using gaussianMatrix_singular_null_proved n
  filter_upwards [hnonzero, GaussianTies.columnsSeparated_ae n] with A hA hsep
  exact actual_good_of_nonsingular_separated ht A hA hsep


theorem measurableSet_strictTruncationBody_joint (t : ℕ) :
    MeasurableSet {z : Mat t × (Fin t → ℝ) | z.2 ∈ strictTruncationBody z.1} := by
  have he : {z : Mat t × (Fin t → ℝ) | z.2 ∈ strictTruncationBody z.1} =
      ⋂ j : Fin t, {z | |multiplier z.1 j z.2| < 1} := by
    ext z; simp [strictTruncationBody]
  rw [he]
  exact MeasurableSet.iInter fun j => measurableSet_lt (measurable_multiplier j).abs measurable_const

theorem measurableSet_product_body {t : ℕ} {ι : Type*} [Fintype ι] :
    MeasurableSet {z : Mat t × (ι → Fin t → ℝ) | ∀ i, z.2 i ∈ truncationBody z.1} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_truncationBody_joint t).preimage
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

theorem measurableSet_product_strict_body {t : ℕ} {ι : Type*} [Fintype ι] :
    MeasurableSet {z : Mat t × (ι → Fin t → ℝ) | ∀ i, z.2 i ∈ strictTruncationBody z.1} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_strictTruncationBody_joint t).preimage
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- All strict/closed fiber differences are null under the exact unconditioned
product law, before selecting any pivot order. -/
theorem product_body_strict_ae {t : ℕ} {ι : Type*} [Fintype ι] :
    ∀ᵐ z ∂(gaussianMatrix t).prod
      (Measure.pi (fun _ : ι => GaussianQuadratic.gaussianVector t)),
      (∀ i, z.2 i ∈ truncationBody z.1) ↔ ∀ i, z.2 i ∈ strictTruncationBody z.1 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_product_body.iff measurableSet_product_strict_body)).2
  apply ae_of_all
  intro T
  have hn : ∀ᵐ x ∂GaussianQuadratic.gaussianVector t,
      x ∉ truncationBody T \ strictTruncationBody T := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using truncationBody_boundary_null T
  have he : truncationBody T =ᵐ[GaussianQuadratic.gaussianVector t] strictTruncationBody T := by
    filter_upwards [hn] with x hx
    apply propext
    exact ⟨fun h => by by_contra hs; exact hx ⟨h,hs⟩, fun h => strictTruncationBody_subset T h⟩
  have hprod := Measure.ae_eq_set_pi (μ := fun _ : ι => GaussianQuadratic.gaussianVector t)
    (I := Set.univ) (fun _ _ => he)
  filter_upwards [hprod] with Z hZ
  exact Set.mem_univ_pi.symm.trans ((Iff.of_eq hZ).trans Set.mem_univ_pi)

/-- A measurable region of fixed selected-row and remaining-row coordinates. -/
def fiberRegion {t : ℕ} (ι : Type*) : Set (Mat t × (ι → Fin t → ℝ)) :=
  {z | Good z.1 ∧ ∀ i, z.2 i ∈ truncationBody z.1}

theorem measurableSet_fiberRegion (t : ℕ) (ι : Type*) [Fintype ι] :
    MeasurableSet (@fiberRegion t ι) :=
  ((measurableSet_good t).preimage measurable_fst).inter measurableSet_product_body

theorem measurable_fixed_blocks {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    Measurable (fun A : Mat n => (selectedBlock ht π A, remainingBlock ht π A)) := by
  unfold selectedBlock remainingBlock
  fun_prop

/-- Exact adaptive pivot-order membership is equal almost everywhere to its
fixed-coordinate Gaussian truncation fiber. -/
theorem orderEvent_ae_eq_fiber {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    orderEvent ht π =ᵐ[gaussianMatrix n]
      (fun A => (selectedBlock ht π A, remainingBlock ht π A)) ⁻¹'
        fiberRegion (RemainingRows π) := by
  have hb := product_body_strict_ae (t := t) (ι := RemainingRows π)
  rw [← fixed_blocks_joint_law ht π] at hb
  have hpull := ae_of_ae_map (measurable_fixed_blocks ht π).aemeasurable hb
  filter_upwards [hpull, actual_good_ae ht] with A hbody hgood
  apply propext
  constructor
  · intro hA
    have horder : pivotOrder ht A = π := hA
    have hg : Good (selectedBlock ht π A) := by simpa only [horder] using hgood
    refine ⟨hg, ?_⟩
    intro r
    subst π
    exact actual_remaining_mem_truncationBody ht A r
  · intro hA
    exact strict_fiber_implies_order ht π A hA.1 (hbody.mp hA.2)

/-- Fixed-order disintegration as an exact equality of finite measures. The
weight of the order is retained; the order is not assigned probability one. -/
theorem fixed_order_restricted_law {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    ((gaussianMatrix n).restrict (orderEvent ht π)).map
      (fun A => (selectedBlock ht π A, remainingBlock ht π A)) =
    ((gaussianMatrix t).prod
      (Measure.pi (fun _ : RemainingRows π => GaussianQuadratic.gaussianVector t))).restrict
        (fiberRegion (RemainingRows π)) := by
  rw [Measure.restrict_congr_set (orderEvent_ae_eq_fiber ht π),
    ← Measure.restrict_map (measurable_fixed_blocks ht π)
      (measurableSet_fiberRegion t (RemainingRows π)), fixed_blocks_joint_law ht π]


/-- Tested form of the fixed-order factorization, retaining the literal mass
q(T)^(n-t) of the remaining-row truncation. -/
theorem fixed_order_lintegral {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (F : Mat t × (RemainingRows π → Fin t → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ A in orderEvent ht π, F (selectedBlock ht π A, remainingBlock ht π A) ∂gaussianMatrix n) =
    ∫⁻ T in {T : Mat t | Good T},
      (GaussianQuadratic.gaussianVector t (truncationBody T))^(n-t) *
        (∫⁻ Z, F (T,Z) ∂Measure.pi
          (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T)))
      ∂gaussianMatrix t := by
  have hR := measurableSet_fiberRegion t (RemainingRows π)
  calc
    _ = ∫⁻ z, F z ∂((gaussianMatrix n).restrict (orderEvent ht π)).map
        (fun A => (selectedBlock ht π A, remainingBlock ht π A)) :=
      (lintegral_map hF (measurable_fixed_blocks ht π)).symm
    _ = ∫⁻ z in fiberRegion (RemainingRows π), F z
        ∂(gaussianMatrix t).prod
          (Measure.pi (fun _ : RemainingRows π => GaussianQuadratic.gaussianVector t)) := by
      rw [fixed_order_restricted_law ht π]
    _ = ∫⁻ T in {T : Mat t | Good T},
        (∫⁻ Z in Set.univ.pi (fun _ : RemainingRows π => truncationBody T), F (T,Z)
          ∂Measure.pi (fun _ : RemainingRows π => GaussianQuadratic.gaussianVector t))
          ∂gaussianMatrix t := by
      rw [← lintegral_indicator hR, lintegral_prod _ (hF.indicator hR).aemeasurable,
        ← lintegral_indicator (measurableSet_good t)]
      apply lintegral_congr
      intro T
      by_cases hg : Good T
      · have hmem : T ∈ {T : Mat t | Good T} := hg
        rw [Set.indicator_of_mem hmem]
        rw [← lintegral_indicator (MeasurableSet.univ_pi (fun _ => (truncationBody_closed T).measurableSet))]
        apply lintegral_congr
        intro Z
        by_cases hz : Z ∈ Set.univ.pi (fun _ : RemainingRows π => truncationBody T)
        · have hr : (T,Z) ∈ fiberRegion (RemainingRows π) := ⟨hg, Set.mem_univ_pi.mp hz⟩
          rw [Set.indicator_of_mem hr, Set.indicator_of_mem hz]
        · have hr : (T,Z) ∉ fiberRegion (RemainingRows π) :=
            fun h => hz (Set.mem_univ_pi.mpr h.2)
          rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hz]
      · simp only [fiberRegion, Set.indicator, Set.mem_ofPred_eq, hg, false_and,
          ↓reduceIte, lintegral_zero]
    _ = _ := by
      apply lintegral_congr
      intro T
      rw [product_restriction_lintegral, remainingRows_card]

/-- The exact weight assigned to a prescribed original pivot order. -/
def orderWeight {n t : ℕ} (_π : Fin t ↪ Fin n) : ℝ≥0∞ :=
  ∫⁻ T in {T : Mat t | Good T},
    (GaussianQuadratic.gaussianVector t (truncationBody T))^(n-t)
    ∂gaussianMatrix t

theorem orderEvent_measure {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    gaussianMatrix n (orderEvent ht π) = orderWeight π := by
  have h := fixed_order_lintegral ht π (fun _ => 1) measurable_const
  have hprob (T : Mat t) : IsProbabilityMeasure
      (Measure.pi (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T))) := by
    let _ := GaussianRestriction.restrictedGaussian_probability (ne_of_gt (truncationBody_mass_pos T))
    infer_instance
  have hu (T : Mat t) : (Measure.pi (fun _ : RemainingRows π =>
      GaussianRestriction.restrictedGaussian (truncationBody T))) Set.univ = 1 := by
    let _ := hprob T
    exact measure_univ
  simpa only [lintegral_one, Measure.restrict_apply_univ, hu, mul_one, orderWeight] using h

/-- Partition weights sum to one, eliminating a possible factorial loss. -/
theorem orderWeights_sum_one {n t : ℕ} (ht : t ≤ n) :
    ∑ π : Fin t ↪ Fin n, orderWeight π = 1 := by
  let _ := gaussianMatrix_probability_proved n
  have hp : Pairwise (fun π σ => Disjoint (orderEvent ht π) (orderEvent ht σ)) := fun _ _ h => orderEvent_disjoint ht h
  have hm := measure_iUnion (μ := gaussianMatrix n) hp (measurableSet_orderEvent ht)
  rw [orderEvent_partition ht, measure_univ] at hm
  rw [tsum_fintype] at hm
  simpa only [orderEvent_measure ht] using hm.symm


/-- Uniform normalized fiber bounds transfer to the actual adaptive selection
with no factor for the number of possible pivot orders. -/
theorem adaptive_lintegral_le {n t : ℕ} (ht : t ≤ n) (ε : ℝ≥0∞)
    (F : (π : Fin t ↪ Fin n) → Mat t × (RemainingRows π → Fin t → ℝ) → ℝ≥0∞)
    (hF : ∀ π, Measurable (F π))
    (hbound : ∀ (π : Fin t ↪ Fin n) (T : Mat t), Good T →
      (∫⁻ Z, F π (T,Z) ∂Measure.pi
        (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T))) ≤ ε) :
    (∑ π : Fin t ↪ Fin n, ∫⁻ A in orderEvent ht π,
      F π (selectedBlock ht π A, remainingBlock ht π A) ∂gaussianMatrix n) ≤ ε := by
  by_cases hε : ε = ⊤
  · simp only [hε, le_top]
  have hsingle (π : Fin t ↪ Fin n) :
      (∫⁻ A in orderEvent ht π, F π (selectedBlock ht π A, remainingBlock ht π A)
        ∂gaussianMatrix n) ≤ orderWeight π * ε := by
    rw [fixed_order_lintegral ht π (F π) (hF π)]
    calc
      _ ≤ ∫⁻ T in {T : Mat t | Good T},
          (GaussianQuadratic.gaussianVector t (truncationBody T))^(n-t) * ε ∂gaussianMatrix t :=
        setLIntegral_mono' (measurableSet_good t) (fun T hT =>
          mul_le_mul_of_nonneg_left (hbound π T hT) zero_le)
      _ = _ := lintegral_mul_const' ε _ hε
  calc
    _ ≤ ∑ π : Fin t ↪ Fin n, orderWeight π * ε := Finset.sum_le_sum (fun π _ => hsingle π)
    _ = (∑ π : Fin t ↪ Fin n, orderWeight π) * ε := (Finset.sum_mul _ _ _).symm
    _ = ε := by rw [orderWeights_sum_one ht, one_mul]

/-- Event form of the adaptive transfer. Every Bπ is a jointly measurable set
of the actual selected-row values and all remaining original-row values. -/
theorem adaptive_event_le {n t : ℕ} (ht : t ≤ n) (ε : ℝ≥0∞)
    (B : (π : Fin t ↪ Fin n) → Set (Mat t × (RemainingRows π → Fin t → ℝ)))
    (hB : ∀ π, MeasurableSet (B π))
    (hbound : ∀ (π : Fin t ↪ Fin n) (T : Mat t), Good T →
      (Measure.pi (fun _ : RemainingRows π =>
        GaussianRestriction.restrictedGaussian (truncationBody T))) {Z | (T,Z) ∈ B π} ≤ ε) :
    gaussianMatrix n {A | ∃ π : Fin t ↪ Fin n, A ∈ orderEvent ht π ∧
      (selectedBlock ht π A, remainingBlock ht π A) ∈ B π} ≤ ε := by
  classical
  let F (π : Fin t ↪ Fin n) := (B π).indicator (fun _ => (1 : ℝ≥0∞))
  have hF (π : Fin t ↪ Fin n) : Measurable (F π) := measurable_const.indicator (hB π)
  have hfiber (π : Fin t ↪ Fin n) (T : Mat t) :
      (∫⁻ Z, F π (T,Z) ∂Measure.pi
        (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T))) =
      (Measure.pi (fun _ : RemainingRows π =>
        GaussianRestriction.restrictedGaussian (truncationBody T))) {Z | (T,Z) ∈ B π} := by
    have hm : MeasurableSet {Z | (T,Z) ∈ B π} := (hB π).preimage (by fun_prop)
    change (∫⁻ Z, {Z | (T,Z) ∈ B π}.indicator 1 Z ∂_) = _
    exact lintegral_indicator_one hm
  have ha := adaptive_lintegral_le ht ε F hF (fun π T hT => by
    rw [hfiber]
    exact hbound π T hT)
  have hone (π : Fin t ↪ Fin n) :
      (∫⁻ A in orderEvent ht π, F π (selectedBlock ht π A, remainingBlock ht π A) ∂gaussianMatrix n) =
      gaussianMatrix n (orderEvent ht π ∩
        (fun A => (selectedBlock ht π A, remainingBlock ht π A)) ⁻¹' B π) := by
    have hm := (hB π).preimage (measurable_fixed_blocks ht π)
    change (∫⁻ A, ((fun A => (selectedBlock ht π A, remainingBlock ht π A)) ⁻¹' B π).indicator 1 A
      ∂(gaussianMatrix n).restrict (orderEvent ht π)) = _
    rw [lintegral_indicator_one hm, Measure.restrict_apply hm, Set.inter_comm]
  simp_rw [hone] at ha
  have he : {A | ∃ π : Fin t ↪ Fin n, A ∈ orderEvent ht π ∧
      (selectedBlock ht π A, remainingBlock ht π A) ∈ B π} =
      ⋃ π : Fin t ↪ Fin n, orderEvent ht π ∩
        (fun A => (selectedBlock ht π A, remainingBlock ht π A)) ⁻¹' B π := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  rw [he]
  exact (measure_iUnion_le _).trans (by simpa only [tsum_fintype] using ha)


/-- The upper-triangular no-pivot factor of the selected block. -/
def upperMatrix {t : ℕ} (T : Mat t) : Mat t := fun i j => upperRow T i j

def multiplierVector {t : ℕ} (T : Mat t) (x : Fin t → ℝ) : Fin t → ℝ :=
  fun j => multiplier T j x

theorem trajectory_inactive_column {t : ℕ} (T : Mat t) (p : PivotPath t)
    (s : ℕ) (i j : Fin t) (hj : j.val < s) : trajectory T p s i j = 0 := by
  cases s with
  | zero => omega
  | succ s =>
      rw [trajectory]
      split_ifs with hs
      · simp only [schurStep]
        rw [if_neg (by intro h; have hh : s < j.val := h.2; omega)]
      · rfl

theorem upperMatrix_triangular {t : ℕ} (T : Mat t) : (upperMatrix T).IsUpperTriangular := by
  intro i j hij
  exact trajectory_inactive_column T id i.val i j hij

theorem upperMatrix_det_ne_zero {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) : (upperMatrix T).det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular (upperMatrix_triangular T)]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => hu j)

theorem residualMap_earlier_zero {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) (x : Fin t → ℝ)
    (s : ℕ) (hs : s ≤ t) (j : Fin t) (hj : j.val < s) : residualMap T s x j = 0 := by
  induction s with
  | zero => omega
  | succ s ih =>
      have hst : s < t := by omega
      let k : Fin t := ⟨s,hst⟩
      have hrec := congrArg (fun y : Fin t → ℝ => y j) (residualMap_succ T k x)
      rw [hrec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hjs : j.val < s
      · rw [ih (by omega) hjs, show upperRow T k j = 0 from
          trajectory_inactive_column T id s k j hjs, mul_zero, sub_zero]
      · have hjk : j = k := Fin.ext (by dsimp [k]; omega)
        subst j
        rw [multiplier_apply]
        change residualMap T s x k - (residualMap T s x k / pivotValue T k) * pivotValue T k = 0
        rw [div_mul_cancel₀ _ (hu k), sub_self]

theorem residualMap_terminal_zero {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) (x : Fin t → ℝ) : residualMap T t x = 0 := by
  funext j
  exact residualMap_earlier_zero T hu x t le_rfl j j.isLt

theorem residualMap_telescoping {t : ℕ} (T : Mat t) (x : Fin t → ℝ)
    (s : ℕ) (hs : s ≤ t) (c : Fin t) :
    residualMap T s x c = x c - ∑ j : Fin t,
      if j.val < s then multiplier T j x * upperRow T j c else 0 := by
  classical
  induction s with
  | zero => simp [residualMap]
  | succ s ih =>
      have hst : s < t := by omega
      let k : Fin t := ⟨s,hst⟩
      have hsum : (∑ j : Fin t, if j.val < s+1 then multiplier T j x * upperRow T j c else 0) =
          (∑ j : Fin t, if j.val < s then multiplier T j x * upperRow T j c else 0) +
            multiplier T k x * upperRow T k c := by
        have hpoint (j : Fin t) :
            (if j.val < s+1 then multiplier T j x * upperRow T j c else 0) =
            (if j.val < s then multiplier T j x * upperRow T j c else 0) +
            (if j = k then multiplier T j x * upperRow T j c else 0) := by
          by_cases hj : j.val < s
          · have hj' : j.val < s+1 := by omega
            have hjk : j ≠ k := by intro h; have he := congrArg Fin.val h; change j.val = s at he; omega
            simp only [hj, hj', hjk, if_true, if_false, add_zero]
          · by_cases hjk : j = k
            · subst j
              simp only [k, Nat.lt_succ_self, Nat.lt_irrefl, if_true, if_false, zero_add]
            · have hj' : ¬ j.val < s+1 := by
                intro h
                apply hjk
                apply Fin.ext
                dsimp [k]
                omega
              simp only [hj, hj', hjk, if_false, add_zero]
        simp_rw [hpoint]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hsum]
      have hrec := congrArg (fun y : Fin t → ℝ => y c) (residualMap_succ T k x)
      rw [hrec]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [ih (by omega)]
      ring

/-- The complete row of elimination multipliers is x times the inverse upper
factor whenever the selected pivots are nonzero. -/
theorem multiplierVector_vecMul_upper {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) (x : Fin t → ℝ) :
    (multiplierVector T x) ᵥ* (upperMatrix T) = x := by
  funext c
  have h := residualMap_telescoping T x t le_rfl c
  rw [residualMap_terminal_zero T hu x] at h
  simp only [Pi.zero_apply, Fin.is_lt, if_true] at h
  change (∑ j : Fin t, multiplier T j x * upperRow T j c) = x c
  exact (sub_eq_zero.mp h.symm).symm

theorem multiplierVector_eq_vecMul_inv {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) (x : Fin t → ℝ) :
    multiplierVector T x = x ᵥ* (upperMatrix T)⁻¹ := by
  have h := congrArg (fun y : Fin t → ℝ => y ᵥ* (upperMatrix T)⁻¹)
    (multiplierVector_vecMul_upper T hu x)
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (upperMatrix_det_ne_zero T hu)), Matrix.vecMul_one] at h
  exact h

theorem truncationBody_eq_inverse_upper {t : ℕ} (T : Mat t)
    (hu : ∀ j : Fin t, pivotValue T j ≠ 0) :
    truncationBody T = {x | ∀ j : Fin t, |(x ᵥ* (upperMatrix T)⁻¹) j| ≤ 1} := by
  ext x
  have h := multiplierVector_eq_vecMul_inv T hu x
  change (∀ j : Fin t, |multiplierVector T x j| ≤ 1) ↔ _
  rw [h]
  rfl


/-! Every owned declaration is audited transitively in LeanCert kernel mode. -/
#assert_trust kernel rowLabels
#assert_trust kernel rowLabels_succ
#assert_trust kernel rowLabels_prefix_congr
#assert_trust kernel rowLabels_earlier
#assert_trust kernel pivotOrder
#assert_trust kernel pivotOrder_stage
#assert_trust kernel pivotOrder_columns_congr
#assert_trust kernel measurable_pivotOrder_coordinate
#assert_trust kernel orderEvent
#assert_trust kernel measurableSet_orderEvent
#assert_trust kernel orderEvent_partition
#assert_trust kernel orderEvent_disjoint
#assert_trust kernel RemainingRows
#assert_trust kernel prefixRows
#assert_trust kernel selectedBlock
#assert_trust kernel remainingBlock
#assert_trust kernel gaussian_coordinates_map
#assert_trust kernel gaussian_prefixRows_map
#assert_trust kernel fixed_blocks_joint_law
#assert_trust kernel upperRow
#assert_trust kernel pivotValue
#assert_trust kernel residualMap
#assert_trust kernel multiplier
#assert_trust kernel residualMap_succ
#assert_trust kernel truncationBody
#assert_trust kernel strictTruncationBody
#assert_trust kernel truncationBody_closed
#assert_trust kernel truncationBody_convex
#assert_trust kernel truncationBody_symmetric
#assert_trust kernel strictTruncationBody_open
#assert_trust kernel zero_mem_strictTruncationBody
#assert_trust kernel strictTruncationBody_subset
#assert_trust kernel measurable_upperRow
#assert_trust kernel measurable_pivotValue
#assert_trust kernel measurable_residualMap_apply
#assert_trust kernel measurable_multiplier
#assert_trust kernel measurableSet_truncationBody_joint
#assert_trust kernel gaussianVector_open_positive
#assert_trust kernel truncationBody_mass_pos
#assert_trust kernel linear_nonzero_level_null
#assert_trust kernel truncationBody_boundary_null
#assert_trust kernel remainingRows_card
#assert_trust kernel product_restriction_normalized
#assert_trust kernel product_restriction_lintegral
#assert_trust kernel fiber_directional_subGaussian
#assert_trust kernel fiber_quadratic_tail
#assert_trust kernel residualMap_row_eq_trajectory
#assert_trust kernel measurable_truncationBody_mass
#assert_trust kernel trajectory_prefix_residual
#assert_trust kernel firstTrajectory_prefix_residual
#assert_trust kernel multiplier_apply
#assert_trust kernel unselected_position_active
#assert_trust kernel firstTrajectory_pivot_entry
#assert_trust kernel actual_remaining_mem_truncationBody
#assert_trust kernel Good
#assert_trust kernel measurableSet_good
#assert_trust kernel selected_label_position
#assert_trust kernel strict_fiber_implies_order
#assert_trust kernel actual_good_of_nonsingular_separated
#assert_trust kernel actual_good_ae
#assert_trust kernel measurableSet_strictTruncationBody_joint
#assert_trust kernel measurableSet_product_body
#assert_trust kernel measurableSet_product_strict_body
#assert_trust kernel product_body_strict_ae
#assert_trust kernel fiberRegion
#assert_trust kernel measurableSet_fiberRegion
#assert_trust kernel measurable_fixed_blocks
#assert_trust kernel orderEvent_ae_eq_fiber
#assert_trust kernel fixed_order_restricted_law
#assert_trust kernel fixed_order_lintegral
#assert_trust kernel orderWeight
#assert_trust kernel orderEvent_measure
#assert_trust kernel orderWeights_sum_one
#assert_trust kernel adaptive_lintegral_le
#assert_trust kernel adaptive_event_le
#assert_trust kernel upperMatrix
#assert_trust kernel multiplierVector
#assert_trust kernel trajectory_inactive_column
#assert_trust kernel upperMatrix_triangular
#assert_trust kernel upperMatrix_det_ne_zero
#assert_trust kernel residualMap_earlier_zero
#assert_trust kernel residualMap_terminal_zero
#assert_trust kernel residualMap_telescoping
#assert_trust kernel multiplierVector_vecMul_upper
#assert_trust kernel multiplierVector_eq_vecMul_inv
#assert_trust kernel truncationBody_eq_inverse_upper

#print axioms rowLabels
#print axioms rowLabels_succ
#print axioms rowLabels_prefix_congr
#print axioms rowLabels_earlier
#print axioms pivotOrder
#print axioms pivotOrder_stage
#print axioms pivotOrder_columns_congr
#print axioms measurable_pivotOrder_coordinate
#print axioms orderEvent
#print axioms measurableSet_orderEvent
#print axioms orderEvent_partition
#print axioms orderEvent_disjoint
#print axioms RemainingRows
#print axioms prefixRows
#print axioms selectedBlock
#print axioms remainingBlock
#print axioms gaussian_coordinates_map
#print axioms gaussian_prefixRows_map
#print axioms fixed_blocks_joint_law
#print axioms upperRow
#print axioms pivotValue
#print axioms residualMap
#print axioms multiplier
#print axioms residualMap_succ
#print axioms truncationBody
#print axioms strictTruncationBody
#print axioms truncationBody_closed
#print axioms truncationBody_convex
#print axioms truncationBody_symmetric
#print axioms strictTruncationBody_open
#print axioms zero_mem_strictTruncationBody
#print axioms strictTruncationBody_subset
#print axioms measurable_upperRow
#print axioms measurable_pivotValue
#print axioms measurable_residualMap_apply
#print axioms measurable_multiplier
#print axioms measurableSet_truncationBody_joint
#print axioms gaussianVector_open_positive
#print axioms truncationBody_mass_pos
#print axioms linear_nonzero_level_null
#print axioms truncationBody_boundary_null
#print axioms remainingRows_card
#print axioms product_restriction_normalized
#print axioms product_restriction_lintegral
#print axioms fiber_directional_subGaussian
#print axioms fiber_quadratic_tail
#print axioms residualMap_row_eq_trajectory
#print axioms measurable_truncationBody_mass
#print axioms trajectory_prefix_residual
#print axioms firstTrajectory_prefix_residual
#print axioms multiplier_apply
#print axioms unselected_position_active
#print axioms firstTrajectory_pivot_entry
#print axioms actual_remaining_mem_truncationBody
#print axioms Good
#print axioms measurableSet_good
#print axioms selected_label_position
#print axioms strict_fiber_implies_order
#print axioms actual_good_of_nonsingular_separated
#print axioms actual_good_ae
#print axioms measurableSet_strictTruncationBody_joint
#print axioms measurableSet_product_body
#print axioms measurableSet_product_strict_body
#print axioms product_body_strict_ae
#print axioms fiberRegion
#print axioms measurableSet_fiberRegion
#print axioms measurable_fixed_blocks
#print axioms orderEvent_ae_eq_fiber
#print axioms fixed_order_restricted_law
#print axioms fixed_order_lintegral
#print axioms orderWeight
#print axioms orderEvent_measure
#print axioms orderWeights_sum_one
#print axioms adaptive_lintegral_le
#print axioms adaptive_event_le
#print axioms upperMatrix
#print axioms multiplierVector
#print axioms trajectory_inactive_column
#print axioms upperMatrix_triangular
#print axioms upperMatrix_det_ne_zero
#print axioms residualMap_earlier_zero
#print axioms residualMap_terminal_zero
#print axioms residualMap_telescoping
#print axioms multiplierVector_vecMul_upper
#print axioms multiplierVector_eq_vecMul_inv
#print axioms truncationBody_eq_inverse_upper

end NLA.IE06.GaussianPivotConditioning
