import NLA.IE06.GaussianColumnSplit
import NLA.IE06.GaussianRegression

/-! Explicit inverses of the fixed selected/past/future Gaussian coordinates.
These coordinate identities are part of the independently reviewed column-split
contract; no adaptive distribution claim is inserted. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianCoordinates
open GaussianNull GaussianQuadratic GaussianPivotConditioning GaussianColumnSplit

/-- Restore every original matrix entry from its fixed selected prefix,
remaining prefix, and original-index fresh columns. -/
def restore {n t : ℕ} (_ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : (Mat t × (RemainingRows π → Fin t → ℝ)) × FutureBlock n t) : Mat n :=
  fun i j => if hc : j.val < t then
    if hr : i ∈ Set.range π then z.1.1 hr.choose ⟨j.val,hc⟩
    else z.1.2 ⟨i,hr⟩ ⟨j.val,hc⟩
    else z.2 ⟨j,by omega⟩ i

theorem restore_measurable {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    Measurable (restore ht π) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hc : j.val < t
  · by_cases hr : i ∈ Set.range π
    · simp only [restore,dif_pos hc,dif_pos hr]
      fun_prop
    · simp only [restore,dif_pos hc,dif_neg hr]
      fun_prop
  · simp only [restore,dif_neg hc]
    fun_prop

theorem selectedBlock_restore {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : (Mat t × (RemainingRows π → Fin t → ℝ)) × FutureBlock n t) :
    selectedBlock ht π (restore ht π z) = z.1.1 := by
  funext i j
  have hc : (Fin.castLE ht j).val < t := j.isLt
  have hr : π i ∈ Set.range π := ⟨i,rfl⟩
  have he : hr.choose = i := π.injective hr.choose_spec
  simp only [selectedBlock,restore,dif_pos hc,dif_pos hr,he]
  rfl

theorem remainingBlock_restore {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : (Mat t × (RemainingRows π → Fin t → ℝ)) × FutureBlock n t) :
    remainingBlock ht π (restore ht π z) = z.1.2 := by
  funext i j
  have hc : (Fin.castLE ht j).val < t := j.isLt
  simp only [remainingBlock,restore,dif_pos hc,dif_neg i.property]
  rfl

theorem futureColumns_restore {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : (Mat t × (RemainingRows π → Fin t → ℝ)) × FutureBlock n t) :
    PivotFiltration.futureColumns t (restore ht π z) = z.2 := by
  funext j i
  have hc : ¬j.val.val < t := not_lt.mpr j.property
  simp only [PivotFiltration.futureColumns,PivotFiltration.column,restore,dif_neg hc]

theorem restore_coordinates {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) (A : Mat n) :
    restore ht π ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A) = A := by
  funext i j
  by_cases hc : j.val < t
  · by_cases hr : i ∈ Set.range π
    · simp only [restore,dif_pos hc,dif_pos hr,selectedBlock,hr.choose_spec]
      rfl
    · simp only [restore,dif_pos hc,dif_neg hr,remainingBlock]
      rfl
  · simp only [restore,dif_neg hc,PivotFiltration.futureColumns,PivotFiltration.column]

theorem restore_prefix_congr {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : Mat t × (RemainingRows π → Fin t → ℝ)) (W V : FutureBlock n t) :
    ColumnsAgree (restore ht π (z,W)) (restore ht π (z,V)) t := by
  intro i j hj
  simp only [restore,dif_pos hj]

theorem selectedRows_restore_future {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (z : Mat t × (RemainingRows π → Fin t → ℝ)) (W V : FutureBlock n t) :
    PivotFiltration.selectedRows (restore ht π (z,W)) t =
      PivotFiltration.selectedRows (restore ht π (z,V)) t :=
  PivotFiltration.selectedRows_columns_congr _ _ t (restore_prefix_congr ht π z W V) t le_rfl

/-- Increasing bijection from the suffix offsets to original future labels. -/
def futureIndex {n t : ℕ} (ht : t ≤ n) : Fin (n-t) ≃ {j : Fin n // t ≤ j.val} where
  toFun i := ⟨⟨t+i.val,by omega⟩,by change t ≤ t+i.val; omega⟩
  invFun j := ⟨j.val.val-t,by have := j.val.isLt; have := j.property; omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv j := by apply Subtype.ext; apply Fin.ext; dsimp; have := j.property; omega

def denseFuture {n t : ℕ} (ht : t ≤ n) (W : FutureBlock n t) : RectMat n (n-t) :=
  fun i j => W (futureIndex ht j) i

def indexedFuture {n t : ℕ} (ht : t ≤ n) (G : RectMat n (n-t)) : FutureBlock n t :=
  fun j i => G i ((futureIndex ht).symm j)

theorem indexed_dense {n t : ℕ} (ht : t ≤ n) (W : FutureBlock n t) :
    indexedFuture ht (denseFuture ht W) = W := by
  funext j i
  simp [indexedFuture,denseFuture]

theorem dense_indexed {n t : ℕ} (ht : t ≤ n) (G : RectMat n (n-t)) :
    denseFuture ht (indexedFuture ht G) = G := by
  funext i j
  simp [indexedFuture,denseFuture]

theorem denseFuture_measurable {n t : ℕ} (ht : t ≤ n) : Measurable (denseFuture ht) := by
  unfold denseFuture
  fun_prop

theorem indexedFuture_measurable {n t : ℕ} (ht : t ≤ n) : Measurable (indexedFuture ht) := by
  unfold indexedFuture
  fun_prop

theorem denseFuture_measurePreserving {n t : ℕ} (ht : t ≤ n) :
    MeasurePreserving (denseFuture ht) (futureLaw n t) (gaussianRect n (n-t)) := by
  have hr := measurePreserving_piCongrLeft (fun _ : Fin (n-t) => gaussianVector n)
    (futureIndex ht).symm
  have htr : MeasurePreserving (@GaussianRegression.transpose (n-t) n)
      (gaussianRect (n-t) n) (gaussianRect n (n-t)) :=
    ⟨by unfold GaussianRegression.transpose; fun_prop,GaussianRegression.gaussian_transpose (n-t) n⟩
  convert htr.comp hr using 1 <;> try rfl
  funext W i j
  simp [denseFuture,GaussianRegression.transpose,MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_eq_cast]

theorem indexedFuture_measurePreserving {n t : ℕ} (ht : t ≤ n) :
    MeasurePreserving (indexedFuture ht) (gaussianRect n (n-t)) (futureLaw n t) := by
  refine ⟨indexedFuture_measurable ht,?_⟩
  rw [← (denseFuture_measurePreserving ht).map_eq,
    Measure.map_map (indexedFuture_measurable ht) (denseFuture_measurable ht)]
  have he : indexedFuture ht ∘ denseFuture ht = id := funext (indexed_dense ht)
  rw [he,Measure.map_id]

#assert_trust kernel futureIndex
#assert_trust kernel denseFuture
#assert_trust kernel indexedFuture
#assert_trust kernel indexed_dense
#assert_trust kernel dense_indexed
#assert_trust kernel denseFuture_measurable
#assert_trust kernel indexedFuture_measurable
#assert_trust kernel denseFuture_measurePreserving
#assert_trust kernel indexedFuture_measurePreserving
#print axioms denseFuture_measurePreserving
#print axioms indexedFuture_measurePreserving

#assert_trust kernel restore
#assert_trust kernel restore_measurable
#assert_trust kernel selectedBlock_restore
#assert_trust kernel remainingBlock_restore
#assert_trust kernel futureColumns_restore
#assert_trust kernel restore_coordinates
#assert_trust kernel restore_prefix_congr
#assert_trust kernel selectedRows_restore_future
#print axioms restore_coordinates
#print axioms selectedRows_restore_future
end NLA.IE06.GaussianCoordinates
