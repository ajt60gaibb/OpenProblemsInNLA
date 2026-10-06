import NLA.IE06.SelectedBlockCandidates
import NLA.IE06.GaussianFutureWindow
import NLA.IE06.GaussianAppend

/-! A fresh-column estimate is paid once for the actual selected row prefix.
Conditioning on all past columns fixes the original row labels; every fixed
injection selects an actual iid Gaussian submatrix of the fresh window. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal BigOperators
namespace NLA.IE06.GaussianAdaptiveAppend
open GaussianNull GaussianQuadratic GaussianPivotConditioning GaussianColumnSplit
open SelectedBlockCandidates PivotFiltration GaussianCandidateStacking
open Spectral SpectralMeasurability KyFan GaussianAppend

local instance gaussianMatrix_prob (n : ℕ) : IsProbabilityMeasure (gaussianMatrix n) :=
  gaussianMatrix_probability_proved n
local instance gaussianRect_prob (m n : ℕ) : IsProbabilityMeasure (gaussianRect m n) := by
  unfold gaussianRect
  infer_instance
local instance matrixMeasurable (r c : Type*) : MeasurableSpace (Matrix r c ℝ) :=
  inferInstanceAs (MeasurableSpace (r → c → ℝ))

def freshWindow {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) : RectMat n s :=
  (GaussianFutureWindow.split hp (futureColumns m A)).1

theorem freshWindow_measurable {n m s : ℕ} (hp : m+s ≤ n) : Measurable (freshWindow hp) :=
  ((GaussianFutureWindow.split_measurable hp).comp (measurable_futureColumns m)).fst

theorem freshWindow_measurePreserving {n m s : ℕ} (hp : m+s ≤ n) :
    MeasurePreserving (freshWindow hp) (gaussianMatrix n) (gaussianRect n s) :=
  measurePreserving_fst.comp ((GaussianFutureWindow.split_measurePreserving hp).comp
    ⟨measurable_futureColumns m,gaussian_futureColumns_map m⟩)

theorem past_fresh_joint_law {n m s : ℕ} (hp : m+s ≤ n) :
    (gaussianMatrix n).map (fun A => (pastMatrix m A,freshWindow hp A)) =
      ((gaussianMatrix n).map (pastMatrix m)).prod (gaussianRect n s) := by
  have hi := (pastMatrix_independent_futureColumns (n:=n) m).comp measurable_id
    (GaussianFutureWindow.split_measurable hp).fst
  have h := hi.map_prod_eq_prod_map_map (measurable_pastMatrix m).aemeasurable
    (freshWindow_measurable hp).aemeasurable
  rw [(freshWindow_measurePreserving hp).map_eq] at h
  exact h

theorem pivotOrder_pastMatrix {n m : ℕ} (hm : m ≤ n) (A : Mat n) :
    pivotOrder hm (pastMatrix m A) = pivotOrder hm A := by
  apply pivotOrder_columns_congr
  intro i j hj
  simp only [pastMatrix,hj,if_true]

theorem actualBlock_pastMatrix {n m : ℕ} (hm : m ≤ n) (A : Mat n) :
    actualBlock hm (pastMatrix m A) = actualBlock hm A := by
  unfold actualBlock
  rw [pivotOrder_pastMatrix]
  funext i j
  simp only [selectedBlock,pastMatrix,Fin.val_castLE,j.isLt,if_true]

theorem actualBlock_measurable {n m : ℕ} (hm : m ≤ n) : Measurable (actualBlock hm) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have he : Measurable (fun q : Mat n × Fin n => q.1 q.2 (Fin.castLE hm j)) :=
    measurable_from_prod_countable_left (fun _ => by fun_prop)
  exact he.comp (measurable_id.prodMk (measurable_pivotOrder_coordinate hm i))

def selectedFresh {n m s : ℕ} (hm : m ≤ n) (P : Mat n) (W : RectMat n s) : RectMat m s :=
  fun i j => W (pivotOrder hm P i) j

theorem selectedFresh_measurable {n m s : ℕ} (hm : m ≤ n) :
    Measurable (fun q : Mat n × RectMat n s => selectedFresh hm q.1 q.2) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have he : Measurable (fun q : RectMat n s × Fin n => q.1 q.2 j) :=
    measurable_from_prod_countable_left (fun _ => by fun_prop)
  exact he.comp (measurable_snd.prodMk
    ((measurable_pivotOrder_coordinate hm i).comp measurable_fst))

theorem selectedFresh_measurePreserving {n m s : ℕ} (hm : m ≤ n) (P : Mat n) :
    MeasurePreserving (selectedFresh (s:=s) hm P) (gaussianRect n s) (gaussianRect m s) :=
  GaussianOvercrowding.restrictRows_measurePreserving (pivotOrder hm P) (pivotOrder hm P).injective

theorem extendedBlock_eq_append {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) :
    Matrix.of (extendedBlock hp A) = RightInverseBounds.append
      (Matrix.of (actualBlock (by omega : m ≤ n) (pastMatrix m A)))
      (Matrix.of (selectedFresh (by omega : m ≤ n) (pastMatrix m A) (freshWindow hp A))) := by
  rw [actualBlock_pastMatrix]
  ext i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simp only [RightInverseBounds.append,Fin.addCases_left,Matrix.of_apply,
      extendedBlock,actualBlock,selectedBlock]
    rfl
  · simp only [RightInverseBounds.append,Fin.addCases_right,Matrix.of_apply,
      selectedFresh,pivotOrder_pastMatrix]
    rfl

/-- Uniform fixed-selected-block fiber estimates transfer to the actual prefix
and its selected fresh rows with their original probability coefficient. -/
theorem adaptive_append_event_le {n m s : ℕ} (hp : m+s ≤ n)
    (E : Set (Mat m × RectMat m s)) (hE : MeasurableSet E) (ε : ℝ≥0∞)
    (hbound : ∀ T : Mat m, gaussianRect m s (Prod.mk T ⁻¹' E) ≤ ε) :
    gaussianMatrix n {A |
      (actualBlock (by omega : m ≤ n) A,
       selectedFresh (by omega : m ≤ n) A (freshWindow hp A)) ∈ E} ≤ ε := by
  let hm : m ≤ n := by omega
  let D : Set (Mat n × RectMat n s) :=
    {q | (actualBlock hm q.1,selectedFresh hm q.1 q.2) ∈ E}
  have hD : MeasurableSet D := hE.preimage
    (((actualBlock_measurable hm).comp measurable_fst).prodMk (selectedFresh_measurable hm))
  have hprod : ((gaussianMatrix n).map (pastMatrix m)).prod (gaussianRect n s) D ≤ ε := by
    rw [Measure.prod_apply hD]
    calc
      _ ≤ ∫⁻ _P : Mat n, ε ∂(gaussianMatrix n).map (pastMatrix m) := by
        apply lintegral_mono
        intro P
        have hmp := selectedFresh_measurePreserving (s:=s) hm P
        have h := Measure.le_map_apply (μ:=gaussianRect n s) hmp.measurable.aemeasurable
          (Prod.mk (actualBlock hm P) ⁻¹' E)
        rw [hmp.map_eq] at h
        exact h.trans (hbound _)
      _ = ε := by rw [lintegral_const,Measure.map_apply (measurable_pastMatrix m) MeasurableSet.univ]; simp
  rw [← past_fresh_joint_law hp,
    Measure.map_apply ((measurable_pastMatrix m).prodMk (freshWindow_measurable hp)) hD] at hprod
  convert hprod using 1
  congr 1
  ext A
  simp only [Set.mem_preimage,D,Set.mem_ofPred_eq,actualBlock_pastMatrix]
  have hs : selectedFresh hm (pastMatrix m A) (freshWindow hp A) =
      selectedFresh hm A (freshWindow hp A) := by
    unfold selectedFresh
    rw [pivotOrder_pastMatrix]
  rw [hs]

#assert_trust kernel gaussianMatrix_prob
#print axioms gaussianMatrix_prob
#assert_trust kernel gaussianRect_prob
#print axioms gaussianRect_prob
#assert_trust kernel matrixMeasurable
#print axioms matrixMeasurable
#assert_trust kernel freshWindow
#print axioms freshWindow
#assert_trust kernel freshWindow_measurable
#print axioms freshWindow_measurable
#assert_trust kernel freshWindow_measurePreserving
#print axioms freshWindow_measurePreserving
#assert_trust kernel past_fresh_joint_law
#print axioms past_fresh_joint_law
#assert_trust kernel pivotOrder_pastMatrix
#print axioms pivotOrder_pastMatrix
#assert_trust kernel actualBlock_pastMatrix
#print axioms actualBlock_pastMatrix
#assert_trust kernel actualBlock_measurable
#print axioms actualBlock_measurable
#assert_trust kernel selectedFresh
#print axioms selectedFresh
#assert_trust kernel selectedFresh_measurable
#print axioms selectedFresh_measurable
#assert_trust kernel selectedFresh_measurePreserving
#print axioms selectedFresh_measurePreserving
#assert_trust kernel extendedBlock_eq_append
#print axioms extendedBlock_eq_append
#assert_trust kernel adaptive_append_event_le
#print axioms adaptive_append_event_le

end NLA.IE06.GaussianAdaptiveAppend
