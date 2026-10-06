import NLA.IE06.GaussianFutureWindow
import NLA.IE06.GaussianSmoothing

/-! Fixed-prefix smoothing for the actual subsequent elimination steps.
The exact constants were independently reviewed before implementation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianFutureSmoothing
open GaussianNull GaussianQuadratic GaussianColumnSplit GaussianCoordinates
open GaussianPivotConditioning EliminationSmoothing PivotFiltration

def threshold (s r : ℕ) (ζ x : ℝ) : ℝ :=
  (2:ℝ)^s*ζ*(1+Real.sqrt (2*(s:ℝ)+4*x)*Real.sqrt (3*Real.exp (2+x/r)/r))

theorem rowNorm_measurable {n : ℕ} (k : ℕ) (i : Fin n) :
    Measurable (fun A : Mat n => rowNorm (Matrix.of (selectedRows A k)) i) := by
  have hn : Measurable (fun E : Mat n => rowNorm (Matrix.of E) i) := by
    change Measurable (fun E : Mat n => ‖(WithLp.toLp 2 (E i) : EuclideanSpace ℝ (Fin n))‖)
    fun_prop
  exact hn.comp (measurable_selectedRows k)

def badEvent (n k : ℕ) (K : ℝ) : Set (Mat n) :=
  {A | A.det ≠ 0 ∧ ∃ i, K < rowNorm (Matrix.of (selectedRows A k)) i}

theorem badEvent_measurable (n k : ℕ) (K : ℝ) : MeasurableSet (badEvent n k K) := by
  simp only [badEvent,Set.ofPred_and,Set.ofPred_exists]
  apply MeasurableSet.inter
  · exact (measurable_matrix_det (measurableSet_singleton 0)).compl
  · exact MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const (rowNorm_measurable k i))

theorem restored_blockColumns {n t s : ℕ} (h : t+s ≤ n) (π : Fin t ↪ Fin n)
    (z : Mat t × (RemainingRows π → Fin t → ℝ))
    (G : RectMat n s) (W : FutureBlock n (t+s)) :
    blockColumns (restore (by omega) π (z,GaussianFutureWindow.assemble h (G,W))) t s h =
      Matrix.of G := by
  have hw := congrArg (fun f : FutureBlock n t => GaussianFutureWindow.split h f)
    (futureColumns_restore (by omega) π (z,GaussianFutureWindow.assemble h (G,W)))
  rw [GaussianFutureWindow.split_assemble] at hw
  exact congrArg Prod.fst hw

theorem fixed_prefix_tail {n t s q r : ℕ} (h : t+s ≤ n) (π : Fin t ↪ Fin n)
    (z : Mat t × (RemainingRows π → Fin t → ℝ))
    (X : Matrix (Fin n) (Fin n) ℝ) (Y Q : Matrix (Fin n) (Fin q) ℝ)
    (hE : Matrix.of (selectedRows (restore (by omega) π (z,0)) t) = X+Y*Qᴴ)
    (hQ : Qᴴ*Q = 1) (hr : 0 < r) (hqr : q ≤ r) (hrs : 3*r ≤ s)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hX : ∀ i, rowNorm X i ≤ ζ) (x : ℝ) (hx : 0 < x) :
    futureLaw n t {W | restore (by omega) π (z,W) ∈ badEvent n (t+s) (threshold s r ζ x)} ≤
      ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
  let _ : IsProbabilityMeasure (gaussianRect n s) := by unfold gaussianRect; infer_instance
  let ht : t ≤ n := by omega
  let E := Matrix.of (selectedRows (restore ht π (z,0)) t)
  let A := fun p : RectMat n s × FutureBlock n (t+s) =>
    restore ht π (z,GaussianFutureWindow.assemble h p)
  let B := A ⁻¹' badEvent n (t+s) (threshold s r ζ x)
  have hA : Measurable A := (restore_measurable ht π).comp
    (measurable_const.prodMk (GaussianFutureWindow.assemble_measurable h))
  have hB : MeasurableSet B := (badEvent_measurable n (t+s) _).preimage hA
  have hfiber (W : FutureBlock n (t+s)) : gaussianRect n s {G | A (G,W) ∈ badEvent n (t+s) (threshold s r ζ x)} ≤
      ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
    let J := fun G : RectMat n s => Matrix.of (blockRows (A (G,W)) (firstPath (A (G,W))) t s)
    apply (measure_mono ?_).trans
      (GaussianSmoothing.gaussian_smoothing E X Y Q hE hQ hr hqr hrs (L := (2:ℝ)^s) hζ (by positivity)
        hX x hx J)
    intro G hG
    have hp := firstPath_admissible_proved (A (G,W)) hG.1
    have he : Matrix.of (selectedRows (A (G,W)) t) = E :=
      congrArg Matrix.of (selectedRows_restore_future ht π z _ 0)
    have hmul : J G*E = Matrix.of (selectedRows (A (G,W)) (t+s)) := by
      rw [← he]
      exact blockRows_mul _ _ t s
    refine ⟨fun i => blockRows_rowL1_le _ _ hp t s i,?_,?_⟩
    · rw [← he,← restored_blockColumns h π z G W]
      exact blockRows_annihilates_block _ _ hp t s h
    · rw [hmul]
      exact hG.2
  have hprod : ((gaussianRect n s).prod (futureLaw n (t+s))) B ≤
      ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) := by
    rw [Measure.prod_apply_symm hB]
    calc
      _ ≤ ∫⁻ _ : FutureBlock n (t+s),
          ((n:ℝ≥0∞)+1)*ENNReal.ofReal (Real.exp (-x)) ∂futureLaw n (t+s) :=
        lintegral_mono hfiber
      _ = _ := by simp
  have hmap := (GaussianFutureWindow.assemble_measurePreserving h).map_eq
  have hm : MeasurableSet {W : FutureBlock n t |
      restore ht π (z,W) ∈ badEvent n (t+s) (threshold s r ζ x)} :=
    (badEvent_measurable n (t+s) _).preimage ((restore_measurable ht π).comp
      (measurable_const.prodMk measurable_id))
  rw [← hmap,Measure.map_apply (GaussianFutureWindow.assemble_measurable h) hm]
  exact hprod

#assert_trust kernel threshold
#assert_trust kernel rowNorm_measurable
#assert_trust kernel badEvent
#assert_trust kernel badEvent_measurable
#assert_trust kernel restored_blockColumns
#assert_trust kernel fixed_prefix_tail
#print axioms fixed_prefix_tail
end NLA.IE06.GaussianFutureSmoothing
