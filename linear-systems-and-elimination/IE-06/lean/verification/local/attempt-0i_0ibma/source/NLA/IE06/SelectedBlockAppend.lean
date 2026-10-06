import NLA.IE06.GaussianAdaptiveAppend

/-! The single fresh-column A5 cost for the actual selected prefix. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal BigOperators
namespace NLA.IE06.SelectedBlockAppend
open GaussianNull Spectral SpectralMeasurability KyFan TruncatedInverse
open GaussianCandidateStacking SelectedBlockCandidates GaussianAdaptiveAppend
open GaussianAppend RightInverseBounds

local instance matrixMeasurable (r c : Type*) : MeasurableSpace (Matrix r c ℝ) :=
  inferInstanceAs (MeasurableSpace (r → c → ℝ))
local instance matrixBorel (r c : Type*) [Fintype r] [Fintype c] : BorelSpace (Matrix r c ℝ) :=
  inferInstanceAs (BorelSpace (r → c → ℝ))

def appendScale (k : ℕ) (μ x : ℝ) : ℝ := Real.sqrt appendConstant*μ⁻¹*Real.exp (x/k)

theorem appendScale_pos (k : ℕ) {μ : ℝ} (hμ : 0 < μ) (x : ℝ) : 0 < appendScale k μ x := by
  unfold appendScale
  have hc := appendConstant_pos
  positivity

theorem appendScale_sq (k : ℕ) (μ x : ℝ) :
    appendScale k μ x^2 = appendConstant*(μ⁻¹)^2*Real.exp (2*x/k) := by
  unfold appendScale
  rw [mul_pow,mul_pow,Real.sq_sqrt appendConstant_pos.le]
  have he : Real.exp (x/k)^2=Real.exp (2*x/k) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he]

theorem append_surjective {m s : ℕ} (T : Matrix (Fin m) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin s) ℝ) (hT : T.det ≠ 0) :
    Function.Surjective (euclideanMap (append T G)) := by
  have hJ : append T G*stack T⁻¹ (0 : Matrix (Fin s) (Fin m) ℝ)=1 := by
    rw [append_mul_stack,Matrix.mul_zero,add_zero,Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.mpr hT)]
  intro y
  refine ⟨euclideanMap (stack T⁻¹ (0 : Matrix (Fin s) (Fin m) ℝ)) y,?_⟩
  have he := congrArg Matrix.toEuclideanLin hJ
  simp only [Matrix.toLpLin_mul_same,Matrix.toLpLin_one] at he
  exact congrArg (fun f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) => f y) he

def initialGood {m : ℕ} (k : ℕ) (μ : ℝ) (T : Mat m) : Prop :=
  T.det ≠ 0 ∧ μ ≤ singularValue (Matrix.of T) (m-k-1) ∧
    sigmaInvSum (Matrix.of T) k ≤ 2*k*(μ⁻¹)^2

theorem measurableSet_initialGood {m : ℕ} (k : ℕ) (μ : ℝ) :
    MeasurableSet {T : Mat m | initialGood k μ T} := by
  have hSigma : Measurable (fun T : Mat m => sigmaInvSum (Matrix.of T) k) := by
    unfold sigmaInvSum
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_singularValue i.val).inv).pow_const 2
  exact (measurableSet_eq_fun continuous_id.matrix_det.measurable measurable_const).compl.inter
    ((measurableSet_le measurable_const (measurable_singularValue (m-k-1))).inter
      (measurableSet_le hSigma measurable_const))

def appendBadEvent (m k : ℕ) (μ x : ℝ) : Set (Mat m × RectMat m (4*k)) :=
  {q | initialGood k μ q.1 ∧ ¬inverseCap (appendScale k μ x)
    (Real.sqrt k*appendScale k μ x) (append (Matrix.of q.1) (Matrix.of q.2))}

theorem measurableSet_appendBadEvent (m k : ℕ) (μ x : ℝ) :
    MeasurableSet (appendBadEvent m k μ x) := by
  have hm : Measurable (fun q : Mat m × RectMat m (4*k) => append (Matrix.of q.1) (Matrix.of q.2)) :=
    GaussianColumnSplit.joinColumns_measurable m m (4*k)
  exact ((measurableSet_initialGood k μ).preimage measurable_fst).inter
    (((measurableSet_inverseCap _ _).preimage hm).compl)

theorem appendBadEvent_fiber_le {m k : ℕ} (hk : 0 < k) (hkm : k < m)
    {μ x : ℝ} (hμ : 0 < μ) (hμk : μ^2 ≤ k) (hx : 0 < x) (T : Mat m) :
    gaussianRect m (4*k) (Prod.mk T ⁻¹' appendBadEvent m k μ x) ≤
      ENNReal.ofReal (2*Real.exp (-x)) := by
  by_cases hT : initialGood k μ T
  · have h := gaussian_append_tail hk hkm (Matrix.of T) hμ hμk hT.2.1 hT.2.2 hx
    apply (measure_mono ?_).trans h
    intro G hG
    by_contra hnot
    have hgood : opNorm (pinv (append (Matrix.of T) (Matrix.of G)))^2 ≤
        appendConstant*(μ⁻¹)^2*Real.exp (2*x/k) ∧
        frobeniusNorm (pinv (append (Matrix.of T) (Matrix.of G)))^2 ≤
        appendConstant*k*(μ⁻¹)^2*Real.exp (2*x/k) := by
      simpa only [Set.mem_ofPred_eq,not_or,not_lt] using hnot
    have ha := appendScale_pos k hμ x
    have hb : (Real.sqrt k*appendScale k μ x)^2 = appendConstant*k*(μ⁻¹)^2*Real.exp (2*x/k) := by
      rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg k),appendScale_sq]
      ring
    have hr := append_surjective (Matrix.of T) (Matrix.of G) hT.1
    apply hG.2
    refine ⟨hr,?_,?_⟩ <;> rw [gramInverse_eq_pinv _ hr]
    · apply (sq_le_sq₀ (opNorm_nonneg _) ha.le).mp
      rw [appendScale_sq]
      exact hgood.1
    · apply (sq_le_sq₀ (frobeniusNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) ha.le)).mp
      rw [hb]
      exact hgood.2
  · have he : Prod.mk T ⁻¹' appendBadEvent m k μ x = ∅ := by
      ext G
      simp only [Set.mem_preimage,appendBadEvent,Set.mem_ofPred_eq,hT,false_and,Set.mem_empty_iff_false]
    rw [he,measure_empty]
    exact zero_le

theorem actual_append_bad_tail {n m k : ℕ} (hp : m+4*k ≤ n) (hk : 0 < k) (hkm : k < m)
    {μ x : ℝ} (hμ : 0 < μ) (hμk : μ^2 ≤ k) (hx : 0 < x) :
    gaussianMatrix n {A | initialGood k μ (actualBlock (by omega : m ≤ n) A) ∧
      ¬inverseCap (appendScale k μ x) (Real.sqrt k*appendScale k μ x)
        (Matrix.of (extendedBlock hp A))} ≤ ENNReal.ofReal (2*Real.exp (-x)) := by
  have h := adaptive_append_event_le hp (appendBadEvent m k μ x)
    (measurableSet_appendBadEvent m k μ x) _ (appendBadEvent_fiber_le hk hkm hμ hμk hx)
  convert h using 1
  congr 1
  ext A
  simp only [Set.mem_ofPred_eq,appendBadEvent]
  rw [extendedBlock_eq_append,actualBlock_pastMatrix]
  have hs : selectedFresh (by omega : m ≤ n) (PivotFiltration.pastMatrix m A) (freshWindow hp A) =
      selectedFresh (by omega : m ≤ n) A (freshWindow hp A) := by
    unfold selectedFresh
    rw [pivotOrder_pastMatrix]
  rw [hs]

#assert_trust kernel matrixMeasurable
#print axioms matrixMeasurable
#assert_trust kernel matrixBorel
#print axioms matrixBorel
#assert_trust kernel appendScale
#print axioms appendScale
#assert_trust kernel appendScale_pos
#print axioms appendScale_pos
#assert_trust kernel appendScale_sq
#print axioms appendScale_sq
#assert_trust kernel append_surjective
#print axioms append_surjective
#assert_trust kernel initialGood
#print axioms initialGood
#assert_trust kernel measurableSet_initialGood
#print axioms measurableSet_initialGood
#assert_trust kernel appendBadEvent
#print axioms appendBadEvent
#assert_trust kernel measurableSet_appendBadEvent
#print axioms measurableSet_appendBadEvent
#assert_trust kernel appendBadEvent_fiber_le
#print axioms appendBadEvent_fiber_le
#assert_trust kernel actual_append_bad_tail
#print axioms actual_append_bad_tail

end NLA.IE06.SelectedBlockAppend
