import NLA.IE06.GaussianStackingTail
import NLA.IE06.GaussianCandidateRows

/-! The fixed outside-row candidate estimate, with an intrinsic measurable
good-rank/good-inverse event. No next-pivot-set conditioning is introduced. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianCandidateStacking
open GaussianNull Spectral KyFan SpectralMeasurability GaussianStackingTail
open GaussianCandidateRows GaussianPivotMasking

local instance matrixMeasurable (r c : Type*) : MeasurableSpace (Matrix r c ℝ) :=
  inferInstanceAs (MeasurableSpace (r → c → ℝ))

def inverseCap {m p : ℕ} (a f : ℝ) (M : Matrix (Fin m) (Fin p) ℝ) : Prop :=
  Function.Surjective (euclideanMap M) ∧ opNorm (gramInverse M) ≤ a ∧
    frobeniusNorm (gramInverse M) ≤ f

theorem measurableSet_inverseCap {m p : ℕ} (a f : ℝ) :
    MeasurableSet {M : Matrix (Fin m) (Fin p) ℝ | inverseCap a f M} := by
  exact measurableSet_surjective.inter
    ((measurableSet_le (measurable_opNorm.comp measurable_gramInverse) measurable_const).inter
      (measurableSet_le (measurable_frobeniusNorm.comp measurable_gramInverse) measurable_const))

def stackBadEvent (m s j : ℕ) (a f x θ : ℝ) :
    Set (RectMat m (m+s) × RectMat s (m+s)) :=
  {q | inverseCap a f (Matrix.of q.1) ∧
    singularValue (Matrix.fromRows (Matrix.of q.1) (Matrix.of q.2)) (m+s-2*j-1) ≤
      stackingThreshold s j a f x θ}

theorem measurableSet_stackBadEvent (m s j : ℕ) (a f x θ : ℝ) :
    MeasurableSet (stackBadEvent m s j a f x θ) := by
  have h : Measurable (fun q : RectMat m (m+s) × RectMat s (m+s) =>
      singularValue (Matrix.fromRows (Matrix.of q.1) (Matrix.of q.2)) (m+s-2*j-1)) := by
    apply (measurable_singularValue (m+s-2*j-1)).comp
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro l
    cases i <;> simp only [Matrix.fromRows, Sum.elim_inl, Sum.elim_inr, Matrix.of_apply] <;> fun_prop
  exact ((measurableSet_inverseCap a f).preimage measurable_fst).inter
    (measurableSet_le h measurable_const)

theorem stackBadEvent_fiber_le {m s j : ℕ}
    (hj : 4 ≤ j) (hjs : 2*j < s) (hjm : j < m)
    {a f x θ : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hx : 0 < x)
    (hθ : 0 < θ) (hθone : θ ≤ 1) (M : RectMat m (m+s)) :
    gaussianRect s (m+s) (Prod.mk M ⁻¹' stackBadEvent m s j a f x θ) ≤
      ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4)) := by
  by_cases hM : inverseCap a f (Matrix.of M)
  · obtain ⟨hrank,ho,hfro⟩ := hM
    rw [gramInverse_eq_pinv _ hrank] at ho hfro
    have h := gaussian_stacking_tail (Matrix.of M) hrank hj hjs hjm ha hf ho hfro hx hθ hθone
    exact (measure_mono (fun B hB => hB.2)).trans h
  · have he : Prod.mk M ⁻¹' stackBadEvent m s j a f x θ = ∅ := by
      ext B
      simp only [Set.mem_preimage,stackBadEvent,Set.mem_ofPred_eq,hM,false_and,Set.mem_empty_iff_false]
    rw [he,measure_empty]
    exact zero_le

/-- One fixed set of original candidate rows, tested against its outside-only
masked candidate prefix. This retains the same fixed-matrix probability cost. -/
theorem candidate_stacking_tail {n m s j : ℕ} (S : Finset (Fin n))
    (e : Fin s ≃ InsideRows S) (hm : m ≤ n-S.card) (hp : m+s ≤ n)
    (hj : 4 ≤ j) (hjs : 2*j < s) (hjm : j < m)
    {a f x θ : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hx : 0 < x)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    gaussianMatrix n {A |
      (candidateBlock S hm hp (outsideData S A),insideData S e hp A) ∈ stackBadEvent m s j a f x θ} ≤
      ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4)) :=
  candidate_fiber_event_le S e hm hp (stackBadEvent m s j a f x θ)
    (measurableSet_stackBadEvent m s j a f x θ) _
    (fun _ => stackBadEvent_fiber_le hj hjs hjm ha hf hx hθ hθone _)

#assert_trust kernel matrixMeasurable
#assert_trust kernel inverseCap
#assert_trust kernel measurableSet_inverseCap
#assert_trust kernel stackBadEvent
#assert_trust kernel measurableSet_stackBadEvent
#assert_trust kernel stackBadEvent_fiber_le
#assert_trust kernel candidate_stacking_tail
#print axioms matrixMeasurable
#print axioms inverseCap
#print axioms measurableSet_inverseCap
#print axioms stackBadEvent
#print axioms measurableSet_stackBadEvent
#print axioms stackBadEvent_fiber_le
#print axioms candidate_stacking_tail

end NLA.IE06.GaussianCandidateStacking
