import NLA.IE06.GaussianPivotMasking

/-! Fixed outside-row coordinates for the selected-block extension argument.
The product law never conditions on which rows the pivot rule later chooses.
Preimplementation contract: reviews/selected-block-extension-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace NLA.IE06.GaussianCandidateRows
open GaussianPivotConditioning GaussianPivotMasking GaussianNull GaussianQuadratic

abbrev InsideRows {n : ℕ} (S : Finset (Fin n)) := {i : Fin n // i ∈ S}

def outsideGaussian {n : ℕ} (S : Finset (Fin n)) :
    Measure (OutsideRows S → Fin n → ℝ) :=
  Measure.pi (fun _ : OutsideRows S => gaussianVector n)

def insideData {n s p : ℕ} (S : Finset (Fin n)) (e : Fin s ≃ InsideRows S)
    (hp : p ≤ n) (A : Mat n) : RectMat s p :=
  fun i j => A (e i).val (Fin.castLE hp j)

theorem measurable_insideData {n s p : ℕ} (S : Finset (Fin n))
    (e : Fin s ≃ InsideRows S) (hp : p ≤ n) : Measurable (insideData S e hp) := by
  unfold insideData
  fun_prop

/-- Exact independence of all outside rows and a prescribed prefix of the
inside rows, with no adaptive conditioning. -/
theorem outside_inside_joint_law {n s p : ℕ} (S : Finset (Fin n))
    (e : Fin s ≃ InsideRows S) (hp : p ≤ n) :
    (gaussianMatrix n).map (fun A => (outsideData S A, insideData S e hp A)) =
      (outsideGaussian S).prod (gaussianRect s p) := by
  classical
  let : Fintype (InsideRows S) := Subtype.fintype _
  let _ : IsProbabilityMeasure (gaussianRect s p) := by unfold gaussianRect; infer_instance
  let μout := outsideGaussian S
  let _ : IsProbabilityMeasure μout := by dsimp [μout, outsideGaussian]; infer_instance
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => gaussianVector n) (fun i => i ∈ S)
  have hreindex := measurePreserving_piCongrLeft
    (fun _ : Fin s => gaussianVector n) e.symm
  have hprefix : MeasurePreserving
      (fun X : Fin s → Fin n → ℝ => fun (i : Fin s) (j : Fin p) => X i (Fin.castLE hp j))
      (gaussianRect s n) (gaussianRect s p) := by
    exact measurePreserving_pi (fun _ : Fin s => gaussianVector n)
      (fun _ : Fin s => gaussianVector p) (fun _ =>
      ⟨by fun_prop, gaussian_coordinates_map
      (⟨Fin.castLE hp, Fin.castLE_injective hp⟩ : Fin p ↪ Fin n)⟩)
  have hid : MeasurePreserving (id : (OutsideRows S → Fin n → ℝ) → _)
      μout μout := ⟨measurable_id, Measure.map_id⟩
  have h := Measure.measurePreserving_swap.comp (((hprefix.comp hreindex).prod hid).comp hsplit)
  have hh := h.map_eq
  have hf : (Prod.swap ∘ (Prod.map
      ((fun X : Fin s → Fin n → ℝ => fun (i : Fin s) (j : Fin p) => X i (Fin.castLE hp j)) ∘
        MeasurableEquiv.piCongrLeft (fun _ : Fin s => Fin n → ℝ) e.symm) id ∘
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => Fin n → ℝ)
        (fun i => i ∈ S))) =
      (fun A => (outsideData S A, insideData S e hp A)) := by
    funext A
    apply Prod.ext
    · rfl
    · funext i j
      have hr := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin s => Fin n → ℝ)
        e.symm (fun x : InsideRows S => A x.val) (e i)
      have hj := congrArg (fun row : Fin n → ℝ => row (Fin.castLE hp j)) hr
      simp only [Equiv.symm_apply_apply] at hj
      simpa only [Function.comp_def, Prod.map, Prod.swap,
        MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
        Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_mk, insideData] using hj
  rw [hf] at hh
  exact hh

/-- The candidate selected block is defined on the literal outside coordinates. -/
def candidateBlock {n m p : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (hp : p ≤ n) (Z : OutsideRows S → Fin n → ℝ) : RectMat m p :=
  fun i j => Z (candidateOrder S hm (restoreOutside S Z) i) (Fin.castLE hp j)

theorem measurable_candidateBlock {n m p : ℕ} (S : Finset (Fin n))
    (hm : m ≤ n-S.card) (hp : p ≤ n) : Measurable (candidateBlock S hm hp) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have he : Measurable (fun q : (OutsideRows S → Fin n → ℝ) × OutsideRows S =>
      q.1 q.2 (Fin.castLE hp j)) :=
    measurable_from_prod_countable_left (fun r => by fun_prop)
  exact he.comp (measurable_id.prodMk
    ((measurable_candidateOrder_coordinate S hm i).comp (measurable_restoreOutside S)))


theorem candidateBlock_outsideData {n m p : ℕ} (S : Finset (Fin n))
    (hm : m ≤ n-S.card) (hp : p ≤ n) (A : Mat n) :
    candidateBlock S hm hp (outsideData S A) =
      (fun i j => A (candidateLabels S hm A i) (Fin.castLE hp j)) := by
  funext i j
  have hc := candidateLabels_outsideData S hm A
  have hi := congrArg (fun q : Fin m ↪ Fin n => q i) hc
  change A (candidateLabels S hm (restoreOutside S (outsideData S A)) i) _ = _
  rw [← hi]

/-- Integrate an intrinsic bad-event bound in each outside-row fiber. In
particular, no measurability of a fiberwise auxiliary frame is required. -/
theorem candidate_fiber_event_le {n m s p : ℕ} (S : Finset (Fin n))
    (e : Fin s ≃ InsideRows S) (hm : m ≤ n-S.card) (hp : p ≤ n)
    (E : Set (RectMat m p × RectMat s p)) (hE : MeasurableSet E)
    (ε : ℝ≥0∞)
    (hbound : ∀ Z : OutsideRows S → Fin n → ℝ,
      gaussianRect s p (Prod.mk (candidateBlock S hm hp Z) ⁻¹' E) ≤ ε) :
    gaussianMatrix n {A | (candidateBlock S hm hp (outsideData S A), insideData S e hp A) ∈ E}
      ≤ ε := by
  let _ : IsProbabilityMeasure (outsideGaussian S) := by unfold outsideGaussian; infer_instance
  let _ : IsProbabilityMeasure (gaussianRect s p) := by unfold gaussianRect; infer_instance
  let D : Set ((OutsideRows S → Fin n → ℝ) × RectMat s p) :=
    (fun q => (candidateBlock S hm hp q.1, q.2)) ⁻¹' E
  have hD : MeasurableSet D := hE.preimage
    (((measurable_candidateBlock S hm hp).comp measurable_fst).prodMk measurable_snd)
  have hprod : (outsideGaussian S).prod (gaussianRect s p) D ≤ ε := by
    rw [Measure.prod_apply hD]
    calc
      _ ≤ ∫⁻ _ : OutsideRows S → Fin n → ℝ, ε ∂outsideGaussian S :=
        lintegral_mono hbound
      _ = ε := by simp
  rw [← outside_inside_joint_law S e hp,
    Measure.map_apply ((measurable_outsideData S).prodMk (measurable_insideData S e hp)) hD] at hprod
  exact hprod

/-! Every owned declaration is audited transitively in kernel mode. -/
#assert_trust kernel InsideRows
#assert_trust kernel outsideGaussian
#assert_trust kernel insideData
#assert_trust kernel measurable_insideData
#assert_trust kernel outside_inside_joint_law
#assert_trust kernel candidateBlock
#assert_trust kernel measurable_candidateBlock
#assert_trust kernel candidateBlock_outsideData
#assert_trust kernel candidate_fiber_event_le
#print axioms InsideRows
#print axioms outsideGaussian
#print axioms insideData
#print axioms measurable_insideData
#print axioms outside_inside_joint_law
#print axioms candidateBlock
#print axioms measurable_candidateBlock
#print axioms candidateBlock_outsideData
#print axioms candidate_fiber_event_le

end NLA.IE06.GaussianCandidateRows
