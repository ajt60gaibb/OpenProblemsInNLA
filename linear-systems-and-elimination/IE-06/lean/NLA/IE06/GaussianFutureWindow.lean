import NLA.IE06.GaussianCoordinates

/-! Exact original-column partition of a fresh Gaussian suffix. The contract
is independently reviewed in gaussian-stage-smoothing-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianFutureWindow
open GaussianNull GaussianQuadratic GaussianColumnSplit GaussianCoordinates

def windowIndex {n t s : ℕ} (h : t+s ≤ n) :
    Fin s ⊕ {j : Fin n // t+s ≤ j.val} ≃ {j : Fin n // t ≤ j.val} where
  toFun := Sum.elim
    (fun i => ⟨⟨t+i.val,by omega⟩,by change t ≤ t+i.val; omega⟩)
    (fun j => ⟨j.val,by have := j.property; omega⟩)
  invFun j := if hj : j.val.val < t+s then
    Sum.inl ⟨j.val.val-t,by have := j.property; omega⟩
    else Sum.inr ⟨j.val,by omega⟩
  left_inv z := by
    cases z with
    | inl i =>
      dsimp
      rw [dif_pos (by omega)]
      congr 1
      apply Fin.ext
      dsimp
      omega
    | inr j =>
      dsimp
      rw [dif_neg (by have := j.property; omega)]
  right_inv j := by
    dsimp
    split_ifs with hj
    · apply Subtype.ext
      apply Fin.ext
      dsimp
      have := j.property
      omega
    · rfl

def split {n t s : ℕ} (h : t+s ≤ n) (W : FutureBlock n t) :
    RectMat n s × FutureBlock n (t+s) :=
  (fun i j => W (windowIndex h (.inl j)) i,
   fun j i => W (windowIndex h (.inr j)) i)

def assemble {n t s : ℕ} (h : t+s ≤ n)
    (z : RectMat n s × FutureBlock n (t+s)) : FutureBlock n t :=
  fun j i => Sum.elim (fun a => z.1 i a) (fun a => z.2 a i) ((windowIndex h).symm j)

theorem split_measurable {n t s : ℕ} (h : t+s ≤ n) : Measurable (split h) := by
  unfold split
  fun_prop

theorem assemble_measurable {n t s : ℕ} (h : t+s ≤ n) : Measurable (assemble h) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro i
  unfold assemble
  cases (windowIndex h).symm j <;> simp only [Sum.elim_inl,Sum.elim_inr] <;> fun_prop

theorem split_assemble {n t s : ℕ} (h : t+s ≤ n)
    (z : RectMat n s × FutureBlock n (t+s)) : split h (assemble h z) = z := by
  apply Prod.ext <;> funext i j <;> simp [split,assemble]

theorem assemble_split {n t s : ℕ} (h : t+s ≤ n) (W : FutureBlock n t) :
    assemble h (split h W) = W := by
  funext j i
  obtain ⟨z,rfl⟩ := (windowIndex h).surjective j
  cases z <;> simp [assemble,split]

theorem split_measurePreserving {n t s : ℕ} (h : t+s ≤ n) :
    MeasurePreserving (split h) (futureLaw n t)
      ((gaussianRect n s).prod (futureLaw n (t+s))) := by
  let _ : IsProbabilityMeasure (gaussianRect s n) := by
    unfold gaussianRect
    infer_instance
  let _ : IsProbabilityMeasure (gaussianRect n s) := by
    unfold gaussianRect
    infer_instance
  have hr := measurePreserving_piCongrLeft
    (fun _ : Fin s ⊕ {j : Fin n // t+s ≤ j.val} => gaussianVector n)
    (windowIndex h).symm
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin s ⊕ {j : Fin n // t+s ≤ j.val} => gaussianVector n)
  have htr : MeasurePreserving (@GaussianRegression.transpose s n)
      (gaussianRect s n) (gaussianRect n s) :=
    ⟨by unfold GaussianRegression.transpose; fun_prop,GaussianRegression.gaussian_transpose s n⟩
  have hp := htr.prod (MeasurePreserving.id (futureLaw n (t+s)))
  convert hp.comp (hs.comp hr) using 1 <;> try rfl
  funext W
  apply Prod.ext <;> funext i j <;>
    simp [split,GaussianRegression.transpose,MeasurableEquiv.coe_sumPiEquivProdPi,
      MeasurableEquiv.coe_piCongrLeft,Equiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_eq_cast]

theorem assemble_measurePreserving {n t s : ℕ} (h : t+s ≤ n) :
    MeasurePreserving (assemble h) ((gaussianRect n s).prod (futureLaw n (t+s)))
      (futureLaw n t) := by
  refine ⟨assemble_measurable h,?_⟩
  rw [← (split_measurePreserving h).map_eq,
    Measure.map_map (assemble_measurable h) (split_measurable h)]
  have he : assemble h ∘ split h = id := funext (assemble_split h)
  rw [he,Measure.map_id]

#assert_trust kernel windowIndex
#assert_trust kernel split
#assert_trust kernel assemble
#assert_trust kernel split_measurable
#assert_trust kernel assemble_measurable
#assert_trust kernel split_assemble
#assert_trust kernel assemble_split
#assert_trust kernel split_measurePreserving
#assert_trust kernel assemble_measurePreserving
#print axioms split_measurePreserving
#print axioms assemble_measurePreserving
end NLA.IE06.GaussianFutureWindow
