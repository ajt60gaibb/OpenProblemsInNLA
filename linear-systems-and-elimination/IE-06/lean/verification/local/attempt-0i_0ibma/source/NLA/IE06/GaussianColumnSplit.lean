import NLA.IE06.GaussianPivotConditioning
import NLA.IE06.RightInverseBounds

/-! Exact fresh-column disintegration. The mathematical contract and its
independent preimplementation review are in gaussian-column-split-specification.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
namespace NLA.IE06.GaussianColumnSplit
open GaussianNull GaussianQuadratic GaussianPivotConditioning

local instance gaussianMatrix_prob (d : ℕ) : IsProbabilityMeasure (gaussianMatrix d) :=
  gaussianMatrix_probability_proved d

def splitVector (a b : ℕ) (x : Fin (a+b) → ℝ) : (Fin a → ℝ) × (Fin b → ℝ) :=
  (fun j => x (Fin.castAdd b j), fun j => x (Fin.natAdd a j))

theorem splitVector_measurePreserving (a b : ℕ) :
    MeasurePreserving (splitVector a b) (gaussianVector (a+b))
      ((gaussianVector a).prod (gaussianVector b)) := by
  have hr := measurePreserving_piCongrLeft
    (fun _ : Fin a ⊕ Fin b => gaussianReal 0 1) finSumFinEquiv.symm
  have hs := measurePreserving_sumPiEquivProdPi
    (fun _ : Fin a ⊕ Fin b => gaussianReal 0 1)
  convert hs.comp hr using 1 <;> try rfl
  funext x
  apply Prod.ext <;> funext j <;>
    simp [splitVector,MeasurableEquiv.coe_sumPiEquivProdPi,
      MeasurableEquiv.coe_piCongrLeft,Equiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_eq_cast]

def splitColumns {m a b : ℕ} (A : RectMat m (a+b)) : RectMat m a × RectMat m b :=
  (fun i j => A i (Fin.castAdd b j), fun i j => A i (Fin.natAdd a j))

theorem splitColumns_measurePreserving (m a b : ℕ) :
    MeasurePreserving (@splitColumns m a b) (gaussianRect m (a+b))
      ((gaussianRect m a).prod (gaussianRect m b)) := by
  have hr := measurePreserving_pi (fun _ : Fin m => gaussianVector (a+b))
    (fun _ : Fin m => (gaussianVector a).prod (gaussianVector b))
    (fun _ => splitVector_measurePreserving a b)
  have hs := measurePreserving_arrowProdEquivProdArrow (Fin a → ℝ) (Fin b → ℝ) (Fin m)
    (fun _ => gaussianVector a) (fun _ => gaussianVector b)
  convert hs.comp hr using 1 <;> rfl

def joinColumns {m a b : ℕ} (z : RectMat m a × RectMat m b) : RectMat m (a+b) :=
  RightInverseBounds.append (Matrix.of z.1) (Matrix.of z.2)

theorem split_join {m a b : ℕ} (z : RectMat m a × RectMat m b) :
    splitColumns (joinColumns z) = z := by
  apply Prod.ext <;> funext i j <;>
    simp [splitColumns,joinColumns,RightInverseBounds.append]

theorem join_split {m a b : ℕ} (A : RectMat m (a+b)) :
    joinColumns (splitColumns A) = A := by
  funext i j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
    simp [splitColumns,joinColumns,RightInverseBounds.append]

theorem joinColumns_measurable (m a b : ℕ) : Measurable (@joinColumns m a b) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;>
    simp only [joinColumns,RightInverseBounds.append,Fin.addCases_left,Fin.addCases_right,
      Matrix.of_apply] <;> fun_prop

theorem joinColumns_measurePreserving (m a b : ℕ) :
    MeasurePreserving (@joinColumns m a b) ((gaussianRect m a).prod (gaussianRect m b))
      (gaussianRect m (a+b)) := by
  refine ⟨joinColumns_measurable m a b,?_⟩
  rw [← (splitColumns_measurePreserving m a b).map_eq,
    Measure.map_map (joinColumns_measurable m a b) (splitColumns_measurePreserving m a b).measurable]
  have he : joinColumns ∘ (@splitColumns m a b) = id := funext join_split
  rw [he,Measure.map_id]

abbrev FutureBlock (n t : ℕ) := {j : Fin n // t ≤ j.val} → Fin n → ℝ

def futureLaw (n t : ℕ) : Measure (FutureBlock n t) :=
  Measure.pi (fun _ : {j : Fin n // t ≤ j.val} => gaussianVector n)

instance futureLaw_probability (n t : ℕ) : IsProbabilityMeasure (futureLaw n t) := by
  unfold futureLaw gaussianVector
  infer_instance

theorem fixed_blocks_independent_future {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    IndepFun (fun A : Mat n => (selectedBlock ht π A, remainingBlock ht π A))
      (PivotFiltration.futureColumns t) (gaussianMatrix n) := by
  have h := (PivotFiltration.pastMatrix_independent_futureColumns (n := n) t).comp
    (measurable_fixed_blocks ht π) measurable_id
  convert h using 1
  · funext A
    apply Prod.ext <;> funext i j <;>
      simp only [Function.comp_apply,selectedBlock,remainingBlock,PivotFiltration.pastMatrix,
        Fin.val_castLE,Fin.is_lt,if_true]
  · rfl

theorem fixed_blocks_future_joint_law {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    (gaussianMatrix n).map (fun A : Mat n =>
      ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)) =
    ((gaussianMatrix t).prod
      (Measure.pi (fun _ : RemainingRows π => gaussianVector t))).prod (futureLaw n t) := by
  let _ := gaussianMatrix_probability_proved n
  have h := (fixed_blocks_independent_future ht π).map_prod_eq_prod_map_map
    (measurable_fixed_blocks ht π).aemeasurable
    (PivotFiltration.measurable_futureColumns t).aemeasurable
  rw [fixed_blocks_joint_law ht π,PivotFiltration.gaussian_futureColumns_map] at h
  exact h

/-- Future columns remain genuinely independent after the exact pivot-prefix
restriction. The prefix restriction has its actual F7 probability weight. -/
theorem fixed_order_future_restricted_law {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n) :
    ((gaussianMatrix n).restrict (orderEvent ht π)).map (fun A : Mat n =>
      ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)) =
    (((gaussianMatrix t).prod
      (Measure.pi (fun _ : RemainingRows π => gaussianVector t))).restrict
        (fiberRegion (RemainingRows π))).prod (futureLaw n t) := by
  let f := fun A : Mat n =>
    ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)
  have hf : Measurable f := (measurable_fixed_blocks ht π).prodMk
    (PivotFiltration.measurable_futureColumns t)
  have hs : MeasurableSet (fiberRegion (RemainingRows π) ×ˢ (Set.univ : Set (FutureBlock n t))) :=
    (measurableSet_fiberRegion t (RemainingRows π)).prod MeasurableSet.univ
  have he : orderEvent ht π =ᵐ[gaussianMatrix n]
      f ⁻¹' (fiberRegion (RemainingRows π) ×ˢ Set.univ) := by
    simpa only [Set.preimage,Set.mem_prod,Set.mem_univ,and_true,f] using
      orderEvent_ae_eq_fiber ht π
  rw [Measure.restrict_congr_set he,← Measure.restrict_map hf hs]
  rw [fixed_blocks_future_joint_law ht π,← Measure.restrict_prod_eq_prod_univ]

/-- Full tested law: selected block, independently truncated remaining rows,
and independent fresh original columns. No future success event is conditioned on. -/
theorem fixed_order_future_lintegral {n t : ℕ} (ht : t ≤ n) (π : Fin t ↪ Fin n)
    (F : (Mat t × (RemainingRows π → Fin t → ℝ)) × FutureBlock n t → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ A in orderEvent ht π,
      F ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)
      ∂gaussianMatrix n) =
    ∫⁻ T in {T : Mat t | Good T},
      (gaussianVector t (truncationBody T))^(n-t) *
        (∫⁻ Z, ∫⁻ W, F ((T,Z),W) ∂futureLaw n t ∂Measure.pi
          (fun _ : RemainingRows π => GaussianRestriction.restrictedGaussian (truncationBody T)))
      ∂gaussianMatrix t := by
  let F₀ := fun z : Mat t × (RemainingRows π → Fin t → ℝ) => ∫⁻ W, F (z,W) ∂futureLaw n t
  have hF₀ : Measurable F₀ := hF.lintegral_prod_right'
  have hmap := (measurable_fixed_blocks ht π).prodMk (PivotFiltration.measurable_futureColumns t)
  calc
    _ = ∫⁻ z, F z ∂((gaussianMatrix n).restrict (orderEvent ht π)).map
        (fun A : Mat n => ((selectedBlock ht π A,remainingBlock ht π A),PivotFiltration.futureColumns t A)) :=
      (lintegral_map hF hmap).symm
    _ = ∫⁻ z, F z ∂(((gaussianMatrix t).prod
        (Measure.pi (fun _ : RemainingRows π => gaussianVector t))).restrict
          (fiberRegion (RemainingRows π))).prod (futureLaw n t) := by
      rw [fixed_order_future_restricted_law ht π]
    _ = ∫⁻ z, F₀ z ∂((gaussianMatrix t).prod
        (Measure.pi (fun _ : RemainingRows π => gaussianVector t))).restrict
          (fiberRegion (RemainingRows π)) := lintegral_prod _ hF.aemeasurable
    _ = ∫⁻ A in orderEvent ht π, F₀ (selectedBlock ht π A,remainingBlock ht π A)
        ∂gaussianMatrix n := by
      rw [← fixed_order_restricted_law ht π,lintegral_map hF₀ (measurable_fixed_blocks ht π)]
    _ = _ := fixed_order_lintegral ht π F₀ hF₀

#assert_trust kernel FutureBlock
#assert_trust kernel futureLaw
#assert_trust kernel futureLaw_probability
#assert_trust kernel fixed_blocks_independent_future
#assert_trust kernel fixed_blocks_future_joint_law
#assert_trust kernel fixed_order_future_restricted_law
#assert_trust kernel fixed_order_future_lintegral
#print axioms fixed_order_future_restricted_law
#print axioms fixed_order_future_lintegral

#assert_trust kernel splitVector
#assert_trust kernel splitVector_measurePreserving
#assert_trust kernel splitColumns
#assert_trust kernel splitColumns_measurePreserving
#assert_trust kernel joinColumns
#assert_trust kernel split_join
#assert_trust kernel join_split
#assert_trust kernel joinColumns_measurable
#assert_trust kernel joinColumns_measurePreserving
#print axioms splitColumns_measurePreserving
#print axioms joinColumns_measurePreserving
end NLA.IE06.GaussianColumnSplit
