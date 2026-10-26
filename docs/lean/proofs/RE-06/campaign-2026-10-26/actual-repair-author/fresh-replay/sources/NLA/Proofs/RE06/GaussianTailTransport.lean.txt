import NLA.Proofs.RE06.GaussianUpperTail

/-! The Gaussian estimates apply to proved laws of actual rotated coordinates;
no independent replacement probability space is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Transport of the source lower tail along an actual finite product law.
The nonnegative cut value includes the strict zero-tail case. -/
theorem gaussianQuadratic_trimmed_lower_tail_of_hasLaw (s : ℕ)
    (X : Ω → (ι × Fin s → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : ι × Fin s => gaussianReal 0 1)) μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (head : Finset ι)
    (a : ℝ) (ha : 0 ≤ a)
    (hhead : ∀ i ∈ head, a ≤ w i) (htail : ∀ i ∉ head, w i ≤ a)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    μ.real {ω | gaussianQuadratic (fun p : ι × Fin s => w p.1) (X ω) <
      (s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i} ≤
      Real.exp (-(s : ℝ) * (head.card : ℝ) * η / 4) := by
  by_cases hapos : 0 < a
  · let f : ι × Fin s → ℕ := fun p => (Fintype.equivFin (ι × Fin s) p).val
    have hf : Function.Injective f := Fin.val_injective.comp (Fintype.equivFin _).injective
    have hc : Continuous (gaussianQuadratic (fun p : ι × Fin s => w p.1)) := by
      unfold gaussianQuadratic
      fun_prop
    have hm : MeasurableSet {x : ι × Fin s → ℝ |
        gaussianQuadratic (fun p : ι × Fin s => w p.1) x <
          (s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i} :=
      (isOpen_lt hc continuous_const).measurableSet
    rw [hX.measureReal_eq hm, ← (finite_stream_selection_hasLaw f hf).measureReal_eq hm]
    exact streamQuadratic_trimmed_lower_tail s f hf w hw head a hapos hhead htail η hη0 hη1
  · have hzero : a = 0 := le_antisymm (le_of_not_gt hapos) ha
    have hT : (∑ i ∈ headᶜ, w i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact le_antisymm (by simpa only [hzero] using htail i (Finset.mem_compl.mp hi)) (hw i)
    have he : {ω : Ω | gaussianQuadratic (fun p : ι × Fin s => w p.1) (X ω) <
        (s : ℝ) * (1 - η) * ∑ i ∈ headᶜ, w i} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      simp only [hT, mul_zero, Set.mem_ofPred_eq] at hω
      exact (not_lt_of_ge (Finset.sum_nonneg (fun p _ =>
        mul_nonneg (hw p.1) (sq_nonneg (X ω p)))) hω)
    rw [he, measureReal_empty]
    exact (Real.exp_pos _).le

/-- Upper tail, including zero total weight, transported to actual coordinates. -/
theorem gaussianQuadratic_upper_tail_of_hasLaw (s : ℕ)
    (X : Ω → (ι × Fin s → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : ι × Fin s => gaussianReal 0 1)) μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    μ.real {ω | (s : ℝ) * (1 + η) * (∑ i, w i) <
      gaussianQuadratic (fun p : ι × Fin s => w p.1) (X ω)} ≤
      Real.exp (-(s : ℝ) * η ^ 2 / 8) := by
  let f : ι × Fin s → ℕ := fun p => (Fintype.equivFin (ι × Fin s) p).val
  have hf : Function.Injective f := Fin.val_injective.comp (Fintype.equivFin _).injective
  have hc : Continuous (gaussianQuadratic (fun p : ι × Fin s => w p.1)) := by
    unfold gaussianQuadratic
    fun_prop
  have hm : MeasurableSet {x : ι × Fin s → ℝ |
      (s : ℝ) * (1 + η) * (∑ i, w i) < gaussianQuadratic (fun p : ι × Fin s => w p.1) x} :=
    (isOpen_lt continuous_const hc).measurableSet
  rw [hX.measureReal_eq hm, ← (finite_stream_selection_hasLaw f hf).measureReal_eq hm]
  exact streamQuadratic_upper_tail s f hf w hw η hη0 hη1

#assert_trust kernel gaussianQuadratic_trimmed_lower_tail_of_hasLaw
#assert_trust kernel gaussianQuadratic_upper_tail_of_hasLaw
#print axioms gaussianQuadratic_trimmed_lower_tail_of_hasLaw
#print axioms gaussianQuadratic_upper_tail_of_hasLaw
end NLA.Proofs.RE06
