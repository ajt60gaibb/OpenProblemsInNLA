import NLA.Proofs.RE06.GaussianFiniteSelection
import NLA.Proofs.RE06.GaussianSelectionMeasurable

/-! Finite-valued warm-start selection keeps the original independent repair
law, with no candidate-count factor. Fixed-candidate repair-event bounds and
null measurability are explicit internal premises, not RE-06 export premises. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

abbrev RepairEntries (n k ell : ℕ) := (Fin n × Fin k → ℝ) × (Fin n × Fin ell → ℝ)

def gaussianRepairEntries (n s k ell : ℕ) (ω : ℕ → ℝ) : RepairEntries n k ell :=
  ((fun p => gaussianBlock n k s ω p.1 p.2),
    (fun p => gaussianBlock n ell (s + k) ω p.1 p.2))

def gaussianRepairLaw (n k ell : ℕ) : Measure (RepairEntries n k ell) :=
  (Measure.pi (fun _ : Fin n × Fin k => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1))

theorem gaussianFirst_independent_repair (n s k ell : ℕ) :
    IndepFun (fun ω : ℕ → ℝ => fun p : Fin n × Fin s => gaussianBlock n s 0 ω p.1 p.2)
      (gaussianRepairEntries n s k ell) GaussianLaw := by
  have h := (gaussianThreeBlocks_independent n s k ell).indepFun_prodMk₀
    (fun b => (gaussianBlock_entries_hasLaw n (gaussianBlockWidth s k ell b)
      (gaussianBlockOffset s k b)).aemeasurable) 1 2 0 (by decide) (by decide)
  simpa [gaussianBlockWidth, gaussianBlockOffset, gaussianRepairEntries] using h.symm

theorem gaussianRepairEntries_hasLaw (n s k ell : ℕ) :
    HasLaw (gaussianRepairEntries n s k ell) (gaussianRepairLaw n k ell) GaussianLaw := by
  have h := (gaussianThreeBlocks_independent n s k ell).indepFun
    (show (1 : Fin 3) ≠ 2 by decide)
  have hind : IndepFun
      (fun ω : ℕ → ℝ => fun p : Fin n × Fin k => gaussianBlock n k s ω p.1 p.2)
      (fun ω : ℕ → ℝ => fun p : Fin n × Fin ell => gaussianBlock n ell (s + k) ω p.1 p.2)
      GaussianLaw := by simpa [gaussianBlockWidth, gaussianBlockOffset] using h
  exact (indepFun_iff_hasLaw_prodMk_prod (gaussianBlock_entries_hasLaw n k s)
    (gaussianBlock_entries_hasLaw n ell (s + k))).mp hind

theorem gaussianWarmIndex_independent_repair {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (s k ell : ℕ) :
    IndepFun (gaussianWarmIndex F A s 0) (gaussianRepairEntries n s k ell) GaussianLaw := by
  have hf : Measurable (fun x : Fin n × Fin s → ℝ =>
      warmIndexFromEntries F A s (fun i j => x (i, j))) := by
    apply (warmIndexFromEntries_measurable F A s).comp
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply (i, j)
  exact (gaussianFirst_independent_repair n s k ell).comp hf measurable_id

/-- Actual independent selection transport, allowing AE-measurable repair events. -/
theorem gaussianWarmIndex_selected_failure_le {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (s k ell : ℕ)
    (E : Fin (m + 2) → Set (RepairEntries n k ell))
    (hE : ∀ b, NullMeasurableSet (E b) (gaussianRepairLaw n k ell)) (δ : ℝ)
    (hbound : ∀ b, (gaussianRepairLaw n k ell).real (E b) ≤ δ) :
    NullMeasurableSet {ω | gaussianRepairEntries n s k ell ω ∈
      E (gaussianWarmIndex F A s 0 ω)} GaussianLaw ∧
    GaussianLaw.real {ω | gaussianRepairEntries n s k ell ω ∈
      E (gaussianWarmIndex F A s 0 ω)} ≤ δ := by
  have hy := gaussianRepairEntries_hasLaw n s k ell
  have he (b : Fin (m + 2)) :
      NullMeasurableSet (E b) (GaussianLaw.map (gaussianRepairEntries n s k ell)) := by
    rw [hy.map_eq]
    exact hE b
  apply finite_selected_failure_le_nullMeasurable
    (gaussianWarmIndex F A s 0) (gaussianWarmIndex_measurable F A s 0)
    (gaussianRepairEntries n s k ell) hy.aemeasurable
    (gaussianWarmIndex_independent_repair F A s k ell) E he δ
  intro b
  have hmap := Measure.map_apply₀ hy.aemeasurable (he b)
  change (GaussianLaw ((gaussianRepairEntries n s k ell) ⁻¹' E b)).toReal ≤ δ
  rw [← hmap, hy.map_eq]
  exact hbound b

/-- Literal `makePlan` warm-start index, with only a uniform fixed-residual
repair estimate as the internal probability premise. -/
theorem sketchWarmIndex_selected_failure_le {n m : ℕ} (F : Family n m)
    (A : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hsketch : firstWidth m ε + secondWidth m ε + thirdWidth m ε < n)
    (E : Fin (m + 2) → Set (RepairEntries n (secondWidth m ε) (thirdWidth m ε)))
    (hE : ∀ b, NullMeasurableSet (E b)
      (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε))) (δ : ℝ)
    (hbound : ∀ b, (gaussianRepairLaw n (secondWidth m ε) (thirdWidth m ε)).real (E b) ≤ δ) :
    NullMeasurableSet {ω | gaussianRepairEntries n (firstWidth m ε) (secondWidth m ε)
      (thirdWidth m ε) ω ∈ E (sketchWarmIndex F A (makePlan n m ε ω))} GaussianLaw ∧
    GaussianLaw.real {ω | gaussianRepairEntries n (firstWidth m ε) (secondWidth m ε)
      (thirdWidth m ε) ω ∈ E (sketchWarmIndex F A (makePlan n m ε ω))} ≤ δ := by
  have h := gaussianWarmIndex_selected_failure_le F A (firstWidth m ε) (secondWidth m ε)
    (thirdWidth m ε) E hE δ hbound
  simpa only [gaussianWarmIndex_eq_sketchWarmIndex F A ε hsketch] using h

#assert_trust kernel gaussianFirst_independent_repair
#assert_trust kernel gaussianRepairEntries_hasLaw
#assert_trust kernel gaussianWarmIndex_independent_repair
#assert_trust kernel gaussianWarmIndex_selected_failure_le
#assert_trust kernel sketchWarmIndex_selected_failure_le
#print axioms gaussianFirst_independent_repair
#print axioms gaussianRepairEntries_hasLaw
#print axioms gaussianWarmIndex_independent_repair
#print axioms gaussianWarmIndex_selected_failure_le
#print axioms sketchWarmIndex_selected_failure_le
end NLA.Proofs.RE06
