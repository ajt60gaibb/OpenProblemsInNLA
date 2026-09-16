/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA.

The actual finite GEPP scan, Schur updates and maxima are measurable in the
ordinary product sigma algebra on the matrix entries. In particular, the
universally quantified class of measurable admissible tie rules is nonempty.
-/
import NLA.IE04.GEPP
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory
noncomputable section
namespace NLA.IE04

theorem measurable_matrix_entries {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : ∀ i j, Measurable (fun a => S a i j)) :
    Measurable S :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hS i)

theorem measurable_matrix_entry {n : ℕ} (i j : Fin n) :
    Measurable (fun A : Mat n => A i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

private theorem measurable_finite_select {α ι β : Type*}
    [MeasurableSpace α] [MeasurableSpace ι] [MeasurableSpace β]
    [Countable ι] [MeasurableSingletonClass ι]
    (f : ι → α → β) (hf : ∀ i, Measurable (f i))
    (p : α → ι) (hp : Measurable p) :
    Measurable (fun a => f (p a) a) := by
  have h : Measurable (fun q : α × ι => f q.2 q.1) :=
    measurable_from_prod_countable_left hf
  exact h.comp (measurable_id.prodMk hp)

private theorem measurable_pivotFold {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : ∀ i j, Measurable (fun a => S a i j))
    (k : Fin n) (l : List (Fin n)) :
    ∀ p : α → Fin n, Measurable p → Measurable (fun a =>
      l.foldl (fun q i => if k ≤ i ∧ |S a q k| < |S a i k| then i else q) (p a)) := by
  classical
  induction l with
  | nil =>
      intro p hp
      simpa only [List.foldl_nil] using hp
  | cons i l ih =>
      intro p hp
      have hleft : Measurable (fun a => S a (p a) k) :=
        measurable_finite_select (fun q a => S a q k) (fun q => hS q k) p hp
      have htest : MeasurableSet {a | k ≤ i ∧ |S a (p a) k| < |S a i k|} := by
        by_cases hki : k ≤ i
        · simpa only [hki, true_and] using measurableSet_lt hleft.abs (hS i k).abs
        · simp only [hki, false_and, Set.ofPred_false, MeasurableSet.empty]
      have hnext : Measurable (fun a =>
          if k ≤ i ∧ |S a (p a) k| < |S a i k| then i else p a) :=
        Measurable.ite htest measurable_const hp
      simpa only [List.foldl_cons] using ih _ hnext

theorem measurable_firstPivotIndex {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : ∀ i j, Measurable (fun a => S a i j)) (k : Fin n) :
    Measurable (fun a => firstPivotIndex (S a) k) := by
  exact measurable_pivotFold S hS k (List.finRange n) (fun _ => k) measurable_const

private theorem measurable_schur_fixed {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : ∀ i j, Measurable (fun a => S a i j)) (k p : Fin n) :
    Measurable (fun a => schurStep (S a) k p) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hij : k < i ∧ k < j
  · convert (hS (Equiv.swap k p i) j).sub
        (((hS (Equiv.swap k p i) k).div (hS (Equiv.swap k p k) k)).mul
          (hS (Equiv.swap k p k) j)) using 1
    funext a
    simp only [schurStep, rowSwap, hij, and_self, if_true,
      Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
  · simpa only [schurStep, rowSwap, hij, if_false] using
      (measurable_const : Measurable (fun _ : α => (0 : ℝ)))

theorem measurable_schur_selected {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : ∀ i j, Measurable (fun a => S a i j))
    (k : Fin n) (p : α → Fin n) (hp : Measurable p) :
    Measurable (fun a => schurStep (S a) k (p a)) :=
  measurable_finite_select (fun q a => schurStep (S a) k q)
    (fun q => measurable_schur_fixed S hS k q) p hp

theorem measurable_firstTrajectory (n k : ℕ) :
    Measurable (fun A : Mat n => firstTrajectory A k) := by
  induction k with
  | zero => simpa only [firstTrajectory, id] using (measurable_id : Measurable (@id (Mat n)))
  | succ k ih =>
      by_cases hk : k < n
      · have hentries : ∀ i j, Measurable (fun A : Mat n => firstTrajectory A k i j) :=
          fun i j => (measurable_matrix_entry i j).comp ih
        simpa only [firstTrajectory, dif_pos hk] using
          measurable_schur_selected (fun A : Mat n => firstTrajectory A k) hentries
            ⟨k, hk⟩ (fun A => firstPivotIndex (firstTrajectory A k) ⟨k, hk⟩)
            (measurable_firstPivotIndex _ hentries ⟨k, hk⟩)
      · simpa only [firstTrajectory, dif_neg hk] using
          (measurable_const : Measurable (fun _ : Mat n => (0 : Mat n)))

private theorem measurable_nnreal_finset_sup {α ι : Type*} [MeasurableSpace α]
    (s : Finset ι) (f : ι → α → ℝ≥0) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => s.sup (fun i => f i a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, NNReal.bot_eq_zero] using
      (measurable_const : Measurable (fun _ : α => (0 : ℝ≥0)))
  | @insert i s hi ih =>
      convert (hf i).sup ih using 1
      funext a
      simp only [Finset.sup_insert, Pi.sup_apply, sup_eq_max]

theorem measurable_entryMax (n : ℕ) : Measurable (@entryMax n) := by
  exact (measurable_nnreal_finset_sup Finset.univ
    (fun ij : Fin n × Fin n => fun A : Mat n => ‖A ij.1 ij.2‖₊)
    (fun ij => (measurable_matrix_entry ij.1 ij.2).nnnorm)).coe_nnreal_real

theorem measurable_activeMaxNN {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : Measurable S) (k : ℕ) :
    Measurable (fun a => activeMaxNN (S a) k) := by
  apply measurable_nnreal_finset_sup
  intro ij
  by_cases hij : k ≤ ij.1.val ∧ k ≤ ij.2.val
  · simpa only [hij, and_self, if_true, Function.comp_def] using
      ((measurable_matrix_entry ij.1 ij.2).comp hS).nnnorm
  · simpa only [hij, if_false] using
      (measurable_const : Measurable (fun _ : α => (0 : ℝ≥0)))

theorem measurable_firstGrowth (n : ℕ) :
    Measurable (fun A : Mat n => growth A (firstPath A)) := by
  have hpeak : Measurable (fun A : Mat n =>
      Finset.univ.sup (fun k : Fin n => activeMaxNN (firstTrajectory A k.val) k.val)) :=
    measurable_nnreal_finset_sup Finset.univ _ fun k =>
      measurable_activeMaxNN _ (measurable_firstTrajectory n k.val) k.val
  convert hpeak.coe_nnreal_real.div (measurable_entryMax n) using 1
  funext A
  simp only [growth, trajectory_firstPath_eq_proved, Pi.div_apply]

theorem firstPath_admissibleRule_proved (n : ℕ) :
    AdmissibleRule (@firstPath n) := by
  refine ⟨?_, measurable_firstGrowth n⟩
  intro A hA k
  exact ((firstPath_semantics_proved A hA).1 k).1

theorem gaussianMatrix_probability_proved (n : ℕ) :
    IsProbabilityMeasure (gaussianMatrix n) := by
  change IsProbabilityMeasure (Measure.pi
    (fun _ : Fin n => Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
  infer_instance

theorem measurable_matrix_det {n : ℕ} :
    Measurable (fun A : Mat n => A.det) := by
  simp_rw [Matrix.det_apply']
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.mul measurable_const
  apply Finset.measurable_prod
  intro i hi
  exact measurable_matrix_entry (σ i) i

theorem measurable_smoothedInput {n : ℕ} (center : Mat n) (σ : ℝ) :
    Measurable (smoothedInput center σ) := by
  apply measurable_matrix_entries
  intro i j
  exact measurable_const.add (measurable_const.mul (measurable_matrix_entry i j))

theorem exceedanceEvent_measurable_proved {n : ℕ} (center : Mat n) (σ t : ℝ)
    (rule : Mat n → PivotPath n) (hrule : AdmissibleRule rule) :
    MeasurableSet (exceedanceEvent center σ t rule) := by
  have hinput := measurable_smoothedInput center σ
  have hdet : Measurable (fun G : Mat n => (smoothedInput center σ G).det) :=
    measurable_matrix_det.comp hinput
  have hnonsingular : MeasurableSet {G : Mat n | (smoothedInput center σ G).det ≠ 0} :=
    (hdet (measurableSet_singleton 0)).compl
  exact hnonsingular.inter (measurableSet_lt measurable_const (hrule.2.comp hinput))

#assert_trust kernel firstPath_admissibleRule_proved
#print axioms firstPath_admissibleRule_proved
#assert_trust kernel gaussianMatrix_probability_proved
#print axioms gaussianMatrix_probability_proved
#assert_trust kernel exceedanceEvent_measurable_proved
#print axioms exceedanceEvent_measurable_proved

end NLA.IE04
