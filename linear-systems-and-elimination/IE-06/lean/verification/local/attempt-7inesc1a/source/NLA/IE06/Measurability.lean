/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Matrix-coordinate, finite-maximum and Schur-update arguments are adapted from
NLA.IE04.Measurability at repository commit
286d8768fbd9a69264daa88e285680293db29837, originally authored by
George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.

The IE-06 adaptation treats every fixed finite pivot path and then takes the
finite union over all admissible paths, retaining all tie choices. The exact
signatures were independently reviewed before implementation.
-/
import NLA.IE06.Definitions
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped NNReal
open MeasureTheory
noncomputable section
namespace NLA.IE06

theorem measurable_matrix_entries {α : Type*} [MeasurableSpace α] {n : ℕ}
    (S : α → Mat n) (hS : ∀ i j, Measurable (fun a => S a i j)) :
    Measurable S :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hS i)

theorem measurable_matrix_entry {n : ℕ} (i j : Fin n) :
    Measurable (fun A : Mat n => A i j) :=
  (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- The total real Schur expression is measurable even away from valid paths.
Nonzero pivots remain part of admissibility, not a measurability premise. -/
theorem measurable_schur_fixed {n : ℕ} (k p : Fin n) :
    Measurable (fun S : Mat n => schurStep S k p) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hij : k < i ∧ k < j
  · convert (measurable_matrix_entry (Equiv.swap k p i) j).sub
        (((measurable_matrix_entry (Equiv.swap k p i) k).div
          (measurable_matrix_entry (Equiv.swap k p k) k)).mul
          (measurable_matrix_entry (Equiv.swap k p k) j)) using 1
    funext S
    simp only [schurStep, rowSwap, hij, and_self, if_true,
      Pi.sub_apply, Pi.mul_apply, Pi.div_apply]
  · simpa only [schurStep, rowSwap, hij, if_false] using
      (measurable_const : Measurable (fun _ : Mat n => (0 : ℝ)))

theorem measurable_trajectory_fixed {n : ℕ} (path : PivotPath n) (k : ℕ) :
    Measurable (fun A : Mat n => trajectory A path k) := by
  induction k with
  | zero =>
      apply measurable_matrix_entries
      intro i j
      simpa only [trajectory] using (measurable_matrix_entry (n := n) i j)
  | succ k ih =>
      by_cases hk : k < n
      · simpa only [trajectory, dif_pos hk, Function.comp_def] using
          (measurable_schur_fixed ⟨k, hk⟩ (path ⟨k, hk⟩)).comp ih
      · simpa only [trajectory, dif_neg hk] using
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
      simp only [Finset.sup_insert, Pi.sup_apply]

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

theorem measurable_growth_fixed {n : ℕ} (path : PivotPath n) :
    Measurable (fun A : Mat n => growth A path) := by
  have hpeak : Measurable (fun A : Mat n =>
      Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val)) :=
    measurable_nnreal_finset_sup Finset.univ _ fun k =>
      measurable_activeMaxNN _ (measurable_trajectory_fixed path k.val) k.val
  exact hpeak.coe_nnreal_real.div (measurable_entryMax n)

theorem measurableSet_admissiblePath_fixed {n : ℕ} (path : PivotPath n) :
    MeasurableSet {A : Mat n | AdmissiblePath A path} := by
  classical
  simp only [AdmissiblePath, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  have hentries : ∀ i j, Measurable (fun A : Mat n => trajectory A path k.val i j) :=
    fun i j => (measurable_matrix_entry i j).comp (measurable_trajectory_fixed path k.val)
  by_cases hactive : k ≤ path k
  · have hnonzero : MeasurableSet {A : Mat n | trajectory A path k.val (path k) k ≠ 0} :=
      ((hentries (path k) k) (measurableSet_singleton 0)).compl
    have hmax : MeasurableSet {A : Mat n | ∀ i, k ≤ i →
        |trajectory A path k.val i k| ≤ |trajectory A path k.val (path k) k|} := by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro _hi
      exact measurableSet_le (hentries i k).abs (hentries (path k) k).abs
    simpa only [AdmissiblePivot, hactive, true_and, Set.ofPred_and] using hnonzero.inter hmax
  · simp only [AdmissiblePivot, hactive, false_and, Set.ofPred_false, MeasurableSet.empty]

theorem measurable_matrix_det {n : ℕ} :
    Measurable (fun A : Mat n => A.det) := by
  simp_rw [Matrix.det_apply']
  apply Finset.measurable_sum
  intro σ hσ
  apply Measurable.mul measurable_const
  apply Finset.measurable_prod
  intro i hi
  exact measurable_matrix_entry (σ i) i

/-- The actual all-admissible-path event is measurable without any
measurability or tie-selection assumptions. -/
theorem exceedanceEvent_measurable_proved (n : ℕ) (t : ℝ) :
    MeasurableSet (exceedanceEvent n t) := by
  classical
  by_cases hn : 0 < n
  · have hnonzero : MeasurableSet {A : Mat n | A.det ≠ 0} :=
      (measurable_matrix_det (measurableSet_singleton 0)).compl
    have hpaths : MeasurableSet {A : Mat n | ∃ path : PivotPath n,
        AdmissiblePath A path ∧ t < growth A path} := by
      simp only [Set.ofPred_exists]
      apply MeasurableSet.iUnion
      intro path
      exact (measurableSet_admissiblePath_fixed path).inter
        (measurableSet_lt measurable_const (measurable_growth_fixed path))
    simpa only [exceedanceEvent, hn, true_and, Set.ofPred_and] using hnonzero.inter hpaths
  · simp only [exceedanceEvent, hn, false_and, Set.ofPred_false, MeasurableSet.empty]

#assert_trust kernel measurable_matrix_entries
#assert_trust kernel measurable_matrix_entry
#assert_trust kernel measurable_schur_fixed
#assert_trust kernel measurable_trajectory_fixed
#assert_trust kernel measurable_nnreal_finset_sup
#assert_trust kernel measurable_entryMax
#assert_trust kernel measurable_activeMaxNN
#assert_trust kernel measurable_growth_fixed
#assert_trust kernel measurableSet_admissiblePath_fixed
#assert_trust kernel measurable_matrix_det
#assert_trust kernel exceedanceEvent_measurable_proved
#print axioms measurable_matrix_entries
#print axioms measurable_matrix_entry
#print axioms measurable_schur_fixed
#print axioms measurable_trajectory_fixed
#print axioms measurable_nnreal_finset_sup
#print axioms measurable_entryMax
#print axioms measurable_activeMaxNN
#print axioms measurable_growth_fixed
#print axioms measurableSet_admissiblePath_fixed
#print axioms measurable_matrix_det
#print axioms exceedanceEvent_measurable_proved

end NLA.IE06
