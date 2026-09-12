/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's TR-15 counterexample.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.TR15.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Continuity
import Mathlib.Topology.Order.IntermediateValue
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical
noncomputable section

namespace NLA.TR15

/-- Reindex the actual ordered pairs by a product; no tensor coefficients are
assumed or supplied by a separate numerical oracle. -/
private lemma sum_ordered_pairs (f : (Fin 2 → Fin 3) → ℝ) :
    (∑ a, f a) = ∑ i : Fin 3, ∑ j : Fin 3, f ![i, j] := by
  calc
    _ = ∑ p : Fin 3 × Fin 3, f ![p.1, p.2] :=
      Fintype.sum_equiv (finTwoArrowEquiv (Fin 3)) f
        (fun p => f ![p.1, p.2]) (fun a => by
          congr 1
          ext j
          fin_cases j <;> rfl)
    _ = _ := Fintype.sum_prod_type _

theorem lower_contractions_proved (x : Fin 3 → ℝ) :
    contraction witnessLower x =
      ![(x 0 + x 2) ^ 2 + (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2,
        2 * x 0 * x 1 + 4 * x 1 * x 2,
        (x 0) ^ 2 + 2 * (x 1) ^ 2 + 4 * x 0 * x 2 - (x 2) ^ 2] := by
  funext i
  unfold contraction
  rw [sum_ordered_pairs]
  fin_cases i <;>
    norm_num [witnessLower, lowerTensor, hankelTensor, generatorIndex,
      prependIndex, witnessGenerator, Fin.sum_univ_succ, Fin.prod_univ_succ] <;> ring

/-- The coordinate product vanishes unless every contracted coordinate is one. -/
private lemma upper_product_zero (a : Fin 5 → Fin 2) (ha : a ≠ fun _ => 1) :
    (∏ j : Fin 5, witnessUpperVector (a j)) = 0 := by
  have hz : ∃ j, a j = 0 := by
    by_contra! hn
    apply ha
    funext j
    have hj := hn j
    apply Fin.ext
    have hj' : (a j).val ≠ 0 := by
      intro hz
      exact hj (Fin.ext hz)
    have := (a j).isLt
    omega
  obtain ⟨j, hj⟩ := hz
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj, witnessUpperVector])

theorem upper_contraction_proved :
    contraction witnessUpper witnessUpperVector = ![0, -1] := by
  funext i
  unfold contraction
  rw [Finset.sum_eq_single (fun _ : Fin 5 => (1 : Fin 2))]
  · fin_cases i <;>
      norm_num [witnessUpper, upperTensor, hankelTensor, generatorIndex,
        prependIndex, witnessGenerator, witnessUpperVector,
        Fin.sum_univ_succ, Fin.prod_univ_succ]
  · intro a _ ha
    rw [upper_product_zero a ha, mul_zero]
  · simp

private lemma first_slice_pos (x : Fin 3 → ℝ) (hx : x ≠ 0) :
    0 < (x 0 + x 2) ^ 2 + (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  by_contra! hn
  have h0 : (x 0) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 2)]
  have h1 : (x 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 2)]
  have h2 : (x 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 2)]
  apply hx
  have z0 : x 0 = 0 := sq_eq_zero_iff.mp h0
  have z1 : x 1 = 0 := sq_eq_zero_iff.mp h1
  have z2 : x 2 = 0 := sq_eq_zero_iff.mp h2
  funext i
  fin_cases i <;> simp_all

theorem lower_eigenvalues_pos_proved (eigenvalue : ℝ) (x : Fin 3 → ℝ)
    (h : IsHEigenpair witnessLower eigenvalue x) : 0 < eigenvalue := by
  have he := h.2 0
  rw [lower_contractions_proved] at he
  norm_num only [Matrix.cons_val_zero, Nat.reduceSub] at he
  have hp := first_slice_pos x h.1
  by_contra! hn
  have hnp := mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg (x 0))
  linarith

theorem lower_eigenpair_exists_proved :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ rootPolynomial t = 0 ∧
      IsHEigenpair witnessLower (lowerEigenvalue t) (lowerEigenvector t) := by
  have hcont : Continuous rootPolynomial := by
    unfold rootPolynomial
    continuity
  have hzero : (0 : ℝ) ∈ Set.Ioo (rootPolynomial 0) (rootPolynomial 1) := by
    norm_num [rootPolynomial]
  obtain ⟨t, ht, hroot⟩ :=
    intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hzero
  refine ⟨t, ht.1, ht.2, hroot, ?_, ?_⟩
  · intro hz
    have := congrFun hz 0
    norm_num [lowerEigenvector] at this
  · intro i
    rw [lower_contractions_proved]
    unfold rootPolynomial at hroot
    have h0 : lowerEigenvector t 0 = 1 := rfl
    have h1 : lowerEigenvector t 1 = 0 := rfl
    have h2 : lowerEigenvector t 2 = t := rfl
    simp only [h0, h1, h2]
    fin_cases i <;> norm_num [lowerEigenvalue, lowerEigenvector] <;> nlinarith

/-- The only point interval certificate, explicitly checked in kernel mode and
retained in the actual negative-eigenpair contradiction. -/
lemma negative_eigenvalue_certificate : (-1 : ℝ) < 0 := by
  interval_decide (trust := kernel)

theorem upper_negative_eigenpair_proved :
    IsHEigenpair witnessUpper (-1) witnessUpperVector ∧ (-1 : ℝ) < 0 := by
  refine ⟨⟨?_, ?_⟩, negative_eigenvalue_certificate⟩
  · intro hz
    have := congrFun hz 1
    norm_num [witnessUpperVector] at this
  · intro i
    rw [upper_contraction_proved]
    fin_cases i <;> norm_num [witnessUpperVector]

theorem counterexample_proved :
    Admissible 3 2 2 ∧ HasNoNegativeHEigenvalues witnessLower ∧
      ¬ HasNoNegativeHEigenvalues witnessUpper := by
  refine ⟨⟨⟨1, rfl⟩, by norm_num, by norm_num, by norm_num⟩, ?_, ?_⟩
  · intro eigenvalue x h
    exact (lower_eigenvalues_pos_proved eigenvalue x h).le
  · intro h
    exact (not_le_of_gt upper_negative_eigenpair_proved.2)
      (h (-1) witnessUpperVector upper_negative_eigenpair_proved.1)

theorem not_inheritanceConjecture_proved : ¬ InheritanceConjecture := by
  intro h
  exact counterexample_proved.2.2
    (h 3 2 2 counterexample_proved.1 witnessGenerator counterexample_proved.2.1)

#assert_trust kernel lower_contractions_proved
#assert_trust kernel upper_contraction_proved
#assert_trust kernel lower_eigenvalues_pos_proved
#assert_trust kernel lower_eigenpair_exists_proved
#assert_trust kernel negative_eigenvalue_certificate
#assert_trust kernel upper_negative_eigenpair_proved
#assert_trust kernel counterexample_proved
#assert_trust kernel not_inheritanceConjecture_proved
#print axioms lower_contractions_proved
#print axioms upper_contraction_proved
#print axioms lower_eigenvalues_pos_proved
#print axioms lower_eigenpair_exists_proved
#print axioms negative_eigenvalue_certificate
#print axioms upper_negative_eigenpair_proved
#print axioms counterexample_proved
#print axioms not_inheritanceConjecture_proved

end NLA.TR15
