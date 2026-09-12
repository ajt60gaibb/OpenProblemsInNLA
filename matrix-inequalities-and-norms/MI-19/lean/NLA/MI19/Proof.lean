/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-19.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI19.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096

open scoped BigOperators ComplexOrder
noncomputable section

namespace NLA.MI19

/-- The displayed complex matrix is exactly the displayed Gram matrix. -/
theorem gramFactor_mul : gramFactor.conjTranspose * gramFactor = witness := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gramFactor, witness, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, map_ofNat]

theorem witness_posSemidef : witness.PosSemidef := by
  rw [← gramFactor_mul]
  exact Matrix.posSemidef_conjTranspose_mul_self gramFactor

/-- A checked decomposition enumerates permutations without an external table. -/
theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), f σ) =
      ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]

/-- The last index obtained by recursive finite-sum enumeration is index three. -/
theorem fin3_succ_two : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl

/-- Only the six increasing pairs can contribute to inversions at order four. -/
theorem inversionCount_fin4 (σ : Equiv.Perm (Fin 4)) :
    inversionCount σ =
      (if σ 1 < σ 0 then 1 else 0) +
      (if σ 2 < σ 0 then 1 else 0) +
      (if σ 3 < σ 0 then 1 else 0) +
      (if σ 2 < σ 1 then 1 else 0) +
      (if σ 3 < σ 1 then 1 else 0) +
      (if σ 3 < σ 2 then 1 else 0) := by
  unfold inversionCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.lt_def, -Fin.val_fin_lt, -Fin.val_pos_iff, fin3_succ_two, add_assoc]

/-- Concrete-index specializations keep the permutation reduction small. -/
theorem decomposeFin3_apply_two (p : Fin 3) (e : Equiv.Perm (Fin 2)) :
    (Equiv.Perm.decomposeFin.symm (p, e)) 2 = Equiv.swap 0 p (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e p 1

theorem decomposeFin4_apply_two (p : Fin 4) (e : Equiv.Perm (Fin 3)) :
    (Equiv.Perm.decomposeFin.symm (p, e)) 2 = Equiv.swap 0 p (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e p 1

theorem decomposeFin4_apply_three (p : Fin 4) (e : Equiv.Perm (Fin 3)) :
    (Equiv.Perm.decomposeFin.symm (p, e)) 3 = Equiv.swap 0 p (e 2).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e p 2

/-- Exact evaluation of all 24 permutations in the original index ordering. -/
theorem qPermanent_witness :
    qPermanent witnessQ witness = (335001935775 / 16384 : ℂ) := by
  unfold qPermanent
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique]
  simp only [qPermanentTerm, inversionCount_fin4, Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num [witnessQ, witness, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, decomposeFin3_apply_two,
    decomposeFin4_apply_two, decomposeFin4_apply_three, Equiv.swap_apply_def,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, Fin.lt_def, -Fin.val_fin_lt, -Fin.val_pos_iff, -Fin.val_eq_zero_iff]


/-- The restricted sum keeps precisely the permutations preserving the interior singleton. -/
theorem restrictedQPermanent_witness :
    restrictedQPermanent witnessQ witness witnessSubset = (167502585675 / 8192 : ℂ) := by
  unfold restrictedQPermanent
  rw [Finset.sum_filter]
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique]
  norm_num [PreservesSubset, witnessSubset, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, decomposeFin3_apply_two,
    decomposeFin4_apply_two, decomposeFin4_apply_three, Equiv.swap_apply_def,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  simp only [qPermanentTerm, inversionCount_fin4, Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num [witnessQ, witness, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, decomposeFin3_apply_two,
    decomposeFin4_apply_two, decomposeFin4_apply_three, Equiv.swap_apply_def,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, Fin.lt_def,
    -Fin.val_fin_lt, -Fin.val_pos_iff, -Fin.val_eq_zero_iff]

/-- Both evaluated sums lie on the real axis. -/
theorem qPermanent_witness_im : (qPermanent witnessQ witness).im = 0 := by
  rw [qPermanent_witness]
  norm_num

theorem restrictedQPermanent_witness_im :
    (restrictedQPermanent witnessQ witness witnessSubset).im = 0 := by
  rw [restrictedQPermanent_witness]
  norm_num

/-- The actual complex permutation sums have this exact rational difference. -/
theorem exact_gap :
    qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset =
      (-3235575 / 16384 : ℂ) := by
  rw [qPermanent_witness, restrictedQPermanent_witness]
  norm_num

/-- The only numerical inequality uses LeanCert's explicit kernel-checked mode. -/
theorem strict_scalar_gap : (-3235575 : ℝ) / 16384 < 0 := by
  leancert (trust := kernel)

/-- The strict comparison is a real comparison, not complex incomparability. -/
theorem strict_counterexample :
    qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset := by
  have hgap : (-3235575 / 16384 : ℂ) < 0 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_zero] using
      (Complex.real_lt_real.mpr strict_scalar_gap)
  rw [← exact_gap] at hgap
  exact sub_neg.mp hgap

/-- All the original hypotheses and the exact strict violation hold together. -/
theorem counterexample_proved :
    gramFactor.conjTranspose * gramFactor = witness ∧
    witness.IsHermitian ∧ witness.PosSemidef ∧
    0 ≤ witnessQ ∧ witnessQ ≤ 1 ∧
    witnessSubset.Nonempty ∧ witnessSubset ≠ Finset.univ ∧
    (qPermanent witnessQ witness).im = 0 ∧
    (restrictedQPermanent witnessQ witness witnessSubset).im = 0 ∧
    qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset =
      (-3235575 / 16384 : ℂ) ∧
    qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset := by
  refine ⟨gramFactor_mul, witness_posSemidef.isHermitian, witness_posSemidef,
    ?_, ?_, ?_, ?_, qPermanent_witness_im, restrictedQPermanent_witness_im,
    exact_gap, strict_counterexample⟩
  · norm_num [witnessQ]
  · norm_num [witnessQ]
  · simp [witnessSubset]
  · decide

/-- The admissible order-four witness refutes the full canonical universal conjecture. -/
theorem not_subsetConjecture_proved : ¬ SubsetConjecture := by
  intro h
  have hbound := h 4 (by norm_num) witness witness_posSemidef witnessQ
    (by norm_num [witnessQ]) (by norm_num [witnessQ]) witnessSubset
    (by simp [witnessSubset]) (by decide)
  exact (not_le_of_gt strict_counterexample) hbound

#assert_trust kernel qPermanent_witness
#print axioms qPermanent_witness
#assert_trust kernel restrictedQPermanent_witness
#print axioms restrictedQPermanent_witness
#assert_trust kernel strict_scalar_gap
#print axioms strict_scalar_gap
#assert_trust kernel counterexample_proved
#print axioms counterexample_proved
#assert_trust kernel not_subsetConjecture_proved
#print axioms not_subsetConjecture_proved

end NLA.MI19
