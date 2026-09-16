/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
-/
import NLA.MF12.Definitions
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical

namespace NLA.MF12

@[simp] lemma matrixProduct_nil {d : ℕ} :
    matrixProduct ([] : List (Square d)) = 1 := by
  simp [matrixProduct]

lemma matrixProduct_append {d : ℕ} (u v : List (Square d)) :
    matrixProduct (u ++ v) = matrixProduct v * matrixProduct u := by
  simp [matrixProduct, List.reverse_append, List.prod_append]

@[simp] lemma matrixProduct_cons {d : ℕ} (A : Square d) (w : List (Square d)) :
    matrixProduct (A :: w) = matrixProduct w * A := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

@[simp] lemma binaryProduct_nil {d : ℕ} (A P : Square d) :
    binaryProduct A P [] = 1 := by simp [binaryProduct]

lemma binaryProduct_cons {d : ℕ} (A P : Square d) (b : Bool) (w : List Bool) :
    binaryProduct A P (b :: w) = binaryProduct A P w * cond b P A := by
  simp [binaryProduct]

lemma binaryProduct_append {d : ℕ} (A P : Square d) (u v : List Bool) :
    binaryProduct A P (u ++ v) = binaryProduct A P v * binaryProduct A P u := by
  simp only [binaryProduct, List.map_append, matrixProduct_append]

@[simp] lemma binaryProduct_replicate_false {d : ℕ} (A P : Square d) (n : ℕ) :
    binaryProduct A P (List.replicate n false) = A ^ n := by
  simp [binaryProduct, matrixProduct, List.map_replicate]

@[simp] lemma binaryProduct_replicate_true {d : ℕ} (A P : Square d) (n : ℕ) :
    binaryProduct A P (List.replicate n true) = P ^ n := by
  simp [binaryProduct, matrixProduct, List.map_replicate]

lemma wordNorms_finite {d : ℕ} (M : Finset (Square d)) (n : ℕ) :
    (wordNorms M n).Finite := by
  let f : List {A : Square d // A ∈ M} → ℝ :=
    fun w => spectralNorm (matrixProduct (w.map Subtype.val))
  have hfin := (List.finite_length_eq {A : Square d // A ∈ M} n).image f
  apply hfin.subset
  rintro r ⟨w, hwn, hwM, hr⟩
  let v : List {A : Square d // A ∈ M} := w.attachWith (fun A => A ∈ M) hwM
  have hv : v.map Subtype.val = w := List.attachWith_map_subtype_val hwM
  refine ⟨v, ?_, ?_⟩
  · change v.length = n
    simpa only [List.length_map, hwn] using congrArg List.length hv
  · change spectralNorm (matrixProduct (v.map Subtype.val)) = r
    rw [hv]
    exact hr.symm

lemma wordNorms_nonempty {d : ℕ} (M : Finset (Square d)) (hM : M.Nonempty)
    (n : ℕ) : (wordNorms M n).Nonempty := by
  obtain ⟨A, hA⟩ := hM
  refine ⟨spectralNorm (matrixProduct (List.replicate n A)),
    List.replicate n A, by simp, ?_, rfl⟩
  intro B hB
  have hBA : B = A := List.eq_of_mem_replicate hB
  simpa only [hBA] using hA

theorem family_growth_is_maximum {d : ℕ} (M : Finset (Square d))
    (hM : M.Nonempty) (n : ℕ) :
    (wordNorms M n).Finite ∧ (wordNorms M n).Nonempty ∧
    (∃ w : List (Square d), w.length = n ∧ (∀ A ∈ w, A ∈ M) ∧
      spectralNorm (matrixProduct w) = familyGrowth M n) ∧
    ∀ w : List (Square d), w.length = n → (∀ A ∈ w, A ∈ M) →
      spectralNorm (matrixProduct w) ≤ familyGrowth M n := by
  have hf := wordNorms_finite M n
  have hn := wordNorms_nonempty M hM n
  obtain ⟨w, hwn, hwM, he⟩ := hn.csSup_mem hf
  refine ⟨hf, hn, ⟨w, hwn, hwM, he.symm⟩, ?_⟩
  intro v hvn hvM
  exact le_csSup hf.bddAbove ⟨v, hvn, hvM, rfl⟩

private lemma list_pair_encoding {d : ℕ} (A P : Square d) (w : List (Square d))
    (hw : ∀ B ∈ w, B ∈ pairFamily A P) :
    ∃ v : List Bool, v.map (fun b => cond b P A) = w := by
  revert hw
  induction w with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons B w ih =>
      intro hw
      obtain ⟨v, hv⟩ := ih (fun C hC => hw C (List.mem_cons_of_mem B hC))
      have hB : B = A ∨ B = P := by simpa [pairFamily] using hw B (by simp)
      rcases hB with hB | hB
      · refine ⟨false :: v, ?_⟩
        simp [hv, hB]
      · refine ⟨true :: v, ?_⟩
        simp [hv, hB]

theorem pair_word_norms {d : ℕ} (A P : Square d) (n : ℕ) :
    wordNorms (pairFamily A P) n =
      {r | ∃ w : List Bool, w.length = n ∧ r = spectralNorm (binaryProduct A P w)} := by
  ext r
  constructor
  · rintro ⟨w, hwn, hwM, hr⟩
    obtain ⟨v, hv⟩ := list_pair_encoding A P w hwM
    refine ⟨v, ?_, ?_⟩
    · simpa only [List.length_map, hwn] using congrArg List.length hv
    · simpa only [binaryProduct, hv] using hr
  · rintro ⟨v, hvn, hr⟩
    refine ⟨v.map (fun b => cond b P A), by simpa using hvn, ?_, hr⟩
    intro B hB
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hB
    cases b <;> simp [pairFamily]

lemma binaryProduct_le_familyGrowth {d : ℕ} (A P : Square d) (w : List Bool) :
    spectralNorm (binaryProduct A P w) ≤ familyGrowth (pairFamily A P) w.length := by
  apply le_csSup (wordNorms_finite _ _).bddAbove
  rw [pair_word_norms]
  exact ⟨w, rfl, rfl⟩

lemma familyGrowth_le_of_binary {d : ℕ} (A P : Square d) (n : ℕ) (C : ℝ)
    (hC : ∀ w : List Bool, w.length = n → spectralNorm (binaryProduct A P w) ≤ C) :
    familyGrowth (pairFamily A P) n ≤ C := by
  apply csSup_le (wordNorms_nonempty _ (by simp [pairFamily]) n)
  intro r hr
  rw [pair_word_norms] at hr
  obtain ⟨w, hwn, rfl⟩ := hr
  exact hC w hwn

#assert_trust kernel family_growth_is_maximum
#assert_trust kernel pair_word_norms
#print axioms family_growth_is_maximum
#print axioms pair_word_norms

end NLA.MF12
