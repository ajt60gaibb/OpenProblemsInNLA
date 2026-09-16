/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
Complex adaptation of the repository IE-05 finite-maximum and active-block proofs.
-/
import NLA.IE14.Definitions
import Mathlib.Data.Finset.Max

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE14

theorem entryMax_nonneg {n : ℕ} (A : Mat n) : 0 ≤ entryMax A :=
  (entryMaxNN A).coe_nonneg

theorem activeMax_nonneg {n : ℕ} (S : Mat n) (k : ℕ) : 0 ≤ activeMax S k :=
  (activeMaxNN S k).coe_nonneg

theorem norm_le_entryMax {n : ℕ} (A : Mat n) (i j : Fin n) :
    ‖A i j‖ ≤ entryMax A := by
  have h : ‖A i j‖₊ ≤ entryMaxNN A :=
    Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ (i, j))
  have hc := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm, entryMax] using hc

theorem norm_le_activeMax {n : ℕ} (S : Mat n) (k : ℕ) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) : ‖S i j‖ ≤ activeMax S k := by
  have h : ‖S i j‖₊ ≤ activeMaxNN S k := by
    simpa only [activeMaxNN, hi, hj, and_self, if_true] using
      (Finset.le_sup (s := Finset.univ)
        (f := fun ij : Fin n × Fin n =>
          if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)
        (Finset.mem_univ (i, j)))
  have hc := NNReal.coe_le_coe.mpr h
  simpa only [coe_nnnorm, activeMax] using hc

theorem activeMax_le {n : ℕ} (S : Mat n) (k : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ i j, k ≤ i.val → k ≤ j.val → ‖S i j‖ ≤ C) :
    activeMax S k ≤ C := by
  have hnn : activeMaxNN S k ≤ ⟨C, hC⟩ := by
    apply Finset.sup_le
    intro ij _
    by_cases hij : k ≤ ij.1.val ∧ k ≤ ij.2.val
    · simp only [if_pos hij]
      apply NNReal.coe_le_coe.mp
      change ‖S ij.1 ij.2‖ ≤ C
      simpa only [] using h ij.1 ij.2 hij.1 hij.2
    · simp only [if_neg hij]
      exact bot_le
  exact NNReal.coe_le_coe.mpr hnn

theorem entryMax_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, ‖A i j‖ ≤ entryMax A) ∧
      ∃ i j, entryMax A = ‖A i j‖ := by
  refine ⟨entryMax_nonneg A, norm_le_entryMax A, ?_⟩
  let z : Fin n := ⟨0, by omega⟩
  obtain ⟨ij, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => ‖A ij.1 ij.2‖₊) ⟨(z, z), Finset.mem_univ _⟩
  have he : entryMaxNN A = ‖A ij.1 ij.2‖₊ :=
    le_antisymm (Finset.sup_le hmax)
      (Finset.le_sup (f := fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) (Finset.mem_univ ij))
  refine ⟨ij.1, ij.2, ?_⟩
  simpa only [entryMax, coe_nnnorm] using congrArg NNReal.toReal he

theorem activeMax_zero {n : ℕ} (S : Mat n) : activeMax S 0 = entryMax S := by
  simp [activeMax, activeMaxNN, entryMax, entryMaxNN]

theorem swap_active {n : ℕ} (k p i : Fin n) (hp : k ≤ p) (hi : k ≤ i) :
    k ≤ Equiv.swap k p i := by
  by_cases hik : i = k
  · subst i; simpa using hp
  · by_cases hip : i = p
    · subst i; simp
    · simpa [Equiv.swap_apply_of_ne_of_ne hik hip] using hi

/-- The actual finite numerator in the frozen definition of `growth`. -/
def peakMax {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ)

theorem activeMax_le_peakMax {n : ℕ} (A : Mat n) (path : PivotPath n) (k : Fin n) :
    activeMax (trajectory A path k.val) k.val ≤ peakMax A path :=
  NNReal.coe_le_coe.mpr
    (Finset.le_sup (f := fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) (Finset.mem_univ k))

theorem peakMax_le {n : ℕ} (A : Mat n) (path : PivotPath n) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ k : Fin n, activeMax (trajectory A path k.val) k.val ≤ C) :
    peakMax A path ≤ C := by
  have hnn : (Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) ≤ ⟨C,hC⟩ := by
    apply Finset.sup_le
    intro k _
    exact NNReal.coe_le_coe.mp (h k)
  exact NNReal.coe_le_coe.mpr hnn

theorem entryMax_le_peakMax {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (path : PivotPath n) :
    entryMax A ≤ peakMax A path := by
  have h := activeMax_le_peakMax A path (⟨0, by omega⟩ : Fin n)
  simpa only [trajectory, activeMax_zero] using h

theorem multiplier_bound {n : ℕ} (S : Mat n) (k p : Fin n)
    (hp : AdmissiblePivot S k p) (i : Fin n) (hi : k ≤ i) :
    ‖S i k / S p k‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.mpr hp.2.1)]
  exact hp.2.2 i hi

end NLA.IE14
