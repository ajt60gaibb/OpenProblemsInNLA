import NLA.Proofs.RA06.GraphMatrix

/-! The exact Bernoulli sample as a nonnegative weighted complete graph. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

noncomputable def SampleWeight (d : ℕ) (p α : ℝ)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (e : Edge (d + 1)) : ℝ :=
  if kept ((edgeIndex d).symm e) = true then
    1 / RetentionProbability (GraphMatrix d) p α ((edgeIndex d).symm e)
  else 0

theorem sampleWeight_nonneg (d : ℕ) (hd : 0 < d)
    (p α : ℝ) (hα : 0 < α)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (e : Edge (d + 1)) :
    0 ≤ SampleWeight d p α kept e := by
  classical
  have hn : 0 < Fintype.card (Edge (d + 1)) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨(0, Fin.succ (⟨0, hd⟩ : Fin d)), by
      change (0 : ℕ) < 1
      omega⟩⟩
  unfold SampleWeight
  split_ifs
  · exact (one_div_pos.mpr
      (retentionProbability_pos (GraphMatrix d) p α
        (graphMatrix_fullColumnRank d) hn hd hα _)).le
  · exact le_refl _

theorem sampledEnergy_eq_weighted (d : ℕ) (p α : ℝ)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (x : Fin d → ℝ) :
    SampledEnergy (GraphMatrix d) p α kept x =
      WeightedEnergy p (SampleWeight d p α kept) (GroundPotential x) := by
  classical
  unfold SampledEnergy WeightedEnergy
  apply Fintype.sum_equiv (edgeIndex d)
    (fun i => if kept i = true then
      Real.rpow |RowValue (GraphMatrix d) i x| p /
        RetentionProbability (GraphMatrix d) p α i else 0)
    (fun e => SampleWeight d p α kept e * EdgePower p (GroundPotential x) e)
  intro i
  rw [graphMatrix_rowValue]
  by_cases h : kept i = true
  · simp [SampleWeight, h, EdgePower, div_eq_mul_inv, mul_comm]
  · simp [SampleWeight, h]

theorem groundPotential_shift {d : ℕ} (z : Fin (d + 1) → ℝ)
    (a : Fin (d + 1)) :
    GroundPotential (fun j => z (Fin.succ j) - z 0) a = z a - z 0 := by
  induction a using Fin.cases with
  | zero => simp [GroundPotential]
  | succ j => simp [GroundPotential]

theorem edgePower_ground_shift {d : ℕ} (p : ℝ)
    (z : Fin (d + 1) → ℝ) (e : Edge (d + 1)) :
    EdgePower p (GroundPotential (fun j => z (Fin.succ j) - z 0)) e =
      EdgePower p z e := by
  have hdiff :
      GroundPotential (fun j => z (Fin.succ j) - z 0) e.val.1 -
        GroundPotential (fun j => z (Fin.succ j) - z 0) e.val.2 =
          z e.val.1 - z e.val.2 := by
    rw [groundPotential_shift, groundPotential_shift]
    ring
  simp only [EdgePower, hdiff]

theorem completeEnergy_ground_shift {d : ℕ} (p : ℝ)
    (z : Fin (d + 1) → ℝ) :
    CompleteEnergy p (GroundPotential (fun j => z (Fin.succ j) - z 0)) =
      CompleteEnergy p z := by
  unfold CompleteEnergy
  apply Finset.sum_congr rfl
  intro e _
  exact edgePower_ground_shift p z e

theorem weightedEnergy_ground_shift {d : ℕ} (p : ℝ)
    (w : Edge (d + 1) → ℝ) (z : Fin (d + 1) → ℝ) :
    WeightedEnergy p w (GroundPotential (fun j => z (Fin.succ j) - z 0)) =
      WeightedEnergy p w z := by
  unfold WeightedEnergy
  apply Finset.sum_congr rfl
  intro e _
  rw [edgePower_ground_shift]

/-- The matrix's all-vector event gives approximation of every graph
potential, including support-dependent potentials chosen after sampling. -/
theorem embedding_to_weighted (d : ℕ) (p α ε : ℝ)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (h : Embedding (GraphMatrix d) p α ε kept) :
    ∀ z : Fin (d + 1) → ℝ,
      (1 - ε) * CompleteEnergy p z ≤
        WeightedEnergy p (SampleWeight d p α kept) z ∧
      WeightedEnergy p (SampleWeight d p α kept) z ≤
        (1 + ε) * CompleteEnergy p z := by
  intro z
  let x : Fin d → ℝ := fun j => z (Fin.succ j) - z 0
  have hx := h x
  rw [graphMatrix_inputEnergy, sampledEnergy_eq_weighted] at hx
  rw [completeEnergy_ground_shift, weightedEnergy_ground_shift] at hx
  exact hx

#print axioms sampleWeight_nonneg
#print axioms sampledEnergy_eq_weighted
#print axioms embedding_to_weighted

end NLA.Proofs.RA06
