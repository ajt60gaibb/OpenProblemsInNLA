import NLA.Proofs.RA06.GraphSensitivity

/-! Grounded complete-graph incidence matrices for the exact RA-06 row model. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

def GroundPotential {d : ℕ} (x : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons 0 x

noncomputable def edgeIndex (d : ℕ) :
    Fin (Fintype.card (Edge (d + 1))) ≃ Edge (d + 1) :=
  (Fintype.equivFin (Edge (d + 1))).symm

noncomputable def GraphMatrix (d : ℕ) :
    Matrix (Fin (Fintype.card (Edge (d + 1)))) (Fin d) ℝ :=
  fun i j =>
    (if (edgeIndex d i).val.1 = Fin.succ j then 1 else 0) -
      (if (edgeIndex d i).val.2 = Fin.succ j then 1 else 0)

private theorem basis_sum_ground {d : ℕ} (a : Fin (d + 1))
    (x : Fin d → ℝ) :
    (∑ j : Fin d, (if a = Fin.succ j then (1 : ℝ) else 0) * x j) =
      GroundPotential x a := by
  induction a using Fin.cases with
  | zero => simp [GroundPotential, eq_comm]
  | succ k => simp [GroundPotential]

theorem graphMatrix_rowValue (d : ℕ)
    (i : Fin (Fintype.card (Edge (d + 1)))) (x : Fin d → ℝ) :
    RowValue (GraphMatrix d) i x =
      GroundPotential x (edgeIndex d i).val.1 -
        GroundPotential x (edgeIndex d i).val.2 := by
  simp only [RowValue, GraphMatrix, sub_mul, Finset.sum_sub_distrib]
  rw [basis_sum_ground, basis_sum_ground]

/-- The edges from the grounded vertex to each free vertex show that the
incidence matrix has full column rank. -/
theorem graphMatrix_fullColumnRank (d : ℕ) :
    FullColumnRank (GraphMatrix d) := by
  intro x hx j
  let e : Edge (d + 1) := ⟨(0, Fin.succ j), by simp⟩
  let i : Fin (Fintype.card (Edge (d + 1))) := (edgeIndex d).symm e
  have hrow := hx i
  rw [graphMatrix_rowValue] at hrow
  have hi : edgeIndex d i = e := (edgeIndex d).apply_symm_apply e
  rw [hi] at hrow
  simpa [e, GroundPotential] using hrow.symm

/-- The exact matrix input energy is the grounded complete-graph energy. -/
theorem graphMatrix_inputEnergy (d : ℕ) (p : ℝ) (x : Fin d → ℝ) :
    InputEnergy (GraphMatrix d) p x =
      CompleteEnergy p (GroundPotential x) := by
  unfold InputEnergy CompleteEnergy
  apply Fintype.sum_equiv (edgeIndex d)
    (fun i => Real.rpow |RowValue (GraphMatrix d) i x| p)
    (fun e => EdgePower p (GroundPotential x) e)
  intro i
  rw [graphMatrix_rowValue]
  rfl

/-- Each ordinary sensitivity of the grounded incidence matrix is bounded
by the two-star graph estimate, with the original `sSup` definition. -/
theorem graphMatrix_sensitivity_le (d : ℕ) (hd : 0 < d)
    (p : ℝ) (hp : 1 ≤ p)
    (i : Fin (Fintype.card (Edge (d + 1)))) :
    Sensitivity (GraphMatrix d) p i ≤
      (2 * Real.rpow 2 (p - 1)) / ((d + 1 : ℕ) : ℝ) := by
  have hv : 0 < (((d + 1 : ℕ) : ℝ)) := by positivity
  apply sensitivity_le_of_rowEnergy_bound (GraphMatrix d) p
    ((2 * Real.rpow 2 (p - 1)) / ((d + 1 : ℕ) : ℝ))
    (graphMatrix_fullColumnRank d) hd i
  intro x
  have hpair := pairPower_le_complete p hp (GroundPotential x)
    (edgeIndex d i).val.1 (edgeIndex d i).val.2
  rw [← graphMatrix_inputEnergy d p x, ← graphMatrix_rowValue d i x] at hpair
  calc
    Real.rpow |RowValue (GraphMatrix d) i x| p ≤
        ((2 * Real.rpow 2 (p - 1)) * InputEnergy (GraphMatrix d) p x) /
          ((d + 1 : ℕ) : ℝ) :=
        (le_div_iff₀ hv).mpr (by simpa only [mul_comm] using hpair)
    _ = ((2 * Real.rpow 2 (p - 1)) / ((d + 1 : ℕ) : ℝ)) *
        InputEnergy (GraphMatrix d) p x := by ring

/-- A convenient, safe total-sensitivity bound; it uses only that the edge
type embeds into the ordered pairs of vertices. -/
theorem graphMatrix_totalSensitivity_bound (d : ℕ) (hd : 0 < d)
    (p : ℝ) (hp : 1 ≤ p) :
    TotalSensitivity (GraphMatrix d) p + (d : ℝ) ≤
      (2 * Real.rpow 2 (p - 1) + 1) * ((d + 1 : ℕ) : ℝ) := by
  let v : ℝ := ((d + 1 : ℕ) : ℝ)
  let B : ℝ := 2 * Real.rpow 2 (p - 1)
  have hv : 0 < v := by dsimp [v]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcardNat : Fintype.card (Edge (d + 1)) ≤ (d + 1) * (d + 1) := by
    simpa only [Edge, Fintype.card_prod, Fintype.card_fin] using
      (Fintype.card_subtype_le
        (fun ij : Fin (d + 1) × Fin (d + 1) => ij.1 < ij.2))
  have hcard : ((Fintype.card (Edge (d + 1)) : ℕ) : ℝ) ≤ v * v := by
    simpa only [v, Nat.cast_mul] using
      (by exact_mod_cast hcardNat :
        ((Fintype.card (Edge (d + 1)) : ℕ) : ℝ) ≤
          (((d + 1) * (d + 1) : ℕ) : ℝ))
  have hscore : 0 ≤ B / v := div_nonneg hB hv.le
  have hsum : TotalSensitivity (GraphMatrix d) p ≤
      ((Fintype.card (Edge (d + 1)) : ℕ) : ℝ) * (B / v) := by
    unfold TotalSensitivity
    calc
      (∑ i : Fin (Fintype.card (Edge (d + 1))),
        Sensitivity (GraphMatrix d) p i) ≤
          ∑ _i : Fin (Fintype.card (Edge (d + 1))), B / v := by
        apply Finset.sum_le_sum
        intro i _
        exact graphMatrix_sensitivity_le d hd p hp i
      _ = ((Fintype.card (Edge (d + 1)) : ℕ) : ℝ) * (B / v) := by simp
  have htotal : TotalSensitivity (GraphMatrix d) p ≤ B * v := by
    calc
      TotalSensitivity (GraphMatrix d) p ≤
          ((Fintype.card (Edge (d + 1)) : ℕ) : ℝ) * (B / v) := hsum
      _ ≤ (v * v) * (B / v) := mul_le_mul_of_nonneg_right hcard hscore
      _ = B * v := by field_simp [ne_of_gt hv]
  have hdle : (d : ℝ) ≤ v := by dsimp [v]; norm_cast; omega
  calc
    TotalSensitivity (GraphMatrix d) p + (d : ℝ) ≤ B * v + v :=
      add_le_add htotal hdle
    _ = (B + 1) * v := by ring

#print axioms graphMatrix_rowValue
#print axioms graphMatrix_fullColumnRank
#print axioms graphMatrix_inputEnergy
#print axioms graphMatrix_sensitivity_le
#print axioms graphMatrix_totalSensitivity_bound

end NLA.Proofs.RA06
