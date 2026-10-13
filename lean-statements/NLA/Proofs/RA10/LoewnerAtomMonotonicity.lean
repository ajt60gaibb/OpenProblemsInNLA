import NLA.Proofs.RA10.OperatorMonotonePositiveApproximation

/-! The harmonic atoms belong to the frozen admissible class. The inverse-order
argument is real and finite dimensional; no complex C*-algebra instance or
general representation theorem is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10

namespace NLA.Proofs.RA10

/-- Completion of a matrix square proves order reversal of inversion. -/
theorem matrix_inverse_sub_posSemidef {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : (A - B).PosSemidef)
    (huA : IsUnit A) (huB : IsUnit B) : (B⁻¹ - A⁻¹).PosSemidef := by
  have hAiA := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp huA)
  have hBiB := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det _).mp huB)
  have hBBi := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det _).mp huB)
  have hform : B⁻¹ - A⁻¹ =
      A⁻¹ * (A - B) * A⁻¹ + (B⁻¹ - A⁻¹) * B * (B⁻¹ - A⁻¹) := by
    simp only [mul_sub, sub_mul]
    simp only [hAiA, hBiB, one_mul, mul_assoc, hBBi, mul_one]
    abel
  rw [hform]
  have hleft := hAB.mul_mul_conjTranspose_same A⁻¹
  have hright := hB.mul_mul_conjTranspose_same (B⁻¹ - A⁻¹)
  simpa only [hA.1.inv.eq, (hB.1.inv.sub hA.1.inv).eq] using hleft.add hright

theorem operatorMonotoneOnNonnegative_ridge {s : ℝ} (hs : 0 < s) :
    OperatorMonotoneOnNonnegative (ridgeAtom s) := by
  intro d hd H G a b QH QG hH hG hHG
  rw [ridgeFunctionMatrix_sub hs hG hH]
  apply (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr
  apply Matrix.PosSemidef.smul _ hs.le
  have hHpsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hH)
  have hGpsd := (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (orderedPSDSpectralDecomposition_positiveSemidefinite hG)
  apply matrix_inverse_sub_posSemidef
    ((Matrix.PosSemidef.one.smul hs.le).add hHpsd)
    ((Matrix.PosSemidef.one.smul hs.le).add hGpsd)
  · simpa only [add_sub_add_left_eq_sub] using
      (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp hHG
  · exact spectralShift_isUnit hs hH
  · exact spectralShift_isUnit hs hG

theorem operatorMonotoneOnNonnegative_const (c : ℝ) :
    OperatorMonotoneOnNonnegative (fun _ => c) := by
  intro d hd H G a b QH QG hH hG hHG
  rw [functionMatrix_const c a QH hH.2.2.1, functionMatrix_const c b QG hG.2.2.1, sub_self]
  exact (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr Matrix.PosSemidef.zero

theorem operatorMonotoneOnNonnegative_id : OperatorMonotoneOnNonnegative (fun x => x) := by
  intro d hd H G a b QH QG hH hG hHG
  change PositiveSemidefinite (SpectralMatrix a QH - SpectralMatrix b QG)
  rwa [← hH.2.2.2, ← hG.2.2.2]

theorem loewnerAtom_operatorMonotone (t : LoewnerParameter) :
    OperatorMonotoneOnNonnegative (loewnerAtom t) := by
  by_cases hzero : (t : ℝ) = 0
  · have heq : loewnerAtom t = fun _ => 1 := by funext x; simp [loewnerAtom, hzero]
    rw [heq]
    exact operatorMonotoneOnNonnegative_const 1
  by_cases hone : (t : ℝ) = 1
  · have heq : loewnerAtom t = fun x => x := by funext x; simp [loewnerAtom, hone]
    rw [heq]
    exact operatorMonotoneOnNonnegative_id
  have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm hzero)
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 hone
  have heq : loewnerAtom t = fun x => (1 - (t : ℝ))⁻¹ * ridgeAtom ((t : ℝ) / (1 - t)) x :=
    funext fun x => loewnerAtom_eq_scaled_ridge t ht0 ht1 x
  rw [heq]
  exact operatorMonotoneOnNonnegative_smul
    (operatorMonotoneOnNonnegative_ridge (div_pos ht0 (sub_pos.mpr ht1)))
    (inv_nonneg.mpr (sub_nonneg.mpr t.property.2))

theorem loewnerAtom_admissible (t : LoewnerParameter) : AdmissibleFunction (loewnerAtom t) :=
  ⟨loewnerAtom_continuousOn t, fun _ hx => loewnerAtom_nonneg t hx,
    loewnerAtom_operatorMonotone t⟩

theorem loewnerProfile_mem_compactClass (t : LoewnerParameter) :
    loewnerProfile t ∈ normalizedAdmissibleCompactClass :=
  normalizedAdmissible_mem_compactClass (loewnerAtom_admissible t) (loewnerAtom_at_one t)

#assert_trust kernel matrix_inverse_sub_posSemidef
#assert_trust kernel operatorMonotoneOnNonnegative_ridge
#assert_trust kernel operatorMonotoneOnNonnegative_const
#assert_trust kernel operatorMonotoneOnNonnegative_id
#assert_trust kernel loewnerAtom_operatorMonotone
#assert_trust kernel loewnerAtom_admissible
#assert_trust kernel loewnerProfile_mem_compactClass
#print axioms loewnerAtom_admissible

end NLA.Proofs.RA10
