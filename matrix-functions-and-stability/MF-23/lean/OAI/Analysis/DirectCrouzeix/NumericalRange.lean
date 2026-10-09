import OAI.Analysis.DirectCrouzeix.Model

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

theorem numericalRange_eq_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRange A =
      (fun u : EuclideanSpace ℂ (Fin n) => inner ℂ u
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)) '' Metric.sphere 0 1 := by
  ext z
  simp [numericalRange, Set.mem_image]

theorem isCompact_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    IsCompact (numericalRange A) := by
  rw [numericalRange_eq_image]
  exact (isCompact_sphere (0 : EuclideanSpace ℂ (Fin n)) 1).image
    (continuous_id.inner (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).continuous)

theorem numericalRange_nonempty {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : (numericalRange A).Nonempty := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  rw [numericalRange_eq_image]
  exact (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _

theorem norm_le_of_mem_numericalRange {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by
  obtain ⟨u, hu, rfl⟩ := hz
  calc
    ‖inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)‖
        ≤ ‖u‖ * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖A‖ := by rw [hu, Matrix.l2_opNorm_toEuclideanCLM]; ring

theorem continuous_polynomialValue {m d : ℕ}
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) : Continuous (polynomialValue B) := by
  unfold polynomialValue
  exact continuous_finsetSum _ (fun k _ => (continuous_id.pow _).smul continuous_const)

theorem rangeMaximum_attained {n m d : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ) :
    ∃ z ∈ numericalRange A, ‖polynomialValue B z‖ = rangeMaximum A B := by
  have hc := (isCompact_numericalRange A).image (continuous_polynomialValue B).norm
  have hne := (numericalRange_nonempty hn A).image (fun z => ‖polynomialValue B z‖)
  obtain ⟨z, hz, he⟩ := hc.sSup_mem hne
  exact ⟨z, hz, he⟩

theorem norm_polynomialValue_le_rangeMaximum {n m d : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Fin (d + 1) → Matrix (Fin m) (Fin m) ℂ)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖polynomialValue B z‖ ≤ rangeMaximum A B := by
  apply le_csSup
  · exact (isCompact_numericalRange A).bddAbove_image
      (continuous_polynomialValue B).norm.continuousOn
  · exact ⟨z, hz, rfl⟩

open scoped MatrixOrder ComplexOrder

end DirectCrouzeix

end

end OAI
