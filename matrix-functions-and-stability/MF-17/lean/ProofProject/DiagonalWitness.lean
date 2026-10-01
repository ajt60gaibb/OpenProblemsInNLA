import ProofProject.DiagonalPeak
import ProofProject.BoundedGenerator

/-! Admissible finite-dimensional witnesses from bounded diagonal semigroups. -/

noncomputable section

namespace ProofProject

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {N : ℕ}

lemma diagonalPeak_forward (b : Module.Basis (Fin N) ℂ H) (ω : ℝ)
    (y : Fin N → ℕ) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • diagonalPeakGenerator b ω y) =
      (Real.exp (-s) : ℂ) • basisDiagonal b
        (fun i => Complex.exp (((s / ω : ℝ) : ℂ) * scalarLambda (y i))) := by
  rw [diagonalPeakGenerator, ← basisDiagonal_smul, basisDiagonal_exp,
    ← basisDiagonal_smul]
  congr 1
  funext i
  change Complex.exp ((s : ℂ) * peakEigenvalue ω (y i)) = _
  have he : (s : ℂ) * peakEigenvalue ω (y i) =
      ((-s : ℝ) : ℂ) + ((s / ω : ℝ) : ℂ) * scalarLambda (y i) := by
    simp only [peakEigenvalue, Complex.ofReal_neg, Complex.ofReal_div]
    ring
  rw [he, Complex.exp_add, ← Complex.ofReal_exp]
  rfl

/-- Shifting and scaling inserts the exact decay rate without changing M. -/
theorem diagonalPeak_forward_bound (b : Module.Basis (Fin N) ℂ H) {M ω : ℝ}
    (hω : 0 < ω) (y : Fin N → ℕ)
    (hforward : ∀ s : ℝ, 0 ≤ s →
      ‖basisDiagonal b (fun i => Complex.exp ((s : ℂ) * scalarLambda (y i)))‖ ≤ M)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖NormedSpace.exp ((s : ℂ) • diagonalPeakGenerator b ω y)‖ ≤ M * Real.exp (-s) := by
  rw [diagonalPeak_forward b ω y s, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (hforward (s / ω) (div_nonneg hs hω.le))
    (Real.exp_pos _).le).trans_eq (mul_comm _ _)

/-- A diagonal model gives a witness with its explicit sign-approximation error.
The inverse is certified against the full strong generator graph. -/
theorem diagonalPeak_finiteWitness (b : Module.Basis (Fin N) ℂ H) {M ω K : ℝ}
    (hω : 0 < ω) (hK : 0 ≤ K) (y : Fin N → ℕ)
    (hcoord : ∀ i, ‖basisCoordinate b i‖ ≤ K)
    (hforward : ∀ s : ℝ, 0 ≤ s →
      ‖basisDiagonal b (fun i => Complex.exp ((s : ℂ) * scalarLambda (y i)))‖ ≤ M) :
    HasFiniteWitness.{u} M (Real.pi / ω)
      (Real.exp (-Real.pi) * ‖basisDiagonal b (fun i => (-1 : ℂ) ^ y i)‖ -
        K * (Real.pi * ω) * ∑ i, (1 + (y i : ℝ) ^ 2)) := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  let A := diagonalPeakGenerator b ω y
  let B := diagonalPeakInverse b ω y
  have hb := diagonalPeak_forward_bound b hω y hforward
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
    boundedGeneratorSemigroup M A hb, B, ?_, ?_⟩
  · exact boundedGeneratorSemigroup_isGeneratorInverse M A B hb
      (diagonalPeak_mul_inverse b hω y) (diagonalPeak_inverse_mul b hω y)
  · exact diagonalPeak_norm_lower b hω hK y hcoord

/-- An explicit scale makes the perturbation error at most one. -/
def peakScale (M : ℝ) (N : ℕ) (Y : ℝ) : ℝ :=
  (2 * Real.pi * M * N * (1 + Y ^ 2))⁻¹

lemma peakScale_pos {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) (Y : ℝ) :
    0 < peakScale M N Y := by
  unfold peakScale
  positivity

lemma peakScale_error_le_one {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N)
    (y : Fin N → ℕ) {Y : ℝ} (hY : ∀ i, (y i : ℝ) ≤ Y) :
    (2 * M) * (Real.pi * peakScale M N Y) * ∑ i, (1 + (y i : ℝ) ^ 2) ≤ 1 := by
  have hsum : ∑ i, (1 + (y i : ℝ) ^ 2) ≤ N * (1 + Y ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin N, (1 + Y ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact add_le_add_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (hY i) 2) 1
      _ = _ := by simp; ring
  have hpos := peakScale_pos hM hN Y
  calc
    _ ≤ (2 * M) * (Real.pi * peakScale M N Y) * (N * (1 + Y ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 1 := by
      unfold peakScale
      field_simp

lemma peakScale_time (M : ℝ) (N : ℕ) (Y : ℝ) :
    Real.pi / peakScale M N Y = 2 * Real.pi ^ 2 * M * N * (1 + Y ^ 2) := by
  simp only [peakScale, div_inv_eq_mul]
  ring

lemma HasFiniteWitness.mono_lower {M t a b : ℝ}
    (hw : HasFiniteWitness.{u} M t a) (hba : b ≤ a) : HasFiniteWitness.{u} M t b := by
  rcases hw with ⟨H, hnorm, hip, hcomplete, hfinite, T, B, hB, ha⟩
  exact ⟨H, hnorm, hip, hcomplete, hfinite, T, B, hB, hba.trans ha⟩

/-- At the explicit source time the additive loss is at most one. -/
theorem diagonalPeak_finiteWitness_unit_error (b : Module.Basis (Fin N) ℂ H)
    {M : ℝ} (hM : 0 < M) (hN : 0 < N) (y : Fin N → ℕ)
    {Y : ℝ} (hY : ∀ i, (y i : ℝ) ≤ Y)
    (hcoord : ∀ i, ‖basisCoordinate b i‖ ≤ 2 * M)
    (hforward : ∀ s : ℝ, 0 ≤ s →
      ‖basisDiagonal b (fun i => Complex.exp ((s : ℂ) * scalarLambda (y i)))‖ ≤ M) :
    HasFiniteWitness.{u} M (2 * Real.pi ^ 2 * M * N * (1 + Y ^ 2))
      (Real.exp (-Real.pi) * ‖basisDiagonal b (fun i => (-1 : ℂ) ^ y i)‖ - 1) := by
  have hw := diagonalPeak_finiteWitness b (peakScale_pos hM hN Y)
    (show 0 ≤ 2 * M by positivity) y hcoord hforward
  rw [peakScale_time] at hw
  exact hw.mono_lower (sub_le_sub_left (peakScale_error_le_one hM hN y hY) _)

end ProofProject
