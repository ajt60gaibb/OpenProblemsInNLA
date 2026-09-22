import NLA.IE22.Definitions

/-!
The literal canonical supremum is finite and attained on the compact set of
unit-row matrices. Original mathematical proof: Matthew J. Colbrook.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21

theorem continuous_normalizedSingular (θ : ℝ) (m n : ℕ) :
    Continuous (normalizedSingular (m := m) (n := n) θ) :=
  continuous_const.mul (continuous_deletionSingular m n θ)

theorem isCompact_unitRows (m n : ℕ) : IsCompact {A : Mat m n | UnitRows A} := by
  have hc := isCompact_pi_infinite (fun _ : Fin m => isCompact_sphere (0 : Space n) 1)
  have hr : Continuous (@rowsMatrix m n) := by
    unfold rowsMatrix
    fun_prop
  have heq : rowsMatrix '' {u : Fin m → Space n | ∀ i, u i ∈ Metric.sphere 0 1} =
      {A : Mat m n | UnitRows A} := by
    ext A
    constructor
    · rintro ⟨u, hu, rfl⟩ i
      simpa using hu i
    · intro hA
      exact ⟨matrixRow A, fun i => by simpa using hA i, rowsMatrix_matrixRow A⟩
  rw [← heq]
  exact hc.image hr

theorem unitRows_nonempty (m n : ℕ) (hn : 1 ≤ n) :
    ({A : Mat m n | UnitRows A} : Set (Mat m n)).Nonempty := by
  obtain ⟨x, hx⟩ := unit_sphere_nonempty n hn
  exact ⟨rowsMatrix (fun _ => x), fun _ => by simpa using hx⟩

theorem unitRowValues_eq_image (θ : ℝ) (m n : ℕ) :
    unitRowValues θ m n = normalizedSingular θ '' {A : Mat m n | UnitRows A} := by
  ext z
  constructor
  · rintro ⟨A, hA, hz⟩
    exact ⟨A, hA, hz.symm⟩
  · rintro ⟨A, hA, hz⟩
    exact ⟨A, hA, hz.symm⟩

theorem normalizedSingular_nonneg_sq (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    {m n : ℕ} (hn : 1 ≤ n) (A : Mat m n) :
    0 ≤ normalizedSingular θ A ∧ normalizedSingular θ A ^ 2 = normalizedDeletion θ A := by
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (deletion_minimum θ hθ A hn).1
  · unfold normalizedSingular normalizedDeletion
    rw [mul_pow, Real.sq_sqrt (div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m))]

theorem normalizedSingular_le_sqrt_dim (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (A : Mat m n) (hA : UnitRows A) :
    normalizedSingular θ A ≤ Real.sqrt n := by
  obtain ⟨S, x, hS, hx, heq⟩ := (deletion_minimum θ hθ A hn).2.1
  have hsum : retainedNorm A S x ^ 2 ≤ (m : ℝ) := by
    rw [retainedNorm_sq]
    calc
      ∑ i ∈ S, (matrixMap A x i) ^ 2 ≤ ∑ _i ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hb : |matrixMap A x i| ≤ 1 := by
          rw [matrixMap_eq_inner_row]
          simpa [hA i, hx] using abs_real_inner_le_norm (matrixRow A i) x
        nlinarith [sq_abs (matrixMap A x i), abs_nonneg (matrixMap A x i)]
      _ = (S.card : ℝ) := by simp
      _ ≤ m := by exact_mod_cast (hS ▸ retainedRows_le θ hθ m)
  have hstat := normalizedSingular_nonneg_sq θ hθ hn A
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hsq : normalizedSingular θ A ^ 2 ≤ (n : ℝ) := by
    rw [hstat.2, normalizedDeletion, heq]
    calc
      (n : ℝ) / m * retainedNorm A S x ^ 2 ≤ (n : ℝ) / m * m :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (Nat.cast_nonneg _) hm0.le)
      _ = n := div_mul_cancel₀ _ (ne_of_gt hm0)
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg n), Real.sqrt_nonneg (n : ℝ)]

theorem supremum_semantics (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (unitRowValues θ m n).Nonempty ∧ BddAbove (unitRowValues θ m n) ∧
    (∃ A : Mat m n, UnitRows A ∧ extremalValue θ m n = normalizedSingular θ A) ∧
    (∀ A : Mat m n, UnitRows A → normalizedSingular θ A ≤ extremalValue θ m n) ∧
    0 ≤ extremalValue θ m n ∧ extremalValue θ m n ≤ Real.sqrt n ∧
    ∀ A : Mat m n, 0 ≤ normalizedSingular θ A ∧
      normalizedSingular θ A ^ 2 = normalizedDeletion θ A := by
  have hc : IsCompact (unitRowValues θ m n) := by
    rw [unitRowValues_eq_image]
    exact (isCompact_unitRows m n).image (continuous_normalizedSingular θ m n)
  have hne : (unitRowValues θ m n).Nonempty := by
    rw [unitRowValues_eq_image]
    exact (unitRows_nonempty m n hn).image _
  obtain ⟨A, hA, heq⟩ := hc.sSup_mem hne
  refine ⟨hne, hc.bddAbove, ⟨A, hA, heq⟩, ?_, ?_, ?_,
    fun B => normalizedSingular_nonneg_sq θ hθ hn B⟩
  · intro B hB
    exact le_csSup hc.bddAbove ⟨B, hB, rfl⟩
  · rw [extremalValue, heq]
    exact (normalizedSingular_nonneg_sq θ hθ hn A).1
  · rw [extremalValue, heq]
    exact normalizedSingular_le_sqrt_dim θ hθ hm hn A hA

theorem constant_semantics (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 ≤ sharpConstant θ ∧ sharpConstant θ ^ 2 = gaussianTrim θ ∧
    sharpConstant θ = Real.sqrt ((1 / Real.sqrt (2 * Real.pi)) *
      ∫ g in Icc (-gaussianCutoff θ) (gaussianCutoff θ), g ^ 2 * Real.exp (-(g ^ 2) / 2)) := by
  exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (gaussian_constant θ hθ).2.2.2.2.1, rfl⟩

end NLA.IE22
