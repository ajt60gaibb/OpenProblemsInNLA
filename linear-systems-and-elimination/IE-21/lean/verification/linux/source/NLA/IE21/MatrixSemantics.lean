import NLA.IE21.Definitions
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology
namespace NLA.IE21

theorem unit_sphere_nonempty (n : ℕ) (hn : 1 ≤ n) :
    (Metric.sphere (0 : Space n) 1).Nonempty := by
  let : NeZero n := ⟨by omega⟩
  exact NormedSpace.sphere_nonempty.mpr zero_le_one

theorem matrixMap_apply {m n : ℕ} (A : Mat m n) (x : Space n) (i : Fin m) :
    matrixMap A x i = ∑ j, A i j * x j := rfl

theorem retainedNorm_sq {m n : ℕ} (A : Mat m n) (S : Finset (Fin m)) (x : Space n) :
    retainedNorm A S x ^ 2 = ∑ i ∈ S, (matrixMap A x i) ^ 2 := by
  classical
  rw [retainedNorm, EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_coe_sort S (fun i => (matrixMap A x i) ^ 2)

theorem matrix_semantics {m n : ℕ} (A : Mat m n) (hn : 1 ≤ n) :
    (∀ (x : Space n) (i : Fin m), matrixMap A x i = ∑ j, A i j * x j) ∧
    (∃ x : Space n, ‖x‖ = 1 ∧ ‖matrixMap A x‖ = operatorNorm A) ∧
    (∀ x : Space n, ‖matrixMap A x‖ ≤ operatorNorm A * ‖x‖) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      retainedNorm A S x ^ 2 = ∑ i ∈ S, (matrixMap A x i) ^ 2) := by
  refine ⟨matrixMap_apply A, ?_, (matrixMap A).le_opNorm, retainedNorm_sq A⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : Space n) 1).exists_isMaxOn
    (unit_sphere_nonempty n hn) (matrixMap A).continuous.norm.continuousOn
  have hx' : ‖x‖ = 1 := by simpa using hx
  refine ⟨x, hx', le_antisymm ?_ ?_⟩
  · simpa [operatorNorm, hx'] using (matrixMap A).le_opNorm x
  · exact ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy =>
      hmax (by simpa using hy)

theorem retainedRows_le (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (m : ℕ) :
    retainedRows θ m ≤ m := by
  apply Nat.floor_le_of_le
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem exists_retained_selection (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (m : ℕ) :
    ∃ S : Finset (Fin m), S.card = retainedRows θ m := by
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m)))
    (n := retainedRows θ m) (by simpa using retainedRows_le θ hθ m)
  exact ⟨S, hS⟩

theorem continuous_matrixMap (m n : ℕ) : Continuous (matrixMap (m := m) (n := n)) := by
  exact ((Matrix.toEuclideanLin (m := Fin m) (n := Fin n) (𝕜 := ℝ)).trans
    LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional

theorem continuous_retainedNorm {m n : ℕ} (S : Finset (Fin m)) :
    Continuous (fun p : Mat m n × Space n => retainedNorm p.1 S p.2) := by
  have heq : (fun p : Mat m n × Space n => retainedNorm p.1 S p.2) =
      fun p => Real.sqrt (∑ i ∈ S, (∑ j, p.1 i j * p.2 j) ^ 2) := by
    funext p
    calc
      retainedNorm p.1 S p.2 = Real.sqrt (retainedNorm p.1 S p.2 ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
      _ = _ := by simp only [retainedNorm_sq, matrixMap_apply]
  rw [heq]
  fun_prop

/- The finite selection index is given the discrete topology only inside this module. -/
local instance (m : ℕ) : TopologicalSpace (Finset (Fin m)) := ⊥
local instance (m : ℕ) : DiscreteTopology (Finset (Fin m)) := ⟨rfl⟩

private def minimizationDomain (θ : ℝ) (m n : ℕ) : Set (Finset (Fin m) × Space n) :=
  {S | S.card = retainedRows θ m} ×ˢ Metric.sphere (0 : Space n) 1

private theorem compact_minimizationDomain (θ : ℝ) (m n : ℕ) :
    IsCompact (minimizationDomain θ m n) :=
  (Set.toFinite _).isCompact.prod (isCompact_sphere _ _)

private theorem nonempty_minimizationDomain (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hn : 1 ≤ n) : (minimizationDomain θ m n).Nonempty := by
  obtain ⟨S, hS⟩ := exists_retained_selection θ hθ m
  obtain ⟨x, hx⟩ := unit_sphere_nonempty n hn
  exact ⟨(S, x), hS, hx⟩

private theorem continuous_retainedNorm_all (m n : ℕ) :
    Continuous (fun p : Mat m n × (Finset (Fin m) × Space n) =>
      retainedNorm p.1 p.2.1 p.2.2) := by
  have hc : Continuous (fun p : Finset (Fin m) × (Mat m n × Space n) =>
      retainedNorm p.2.1 p.1 p.2.2) :=
    continuous_prod_of_discrete_left.mpr fun S => continuous_retainedNorm S
  have hp : Continuous (fun p : Mat m n × (Finset (Fin m) × Space n) =>
      (p.2.1, (p.1, p.2.2))) := by fun_prop
  simpa only [Function.comp_def] using hc.comp hp

private theorem deletion_eq_inf_image {m n : ℕ} (θ : ℝ) (A : Mat m n) :
    deletionSingular θ A = sInf ((fun p : Finset (Fin m) × Space n =>
      retainedNorm A p.1 p.2) '' minimizationDomain θ m n) := by
  unfold deletionSingular
  congr 1
  ext z
  constructor
  · rintro ⟨S, x, hS, hx, rfl⟩
    exact ⟨(S, x), ⟨hS, by simpa using hx⟩, rfl⟩
  · rintro ⟨⟨S, x⟩, ⟨hS, hx⟩, rfl⟩
    exact ⟨S, x, hS, by simpa using hx, rfl⟩

theorem continuous_deletionSingular (m n : ℕ) (θ : ℝ) :
    Continuous (deletionSingular (m := m) (n := n) θ) := by
  have heq : deletionSingular (m := m) (n := n) θ =
      fun A => sInf ((fun p : Finset (Fin m) × Space n => retainedNorm A p.1 p.2) ''
        minimizationDomain θ m n) := funext (deletion_eq_inf_image θ)
  rw [heq]
  exact (compact_minimizationDomain θ m n).continuous_sInf (continuous_retainedNorm_all m n)

theorem deletion_minimum {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n) :
    0 ≤ deletionSingular θ A ∧
    (∃ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m ∧ ‖x‖ = 1 ∧
      deletionSingular θ A = retainedNorm A S x) ∧
    (∀ (S : Finset (Fin m)) (x : Space n),
      S.card = retainedRows θ m → ‖x‖ = 1 →
      deletionSingular θ A ≤ retainedNorm A S x) := by
  have hc := (compact_minimizationDomain θ m n).image
    ((continuous_retainedNorm_all m n).comp
      ((continuous_const (y := A)).prodMk continuous_id))
  have hne := (nonempty_minimizationDomain θ hθ m n hn).image
    (fun p : Finset (Fin m) × Space n => retainedNorm A p.1 p.2)
  obtain ⟨⟨S, x⟩, ⟨hS, hx⟩, heq⟩ := hc.sInf_mem hne
  have hval : deletionSingular θ A = retainedNorm A S x :=
    (deletion_eq_inf_image θ A).trans heq.symm
  refine ⟨hval ▸ norm_nonneg _, ⟨S, x, hS, by simpa using hx, hval⟩, ?_⟩
  intro T y hT hy
  rw [deletion_eq_inf_image]
  exact csInf_le hc.bddBelow ⟨(T, y), ⟨hT, by simpa using hy⟩, rfl⟩

theorem deletion_zero_cases {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (hn : 1 ≤ n) :
    (retainedRows θ m = 0 → deletionSingular θ A = 0) ∧
    ((∃ S : Finset (Fin m), S.card = retainedRows θ m ∧
      ∃ x : Space n, x ≠ 0 ∧ Matrix.toEuclideanLin (retainedMatrix A S) x = 0) →
      deletionSingular θ A = 0) := by
  obtain ⟨h0, _, hle⟩ := deletion_minimum θ hθ A hn
  constructor
  · intro hk
    obtain ⟨x, hx⟩ := unit_sphere_nonempty n hn
    apply le_antisymm _ h0
    have h := hle ∅ x (by simpa using hk.symm) (by simpa using hx)
    have hz : retainedNorm A ∅ x = 0 := by
      have := retainedNorm_sq A ∅ x
      simp only [Finset.sum_empty] at this
      nlinarith [norm_nonneg (Matrix.toEuclideanLin (retainedMatrix A ∅) x)]
    simpa [hz] using h
  · rintro ⟨S, hS, x, hx, hker⟩
    apply le_antisymm _ h0
    have h := hle S (‖x‖⁻¹ • x) hS (norm_smul_inv_norm hx)
    simpa [retainedNorm, map_smul, hker] using h

end NLA.IE21
