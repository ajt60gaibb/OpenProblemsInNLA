import NLA.IE21.Definitions
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Tactic

/-! Exact Euclidean sphere nets for IE-21, using disjoint ambient balls.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
The volume argument generalizes Mathlib's Besicovitch.card_le_of_separated. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Set
open scoped ENNReal NNReal Function
namespace NLA.IE21

lemma sphere_separated_card (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (s : Finset (Space n))
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 / δ) ^ n := by
  let μ : Measure (Space n) := volume
  let r : ℝ := δ / 2
  let R : ℝ := 1 + δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hdim : Module.finrank ℝ (Space n) = n := by simp [Space]
  let A := ⋃ x ∈ s, ball x r
  have hdis : Set.Pairwise (s : Set (Space n)) (Disjoint on fun x => ball x r) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep x hx y hy hxy
    dsimp [r]
    linarith
  have hsub : A ⊆ ball (0 : Space n) R := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    dsimp [r, R]
    linarith [hs x hx]
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ n) * μ (ball 0 1) ≤
      ENNReal.ofReal (R ^ n) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ x ∈ s, ball x r from rfl, measure_biUnion_finset hdis
          (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hr, hdim]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball 0 R) := measure_mono hsub
      _ = _ := by rw [μ.addHaar_ball_of_pos _ hR, hdim]
  have hcancel : (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ n) ≤ ENNReal.ofReal (R ^ n) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvol
  have hreal : (s.card : ℝ) * r ^ n ≤ R ^ n := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hR.le _) hcancel
    simpa [ENNReal.toReal_mul, pow_nonneg hr.le] using h
  have hratio : R / r = 1 + 2 / δ := by dsimp [R, r]; field_simp; ring
  calc
    (s.card : ℝ) ≤ R ^ n / r ^ n := (le_div_iff₀ (pow_pos hr _)).mpr hreal
    _ = (1 + 2 / δ) ^ n := by rw [← div_pow, hratio]

theorem sphere_net (n : ℕ) (_hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset (Space n), (∀ x ∈ C, ‖x‖ = 1) ∧
      (C.card : ℝ) ≤ (1 + 2 / δ) ^ n ∧
      ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ δ := by
  classical
  let ε : ℝ≥0 := ⟨δ, hδ.le⟩
  let S : Set (Space n) := sphere 0 1
  obtain ⟨B, _hBsub, hBfin, hBcover⟩ := exists_finite_isCover_of_isCompact
    (ε := ε / 2) (ne_of_gt (div_pos (show (0 : ℝ≥0) < ε from hδ) (by norm_num))) (isCompact_sphere (0 : Space n) 1)
  have hpack : packingNumber ε S ≠ ⊤ := by
    have hbound := (packingNumber_two_mul_le_externalCoveringNumber (ε / 2) S).trans
      hBcover.externalCoveringNumber_le_encard
    have heq : 2 * (ε / 2) = ε := by ring
    rw [heq] at hbound
    exact ne_of_lt (lt_of_le_of_lt hbound hBfin.encard_lt_top)
  let C := maximalSeparatedSet ε S
  have hCfin : C.Finite := Set.encard_ne_top_iff.mp (by
    rw [show C = maximalSeparatedSet ε S from rfl, encard_maximalSeparatedSet hpack]
    exact hpack)
  have hCsub : C ⊆ S := maximalSeparatedSet_subset
  have hCsep : IsSeparated ε C := isSeparated_maximalSeparatedSet
  have hCcover : IsCover ε S C := isCover_maximalSeparatedSet hpack
  refine ⟨hCfin.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have := hCsub (hCfin.mem_toFinset.mp hx)
    simpa only [S, mem_sphere, dist_zero_right] using this
  · apply sphere_separated_card n δ hδ
    · intro x hx
      have := hCsub (hCfin.mem_toFinset.mp hx)
      exact (show ‖x‖ = 1 by simpa only [S, mem_sphere, dist_zero_right] using this).le
    · intro x hx y hy hxy
      have h := hCsep (hCfin.mem_toFinset.mp hx) (hCfin.mem_toFinset.mp hy) hxy
      have hnn : ε < nndist x y := ENNReal.coe_lt_coe.mp (by
        simpa only [edist_nndist] using h)
      have : δ < dist x y := hnn
      simpa only [dist_eq_norm] using this.le
  · intro x hx
    have hxS : x ∈ S := by simpa only [S, mem_sphere, dist_zero_right] using hx
    obtain ⟨y, hy, hd⟩ := hCcover hxS
    refine ⟨y, hCfin.mem_toFinset.mpr hy, ?_⟩
    have hnn : nndist x y ≤ ε := ENNReal.coe_le_coe.mp (by
      simpa only [Set.mem_ofPred_eq, edist_nndist] using hd)
    have : dist x y ≤ δ := hnn
    simpa only [dist_eq_norm] using this

#print axioms sphere_net
end NLA.IE21
