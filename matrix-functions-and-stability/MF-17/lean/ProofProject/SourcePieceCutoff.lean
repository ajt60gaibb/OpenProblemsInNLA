import ProofProject.SourcePieceScale
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Actual smooth cutoffs for the source pieces

The cutoff is constant on both exterior half-lines and globally nonincreasing.
Its differences have the source support and telescope exactly, including at
the endpoints. No amplitude estimates are assumed in these constructions.
-/

noncomputable section

namespace ProofProject

open Set Filter
open scoped ContDiff Topology

private theorem cutoff_nat_le_infty (k : ℕ) : (k : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

/-- The fixed source cutoff, equal to one below one and zero above two. -/
def sourcePieceChi (u : ℝ) : ℝ := Real.smoothTransition (2 - u)

theorem sourcePieceChi_contDiff : ContDiff ℝ ∞ sourcePieceChi :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem sourcePieceChi_antitone : Antitone sourcePieceChi := by
  intro u v huv
  exact Real.smoothTransition.monotone (by linarith)

theorem sourcePieceChi_nonneg (u : ℝ) : 0 ≤ sourcePieceChi u :=
  Real.smoothTransition.nonneg _

theorem sourcePieceChi_le_one (u : ℝ) : sourcePieceChi u ≤ 1 :=
  Real.smoothTransition.le_one _

theorem sourcePieceChi_eq_one {u : ℝ} (hu : u ≤ 1) : sourcePieceChi u = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem sourcePieceChi_eq_zero {u : ℝ} (hu : 2 ≤ u) : sourcePieceChi u = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem sourcePieceChi_deriv_eq_zero {u : ℝ} (hu : u < 1 ∨ 2 < u) :
    deriv sourcePieceChi u = 0 := by
  rcases hu with hu | hu
  · have heq : sourcePieceChi =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
      filter_upwards [gt_mem_nhds hu] with v hv
      exact sourcePieceChi_eq_one hv.le
    rw [heq.deriv_eq, deriv_const]
  · have heq : sourcePieceChi =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
      filter_upwards [lt_mem_nhds hu] with v hv
      exact sourcePieceChi_eq_zero hv.le
    rw [heq.deriv_eq, deriv_const]

theorem sourcePieceChi_deriv_tsupport :
    tsupport (deriv sourcePieceChi) ⊆ Icc (1 : ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  by_contra h
  have hout : u < 1 ∨ 2 < u := by
    simpa only [mem_Icc, not_and_or, not_le] using h
  exact hu (sourcePieceChi_deriv_eq_zero hout)

theorem sourcePieceChi_deriv_hasCompactSupport :
    HasCompactSupport (deriv sourcePieceChi) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure sourcePieceChi_deriv_tsupport

/-- The exact cutoff difference appearing in the source amplitude. -/
def sourcePieceCutoff (q : ℕ) (u : ℝ) : ℝ :=
  sourcePieceChi (u / (2 * sourcePieceScale (q + 1))) -
    sourcePieceChi (u / (2 * sourcePieceScale q))

theorem sourcePieceCutoff_contDiff (q : ℕ) : ContDiff ℝ ∞ (sourcePieceCutoff q) := by
  have hc := sourcePieceChi_contDiff
  unfold sourcePieceCutoff
  fun_prop

theorem sourcePieceCutoff_eq_zero_of_le (q : ℕ) {u : ℝ}
    (hu : u ≤ 2 * sourcePieceScale q) : sourcePieceCutoff q u = 0 := by
  have hp := sourcePieceScale_pos q
  have hp' := sourcePieceScale_pos (q + 1)
  have hm := sourcePieceScale_monotone (Nat.le_succ q)
  have hlow : u / (2 * sourcePieceScale q) ≤ 1 := (div_le_one (by positivity)).mpr hu
  have hhigh : u / (2 * sourcePieceScale (q + 1)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  simp only [sourcePieceCutoff, sourcePieceChi_eq_one hlow, sourcePieceChi_eq_one hhigh,
    sub_self]

theorem sourcePieceCutoff_eq_zero_of_ge (q : ℕ) {u : ℝ}
    (hu : 4 * sourcePieceScale (q + 1) ≤ u) : sourcePieceCutoff q u = 0 := by
  have hp := sourcePieceScale_pos q
  have hp' := sourcePieceScale_pos (q + 1)
  have hm := sourcePieceScale_monotone (Nat.le_succ q)
  have hlow : 2 ≤ u / (2 * sourcePieceScale q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have hhigh : 2 ≤ u / (2 * sourcePieceScale (q + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  simp only [sourcePieceCutoff, sourcePieceChi_eq_zero hlow, sourcePieceChi_eq_zero hhigh,
    sub_self]

theorem sourcePieceCutoff_nonneg (q : ℕ) (u : ℝ) : 0 ≤ sourcePieceCutoff q u := by
  by_cases hu : 0 ≤ u
  · apply sub_nonneg.mpr
    apply sourcePieceChi_antitone
    apply div_le_div_of_nonneg_left hu (by have := sourcePieceScale_pos q; positivity)
    exact mul_le_mul_of_nonneg_left (sourcePieceScale_monotone (Nat.le_succ q)) (by norm_num)
  · rw [sourcePieceCutoff_eq_zero_of_le q (by have := sourcePieceScale_pos q; linarith)]

theorem sourcePieceCutoff_le_one (q : ℕ) (u : ℝ) : sourcePieceCutoff q u ≤ 1 := by
  unfold sourcePieceCutoff
  linarith [sourcePieceChi_le_one (u / (2 * sourcePieceScale (q + 1))),
    sourcePieceChi_nonneg (u / (2 * sourcePieceScale q))]

theorem sourcePieceCutoff_norm_le_one (q : ℕ) (u : ℝ) : ‖sourcePieceCutoff q u‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (sourcePieceCutoff_nonneg q u)]
  exact sourcePieceCutoff_le_one q u

theorem sourcePieceCutoff_support_subset (q : ℕ) :
    Function.support (sourcePieceCutoff q) ⊆
      Ioo (2 * sourcePieceScale q) (4 * sourcePieceScale (q + 1)) := by
  intro u hu
  constructor
  · by_contra h
    exact hu (sourcePieceCutoff_eq_zero_of_le q (le_of_not_gt h))
  · by_contra h
    exact hu (sourcePieceCutoff_eq_zero_of_ge q (le_of_not_gt h))

theorem sourcePieceCutoff_tsupport_subset (q : ℕ) :
    tsupport (sourcePieceCutoff q) ⊆
      Icc (2 * sourcePieceScale q) (4 * sourcePieceScale (q + 1)) :=
  closure_minimal ((sourcePieceCutoff_support_subset q).trans Ioo_subset_Icc_self) isClosed_Icc

theorem sourcePieceCutoff_hasCompactSupport (q : ℕ) : HasCompactSupport (sourcePieceCutoff q) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (sourcePieceCutoff_tsupport_subset q)

/-- Every derivative has the same closed support bounds as the actual piece. -/
theorem sourcePieceCutoff_iteratedDeriv_tsupport (q k : ℕ) :
    tsupport (deriv^[k] (sourcePieceCutoff q)) ⊆
      Icc (2 * sourcePieceScale q) (4 * sourcePieceScale (q + 1)) := by
  induction k with
  | zero => exact sourcePieceCutoff_tsupport_subset q
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact tsupport_deriv_subset.trans ih

/-- Exact finite telescoping; no infinite sum or convergence is assumed. -/
theorem sum_sourcePieceCutoff (n : ℕ) (u : ℝ) :
    (∑ q ∈ Finset.range n, sourcePieceCutoff q u) =
      sourcePieceChi (u / (2 * sourcePieceScale n)) - sourcePieceChi (u / 32) := by
  unfold sourcePieceCutoff
  simpa only [sourcePieceScale_zero, show (2 : ℝ) * 16 = 32 by norm_num] using
    Finset.sum_range_sub (fun q => sourcePieceChi (u / (2 * sourcePieceScale q))) n

theorem sum_sourcePieceCutoff_eq_one_sub (n : ℕ) {u : ℝ}
    (hu : u ≤ 2 * sourcePieceScale n) :
    (∑ q ∈ Finset.range n, sourcePieceCutoff q u) = 1 - sourcePieceChi (u / 32) := by
  rw [sum_sourcePieceCutoff, sourcePieceChi_eq_one]
  exact (div_le_one (by have := sourcePieceScale_pos n; positivity)).mpr hu

theorem sourcePieceChi_iteratedDeriv_tsupport (k : ℕ) :
    tsupport (iteratedDeriv (k + 1) sourcePieceChi) ⊆ Icc (1 : ℝ) 2 := by
  induction k with
  | zero => simpa only [zero_add, iteratedDeriv_one] using sourcePieceChi_deriv_tsupport
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem exists_sourcePieceChi_iteratedDeriv_bound (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, ‖iteratedDeriv (k + 1) sourcePieceChi u‖ ≤ B := by
  have hc : HasCompactSupport (iteratedDeriv (k + 1) sourcePieceChi) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (sourcePieceChi_iteratedDeriv_tsupport k)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous
    (sourcePieceChi_contDiff.continuous_iteratedDeriv (k + 1) (cutoff_nat_le_infty _))
  exact ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun u => (hB u).trans (le_max_right _ _)⟩

private theorem scaled_sourcePieceChi_iteratedDeriv (k : ℕ) (L : ℝ) (u : ℝ) :
    iteratedDeriv k (fun v => sourcePieceChi (v / L)) u =
      L⁻¹ ^ k * iteratedDeriv k sourcePieceChi (u / L) := by
  have hf : (fun v => sourcePieceChi (v / L)) = (fun v => sourcePieceChi (L⁻¹ * v)) := by
    funext v
    rw [div_eq_mul_inv, mul_comm]
  rw [hf, iteratedDeriv_comp_const_mul (sourcePieceChi_contDiff.of_le (cutoff_nat_le_infty k))]
  simp only [div_eq_mul_inv, mul_comm]

private theorem scaled_sourcePieceChi_bound (k : ℕ) {B L u : ℝ}
    (hB : 0 ≤ B) (hL : 0 < L) (hu : 0 < u)
    (hbound : ∀ v : ℝ, ‖iteratedDeriv (k + 1) sourcePieceChi v‖ ≤ B) :
    ‖iteratedDeriv (k + 1) (fun v => sourcePieceChi (v / L)) u‖ ≤
      B * (2 : ℝ) ^ (k + 1) * u ^ (-((k + 1 : ℕ) : ℝ)) := by
  rw [scaled_sourcePieceChi_iteratedDeriv]
  by_cases hz : iteratedDeriv (k + 1) sourcePieceChi (u / L) = 0
  · rw [hz, mul_zero, norm_zero]
    positivity
  have hs := sourcePieceChi_iteratedDeriv_tsupport k (subset_closure hz)
  have hLu : u ≤ 2 * L := (div_le_iff₀ hL).mp hs.2
  have hratio : L⁻¹ ≤ 2 / u := by
    rw [← one_div]
    exact (div_le_div_iff₀ hL hu).mpr (by linarith)
  rw [norm_mul, norm_pow, Real.norm_of_nonneg (inv_nonneg.mpr hL.le)]
  calc
    _ ≤ (2 / u) ^ (k + 1) * B :=
      mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr hL.le) hratio (k + 1))
        (hbound _) (norm_nonneg _) (by positivity)
    _ = B * (2 : ℝ) ^ (k + 1) * u ^ (-((k + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hu.le, Real.rpow_natCast, div_pow]
      ring

/-- Every derivative order has a bound uniform in the source piece. The
constant is chosen before the piece and evaluation point; order zero is
included without appealing to support of a positive-order derivative. -/
theorem exists_sourcePieceCutoff_weighted_derivative_bound (k : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (q : ℕ) (u : ℝ), 0 < u →
      ‖iteratedDeriv k (sourcePieceCutoff q) u‖ ≤ D * u ^ (-(k : ℝ)) := by
  cases k with
  | zero =>
      refine ⟨1, zero_lt_one, fun q u _ => ?_⟩
      simpa using sourcePieceCutoff_norm_le_one q u
  | succ k =>
      obtain ⟨B, hB, hbound⟩ := exists_sourcePieceChi_iteratedDeriv_bound k
      refine ⟨2 * B * (2 : ℝ) ^ (k + 1), by positivity, fun q u hu => ?_⟩
      have hleft : ContDiff ℝ ∞
          (fun v => sourcePieceChi (v / (2 * sourcePieceScale (q + 1)))) := by
        have := sourcePieceChi_contDiff
        fun_prop
      have hright : ContDiff ℝ ∞
          (fun v => sourcePieceChi (v / (2 * sourcePieceScale q))) := by
        have := sourcePieceChi_contDiff
        fun_prop
      have hb0 := scaled_sourcePieceChi_bound k hB.le
        (show 0 < 2 * sourcePieceScale (q + 1) by have := sourcePieceScale_pos (q + 1); positivity)
        hu hbound
      have hb1 := scaled_sourcePieceChi_bound k hB.le
        (show 0 < 2 * sourcePieceScale q by have := sourcePieceScale_pos q; positivity) hu hbound
      unfold sourcePieceCutoff
      rw [iteratedDeriv_fun_sub (hleft.of_le (cutoff_nat_le_infty (k + 1))).contDiffAt
        (hright.of_le (cutoff_nat_le_infty (k + 1))).contDiffAt]
      exact (norm_sub_le _ _).trans (by nlinarith [hb0, hb1])

end ProofProject
