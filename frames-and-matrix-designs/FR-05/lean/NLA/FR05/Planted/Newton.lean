import NLA.FR05.Geometry.Planted
import NLA.FR05.SourceParameters
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! ## Newton -/

section

/-
The fixed-point endpoint used in the proof of Proposition 3.1.

This module records the Banach-contraction step separately from the
source-specific estimates which establish its hypotheses.  It is stated for
the planted equation map, so a fixed point is immediately an exact
phase-retrieval ambiguity through `Planted.lean`.
-/


set_option autoImplicit false
noncomputable section

open scoped BigOperators ComplexConjugate Matrix NNReal

namespace NLA.FR05

/-- The real coordinate space of the polynomial rank-two factor chart. -/
abbrev FactorParameters (n : ℕ) := ℝ × ℂ × Signal n × Signal n

/-- The real dimension of the chart coordinate space.  With `n = M - 2`,
this is the source row count `4M - 5`. -/
theorem finrank_factorParameters (n : ℕ) :
    Module.finrank ℝ (FactorParameters n) = 1 + 2 + 2 * n + 2 * n := by
  simp [FactorParameters, Complex.finrank_real_complex, Module.finrank_pi_fintype]
  lia

/-- At the source dimensions, the planted equation map has square real
Jacobian size. -/
theorem finrank_factorParameters_source (M : ℕ) (hM : 2 ≤ M) :
    Module.finrank ℝ (FactorParameters (sourceTailDimension M)) =
      sourceRowCount M := by
  rw [finrank_factorParameters]
  exact source_chart_real_parameter_count M hM

/-- The planted measurement map in the polynomial factor-chart coordinates. -/
def plantedEquationMap {m n : ℕ} (rows : Fin m → PlantedRow n) :
    FactorParameters n → (Fin m → ℝ) :=
  fun θ i ↦ plantedEquation (rows i) θ.1 θ.2.1 θ.2.2.1 θ.2.2.2

theorem plantedEquationMap_apply {m n : ℕ} (rows : Fin m → PlantedRow n)
    (θ : FactorParameters n) (i : Fin m) :
    plantedEquationMap rows θ i =
      plantedEquation (rows i) θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 := rfl

/-- `F^ε(0)` is exactly the vector of planted imbalances. -/
theorem plantedEquationMap_zero {m n : ℕ} (rows : Fin m → PlantedRow n) :
    plantedEquationMap rows 0 = fun i ↦ (rows i).imbalance := by
  funext i
  simp [plantedEquationMap, plantedEquation_zero]

/-- A coordinate of a point in the chart ball is bounded by the ball radius.
This is the small local-chart fact used to pass from the Newton ball to the
`|s| ≤ 1` hypothesis of the factor chart. -/
theorem abs_factorParameter_scalar_le_radius {n : ℕ}
    (θ : FactorParameters n) {R : ℝ}
    (hθ : θ ∈ Metric.closedBall (0 : FactorParameters n) R) :
    |θ.1| ≤ R := by
  rw [← Real.norm_eq_abs]
  calc
    ‖θ.1‖ ≤ ‖θ‖ := norm_fst_le θ
    _ = dist θ 0 := (dist_zero_right θ).symm
    _ ≤ R := Metric.mem_closedBall.mp hθ

/-- The Newton self-map associated to a chosen injective left inverse of the
linearization. -/
def plantedNewtonMap {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n) :
    FactorParameters n → FactorParameters n :=
  fun θ ↦ θ - Jinv (plantedEquationMap rows θ)

/-- A contraction of the source Newton map on a closed coordinate ball has a
zero of the planted equations in that ball.  This discharges the exact
fixed-point implication in Proposition 3.1 without assuming a root. -/
theorem exists_plantedEquationMap_zero_of_contracting
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n)
    (hJinj : Function.Injective Jinv)
    (R : ℝ) (hR : 0 ≤ R) (K : ℝ≥0)
    (hmap : Set.MapsTo (plantedNewtonMap rows Jinv)
      (Metric.closedBall (0 : FactorParameters n) R)
      (Metric.closedBall (0 : FactorParameters n) R))
    (hcontract : ContractingWith K
      (hmap.restrict (plantedNewtonMap rows Jinv)
        (Metric.closedBall (0 : FactorParameters n) R)
        (Metric.closedBall (0 : FactorParameters n) R))) :
    ∃ θ : FactorParameters n, θ ∈ Metric.closedBall 0 R ∧
      plantedEquationMap rows θ = 0 := by
  have hcomplete : IsComplete (Metric.closedBall (0 : FactorParameters n) R) :=
    Metric.isClosed_closedBall.isComplete
  have hzero : (0 : FactorParameters n) ∈ Metric.closedBall 0 R := by
    simp [hR]
  obtain ⟨θ, hθball, hfixed, -, -⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmap hzero (edist_ne_top _ _)
  refine ⟨θ, hθball, ?_⟩
  apply hJinj
  have hsub : Jinv (plantedEquationMap rows θ) = 0 := by
    exact sub_eq_self.mp hfixed
  simpa using hsub

/-- If the contraction ball keeps the scalar chart coordinate in the local
range used by the factor chart, the fixed point produces a genuine
non-injectivity witness for the planted frame. -/
theorem plantedFrame_not_phaseRetrievalInjective_of_contracting
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n)
    (hJinj : Function.Injective Jinv)
    (R : ℝ) (hR : 0 ≤ R) (K : ℝ≥0)
    (hmap : Set.MapsTo (plantedNewtonMap rows Jinv)
      (Metric.closedBall (0 : FactorParameters n) R)
      (Metric.closedBall (0 : FactorParameters n) R))
    (hcontract : ContractingWith K
      (hmap.restrict (plantedNewtonMap rows Jinv)
        (Metric.closedBall (0 : FactorParameters n) R)
        (Metric.closedBall (0 : FactorParameters n) R)))
    (hscalar : ∀ θ : FactorParameters n,
      θ ∈ Metric.closedBall 0 R → |θ.1| ≤ 1) :
    ¬ PhaseRetrievalInjective (plantedFrame rows) := by
  obtain ⟨θ, hθball, hzero⟩ := exists_plantedEquationMap_zero_of_contracting
    rows Jinv hJinj R hR K hmap hcontract
  exact plantedFrame_not_phaseRetrievalInjective_of_equations_eq_zero rows
    θ.1 θ.2.1 θ.2.2.1 θ.2.2.2 (hscalar θ hθball) (by
      intro i
      exact congr_fun hzero i)

/-- The previous endpoint in the concrete source regime where the Newton
radius is at most one. -/
theorem plantedFrame_not_phaseRetrievalInjective_of_contracting_of_radius_le_one
    {m n : ℕ} (rows : Fin m → PlantedRow n)
    (Jinv : (Fin m → ℝ) →ₗ[ℝ] FactorParameters n)
    (hJinj : Function.Injective Jinv)
    (R : ℝ) (hR : 0 ≤ R) (hRone : R ≤ 1) (K : ℝ≥0)
    (hmap : Set.MapsTo (plantedNewtonMap rows Jinv)
      (Metric.closedBall (0 : FactorParameters n) R)
      (Metric.closedBall (0 : FactorParameters n) R))
    (hcontract : ContractingWith K
      (hmap.restrict (plantedNewtonMap rows Jinv)
        (Metric.closedBall (0 : FactorParameters n) R)
        (Metric.closedBall (0 : FactorParameters n) R))) :
    ¬ PhaseRetrievalInjective (plantedFrame rows) := by
  apply plantedFrame_not_phaseRetrievalInjective_of_contracting rows Jinv hJinj
    R hR K hmap hcontract
  intro θ hθ
  exact (abs_factorParameter_scalar_le_radius θ hθ).trans hRone

end NLA.FR05

end
end

/-! ## LocalNewton -/

section

set_option autoImplicit false
noncomputable section
open scoped NNReal
namespace NLA.FR05

theorem exists_zero_of_local_linear_control
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (F : E → E) (J : E →ₗ[ℝ] E) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 ≤ R)
    (hJ : ∀ x, κ * ‖x‖ ≤ ‖J x‖)
    (hres : 2 * ‖F 0‖ ≤ κ * R)
    (hlip : ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖F x - F y - J (x - y)‖ ≤ (κ / 2) * ‖x - y‖) :
    ∃ x, ‖x‖ ≤ R ∧ F x = 0 := by
  have hinj : Function.Injective J := by
    intro x y h
    have hh := hJ (x - y)
    rw [map_sub, h, sub_self, norm_zero] at hh
    have hn : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  let e := LinearEquiv.ofBijective J ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let T : E → E := fun x ↦ x - e.symm (F x)
  have hJT (x y : E) : J (T x - T y) = -(F x - F y - J (x - y)) := by
    change e (T x - T y) = _
    simp only [T, map_sub, e.apply_symm_apply]
    change J x - F x - (J y - F y) = -(F x - F y - (J x - J y))
    abel
  have hT (x y : E) (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) :
      ‖T x - T y‖ ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
    have hh := hJ (T x - T y)
    rw [hJT, norm_neg] at hh
    have hb := hh.trans (hlip x y hx hy)
    nlinarith
  have hT0 : ‖T 0‖ ≤ R / 2 := by
    have hh := hJ (T 0)
    have he : J (T 0) = -(F 0) := by
      change e (0 - e.symm (F 0)) = _
      simp
    rw [he, norm_neg] at hh
    nlinarith
  have hmap : Set.MapsTo T (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    calc
      ‖T x‖ ≤ ‖T x - T 0‖ + ‖T 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (T x - T 0) (T 0)
      _ ≤ (1 / 2 : ℝ) * ‖x - 0‖ + R / 2 := add_le_add (hT x 0 hx (by simpa using hR)) hT0
      _ ≤ R := by rw [sub_zero]; linarith
  have hcontract : ContractingWith (1 / 2 : ℝ≥0)
      (hmap.restrict T (Metric.closedBall 0 R) (Metric.closedBall 0 R)) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x) (T y) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (x : E) y
    norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    simp only [dist_eq_norm]
    exact hT x y (by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property)
  obtain ⟨x, hx, hfixed, _, _⟩ :=
    hcontract.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmap
      (show (0 : E) ∈ Metric.closedBall 0 R by simpa using hR) (edist_ne_top _ _)
  refine ⟨x, by simpa using hx, ?_⟩
  have hz : e.symm (F x) = 0 := sub_eq_self.mp hfixed
  exact e.symm.injective (by simpa using hz)
end NLA.FR05

end

end

/-! ## NewtonCalibration -/

section

set_option autoImplicit false
noncomputable section
namespace NLA.FR05

def sourceNewtonRadius (M : ℕ) : ℝ := 1 / (M : ℝ) ^ 30

theorem sourceNewton_calibration {M : ℕ} (hM : 8192 ≤ M) :
    0 ≤ sourceNewtonRadius M ∧ sourceNewtonRadius M ≤ 1 ∧
    2 * (2 / (M : ℝ) ^ 49) ≤ sourceKappa M * sourceNewtonRadius M ∧
    512 / (M : ℝ) ^ 44 + 2048 * (M : ℝ) ^ 6 * sourceNewtonRadius M ≤
      sourceKappa M / 2 := by
  have hm : (8192 : ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < M := by linarith
  have hm1 : (1 : ℝ) ≤ M := by linarith
  have hm7 : (4 : ℝ) ≤ (M : ℝ) ^ 7 := by
    have h := pow_le_pow_right₀ hm1 (show 1 ≤ 7 by lia)
    norm_num only [pow_one] at h
    linarith
  have hm12 : (8192 : ℝ) ≤ (M : ℝ) ^ 12 := by
    have h := pow_le_pow_right₀ hm1 (show 1 ≤ 12 by lia)
    norm_num only [pow_one] at h
    linarith
  have hm32 : (2048 : ℝ) ≤ (M : ℝ) ^ 32 := by
    have h := pow_le_pow_right₀ hm1 (show 1 ≤ 32 by lia)
    norm_num only [pow_one] at h
    linarith
  have hres : 4 / (M : ℝ) ^ 49 ≤ 1 / (M : ℝ) ^ 42 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      4 * (M : ℝ) ^ 42 ≤ (M : ℝ) ^ 7 * (M : ℝ) ^ 42 :=
        mul_le_mul_of_nonneg_right hm7 (by positivity)
      _ = 1 * (M : ℝ) ^ 49 := by ring
  have ht : 512 / (M : ℝ) ^ 44 ≤ (1 / (M : ℝ) ^ 12) / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      (512 * 4) * (M : ℝ) ^ 12 ≤ (M : ℝ) ^ 32 * (M : ℝ) ^ 12 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * (M : ℝ) ^ 44 := by ring
  have hq : 2048 / (M : ℝ) ^ 24 ≤ (1 / (M : ℝ) ^ 12) / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    calc
      (2048 * 4) * (M : ℝ) ^ 12 ≤ (M : ℝ) ^ 12 * (M : ℝ) ^ 12 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 * (M : ℝ) ^ 24 := by ring
  unfold sourceNewtonRadius sourceKappa
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show 1 ≤ (M : ℝ) ^ 30 from one_le_pow₀ hm1)
  · have he : ((M : ℝ) ^ 12)⁻¹ * (1 / (M : ℝ) ^ 30) = 1 / (M : ℝ) ^ 42 := by
      field_simp
    rw [he]
    simpa only [div_eq_mul_inv, ← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hres
  · have he : 2048 * (M : ℝ) ^ 6 * (1 / (M : ℝ) ^ 30) = 2048 / (M : ℝ) ^ 24 := by
      field_simp
    rw [he]
    simp only [one_div] at ht hq
    linarith
end NLA.FR05

end

end

/-! ## PlantedBounds -/

section

/-
Finite-dimensional norm estimates for the planted equation map.

The norm in this file is the actual Euclidean norm (rather than Lean's
default sup norm on a finite function type), matching the vector norm in
equation (3.24) of the source.
-/


set_option autoImplicit false
noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace NLA.FR05

/-- Euclidean norm on a finite real coordinate vector. -/
def realEuclideanNorm {m : ℕ} (x : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

theorem realEuclideanNorm_nonneg {m : ℕ} (x : Fin m → ℝ) :
    0 ≤ realEuclideanNorm x :=
  Real.sqrt_nonneg _

theorem sq_realEuclideanNorm {m : ℕ} (x : Fin m → ℝ) :
    realEuclideanNorm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold realEuclideanNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- A coordinatewise interval bound gives the usual Euclidean $ℓ^2$
bound. -/
theorem realEuclideanNorm_le_of_abs_le {m : ℕ} (x : Fin m → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hx : ∀ i, |x i| ≤ ε) :
    realEuclideanNorm x ≤ ε * Real.sqrt m := by
  have hsquares : ∀ i, x i ^ 2 ≤ ε ^ 2 := by
    intro i
    have habs : 0 ≤ |x i| := abs_nonneg _
    have hbound := hx i
    rw [← sq_abs]
    nlinarith
  have hsum : ∑ i, x i ^ 2 ≤ (m : ℝ) * ε ^ 2 := by
    calc
      ∑ i, x i ^ 2 ≤ ∑ _i : Fin m, ε ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ hsquares i
      _ = (m : ℝ) * ε ^ 2 := by simp
  have hleft : 0 ≤ realEuclideanNorm x := realEuclideanNorm_nonneg x
  have hright : 0 ≤ ε * Real.sqrt m :=
    mul_nonneg hε (Real.sqrt_nonneg _)
  have hsqrtSq : (Real.sqrt (m : ℝ)) ^ 2 = m := by
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hsum' : realEuclideanNorm x ^ 2 ≤ (m : ℝ) * ε ^ 2 := by
    rwa [sq_realEuclideanNorm]
  nlinarith

/-- The source's $F^ε(0)$ estimate: when every planted imbalance lies in
`[-ε, ε]`, its exact initial residual has Euclidean norm at most
`ε √m`. -/
theorem plantedEquationMap_zero_euclideanNorm_le
    {m n : ℕ} (rows : Fin m → PlantedRow n) (ε : ℝ) (hε : 0 ≤ ε)
    (himbalance : ∀ i, |(rows i).imbalance| ≤ ε) :
    realEuclideanNorm (plantedEquationMap rows 0) ≤ ε * Real.sqrt m := by
  rw [plantedEquationMap_zero]
  exact realEuclideanNorm_le_of_abs_le (fun i ↦ (rows i).imbalance) ε hε himbalance

end NLA.FR05

end

end
