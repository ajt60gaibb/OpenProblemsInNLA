/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original question: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. This is the reviewed direct trace-pairing
form of Holden's elementary commutator estimate. R=2Q-I is a contraction, and
the half in [Q,H]=(1/2)[R,H] cancels the two norm products exactly.

The sole fixed numerical certificate, C01, is consumed in the scalar norm
identity through abs_of_pos and in both nonnegative scalar multiplications.
No general trace-norm triangle, ideal inequality or duality is assumed.
-/
import NLA.MI27.Numerical
import NLA.MI27.PositiveTrace
import NLA.MI27.SkewRotation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Tactic.Abel

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- A Hermitian matrix between -I and I has Euclidean operator norm at most one. -/
lemma hermitian_opNorm_le_one_of_bounds {n : ℕ} (R : Mat n) (hR : R.IsHermitian)
    (hl : -(1 : Mat n) ≤ R) (hu : R ≤ 1) : opNorm R ≤ 1 := by
  have hl' : algebraMap ℝ (Mat n) (-1) ≤ R := by
    simpa only [map_neg, map_one] using hl
  have hu' : R ≤ algebraMap ℝ (Mat n) 1 := by
    simpa only [map_one] using hu
  have hlo := (algebraMap_le_iff_le_spectrum (R := ℝ) hR.isSelfAdjoint).mp hl'
  have hup := (le_algebraMap_iff_spectrum_le (R := ℝ) hR.isSelfAdjoint).mp hu'
  rw [opNorm_eq_l2]
  calc
    ‖R‖ = ‖cfc (id : ℝ → ℝ) R‖ :=
      congrArg norm (cfc_id ℝ R hR.isSelfAdjoint).symm
    _ ≤ 1 := norm_cfc_le zero_le_one fun x hx => by
      simpa only [id_eq, Real.norm_eq_abs] using abs_le.mpr ⟨hlo x hx, hup x hx⟩

/-- The affine center of a Loewner effect is a Hermitian contraction. -/
lemma effect_center_opNorm_le_one {n : ℕ} (Q : Mat n)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) : opNorm ((2 : ℂ) • Q - 1) ≤ 1 := by
  have hQ := (Matrix.nonneg_iff_posSemidef.mp hQ0).isHermitian
  have hR : ((2 : ℂ) • Q - 1).IsHermitian := by
    simpa only [two_smul] using (hQ.add hQ).sub Matrix.isHermitian_one
  apply hermitian_opNorm_le_one_of_bounds _ hR
  · rw [two_smul, le_sub_iff_add_le]
    simpa only [neg_add_cancel] using add_nonneg hQ0 hQ0
  · rw [two_smul, sub_le_iff_le_add]
    exact add_le_add hQ1 hQ1

lemma opNorm_comm_le {n : ℕ} (R H : Mat n) :
    opNorm (comm R H) ≤ opNorm R * opNorm H + opNorm H * opNorm R := by
  simp only [opNorm_eq_l2, comm]
  exact (norm_sub_le (R * H) (H * R)).trans
    (add_le_add (norm_mul_le R H) (norm_mul_le H R))

lemma opNorm_ofReal_smul {n : ℕ} (c : ℝ) (X : Mat n) :
    opNorm ((c : ℂ) • X) = |c| * opNorm X := by
  simp only [opNorm_eq_l2, norm_smul, Complex.norm_real, Real.norm_eq_abs]

lemma opNorm_neg_I_smul {n : ℕ} (X : Mat n) :
    opNorm ((-Complex.I) • X) = opNorm X := by
  simp only [opNorm_eq_l2, norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- The half-commutator estimate, retaining a proof dependency on certified C01. -/
lemma effect_commutator_opNorm_le {n : ℕ} (Q H : Mat n)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) : opNorm (comm Q H) ≤ opNorm H := by
  let R : Mat n := (2 : ℂ) • Q - 1
  have hR : opNorm R ≤ 1 := effect_center_opNorm_le_one Q hQ0 hQ1
  have hdouble : comm R H = (2 : ℂ) • comm Q H := by
    dsimp only [R, comm]
    simp only [two_smul, add_mul, sub_mul, mul_add, mul_sub, one_mul, mul_one]
    abel
  have hhalf : comm Q H = ((1 / 2 : ℝ) : ℂ) • comm R H := by
    rw [hdouble, smul_smul]
    norm_num
  calc
    opNorm (comm Q H) = (1 / 2 : ℝ) * opNorm (comm R H) := by
      rw [hhalf, opNorm_ofReal_smul, abs_of_pos half_coefficient_positive]
    _ ≤ (1 / 2 : ℝ) * (opNorm R * opNorm H + opNorm H * opNorm R) :=
      mul_le_mul_of_nonneg_left (opNorm_comm_le R H) half_coefficient_positive.le
    _ ≤ (1 / 2 : ℝ) * (1 * opNorm H + opNorm H * 1) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_right hR (opNorm_nonneg H))
          (mul_le_mul_of_nonneg_left hR (opNorm_nonneg H))) half_coefficient_positive.le
    _ = opNorm H := by ring

lemma neg_I_comm_isHermitian {n : ℕ} (Q H : Mat n)
    (hQ : Q.IsHermitian) (hH : H.IsHermitian) :
    ((-Complex.I) • comm Q H).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, comm_conjTranspose Q H hQ hH]
  simp only [Complex.star_def, Complex.conj_neg_I, smul_neg, neg_smul]

/-- Trace cyclicity moves the commutator onto the Hermitian test/effect pair. -/
lemma trR_comm_cycle {n : ℕ} (X H Q : Mat n) :
    trR ((-Complex.I) • (H * comm X Q)) =
      trR (X * ((-Complex.I) • comm Q H)) := by
  have ht : Matrix.trace (H * comm X Q) = Matrix.trace (X * comm Q H) := by
    simp only [comm, mul_sub, Matrix.trace_sub]
    rw [Matrix.trace_mul_comm H (X * Q), Matrix.trace_mul_cycle' H Q X]
    simp only [mul_assoc]
  unfold trR
  rw [Matrix.trace_smul, mul_smul_comm, Matrix.trace_smul, ht]

/-- C05. Direct PSD trace pairing with -i[Q,H], using C04 and the certified
half-commutator estimate, including the zero/singular X and endpoint Q cases. -/
theorem positive_commutator_trace_bound {n : ℕ} (hn : 1 ≤ n) (X H Q : Mat n)
    (hX : X.PosSemidef) (hH : H.IsHermitian) (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) :
    |trR ((-Complex.I) • (H * comm X Q))| ≤ opNorm H * trR X := by
  have hQ := (Matrix.nonneg_iff_posSemidef.mp hQ0).isHermitian
  have hY := neg_I_comm_isHermitian Q H hQ hH
  have hnorm : opNorm ((-Complex.I) • comm Q H) ≤ opNorm H := by
    rw [opNorm_neg_I_smul]
    exact effect_commutator_opNorm_le Q H hQ0 hQ1
  calc
    |trR ((-Complex.I) • (H * comm X Q))| =
        |trR (X * ((-Complex.I) • comm Q H))| := congrArg abs (trR_comm_cycle X H Q)
    _ ≤ trR X * opNorm ((-Complex.I) • comm Q H) :=
      positive_trace_operator_bound hn X _ hX hY
    _ ≤ trR X * opNorm H := mul_le_mul_of_nonneg_left hnorm (trR_nonneg X hX)
    _ = opNorm H * trR X := mul_comm _ _

#print axioms positive_commutator_trace_bound
#assert_trust kernel positive_commutator_trace_bound

end NLA.MI27
