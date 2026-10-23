import NLA.Proofs.PF05.CoordinateActions
import Mathlib

/-! Exact determinant consequences of an invertible symmetric-coordinate
operator that preserves the rank-one conic. This module begins the actual
conic-preserver classification; it assumes no congruence representation. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05.ConicDeterminant
noncomputable section
open Matrix
open CoordinateActions
open NLA.Statements.PF05
open scoped BigOperators Matrix
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Vec2 := Fin 2 → ℝ

def outer (v : Vec2) : M2 := Matrix.vecMulVec v v
def scale (L : M3) : ℝ := L 0 0 * L 1 1 + L 1 0 * L 0 1 - 2 * L 0 2 * L 1 2

theorem conic_coefficients (L : M3)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0) :
    L 0 0 * L 0 1 - (L 0 2)^2 = 0 ∧
    L 1 0 * L 1 1 - (L 1 2)^2 = 0 ∧
    L 0 0 * L 2 1 + L 2 0 * L 0 1 - 2 * L 0 2 * L 2 2 = 0 ∧
    L 1 0 * L 2 1 + L 2 0 * L 1 1 - 2 * L 1 2 * L 2 2 = 0 ∧
    scale L + L 2 0 * L 2 1 - (L 2 2)^2 = 0 := by
  have h0 := h ![1,0]
  have hinf := h ![0,1]
  have h1 := h ![1,1]
  have hm1 := h ![1,-1]
  have h2 := h ![1,2]
  norm_num [primal, decodeLeft, leftVector, outer, Matrix.vecMulVec_apply,
    Matrix.vecMul, dotProduct, Matrix.det_fin_two, Fin.sum_univ_three] at h0 hinf h1 hm1 h2
  dsimp at h0 hinf h1 hm1 h2
  refine ⟨by nlinarith [h0], by nlinarith [hinf], ?_, ?_, ?_⟩ <;>
    (try dsimp [scale]) <;> nlinarith only [h0, hinf, h1, hm1, h2]

/-- The rank-one conic equations force preservation of the whole determinant
form, up to its actual scalar coefficient. -/
theorem determinant_scale (L : M3)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0)
    (A : M2) (hA : Symmetric A) :
    (primal L A).det = scale L * A.det := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := conic_coefficients L h
  simp only [primal, decodeLeft, leftVector, Matrix.vecMul, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.det_fin_two, hA 1 0]
  simp only [Matrix.head_cons, Matrix.tail_cons]
  dsimp [scale] at h4 ⊢
  linear_combination (A 0 0)^2 * h0 + (A 1 1)^2 * h1 +
    (A 0 0 * A 0 1) * h2 + (A 1 1 * A 0 1) * h3 + (A 0 1)^2 * h4

/-- The exact matrix of the determinant quadratic form in (a,c,b) coordinates. -/
def metric : M3 := !![0,1/2,0;1/2,0,0;0,0,-1]

theorem metric_identity (L : M3)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0) :
    L * metric * L.transpose = scale L • metric := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := conic_coefficients L h
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [metric, Matrix.mul_apply, Fin.sum_univ_three, scale, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] <;>
    dsimp at * <;> (try dsimp [scale] at h4) <;> nlinarith only [h0, h1, h2, h3, h4]

/-- Invertibility forces the determinant scale to be positive: its cube is
the square of the actual nonzero coordinate determinant. -/
theorem scale_cube (L : M3)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0) :
    (scale L)^3 = L.det^2 := by
  have hh := congrArg Matrix.det (metric_identity L h)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul] at hh
  have hm : metric.det = 1 / 4 := by
    norm_num [metric, Matrix.det_fin_three, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  rw [hm] at hh
  norm_num at hh
  nlinarith only [hh]

theorem scale_pos (L : M3) (hL : L.det ≠ 0)
    (h : ∀ v : Vec2, (primal L (outer v)).det = 0) : 0 < scale L := by
  have hc := scale_cube L h
  have hd : 0 < L.det^2 := sq_pos_of_ne_zero hL
  by_contra hn
  have hk : scale L ≤ 0 := le_of_not_gt hn
  have hcube := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (scale L)) hk
  nlinarith only [hc, hd, hcube]

#assert_trust kernel conic_coefficients
#assert_trust kernel determinant_scale
#assert_trust kernel metric_identity
#assert_trust kernel scale_cube
#assert_trust kernel scale_pos
#print axioms determinant_scale
#print axioms scale_pos
end
end NLA.Proofs.PF05.ConicDeterminant
