/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original projective counterexample: Matthew J. Colbrook.
-/
import NLA.TR27.Geometry
import Mathlib.Algebra.Polynomial.Roots

/-!
# The algebraic border-rank witness

The explicit divided difference has two full-cone terms away from zero.
Substitution into any polynomial vanishing on all such rank-two points is a
univariate polynomial vanishing identically, hence also at zero. This proves
the frozen all-polynomial Zariski-closure statement directly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.TR27

/-- The displayed divided difference is an actual two-term cone expression. -/
theorem borderCurve_rank_two (t : ℂ) (ht : t ≠ 0) :
    ConeRankAtMost witnessVariety.cone 2 (borderCurve t) := by
  refine ⟨2, le_rfl, ![t⁻¹, -t⁻¹], ![curve (some t), curve (some 0)], ?_, ?_⟩
  · intro i
    fin_cases i <;> exact curve_mem_cone _
  · rw [borderCurve_divided_difference t ht]
    simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- Exact frozen semantics of the polynomial curve, including the special value. -/
theorem border_curve_semantics :
    borderCurve 0 = witnessVector ∧
    (∀ t : ℂ, borderCurve t ≠ 0) ∧
    (∀ t : ℂ, t ≠ 0 →
      borderCurve t = t⁻¹ • (curve (some t) - curve (some 0))) ∧
    (∀ t : ℂ, t ≠ 0 → ConeRankAtMost witnessVariety.cone 2 (borderCurve t)) :=
  ⟨borderCurve_zero, borderCurve_nonzero, borderCurve_divided_difference, borderCurve_rank_two⟩

/-- Polynomial coordinate functions of the extension at zero. -/
def borderCoordinatePolynomial (j : Fin 12) : Polynomial ℂ :=
  if coordinateIndex j = 0 then Polynomial.C (-3)
  else Polynomial.C 5 * Polynomial.X ^ ((coordinateIndex j : ℕ) - 1) -
    Polynomial.C (powerSum (coordinateIndex j : ℕ))

/-- Evaluation agrees with every frozen coordinate, including at zero. -/
theorem eval_borderCoordinatePolynomial (t : ℂ) (j : Fin 12) :
    Polynomial.eval t (borderCoordinatePolynomial j) = borderCurve t j := by
  by_cases hj : coordinateIndex j = 0 <;>
    simp [borderCoordinatePolynomial, borderCurve, hj]

/-- Substitution along the polynomial curve, with all twelve coordinates. -/
def borderSubstitution : CoordinatePolynomial →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval borderCoordinatePolynomial

/-- Substitution commutes with evaluation at every complex parameter. -/
theorem eval_borderSubstitution (t : ℂ) (f : CoordinatePolynomial) :
    Polynomial.eval t (borderSubstitution f) = MvPolynomial.eval (borderCurve t) f := by
  simpa only [borderSubstitution, Polynomial.coe_aeval_eq_eval, eval_borderCoordinatePolynomial,
    MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.comp_aeval_apply borderCoordinatePolynomial (Polynomial.aeval t) f)

/-- A polynomial zero away from zero is zero: multiply by X and use polynomial extensionality. -/
theorem polynomial_eq_zero_of_eval_nonzero (p : Polynomial ℂ)
    (hp : ∀ t : ℂ, t ≠ 0 → Polynomial.eval t p = 0) : p = 0 := by
  have hprod : Polynomial.X * p = 0 := by
    apply Polynomial.funext
    intro t
    by_cases ht : t = 0
    · simp [ht]
    · simp [hp t ht]
  exact (mul_eq_zero.mp hprod).resolve_left Polynomial.X_ne_zero

/-- Every polynomial vanishing on cone rank at most two also vanishes on the entire curve. -/
theorem polynomial_vanishes_borderCurve (f : CoordinatePolynomial)
    (hf : ∀ w : Space, ConeRankAtMost witnessVariety.cone 2 w →
      MvPolynomial.eval w f = 0) (t : ℂ) :
    MvPolynomial.eval (borderCurve t) f = 0 := by
  have hp : borderSubstitution f = 0 := by
    apply polynomial_eq_zero_of_eval_nonzero
    intro u hu
    rw [eval_borderSubstitution]
    exact hf (borderCurve u) (borderCurve_rank_two u hu)
  rw [← eval_borderSubstitution, hp, Polynomial.eval_zero]

/-- Exact frozen all-polynomial affine Zariski-closure membership. -/
theorem border_two :
    witnessVector ∈ witnessVariety.affineClosure
      {w | ConeRankAtMost witnessVariety.cone 2 w} := by
  intro f hf
  change MvPolynomial.eval witnessVector f = 0
  rw [← borderCurve_zero]
  apply polynomial_vanishes_borderCurve f
  intro w hw
  exact hf w ⟨w, hw, rfl⟩

end NLA.TR27
