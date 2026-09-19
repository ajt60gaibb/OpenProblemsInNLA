import NLA.PF03.TriangleRationalData

/-!
C09: exact barycentric and generator identities for the defined triangle.
Strict signs consume the actual root enclosure through cubicLower.
Original mathematics and seed: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

theorem barycentric_literal :
    barycentric = (fun j => cubicEval (RawData.barycentricCoefficients j)) := by
  funext j
  fin_cases j <;>
    norm_num [barycentric, cubicEval, RawData.barycentricCoefficients,
      dx, dy, centerA, centerB, triangleDelta, Matrix.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

theorem barycentric_sum : (∑ j : Fin 3, barycentric j) = 1 := by
  rw [Fin.sum_univ_three]
  change (1 + 2 * dx - dy) / 3 + (1 - dx + 2 * dy) / 3 +
    (1 - dx - dy) / 3 = 1
  ring

theorem triangle_barycentric : (castMatrix triangle).mulVec barycentric = alphaVector := by
  ext r
  change (∑ j : Fin 3, (triangle r j : ℝ) * barycentric j) = alphaVector r
  fin_cases r <;>
    norm_num [castMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      triangle, barycentric, alphaVector, dx, dy, centerA, centerB, triangleDelta, Matrix.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- C09: all literal caches, strict barycentric signs, and actual generators. -/
theorem triangle_certificate :
    triangle = RawData.triangle ∧
      barycentric = (fun j => cubicEval (RawData.barycentricCoefficients j)) ∧
      (∀ j : Fin 3, 0 < barycentric j) ∧
      (∑ j : Fin 3, barycentric j) = 1 ∧
      (castMatrix triangle).mulVec barycentric = alphaVector ∧
      generatorMatrix = RawData.generators := by
  refine ⟨triangle_literal, barycentric_literal, ?_, barycentric_sum,
    triangle_barycentric, generator_literal⟩
  intro j
  rw [barycentric_literal]
  exact cubicEval_pos_of_lower (RawData.barycentricCoefficients j)
    (barycentric_lower_positive j)

#print axioms triangle_certificate
#assert_trust kernel triangle_certificate

end NLA.PF03
