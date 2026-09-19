import NLA.PF03.ConeLocalQuadratics
import NLA.PF03.CrossConeCertificate

/-!
All off-diagonal group pairings are nonnegative. A zero such pairing forces
every product of its nonnegative coefficients to vanish, since each actual
generator pairing is strictly positive. Reversed indices use C05 symmetry.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

lemma distinct_generator_bilinear_pos (i j : Fin 7) (hij : i ≠ j) (a b : Fin 3) :
    0 < bilinear quadraticSeed (castVector (generator i a))
      (castVector (generator j b)) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact cross_cone_certificate i j hlt a b
  · rw [cone_bilinear_symm quadraticSeed seed_quadratic_form.1
      (castVector (generator i a)) (castVector (generator j b))]
    exact cross_cone_certificate j i hgt b a

lemma cone_group_bilinear (i j : Fin 7) (lam mu : Fin 3 → ℝ) :
    bilinear quadraticSeed (coneGroup i lam) (coneGroup j mu) =
      ∑ a : Fin 3, ∑ b : Fin 3, (lam a * mu b) *
        bilinear quadraticSeed (castVector (generator i a))
          (castVector (generator j b)) := by
  simp only [coneGroup, cone_bilinear_sum_left, cone_bilinear_sum_right,
    cone_bilinear_smul_left, cone_bilinear_smul_right, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

lemma cone_group_cross_nonneg (i j : Fin 7) (hij : i ≠ j)
    (lam mu : Fin 3 → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ b, 0 ≤ mu b) :
    0 ≤ bilinear quadraticSeed (coneGroup i lam) (coneGroup j mu) := by
  rw [cone_group_bilinear]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (mul_nonneg (hlam a) (hmu b))
    (distinct_generator_bilinear_pos i j hij a b).le

lemma cone_group_cross_zero (i j : Fin 7) (hij : i ≠ j)
    (lam mu : Fin 3 → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ b, 0 ≤ mu b)
    (hz : bilinear quadraticSeed (coneGroup i lam) (coneGroup j mu) = 0)
    (a b : Fin 3) : lam a * mu b = 0 := by
  rw [cone_group_bilinear] at hz
  have ht := cone_double_sum_term_zero
    (fun c d : Fin 3 => (lam c * mu d) *
      bilinear quadraticSeed (castVector (generator i c))
        (castVector (generator j d)))
    (fun c d => mul_nonneg (mul_nonneg (hlam c) (hmu d))
      (distinct_generator_bilinear_pos i j hij c d).le) hz a b
  exact (mul_eq_zero.mp ht).resolve_right
    (distinct_generator_bilinear_pos i j hij a b).ne'

#print axioms cone_group_cross_zero
#assert_trust kernel cone_group_cross_zero

end NLA.PF03
