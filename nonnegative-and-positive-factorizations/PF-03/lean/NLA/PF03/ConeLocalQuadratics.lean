import NLA.PF03.ConeQuadraticAlgebra
import NLA.PF03.ConeCoordinates
import NLA.PF03.SeedLocalData

/-!
Each nonnegative local combination has a nonnegative quadratic value. A zero
is a nonnegative scalar seed ray; the scalar's sign follows from the literal
first row of the triangle, not from an assumed orientation of a kernel.
Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

def coneGroup (i : Fin 7) (lam : Fin 3 → ℝ) : Fin 7 → ℝ :=
  ∑ a : Fin 3, lam a • castVector (generator i a)

lemma cone_group_quad (i : Fin 7) (lam : Fin 3 → ℝ) :
    quad quadraticSeed (coneGroup i lam) =
      quad (localCache i) ((castMatrix triangle).mulVec lam) := by
  rw [coneGroup, local_generator_sum, cone_quad_mulVec]
  change quad (localForm i) _ = quad (localCache i) _
  rw [(seed_local_data i).1]

lemma cone_local_kernel (i : Fin 7) (z : Fin 3 → ℝ) :
    0 ≤ quad (localCache i) z ∧
      (quad (localCache i) z = 0 ↔ ∃ t : ℝ, z = t • alphaVector) := by
  apply local_quadratic_kernel (localCache i) alphaVector (localCache_isSymm i)
    ?_ (seed_local_data i).2.1 (seed_local_data i).2.2.1
    (seed_local_data i).2.2.2.1 z
  change alpha ^ 2 ≠ 0
  exact pow_ne_zero 2 alpha_certificate.2.1.ne'

lemma triangle_first_coordinate (lam : Fin 3 → ℝ) :
    ((castMatrix triangle).mulVec lam) 0 = ∑ a : Fin 3, lam a := by
  change (∑ a : Fin 3, (triangle 0 a : ℝ) * lam a) = ∑ a : Fin 3, lam a
  apply Finset.sum_congr rfl
  intro a _
  fin_cases a <;> norm_num [triangle]

lemma cone_group_local_kernel (i : Fin 7) (lam : Fin 3 → ℝ)
    (hlam : ∀ a, 0 ≤ lam a) :
    0 ≤ quad quadraticSeed (coneGroup i lam) ∧
      (quad quadraticSeed (coneGroup i lam) = 0 →
        ∃ t : ℝ, 0 ≤ t ∧ coneGroup i lam = t • seedColumn i) := by
  have hk := cone_local_kernel i ((castMatrix triangle).mulVec lam)
  constructor
  · rw [cone_group_quad]
    exact hk.1
  · intro hz
    rw [cone_group_quad] at hz
    obtain ⟨t, ht⟩ := hk.2.mp hz
    have htval : (∑ a : Fin 3, lam a) = t := by
      have h0 := congrFun ht 0
      simpa [triangle_first_coordinate, alphaVector] using h0
    have ht0 : 0 ≤ t := by
      rw [← htval]
      exact Finset.sum_nonneg (fun a _ => hlam a)
    refine ⟨t, ht0, ?_⟩
    rw [coneGroup, local_generator_sum, ht, Matrix.mulVec_smul]
    rfl

lemma seedColumn_quad_zero (i : Fin 7) : quad quadraticSeed (seedColumn i) = 0 := by
  rw [seedColumn, cone_quad_mulVec]
  change quad (localForm i) alphaVector = 0
  rw [← (seed_local_data i).1, quad_eq_dotProduct,
    (seed_local_data i).2.1, dotProduct_zero]

#print axioms cone_group_local_kernel
#assert_trust kernel cone_group_local_kernel
#print axioms seedColumn_quad_zero
#assert_trust kernel seedColumn_quad_zero

end NLA.PF03
