import NLA.PF03.CubicFiniteArithmetic

/-!
C05: the literal quadratic seed is symmetric and has trace zero. Only exact
rational cubic coordinates are checked; evaluation then gives the real facts.
Original mathematics and seed: Sidney Holden, Center for Computational Biology,
Flatiron Institute, Simons Foundation. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem seed_quadratic_symmetry_coordinates : ∀ r s : Fin 7, ∀ k : Fin 3,
    RawData.quadraticMatrix s r k = RawData.quadraticMatrix r s k := by
  intro r s k
  fin_cases r <;> fin_cases s <;> fin_cases k <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem seed_quadratic_trace_coordinates : ∀ k : Fin 3,
    (∑ i : Fin 7, RawData.quadraticMatrix i i) k = 0 := by
  decide +kernel

/-- C05: exact symmetry and zero trace of the defined real quadratic matrix. -/
theorem seed_quadratic_form :
    quadraticSeed.IsSymm ∧ Matrix.trace quadraticSeed = 0 := by
  constructor
  · apply Matrix.IsSymm.ext
    intro r s
    change cubicEval (RawData.quadraticMatrix s r) =
      cubicEval (RawData.quadraticMatrix r s)
    apply congrArg cubicEval
    funext k
    exact seed_quadratic_symmetry_coordinates r s k
  · calc
      Matrix.trace quadraticSeed =
          ∑ i : Fin 7, cubicEval (RawData.quadraticMatrix i i) := rfl
      _ = cubicEval (∑ i : Fin 7, RawData.quadraticMatrix i i) :=
        (cubicEval_finset_sum Finset.univ (fun i : Fin 7 => RawData.quadraticMatrix i i)).symm
      _ = cubicEval (0 : Cubic) := by
        apply congrArg cubicEval
        funext k
        exact seed_quadratic_trace_coordinates k
      _ = 0 := by simp [cubicEval]

#print axioms seed_quadratic_form
#assert_trust kernel seed_quadratic_form

end NLA.PF03
