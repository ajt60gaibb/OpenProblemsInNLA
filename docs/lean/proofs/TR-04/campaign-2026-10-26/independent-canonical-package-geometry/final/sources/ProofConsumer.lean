import FullSolution
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace IndependentCanonicalProofGeometry
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

theorem literal_uniform_program :
  ∃ P : Program,∃ C k : ℕ,1≤C ∧
    ∀ S : Shape,∀ r : Ranks S,(∀ j,1≤r j) → ∀ A : Tensor S,
      (∃ trace : Trace P,LegalTrace P (Start P S r A) trace) ∧
      ∀ trace : Trace P,LegalTrace P (Start P S r A) trace →
        ∃ t : ℕ,∃ X : Tensor S,
          Returns P S (trace.state t) X ∧ CostThrough P trace t≤C*Size S r^k ∧
          Feasible S r X ∧
          (0<Optimum S r A → FrobeniusSq S A X<((S.order : ℝ)-1)*Optimum S r A) ∧
          (Optimum S r A=0 → X=A) := NLA.TR04.target

theorem literal_count {n₁ t k : ℕ} (ht : t≤n₁) (hk : k≤t) : k≤n₁ :=
  candidate_count_le_first_mode ht hk

theorem literal_cyclic {n₁ t : ℕ} (ht : t≤n₁) : t≤n₁ :=
  cyclic_window_count_le_first_mode ht

#assert_trust kernel NLA.TR04.target
#assert_trust kernel candidate_count_le_first_mode
#assert_trust kernel cyclic_window_count_le_first_mode
#assert_trust kernel literal_uniform_program
#assert_trust kernel literal_count
#assert_trust kernel literal_cyclic
#print axioms NLA.TR04.target
#print axioms candidate_count_le_first_mode
#print axioms cyclic_window_count_le_first_mode
#print axioms literal_uniform_program
#print axioms literal_count
#print axioms literal_cyclic
end IndependentCanonicalProofGeometry
