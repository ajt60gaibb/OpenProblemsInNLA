import NLA.IE21.SphereNet
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21
example (n : ℕ) (hn : 1 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : Finset (Space n), (∀ x ∈ C, ‖x‖ = 1) ∧
      (C.card : ℝ) ≤ (1 + 2 / δ) ^ n ∧
      ∀ x : Space n, ‖x‖ = 1 → ∃ y ∈ C, ‖x - y‖ ≤ δ := by
  exact sphere_net n hn δ hδ
end NLA.IE21
