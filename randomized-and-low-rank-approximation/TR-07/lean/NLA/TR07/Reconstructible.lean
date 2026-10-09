import NLA.TR07.Witnesses

/-! The reservoir event is defined by the actual span of its sampled columns. -/
noncomputable section
namespace NLA.TR07

def Reconstructible {ι : Type*} {k : ℕ} (center : Vec k) (reservoir : ι → Vec k) (ε : ℝ) : Prop :=
  ∃ y : Vec k, y ∈ Submodule.span ℝ (Set.range reservoir) ∧ ‖center - y‖ ≤ ε

end NLA.TR07
