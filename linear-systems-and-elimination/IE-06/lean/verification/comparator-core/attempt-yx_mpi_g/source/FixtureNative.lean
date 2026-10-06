import Lean.Elab.Tactic.Decide
def meaning : Prop := (1 : Nat) = 1
theorem claim : meaning := by unfold meaning; native_decide
