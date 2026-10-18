import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import LeanCert.Tactic.Verification

/-!
# Local color bounds from distinct incident colors

Once lower-label conduits have their canonical colors, injectivity excludes
all smaller colors for the next conduit. These finite facts do not presume
that a complete garden coloring is canonical.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

/-- If other slots already realize every color below `s`, the distinguished
slot of an injective color tuple must have color at least `s`. -/
theorem color_ge_of_covered_prefix {α : Type*} {d : ℕ}
    (colors : α → Fin d) (hinj : Function.Injective colors) (slot : α) (s : ℕ)
    (hcover : ∀ c : Fin s, ∃ a : α, a ≠ slot ∧ (colors a).val = c.val) :
    s ≤ (colors slot).val := by
  by_contra hnot
  have hlt : (colors slot).val < s := Nat.lt_of_not_ge hnot
  obtain ⟨a, ha, hcolor⟩ := hcover ⟨(colors slot).val, hlt⟩
  exact ha (hinj (Fin.ext hcolor))

/-- Distinct colors and canonical preceding sibling colors force the next
sibling's color to be no smaller than its zero-based slot. -/
theorem color_ge_slot_of_earlier_fixed {k d : ℕ} (colors : Fin k → Fin d)
    (hinj : Function.Injective colors) (slot : Fin k)
    (hprior : ∀ a : Fin k, a < slot → (colors a).val = a.val) :
    slot.val ≤ (colors slot).val := by
  apply color_ge_of_covered_prefix colors hinj slot slot.val
  intro c
  let a : Fin k := ⟨c.val, Nat.lt_trans c.isLt slot.isLt⟩
  refine ⟨a, ?_, ?_⟩
  · exact ne_of_lt (show a < slot from c.isLt)
  · exact hprior a (show a < slot from c.isLt)

/-- At an ordinary node, input colors `0,...,k-1` exclude those colors from
the output cap, without a positivity or nonempty-arity assumption. -/
theorem outputColor_ge_arity {k d : ℕ} (output : Fin d) (inputs : Fin k → Fin d)
    (hinj : Function.Injective (Matrix.vecCons output inputs))
    (hinputs : ∀ i : Fin k, (inputs i).val = i.val) :
    k ≤ output.val := by
  apply color_ge_of_covered_prefix (Matrix.vecCons output inputs) hinj 0 k
  intro c
  refine ⟨c.succ, c.succ_ne_zero, ?_⟩
  simpa using hinputs c

#assert_trust kernel color_ge_of_covered_prefix
#assert_trust kernel color_ge_slot_of_earlier_fixed
#assert_trust kernel outputColor_ge_arity
#print axioms color_ge_slot_of_earlier_fixed
#print axioms outputColor_ge_arity

end NLA.Proofs.SP11
