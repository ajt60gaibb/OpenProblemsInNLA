import Mathlib.Data.Fin.Tuple.Basic
import LeanCert.Tactic.Verification

/-!
# Inserting a shared cap among ordered child colors

This reindexes one cap and `k` children into the augmented ordered predecessor
list.  It preserves injectivity; it introduces no fresh color or variable.
-/

namespace NLA.Proofs.SP11

variable {k : ℕ} {α : Type*}

/-- Place the cap at the insertion position, preserving the order of children. -/
def augmentedColors (p : Fin (k + 1)) (cap : α) (kids : Fin k → α) :
    Fin (k + 1) → α :=
  Fin.insertNth p cap kids

@[simp] theorem augmentedColors_at_cap (p : Fin (k + 1)) (cap : α)
    (kids : Fin k → α) : augmentedColors p cap kids p = cap := by
  exact Fin.insertNth_apply_same (α := fun _ => α) p cap kids

@[simp] theorem augmentedColors_at_child (p : Fin (k + 1)) (cap : α)
    (kids : Fin k → α) (s : Fin k) :
    augmentedColors p cap kids (p.succAbove s) = kids s := by
  exact Fin.insertNth_apply_succAbove (α := fun _ => α) p cap kids s

/-- The augmented tuple is exactly a permutation of the cap-first tuple. -/
theorem augmentedColors_injective (p : Fin (k + 1)) (cap : α)
    (kids : Fin k → α) (h : Function.Injective (Fin.cons cap kids)) :
    Function.Injective (augmentedColors p cap kids) := by
  intro r s hrs
  cases r using Fin.succAboveCases p with
  | x =>
    cases s using Fin.succAboveCases p with
    | x => rfl
    | p j =>
      have heq : (0 : Fin (k + 1)) = j.succ :=
        h (by simpa using hrs)
      exact False.elim (Fin.succ_ne_zero j heq.symm)
  | p i =>
    cases s using Fin.succAboveCases p with
    | x =>
      have heq : i.succ = (0 : Fin (k + 1)) :=
        h (by simpa using hrs)
      exact False.elim (Fin.succ_ne_zero i heq)
    | p j =>
      have heq : i.succ = j.succ := h (by simpa using hrs)
      exact congrArg p.succAbove (Fin.succ_injective k heq)

/-- Any augmented tuple is determined by its cap and the remaining entries. -/
theorem augmentedColors_reindex (p : Fin (k + 1)) (f : Fin (k + 1) → α) :
    augmentedColors p (f p) (fun s => f (p.succAbove s)) = f := by
  apply Fin.insertNth_eq_iff.mpr
  exact ⟨rfl, rfl⟩

/-- In particular, the canonical indexed colors are recovered at every slot. -/
theorem augmentedColors_castLE {d : ℕ} (hkd : k + 1 ≤ d) (p : Fin (k + 1)) :
    augmentedColors p (p.castLE hkd)
      (fun s => (p.succAbove s).castLE hkd) = fun r => r.castLE hkd := by
  exact augmentedColors_reindex p (fun r => r.castLE hkd)

#assert_trust kernel augmentedColors_injective
#assert_trust kernel augmentedColors_castLE

end NLA.Proofs.SP11
