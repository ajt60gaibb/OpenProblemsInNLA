import NLA.NR04.Definitions
import LeanCert.Tactic.Verification

/-!
The nine-rectangle integer obstruction. No ordering or geometric theorem is
assumed to have been proved by this module. Original NR04 mathematics:
Matthew J. Colbrook, University of Cambridge. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; Codex assistance. The statement was sealed before this body.
-/

namespace NLA.NR04

/-- The three row-pairs and three column-pairs cannot all have odd crossing
parity. Arrays are arbitrary integers; no finite permutation search is used. -/
theorem nine_rectangle_parities_impossible
    (R C : Fin 3 → Fin 3 → Fin 3 → ℤ)
    (h : ∀ i k j l : Fin 3, i < k → j < l →
      Odd (2 + R i j l - R k j l + C j i k - C l i k)) : False := by
  obtain ⟨a, ha⟩ := h 0 1 0 1 (by decide) (by decide)
  obtain ⟨b, hb⟩ := h 0 1 0 2 (by decide) (by decide)
  obtain ⟨c, hc⟩ := h 0 1 1 2 (by decide) (by decide)
  obtain ⟨d, hd⟩ := h 0 2 0 1 (by decide) (by decide)
  obtain ⟨e, he⟩ := h 0 2 0 2 (by decide) (by decide)
  obtain ⟨f, hf⟩ := h 0 2 1 2 (by decide) (by decide)
  obtain ⟨g, hg⟩ := h 1 2 0 1 (by decide) (by decide)
  obtain ⟨i, hi⟩ := h 1 2 0 2 (by decide) (by decide)
  obtain ⟨j, hj⟩ := h 1 2 1 2 (by decide) (by decide)
  omega

#print axioms nine_rectangle_parities_impossible
#assert_trust kernel nine_rectangle_parities_impossible

end NLA.NR04
