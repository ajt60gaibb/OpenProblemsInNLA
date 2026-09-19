import NLA.NR04.SliceRecombination
import LeanCert.Tactic.Verification

/-!
Positive reciprocal-height certificates for actual crossing diagonals.
Original NR04 mathematics: Matthew J. Colbrook, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
These internal identities do not prove the missing planar order theorem.
-/

namespace NLA.NR04

lemma slice_cross_reciprocal_rescale {N : ℕ} (a b : ℝ)
    (u v : Fin N → ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 / a + 1 / b) • sliceCrossPoint a b u v =
      (1 / a) • u + (1 / b) • v := by
  funext i
  simp only [sliceCrossPoint, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt (add_pos ha hb)] <;> ring

/-- Mathlib's open segments include the singleton case, so this algebraic
certificate needs no distinctness assumption. The geometric application
separately supplies distinct endpoints. -/
lemma slice_cross_diagonals_intersect {N : ℕ}
    (a0 a1 b0 b1 : ℝ) (u0 u1 v0 v1 : Fin N → ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb1 : 0 < b1) :
    (openSegment ℝ (sliceCrossPoint a0 b0 u0 v0) (sliceCrossPoint a1 b1 u1 v1) ∩
      openSegment ℝ (sliceCrossPoint a0 b1 u0 v1) (sliceCrossPoint a1 b0 u1 v0)).Nonempty := by
  let w00 := 1 / a0 + 1 / b0
  let w11 := 1 / a1 + 1 / b1
  let w01 := 1 / a0 + 1 / b1
  let w10 := 1 / a1 + 1 / b0
  have h00 : 0 < w00 := add_pos (one_div_pos.mpr ha0) (one_div_pos.mpr hb0)
  have h11 : 0 < w11 := add_pos (one_div_pos.mpr ha1) (one_div_pos.mpr hb1)
  have h01 : 0 < w01 := add_pos (one_div_pos.mpr ha0) (one_div_pos.mpr hb1)
  have h10 : 0 < w10 := add_pos (one_div_pos.mpr ha1) (one_div_pos.mpr hb0)
  let L := w00 + w11
  have hL : 0 < L := add_pos h00 h11
  have hsum : w01 + w10 = L := by dsimp [L, w00, w11, w01, w10]; ring
  have hcross :
      w00 • sliceCrossPoint a0 b0 u0 v0 + w11 • sliceCrossPoint a1 b1 u1 v1 =
      w01 • sliceCrossPoint a0 b1 u0 v1 + w10 • sliceCrossPoint a1 b0 u1 v0 := by
    dsimp [w00, w11, w01, w10]
    rw [slice_cross_reciprocal_rescale _ _ _ _ ha0 hb0,
      slice_cross_reciprocal_rescale _ _ _ _ ha1 hb1,
      slice_cross_reciprocal_rescale _ _ _ _ ha0 hb1,
      slice_cross_reciprocal_rescale _ _ _ _ ha1 hb0]
    abel
  let z := (w00 / L) • sliceCrossPoint a0 b0 u0 v0 +
    (w11 / L) • sliceCrossPoint a1 b1 u1 v1
  refine ⟨z, ?_, ?_⟩
  · refine ⟨w00 / L, w11 / L, div_pos h00 hL, div_pos h11 hL, ?_, rfl⟩
    rw [← add_div]
    exact div_self (ne_of_gt hL)
  · refine ⟨w01 / L, w10 / L, div_pos h01 hL, div_pos h10 hL, ?_, ?_⟩
    · rw [← add_div, hsum, div_self (ne_of_gt hL)]
    · calc
        _ = (1 / L) • (w01 • sliceCrossPoint a0 b1 u0 v1 +
            w10 • sliceCrossPoint a1 b0 u1 v0) := by
          simp [smul_add, smul_smul, div_eq_mul_inv, mul_comm]
        _ = (1 / L) • (w00 • sliceCrossPoint a0 b0 u0 v0 +
            w11 • sliceCrossPoint a1 b1 u1 v1) := by rw [← hcross]
        _ = z := by simp [z, smul_add, smul_smul, div_eq_mul_inv, mul_comm]

#print axioms slice_cross_diagonals_intersect
#assert_trust kernel slice_cross_diagonals_intersect

end NLA.NR04
