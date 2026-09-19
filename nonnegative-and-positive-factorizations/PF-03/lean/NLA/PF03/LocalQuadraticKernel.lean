import NLA.PF03.Definitions
import LeanCert.Tactic

/-!
C07: remove the component in the given kernel direction and complete a square
in the remaining two coordinates. The exact kernel equation, symmetry and
both positive minors are used. No rank/eigenvalue oracle or numeric search.

Original mathematics: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance. Author: /root.
-/

set_option autoImplicit false
open scoped BigOperators Classical Matrix
noncomputable section
namespace NLA.PF03

lemma quad_eq_dotProduct {d : ℕ} (H : RMat d d) (z : Fin d → ℝ) :
    quad H z = z ⬝ᵥ H.mulVec z := by
  simp only [quad, bilinear, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private lemma quad_sub_kernel {d : ℕ} (H : RMat d d) (v z : Fin d → ℝ)
    (hH : H.IsSymm) (hHv : H.mulVec v = 0) (t : ℝ) :
    quad H (z - t • v) = quad H z := by
  have hHT : Hᵀ = H := hH
  have hleft : v ⬝ᵥ H.mulVec z = 0 := by
    calc
      v ⬝ᵥ H.mulVec z = z ⬝ᵥ H.mulVec v := by
        simpa only [hHT] using Matrix.dotProduct_transpose_mulVec H v z
      _ = 0 := by rw [hHv, dotProduct_zero]
  simp only [quad_eq_dotProduct, Matrix.mulVec_sub, Matrix.mulVec_smul,
    hHv, smul_zero, sub_zero, sub_dotProduct, smul_dotProduct, hleft]

private lemma positive_binary_form (a b c u w : ℝ)
    (ha : 0 < a) (hdet : 0 < a * c - b ^ 2) :
    0 ≤ a * u ^ 2 + 2 * b * u * w + c * w ^ 2 ∧
      (a * u ^ 2 + 2 * b * u * w + c * w ^ 2 = 0 ↔ u = 0 ∧ w = 0) := by
  let q := a * u ^ 2 + 2 * b * u * w + c * w ^ 2
  change 0 ≤ q ∧ (q = 0 ↔ u = 0 ∧ w = 0)
  have hid : a * q = (a * u + b * w) ^ 2 + (a * c - b ^ 2) * w ^ 2 := by
    dsimp [q]
    ring
  have hprod : 0 ≤ (a * c - b ^ 2) * w ^ 2 := mul_nonneg hdet.le (sq_nonneg w)
  constructor
  · exact nonneg_of_mul_nonneg_left (by rw [mul_comm q a, hid]; positivity) ha
  · constructor
    · intro hq
      have hsum : (a * u + b * w) ^ 2 + (a * c - b ^ 2) * w ^ 2 = 0 := by
        rw [← hid, hq, mul_zero]
      have hpzero : (a * c - b ^ 2) * w ^ 2 = 0 := by
        apply le_antisymm _ hprod
        linarith only [hsum, sq_nonneg (a * u + b * w)]
      have hw : w = 0 := sq_eq_zero_iff.mp
        ((mul_eq_zero.mp hpzero).resolve_left hdet.ne')
      refine ⟨?_, hw⟩
      have hu : a * u ^ 2 = 0 := by simpa [q, hw] using hq
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hu).resolve_left ha.ne')
    · rintro ⟨hu, hw⟩
      simp [q, hu, hw]

theorem local_quadratic_kernel (H : RMat 3 3) (v : Fin 3 → ℝ)
    (hH : H.IsSymm) (hv : v 2 ≠ 0) (hHv : H.mulVec v = 0)
    (h00 : 0 < H 0 0) (hdet : 0 < H 0 0 * H 1 1 - (H 0 1) ^ 2) :
    ∀ z : Fin 3 → ℝ, 0 ≤ quad H z ∧
      (quad H z = 0 ↔ ∃ t : ℝ, z = t • v) := by
  intro z
  let t : ℝ := z 2 / v 2
  let w : Fin 3 → ℝ := z - t • v
  have hw2 : w 2 = 0 := by
    change z 2 - (z 2 / v 2) * v 2 = 0
    rw [div_mul_cancel₀ _ hv, sub_self]
  have hwquad : quad H w =
      H 0 0 * (w 0) ^ 2 + 2 * H 0 1 * w 0 * w 1 + H 1 1 * (w 1) ^ 2 := by
    simp only [quad, bilinear, Fin.sum_univ_three, hw2,
      hH.apply 0 1, zero_mul, mul_zero, add_zero, zero_add]
    ring
  have hqeq : quad H z =
      H 0 0 * (w 0) ^ 2 + 2 * H 0 1 * w 0 * w 1 + H 1 1 * (w 1) ^ 2 :=
    (quad_sub_kernel H v z hH hHv t).symm.trans hwquad
  have hbinary := positive_binary_form (H 0 0) (H 0 1) (H 1 1) (w 0) (w 1) h00 hdet
  refine ⟨hqeq ▸ hbinary.1, ?_⟩
  constructor
  · intro hz
    obtain ⟨hw0, hw1⟩ := hbinary.2.mp (hqeq ▸ hz)
    have hw : w = 0 := by
      funext i
      fin_cases i
      · exact hw0
      · exact hw1
      · exact hw2
    exact ⟨t, sub_eq_zero.mp hw⟩
  · rintro ⟨s, rfl⟩
    rw [quad_eq_dotProduct, Matrix.mulVec_smul, hHv, smul_zero, dotProduct_zero]

#print axioms local_quadratic_kernel
#assert_trust kernel local_quadratic_kernel

end NLA.PF03
