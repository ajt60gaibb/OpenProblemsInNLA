import NLA.Proofs.RA10.CustomPSDMathlibBridge
import Mathlib.Tactic.Ring

/-! A singular-safe replacement for the Schur-complement step of source
Lemma 2. Its two block-energy equations are explicit hypotheses; the passage
from an actual ridge eigenvector is proved separately in RidgeCompressionEnergy.
No invertibility or limiting argument is needed for this mass estimate. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open Matrix

namespace NLA.Proofs.RA10

/-- Evaluate positivity at `μ • u + w`. In the intended application u and w
are the selected and complementary components of a ridge eigenvector. -/
theorem ridgeCompression_complement_mass_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (u w : Fin n → ℝ) {s μ : ℝ} (hs : 0 < s) (hμ : 0 < μ)
    (hcross : u ⬝ᵥ (A *ᵥ w) = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)))
    (hbottom : w ⬝ᵥ (A *ᵥ w) =
      μ * s * ((u ⬝ᵥ u) - (w ⬝ᵥ w)) + μ ^ 2 * (u ⬝ᵥ (A *ᵥ u))) :
    w ⬝ᵥ w ≤ (1 - 2 * μ) * (u ⬝ᵥ u) := by
  have ht : A.transpose = A := Matrix.isHermitian_iff_isSymm.mp hA.1
  have hsym : w ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ w) := by
    simpa only [ht] using Matrix.dotProduct_transpose_mulVec A w u
  have hp := hA.dotProduct_mulVec_nonneg (μ • u + w)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hsym] at hp
  rw [hcross, hbottom] at hp
  have hprod : 0 ≤ (μ * s) * ((1 - 2 * μ) * (u ⬝ᵥ u) - (w ⬝ᵥ w)) := by
    nlinarith [hp]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod (mul_pos hμ hs))

/-- Source (5), from the block-energy equations without assuming H invertible. -/
theorem ridgeCompression_selected_mass_ge {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (u w : Fin n → ℝ) {s μ : ℝ} (hs : 0 < s) (hμ : 0 < μ)
    (hμ1 : μ < 1)
    (hcross : u ⬝ᵥ (A *ᵥ w) = -μ * (s * (u ⬝ᵥ u) + u ⬝ᵥ (A *ᵥ u)))
    (hbottom : w ⬝ᵥ (A *ᵥ w) =
      μ * s * ((u ⬝ᵥ u) - (w ⬝ᵥ w)) + μ ^ 2 * (u ⬝ᵥ (A *ᵥ u)))
    (hunit : (u ⬝ᵥ u) + (w ⬝ᵥ w) = 1) :
    1 / (2 * (1 - μ)) ≤ u ⬝ᵥ u := by
  have hmass := ridgeCompression_complement_mass_le hA u w hs hμ hcross hbottom
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (sub_pos.mpr hμ1))).mpr
  nlinarith

#assert_trust kernel ridgeCompression_complement_mass_le
#assert_trust kernel ridgeCompression_selected_mass_ge
#print axioms ridgeCompression_selected_mass_ge

end NLA.Proofs.RA10
