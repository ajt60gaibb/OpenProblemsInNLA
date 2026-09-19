/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted source development by Codex coordinator /root.

The four exact interfaces were reviewed by two independent nonauthors before
implementation; see STATEMENT-FREEZE.json. This is a helper for the MI27
relative-entropy representation, not a completed proof of the original target.
Original question: Audenaert and Kittaneh; analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. The pencil method is due to Peter E. Frenkel.
-/
import NLA.MI27.NegativeWeights
import NLA.MI27.NegativeCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c11_hermitian_quadratic_spectral {n : ℕ} (M : Mat n)
    (hM : M.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ (M *ᵥ v)).re =
      ∑ i : Fin n, hM.eigenvalues i *
        Complex.normSq (((hM.eigenvectorUnitary : Mat n)ᴴ *ᵥ v) i) := by
  let U : Mat n := hM.eigenvectorUnitary
  let d : Fin n → ℂ := fun i => (hM.eigenvalues i : ℂ)
  have hs : M = U * Matrix.diagonal d * Uᴴ := by
    convert! hM.spectral_theorem using 1 <;> rfl
  have hq : star v ⬝ᵥ ((U * Matrix.diagonal d * Uᴴ) *ᵥ v) =
      star (Uᴴ *ᵥ v) ⬝ᵥ (Matrix.diagonal d *ᵥ (Uᴴ *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  calc
    (star v ⬝ᵥ (M *ᵥ v)).re =
        (star (Uᴴ *ᵥ v) ⬝ᵥ (Matrix.diagonal d *ᵥ (Uᴴ *ᵥ v))).re := by rw [hs, hq]
    _ = _ := by
      simp only [dotProduct, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.mulVec_diagonal, Pi.star_apply, d, Complex.star_def]
      rw [mul_left_comm, ← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, U]

lemma c11_negativeCount_congruence_le {n : ℕ} (hn : 1 ≤ n) (M S : Mat n)
    (hM : M.IsHermitian) :
    c11_negativeCount (Sᴴ * M * S) ≤ c11_negativeCount M := by
  let N : Mat n := Sᴴ * M * S
  have hN : N.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul S hM
  let U : Mat n := hM.eigenvectorUnitary
  let V : Mat n := hN.eigenvectorUnitary
  let T : Mat n := Uᴴ * S * V
  have hV : Vᴴ * V = 1 := by
    exact Unitary.coe_star_mul_self hN.eigenvectorUnitary
  have hform : ∀ w : Fin n → ℂ,
      (∑ j : Fin n, hN.eigenvalues j * Complex.normSq (w j)) =
        ∑ i : Fin n, hM.eigenvalues i * Complex.normSq ((T *ᵥ w) i) := by
    intro w
    have hspecN := c11_hermitian_quadratic_spectral N hN (V *ᵥ w)
    change (star (V *ᵥ w) ⬝ᵥ (N *ᵥ (V *ᵥ w))).re =
      ∑ j : Fin n, hN.eigenvalues j * Complex.normSq ((Vᴴ *ᵥ (V *ᵥ w)) j) at hspecN
    have hVw : Vᴴ *ᵥ (V *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec]
    rw [hVw] at hspecN
    have hcov : star (V *ᵥ w) ⬝ᵥ (N *ᵥ (V *ᵥ w)) =
        star (S *ᵥ (V *ᵥ w)) ⬝ᵥ (M *ᵥ (S *ᵥ (V *ᵥ w))) := by
      dsimp only [N]
      simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]
    have hspecM := c11_hermitian_quadratic_spectral M hM (S *ᵥ (V *ᵥ w))
    change (star (S *ᵥ (V *ᵥ w)) ⬝ᵥ (M *ᵥ (S *ᵥ (V *ᵥ w)))).re =
      ∑ i : Fin n, hM.eigenvalues i * Complex.normSq ((Uᴴ *ᵥ (S *ᵥ (V *ᵥ w))) i) at hspecM
    have hTw : Uᴴ *ᵥ (S *ᵥ (V *ᵥ w)) = T *ᵥ w := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [hTw] at hspecM
    calc
      (∑ j : Fin n, hN.eigenvalues j * Complex.normSq (w j)) =
          (star (V *ᵥ w) ⬝ᵥ (N *ᵥ (V *ᵥ w))).re := hspecN.symm
      _ = (star (S *ᵥ (V *ᵥ w)) ⬝ᵥ (M *ᵥ (S *ᵥ (V *ᵥ w)))).re :=
        congrArg Complex.re hcov
      _ = ∑ i : Fin n, hM.eigenvalues i * Complex.normSq ((T *ᵥ w) i) := hspecM
  have hc := c11_negative_weights_card_le hM.eigenvalues hN.eigenvalues T hform
  have card_count (A : Mat n) (hA : A.IsHermitian) :
      c11_negativeCount A = (Fintype.card {i : Fin n // hA.eigenvalues i < 0} : ℝ) := by
    rw [c11_negativeCount_spectral hn A hA, Fintype.card_subtype]
    simp [Finset.sum_ite]
  rw [card_count _ hN, card_count _ hM]
  exact_mod_cast hc

lemma c11_negativeCount_congruence {n : ℕ} (hn : 1 ≤ n) (M S : Mat n)
    (hM : M.IsHermitian) (hS : IsUnit S) :
    c11_negativeCount (Sᴴ * M * S) = c11_negativeCount M := by
  apply le_antisymm (c11_negativeCount_congruence_le hn M S hM)
  have hN := Matrix.isHermitian_conjTranspose_mul_mul S hM
  have hi := c11_negativeCount_congruence_le hn (Sᴴ * M * S) S⁻¹ hN
  letI := hS.invertible
  have hSH : IsUnit Sᴴ := by
    simpa only [Matrix.star_eq_conjTranspose] using hS.star
  letI := hSH.invertible
  have he : (S⁻¹)ᴴ * (Sᴴ * M * S) * S⁻¹ = M := by
    rw [Matrix.conjTranspose_nonsing_inv]
    simp only [← mul_assoc, Matrix.inv_mul_of_invertible, one_mul,
      Matrix.mul_inv_cancel_right_of_invertible]
  rwa [he] at hi

#print axioms c11_hermitian_quadratic_spectral
#assert_trust kernel c11_hermitian_quadratic_spectral
#print axioms c11_negativeCount_congruence_le
#assert_trust kernel c11_negativeCount_congruence_le
#print axioms c11_negativeCount_congruence
#assert_trust kernel c11_negativeCount_congruence

end NLA.MI27
