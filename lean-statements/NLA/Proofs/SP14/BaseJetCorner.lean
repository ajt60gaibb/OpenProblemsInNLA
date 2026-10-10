import NLA.Proofs.SP14.BaseJetTriangular

/-!
Generic finite cofactor identity for the SP-14 odd-pencil jet quotient.
This identifies the selected rectangular-block characteristic polynomial
with a corner adjugate entry. The actual base Fourier and explicit corner
formula are separate obligations.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem pencil_minor (m : ℕ)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (t : ℂ) :
    (G * G - (t + 1) • baseUpperShift m).submatrix Fin.castSucc Fin.succ =
      (G.submatrix Fin.castSucc id) * (G.submatrix id Fin.succ) -
        Matrix.scalar (Fin m) (t + 1) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.mul_apply]
  have hsum :
      (∑ k : Fin (m + 1), G (Fin.castSucc i) k * G k (Fin.succ j)) =
      ∑ k : Fin (m + 1),
        (G.submatrix Fin.castSucc id) i k *
          (G.submatrix id Fin.succ) k j := by
    rfl
  rw [hsum]
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  by_cases hij : i = j
  · subst j
    simp [baseUpperShift, Matrix.scalar_apply]
  · have hval : j.val ≠ i.val := by
      intro heq
      exact hij (Fin.ext (by omega))
    simp [baseUpperShift, Matrix.scalar_apply, hij, hval]

/-- The characteristic polynomial of the selected `C*B` block at `1+t`
is the upper-right adjugate corner of the exact square pencil. -/
theorem selected_charpoly_eq_pencil_adjugate (m : ℕ)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (t : ℂ) :
    ((G.submatrix Fin.castSucc id * G.submatrix id Fin.succ).charpoly).eval (t + 1) =
      (G * G - (t + 1) • baseUpperShift m).adjugate 0 (Fin.last m) := by
  let A := G * G - (t + 1) • baseUpperShift m
  let B := (G.submatrix Fin.castSucc id) * (G.submatrix id Fin.succ)
  have hminor : A.submatrix Fin.castSucc Fin.succ = B - Matrix.scalar (Fin m) (t + 1) :=
    pencil_minor m G t
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.succAbove_last, Fin.succAbove_zero]
  rw [hminor]
  have hneg : B - Matrix.scalar (Fin m) (t + 1) =
      -(Matrix.scalar (Fin m) (t + 1) - B) := by abel
  rw [hneg, Matrix.det_neg]
  rw [Matrix.eval_charpoly]
  simp [B, ← mul_assoc, ← pow_two, ← pow_mul]

#assert_trust kernel selected_charpoly_eq_pencil_adjugate
#print axioms selected_charpoly_eq_pencil_adjugate

end NLA.Proofs.SP14
