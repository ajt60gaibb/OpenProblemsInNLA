import NLA.Proofs.SP14.BaseBlockCharpoly

/-!
A finite matrix bridge for the SP-14 base symbol. Once the upper Toeplitz
coefficient matrix `G` is proved to satisfy `G² = I + U`, selecting its
rows and columns gives the unit lower-bidiagonal block exactly.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The upper unit shift on the `m+1` even-coordinate indices. -/
def baseUpperShift (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
  fun i j => if j.val = i.val + 1 then 1 else 0

/-- The product of the selected rectangular blocks of a square-root
coefficient matrix is the explicit unit lower-bidiagonal block. -/
theorem base_selected_product (m : ℕ)
    (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hG : G * G = 1 + baseUpperShift m) :
    (G.submatrix Fin.castSucc id) * (G.submatrix id Fin.succ) = baseBlock m := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ =>
    M (Fin.castSucc i) (Fin.succ j)) hG
  by_cases hdiag : i.val = j.val
  · have hsub : i.val ≠ j.val + 1 := by omega
    simpa [Matrix.mul_apply, baseUpperShift, baseBlock, Matrix.one_apply,
      Fin.ext_iff, hdiag, hsub] using h
  · have hdiag' : j.val ≠ i.val := Ne.symm hdiag
    simpa [Matrix.mul_apply, baseUpperShift, baseBlock, Matrix.one_apply,
      Fin.ext_iff, hdiag, hdiag'] using h

#assert_trust kernel base_selected_product
#print axioms base_selected_product

end NLA.Proofs.SP14
