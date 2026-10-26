import NLA.Proofs.TR14.BinaryFrobeniusRepresenter
import Mathlib.RingTheory.AdjoinRoot

/-! The concrete top-remainder functional in the normalized least-apolar
quotient. Its Frobenius theorem is developed from this exact coefficient model. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
noncomputable section

/-- The coefficient of `t^(r-1)` in the unique representative of degree below
`r = g.natDegree` for a monic polynomial `g`. -/
def binaryTopRemainder (g : Polynomial ℂ) (hg : g.Monic)
    (hr : 0 < g.natDegree) : AdjoinRoot g →ₗ[ℂ] ℂ where
  toFun a := ((AdjoinRoot.powerBasisAux' hg).repr a)
    ⟨g.natDegree - 1, by omega⟩
  map_add' := by
    intro a b
    simp only [map_add, Finsupp.add_apply]
  map_smul' := by
    intro c a
    simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply]

/-- The basis coefficient is exactly the coefficient of the polynomial
remainder, not an arbitrary coordinate functional. -/
theorem binaryTopRemainder_eq_mod_coeff (g : Polynomial ℂ) (hg : g.Monic)
    (hr : 0 < g.natDegree) (a : AdjoinRoot g) :
    binaryTopRemainder g hg hr a =
      (AdjoinRoot.modByMonicHom hg a).coeff (g.natDegree - 1) := by
  change ((AdjoinRoot.powerBasisAux' hg).repr a)
    ⟨g.natDegree - 1, by omega⟩ =
      (AdjoinRoot.modByMonicHom hg a).coeff (g.natDegree - 1)
  exact AdjoinRoot.powerBasisAux'_repr_apply_to_fun hg a _

/-- The top power has coefficient one. -/
theorem binaryTopRemainder_top_pow (g : Polynomial ℂ) (hg : g.Monic)
    (hr : 0 < g.natDegree) :
    binaryTopRemainder g hg hr
      ((AdjoinRoot.root g) ^ (g.natDegree - 1)) = 1 := by
  let i : Fin g.natDegree := ⟨g.natDegree - 1, by omega⟩
  change ((AdjoinRoot.powerBasisAux' hg).repr
    ((AdjoinRoot.root g) ^ i.val)) i = 1
  have hpow : (AdjoinRoot.powerBasisAux' hg) i =
      (AdjoinRoot.root g) ^ i.val :=
    (AdjoinRoot.powerBasis' hg).basis_eq_pow i
  rw [← hpow]
  simp

/-- Every lower power has zero top coefficient. -/
theorem binaryTopRemainder_lower_pow (g : Polynomial ℂ) (hg : g.Monic)
    (hr : 0 < g.natDegree) (j : ℕ) (hj : j < g.natDegree - 1) :
    binaryTopRemainder g hg hr ((AdjoinRoot.root g) ^ j) = 0 := by
  let i : Fin g.natDegree := ⟨j, by omega⟩
  let top : Fin g.natDegree := ⟨g.natDegree - 1, by omega⟩
  have hitop : i ≠ top := by
    intro heq
    have := congrArg Fin.val heq
    exact (Nat.ne_of_lt hj) this
  change ((AdjoinRoot.powerBasisAux' hg).repr
    ((AdjoinRoot.root g) ^ i.val)) top = 0
  have hpow : (AdjoinRoot.powerBasisAux' hg) i =
      (AdjoinRoot.root g) ^ i.val :=
    (AdjoinRoot.powerBasis' hg).basis_eq_pow i
  rw [← hpow]
  simp [hitop]

#assert_trust kernel binaryTopRemainder
#assert_trust kernel binaryTopRemainder_eq_mod_coeff
#assert_trust kernel binaryTopRemainder_top_pow
#assert_trust kernel binaryTopRemainder_lower_pow
#print axioms binaryTopRemainder_eq_mod_coeff

end
end NLA.Proofs.TR14
