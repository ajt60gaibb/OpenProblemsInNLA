import NLA.Proofs.TR14.BinaryTopRemainder

/-! The top-remainder functional is Frobenius on the monic quotient. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
noncomputable section

/-- Multiplication by a suitable root power exposes the leading coefficient
of every nonzero quotient representative in the top remainder slot. -/
theorem binaryTopRemainder_frobenius (g : Polynomial ℂ) (hg : g.Monic)
    (hr : 0 < g.natDegree) :
    ∀ a : AdjoinRoot g,
      (∀ b : AdjoinRoot g,
        binaryTopRemainder g hg hr (a * b) = 0) → a = 0 := by
  intro a ha
  let p := AdjoinRoot.modByMonicHom hg a
  have hmk : AdjoinRoot.mk g p = a := AdjoinRoot.mk_leftInverse hg a
  by_contra hne
  have hp : p ≠ 0 := by
    intro h
    apply hne
    rw [← hmk, h]
    exact (AdjoinRoot.mk g).map_zero
  have hg1 : g ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp at this
    omega
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  have hpdef : p = q %ₘ g := AdjoinRoot.modByMonicHom_mk hg q
  have hpd : p.natDegree < g.natDegree := by
    rw [hpdef]
    exact Polynomial.natDegree_modByMonic_lt q hg hg1
  let k := g.natDegree - 1 - p.natDegree
  have hdk : p.natDegree + k = g.natDegree - 1 := by
    dsimp [k]
    omega
  have hdprod : (p * Polynomial.X ^ k).degree < g.degree := by
    rw [Polynomial.degree_mul_X_pow, Polynomial.degree_eq_natDegree hp,
      Polynomial.degree_eq_natDegree hg.ne_zero]
    rw [← Nat.cast_add, hdk]
    exact_mod_cast (show g.natDegree - 1 < g.natDegree by omega)
  have hmod : (p * Polynomial.X ^ k) %ₘ g = p * Polynomial.X ^ k :=
    (Polynomial.modByMonic_eq_self_iff hg).mpr hdprod
  have htop : binaryTopRemainder g hg hr
      (AdjoinRoot.mk g q * (AdjoinRoot.root g) ^ k) = p.leadingCoeff := by
    rw [binaryTopRemainder_eq_mod_coeff]
    have heq : AdjoinRoot.mk g q * (AdjoinRoot.root g) ^ k =
        AdjoinRoot.mk g (p * Polynomial.X ^ k) := by
      have hqp : AdjoinRoot.mk g q = AdjoinRoot.mk g p :=
        (AdjoinRoot.mk_leftInverse hg (AdjoinRoot.mk g q)).symm
      rw [hqp, ← AdjoinRoot.mk_X, ← map_pow, ← map_mul]
    rw [heq, AdjoinRoot.modByMonicHom_mk, hmod, ← hdk,
      Polynomial.coeff_mul_X_pow]
    rfl
  have hzero := ha ((AdjoinRoot.root g) ^ k)
  rw [htop] at hzero
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp) hzero

#assert_trust kernel binaryTopRemainder_frobenius
#print axioms binaryTopRemainder_frobenius

end
end NLA.Proofs.TR14
