import NLA.Proofs.TR14.BinaryMomentUnitInverse
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The actual inverse polynomial in the least-apolar quotient. Its low
moment annihilation and coprimality are derived from the existing unit inverse. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- A quotient unit has a nonzero remainder below the modulus degree, with
no common root with the modulus. -/
theorem binary_unit_remainder (g : ℂ[X]) (hg : g.Monic)
    (hr : 0 < g.natDegree) (u c : AdjoinRoot g) (huc : u * c = 1) :
    let b := AdjoinRoot.modByMonicHom hg c
    b ≠ 0 ∧ b.natDegree < g.natDegree ∧ IsCoprime b g := by
  let : Nontrivial (AdjoinRoot g) :=
    AdjoinRoot.nontrivial g (ne_of_gt (natDegree_pos_iff_degree_pos.mp hr))
  let b := AdjoinRoot.modByMonicHom hg c
  have hmk : AdjoinRoot.mk g b = c := AdjoinRoot.mk_leftInverse hg c
  have hb0 : b ≠ 0 := by
    intro hz
    have hc0 : c = 0 := by simpa [hz] using hmk.symm
    rw [hc0, mul_zero] at huc
    exact zero_ne_one huc
  have hdegree : b.natDegree < g.natDegree := by
    induction c using AdjoinRoot.induction_on with
    | ih p =>
      exact natDegree_modByMonic_lt p hg (by
        intro h
        rw [h, natDegree_one] at hr
        omega)
  refine ⟨hb0, hdegree, ?_⟩
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ b g).mpr
  intro α
  by_cases hga : g.eval α = 0
  · left
    let φ : AdjoinRoot g →+* ℂ :=
      AdjoinRoot.lift (RingHom.id ℂ) α (by simpa using hga)
    have heq := congrArg φ huc
    have hcb : φ c = b.eval α := by
      rw [← hmk, AdjoinRoot.lift_mk]
      simp
    have hunit : φ u * b.eval α = 1 := by
      simpa only [map_mul, map_one, hcb] using heq
    have : b.eval α ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hunit
      exact zero_ne_one hunit
    simpa using this
  · right
    simpa using hga

/-- The inverse representer annihilates all powers below the top coefficient.
All conclusions concern the actual quotient and moment functional. -/
theorem binary_inverse_polynomial {D : ℕ}
    (h : Fin (D + 1) → ℂ) (hh : h ≠ 0) (g : ℂ[X])
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree) (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ D, d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    ∃ b : ℂ[X], b ≠ 0 ∧ b.natDegree < g.natDegree ∧ IsCoprime b g ∧
      ∀ j : ℕ, j < g.natDegree - 1 →
        quotientMomentFunctional h g hg hrD
          ((AdjoinRoot.root g) ^ j * AdjoinRoot.mk g b) = 0 := by
  obtain ⟨u, c, huc, hrepr⟩ :=
    binaryMomentUnitInverse h hh g hg hrPos hrD hAp hmin
  let b := AdjoinRoot.modByMonicHom hg c
  have hb := binary_unit_remainder g hg (by omega) u c huc
  refine ⟨b, hb.1, hb.2.1, hb.2.2, ?_⟩
  intro j hj
  have hmk : AdjoinRoot.mk g b = c := AdjoinRoot.mk_leftInverse hg c
  rw [hmk, hrepr]
  have heq : u * ((AdjoinRoot.root g) ^ j * c) = (AdjoinRoot.root g) ^ j := by
    calc
      u * ((AdjoinRoot.root g) ^ j * c) = (u * c) * (AdjoinRoot.root g) ^ j := by ring
      _ = (AdjoinRoot.root g) ^ j := by rw [huc, one_mul]
  rw [heq]
  exact binaryTopRemainder_lower_pow g hg (by omega) j hj

#assert_trust kernel binary_unit_remainder
#assert_trust kernel binary_inverse_polynomial
#print axioms binary_inverse_polynomial

end
end NLA.Proofs.TR14
