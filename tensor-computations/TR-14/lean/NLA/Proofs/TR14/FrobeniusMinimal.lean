import NLA.Proofs.TR14.NormalizedQuotient

/-!
Conditional Frobenius nondegeneracy for the normalized moment quotient.
The proof expands a radical element in the power basis and uses the full
moment match to produce a forbidden lower-degree apolar vector. Global
projective chart transport and the TR-14 all-width target remain open.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Polynomial

namespace NLA.Proofs.TR14

/-- A monic least-degree apolar polynomial gives a nondegenerate moment
pairing on its exact quotient. No Frobenius condition is assumed. -/
theorem quotientMomentFunctional_frobenius {D : ℕ}
    (h : Fin (D + 1) → ℂ) (_hh : h ≠ 0) (g : Polynomial ℂ)
    (hg : g.Monic) (hrPos : 1 ≤ g.natDegree)
    (hrD : g.natDegree ≤ D)
    (hAp : IsApolar h g.natDegree hrD
      (fun i : Fin (g.natDegree + 1) => g.coeff i.val))
    (hmin : ∀ d : ℕ, ∀ hd : d ≤ D, d < g.natDegree →
      ∀ b : Fin (d + 1) → ℂ, IsApolar h d hd b → b = 0) :
    ∀ a : AdjoinRoot g,
      (∀ b : AdjoinRoot g,
        quotientMomentFunctional h g hg hrD (a * b) = 0) → a = 0 := by
  classical
  let r := g.natDegree
  let A := AdjoinRoot g
  let t : A := AdjoinRoot.root g
  let Λ := quotientMomentFunctional h g hg hrD
  let basis := (AdjoinRoot.powerBasis' hg).basis
  have hrEq : r - 1 + 1 = r := by omega
  have hd : r - 1 ≤ D := by omega
  have hrec : MonicMomentRecurrence h g :=
    monicMomentRecurrence_of_apolar h g hg hrD hAp
  have hall := quotientMomentFunctional_all h g hg hrD hrec
  intro a ha
  let coeff : Fin r → ℂ := fun i => (basis.repr a) i
  let bvec : Fin (r - 1 + 1) → ℂ := fun i => coeff (Fin.cast hrEq i)
  have hpow (i : Fin r) : basis i = t ^ i.val :=
    (AdjoinRoot.powerBasis' hg).basis_eq_pow i
  have hrepr : (∑ i : Fin r, coeff i • t ^ i.val) = a := by
    calc
      (∑ i : Fin r, coeff i • t ^ i.val) =
          ∑ i : Fin r, (basis.repr a i) • basis i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [coeff, hpow]
      _ = a := basis.sum_repr a
  have hbApolar : IsApolar h (r - 1) hd bvec := by
    apply funext
    intro j
    have hjbound : j.val ≤ D - (r - 1) := by have := j.isLt; omega
    have hzero := ha (t ^ j.val)
    have hsum :
        Λ (a * t ^ j.val) =
          ∑ i : Fin r, coeff i *
            h ⟨i.val + j.val, by have := i.isLt; omega⟩ := by
      conv_lhs => rw [← hrepr]
      simp only [Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_mul_assoc, map_smul, smul_eq_mul, ← pow_add]
      exact congrArg (fun z : ℂ => coeff i * z)
        (hall ⟨i.val + j.val, by have := i.isLt; omega⟩)
    have hsumZero :
        (∑ i : Fin r, coeff i *
          h ⟨i.val + j.val, by have := i.isLt; omega⟩) = 0 := by
      exact hsum ▸ hzero
    have hsumCast :
        (∑ i : Fin (r - 1 + 1), bvec i *
          h ⟨i.val + j.val, by have := i.isLt; omega⟩) =
        (∑ i : Fin r, coeff i *
          h ⟨i.val + j.val, by have := i.isLt; omega⟩) := by
      apply Fintype.sum_equiv (finCongr hrEq)
      intro i
      simp [bvec, finCongr_apply]
    have hsumZero' := hsumCast.trans hsumZero
    simpa [IsApolar, apolarMap] using hsumZero'
  have hbzero : bvec = 0 :=
    hmin (r - 1) hd (by omega) bvec hbApolar
  have hcoeffZero (i : Fin r) : coeff i = 0 := by
    have hz := congrFun hbzero (Fin.cast hrEq.symm i)
    simpa [bvec, coeff] using hz
  rw [← hrepr]
  simp [hcoeffZero]

#assert_trust kernel quotientMomentFunctional_frobenius
#print axioms quotientMomentFunctional_frobenius

end NLA.Proofs.TR14
