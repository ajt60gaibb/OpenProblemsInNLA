import NLA.Proofs.TR14.GL2ApolarTransport
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots

/-!
Exact affine dehomogenization and the last-coefficient identity for the
audited TR-14 chart. This does not normalize an apolar witness yet.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
open MvPolynomial Polynomial
noncomputable section

/-- The exact affine polynomial `Σ_i g_i t^i`, including trailing zeros. -/
def dehomogenize (d : ℕ) : (Fin (d + 1) → ℂ) →ₗ[ℂ] Polynomial ℂ :=
  Polynomial.ofFn (d + 1)

theorem dehomogenize_coeff (d : ℕ) (g : Fin (d + 1) → ℂ)
    (i : Fin (d + 1)) :
    (dehomogenize d g).coeff i.val = g i := by
  exact Polynomial.ofFn_coeff_eq_val_of_lt g i.isLt

theorem dehomogenize_eq_zero_iff (d : ℕ) (g : Fin (d + 1) → ℂ) :
    dehomogenize d g = 0 ↔ g = 0 := by
  constructor
  · intro hz
    exact (Polynomial.injective_ofFn (d + 1)) (by simpa [dehomogenize] using hz)
  · intro hz
    subst g
    simp [dehomogenize]

theorem dehomogenize_eval (d : ℕ) (g : Fin (d + 1) → ℂ) (z : ℂ) :
    (dehomogenize d g).eval z = ∑ i : Fin (d + 1), g i * z ^ i.val := by
  rw [dehomogenize, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]

private def formEval (a b : ℂ) {d : ℕ} (P : BinaryForm d) : ℂ :=
  MvPolynomial.aeval ![a, b] P.1

private theorem formEval_monomial (a b : ℂ) (d : ℕ) (i : Fin (d + 1)) :
    formEval a b (binaryMonomial d i) = a ^ (d - i.val) * b ^ i.val := by
  change MvPolynomial.aeval ![a, b]
      ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ (d - i.val) *
        MvPolynomial.X 1 ^ i.val) = _
  simp

private theorem formEval_form (a b : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    formEval a b (binaryFormEquiv d g) =
      ∑ i : Fin (d + 1), g i * a ^ (d - i.val) * b ^ i.val := by
  rw [binaryFormEquiv_eq_sum]
  have hs : (∑ i : Fin (d + 1), g i • binaryMonomial d i).1 =
      ∑ i : Fin (d + 1), g i • (binaryMonomial d i).1 := by simp
  rw [formEval, hs, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hm := formEval_monomial a b d i
  change (MvPolynomial.aeval ![a, b]) (binaryMonomial d i).1 =
    a ^ (d - i.val) * b ^ i.val at hm
  rw [hm]
  ring

private theorem formEval_one (d : ℕ) (g : Fin (d + 1) → ℂ) (z : ℂ) :
    formEval 1 z (binaryFormEquiv d g) = (dehomogenize d g).eval z := by
  rw [formEval_form, dehomogenize_eval]
  simp

private theorem formEval_zero_one (d : ℕ) (g : Fin (d + 1) → ℂ) :
    formEval 0 1 (binaryFormEquiv d g) = g ⟨d, by omega⟩ := by
  rw [formEval_form]
  have hterm (i : Fin (d + 1)) :
      g i * (0 : ℂ) ^ (d - i.val) * (1 : ℂ) ^ i.val =
        if i = ⟨d, by omega⟩ then g i else 0 := by
    by_cases hi : i.val = d
    · have hii : i = ⟨d, by omega⟩ := Fin.ext hi
      simp [hii]
    · have hpos : d - i.val ≠ 0 := by have := i.isLt; omega
      have hneq : i ≠ (⟨d, by omega⟩ : Fin (d + 1)) := by
        intro heq
        exact hi (congrArg Fin.val heq)
      simp [hpos, hneq]
  simp_rw [hterm]
  simp

private theorem formEval_chart (z : ℂ) {d : ℕ} (P : BinaryForm d) :
    formEval 0 1 (chartPhi z d P) = formEval 1 z P := by
  have hcomp : (MvPolynomial.aeval ![(0 : ℂ), (1 : ℂ)]).comp (chartSubst z) =
      (MvPolynomial.aeval ![(1 : ℂ), z] :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp only [AlgHom.comp_apply, chartSubst, MvPolynomial.aeval_X]
      change (MvPolynomial.aeval ![(0 : ℂ), (1 : ℂ)])
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) = 1
      simp
    · simp only [AlgHom.comp_apply, chartSubst, MvPolynomial.aeval_X]
      change (MvPolynomial.aeval ![(0 : ℂ), (1 : ℂ)])
        (MvPolynomial.X 0 + MvPolynomial.C z * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) ℂ) = z
      simp
  exact DFunLike.congr_fun hcomp P.1

/-- The transformed final coefficient is exactly `G(1,z)`. -/
theorem chart_last_coefficient (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    transportedApolarVector z d g ⟨d, by omega⟩ =
      (dehomogenize d g).eval z := by
  calc
    transportedApolarVector z d g ⟨d, by omega⟩ =
        formEval 0 1 (binaryFormEquiv d (transportedApolarVector z d g)) := by
          symm
          exact formEval_zero_one d _
    _ = formEval 0 1 (chartPhi z d (binaryFormEquiv d g)) := by
          rw [binaryFormEquiv_transportedApolarVector]
    _ = formEval 1 z (binaryFormEquiv d g) := formEval_chart z _
    _ = (dehomogenize d g).eval z := formEval_one d g z

theorem exists_chart_last_nonzero (d : ℕ) (g : Fin (d + 1) → ℂ)
    (hg : g ≠ 0) :
    ∃ z : ℂ, transportedApolarVector z d g ⟨d, by omega⟩ ≠ 0 := by
  have hp : dehomogenize d g ≠ 0 :=
    fun hz => hg ((dehomogenize_eq_zero_iff d g).mp hz)
  by_contra hz
  push Not at hz
  apply hp
  apply Polynomial.zero_of_eval_zero
  intro z
  exact (chart_last_coefficient z d g).symm.trans (hz z)

#assert_trust kernel dehomogenize
#assert_trust kernel dehomogenize_coeff
#assert_trust kernel dehomogenize_eq_zero_iff
#assert_trust kernel chart_last_coefficient
#assert_trust kernel exists_chart_last_nonzero
#print axioms exists_chart_last_nonzero

end
end NLA.Proofs.TR14
