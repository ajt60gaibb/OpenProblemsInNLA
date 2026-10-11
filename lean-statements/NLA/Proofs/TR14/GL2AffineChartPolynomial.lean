import NLA.Proofs.TR14.GL2Dehomogenize

/-!
The exact affine polynomial obtained by dehomogenizing the audited binary
chart substitution. This records all coefficients, including trailing zeros.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators
open MvPolynomial Polynomial
noncomputable section

private def affineFormEval (a b : ℂ) {d : ℕ} (P : BinaryForm d) : ℂ :=
  MvPolynomial.aeval ![a, b] P.1

private theorem affineFormEval_monomial (a b : ℂ) (d : ℕ)
    (i : Fin (d + 1)) :
    affineFormEval a b (binaryMonomial d i) =
      a ^ (d - i.val) * b ^ i.val := by
  change MvPolynomial.aeval ![a, b]
      ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ (d - i.val) *
        MvPolynomial.X 1 ^ i.val) = _
  simp

private theorem affineFormEval_form (a b : ℂ) (d : ℕ)
    (g : Fin (d + 1) → ℂ) :
    affineFormEval a b (binaryFormEquiv d g) =
      ∑ i : Fin (d + 1), g i * a ^ (d - i.val) * b ^ i.val := by
  rw [binaryFormEquiv_eq_sum]
  have hs : (∑ i : Fin (d + 1), g i • binaryMonomial d i).1 =
      ∑ i : Fin (d + 1), g i • (binaryMonomial d i).1 := by simp
  rw [affineFormEval, hs, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hm := affineFormEval_monomial a b d i
  change (MvPolynomial.aeval ![a, b]) (binaryMonomial d i).1 =
    a ^ (d - i.val) * b ^ i.val at hm
  rw [hm]
  ring

private theorem affineFormEval_one (d : ℕ) (g : Fin (d + 1) → ℂ)
    (t : ℂ) :
    affineFormEval 1 t (binaryFormEquiv d g) =
      (dehomogenize d g).eval t := by
  rw [affineFormEval_form, dehomogenize_eval]
  simp

private theorem affineFormEval_chart (z t : ℂ) {d : ℕ}
    (P : BinaryForm d) :
    affineFormEval 1 t (chartPhi z d P) =
      affineFormEval t (1 + z * t) P := by
  have hcomp : (MvPolynomial.aeval ![(1 : ℂ), t]).comp (chartSubst z) =
      (MvPolynomial.aeval ![t, (1 : ℂ) + z * t] :
        MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp only [AlgHom.comp_apply, chartSubst, MvPolynomial.aeval_X]
      change (MvPolynomial.aeval ![(1 : ℂ), t])
        (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) = t
      simp
    · simp only [AlgHom.comp_apply, chartSubst, MvPolynomial.aeval_X]
      change (MvPolynomial.aeval ![(1 : ℂ), t])
        (MvPolynomial.X 0 + MvPolynomial.C z * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) ℂ) = 1 + z * t
      simp
  exact DFunLike.congr_fun hcomp P.1

/-- The full degree-`d` affine polynomial under the audited chart. -/
theorem dehomogenize_transportedApolarVector
    (z : ℂ) (d : ℕ) (g : Fin (d + 1) → ℂ) :
    dehomogenize d (transportedApolarVector z d g) =
      ∑ i : Fin (d + 1),
        Polynomial.C (g i) * Polynomial.X ^ (d - i.val) *
          (1 + Polynomial.C z * Polynomial.X) ^ i.val := by
  apply Polynomial.funext
  intro t
  calc
    (dehomogenize d (transportedApolarVector z d g)).eval t =
        affineFormEval 1 t
          (binaryFormEquiv d (transportedApolarVector z d g)) := by
            symm
            exact affineFormEval_one d _ t
    _ = affineFormEval 1 t (chartPhi z d (binaryFormEquiv d g)) := by
          rw [binaryFormEquiv_transportedApolarVector]
    _ = affineFormEval t (1 + z * t) (binaryFormEquiv d g) :=
          affineFormEval_chart z t _
    _ = (∑ i : Fin (d + 1),
          Polynomial.C (g i) * Polynomial.X ^ (d - i.val) *
            (1 + Polynomial.C z * Polynomial.X) ^ i.val).eval t := by
          rw [affineFormEval_form]
          simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
            Polynomial.eval_add, Polynomial.eval_one]
  all_goals rfl

#assert_trust kernel dehomogenize_transportedApolarVector
#print axioms dehomogenize_transportedApolarVector

end
end NLA.Proofs.TR14
