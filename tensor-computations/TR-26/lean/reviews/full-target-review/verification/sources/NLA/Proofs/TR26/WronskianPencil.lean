import NLA.Proofs.TR26.WronskianPencilDegree
import NLA.Proofs.TR26.Denominator
import NLA.Proofs.TR26.Numerator

/-! An actual numerator producing a separable full-degree Wronskian for the
fixed unweighted denominator. Both choices avoid explicitly finite bad sets. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem exists_separable_full_degree_affineWronskian {d : ℕ} (hd : 2 ≤ d) :
    ∃ H : Parameter d, (affineWronskian H).Separable ∧
      (affineWronskian H).natDegree = 4 * d - 2 := by
  classical
  let D := affineDenominator d
  let n := 2 * d - 1
  have hn : 1 < n := by dsimp [n]; omega
  have hDdeg : D.natDegree = 2 * d := affineDenominator_natDegree d
  have hDmonic : D.Monic := affineDenominator_monic d
  have hDderne : D.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (by omega)
  let badc : Finset ℂ := D.derivative.roots.toFinset.image (fun r => -(n : ℂ) * r ^ (n - 1))
  obtain ⟨c, hc⟩ := badc.exists_notMem
  let N : Polynomial ℂ := X ^ n + C c * X
  have hsmall : (C c * X : Polynomial ℂ).natDegree < n := by
    exact (Polynomial.natDegree_C_mul_le c X).trans_lt (by simpa using hn)
  have hNdata : N.IsMonicOfDegree n :=
    (Polynomial.isMonicOfDegree_X_pow ℂ n).add_right hsmall
  let f : Polynomial ℂ := -D.derivative
  let g : Polynomial ℂ := polynomialWronskian N D
  have hfdeg : f.natDegree = n := by
    simp only [f, Polynomial.natDegree_neg, Polynomial.natDegree_derivative, hDdeg]
    rfl
  have hgdeg : g.natDegree = 4 * d - 2 := by
    rw [monicWronskian_natDegree N D hNdata.monic hDmonic
      (by rw [hNdata.natDegree_eq]; omega)
      (by rw [hNdata.natDegree_eq, hDdeg]; dsimp [n]; omega)]
    rw [hNdata.natDegree_eq, hDdeg]
    dsimp [n]
    omega
  have hcoprime : IsCoprime f g := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mpr
    intro r
    change f.eval r ≠ 0 ∨ g.eval r ≠ 0
    by_cases hfr : f.eval r = 0
    · right
      intro hgr
      have hDr : D.derivative.eval r = 0 := by simpa only [f, Polynomial.eval_neg, neg_eq_zero] using hfr
      have hDrne : D.eval r ≠ 0 := by
        intro hz
        have h := (affineDenominator_separable d).aeval_derivative_ne_zero hz
        exact h hDr
      have hNr : N.derivative.eval r = (n : ℂ) * r ^ (n - 1) + c := by simp [N, Polynomial.derivative_X_pow]
      have hNrne : N.derivative.eval r ≠ 0 := by
        rw [hNr]
        intro hz
        apply hc
        apply Finset.mem_image.mpr
        refine ⟨r, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hDderne).mpr hDr), ?_⟩
        linear_combination -hz
      change (N.derivative * D - N * D.derivative).eval r = 0 at hgr
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, hDr, mul_zero, sub_zero] at hgr
      exact (mul_ne_zero hNrne hDrne) hgr
    · exact Or.inl hfr
  have hdegree : f.natDegree < g.natDegree := by rw [hfdeg, hgdeg]; dsimp [n]; omega
  obtain ⟨a, hsep, hdeg⟩ := exists_separable_pencil f g hcoprime hdegree
  let P : Polynomial ℂ := N + C a
  have hPdegree : P.natDegree ≤ 2 * d := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · rw [hNdata.natDegree_eq]
      dsimp [n]
      omega
    · simp
  obtain ⟨H, hH⟩ := affineNumerator_surjective_degreeLE d P hPdegree
  have hPWr : polynomialWronskian P D = g + C a * f := by
    simp only [polynomialWronskian, P, Polynomial.derivative_add, Polynomial.derivative_C,
      add_zero, f, g]
    ring
  have hWH : affineWronskian H = g + C a * f := by
    change polynomialWronskian (affineNumerator H) D = _
    rw [hH]
    exact hPWr
  refine ⟨H, ?_, ?_⟩
  · rwa [hWH]
  · rw [hWH, hdeg, hgdeg]

#assert_trust kernel exists_separable_full_degree_affineWronskian
#print axioms exists_separable_full_degree_affineWronskian
end NLA.Proofs.TR26
