import NLA.Proofs.TR26.CommonFactorWronskian
import NLA.Proofs.TR26.SeparablePencilAvoid

/-! A genuine ordinary-double-root Wronskian above each actual denominator
root. The cofactor is obtained by a proved finite-exception pencil. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26 Polynomial

theorem exists_separable_Wronskian_cofactor (E : Polynomial ℂ) (hmon : E.Monic)
    (hsep : E.Separable) (hdeg : 3 ≤ E.natDegree) (r : ℂ) :
    ∃ M : Polynomial ℂ, M.natDegree ≤ E.natDegree-1 ∧
      (polynomialWronskian M E).Separable ∧
      (polynomialWronskian M E).natDegree=2*E.natDegree-2 ∧
      (polynomialWronskian M E).eval r ≠ 0 := by
  classical
  let n := E.natDegree-1
  have hn : 1 < n := by dsimp [n]; omega
  have hEderne : E.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (by omega)
  let badc : Finset ℂ := E.derivative.roots.toFinset.image (fun z => -(n:ℂ)*z^(n-1))
  obtain ⟨c,hc⟩ := badc.exists_notMem
  let N : Polynomial ℂ := X^n+C c*X
  have hsmall : (C c*X : Polynomial ℂ).natDegree<n :=
    (Polynomial.natDegree_C_mul_le c X).trans_lt (by simpa using hn)
  have hNdata : N.IsMonicOfDegree n := (isMonicOfDegree_X_pow ℂ n).add_right hsmall
  let f : Polynomial ℂ := -E.derivative
  let g : Polynomial ℂ := polynomialWronskian N E
  have hfdeg : f.natDegree=n := by simp only [f,natDegree_neg,natDegree_derivative,n]
  have hgdeg : g.natDegree=2*E.natDegree-2 := by
    rw [monicWronskian_natDegree N E hNdata.monic hmon
      (by rw [hNdata.natDegree_eq]; omega)
      (by rw [hNdata.natDegree_eq]; dsimp [n]; omega)]
    rw [hNdata.natDegree_eq]
    dsimp [n]
    omega
  have hcop : IsCoprime f g := by
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mpr
    intro z
    change f.eval z ≠ 0 ∨ g.eval z ≠ 0
    by_cases hfz : f.eval z=0
    · right
      intro hgz
      have hEz : E.derivative.eval z=0 := by simpa only [f,eval_neg,neg_eq_zero] using hfz
      have hEzne : E.eval z ≠ 0 := by
        intro hz
        exact (hsep.aeval_derivative_ne_zero hz) hEz
      have hNz : N.derivative.eval z=(n:ℂ)*z^(n-1)+c := by simp [N,derivative_X_pow]
      have hNzne : N.derivative.eval z ≠ 0 := by
        rw [hNz]
        intro hz
        apply hc
        apply Finset.mem_image.mpr
        refine ⟨z,Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hEderne).mpr hEz),?_⟩
        linear_combination -hz
      change (N.derivative*E-N*E.derivative).eval z=0 at hgz
      simp only [eval_sub,eval_mul,hEz,mul_zero,sub_zero] at hgz
      exact (mul_ne_zero hNzne hEzne) hgz
    · exact Or.inl hfz
  obtain ⟨a,_ha,hSsep,hSdeg,hSr⟩ := exists_separable_pencil_avoiding_roots f g hcop
    (by rw [hfdeg,hgdeg]; dsimp [n]; omega) ∅ {r}
  let M : Polynomial ℂ := N+C a
  have hMdeg : M.natDegree ≤ E.natDegree-1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · rw [hNdata.natDegree_eq]
    · simp
  have hWr : polynomialWronskian M E=g+C a*f := by
    simp only [polynomialWronskian,M,derivative_add,derivative_C,add_zero,f,g]
    ring
  refine ⟨M,hMdeg,?_,?_,?_⟩
  · rwa [hWr]
  · rw [hWr,hSdeg,hgdeg]
  · rw [hWr]
    exact hSr r (by simp)

theorem exists_isotropic_ordinary_Wronskian {d : ℕ} (hd : 2 ≤ d)
    {r : ℂ} (hr : r ∈ denominatorRoots d) :
    ∃ H : Parameter d, ∃ S : Polynomial ℂ,
      (affineNumerator H).eval r=0 ∧
      affineWronskian H=(X-C r)^2*S ∧ S.Separable ∧
      S.natDegree=4*d-4 ∧ S.eval r ≠ 0 := by
  obtain ⟨E,hE,hEmon,hEsep,hEdeg,_hEr⟩ := denominator_root_linear_factor hr
  obtain ⟨M,hMdeg,hSsep,hSdeg,hSr⟩ :=
    exists_separable_Wronskian_cofactor E hEmon hEsep (by omega) r
  obtain ⟨H,hH⟩ := exists_parameter_linear_factor_numerator (d := d) r M (by omega) (by omega)
  refine ⟨H,polynomialWronskian M E,?_,?_,hSsep,?_,hSr⟩
  · rw [hH]
    simp
  · change polynomialWronskian (affineNumerator H) (affineDenominator d)=_
    rw [hH,hE,polynomialWronskian_common_factor]
  · rw [hSdeg,hEdeg]
    omega

#assert_trust kernel exists_separable_Wronskian_cofactor
#assert_trust kernel exists_isotropic_ordinary_Wronskian
#print axioms exists_isotropic_ordinary_Wronskian
end NLA.Proofs.TR26
