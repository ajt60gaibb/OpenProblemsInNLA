import NLA.Statements.TR26

/-! A constructive finite-exception argument for an actual polynomial pencil.
The exceptional parameters are explicit images of the roots of its nonzero
Wronskian; no generic-separability premise is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26

def pencilWronskian (f g : Polynomial ℂ) : Polynomial ℂ := g.derivative * f - g * f.derivative

theorem pencilWronskian_ne_zero (f g : Polynomial ℂ) (hfg : IsCoprime f g)
    (hdegree : f.natDegree < g.natDegree) : pencilWronskian f g ≠ 0 := by
  intro hz
  have hgdeg : g.natDegree ≠ 0 := by omega
  have hder : g.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hgdeg
  have heq : f * g.derivative = g * f.derivative := by
    simpa only [pencilWronskian, sub_eq_zero, mul_comm] using hz
  have hdvd : g ∣ g.derivative := hfg.symm.dvd_of_dvd_mul_left ⟨f.derivative, heq⟩
  have hle := Polynomial.natDegree_le_of_dvd hdvd hder
  have hlt := Polynomial.natDegree_derivative_lt hgdeg
  omega

theorem exists_separable_pencil (f g : Polynomial ℂ) (hfg : IsCoprime f g)
    (hdegree : f.natDegree < g.natDegree) :
    ∃ t : ℂ, (g + C t * f).Separable ∧ (g + C t * f).natDegree = g.natDegree := by
  classical
  let W := pencilWronskian f g
  have hW : W ≠ 0 := pencilWronskian_ne_zero f g hfg hdegree
  let bad : Finset ℂ := W.roots.toFinset.image (fun r => -g.eval r / f.eval r)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  refine ⟨t, ?_, ?_⟩
  · rw [Polynomial.separable_def]
    apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ
      (g + C t * f) (g + C t * f).derivative).mpr
    intro r
    change (g + C t * f).eval r ≠ 0 ∨ (g + C t * f).derivative.eval r ≠ 0
    by_cases hr : (g + C t * f).eval r = 0
    · right
      intro hdr
      have hroot : g.eval r + t * f.eval r = 0 := by simpa using hr
      have hder : g.derivative.eval r + t * f.derivative.eval r = 0 := by
        simpa only [Polynomial.derivative_add, Polynomial.derivative_mul,
          Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C] using hdr
      have hfne : f.eval r ≠ 0 := by
        intro hfr
        have hgr : g.eval r = 0 := by simpa only [hfr, mul_zero, add_zero] using hroot
        have hn := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mp hfg r
        change f.eval r ≠ 0 ∨ g.eval r ≠ 0 at hn
        exact hn.elim (fun h => h hfr) (fun h => h hgr)
      have hWr : W.eval r = 0 := by
        change (pencilWronskian f g).eval r = 0
        simp only [pencilWronskian, Polynomial.eval_sub, Polynomial.eval_mul]
        linear_combination f.eval r * hder - f.derivative.eval r * hroot
      apply ht
      apply Finset.mem_image.mpr
      refine ⟨r, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hW).mpr hWr), ?_⟩
      apply (div_eq_iff hfne).2
      linear_combination -hroot
    · exact Or.inl hr
  · apply Polynomial.natDegree_add_eq_left_of_natDegree_lt
    exact (Polynomial.natDegree_C_mul_le _ _).trans_lt hdegree

#assert_trust kernel pencilWronskian_ne_zero
#assert_trust kernel exists_separable_pencil
#print axioms exists_separable_pencil
end NLA.Proofs.TR26
