import NLA.Proofs.TR26.SeparablePencil

/-! The same constructive pencil argument with explicit finite exclusions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26

theorem exists_separable_pencil_avoiding (f g : Polynomial ℂ) (hfg : IsCoprime f g)
    (hdegree : f.natDegree < g.natDegree) (avoid : Finset ℂ) :
    ∃ t : ℂ, t ∉ avoid ∧ (g + C t * f).Separable ∧ (g + C t * f).natDegree = g.natDegree := by
  classical
  let W := pencilWronskian f g
  have hW : W ≠ 0 := pencilWronskian_ne_zero f g hfg hdegree
  let bad : Finset ℂ := W.roots.toFinset.image (fun r => -g.eval r / f.eval r)
  obtain ⟨t, htall⟩ := (bad ∪ avoid).exists_notMem
  have ht : t ∉ bad := fun h => htall (Finset.mem_union.mpr (Or.inl h))
  have htavoid : t ∉ avoid := fun h => htall (Finset.mem_union.mpr (Or.inr h))
  refine ⟨t, htavoid, ?_, ?_⟩
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

theorem exists_separable_pencil_avoiding_roots (f g : Polynomial ℂ) (hfg : IsCoprime f g)
    (hdegree : f.natDegree < g.natDegree) (avoid roots : Finset ℂ) :
    ∃ t : ℂ, t ∉ avoid ∧ (g + C t * f).Separable ∧
      (g + C t * f).natDegree = g.natDegree ∧
      ∀ r ∈ roots, (g + C t * f).eval r ≠ 0 := by
  classical
  let badRoots := roots.image (fun r => -g.eval r / f.eval r)
  obtain ⟨t, ht, hsep, hdeg⟩ := exists_separable_pencil_avoiding f g hfg hdegree (avoid ∪ badRoots)
  refine ⟨t, (fun h => ht (Finset.mem_union.mpr (Or.inl h))), hsep, hdeg, ?_⟩
  intro r hr hz
  have hroot : g.eval r + t * f.eval r = 0 := by simpa using hz
  have hfne : f.eval r ≠ 0 := by
    intro hf0
    have hg0 : g.eval r = 0 := by simpa only [hf0, mul_zero, add_zero] using hroot
    have hn := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ f g).mp hfg r
    change f.eval r ≠ 0 ∨ g.eval r ≠ 0 at hn
    exact hn.elim (fun h => h hf0) (fun h => h hg0)
  apply ht
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_image.mpr
  refine ⟨r, hr, ?_⟩
  apply (div_eq_iff hfne).2
  linear_combination -hroot

#assert_trust kernel exists_separable_pencil_avoiding
#assert_trust kernel exists_separable_pencil_avoiding_roots
#print axioms exists_separable_pencil_avoiding_roots
end NLA.Proofs.TR26
