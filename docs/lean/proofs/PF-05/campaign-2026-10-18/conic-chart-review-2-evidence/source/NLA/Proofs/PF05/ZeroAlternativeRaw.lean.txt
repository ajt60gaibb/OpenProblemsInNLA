import NLA.Proofs.PF05.Operator
import NLA.Proofs.PF05.PositiveReduction

/-! Actual finite operator constraints when both factorizations contain the
same distinguished P,Q pair. Coordinates retain the trace weight two. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

/-- The actual finite change-of-basis operator has the four-parameter raw
normal form forced by the two normalized distinguished factors. -/
theorem zeroAlternative_raw {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → Sym2) (B Bt : Fin q → Sym2)
    (hfact : Factorization M A B) (ht : Factorization M At Bt) (hrank : M.rank = 3)
    (i₀ : Fin p) (j₀ : Fin q)
    (hA : A i₀ = !![1,0;0,0]) (hB : B j₀ = !![0,0;0,1])
    (hAt : At i₀ = !![1,0;0,0]) (hBt : Bt j₀ = !![0,0;0,1]) :
    ∃ α β γ δ : ℝ, γ ≠ 0 ∧ ∀ i,
      At i = !![A i 0 0 + α * A i 0 1 + β * A i 1 1,
        γ * A i 0 1 + δ * A i 1 1;
        γ * A i 0 1 + δ * A i 1 1, A i 1 1] := by
  obtain ⟨L, hL, hleft, hright⟩ := factorization_change_of_basis M A At B Bt hfact ht hrank
  have hrow (k : Fin 3) : L 0 k = (![1,0,0] : Fin 3 → ℝ) k := by
    have hx := congrArg (fun X : Matrix (Fin p) (Fin 3) ℝ => X i₀ k) hleft
    simpa [leftCoordinates, Matrix.mul_apply, Fin.sum_univ_three, hA, hAt] using hx.symm
  have hY : L * rightCoordinates Bt = rightCoordinates B := by
    rw [hright, ← Matrix.mul_assoc, L.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hL), Matrix.one_mul]
  have hcol (k : Fin 3) : L k 1 = (![0,1,0] : Fin 3 → ℝ) k := by
    have hx := congrArg (fun X : Matrix (Fin 3) (Fin q) ℝ => X k j₀) hY
    simpa [rightCoordinates, Matrix.mul_apply, Fin.sum_univ_three, hB, hBt] using hx
  have hLform : L = !![1,0,0; L 1 0,1,L 1 2; L 2 0,0,L 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hrow, hcol]
  have hγ : L 2 2 ≠ 0 := by
    intro hz
    apply hL
    rw [hLform]
    simp [Matrix.det_fin_three, hz]
  refine ⟨L 2 0, L 1 0, L 2 2, L 1 2, hγ, ?_⟩
  intro i
  have h00 := congrArg (fun X : Matrix (Fin p) (Fin 3) ℝ => X i 0) hleft
  have h11 := congrArg (fun X : Matrix (Fin p) (Fin 3) ℝ => X i 1) hleft
  have h01 := congrArg (fun X : Matrix (Fin p) (Fin 3) ℝ => X i 2) hleft
  simp [leftCoordinates, Matrix.mul_apply, Fin.sum_univ_three, hrow, hcol] at h00 h11 h01
  ext a b
  fin_cases a <;> fin_cases b
  · simpa using h00.trans (by ring)
  · simpa using h01.trans (by ring)
  · change At i 1 0 = L 2 2 * A i 0 1 + L 1 2 * A i 1 1
    rw [(ht.1 i).1 1 0]
    exact h01.trans (by ring)
  · simpa using h11

#assert_trust kernel zeroAlternative_raw
#print axioms zeroAlternative_raw
end
end NLA.Proofs.PF05
