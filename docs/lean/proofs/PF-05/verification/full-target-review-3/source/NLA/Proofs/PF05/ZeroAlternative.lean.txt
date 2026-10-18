import NLA.Proofs.PF05.ZeroAlternativeShear
import NLA.Proofs.PF05.ZeroNormalize

/-! Every actual alternative to a normalized nonzero orthogonal-pair
factorization has the canonical primal and inverse-dual maps after one
actual invertible congruence. No alternative normal form is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

/-- Actual normalized alternative normal form, including shear/reflection
and the exact weighted inverse-dual formula on the whole factor family. -/
theorem zeroAlternative_normal_form {p q : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (A At : Fin p → Sym2) (B Bt : Fin q → Sym2)
    (hfact : Factorization M A B) (ht : Factorization M At Bt) (hrank : M.rank = 3)
    (i₀ : Fin p) (j₀ : Fin q)
    (hA : A i₀ = !![1,0;0,0]) (hB : B j₀ = !![0,0;0,1]) :
    ∃ (S : Sym2) (α β γ : ℝ), S.det ≠ 0 ∧ 0 < γ ∧
      (∀ i, primalCongruence S (At i) = zeroCanonicalPrimal α β γ (A i)) ∧
      (∀ j, dualCongruence S (Bt j) = zeroCanonicalDual α β γ (B j)) := by
  have hAt0 : At i₀ ≠ 0 := by
    intro hz
    have hrow : ∀ j, M i₀ j = 0 := by
      intro j
      rw [ht.2.2 i₀ j, hz]
      simp
    have hzero := factor_zero_row M A B hfact hrank i₀ hrow
    rw [hA] at hzero
    have hh := congrArg (fun X : Sym2 => X 0 0) hzero
    norm_num at hh
  have hBt0 : Bt j₀ ≠ 0 := by
    intro hz
    have hcol : ∀ i, M i j₀ = 0 := by
      intro i
      rw [ht.2.2 i j₀, hz]
      simp
    have hzero := factor_zero_column M A B hfact hrank j₀ hcol
    rw [hB] at hzero
    have hh := congrArg (fun X : Sym2 => X 1 1) hzero
    norm_num at hh
  have htrace : Matrix.trace (At i₀ * Bt j₀) = 0 := by
    rw [← ht.2.2 i₀ j₀, hfact.2.2 i₀ j₀, hA, hB]
    norm_num [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨U, hU, hUP, hUQ⟩ := normalize_nonzero_zero_pair (At i₀) (Bt j₀)
    (ht.1 i₀) (ht.2.1 j₀) hAt0 hBt0 htrace
  let Au := fun i => primalCongruence U (At i)
  let Bu := fun j => dualCongruence U (Bt j)
  have hu : Factorization M Au Bu := factorization_congruence M At Bt ht U hU
  obtain ⟨V, α, β, γ, hV, hγ, hprimal⟩ :=
    zeroAlternative_shear M A Au B Bu hfact hu hrank i₀ j₀ hA hB hUP hUQ
  let S := U * V
  have hS : S.det ≠ 0 := by
    dsimp [S]
    rw [Matrix.det_mul]
    exact mul_ne_zero hU hV
  have hmap (i : Fin p) : primalCongruence S (At i) = zeroCanonicalPrimal α β γ (A i) := by
    rw [show S = U * V from rfl, ← primalCongruence_comp]
    exact hprimal i
  have hnew : Factorization M (fun i => primalCongruence S (At i))
      (fun j => dualCongruence S (Bt j)) := factorization_congruence M At Bt ht S hS
  refine ⟨S, α, β, γ, hS, hγ, hmap, ?_⟩
  exact zeroCanonical_dual_of_primal M A _ B _ hfact hnew hrank α β γ (ne_of_gt hγ) hmap

#assert_trust kernel zeroAlternative_normal_form
#print axioms zeroAlternative_normal_form
end
end NLA.Proofs.PF05
