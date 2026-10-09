import NLA.TR13.Definitions
import Mathlib.Algebra.MvPolynomial.Funext

noncomputable section
open scoped BigOperators
open Filter
namespace NLA.TR13

theorem vandermonde_le_symmetric {m n q : ℕ} {T : Tensor m n}
    (h : VandermondeRankAtMost q T) : SymmetricRankAtMost q T := by
  obtain ⟨c, a, b, _, h⟩ := h
  exact ⟨c, fun j => vandermondeVector n (a j) (b j), h⟩

theorem symmetric_le_ordinary {m n q : ℕ} (hm : 0 < m) {T : Tensor m n}
    (h : SymmetricRankAtMost q T) : OrdinaryRankAtMost q T := by
  classical
  obtain ⟨c, v, h⟩ := h
  let j₀ : Fin m := ⟨0, hm⟩
  refine ⟨fun a j i => (if j = j₀ then c a else 1) * v a i, ?_⟩
  rw [h]
  apply Finset.sum_congr rfl
  intro a _
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, symmetricTensor, pureTensor]
  rw [Finset.prod_mul_distrib]
  simp

theorem ordinary_le_border {m n q : ℕ} {T : Tensor m n}
    (h : OrdinaryRankAtMost q T) : OrdinaryBorderRankAtMost q T :=
  ⟨fun _ => T, fun _ => h, tendsto_const_nhds⟩

theorem symmetric_le_border {m n q : ℕ} {T : Tensor m n}
    (h : SymmetricRankAtMost q T) : SymmetricBorderRankAtMost q T :=
  ⟨fun _ => T, fun _ => h, tendsto_const_nhds⟩

theorem symmetric_border_le_ordinary_border {m n q : ℕ} (hm : 0 < m)
    {T : Tensor m n} (h : SymmetricBorderRankAtMost q T) :
    OrdinaryBorderRankAtMost q T := by
  obtain ⟨U, hU, ht⟩ := h
  exact ⟨U, fun k => symmetric_le_ordinary hm (hU k), ht⟩

private theorem least_eq {P : ℕ → Prop} {r : ℕ} (hr : P r)
    (hmin : ∀ q, P q → r ≤ q) : sInf {q | P q} = r := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) hr
  · exact le_csInf ⟨r, hr⟩ (fun q hq => hmin q hq)

/-- Every infimum below has an actual member supplied by the Vandermonde
decomposition. The ordinary-border obstruction bounds every such member. -/
theorem all_ranks_equal_of_bounds {m n r : ℕ} (hm : 0 < m) {T : Tensor m n}
    (hu : VandermondeRankAtMost r T)
    (hl : ∀ q, OrdinaryBorderRankAtMost q T → r ≤ q) :
    AllRanksEqual T r := by
  have hs := vandermonde_le_symmetric hu
  have ho := symmetric_le_ordinary hm hs
  have hob := ordinary_le_border ho
  have hsb := symmetric_le_border hs
  refine ⟨least_eq ho ?_, least_eq hs ?_, least_eq hob hl,
    least_eq hsb ?_, least_eq hu ?_⟩
  · intro q hq
    exact hl q (ordinary_le_border hq)
  · intro q hq
    exact hl q (ordinary_le_border (symmetric_le_ordinary hm hq))
  · intro q hq
    exact hl q (symmetric_border_le_ordinary_border hm hq)
  · intro q hq
    exact hl q (ordinary_le_border
      (symmetric_le_ordinary hm (vandermonde_le_symmetric hq)))

theorem principalOpen_nonempty {m n : ℕ}
    {p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ} (hp : p ≠ 0) :
    (principalOpen p).Nonempty := by
  classical
  by_contra h
  apply hp
  apply MvPolynomial.funext
  intro x
  simp only [map_zero]
  by_contra hx
  exact h ⟨x, hx⟩

end NLA.TR13
