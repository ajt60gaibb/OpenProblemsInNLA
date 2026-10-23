import NLA.Proofs.TR14.WidthBasics
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.BigOperators.Fin

/-! Minimum-length actual ordinary decompositions have independent
rank-one coordinate functions. Scalars are absorbed in one existing mode;
no symmetry, Vandermonde condition, or nonzero factor-coordinate premise is
introduced. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.TR14
open NLA.Statements.TR14

/-- The actual rank-one coordinate function of one ordinary summand. -/
def ordinarySummand {m n r : ℕ} (u : Fin r → Fin m → Fin n → ℂ) (j : Fin r) :
    (Fin m → Fin n) → ℂ := fun i => ∏ k, u j k (i k)

/-- The supplied witness itself gives a least ordinary width below it. -/
theorem exists_minimal_ordinaryWidth {m n w : ℕ} {H : (Fin m → Fin n) → ℂ}
    (hw : OrdinaryWidth H w) :
    ∃ r ≤ w, OrdinaryWidth H r ∧ ∀ s < r, ¬ OrdinaryWidth H s := by
  classical
  let ex : ∃ r, OrdinaryWidth H r := ⟨w, hw⟩
  exact ⟨Nat.find ex, Nat.find_min' ex hw, Nat.find_spec ex,
    fun s hs => Nat.find_min ex hs⟩

/-- Reweighting arbitrary ordinary summands remains an ordinary witness,
with the weights absorbed into mode zero. -/
theorem ordinaryWidth_of_weighted_summands {m n r s : ℕ}
    (hm : 0 < m) (u : Fin r → Fin m → Fin n → ℂ)
    (f : Fin s → Fin r) (c : Fin s → ℂ) (H : (Fin m → Fin n) → ℂ)
    (hH : ∀ i, H i = ∑ j, c j * ordinarySummand u (f j) i) :
    OrdinaryWidth H s := by
  classical
  let k0 : Fin m := ⟨0, hm⟩
  refine ⟨fun j k x => (if k = k0 then c j else 1) * u (f j) k x, ?_⟩
  intro i
  rw [hH i]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.prod_mul_distrib]
  have hc : (∏ k : Fin m, if k = k0 then c j else 1) = c j :=
    Fintype.prod_ite_eq' k0 (fun _ : Fin m => c j)
  rw [hc]
  rfl

/-- Eliminate any nonzero coefficient of a linear dependence, as an exact
identity of finite complex sums. -/
theorem sum_eq_reweighted_erase {r : ℕ} (z c : Fin (r + 1) → ℂ)
    (j : Fin (r + 1)) (hcj : c j ≠ 0) (hc : ∑ i, c i * z i = 0) :
    ∑ i, z i = ∑ i : Fin r, (1 - c (j.succAbove i) / c j) * z (j.succAbove i) := by
  have hrel : c j * z j + ∑ i : Fin r, c (j.succAbove i) * z (j.succAbove i) = 0 := by
    rw [← Fin.sum_univ_succAbove (fun i => c i * z i) j]
    exact hc
  have hquot : (∑ i : Fin r, c (j.succAbove i) * z (j.succAbove i)) / c j = - z j := by
    apply (div_eq_iff hcj).mpr
    linear_combination hrel
  have hw : (∑ i : Fin r, (1 - c (j.succAbove i) / c j) * z (j.succAbove i)) =
      (∑ i : Fin r, z (j.succAbove i)) -
        (∑ i : Fin r, c (j.succAbove i) * z (j.succAbove i)) / c j := by
    simp_rw [sub_mul, one_mul, div_mul_eq_mul_div]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  rw [Fin.sum_univ_succAbove z j, hw, hquot]
  ring

/-- A dependence among the actual ordinary summands shortens the actual
ordinary decomposition, not merely a related flattened matrix. -/
theorem ordinaryWidth_erase_of_relation {m n r : ℕ} (hm : 0 < m)
    (u : Fin (r + 1) → Fin m → Fin n → ℂ) (H : (Fin m → Fin n) → ℂ)
    (hH : ∀ i, H i = ∑ j, ordinarySummand u j i)
    (c : Fin (r + 1) → ℂ) (hc : ∑ j, c j • ordinarySummand u j = 0)
    (j : Fin (r + 1)) (hcj : c j ≠ 0) : OrdinaryWidth H r := by
  apply ordinaryWidth_of_weighted_summands hm u j.succAbove
    (fun i => 1 - c (j.succAbove i) / c j) H
  intro i
  rw [hH i]
  apply sum_eq_reweighted_erase (fun j => ordinarySummand u j i) c j hcj
  have h := congrFun hc i
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using h

/-- Every minimum ordinary decomposition has linearly independent actual
rank-one coordinate functions, by deleting a dependent summand. -/
theorem minimal_ordinary_summands_independent {m n r : ℕ} (hm : 0 < m)
    (u : Fin r → Fin m → Fin n → ℂ) (H : (Fin m → Fin n) → ℂ)
    (hH : ∀ i, H i = ∑ j, ordinarySummand u j i)
    (hmin : ∀ s < r, ¬ OrdinaryWidth H s) :
    LinearIndependent ℂ (ordinarySummand u) := by
  classical
  cases r with
  | zero =>
    apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    exact Fin.elim0 j
  | succ r =>
    by_contra hdep
    obtain ⟨c, hc, j, hcj⟩ := Fintype.not_linearIndependent_iff.mp hdep
    exact hmin r (Nat.lt_succ_self r)
      (ordinaryWidth_erase_of_relation hm u H hH c hc j hcj)

/-- No entire mode factor of a minimum summand is zero. Individual entries
may still be zero, and no extra chart condition is imposed. -/
theorem ordinary_mode_ne_zero_of_independent {m n r : ℕ}
    (u : Fin r → Fin m → Fin n → ℂ)
    (hind : LinearIndependent ℂ (ordinarySummand u)) (j : Fin r) (k : Fin m) :
    u j k ≠ 0 := by
  intro hzero
  apply hind.ne_zero j
  funext i
  exact Finset.prod_eq_zero (Finset.mem_univ k) (congrFun hzero (i k))

#assert_trust kernel exists_minimal_ordinaryWidth
#assert_trust kernel minimal_ordinary_summands_independent
#assert_trust kernel ordinary_mode_ne_zero_of_independent
#print axioms minimal_ordinary_summands_independent

end NLA.Proofs.TR14
