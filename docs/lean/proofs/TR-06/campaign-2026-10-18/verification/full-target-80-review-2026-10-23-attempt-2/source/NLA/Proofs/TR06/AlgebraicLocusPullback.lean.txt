import NLA.TR06.SegreAlgebra
import NLA.TR06.SegreNonzero

/-! A nonzero pullback to the genuine integral Segre source is nonzero in
every exact-dimensional pivot pattern. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.AlgebraicLocus
open scoped BigOperators
open NLA.TR06 NLA.TR06.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

def rawAnchorPolynomial (q₀ : Fin r → TensorIndex d n) :
    MvPolynomial (OrderedFactorIndex d n r) ℂ :=
  ∏ i : Fin r, ∏ j : Fin d, MvPolynomial.X (i,⟨j,q₀ i j⟩)

theorem rawAnchorPolynomial_ne_zero (q₀ : Fin r → TensorIndex d n) :
    rawAnchorPolynomial q₀ ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    Finset.prod_ne_zero_iff.mpr fun j _ => MvPolynomial.X_ne_zero _

theorem exists_decomposition_eval_ne_zero_of_source_pullback
    (q₀ : Fin r → TensorIndex d n) (p : MvPolynomial (TensorIndex d n) ℂ)
    (hp : additionAlgebraHom d n r p ≠ 0) :
    ∃ (A : Tensor ℂ d n) (a : Fin r → Tensor ℂ d n),
      Decomposes a A ∧ MvPolynomial.eval (fun q => A q) p ≠ 0 := by
  classical
  have hraw : (additionAlgebraHom d n r p).val ≠ 0 := by
    intro h
    apply hp
    exact Subtype.ext h
  obtain ⟨x,hx⟩ := Segre.exists_eval_ne_zero
    ((additionAlgebraHom d n r p).val * rawAnchorPolynomial q₀)
    (mul_ne_zero hraw (rawAnchorPolynomial_ne_zero q₀))
  rw [map_mul] at hx
  have hxraw := (mul_ne_zero_iff.mp hx).1
  have hxanchor := (mul_ne_zero_iff.mp hx).2
  let u : Fin r → (j : Fin d) → Fin (n j) → ℂ := fun i j k => x (i,⟨j,k⟩)
  let a : Fin r → Tensor ℂ d n := fun i => pureTensor (u i)
  have hpivot (i : Fin r) : a i (q₀ i) ≠ 0 := by
    have hprod : (∏ i : Fin r, ∏ j : Fin d, x (i,⟨j,q₀ i j⟩)) ≠ 0 := by
      simpa only [rawAnchorPolynomial,map_prod,MvPolynomial.eval_X] using hxanchor
    exact Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  have ha (i : Fin r) : RankOne (a i) := by
    refine ⟨?_,u i,rfl⟩
    intro hzero
    apply hpivot i
    have h := congrArg (fun A : Tensor ℂ d n => A (q₀ i)) hzero
    simpa only [PiLp.zero_apply] using h
  have heval : MvPolynomial.eval x (additionAlgebraHom d n r p).val =
      MvPolynomial.eval (fun q => (∑ i, a i) q) p := by
    have h := AlgHom.congr_fun (character_comp_addition (factorCharacter u)) p
    rw [characterTuple_factorCharacter] at h
    have hxeta : (fun y : OrderedFactorIndex d n r => u y.1 y.2.1 y.2.2) = x := by
      funext y
      rcases y with ⟨i,⟨j,k⟩⟩
      rfl
    simpa only [factorCharacter,AlgHom.comp_apply,MvPolynomial.aeval_eq_eval,
      Subalgebra.val_apply,hxeta,a] using h
  exact ⟨∑ i, a i,a,⟨ha,rfl⟩,heval ▸ hxraw⟩

theorem pivot_pullback_ne_zero_of_source_pullback
    (q₀ : Fin r → TensorIndex d n) (p : MvPolynomial (TensorIndex d n) ℂ)
    (hp : additionAlgebraHom d n r p ≠ 0) : Segre.pullback q₀ p ≠ 0 := by
  obtain ⟨A,a,ha,hpA⟩ := exists_decomposition_eval_ne_zero_of_source_pullback q₀ p hp
  exact Segre.pullback_ne_zero_of_decomposition q₀ p A a ha hpA

#assert_trust kernel rawAnchorPolynomial
#assert_trust kernel rawAnchorPolynomial_ne_zero
#assert_trust kernel exists_decomposition_eval_ne_zero_of_source_pullback
#assert_trust kernel pivot_pullback_ne_zero_of_source_pullback
#print axioms exists_decomposition_eval_ne_zero_of_source_pullback
#print axioms pivot_pullback_ne_zero_of_source_pullback
end NLA.Proofs.TR06.AlgebraicLocus
