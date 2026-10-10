import NLA.Proofs.TR14.LocalUnitRoot
import NLA.Proofs.TR14.LocalFourierFilter
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
Exact one-factor Fourier decomposition of a Frobenius functional on
`ℂ[z]/(z^ℓ)`. Evaluation occurs only after taking the canonical degree-`<ℓ`
polynomial representative. No CRT or global tensor width is asserted.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open Polynomial Module
open scoped BigOperators Polynomial
noncomputable section

/-- The canonical monic remainder of a truncated local class. -/
def localRepresentative (ℓ : ℕ) (a : LocalTruncated ℓ) : Polynomial ℂ :=
  AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow ℓ) a

theorem localRepresentative_mk (ℓ : ℕ) (a : LocalTruncated ℓ) :
    AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ)
      (localRepresentative ℓ a) = a := by
  exact AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow ℓ) a

/-- Every representative has degree at most `ℓ-1`, including zero. -/
theorem localRepresentative_natDegree_le (ℓ : ℕ) (hℓ : 0 < ℓ)
    (a : LocalTruncated ℓ) :
    (localRepresentative ℓ a).natDegree ≤ ℓ - 1 := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  change (p %ₘ ((Polynomial.X : Polynomial ℂ) ^ ℓ)).natDegree ≤ ℓ - 1
  have hX : ((Polynomial.X : Polynomial ℂ) ^ ℓ) ≠ 1 := by
    intro heq
    have hd := congrArg Polynomial.natDegree heq
    simp at hd
    omega
  have hd := Polynomial.natDegree_modByMonic_lt p
    (Polynomial.monic_X_pow ℓ) hX
  simpa only [Polynomial.natDegree_X_pow] using Nat.le_sub_one_of_lt hd

/-- Evaluation of the canonical representative of `w*a` at one Fourier
node, as a complex-linear functional of `a`. -/
def localFourierFunctional (m ℓ : ℕ) (_hℓ : 0 < ℓ)
    (w : LocalTruncated ℓ) (ζ : ℂ)
    (j : Fin (localFourierCount m ℓ)) : LocalTruncated ℓ →ₗ[ℂ] ℂ :=
  (Polynomial.leval (ζ ^ j.val)).comp
    ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow ℓ)).comp
      (LinearMap.mulLeft ℂ w))

theorem localFourierFunctional_apply (m ℓ : ℕ) (hℓ : 0 < ℓ)
    (w : LocalTruncated ℓ) (ζ : ℂ) (j : Fin (localFourierCount m ℓ))
    (a : LocalTruncated ℓ) :
    localFourierFunctional m ℓ hℓ w ζ j a =
      (localRepresentative ℓ (w * a)).eval (ζ ^ j.val) := rfl

private theorem localRepresentative_prod_degree (m ℓ : ℕ) (hℓ : 0 < ℓ)
    (w : LocalTruncated ℓ) (a : Fin m → LocalTruncated ℓ) :
    (∏ k : Fin m, localRepresentative ℓ (w * a k)).natDegree ≤
      m * (ℓ - 1) := by
  calc
    (∏ k : Fin m, localRepresentative ℓ (w * a k)).natDegree ≤
        ∑ k : Fin m, (localRepresentative ℓ (w * a k)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _k : Fin m, (ℓ - 1) := by
      apply Finset.sum_le_sum
      intro k _
      exact localRepresentative_natDegree_le ℓ hℓ (w * a k)
    _ = m * (ℓ - 1) := by simp

private theorem localRepresentative_prod_mk (m ℓ : ℕ)
    (w : LocalTruncated ℓ) (a : Fin m → LocalTruncated ℓ) :
    AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ)
      (∏ k : Fin m, localRepresentative ℓ (w * a k)) =
        w ^ m * ∏ k : Fin m, a k := by
  rw [map_prod]
  calc
    (∏ k : Fin m,
      AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ)
        (localRepresentative ℓ (w * a k))) =
        ∏ k : Fin m, w * a k := by
          apply Finset.prod_congr rfl
          intro k _
          exact localRepresentative_mk ℓ (w * a k)
    _ = w ^ m * ∏ k : Fin m, a k := by
      rw [Finset.prod_mul_distrib]
      simp

private theorem localRepresentative_prod_eval (m ℓ : ℕ)
    (w : LocalTruncated ℓ) (a : Fin m → LocalTruncated ℓ)
    (x : ℂ) :
    (∏ k : Fin m, localRepresentative ℓ (w * a k)).eval x =
      ∏ k : Fin m, (localRepresentative ℓ (w * a k)).eval x := by
  simpa only using Polynomial.eval_prod (Finset.univ : Finset (Fin m))
    (fun k : Fin m => localRepresentative ℓ (w * a k)) x

/-- One local Frobenius functional is exactly a sum of `N` symmetric
products of the same linear factors in all `m` modes. -/
theorem local_fourier_multilinear (m ℓ : ℕ)
    (hm : 3 ≤ m) (hℓ : 0 < ℓ)
    (Λ : LocalTruncated ℓ →ₗ[ℂ] ℂ)
    (hFrob : ∀ a : LocalTruncated ℓ,
      (∀ b : LocalTruncated ℓ, Λ (a * b) = 0) → a = 0) :
    ∃ w : LocalTruncated ℓ, ∃ ζ : ℂ,
      IsPrimitiveRoot ζ (localFourierCount m ℓ) ∧
      w ^ m = localFrobeniusElement ℓ hℓ Λ ∧
      ∀ a : Fin m → LocalTruncated ℓ,
        Λ (∏ k, a k) =
          ∑ j : Fin (localFourierCount m ℓ),
            (localFourierCount m ℓ : ℂ)⁻¹ *
              ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ *
              ∏ k, localFourierFunctional m ℓ hℓ w ζ j (a k) := by
  have hu0 := localFrobenius_const_ne_zero ℓ hℓ Λ hFrob
  obtain ⟨w, hw⟩ := local_unit_has_nth_root ℓ m hℓ (by omega)
    (localFrobeniusElement ℓ hℓ Λ) hu0
  obtain ⟨ζ, hζ⟩ := local_fourier_primitive_exists m ℓ
  refine ⟨w, ζ, hζ, hw, ?_⟩
  intro a
  let P : Polynomial ℂ := ∏ k : Fin m, localRepresentative ℓ (w * a k)
  have hdeg : P.natDegree ≤ m * (ℓ - 1) :=
    localRepresentative_prod_degree m ℓ hℓ w a
  have hmk : AdjoinRoot.mk ((Polynomial.X : Polynomial ℂ) ^ ℓ) P =
      w ^ m * ∏ k : Fin m, a k :=
    localRepresentative_prod_mk m ℓ w a
  have htop : localTopCoeff ℓ hℓ
      (localFrobeniusElement ℓ hℓ Λ * ∏ k : Fin m, a k) =
      P.coeff (ℓ - 1) := by
    rw [← hw, ← hmk]
    exact localCoeffNat_mk ℓ P (ℓ - 1) (by omega)
  have heval (j : Fin (localFourierCount m ℓ)) :
      (∑ k : Fin (m * (ℓ - 1) + 1),
        P.coeff k.val * (ζ ^ j.val) ^ k.val) = P.eval (ζ ^ j.val) := by
    have he := Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le hdeg) (ζ ^ j.val)
    have hfin := Fin.sum_univ_eq_sum_range
      (fun i : ℕ => P.coeff i * (ζ ^ j.val) ^ i)
      (m * (ℓ - 1) + 1)
    exact hfin.trans he.symm
  have hfilter := primitive_fourier_coefficient_inv m ℓ hm (by omega) hζ
    (fun k : Fin (m * (ℓ - 1) + 1) => P.coeff k.val)
  have hfilter' :
      (localFourierCount m ℓ : ℂ)⁻¹ *
        (∑ j : Fin (localFourierCount m ℓ),
          ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ * P.eval (ζ ^ j.val)) =
        P.coeff (ℓ - 1) := by
    simpa only [heval] using hfilter
  calc
    Λ (∏ k, a k) = localTopCoeff ℓ hℓ
        (localFrobeniusElement ℓ hℓ Λ * ∏ k : Fin m, a k) :=
      localFrobenius_repr ℓ hℓ Λ _
    _ = P.coeff (ℓ - 1) := htop
    _ = (localFourierCount m ℓ : ℂ)⁻¹ *
        (∑ j : Fin (localFourierCount m ℓ),
          ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ * P.eval (ζ ^ j.val)) := hfilter'.symm
    _ = ∑ j : Fin (localFourierCount m ℓ),
          (localFourierCount m ℓ : ℂ)⁻¹ *
            ((ζ ^ j.val) ^ (ℓ - 1))⁻¹ *
            ∏ k, localFourierFunctional m ℓ hℓ w ζ j (a k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [localRepresentative_prod_eval m ℓ w a (ζ ^ j.val)]
      simp only [localFourierFunctional_apply]
      ring

#assert_trust kernel localRepresentative_natDegree_le
#assert_trust kernel localFourierFunctional
#assert_trust kernel localRepresentative_prod_degree
#assert_trust kernel localRepresentative_prod_mk
#assert_trust kernel local_fourier_multilinear
#print axioms local_fourier_multilinear

end
end NLA.Proofs.TR14
