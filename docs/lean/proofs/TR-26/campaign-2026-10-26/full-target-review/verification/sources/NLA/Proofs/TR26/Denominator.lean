import NLA.Proofs.TR26.BinaryDefinitions

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26
open Polynomial

theorem affineDenominatorOver_zero (R : Type*) [CommSemiring R] :
    affineDenominatorOver R 0 = 1 := by
  simp [affineDenominatorOver]

theorem affineDenominatorOver_succ (R : Type*) [CommSemiring R] (d : ℕ) :
    affineDenominatorOver R (d+1) = affineDenominatorOver R d + X^(2*(d+1)) := by
  unfold affineDenominatorOver
  rw [Fin.sum_univ_castSucc]
  simp

theorem affineDenominatorOver_isMonicOfDegree (R : Type*) [CommSemiring R]
    [Nontrivial R] (d : ℕ) :
    (affineDenominatorOver R d).IsMonicOfDegree (2*d) := by
  induction d with
  | zero => simp [affineDenominatorOver_zero]
  | succ d ih =>
    rw [affineDenominatorOver_succ]
    apply Polynomial.IsMonicOfDegree.add_left _ (isMonicOfDegree_X_pow R (2*(d+1)))
    rw [ih.natDegree_eq]
    omega

theorem affineDenominator_natDegree (d : ℕ) : (affineDenominator d).natDegree = 2*d :=
  (affineDenominatorOver_isMonicOfDegree ℂ d).natDegree_eq

theorem affineDenominator_monic (d : ℕ) : (affineDenominator d).Monic :=
  (affineDenominatorOver_isMonicOfDegree ℂ d).monic

theorem affineDenominator_ne_zero (d : ℕ) : affineDenominator d ≠ 0 :=
  (affineDenominator_monic d).ne_zero

theorem affineDenominatorOver_factor (R : Type*) [CommRing R] (d : ℕ) :
    (X^2-1) * affineDenominatorOver R d = X^(2*d+2)-1 := by
  have hsum : affineDenominatorOver R d = ∑ i ∈ Finset.range (d+1), (X^2)^i := by
    simp only [affineDenominatorOver, Fin.sum_univ_eq_sum_range, pow_mul]
  rw [hsum, mul_geom_sum]
  rw [← pow_mul]
  congr 2

theorem affineDenominator_separable (d : ℕ) : (affineDenominator d).Separable := by
  have hsep : (X^(2*d+2)-C (1 : ℂ)).Separable :=
    separable_X_pow_sub_C 1 (by exact_mod_cast (by omega : 2*d+2 ≠ 0)) one_ne_zero
  apply hsep.of_dvd
  rw [C_1, ← affineDenominatorOver_factor ℂ d]
  exact dvd_mul_left _ _

theorem affineDenominator_eval_zero (d : ℕ) : (affineDenominator d).eval 0 = 1 := by
  induction d with
  | zero => simp [affineDenominatorOver_zero]
  | succ d ih =>
    change (affineDenominatorOver ℂ (d+1)).eval 0 = 1
    change (affineDenominatorOver ℂ d).eval 0 = 1 at ih
    rw [affineDenominatorOver_succ, eval_add, ih]
    simp

theorem affineDenominator_eval_one (d : ℕ) : (affineDenominator d).eval 1 = (d+1 : ℕ) := by
  change evalRingHom (1 : ℂ) (affineDenominatorOver ℂ d) = _
  simp [affineDenominatorOver]

theorem affineDenominator_eval_neg_one (d : ℕ) :
    (affineDenominator d).eval (-1) = (d+1 : ℕ) := by
  change evalRingHom (-1 : ℂ) (affineDenominatorOver ℂ d) = _
  simp [affineDenominatorOver, pow_mul]

def denominatorRoots (d : ℕ) : Finset ℂ := by
  classical
  exact (affineDenominator d).roots.toFinset

theorem mem_denominatorRoots_iff (d : ℕ) (r : ℂ) :
    r ∈ denominatorRoots d ↔ (affineDenominator d).eval r = 0 := by
  classical
  simp [denominatorRoots, Polynomial.mem_roots (affineDenominator_ne_zero d), Polynomial.IsRoot]

theorem denominatorRoots_card (d : ℕ) : (denominatorRoots d).card = 2*d := by
  classical
  rw [denominatorRoots, Multiset.toFinset_card_of_nodup (nodup_roots (affineDenominator_separable d)),
    IsAlgClosed.card_roots_eq_natDegree, affineDenominator_natDegree]

theorem denominator_root_nonzero {d : ℕ} {r : ℂ} (hr : r ∈ denominatorRoots d) : r ≠ 0 := by
  intro hz
  rw [mem_denominatorRoots_iff, hz, affineDenominator_eval_zero] at hr
  exact one_ne_zero hr

theorem denominator_derivative_at_root_ne_zero {d : ℕ} {r : ℂ}
    (hr : r ∈ denominatorRoots d) : (affineDenominator d).derivative.eval r ≠ 0 := by
  have h := (affineDenominator_separable d).aeval_derivative_ne_zero
    ((mem_denominatorRoots_iff d r).mp hr)
  simpa using h

theorem binaryDenominator_eval_zero_one (d : ℕ) :
    binaryEval (binaryDenominator d) 0 1 = 1 := by
  rw [binaryDenominator_eval]
  unfold denominator
  rw [Finset.sum_eq_single (Fin.last d)]
  · simp [veronese]
  · intro i _ hi
    have hiv : i.val < d := by
      have hle : i.val ≤ d := Nat.le_of_lt_succ i.isLt
      have hne : i.val ≠ d := by
        intro he
        apply hi
        exact Fin.ext he
      omega
    have hpos : 0 < d-i.val := Nat.sub_pos_of_lt hiv
    simp [veronese, zero_pow (Nat.ne_of_gt hpos)]
  · simp

#assert_trust kernel affineDenominatorOver_factor
#assert_trust kernel affineDenominator_separable
#assert_trust kernel denominatorRoots_card
#assert_trust kernel binaryDenominator_eval_zero_one
#print axioms affineDenominator_separable
#print axioms denominatorRoots_card
end NLA.Proofs.TR26
