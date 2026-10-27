import NLA.Proofs.TR26.Wronskian
import Mathlib.Data.Fin.Rev

/-! Reversal in the original independent symmetric-matrix coordinates swaps
the two binary variables. Its Wronskian acquires the exact orientation sign. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

def reverseSymIndex (d : ℕ) (ij : SymIndex d) : SymIndex d :=
  ⟨(ij.val.2.rev,ij.val.1.rev),Fin.rev_le_rev.mpr ij.property⟩

theorem reverseSymIndex_involutive (d : ℕ) : Function.Involutive (reverseSymIndex d) := by
  intro ij
  apply Subtype.ext
  simp [reverseSymIndex]

def reverseParameterOver {R : Type*} {d : ℕ} (H : SymIndex d → R) : SymIndex d → R :=
  fun ij => H (reverseSymIndex d ij)

abbrev reverseParameter {d : ℕ} (H : Parameter d) : Parameter d := reverseParameterOver H

theorem reverseParameterOver_involutive {R : Type*} (d : ℕ) :
    Function.Involutive (@reverseParameterOver R d) := by
  intro H
  funext ij
  exact congrArg H (reverseSymIndex_involutive d ij)

theorem reverseParameter_ne_zero_iff {d : ℕ} (H : Parameter d) :
    reverseParameter H ≠ 0 ↔ H ≠ 0 := by
  constructor
  · intro h hz
    apply h
    rw [hz]
    rfl
  · intro h hz
    apply h
    have hh := congrArg reverseParameter hz
    change reverseParameterOver (reverseParameterOver H)=reverseParameterOver (0 : Parameter d) at hh
    rw [reverseParameterOver_involutive d H] at hh
    exact hh

theorem coordinateEntry_reverse {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) (i j : Index d) :
    coordinateEntry (reverseParameterOver H) i j = coordinateEntry H j.rev i.rev := by
  classical
  by_cases h : i ≤ j
  · have hr : j.rev ≤ i.rev := Fin.rev_le_rev.mpr h
    simp only [coordinateEntry,dif_pos h,dif_pos hr,reverseParameterOver,reverseSymIndex]
  · have hr : ¬ j.rev ≤ i.rev := by simpa only [Fin.rev_le_rev] using h
    simp only [coordinateEntry,dif_neg h,dif_neg hr,reverseParameterOver,reverseSymIndex]

theorem coordinateEntry_comm {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) (i j : Index d) : coordinateEntry H i j=coordinateEntry H j i := by
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have he := le_antisymm hij hji
      subst j
      rfl
    · simp [coordinateEntry,hij,hji]
  · have hji : j ≤ i := (lt_of_not_ge hij).le
    simp [coordinateEntry,hij,hji]

@[simp] theorem fin2_rev_zero : Fin.rev (0 : Fin 2)=1 := rfl
@[simp] theorem fin2_rev_one : Fin.rev (1 : Fin 2)=0 := rfl

theorem binaryVeronese_rename_rev {R : Type*} [CommSemiring R]
    (d : ℕ) (i : Index d) :
    MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) (binaryVeroneseOver R d i)=
      binaryVeroneseOver R d i.rev := by
  have hi : i.val ≤ d := Nat.le_of_lt_succ i.isLt
  have hrev : i.rev.val=d-i.val := by rw [Fin.val_rev]; omega
  have hrevrev : d-i.rev.val=i.val := by omega
  simp only [binaryVeroneseOver,map_mul,map_pow,MvPolynomial.rename_X,fin2_rev_zero,fin2_rev_one]
  rw [hrevrev,hrev]
  ring

theorem binaryDenominator_rename_rev {R : Type*} [CommSemiring R] (d : ℕ) :
    MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) (binaryDenominatorOver R d)=
      binaryDenominatorOver R d := by
  unfold binaryDenominatorOver
  simp only [map_sum,map_mul,binaryVeronese_rename_rev]
  exact Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Index d))
    (fun i => binaryVeroneseOver R d i*binaryVeroneseOver R d i)

theorem binaryNumerator_reverse {R : Type*} [CommSemiring R] {d : ℕ}
    (H : SymIndex d → R) :
    binaryNumeratorOver (reverseParameterOver H)=
      MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) (binaryNumeratorOver H) := by
  classical
  unfold binaryNumeratorOver
  simp only [map_sum,map_mul,MvPolynomial.rename_C,binaryVeronese_rename_rev]
  apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Index d)) _ _
  intro i
  apply Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Index d)) _ _
  intro j
  simp only [Fin.revPerm_apply,Fin.rev_rev,coordinateEntry_reverse]
  rw [coordinateEntry_comm H j.rev i.rev]

theorem binary_pderiv_rename_rev {R : Type*} [CommSemiring R]
    (i : Fin 2) (P : BinaryForm R) :
    MvPolynomial.pderiv i (MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) P)=
      MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) (MvPolynomial.pderiv i.rev P) := by
  simpa only [Fin.rev_rev] using MvPolynomial.pderiv_rename Fin.rev_injective i.rev P

theorem binaryWronskian_reverse {R : Type*} [CommRing R] [Algebra ℂ R] {d : ℕ}
    (H : SymIndex d → R) :
    binaryWronskianOver (reverseParameterOver H)=
      -MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) (binaryWronskianOver H) := by
  have hD0 : MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2)
      (MvPolynomial.pderiv 0 (binaryDenominatorOver R d))=
        MvPolynomial.pderiv 1 (binaryDenominatorOver R d) := by
    have hh := binary_pderiv_rename_rev (1 : Fin 2) (binaryDenominatorOver R d)
    rw [fin2_rev_one,binaryDenominator_rename_rev] at hh
    exact hh.symm
  have hD1 : MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2)
      (MvPolynomial.pderiv 1 (binaryDenominatorOver R d))=
        MvPolynomial.pderiv 0 (binaryDenominatorOver R d) := by
    have hh := binary_pderiv_rename_rev (0 : Fin 2) (binaryDenominatorOver R d)
    rw [fin2_rev_zero,binaryDenominator_rename_rev] at hh
    exact hh.symm
  unfold binaryWronskianOver
  rw [binaryNumerator_reverse]
  simp only [binary_pderiv_rename_rev,map_mul,map_sub,MvPolynomial.rename_C]
  rw [hD0,hD1]
  simp only [fin2_rev_zero,fin2_rev_one]
  ring

theorem binaryWronskian_reverse_partial {R : Type*} [CommRing R] [Algebra ℂ R] {d : ℕ}
    (H : SymIndex d → R) (i : Fin 2) :
    MvPolynomial.pderiv i (binaryWronskianOver (reverseParameterOver H))=
      -MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2)
        (MvPolynomial.pderiv i.rev (binaryWronskianOver H)) := by
  rw [binaryWronskian_reverse,map_neg,binary_pderiv_rename_rev]

theorem binaryEval_rename_rev (P : BinaryForm ℂ) (a b : ℂ) :
    binaryEval (MvPolynomial.rename (Fin.rev : Fin 2 → Fin 2) P) a b=binaryEval P b a := by
  change MvPolynomial.eval ![a,b] (MvPolynomial.rename Fin.rev P)=MvPolynomial.eval ![b,a] P
  rw [MvPolynomial.eval_rename]
  have hfun : ![a,b] ∘ (Fin.rev : Fin 2 → Fin 2)=![b,a] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

theorem binaryDenominator_eval_swap (d : ℕ) (a b : ℂ) :
    binaryEval (binaryDenominator d) a b=binaryEval (binaryDenominator d) b a := by
  have hh := binaryEval_rename_rev (binaryDenominator d) a b
  rw [binaryDenominator_rename_rev] at hh
  exact hh

theorem binaryWronskian_reverse_partial_eval {d : ℕ} (H : Parameter d)
    (i : Fin 2) (a b : ℂ) :
    binaryEval (MvPolynomial.pderiv i (binaryWronskian (reverseParameter H))) a b=
      -binaryEval (MvPolynomial.pderiv i.rev (binaryWronskian H)) b a := by
  rw [binaryWronskian_reverse_partial]
  change MvPolynomial.eval ![a,b] (-MvPolynomial.rename Fin.rev
    (MvPolynomial.pderiv i.rev (binaryWronskian H)))=_
  rw [map_neg]
  change -binaryEval (MvPolynomial.rename Fin.rev
    (MvPolynomial.pderiv i.rev (binaryWronskian H))) a b=_
  rw [binaryEval_rename_rev]

theorem binaryWronskian_reverse_double_root_iff {d : ℕ} (H : Parameter d) (a b : ℂ) :
    (binaryEval (MvPolynomial.pderiv 0 (binaryWronskian (reverseParameter H))) a b=0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian (reverseParameter H))) a b=0) ↔
    (binaryEval (MvPolynomial.pderiv 0 (binaryWronskian H)) b a=0 ∧
      binaryEval (MvPolynomial.pderiv 1 (binaryWronskian H)) b a=0) := by
  rw [binaryWronskian_reverse_partial_eval,binaryWronskian_reverse_partial_eval]
  simp [and_comm]

#assert_trust kernel reverseParameter_ne_zero_iff
#assert_trust kernel binaryNumerator_reverse
#assert_trust kernel binaryDenominator_rename_rev
#assert_trust kernel binaryWronskian_reverse
#assert_trust kernel binaryWronskian_reverse_double_root_iff
#print axioms binaryWronskian_reverse
end NLA.Proofs.TR26
