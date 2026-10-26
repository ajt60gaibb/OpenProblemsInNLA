import NLA.Proofs.TR26.WronskianLinear

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

def binaryNumeratorLinear (d : ℕ) : Parameter d →ₗ[ℂ] BinaryForm ℂ where
  toFun := binaryNumerator
  map_add' H K := by
    change binaryNumeratorOver (H+K) = binaryNumeratorOver H + binaryNumeratorOver K
    unfold binaryNumeratorOver
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : coordinateEntry (H+K) i j = coordinateEntry H i j+coordinateEntry K i j := by
      unfold coordinateEntry
      split_ifs <;> rfl
    rw [hentry, map_add, add_mul, add_mul]
  map_smul' c H := by
    change binaryNumeratorOver (c • H) = c • binaryNumeratorOver H
    unfold binaryNumeratorOver
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hentry : coordinateEntry (c • H) i j = c*coordinateEntry H i j := by
      unfold coordinateEntry
      split_ifs <;> rfl
    rw [hentry, map_mul, MvPolynomial.smul_eq_C_mul]
    ring

theorem binaryNumerator_add {d : ℕ} (H K : Parameter d) :
    binaryNumerator (H+K) = binaryNumerator H + binaryNumerator K :=
  (binaryNumeratorLinear d).map_add H K

theorem binaryNumerator_smul {d : ℕ} (c : ℂ) (H : Parameter d) :
    binaryNumerator (c • H) = c • binaryNumerator H :=
  (binaryNumeratorLinear d).map_smul c H

def binaryWronskianLinear (d : ℕ) : Parameter d →ₗ[ℂ] BinaryForm ℂ where
  toFun := binaryWronskian
  map_add' H K := by
    change binaryWronskianOver (H+K) = binaryWronskianOver H + binaryWronskianOver K
    unfold binaryWronskianOver
    rw [show binaryNumeratorOver (H+K) = binaryNumeratorOver H + binaryNumeratorOver K
      from binaryNumerator_add H K]
    simp only [map_add]
    ring
  map_smul' c H := by
    change binaryWronskianOver (c • H) = c • binaryWronskianOver H
    unfold binaryWronskianOver
    rw [show binaryNumeratorOver (c • H) = c • binaryNumeratorOver H
      from binaryNumerator_smul c H]
    simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul]
    ring

theorem binaryWronskianLinear_apply {d : ℕ} (H : Parameter d) :
    binaryWronskianLinear d H = binaryWronskian H := rfl

def binaryCriticalLinear (d : ℕ) (a b : ℂ) : Parameter d →ₗ[ℂ] ℂ :=
  (MvPolynomial.aeval ![a,b]).toLinearMap.comp (binaryWronskianLinear d)

theorem binaryCriticalLinear_apply {d : ℕ} (H : Parameter d) (a b : ℂ) :
    binaryCriticalLinear d a b H = binaryEval (binaryWronskian H) a b := by
  change (MvPolynomial.aeval ![a,b]) (binaryWronskian H) = _
  rfl

#assert_trust kernel binaryNumerator_add
#assert_trust kernel binaryWronskianLinear_apply
#assert_trust kernel binaryCriticalLinear_apply
#print axioms binaryCriticalLinear_apply
end NLA.Proofs.TR26
