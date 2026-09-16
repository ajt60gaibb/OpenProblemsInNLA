import Challenge
import Mathlib.LinearAlgebra.Matrix.SchurComplement
open NLA.IE14
open scoped NNReal
#print NLA.IE14.rowSwap
#print NLA.IE14.schurStep
#print NLA.IE14.trajectory
#print NLA.IE14.AdmissiblePivot
#print NLA.IE14.AdmissiblePath
#print NLA.IE14.entryMaxNN
#print NLA.IE14.entryMax
#print NLA.IE14.activeMaxNN
#print NLA.IE14.growth
#print NLA.IE14.CyclicPosition
#print NLA.IE14.CyclicInput
#print NLA.IE14.cyclicGrowthSet
#print NLA.IE14.sharpConstant
#print NLA.IE14.fibonacciBound
#print NLA.IE14.witnessLower
#print NLA.IE14.witnessUpper
#print NLA.IE14.factorIndex
#print NLA.IE14.witnessMatrix
#print NLA.IE14.witnessPath
#print IsGreatest
#check NLA.IE14.numerical_bounds
#check NLA.IE14.entryMax_semantics
#check NLA.IE14.admissible_path_exists
#check NLA.IE14.all_active_entries_bound
#check NLA.IE14.witness_data
#check NLA.IE14.witness_attainment
#check NLA.IE14.canonical_result
#check Finset.le_sup
#check Finset.sup_le
#check Finset.exists_mem_eq_sup
#check IsGreatest.isLUB
#check IsLUB.csSup_eq
#check Matrix.det_mul
#check Matrix.det_permute
#check Matrix.det_eq_zero_of_column_eq_zero
#check Matrix.det_updateRow_add_smul_self
#check Nat.fib_add_two
#check Nat.fib_le_fib_succ
#check norm_div
#check norm_mul
#check norm_sub_le
#synth Norm ℂ
#synth LinearOrder ℝ≥0
#reduce Nat.fib 5 + 1
#reduce Nat.fib 6 + 1
#reduce Nat.fib 7 + 1
#reduce Nat.fib 8 + 1

#check Matrix.det_fromBlocks₁₁
#check Matrix.det_fromBlocks_one₁₁
