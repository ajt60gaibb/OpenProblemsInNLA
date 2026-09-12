"""Emit rational tables; Lean independently checks every matrix identity.
The frozen Fraction reconstruction supplies data, never a trusted premise.
"""
from fractions import Fraction
from pathlib import Path
import json
project=Path(__file__).resolve().parents[1]
x=json.loads((project/'reviews/reconstruction.json').read_text())
def q(s):
 f=Fraction(s)
 if f.denominator==1:return str(f.numerator)
 return f'({f.numerator} / {f.denominator})'
def matrix(key):
 return '!!['+';\n    '.join(', '.join(q(a) for a in row) for row in x[key])+']'
header='''/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact rational certificates for the disclosed adaptation of Colbrook's MI-22
counterexample. Each displayed table is verified by ordinary kernel-checked
finite matrix algebra; generated rational data are not assumed as premises.
The addition chain T²,T⁴,T⁸ uses only three non-diagonal matrix products.
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.MI22.Witness

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI22

'''
s=header
for k,name in [('T2','t2Data'),('T4','t4Data'),('T8','t8Data'),('B','bData'),('AB','abData')]:
 s+=f'private def {name} : Mat 3 :=\n  {matrix(k)}\n\n'
s+='private def nRowData : Fin 3 → ℂ :=\n  !['+', '.join(q(v) for v in x['N'][0])+']\n\n'
simp='Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,\n      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail'
for name,lhs,rhs,defs in [
 ('t2_certificate','witnessT * witnessT','t2Data','witnessT, t2Data'),
 ('t4_certificate','t2Data * t2Data','t4Data','t2Data, t4Data'),
 ('t8_certificate','t4Data * t4Data','t8Data','t4Data, t8Data'),
 ('b_certificate','witnessD * t8Data * witnessD','bData','witnessD, t8Data, bData'),
 ('ab_certificate','Matrix.diagonal (![256, 1 / 256, 1] : Fin 3 → ℂ) * bData','abData','bData, abData')]:
 s+=f'private theorem {name} : {lhs} = {rhs} := by\n  ext i j\n  fin_cases i <;> fin_cases j <;>\n    norm_num [{defs}, {simp}]\n\n'
s+='''private theorem witnessT_pow_eight_data : witnessT ^ (8 : ℕ) = t8Data := by
  calc
    witnessT ^ (8 : ℕ) =
        ((witnessT * witnessT) * (witnessT * witnessT)) *
          ((witnessT * witnessT) * (witnessT * witnessT)) := by
      simp only [← pow_two, ← pow_mul]
      norm_num
    _ = t8Data := by rw [t2_certificate, t4_certificate, t8_certificate]

private theorem witnessB_data : witnessB = bData := by
  rw [witnessB, witnessT_pow_eight_data, b_certificate]

private theorem witnessAB_data : witnessA * witnessB = abData := by
  rw [witnessA_diagonal, witnessB_data, ab_certificate]

private theorem witnessN_row_data (j : Fin 3) : witnessN 0 j = nRowData j := by
  rw [witnessN, witnessB_data]
  fin_cases j <;>
    norm_num [witnessAFiveEighths, witnessT, witnessD, bData, nRowData,
      Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

'''
s+='theorem witnessB_trace_lt : witnessB.trace.re < (4 : ℝ) ^ (8 : ℕ) := by\n  rw [witnessB_data]\n  norm_num [bData, Matrix.trace, Fin.sum_univ_succ, Matrix.diag_apply,\n    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]\n\n'
s+='''theorem witnessTestValue_gt : (44000 : ℝ) < witnessTestValue := by
  unfold witnessTestValue
  change 44000 < (∑ j, witnessN 0 j * witnessVector j).re
  simp only [witnessN_row_data]
  norm_num [nRowData, witnessVector, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

'''
s+='''theorem witnessAB_frobeniusSquared_lt :
    frobeniusSquared (witnessA * witnessB) < (10500 : ℝ) ^ (2 : ℕ) := by
  rw [witnessAB_data]
  norm_num [frobeniusSquared, abData, Fin.sum_univ_succ,
    Complex.normSq_apply, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end NLA.MI22
'''
(project/'NLA/MI22/ExactData.lean').write_text(s)
print('Generated kernel-checkable ExactData.lean:',len(s),'bytes')
