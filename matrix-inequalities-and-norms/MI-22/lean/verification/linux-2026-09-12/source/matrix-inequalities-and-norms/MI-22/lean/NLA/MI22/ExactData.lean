/-
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

private def t2Data : Mat 3 :=
  !![(22871477 / 67108864), (-428965 / 67108864), (-13834509 / 67108864);
    (-428965 / 67108864), (3034903643 / 67108864), (-46736521 / 33554432);
    (-13834509 / 67108864), (-46736521 / 33554432), (23053431 / 33554432)]

private def t4Data : Mat 3 :=
  !![(714682110403835 / 4503599627370496), (-9262431772211 / 2251799813685248), (-914184788239021 / 4503599627370496);
    (-9262431772211 / 2251799813685248), (4609688757943188219 / 2251799813685248), (-287985489816153025 / 4503599627370496);
    (-914184788239021 / 4503599627370496), (-287985489816153025 / 4503599627370496), (11054445943491889 / 4503599627370496)]

private def t8Data : Mat 3 :=
  !![(673423758274121261826888529875 / 10141204801825835211973625643008), (92471004188610328280299703401319 / 20282409603651670423947251286016), (-2712132968045408731883242334827 / 10141204801825835211973625643008);
    (92471004188610328280299703401319 / 20282409603651670423947251286016), (85079857423119073377444115764825532553 / 20282409603651670423947251286016), (-2658230452807100476146652411645448313 / 20282409603651670423947251286016);
    (-2712132968045408731883242334827 / 10141204801825835211973625643008), (-2658230452807100476146652411645448313 / 20282409603651670423947251286016), (83058678853594209576652847052477387 / 20282409603651670423947251286016)]

private def bData : Mat 3 :=
  !![(673423758274121261826888529875 / 39614081257132168796771975168), (92471004188610328280299703401319 / 20282409603651670423947251286016), (-2712132968045408731883242334827 / 633825300114114700748351602688);
    (92471004188610328280299703401319 / 20282409603651670423947251286016), (85079857423119073377444115764825532553 / 5192296858534827628530496329220096), (-2658230452807100476146652411645448313 / 324518553658426726783156020576256);
    (-2712132968045408731883242334827 / 633825300114114700748351602688), (-2658230452807100476146652411645448313 / 324518553658426726783156020576256), (83058678853594209576652847052477387 / 20282409603651670423947251286016)]

private def abData : Mat 3 :=
  !![(673423758274121261826888529875 / 154742504910672534362390528), (92471004188610328280299703401319 / 79228162514264337593543950336), (-2712132968045408731883242334827 / 2475880078570760549798248448);
    (92471004188610328280299703401319 / 5192296858534827628530496329220096), (85079857423119073377444115764825532553 / 1329227995784915872903807060280344576), (-2658230452807100476146652411645448313 / 83076749736557242056487941267521536);
    (-2712132968045408731883242334827 / 633825300114114700748351602688), (-2658230452807100476146652411645448313 / 324518553658426726783156020576256), (83058678853594209576652847052477387 / 20282409603651670423947251286016)]

private def nRowData : Fin 3 → ℂ :=
  ![(409172625396623657076885219923830644559 / 83076749736557242056487941267521536), (875289420094780510550012813019209678988577 / 21267647932558653966460912964485513216), (-28116023585552052452176919578995603370897 / 1329227995784915872903807060280344576)]

private theorem t2_certificate : witnessT * witnessT = t2Data := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessT, t2Data, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem t4_certificate : t2Data * t2Data = t4Data := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [t2Data, t4Data, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem t8_certificate : t4Data * t4Data = t8Data := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [t4Data, t8Data, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem b_certificate : witnessD * t8Data * witnessD = bData := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessD, t8Data, bData, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem ab_certificate : Matrix.diagonal (![256, 1 / 256, 1] : Fin 3 → ℂ) * bData = abData := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bData, abData, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

private theorem witnessT_pow_eight_data : witnessT ^ (8 : ℕ) = t8Data := by
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

theorem witnessB_trace_lt : witnessB.trace.re < (4 : ℝ) ^ (8 : ℕ) := by
  rw [witnessB_data]
  norm_num [bData, Matrix.trace, Fin.sum_univ_succ, Matrix.diag_apply,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem witnessTestValue_gt : (44000 : ℝ) < witnessTestValue := by
  unfold witnessTestValue
  change 44000 < (∑ j, witnessN 0 j * witnessVector j).re
  simp only [witnessN_row_data]
  norm_num [nRowData, witnessVector, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem witnessAB_frobeniusSquared_lt :
    frobeniusSquared (witnessA * witnessB) < (10500 : ℝ) ^ (2 : ℕ) := by
  rw [witnessAB_data]
  norm_num [frobeniusSquared, abData, Fin.sum_univ_succ,
    Complex.normSq_apply, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

end NLA.MI22
