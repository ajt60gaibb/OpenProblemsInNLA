import NLA.IE03.Certificate.Phase4096
import NLA.IE03.Certificate.Sound

/-! Kernel checks for the generated active squares in this phase. -/

namespace NLA.IE03.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem checked_0 :
    stepOK 47 stage4096_0 stage4096_1 3 1 = true := by
  decide +kernel

private theorem checked_1 :
    stepOK 46 stage4096_1 stage4096_2 6 16 = true := by
  decide +kernel

private theorem checked_2 :
    stepOK 45 stage4096_2 stage4096_3 9 4 = true := by
  decide +kernel

private theorem checked_3 :
    stepOK 44 stage4096_3 stage4096_4 16 7 = true := by
  decide +kernel

private theorem checked_4 :
    stepOK 43 stage4096_4 stage4096_5 23 21 = true := by
  decide +kernel

private theorem checked_5 :
    stepOK 42 stage4096_5 stage4096_6 26 24 = true := by
  decide +kernel

private theorem checked_6 :
    stepOK 41 stage4096_6 stage4096_7 12 35 = true := by
  decide +kernel

private theorem checked_7 :
    stepOK 40 stage4096_7 stage4096_8 32 10 = true := by
  decide +kernel

private theorem checked_8 :
    stepOK 39 stage4096_8 stage4096_9 35 16 = true := by
  decide +kernel

private theorem checked_9 :
    stepOK 38 stage4096_9 stage4096_10 38 36 = true := by
  decide +kernel

private theorem checked_10 :
    stepOK 37 stage4096_10 stage4096_11 18 25 = true := by
  decide +kernel

private theorem checked_11 :
    stepOK 36 stage4096_11 stage4096_12 24 29 = true := by
  decide +kernel

private theorem checked_12 :
    stepOK 35 stage4096_12 stage4096_13 24 27 = true := by
  decide +kernel

private theorem checked_13 :
    stepOK 34 stage4096_13 stage4096_14 24 28 = true := by
  decide +kernel

private theorem checked_14 :
    stepOK 33 stage4096_14 stage4096_15 17 13 = true := by
  decide +kernel

private theorem checked_15 :
    stepOK 32 stage4096_15 stage4096_16 16 14 = true := by
  decide +kernel

private theorem checked_16 :
    stepOK 31 stage4096_16 stage4096_17 19 29 = true := by
  decide +kernel

private theorem checked_17 :
    stepOK 30 stage4096_17 stage4096_18 3 26 = true := by
  decide +kernel

private theorem checked_18 :
    stepOK 29 stage4096_18 stage4096_19 29 14 = true := by
  decide +kernel

private theorem checked_19 :
    stepOK 28 stage4096_19 stage4096_20 4 27 = true := by
  decide +kernel

private theorem checked_20 :
    stepOK 27 stage4096_20 stage4096_21 18 25 = true := by
  decide +kernel

private theorem checked_21 :
    stepOK 26 stage4096_21 stage4096_22 21 19 = true := by
  decide +kernel

private theorem checked_22 :
    stepOK 25 stage4096_22 stage4096_23 6 0 = true := by
  decide +kernel

private theorem checked_23 :
    stepOK 24 stage4096_23 stage4096_24 2 9 = true := by
  decide +kernel

private theorem checked_24 :
    stepOK 23 stage4096_24 stage4096_25 18 16 = true := by
  decide +kernel

private theorem checked_25 :
    stepOK 22 stage4096_25 stage4096_26 13 3 = true := by
  decide +kernel

private theorem checked_26 :
    stepOK 21 stage4096_26 stage4096_27 4 5 = true := by
  decide +kernel

private theorem checked_27 :
    stepOK 20 stage4096_27 stage4096_28 1 2 = true := by
  decide +kernel

private theorem checked_28 :
    stepOK 19 stage4096_28 stage4096_29 19 7 = true := by
  decide +kernel

private theorem checked_29 :
    stepOK 18 stage4096_29 stage4096_30 16 0 = true := by
  decide +kernel

private theorem checked_30 :
    stepOK 17 stage4096_30 stage4096_31 8 2 = true := by
  decide +kernel

private theorem checked_31 :
    stepOK 16 stage4096_31 stage4096_32 15 3 = true := by
  decide +kernel

private theorem checked_32 :
    stepOK 15 stage4096_32 stage4096_33 10 7 = true := by
  decide +kernel

private theorem checked_33 :
    stepOK 14 stage4096_33 stage4096_34 7 6 = true := by
  decide +kernel

private theorem checked_34 :
    stepOK 13 stage4096_34 stage4096_35 8 4 = true := by
  decide +kernel

private theorem checked_35 :
    stepOK 12 stage4096_35 stage4096_36 2 6 = true := by
  decide +kernel

private theorem checked_36 :
    stepOK 11 stage4096_36 stage4096_37 10 11 = true := by
  decide +kernel

private theorem checked_37 :
    stepOK 10 stage4096_37 stage4096_38 3 8 = true := by
  decide +kernel

private theorem checked_38 :
    stepOK 9 stage4096_38 stage4096_39 1 5 = true := by
  decide +kernel

private theorem checked_39 :
    stepOK 8 stage4096_39 stage4096_40 2 5 = true := by
  decide +kernel

private theorem checked_40 :
    stepOK 7 stage4096_40 stage4096_41 7 2 = true := by
  decide +kernel

private theorem checked_41 :
    stepOK 6 stage4096_41 stage4096_42 0 1 = true := by
  decide +kernel

private theorem checked_42 :
    stepOK 5 stage4096_42 stage4096_43 0 1 = true := by
  decide +kernel

private theorem checked_43 :
    stepOK 4 stage4096_43 stage4096_44 0 0 = true := by
  decide +kernel

private theorem checked_44 :
    stepOK 3 stage4096_44 stage4096_45 0 0 = true := by
  decide +kernel

private theorem checked_45 :
    stepOK 2 stage4096_45 stage4096_46 0 0 = true := by
  decide +kernel

private theorem checked_46 :
    stepOK 1 stage4096_46 stage4096_47 0 0 = true := by
  decide +kernel

private theorem checked_47 :
    stepOK 0 stage4096_47 stage4096_48 0 0 = true := by
  decide +kernel

private def steps : List Step := [
  (3, 1, stage4096_1), (6, 16, stage4096_2), (9, 4, stage4096_3),
  (16, 7, stage4096_4), (23, 21, stage4096_5), (26, 24, stage4096_6),
  (12, 35, stage4096_7), (32, 10, stage4096_8), (35, 16, stage4096_9),
  (38, 36, stage4096_10), (18, 25, stage4096_11), (24, 29, stage4096_12),
  (24, 27, stage4096_13), (24, 28, stage4096_14), (17, 13, stage4096_15),
  (16, 14, stage4096_16), (19, 29, stage4096_17), (3, 26, stage4096_18),
  (29, 14, stage4096_19), (4, 27, stage4096_20), (18, 25, stage4096_21),
  (21, 19, stage4096_22), (6, 0, stage4096_23), (2, 9, stage4096_24),
  (18, 16, stage4096_25), (13, 3, stage4096_26), (4, 5, stage4096_27),
  (1, 2, stage4096_28), (19, 7, stage4096_29), (16, 0, stage4096_30),
  (8, 2, stage4096_31), (15, 3, stage4096_32), (10, 7, stage4096_33),
  (7, 6, stage4096_34), (8, 4, stage4096_35), (2, 6, stage4096_36),
  (10, 11, stage4096_37), (3, 8, stage4096_38), (1, 5, stage4096_39),
  (2, 5, stage4096_40), (7, 2, stage4096_41), (0, 1, stage4096_42),
  (0, 1, stage4096_43), (0, 0, stage4096_44), (0, 0, stage4096_45),
  (0, 0, stage4096_46), (0, 0, stage4096_47), (0, 0, stage4096_48)
]

theorem phase4096 :
    Trace 48 stage4096_0.entries 0 stage4096_48.entries 4608 := by
  have checked : traceOK 48 stage4096_0 steps = true := by
    simp only [steps, traceOK, Bool.true_and,
      checked_0, checked_1, checked_2, checked_3, checked_4, checked_5,
      checked_6, checked_7, checked_8, checked_9, checked_10, checked_11,
      checked_12, checked_13, checked_14, checked_15, checked_16, checked_17,
      checked_18, checked_19, checked_20, checked_21, checked_22, checked_23,
      checked_24, checked_25, checked_26, checked_27, checked_28, checked_29,
      checked_30, checked_31, checked_32, checked_33, checked_34, checked_35,
      checked_36, checked_37, checked_38, checked_39, checked_40, checked_41,
      checked_42, checked_43, checked_44, checked_45, checked_46, checked_47]
  have growth : peak stage4096_0 steps = 4608 := by decide +kernel
  simpa only [growth, Rat.cast_ofNat] using! trace_sound checked

end NLA.IE03.Certificate
