import NLA.IE03.Certificate.Phase1024
import NLA.IE03.Certificate.Sound

/-! Kernel checks for the generated active squares in this phase. -/

namespace NLA.IE03.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem checked_0 :
    stepOK 39 stage1024_0 stage1024_1 3 1 = true := by
  decide +kernel

private theorem checked_1 :
    stepOK 38 stage1024_1 stage1024_2 6 16 = true := by
  decide +kernel

private theorem checked_2 :
    stepOK 37 stage1024_2 stage1024_3 9 35 = true := by
  decide +kernel

private theorem checked_3 :
    stepOK 36 stage1024_3 stage1024_4 16 23 = true := by
  decide +kernel

private theorem checked_4 :
    stepOK 35 stage1024_4 stage1024_5 19 30 = true := by
  decide +kernel

private theorem checked_5 :
    stepOK 34 stage1024_5 stage1024_6 22 26 = true := by
  decide +kernel

private theorem checked_6 :
    stepOK 33 stage1024_6 stage1024_7 25 12 = true := by
  decide +kernel

private theorem checked_7 :
    stepOK 32 stage1024_7 stage1024_8 32 18 = true := by
  decide +kernel

private theorem checked_8 :
    stepOK 31 stage1024_8 stage1024_9 28 4 = true := by
  decide +kernel

private theorem checked_9 :
    stepOK 30 stage1024_9 stage1024_10 9 8 = true := by
  decide +kernel

private theorem checked_10 :
    stepOK 29 stage1024_10 stage1024_11 9 6 = true := by
  decide +kernel

private theorem checked_11 :
    stepOK 28 stage1024_11 stage1024_12 9 7 = true := by
  decide +kernel

private theorem checked_12 :
    stepOK 27 stage1024_12 stage1024_13 11 18 = true := by
  decide +kernel

private theorem checked_13 :
    stepOK 26 stage1024_13 stage1024_14 11 8 = true := by
  decide +kernel

private theorem checked_14 :
    stepOK 25 stage1024_14 stage1024_15 8 1 = true := by
  decide +kernel

private theorem checked_15 :
    stepOK 24 stage1024_15 stage1024_16 7 1 = true := by
  decide +kernel

private theorem checked_16 :
    stepOK 23 stage1024_16 stage1024_17 16 14 = true := by
  decide +kernel

private theorem checked_17 :
    stepOK 22 stage1024_17 stage1024_18 21 22 = true := by
  decide +kernel

private theorem checked_18 :
    stepOK 21 stage1024_18 stage1024_19 16 6 = true := by
  decide +kernel

private theorem checked_19 :
    stepOK 20 stage1024_19 stage1024_20 2 7 = true := by
  decide +kernel

private theorem checked_20 :
    stepOK 19 stage1024_20 stage1024_21 12 7 = true := by
  decide +kernel

private theorem checked_21 :
    stepOK 18 stage1024_21 stage1024_22 1 12 = true := by
  decide +kernel

private theorem checked_22 :
    stepOK 17 stage1024_22 stage1024_23 17 16 = true := by
  decide +kernel

private theorem checked_23 :
    stepOK 16 stage1024_23 stage1024_24 11 3 = true := by
  decide +kernel

private theorem checked_24 :
    stepOK 15 stage1024_24 stage1024_25 14 2 = true := by
  decide +kernel

private theorem checked_25 :
    stepOK 14 stage1024_25 stage1024_26 8 10 = true := by
  decide +kernel

private theorem checked_26 :
    stepOK 13 stage1024_26 stage1024_27 12 7 = true := by
  decide +kernel

private theorem checked_27 :
    stepOK 12 stage1024_27 stage1024_28 8 5 = true := by
  decide +kernel

private def steps : List Step := [
  (3, 1, stage1024_1), (6, 16, stage1024_2), (9, 35, stage1024_3),
  (16, 23, stage1024_4), (19, 30, stage1024_5), (22, 26, stage1024_6),
  (25, 12, stage1024_7), (32, 18, stage1024_8), (28, 4, stage1024_9),
  (9, 8, stage1024_10), (9, 6, stage1024_11), (9, 7, stage1024_12),
  (11, 18, stage1024_13), (11, 8, stage1024_14), (8, 1, stage1024_15),
  (7, 1, stage1024_16), (16, 14, stage1024_17), (21, 22, stage1024_18),
  (16, 6, stage1024_19), (2, 7, stage1024_20), (12, 7, stage1024_21),
  (1, 12, stage1024_22), (17, 16, stage1024_23), (11, 3, stage1024_24),
  (14, 2, stage1024_25), (8, 10, stage1024_26), (12, 7, stage1024_27),
  (8, 5, stage1024_28)
]

theorem phase1024 :
    Trace 40 stage1024_0.entries 12 stage1024_28.entries 256 := by
  have checked : traceOK 40 stage1024_0 steps = true := by
    simp only [steps, traceOK, Bool.true_and,
      checked_0, checked_1, checked_2, checked_3, checked_4, checked_5,
      checked_6, checked_7, checked_8, checked_9, checked_10, checked_11,
      checked_12, checked_13, checked_14, checked_15, checked_16, checked_17,
      checked_18, checked_19, checked_20, checked_21, checked_22, checked_23,
      checked_24, checked_25, checked_26, checked_27]
  have growth : peak stage1024_0 steps = 256 := by decide +kernel
  simpa only [growth, Rat.cast_ofNat] using! trace_sound checked

end NLA.IE03.Certificate
