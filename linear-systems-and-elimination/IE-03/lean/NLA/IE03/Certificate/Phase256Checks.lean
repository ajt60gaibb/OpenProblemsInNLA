import NLA.IE03.Certificate.Phase256
import NLA.IE03.Certificate.Sound

/-! Kernel checks for the generated active squares in this phase. -/

namespace NLA.IE03.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem checked_0 :
    stepOK 31 stage256_0 stage256_1 3 1 = true := by
  decide +kernel

private theorem checked_1 :
    stepOK 30 stage256_1 stage256_2 10 8 = true := by
  decide +kernel

private theorem checked_2 :
    stepOK 29 stage256_2 stage256_3 13 15 = true := by
  decide +kernel

private theorem checked_3 :
    stepOK 28 stage256_3 stage256_4 16 26 = true := by
  decide +kernel

private theorem checked_4 :
    stepOK 27 stage256_4 stage256_5 19 18 = true := by
  decide +kernel

private theorem checked_5 :
    stepOK 26 stage256_5 stage256_6 22 11 = true := by
  decide +kernel

private theorem checked_6 :
    stepOK 25 stage256_6 stage256_7 25 20 = true := by
  decide +kernel

private theorem checked_7 :
    stepOK 24 stage256_7 stage256_8 3 5 = true := by
  decide +kernel

private theorem checked_8 :
    stepOK 23 stage256_8 stage256_9 3 3 = true := by
  decide +kernel

private theorem checked_9 :
    stepOK 22 stage256_9 stage256_10 3 4 = true := by
  decide +kernel

private theorem checked_10 :
    stepOK 21 stage256_10 stage256_11 9 14 = true := by
  decide +kernel

private theorem checked_11 :
    stepOK 20 stage256_11 stage256_12 9 19 = true := by
  decide +kernel

private theorem checked_12 :
    stepOK 19 stage256_12 stage256_13 11 10 = true := by
  decide +kernel

private theorem checked_13 :
    stepOK 18 stage256_13 stage256_14 9 10 = true := by
  decide +kernel

private theorem checked_14 :
    stepOK 17 stage256_14 stage256_15 6 8 = true := by
  decide +kernel

private theorem checked_15 :
    stepOK 16 stage256_15 stage256_16 12 6 = true := by
  decide +kernel

private theorem checked_16 :
    stepOK 15 stage256_16 stage256_17 9 13 = true := by
  decide +kernel

private theorem checked_17 :
    stepOK 14 stage256_17 stage256_18 12 7 = true := by
  decide +kernel

private theorem checked_18 :
    stepOK 13 stage256_18 stage256_19 12 10 = true := by
  decide +kernel

private theorem checked_19 :
    stepOK 12 stage256_19 stage256_20 4 8 = true := by
  decide +kernel

private theorem checked_20 :
    stepOK 11 stage256_20 stage256_21 9 4 = true := by
  decide +kernel

private theorem checked_21 :
    stepOK 10 stage256_21 stage256_22 5 10 = true := by
  decide +kernel

private def steps : List Step := [
  (3, 1, stage256_1), (10, 8, stage256_2), (13, 15, stage256_3),
  (16, 26, stage256_4), (19, 18, stage256_5), (22, 11, stage256_6),
  (25, 20, stage256_7), (3, 5, stage256_8), (3, 3, stage256_9),
  (3, 4, stage256_10), (9, 14, stage256_11), (9, 19, stage256_12),
  (11, 10, stage256_13), (9, 10, stage256_14), (6, 8, stage256_15),
  (12, 6, stage256_16), (9, 13, stage256_17), (12, 7, stage256_18),
  (12, 10, stage256_19), (4, 8, stage256_20), (9, 4, stage256_21),
  (5, 10, stage256_22)
]

theorem phase256 :
    Trace 32 stage256_0.entries 10 stage256_22.entries 64 := by
  have checked : traceOK 32 stage256_0 steps = true := by
    simp only [steps, traceOK, Bool.true_and,
      checked_0, checked_1, checked_2, checked_3, checked_4, checked_5,
      checked_6, checked_7, checked_8, checked_9, checked_10, checked_11,
      checked_12, checked_13, checked_14, checked_15, checked_16, checked_17,
      checked_18, checked_19, checked_20, checked_21]
  have growth : peak stage256_0 steps = 64 := by decide +kernel
  simpa only [growth, Rat.cast_ofNat] using! trace_sound checked

end NLA.IE03.Certificate
