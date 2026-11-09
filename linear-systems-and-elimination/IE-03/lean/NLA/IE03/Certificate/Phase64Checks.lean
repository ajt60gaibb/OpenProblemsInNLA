import NLA.IE03.Certificate.Phase64
import NLA.IE03.Certificate.Sound

/-! Kernel checks for the generated active squares in this phase. -/

namespace NLA.IE03.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem checked_0 :
    stepOK 23 stage64_0 stage64_1 19 17 = true := by
  decide +kernel

private theorem checked_1 :
    stepOK 22 stage64_1 stage64_2 15 1 = true := by
  decide +kernel

private theorem checked_2 :
    stepOK 21 stage64_2 stage64_3 11 8 = true := by
  decide +kernel

private theorem checked_3 :
    stepOK 20 stage64_3 stage64_4 3 18 = true := by
  decide +kernel

private theorem checked_4 :
    stepOK 19 stage64_4 stage64_5 18 13 = true := by
  decide +kernel

private theorem checked_5 :
    stepOK 18 stage64_5 stage64_6 6 4 = true := by
  decide +kernel

private theorem checked_6 :
    stepOK 17 stage64_6 stage64_7 16 9 = true := by
  decide +kernel

private theorem checked_7 :
    stepOK 16 stage64_7 stage64_8 15 10 = true := by
  decide +kernel

private theorem checked_8 :
    stepOK 15 stage64_8 stage64_9 0 0 = true := by
  decide +kernel

private theorem checked_9 :
    stepOK 14 stage64_9 stage64_10 3 1 = true := by
  decide +kernel

private theorem checked_10 :
    stepOK 13 stage64_10 stage64_11 0 1 = true := by
  decide +kernel

private theorem checked_11 :
    stepOK 12 stage64_11 stage64_12 1 2 = true := by
  decide +kernel

private theorem checked_12 :
    stepOK 11 stage64_12 stage64_13 8 6 = true := by
  decide +kernel

private theorem checked_13 :
    stepOK 10 stage64_13 stage64_14 8 7 = true := by
  decide +kernel

private theorem checked_14 :
    stepOK 9 stage64_14 stage64_15 6 9 = true := by
  decide +kernel

private theorem checked_15 :
    stepOK 8 stage64_15 stage64_16 5 7 = true := by
  decide +kernel

private def steps : List Step := [
  (19, 17, stage64_1), (15, 1, stage64_2), (11, 8, stage64_3),
  (3, 18, stage64_4), (18, 13, stage64_5), (6, 4, stage64_6),
  (16, 9, stage64_7), (15, 10, stage64_8), (0, 0, stage64_9),
  (3, 1, stage64_10), (0, 1, stage64_11), (1, 2, stage64_12),
  (8, 6, stage64_13), (8, 7, stage64_14), (6, 9, stage64_15),
  (5, 7, stage64_16)
]

theorem phase64 :
    Trace 24 stage64_0.entries 8 stage64_16.entries 16 := by
  have checked : traceOK 24 stage64_0 steps = true := by
    simp only [steps, traceOK, Bool.true_and,
      checked_0, checked_1, checked_2, checked_3, checked_4, checked_5,
      checked_6, checked_7, checked_8, checked_9, checked_10, checked_11,
      checked_12, checked_13, checked_14, checked_15]
  have growth : peak stage64_0 steps = 16 := by decide +kernel
  simpa only [growth, Rat.cast_ofNat] using! trace_sound checked

end NLA.IE03.Certificate
