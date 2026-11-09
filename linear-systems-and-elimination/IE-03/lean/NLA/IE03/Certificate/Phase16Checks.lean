import NLA.IE03.Certificate.Phase16
import NLA.IE03.Certificate.Sound

/-! Kernel checks for the generated active squares in this phase. -/

namespace NLA.IE03.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

private theorem checked_0 :
    stepOK 15 stage16_0 stage16_1 14 8 = true := by
  decide +kernel

private theorem checked_1 :
    stepOK 14 stage16_1 stage16_2 12 6 = true := by
  decide +kernel

private theorem checked_2 :
    stepOK 13 stage16_2 stage16_3 10 4 = true := by
  decide +kernel

private theorem checked_3 :
    stepOK 12 stage16_3 stage16_4 9 2 = true := by
  decide +kernel

private theorem checked_4 :
    stepOK 11 stage16_4 stage16_5 7 4 = true := by
  decide +kernel

private theorem checked_5 :
    stepOK 10 stage16_5 stage16_6 6 10 = true := by
  decide +kernel

private theorem checked_6 :
    stepOK 9 stage16_6 stage16_7 8 6 = true := by
  decide +kernel

private theorem checked_7 :
    stepOK 8 stage16_7 stage16_8 7 4 = true := by
  decide +kernel

private theorem checked_8 :
    stepOK 7 stage16_8 stage16_9 5 1 = true := by
  decide +kernel

private theorem checked_9 :
    stepOK 6 stage16_9 stage16_10 3 1 = true := by
  decide +kernel

private def steps : List Step := [
  (14, 8, stage16_1), (12, 6, stage16_2), (10, 4, stage16_3),
  (9, 2, stage16_4), (7, 4, stage16_5), (6, 10, stage16_6),
  (8, 6, stage16_7), (7, 4, stage16_8), (5, 1, stage16_9),
  (3, 1, stage16_10)
]

theorem phase16 :
    Trace 16 stage16_0.entries 6 stage16_10.entries 4 := by
  have checked : traceOK 16 stage16_0 steps = true := by
    simp only [steps, traceOK, Bool.true_and,
      checked_0, checked_1, checked_2, checked_3, checked_4, checked_5,
      checked_6, checked_7, checked_8, checked_9]
  have growth : peak stage16_0 steps = 4 := by decide +kernel
  simpa only [growth, Rat.cast_ofNat] using! trace_sound checked

end NLA.IE03.Certificate
