import NLA.Proofs.TR04.MachineFrameGather

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

set_option maxHeartbeats 2200000 in
theorem frameGatherProgram_eleven_steps (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (i k selected address : ℕ) (value : ℝ) (hi : i < P.rows) (hk : k < P.width) :
    (ordinaryStep frameGatherProgram)^[11] (frameGatherInnerState memory P i k selected address value) =
      frameGatherInnerState memory P i (k + 1) (P.column k) (P.sourceAddress (i * P.width + k))
        (memory (P.sourceAddress (i * P.width + k))) := by
  have hq : i * P.width + k < P.rows * P.width := by
    have hb := Nat.mul_le_mul (show i + 1 ≤ P.rows by omega) (show P.width ≤ P.width from le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at hb
    omega
  have hread := frameGatherMemory_read memory P hP hd (i * P.width + k) hq.le
    (i * P.width + k) hq
  have hmem := frameGatherMemory_succ memory P (i * P.width + k)
  have hflat := P.sourceAddress_flat i k hk
  rw [hflat] at hread hmem
  simp only [Nat.add_assoc] at hread hmem hflat
  by_cases hp : k < P.above
  · have hc := P.counter_prefix hP k hp.le
    have hcn := P.counter_prefix hP (k + 1) (by omega)
    have hcol : P.column k = k := if_pos hp
    simp only [hcol] at hread hmem hflat
    apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      frameGatherProgram, frameGatherInnerState, hk, hp, hc, hcn, hcol, hflat, hread, hmem,
      Nat.add_assoc]
    all_goals try rfl
    · funext r
      fin_cases r
      simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe, -Fin.val_eq_zero_iff]
    · funext r
      fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
        -Fin.val_eq_zero_iff, Fin.ext_iff]
  · have hcn := P.counter_succ hP k (by omega)
    have hcol : P.column k = P.above + P.counter k := if_neg hp
    simp only [hcol] at hread hmem hflat
    by_cases he : P.counter k + 1 = P.tied
    all_goals apply machineState_ext
    all_goals simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff, Function.iterate_succ_apply', ordinaryStep,
      frameGatherProgram, frameGatherInnerState, hk, hp, hcn, he, hcol, hflat, hread, hmem,
      Nat.add_assoc]
    all_goals try rfl
    all_goals funext r
    all_goals fin_cases r <;> simp (config := { decide := false }) [-Fin.reduceEq, -Fin.reduceNe,
      -Fin.val_eq_zero_iff, Fin.ext_iff]

#assert_trust kernel frameGatherProgram_eleven_steps
#print axioms frameGatherProgram_eleven_steps
end NLA.Proofs.TR04
