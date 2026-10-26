import NLA.Proofs.TR04.MachineTTCandidateGatherRun
import NLA.Proofs.TR04.MachineTensorMemory

/-! Actual dense selected-frame storage and read protection for every saved
input, U, sigma, or V block disjoint from the literal frame destination. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TensorFormat

theorem ttCandidateGather_frame_memory (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (U : Matrix (Fin P.rows) (Fin P.rows) ℝ) (hU : StoresFrame memory P.inputBase P.rows U) :
    StoresFrame (frameGatherMemory memory P (P.rows * P.width)) P.outputBase P.width (frameGatherMatrix P hP U) :=
  frameGatherMemory_matrix memory P hP U hU

theorem ttCandidateGather_saved_block (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (base count : ℕ) (hd : DisjointBlocks base count P.outputBase (P.rows * P.width)) :
    ∀ a, base ≤ a ∧ a < base + count → frameGatherMemory memory P (P.rows * P.width) a = memory a := by
  intro a ha
  exact frameGatherMemory_outside memory P _ a (disjointBlocks_not_mem_right hd ha)

theorem ttCandidateGather_saved_matrix (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (base rows cols : ℕ) (hd : DisjointBlocks base (rows * cols) P.outputBase (P.rows * P.width)) :
    readMatrix (frameGatherMemory memory P (P.rows * P.width)) rows cols base = readMatrix memory rows cols base := by
  ext i j
  exact ttCandidateGather_saved_block memory P base (rows * cols) hd _
    (by have hh := matrix_offset_lt i j; omega)

theorem ttCandidateGather_saved_tensor (memory : ℕ → ℝ) (P : FrameGatherParameters)
    (base : ℕ) (ns : List ℕ) (A : Tensor ns) (hA : StoresTensor memory base ns A)
    (hd : DisjointBlocks base ns.prod P.outputBase (P.rows * P.width)) :
    StoresTensor (frameGatherMemory memory P (P.rows * P.width)) base ns A :=
  hA.memory_eq (ttCandidateGather_saved_block memory P base ns.prod hd)

/-- Native dense output at the fixed metadata boundary, with every outside
memory cell preserved. Input U is read from the caller's actual stored array. -/
theorem ttCandidateGather_stored {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (s : State ttProgram)
    (he : trace.state offset = s) (hl : s.label = 189) (hs : s.status = .running)
    (hj : s.natural 76 < s.natural 75) (hP : (ttCandidateGatherParameters s).Valid)
    (hd : DisjointBlocks (s.natural 72) (s.natural 81 * s.natural 81)
      (s.natural 67) (s.natural 81 * (ttCandidateGatherParameters s).width))
    (U : Matrix (Fin (s.natural 81)) (Fin (s.natural 81)) ℝ)
    (hU : StoresFrame s.memory (s.natural 72) (s.natural 81) U) :
    let P := ttCandidateGatherParameters s
    let n := offset + (P.rows * (11 * P.width + 7) + 24)
    StoresFrame (trace.state n).memory P.outputBase P.width (frameGatherMatrix P hP U) ∧
      (∀ a, ¬(P.outputBase ≤ a ∧ a < P.outputBase + P.rows * P.width) →
        (trace.state n).memory a = s.memory a) := by
  obtain ⟨_, _, hm, _, _, _, _⟩ := ttCandidateGather_run ht offset s he hl hs hj hP hd
  dsimp only [ttCandidateGatherParameters] at hm hP hd ⊢
  rw [hm]
  exact ⟨ttCandidateGather_frame_memory s.memory _ hP U hU,
    fun a ha => frameGatherMemory_outside s.memory _ _ a ha⟩

#assert_trust kernel ttCandidateGather_frame_memory
#assert_trust kernel ttCandidateGather_saved_block
#assert_trust kernel ttCandidateGather_saved_matrix
#assert_trust kernel ttCandidateGather_saved_tensor
#assert_trust kernel ttCandidateGather_stored
#print axioms ttCandidateGather_stored
end NLA.Proofs.TR04
