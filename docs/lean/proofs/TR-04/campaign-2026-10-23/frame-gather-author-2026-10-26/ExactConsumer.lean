import NLA.Proofs.TR04.MachineFrameGatherSVD
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open NLA.Proofs.TR04 NLA.Computation.SVDMachine
namespace FrameGatherExactConsumer

theorem literal_caller {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    let n := offset + (P.rows * (11 * P.width + 7) + 4)
    (trace.state n).label = E.labels 25 ∧ (trace.state n).status = .running ∧
      (∀ i < P.rows, ∀ k < P.width,
        (trace.state n).memory (P.outputBase + i * P.width + k) =
          memory (P.inputBase + i * P.rows + (if k < P.above then k else P.above + ((P.start + (k - P.above)) % P.tied)))) ∧
      (∀ a, ¬ (P.outputBase ≤ a ∧ a < P.outputBase + P.rows * P.width) →
        (trace.state n).memory a = memory a) ∧
      CostThrough Q trace n ≤ CostThrough Q trace offset + (P.rows * (11 * P.width + 7) + 4) := by
  simpa only [FrameGatherParameters.column, FrameGatherParameters.counter] using
    E.frameGather_run_cells memory P hP hd aux rowScratch widthScratch writeScratch value offset hs ht
#assert_trust kernel literal_caller

theorem literal_tie {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    (frameGatherMatrix (tieGatherParameters T j inputBase outputBase)
      (tieGatherParameters_valid T j inputBase outputBase) U).submatrix id (Fin.cast T.rank_eq.symm) =
        T.explicitFrame U j :=
  frameGatherMatrix_tie T j inputBase outputBase U
#assert_trust kernel literal_tie

theorem literal_prefix (m width inputBase outputBase : ℕ) (hw : width ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    frameGatherMatrix (prefixGatherParameters m width inputBase outputBase)
      (prefixGatherParameters_valid m width inputBase outputBase hw) U = U.submatrix id (Fin.castLE hw) :=
  frameGatherMatrix_prefix m width inputBase outputBase hw U
#assert_trust kernel literal_prefix

end FrameGatherExactConsumer
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters
#print axioms NLA.Proofs.TR04.FrameGatherParameters
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.width
#print axioms NLA.Proofs.TR04.FrameGatherParameters.width
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.Valid
#print axioms NLA.Proofs.TR04.FrameGatherParameters.Valid
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.column
#print axioms NLA.Proofs.TR04.FrameGatherParameters.column
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.sourceAddress
#print axioms NLA.Proofs.TR04.FrameGatherParameters.sourceAddress
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le
#print axioms NLA.Proofs.TR04.FrameGatherParameters.Valid.width_le
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter_prefix
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter_prefix
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter_lt
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter_lt
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.counter_succ
#print axioms NLA.Proofs.TR04.FrameGatherParameters.counter_succ
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.column_lt
#print axioms NLA.Proofs.TR04.FrameGatherParameters.column_lt
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat
#print axioms NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_flat
#assert_trust kernel NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_mem
#print axioms NLA.Proofs.TR04.FrameGatherParameters.sourceAddress_mem
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory
#print axioms NLA.Proofs.TR04.frameGatherMemory
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_zero
#print axioms NLA.Proofs.TR04.frameGatherMemory_zero
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_outside
#print axioms NLA.Proofs.TR04.frameGatherMemory_outside
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_succ
#print axioms NLA.Proofs.TR04.frameGatherMemory_succ
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_input
#print axioms NLA.Proofs.TR04.frameGatherMemory_input
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_read
#print axioms NLA.Proofs.TR04.frameGatherMemory_read
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_output
#print axioms NLA.Proofs.TR04.frameGatherMemory_output
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram
#print axioms NLA.Proofs.TR04.frameGatherProgram
#assert_trust kernel NLA.Proofs.TR04.frameGatherOuterState
#print axioms NLA.Proofs.TR04.frameGatherOuterState
#assert_trust kernel NLA.Proofs.TR04.frameGatherStart
#print axioms NLA.Proofs.TR04.frameGatherStart
#assert_trust kernel NLA.Proofs.TR04.frameGatherInnerState
#print axioms NLA.Proofs.TR04.frameGatherInnerState
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_scalar
#print axioms NLA.Proofs.TR04.frameGatherProgram_scalar
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_initialize
#print axioms NLA.Proofs.TR04.frameGatherProgram_initialize
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_row_setup
#print axioms NLA.Proofs.TR04.frameGatherProgram_row_setup
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_eleven_steps
#print axioms NLA.Proofs.TR04.frameGatherProgram_eleven_steps
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_inner_iterations
#print axioms NLA.Proofs.TR04.frameGatherProgram_inner_iterations
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_row_exit
#print axioms NLA.Proofs.TR04.frameGatherProgram_row_exit
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_one_row
#print axioms NLA.Proofs.TR04.frameGatherProgram_one_row
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_rows
#print axioms NLA.Proofs.TR04.frameGatherProgram_rows
#assert_trust kernel NLA.Proofs.TR04.frameGatherReturnState
#print axioms NLA.Proofs.TR04.frameGatherReturnState
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_return
#print axioms NLA.Proofs.TR04.frameGatherProgram_return
#assert_trust kernel NLA.Proofs.TR04.frameGatherProgram_trace_result
#print axioms NLA.Proofs.TR04.frameGatherProgram_trace_result
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_at
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_at
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_cells
#assert_trust kernel NLA.Proofs.TR04.frameGatherMatrix
#print axioms NLA.Proofs.TR04.frameGatherMatrix
#assert_trust kernel NLA.Proofs.TR04.frameGatherMemory_matrix
#print axioms NLA.Proofs.TR04.frameGatherMemory_matrix
#assert_trust kernel NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix
#print axioms NLA.Proofs.TR04.RoutineEmbedding.frameGather_run_matrix
#assert_trust kernel NLA.Proofs.TR04.tieGatherParameters
#print axioms NLA.Proofs.TR04.tieGatherParameters
#assert_trust kernel NLA.Proofs.TR04.tieGatherParameters_valid
#print axioms NLA.Proofs.TR04.tieGatherParameters_valid
#assert_trust kernel NLA.Proofs.TR04.tieGatherParameters_width
#print axioms NLA.Proofs.TR04.tieGatherParameters_width
#assert_trust kernel NLA.Proofs.TR04.frameGatherMatrix_tie
#print axioms NLA.Proofs.TR04.frameGatherMatrix_tie
#assert_trust kernel NLA.Proofs.TR04.prefixGatherParameters
#print axioms NLA.Proofs.TR04.prefixGatherParameters
#assert_trust kernel NLA.Proofs.TR04.prefixGatherParameters_valid
#print axioms NLA.Proofs.TR04.prefixGatherParameters_valid
#assert_trust kernel NLA.Proofs.TR04.frameGatherMatrix_prefix
#print axioms NLA.Proofs.TR04.frameGatherMatrix_prefix
