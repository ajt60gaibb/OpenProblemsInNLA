import NLA.Proofs.TR04.MachineFrameGatherTrace
import NLA.Proofs.TR04.SVDExplicitTie

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine

def frameGatherMatrix (P : FrameGatherParameters) (hP : P.Valid)
    (U : Matrix (Fin P.rows) (Fin P.rows) ℝ) : Matrix (Fin P.rows) (Fin P.width) ℝ :=
  fun i k => U i ⟨P.column k.val, P.column_lt hP k.val k.isLt⟩

theorem frameGatherMemory_matrix (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (U : Matrix (Fin P.rows) (Fin P.rows) ℝ)
    (hU : ∀ i j, memory (P.inputBase + i.val * P.rows + j.val) = U i j)
    (i : Fin P.rows) (k : Fin P.width) :
    frameGatherMemory memory P (P.rows * P.width) (P.outputBase + i.val * P.width + k.val) =
      frameGatherMatrix P hP U i k := by
  have hq : i.val * P.width + k.val < P.rows * P.width := by
    have hb := Nat.mul_le_mul (show i.val + 1 ≤ P.rows by omega) (show P.width ≤ P.width from le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at hb
    omega
  rw [Nat.add_assoc, frameGatherMemory_output memory P _ hq,
    P.sourceAddress_flat i.val k.val k.isLt]
  exact hU i ⟨P.column k.val, P.column_lt hP _ k.isLt⟩

theorem RoutineEmbedding.frameGather_run_matrix {Q : Program} (E : RoutineEmbedding frameGatherProgram Q)
    (memory : ℕ → ℝ) (P : FrameGatherParameters) (hP : P.Valid)
    (hd : DisjointBlocks P.inputBase (P.rows * P.rows) P.outputBase (P.rows * P.width))
    (U : Matrix (Fin P.rows) (Fin P.rows) ℝ)
    (hU : ∀ i j, memory (P.inputBase + i.val * P.rows + j.val) = U i j)
    (aux : Fin 5 → ℕ) (rowScratch widthScratch writeScratch : ℕ) (value : ℝ)
    {start : State Q} {trace : Trace Q} (offset : ℕ)
    (hs : E.Relates (frameGatherStart memory P aux rowScratch widthScratch writeScratch value)
      (trace.state offset)) (ht : LegalTrace Q start trace) :
    ∀ i : Fin P.rows, ∀ k : Fin P.width,
      (trace.state (offset + (P.rows * (11 * P.width + 7) + 4))).memory
          (P.outputBase + i.val * P.width + k.val) = frameGatherMatrix P hP U i k := by
  obtain ⟨aux', v, hr, _⟩ := E.frameGather_run_at memory P hP hd aux
    rowScratch widthScratch writeScratch value offset hs ht
  intro i k
  rw [hr.memory]
  exact frameGatherMemory_matrix memory P hP U hU i k

def tieGatherParameters {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ) : FrameGatherParameters where
  rows := m
  above := T.above
  tied := T.tied
  take := T.take
  start := j.val
  inputBase := inputBase
  outputBase := outputBase

theorem tieGatherParameters_valid {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ) :
    (tieGatherParameters T j inputBase outputBase).Valid := by
  have hf : T.above + T.tied ≤ m := T.fits.trans (Nat.min_le_left m l)
  exact ⟨T.tied_pos, j.isLt, T.take_le, by dsimp [tieGatherParameters]; omega, fun _ => hf⟩

theorem tieGatherParameters_width {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ) :
    (tieGatherParameters T j inputBase outputBase).width = a.val + 1 := T.rank_eq

theorem frameGatherMatrix_tie {m l : ℕ} {sigma : Fin (min m l) → ℝ} {a : Fin (min m l)}
    (T : SVD.TieStructure sigma a) (j : Fin T.tied) (inputBase outputBase : ℕ)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    (frameGatherMatrix (tieGatherParameters T j inputBase outputBase)
      (tieGatherParameters_valid T j inputBase outputBase) U).submatrix id (Fin.cast T.rank_eq.symm) =
        T.explicitFrame U j := by
  ext i k
  change U i ⟨_, _⟩ = U i (Fin.castLE (Nat.min_le_left m l) (T.explicitIndex j k))
  congr 1
  apply Fin.ext
  exact (T.explicitIndex_val j k).symm

def prefixGatherParameters (m width inputBase outputBase : ℕ) : FrameGatherParameters where
  rows := m
  above := width
  tied := 1
  take := 0
  start := 0
  inputBase := inputBase
  outputBase := outputBase

theorem prefixGatherParameters_valid (m width inputBase outputBase : ℕ) (hw : width ≤ m) :
    (prefixGatherParameters m width inputBase outputBase).Valid := by
  refine ⟨by change 0 < 1; decide, by change 0 < 1; decide,
    by change 0 ≤ 1; decide, hw, ?_⟩
  intro h
  change 0 < 0 at h
  omega

theorem frameGatherMatrix_prefix (m width inputBase outputBase : ℕ) (hw : width ≤ m)
    (U : Matrix (Fin m) (Fin m) ℝ) :
    frameGatherMatrix (prefixGatherParameters m width inputBase outputBase)
      (prefixGatherParameters_valid m width inputBase outputBase hw) U = U.submatrix id (Fin.castLE hw) := by
  ext i k
  change U i ⟨_, _⟩ = U i (Fin.castLE hw k)
  congr 1
  apply Fin.ext
  exact if_pos k.isLt

#assert_trust kernel frameGatherMemory_matrix
#assert_trust kernel RoutineEmbedding.frameGather_run_matrix
#assert_trust kernel tieGatherParameters_valid
#assert_trust kernel tieGatherParameters_width
#assert_trust kernel frameGatherMatrix_tie
#assert_trust kernel prefixGatherParameters_valid
#assert_trust kernel frameGatherMatrix_prefix
#print axioms frameGatherMatrix_tie
end NLA.Proofs.TR04
