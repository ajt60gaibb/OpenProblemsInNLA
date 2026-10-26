import NLA.Proofs.TR04.MachineTTFirstStage
import NLA.Proofs.TR04.TTStrictOriginalView

/-! The immutable original shape and ranks identify the first stored tensor,
its reachable format, and the exact capped rank used by the fixed family. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat TensorFormat.TTStrict

theorem TTInitialSVDData.two_format {S : Shape} {r : Ranks S} {A : NLA.Computation.TensorTrainApproximation.Tensor S}
    {s0 : State ttProgram} (hi : TTInitialSVDData S r A s0) :
    ∃ n : ℕ,∃ ns : List ℕ,modeList S.mode=s0.natural 81::n::ns ∧
      suffixSize (n::ns)=s0.natural 82 ∧ 1≤ns.length := by
  obtain ⟨rest,he,hcols,hlen⟩ := ttInitial_first_format S
  cases rest with
  | nil =>
    have := S.order_ge
    simp only [List.length_nil] at hlen
    omega
  | cons n ns =>
    refine ⟨n,ns,?_,hcols.trans hi.cols.symm,?_⟩
    · rwa [hi.rows]
    · have := S.order_ge
      simp only [List.length_cons] at hlen
      omega

theorem ttStoresTensor_formatCast {ns ms : List ℕ} (he : ns=ms)
    {memory : ℕ → ℝ} {base : ℕ} {A : TensorFormat.Tensor ns}
    (h : StoresTensor memory base ns A) :
    StoresTensor memory base ms (Original.formatCast he A) := by
  cases he
  exact h

theorem TTInitialSVDData.read_original {S : Shape} {r : Ranks S}
    {A : NLA.Computation.TensorTrainApproximation.Tensor S} {s0 : State ttProgram}
    (hi : TTInitialSVDData S r A s0) {ns : List ℕ}
    (he : modeList S.mode=s0.natural 81::ns) :
    readMatrix s0.memory (s0.natural 81) (suffixSize ns) (s0.natural 92)=
      radixDenseFirst (Original.input he A) :=
  (storesTensor_readMatrix_iff _ _ _).mp (ttStoresTensor_formatCast he hi.storedOriginal)

theorem TTInitialSVDData.first_rank {S : Shape} {r : Ranks S}
    {A : NLA.Computation.TensorTrainApproximation.Tensor S} {s0 : State ttProgram}
    (hi : TTInitialSVDData S r A s0) : s0.natural 80=originalRanks S r 0 :=
  hi.rank.trans (ttFirstRankValue_originalRanks S r)

theorem TTFirstContext.original_width {S : Shape} {r : Ranks S}
    {A : NLA.Computation.TensorTrainApproximation.Tensor S} {s0 s : State ttProgram}
    (hi : TTInitialSVDData S r A s0) {R : TTFirstReply s0} {hr : 1≤s0.natural 80}
    (_h : TTFirstContext R hr (ofShape S) s) {ns : List ℕ}
    (hcols : suffixSize ns=s0.natural 82) :
    R.family.width=stepRank (s0.natural 81) ns (originalRanks S r) := by
  obtain ⟨_,hw,_⟩ := ttFirstChoice_realizes_explicit R.valid (s0.natural 80) hr 0 0
  have hc := ttFirstChoice_width R.sigma R.valid.2.2.2.1 (s0.natural 80) hr
  change (ttFirstChoice R.sigma R.valid.2.2.2.1 (s0.natural 80)
    (min (s0.natural 80) (min (s0.natural 81) (s0.natural 82))) hr).above+
    (ttFirstChoice R.sigma R.valid.2.2.2.1 (s0.natural 80)
    (min (s0.natural 80) (min (s0.natural 81) (s0.natural 82))) hr).take=R.family.width at hw
  rw [←hw,hc]
  unfold stepRank cappedRank
  rw [hcols,hi.first_rank]

#assert_trust kernel TTInitialSVDData.two_format
#assert_trust kernel ttStoresTensor_formatCast
#assert_trust kernel TTInitialSVDData.read_original
#assert_trust kernel TTInitialSVDData.first_rank
#assert_trust kernel TTFirstContext.original_width
#print axioms TTFirstContext.original_width
end NLA.Proofs.TR04
