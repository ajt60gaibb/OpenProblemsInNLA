import NLA.Proofs.TR04.MachineTTFirstOriginal
import NLA.Proofs.TR04.TTCompletion

/-! Every recorded witness is tied to the output actually stored in its own
candidate slot. Choice below only collects those witnessed trace outputs. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout
open TensorFormat TensorFormat.TTStrict

def TTCompletedCandidates (S : Shape) (r : Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n rank : ℕ} {ns : List ℕ} (hshape : modeList S.mode=m::n::ns)
    (F : FirstFrames m rank) (s : State ttProgram) (done : ℕ) : Prop :=
  ∀ j : Fin F.count,j.val<done →
    ∃ Z : TensorFormat.Tensor ((F.width*n)::ns),
      Completion ((F.width*n)::ns) (fun i => originalRanks S r (i+1))
        (merge F.width n ns (contract (F.frame j) (Original.input hshape A))) Z ∧
      ∀ x,s.memory (s.natural 71+j.val*DenseSize S+Offset S x)=
        Original.output hshape (completionOutput (F.frame j) Z) x

theorem ttCompletedCandidates_zero (S : Shape) (r : Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n rank : ℕ} {ns : List ℕ} (hshape : modeList S.mode=m::n::ns)
    (F : FirstFrames m rank) (s : State ttProgram) : TTCompletedCandidates S r A hshape F s 0 := by
  intro j hj
  omega

theorem TTCompletedCandidates.memory_eq {S : Shape} {r : Ranks S}
    {A : NLA.Computation.TensorTrainApproximation.Tensor S}
    {m n rank : ℕ} {ns : List ℕ} {hshape : modeList S.mode=m::n::ns}
    {F : FirstFrames m rank} {s t : State ttProgram} {done : ℕ}
    (h : TTCompletedCandidates S r A hshape F s done)
    (hn : t.natural 71=s.natural 71)
    (hm : ∀ a,s.natural 71≤a → t.memory a=s.memory a) :
    TTCompletedCandidates S r A hshape F t done := by
  intro j hj
  obtain ⟨Z,hZ,hstored⟩ := h j hj
  refine ⟨Z,hZ,?_⟩
  intro x
  rw [hn,hm _ (by omega)]
  exact hstored x

theorem TTCompletedCandidates.extend {S : Shape} {r : Ranks S}
    {A : NLA.Computation.TensorTrainApproximation.Tensor S}
    {m n rank : ℕ} {ns : List ℕ} {hshape : modeList S.mode=m::n::ns}
    {F : FirstFrames m rank} {s t : State ttProgram} (j : Fin F.count)
    (h : TTCompletedCandidates S r A hshape F s j.val)
    (hn : t.natural 71=s.natural 71)
    (hm : ∀ i<j.val,∀ x,
      t.memory (s.natural 71+i*DenseSize S+Offset S x)=
        s.memory (s.natural 71+i*DenseSize S+Offset S x))
    (Z : TensorFormat.Tensor ((F.width*n)::ns))
    (hZ : Completion ((F.width*n)::ns) (fun i => originalRanks S r (i+1))
      (merge F.width n ns (contract (F.frame j) (Original.input hshape A))) Z)
    (hstored : ∀ x,t.memory (s.natural 71+j.val*DenseSize S+Offset S x)=
      Original.output hshape (completionOutput (F.frame j) Z) x) :
    TTCompletedCandidates S r A hshape F t (j.val+1) := by
  intro i hi
  have hil : i.val≤j.val := by omega
  rcases lt_or_eq_of_le hil with hij|hij
  · obtain ⟨W,hW,hwstored⟩ := h i hij
    refine ⟨W,hW,?_⟩
    intro x
    rw [hn,hm i.val hij x]
    exact hwstored x
  · have hij' : i=j := Fin.ext hij
    subst i
    refine ⟨Z,hZ,?_⟩
    intro x
    rw [hn]
    exact hstored x

theorem TTCompletedCandidates.collect {S : Shape} {r : Ranks S}
    {A : NLA.Computation.TensorTrainApproximation.Tensor S}
    {m n rank : ℕ} {ns : List ℕ} {hshape : modeList S.mode=m::n::ns}
    {F : FirstFrames m rank} {s : State ttProgram}
    (h : TTCompletedCandidates S r A hshape F s F.count) :
    ∃ Z : Fin F.count → TensorFormat.Tensor ((F.width*n)::ns),
      (∀ j,Completion ((F.width*n)::ns) (fun i => originalRanks S r (i+1))
        (merge F.width n ns (contract (F.frame j) (Original.input hshape A))) (Z j)) ∧
      ∀ j : Fin F.count,∀ x,s.memory (s.natural 71+j.val*DenseSize S+Offset S x)=
        Original.output hshape (completionOutput (F.frame j) (Z j)) x := by
  classical
  let Z := fun j : Fin F.count => Classical.choose (h j j.isLt)
  refine ⟨Z,fun j => (Classical.choose_spec (h j j.isLt)).1,?_⟩
  intro j
  exact (Classical.choose_spec (h j j.isLt)).2

#assert_trust kernel TTCompletedCandidates
#assert_trust kernel ttCompletedCandidates_zero
#assert_trust kernel TTCompletedCandidates.memory_eq
#assert_trust kernel TTCompletedCandidates.extend
#assert_trust kernel TTCompletedCandidates.collect
#print axioms TTCompletedCandidates.collect
end NLA.Proofs.TR04
