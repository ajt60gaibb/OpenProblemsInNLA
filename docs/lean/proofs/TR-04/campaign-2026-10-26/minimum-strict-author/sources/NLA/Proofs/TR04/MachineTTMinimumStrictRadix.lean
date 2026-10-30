import NLA.Proofs.TR04.MachineTTMinimumStrict

/-! The same original selector/strictness endpoint for the actual explicit
mixed-radix first SVD. Only V's rows are permuted; the fixed explicit first
family depends on the unchanged U and sigma and precedes every supplied Z. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open TensorFormat TensorFormat.TTStrict

/-- The explicit data family depends only on U, sigma and r. Matrix/right-basis
proof transport does not alter even its actual selected columns. -/
theorem ttExplicitFamily_same_u_sigma {m l : ℕ}
    {B B' : Matrix (Fin m) (Fin l) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {sigma : Fin (min m l) → ℝ} {V V' : Matrix (Fin l) (Fin l) ℝ}
    (h : ValidSVD B U sigma V) (h' : ValidSVD B' U sigma V') (r : ℕ) :
    explicitFirstFrames h r=explicitFirstFrames h' r := by
  unfold explicitFirstFrames
  split_ifs <;> rfl

theorem ttBest_explicit_radix_strict_at (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n : ℕ} {ns : List ℕ} (hshape : modeList S.mode=m::n::ns)
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n::ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n::ns))) (Fin (suffixSize (n::ns))) ℝ}
    (h : ValidSVD (radixDenseFirst (Original.input hshape A)) U sigma V) :
    let F := explicitFirstFrames h (originalRanks S r 0)
    ∀ Z : Fin F.count → TensorFormat.Tensor ((F.width*n)::ns),
      (∀ j,Completion ((F.width*n)::ns) (fun i => originalRanks S r (i+1))
        (merge F.width n ns (contract (F.frame j) (Original.input hshape A))) (Z j)) →
      ∀ {start : State ttProgram} {trace : Trace ttProgram},
      LegalTrace ttProgram start trace → ∀ offset : ℕ,
      (trace.state offset).label=189 → (trace.state offset).status=.running →
      (trace.state offset).natural 127=0 →
      (trace.state offset).natural 75=F.count →
      (trace.state offset).natural 75≤(trace.state offset).natural 76 →
      (trace.state offset).natural 64=DenseSize S →
      (∀ x,(trace.state offset).memory ((trace.state offset).natural 92+Offset S x)=A x) →
      (∀ j : Fin F.count,∀ x,(trace.state offset).memory
        ((trace.state offset).natural 71+j.val*DenseSize S+Offset S x)=
          Original.output hshape (completionOutput (F.frame j) (Z j)) x) →
      let s := trace.state offset
      let time := offset+(bestCandidateReturnTime (ttBestData s)+17)
      ∃ winner : Fin F.count,
        let X := Original.output hshape (completionOutput (F.frame winner) (Z winner))
        Returns ttProgram S (trace.state time) X ∧
        (trace.state time).status=.halted (s.natural 71+winner.val*DenseSize S) ∧
        (trace.state time).natural 83=s.natural 71+winner.val*DenseSize S ∧
        (trace.state time).natural 54=winner.val ∧
        (trace.state time).real 12=FrobeniusSq S A X ∧
        (∀ j : Fin F.count,FrobeniusSq S A X≤
          FrobeniusSq S A (Original.output hshape (completionOutput (F.frame j) (Z j)))) ∧
        Feasible S r X ∧
        (0<Optimum S r A → FrobeniusSq S A X<((S.order : ℝ)-1)*Optimum S r A) ∧
        (Optimum S r A=0 → X=A) ∧
        (trace.state time).memory=s.memory ∧
        CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+300*(Size S r+1)^2 := by
  have hd := radix_validSVD_to_denseFirst h
  have heq : explicitFirstFrames hd (originalRanks S r 0)=
      explicitFirstFrames h (originalRanks S r 0) := ttExplicitFamily_same_u_sigma hd h _
  let P (F : FirstFrames m (originalRanks S r 0)) : Prop :=
    ∀ Z : Fin F.count → TensorFormat.Tensor ((F.width*n)::ns),
      (∀ j,Completion ((F.width*n)::ns) (fun i => originalRanks S r (i+1))
        (merge F.width n ns (contract (F.frame j) (Original.input hshape A))) (Z j)) →
      ∀ {start : State ttProgram} {trace : Trace ttProgram},
      LegalTrace ttProgram start trace → ∀ offset : ℕ,
      (trace.state offset).label=189 → (trace.state offset).status=.running →
      (trace.state offset).natural 127=0 →
      (trace.state offset).natural 75=F.count →
      (trace.state offset).natural 75≤(trace.state offset).natural 76 →
      (trace.state offset).natural 64=DenseSize S →
      (∀ x,(trace.state offset).memory ((trace.state offset).natural 92+Offset S x)=A x) →
      (∀ j : Fin F.count,∀ x,(trace.state offset).memory
        ((trace.state offset).natural 71+j.val*DenseSize S+Offset S x)=
          Original.output hshape (completionOutput (F.frame j) (Z j)) x) →
      let s := trace.state offset
      let time := offset+(bestCandidateReturnTime (ttBestData s)+17)
      ∃ winner : Fin F.count,
        let X := Original.output hshape (completionOutput (F.frame winner) (Z winner))
        Returns ttProgram S (trace.state time) X ∧
        (trace.state time).status=.halted (s.natural 71+winner.val*DenseSize S) ∧
        (trace.state time).natural 83=s.natural 71+winner.val*DenseSize S ∧
        (trace.state time).natural 54=winner.val ∧
        (trace.state time).real 12=FrobeniusSq S A X ∧
        (∀ j : Fin F.count,FrobeniusSq S A X≤
          FrobeniusSq S A (Original.output hshape (completionOutput (F.frame j) (Z j)))) ∧
        Feasible S r X ∧
        (0<Optimum S r A → FrobeniusSq S A X<((S.order : ℝ)-1)*Optimum S r A) ∧
        (Optimum S r A=0 → X=A) ∧
        (trace.state time).memory=s.memory ∧
        CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+300*(Size S r+1)^2
  change P (explicitFirstFrames h (originalRanks S r 0))
  have hmain : P (explicitFirstFrames hd (originalRanks S r 0)) :=
    ttBest_explicit_strict_at S r hr A hshape hd
  exact heq ▸ hmain

#assert_trust kernel ttExplicitFamily_same_u_sigma
#assert_trust kernel ttBest_explicit_radix_strict_at
#print axioms ttExplicitFamily_same_u_sigma
#print axioms ttBest_explicit_radix_strict_at
end NLA.Proofs.TR04
