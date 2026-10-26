import NLA.Proofs.TR04.MachineTTFinalOriginal
import NLA.Proofs.TR04.TTStrictExplicitOriginal
import NLA.Proofs.TR04.TensorCompressionRadixSVD

/-! Actual selector to the immutable original strict tensor boundary. The first
explicit frame family is fixed before the supplied actual child completions.
No completion witness is chosen from a mathematical existence theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation
open TensorFormat TensorFormat.TTStrict

/-- Total extension used only to adapt a finite actual family to the selector's
natural index interface. Outside-family values are never read by its proof. -/
def ttFiniteFamilyAt {α : Type*} {k : ℕ} (fallback : α) (C : Fin k → α) (i : ℕ) : α :=
  if hi : i<k then C ⟨i,hi⟩ else fallback

theorem ttFiniteFamilyAt_fin {α : Type*} {k : ℕ} (fallback : α) (C : Fin k → α) (i : Fin k) :
    ttFiniteFamilyAt fallback C i.val=C i := by
  simp only [ttFiniteFamilyAt,dif_pos i.isLt]

/-- A nontrivial dense array dominates the possible explicit family bound. -/
theorem tt_min_add_one_le_prod (m l : ℕ) (h : 2≤m*l) : min m l+1≤m*l := by
  by_cases hm : m=0
  · simp [hm] at h
  by_cases hm1 : m=1
  · subst m
    simp only [Nat.one_mul] at h ⊢
    have := Nat.min_le_left 1 l
    omega
  have hm2 : 2≤m := by omega
  have hl : 1≤l := by
    by_contra hh
    have hz : l=0 := by omega
    simp [hz] at h
  have hp := Nat.mul_le_mul_right l hm2
  have hmin := Nat.min_le_right m l
  omega

theorem tt_original_dense_two_le (S : Shape) : 2≤DenseSize S := by
  let i : Fin S.order := ⟨0,by have := S.order_ge;omega⟩
  exact (S.mode_ge i).trans (shape_mode_le_denseSize S i)

theorem tt_first_format_product (S : Shape) {m n : ℕ} {ns : List ℕ}
    (hl : modeList S.mode=m::n::ns) : m*suffixSize (n::ns)=DenseSize S := by
  calc
    m*suffixSize (n::ns)=(m::n::ns).prod := by rw [show suffixSize (n::ns)=(n::ns).prod from card_index (n::ns)];rfl
    _=DenseSize S := by rw [←hl,prod_modeList];rfl

/-- Actual-array count capacity follows from the first family and the original
shape product; it is independent of every subsequent child response. -/
theorem tt_explicit_count_le_dense (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n : ℕ} {ns : List ℕ} (hl : modeList S.mode=m::n::ns)
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n::ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n::ns))) (Fin (suffixSize (n::ns))) ℝ}
    (h : ValidSVD (denseFirst (Original.input hl A)) U sigma V) :
    (explicitFirstFrames h (originalRanks S r 0)).count≤DenseSize S := by
  have hc := (Original.first_svd_explicit_strict_family S r hr A hl h).1
  have hp := tt_first_format_product S hl
  have hn := tt_original_dense_two_le S
  have hb : min m (suffixSize (n::ns))+1≤m*suffixSize (n::ns) :=
    tt_min_add_one_le_prod _ _ (by rwa [hp])
  exact hc.trans (hb.trans_eq hp)

/-- Fixed first response, then every supplied actual Completion family and
stored output family, then the actual minimum. No mathematical existence of
completions is used to supply the premise hZ. -/
theorem ttBest_explicit_strict_at (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S)
    {m n : ℕ} {ns : List ℕ} (hshape : modeList S.mode=m::n::ns)
    {U : Matrix (Fin m) (Fin m) ℝ} {sigma : Fin (min m (suffixSize (n::ns))) → ℝ}
    {V : Matrix (Fin (suffixSize (n::ns))) (Fin (suffixSize (n::ns))) ℝ}
    (h : ValidSVD (denseFirst (Original.input hshape A)) U sigma V) :
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
  dsimp only
  let F := explicitFirstFrames h (originalRanks S r 0)
  intro Z hZ start trace ht offset hl hs hz hcount hfull hN hA hstored
  let C : Fin F.count → NLA.Computation.TensorTrainApproximation.Tensor S :=
    fun j => Original.output hshape (completionOutput (F.frame j) (Z j))
  let ext := ttFiniteFamilyAt A C
  have hext (j : Fin F.count) : ext j.val=C j := ttFiniteFamilyAt_fin A C j
  have hp : 0<(trace.state offset).natural 75 := by rw [hcount];exact F.count_pos
  have hK : (trace.state offset).natural 75≤DenseSize S := by
    rw [hcount]
    exact tt_explicit_count_le_dense S r hr A hshape h
  have hcells : ∀ i<(trace.state offset).natural 75,∀ x,
      (trace.state offset).memory ((trace.state offset).natural 71+i*DenseSize S+Offset S x)=ext i x := by
    intro i hi x
    have hif : i<F.count := by rwa [hcount] at hi
    simpa only [ext,ttFiniteFamilyAt,dif_pos hif,C] using hstored ⟨i,hif⟩ x
  obtain ⟨winner,hw,hstatus,hbase,hwinner,herr,hmin,hm,hout,hcost⟩ :=
    ttBest_halt_original_at ht offset S r A ext hl hs hz hp hfull hK hN hA hcells
  let j : Fin F.count := ⟨winner,by rwa [hcount] at hw⟩
  have hj : ext winner=C j := hext j
  have hleast : ∀ i : Fin F.count,FrobeniusSq S A (C j)≤FrobeniusSq S A (C i) := by
    intro i
    have hi : i.val<(trace.state offset).natural 75 := by rw [hcount];exact i.isLt
    have hh := hmin i.val hi
    rwa [hj,hext i] at hh
  -- Only the universal actual-family clause is used. Its separate existence
  -- clause is deliberately ignored; Z and hZ are the supplied actual witnesses.
  have hactual := (Original.first_svd_explicit_strict_family S r hr A hshape h).2.2.2 Z hZ
  obtain ⟨hfeas,hstrict,hzero⟩ := hactual.2 j hleast
  refine ⟨j,?_,hstatus,hbase,hwinner,?_,hleast,hfeas,hstrict,hzero,hm,hcost⟩
  · refine ⟨(trace.state offset).natural 71+winner*DenseSize S,hstatus,?_⟩
    intro x
    rw [hj] at hout
    exact (hout x).symm
  · rw [hj] at herr
    exact herr

#assert_trust kernel ttFiniteFamilyAt
#assert_trust kernel ttFiniteFamilyAt_fin
#assert_trust kernel tt_min_add_one_le_prod
#assert_trust kernel tt_original_dense_two_le
#assert_trust kernel tt_first_format_product
#assert_trust kernel tt_explicit_count_le_dense
#assert_trust kernel ttBest_explicit_strict_at
#print axioms ttBest_explicit_strict_at
end NLA.Proofs.TR04
