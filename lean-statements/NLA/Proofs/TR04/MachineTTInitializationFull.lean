import NLA.Proofs.TR04.MachineTTInitialization
import NLA.Proofs.TR04.MachineTTInitialShape

/-! Complete actual initialization up to the first SVD opcode. Every legal
trace begins at the original Start with only the original real-valued headers. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout

def ttFirstRankEntryTime (S : Shape) (r : Ranks S) : ℕ :=
  ttFirstModeDecodedTime S+5+6+headerRangeTime (shapeHeaderValues S) 1 S.order+7+7+
    (3*ttFirstRankValue S r+5)+9

structure TTInitialRankRead (S : Shape) (r : Ranks S) (A : Tensor S)
    (s : State ttProgram) : Prop where
  label : s.label=157
  status : s.status=.running
  allocation : TTAllocationRegisters (ofShape S) s
  memory : s.memory=InputMemory S r A
  candidateZero : s.natural 76=0
  rows : s.natural 81=shapeHeaderValues S 0
  cols : s.natural 82=ttFirstCols S
  rank : s.natural 2=ttFirstRankValue S r

/-- The actual decoder/dispatch/caller composition reads the first mode,
entire remaining suffix and first requested rank without changing input memory. -/
theorem ttInitial_rank_read (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    TTInitialRankRead S r A (trace.state (ttFirstRankEntryTime S r)) ∧
    CostThrough ttProgram trace (ttFirstRankEntryTime S r)≤
      7*Size S r+3*shapeHeaderValues S 0+headerRangeTime (shapeHeaderValues S) 1 S.order+
        3*ttFirstRankValue S r+72 := by
  let t0 := ttFirstModeDecodedTime S
  let t1 := t0+5
  let t2 := t1+6+headerRangeTime (shapeHeaderValues S) 1 S.order
  let t3 := t2+7
  let t4 := t3+7+(3*ttFirstRankValue S r+5)
  let t5 := t4+9
  obtain ⟨hr0,ha0,hj0,hg0,hc0⟩ := ttInitial_mode_full S r A trace ht
  obtain ⟨hl1,hs1,hp01,hn1,hc1⟩ := ttHeaderDispatch_call_at ht t0 1 hr0.label hr0.status hg0
  have ha1 := ttInitPreserves_allocation hp01 ha0
  have hd1 : (trace.state t1).natural 0=S.order := ha1.order
  have hm1 : (trace.state t1).memory=InputMemory S r A := hp01.1.trans hr0.memory
  have hcall2 := ttModeSuffix_call_at ht t1 (shapeHeaderValues S) hl1 hs1 ha1.one
    (by rw [hd1];have := S.order_ge;omega) (by
      intro j _ hj
      rw [hd1] at hj
      rw [hm1]
      exact inputMemory_shapeHeader S r A j hj)
  rw [hd1] at hcall2
  obtain ⟨last,reals,hr2,hp12,hrows2,hg2,hc2⟩ := hcall2
  have hp02 := ttInitPreserves_trans hp01 hp12
  have ha2 := ttInitPreserves_allocation hp02 ha0
  have hcols2 : (trace.state t2).natural 2=ttFirstCols S :=
    (hr2.natural_apply 2).trans (headerRange_return_product _ _ _ _ _ _
      (by have := S.order_ge;omega))
  have hrows1 : (trace.state t1).natural 2=shapeHeaderValues S 0 :=
    (hn1 2 (by decide)).trans (hr0.natural_apply 2)
  have hm2 : (trace.state t2).memory=InputMemory S r A := hp02.1.trans hr0.memory
  obtain ⟨hl3,hs3,hp23,hn3,hc3⟩ := ttHeaderDispatch_call_at ht t2 2 hr2.label hr2.status hg2
  have hp03 := ttInitPreserves_trans hp02 hp23
  have ha3 := ttInitPreserves_allocation hp03 ha0
  have hd3 : (trace.state t3).natural 0=S.order := ha3.order
  have hm3 : (trace.state t3).memory=InputMemory S r A := hp03.1.trans hr0.memory
  have hcall4 := ttColsRank_call_at ht t3 (ttFirstRankValue S r) hl3 hs3 (by
    rw [hd3,hm3]
    exact inputMemory_firstRank S r A)
  obtain ⟨hr4,hp34,hrows4,hcols4,hg4,hc4⟩ := hcall4
  obtain ⟨hl5,hs5,hp45,hn5,hc5⟩ := ttHeaderDispatch_call_at ht t4 3 hr4.label hr4.status hg4
  have hp05 := ttInitPreserves_trans (ttInitPreserves_trans hp03 hp34) hp45
  have ha5 := ttInitPreserves_allocation hp05 ha0
  have hrows3 : (trace.state t3).natural 81=shapeHeaderValues S 0 :=
    (hn3 81 (by decide)).trans (hrows2.trans hrows1)
  have hcols3 : (trace.state t3).natural 2=ttFirstCols S :=
    (hn3 2 (by decide)).trans hcols2
  have hdata : TTInitialRankRead S r A (trace.state t5) :=
    ⟨hl5,hs5,ha5,hp05.1.trans hr0.memory,
      (hp05.2 76 (by unfold TTInitKept;decide)).trans hj0,
      (hn5 81 (by decide)).trans (hrows4.trans hrows3),
      (hn5 82 (by decide)).trans (hcols4.trans hcols3),
      (hn5 2 (by decide)).trans (hr4.natural_apply 2)⟩
  refine ⟨hdata,?_⟩
  change CostThrough ttProgram trace t0≤7*Size S r+28+(3*shapeHeaderValues S 0+5) at hc0
  change CostThrough ttProgram trace t1≤CostThrough ttProgram trace t0+5 at hc1
  change CostThrough ttProgram trace t2≤CostThrough ttProgram trace t1+6+
    headerRangeTime (shapeHeaderValues S) 1 S.order at hc2
  change CostThrough ttProgram trace t3≤CostThrough ttProgram trace t2+7 at hc3
  change CostThrough ttProgram trace t4≤CostThrough ttProgram trace t3+7+
    (3*ttFirstRankValue S r+5) at hc4
  change CostThrough ttProgram trace t5≤CostThrough ttProgram trace t4+9 at hc5
  change CostThrough ttProgram trace t5≤_
  omega

structure TTInitialSVDData (S : Shape) (r : Ranks S) (A : Tensor S)
    (s : State ttProgram) : Prop where
  label : s.label=167
  status : s.status=.running
  allocation : TTAllocationRegisters (ofShape S) s
  memory : s.memory=InputMemory S r A
  candidateZero : s.natural 76=0
  rows : s.natural 81=shapeHeaderValues S 0
  cols : s.natural 82=ttFirstCols S
  rank : s.natural 80=ttFirstRankValue S r
  minimum : s.natural 105=min (shapeHeaderValues S 0) (ttFirstCols S)
  cap : s.natural 106=min (ttFirstRankValue S r) (min (shapeHeaderValues S 0) (ttFirstCols S))

/-- One fixed finite program reaches its first actual full-SVD call for every
original input. The explicit prefix time and every charged operation have a
uniform linear bound; all allocation and data fields are actual trace fields. -/
theorem ttInitial_svd_ready (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    ∃ n : ℕ,n≤10 ∧
      TTInitialSVDData S r A (trace.state (ttFirstRankEntryTime S r+n)) ∧
      ttFirstRankEntryTime S r+n≤102*(Size S r+1) ∧
      CostThrough ttProgram trace (ttFirstRankEntryTime S r+n)≤102*(Size S r+1) := by
  obtain ⟨hd,hc⟩ := ttInitial_rank_read S r A trace ht
  obtain ⟨n,hn,he,hp,hc'⟩ := ttFirstRank_run_at ht (ttFirstRankEntryTime S r) hd.label hd.status
  obtain ⟨hl,hr,hmin,hcap,hm,hcols⟩ := ttFirstRank_fields (trace.state (ttFirstRankEntryTime S r))
  rw [← he] at hl hr hmin hcap hm hcols
  have hrun : (trace.state (ttFirstRankEntryTime S r+n)).status=.running := by
    rw [he]
    exact hd.status
  have hdata : TTInitialSVDData S r A (trace.state (ttFirstRankEntryTime S r+n)) :=
    ⟨hl,hrun,ttInitPreserves_allocation hp hd.allocation,hp.1.trans hd.memory,
      (hp.2 76 (by unfold TTInitKept;decide)).trans hd.candidateZero,
      hm.trans hd.rows,hcols.trans hd.cols,hr.trans hd.rank,
      by rw [hmin,hd.rows,hd.cols],by rw [hcap,hd.rank,hd.rows,hd.cols]⟩
  have hmode := ttFirstMode_le_size S r
  have hrank := ttFirstRankValue_le_size S r
  have hrange := headerRangeTime_shape_le_size S r 1
  have htime := headerProductTime_shape_le_size S r
  unfold headerProductTime at htime
  have hpref : headerProductReturnTime (shapeHeaderValues S) S.order≤7*Size S r := by
    unfold headerProductReturnTime
    omega
  refine ⟨n,hn,hdata,?_,by omega⟩
  unfold ttFirstRankEntryTime ttFirstModeDecodedTime ttInitialDecoderTime
  omega

#assert_trust kernel ttInitial_rank_read
#assert_trust kernel ttInitial_svd_ready
#print axioms ttInitial_rank_read
#print axioms ttInitial_svd_ready
end NLA.Proofs.TR04
