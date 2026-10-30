import NLA.Proofs.TR04.MachineTTStartup
import NLA.Proofs.TR04.MachineTTInitializationTrace

/-! Composed actual initialization from the original tensor input. In
particular, the first real mode header is loaded by literal caller code before
its natural decoding; no natural header or allocation is supplied at Start. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout

def ttInitialDecoderTime (S : Shape) : ℕ :=
  headerProductReturnTime (shapeHeaderValues S) S.order+28

/-- Every original input trace reaches the actual first decoder, after the
whole size scan, finite return dispatch and literal pointer/read startup. -/
theorem ttInitial_decoder (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    ∃ scratch : ℝ,
      ttHeaderEmbedding.Relates
        (headerProductDecodeState (InputMemory S r A) S.order S.order 1
          (shapeHeaderValues S 0) scratch) (trace.state (ttInitialDecoderTime S)) ∧
      TTAllocationRegisters (ofShape S) (trace.state (ttInitialDecoderTime S)) ∧
      (trace.state (ttInitialDecoderTime S)).natural 76=0 ∧
      (trace.state (ttInitialDecoderTime S)).natural 97=1 ∧
      CostThrough ttProgram trace (ttInitialDecoderTime S)≤7*Size S r+28 := by
  let time := headerProductReturnTime (shapeHeaderValues S) S.order
  obtain ⟨hl,hs,hN,hmem,hcost⟩ := ttProgram_header_result S r A trace ht
  have hentry : ttHeaderEmbedding.Relates
      (initial headerProductProgram S.order (InputMemory S r A)) (trace.state 0) := by
    rw [ht.1]
    exact ttHeader_initial_relates _ _
  obtain ⟨counter,reals,hr,_⟩ := ttHeaderEmbedding.headerProduct_run_at (InputMemory S r A)
    S.order (shapeHeaderValues S) (inputMemory_shapeHeader S r A) ht 0 hentry
  simp only [zero_add] at hr
  have hd : (trace.state time).natural 0=S.order := hr.natural_apply 0
  have htag : (trace.state time).natural 97=(0 : Fin 11).val :=
    ttProgram_header_natural_outside S r A trace ht 97 (by decide)
  have hz : (trace.state time).natural 127=0 :=
    ttProgram_header_natural_outside S r A trace ht 127 (by decide)
  obtain ⟨hdl,hds,hdm,_,_,hdn,hdc⟩ := ttHeaderDispatch_fields_at ht time 0 hl hs htag
  change (trace.state (time+3)).label=119 at hdl
  change (trace.state (time+3)).status=.running at hds
  change (trace.state (time+3)).memory=(trace.state time).memory at hdm
  change ∀ i : Fin 128,i≠123 →
    (trace.state (time+3)).natural i=(trace.state time).natural i at hdn
  change CostThrough ttProgram trace (time+3)≤CostThrough ttProgram trace time+3 at hdc
  have hd' := (hdn 0 (by decide)).trans hd
  have hn' := (hdn 2 (by decide)).trans hN
  have hz' := (hdn 127 (by decide)).trans hz
  have hmem' := hdm.trans hmem
  have hmode : (trace.state (time+3)).memory 0=(shapeHeaderValues S 0 : ℝ) := by
    rw [hmem']
    exact inputMemory_shapeHeader S r A 0 (by have := S.order_ge;omega)
  obtain ⟨hdecode,halloc,hj,htag',hc⟩ := ttStartup_run_at ht (time+3)
    (ofShape S) (shapeHeaderValues S 0) hdl hds hd' hn' hz' hmode
  have htime : time+3+25=ttInitialDecoderTime S := by
    unfold ttInitialDecoderTime
    dsimp [time]
  rw [htime] at hdecode halloc hj htag' hc
  rw [hmem'] at hdecode
  refine ⟨(trace.state (time+3)).real 1,hdecode,halloc,hj,htag',?_⟩
  dsimp [time] at hcost hdc hc ⊢
  omega

def ttFirstModeDecodedTime (S : Shape) : ℕ :=
  ttInitialDecoderTime S+(3*shapeHeaderValues S 0+5)

/-- The read mode is decoded by the same actual finite instruction bank.
All original input cells are retained and the charged prefix is explicit. -/
theorem ttInitial_mode_decoded (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    (trace.state (ttFirstModeDecodedTime S)).label=10 ∧
    (trace.state (ttFirstModeDecodedTime S)).status=.running ∧
    (trace.state (ttFirstModeDecodedTime S)).natural 0=S.order ∧
    (trace.state (ttFirstModeDecodedTime S)).natural 2=shapeHeaderValues S 0 ∧
    (trace.state (ttFirstModeDecodedTime S)).memory=InputMemory S r A ∧
    CostThrough ttProgram trace (ttFirstModeDecodedTime S)≤
      7*Size S r+28+(3*shapeHeaderValues S 0+5) := by
  obtain ⟨scratch,hentry,_,_,_,hc⟩ := ttInitial_decoder S r A trace ht
  obtain ⟨hr,hc'⟩ := ttHeaderEmbedding.headerSingle_run_at (InputMemory S r A)
    S.order (shapeHeaderValues S 0) scratch ht (ttInitialDecoderTime S) hentry
  refine ⟨hr.label,hr.status,hr.natural_apply 0,hr.natural_apply 2,hr.memory,?_⟩
  unfold ttFirstModeDecodedTime
  omega

theorem ttInitial_mode_full (S : Shape) (r : Ranks S) (A : Tensor S)
    (trace : Trace ttProgram) (ht : LegalTrace ttProgram (Start ttProgram S r A) trace) :
    ttHeaderEmbedding.Relates
      (headerSingleReturnState (InputMemory S r A) S.order (shapeHeaderValues S 0))
      (trace.state (ttFirstModeDecodedTime S)) ∧
    TTAllocationRegisters (ofShape S) (trace.state (ttFirstModeDecodedTime S)) ∧
    (trace.state (ttFirstModeDecodedTime S)).natural 76=0 ∧
    (trace.state (ttFirstModeDecodedTime S)).natural 97=1 ∧
    CostThrough ttProgram trace (ttFirstModeDecodedTime S)≤
      7*Size S r+28+(3*shapeHeaderValues S 0+5) := by
  obtain ⟨scratch,hentry,halloc,hj,htag,hc⟩ := ttInitial_decoder S r A trace ht
  obtain ⟨hr,hn,hc'⟩ := ttHeaderSingle_full_at ht (ttInitialDecoderTime S) (InputMemory S r A)
    S.order (shapeHeaderValues S 0) scratch hentry
  have hp : TTInitPreserves (trace.state (ttInitialDecoderTime S))
      (trace.state (ttFirstModeDecodedTime S)) :=
    ttHeader_preserves_of_outside (hr.memory.trans hentry.memory.symm)
      ((hr.natural_apply 0).trans (hentry.natural_apply 0).symm) hn
  exact ⟨hr,ttInitPreserves_allocation hp halloc,
    (hn 76 (by decide)).trans hj,(hn 97 (by decide)).trans htag,by
      unfold ttFirstModeDecodedTime;omega⟩

#assert_trust kernel ttInitial_mode_full
#print axioms ttInitial_mode_full
#assert_trust kernel ttInitial_decoder
#assert_trust kernel ttInitial_mode_decoded
#print axioms ttInitial_decoder
#print axioms ttInitial_mode_decoded
end NLA.Proofs.TR04
