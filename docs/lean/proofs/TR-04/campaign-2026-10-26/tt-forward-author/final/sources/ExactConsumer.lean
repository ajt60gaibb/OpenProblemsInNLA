import NLA.Proofs.TR04.MachineTTForward
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace ForwardAuthorLiteralConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04 NLA.Proofs.TR04.TensorFormat

theorem literal_first_contraction {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q : ℕ) (ns : List ℕ)
    (stride frame input output metadata metadataCount : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 0)
    (hworkA : (trace.state offset).natural 69=output)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns))
    (hmetadata : DisjointBlocks metadata metadataCount output (q*suffixSize ns)) :
    let time := offset+19+(((8*m+11)*suffixSize ns+4)*q+1)+9
    (trace.state time).label=(if (trace.state offset).natural 84+1<(trace.state offset).natural 0-1 then 208 else 286) ∧
    (trace.state time).status=.running ∧
    (trace.state time).natural 89=output ∧
    (trace.state time).natural 90=(trace.state offset).natural 70 ∧
    (trace.state time).natural 100=q ∧
    (trace.state time).natural 84=(trace.state offset).natural 84+1 ∧
    (trace.state time).natural 110=(trace.state offset).natural 0-1 ∧
    StoresTensor (trace.state time).memory ((trace.state time).natural 89) (q::ns) (contract Q A) ∧
    StoresTensor (trace.state time).memory input (m::ns) A ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, metadata≤a ∧ a<metadata+metadataCount → (trace.state time).memory a=(trace.state offset).memory a) ∧
    (∀ i : Fin 16, ((i.val < 2) ∨ (5 ≤ i.val)) → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, (((i.val < 4) ∨ (21 ≤ i.val)) ∧ i≠97 ∧
      i≠89 ∧ i≠90 ∧ i≠100 ∧ i≠84 ∧ i≠110 ∧ i≠123) →
      (trace.state time).natural i=(trace.state offset).natural i) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+9 := by
  obtain ⟨h,hcost⟩ := ttForward_first_at ht offset m q ns stride frame input output hl hs hr hworkA hq Q hQ A hA hQblock hAblock
  exact ⟨h.label,h.running,h.current,h.nextBuffer,h.previousRank,h.level,h.lastLevel,
    h.currentStored,h.inputStored,h.frameStored,h.metadata metadata metadataCount hmetadata,
    h.realOutside,h.naturalOutside,hcost⟩
#assert_trust kernel literal_first_contraction
#print axioms literal_first_contraction

theorem literal_child_contraction {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q : ℕ) (ns : List ℕ)
    (stride frame input output metadata metadataCount : ℕ)
    (hl : (trace.state offset).label=255) (hs : (trace.state offset).status=.running)
    (hr : TTForwardRegisters (trace.state offset) m q (suffixSize ns) stride frame input output 1)
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (A : Tensor (m::ns)) (hA : StoresTensor (trace.state offset).memory input (m::ns) A)
    (hQblock : DisjointBlocks frame (m*stride) output (q*suffixSize ns))
    (hAblock : DisjointBlocks input (m*suffixSize ns) output (q*suffixSize ns))
    (hmetadata : DisjointBlocks metadata metadataCount output (q*suffixSize ns)) :
    let time := offset+19+(((8*m+11)*suffixSize ns+4)*q+1)+11
    (trace.state time).label=(if (trace.state offset).natural 84+1<(trace.state offset).natural 0-1 then 208 else 286) ∧
    (trace.state time).status=.running ∧
    (trace.state time).natural 89=output ∧
    (trace.state time).natural 90=input ∧
    (trace.state time).natural 100=q ∧
    (trace.state time).natural 84=(trace.state offset).natural 84+1 ∧
    (trace.state time).natural 110=(trace.state offset).natural 0-1 ∧
    StoresTensor (trace.state time).memory ((trace.state time).natural 89) (q::ns) (contract Q A) ∧
    StoresTensor (trace.state time).memory input (m::ns) A ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, metadata≤a ∧ a<metadata+metadataCount → (trace.state time).memory a=(trace.state offset).memory a) ∧
    (∀ i : Fin 16, ((i.val < 2) ∨ (5 ≤ i.val)) → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, (((i.val < 4) ∨ (21 ≤ i.val)) ∧ i≠97 ∧
      i≠89 ∧ i≠90 ∧ i≠100 ∧ i≠84 ∧ i≠110 ∧ i≠123) →
      (trace.state time).natural i=(trace.state offset).natural i) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+19+17*(q+m+suffixSize ns+1)^3+11 := by
  obtain ⟨h,hcost⟩ := ttForward_child_at ht offset m q ns stride frame input output hl hs hr hq Q hQ A hA hQblock hAblock
  exact ⟨h.label,h.running,h.current,h.nextBuffer,h.previousRank,h.level,h.lastLevel,
    h.currentStored,h.inputStored,h.frameStored,h.metadata metadata metadataCount hmetadata,
    h.realOutside,h.naturalOutside,hcost⟩
#assert_trust kernel literal_child_contraction
#print axioms literal_child_contraction

theorem literal_no_copy_child_format {old final : State ttProgram}
    {m q n : ℕ} {ns : List ℕ} {stride frame input output next : ℕ}
    {Q : Matrix (Fin m) (Fin q) ℝ} {A : Tensor (m::n::ns)}
    (h : TTForwardResult old final m q (n::ns) stride frame input output next Q A) :
    StoresTensor final.memory (final.natural 89) ((q*n)::ns) (merge q n ns (contract Q A)) :=
  h.mergedStored
#assert_trust kernel literal_no_copy_child_format
#print axioms literal_no_copy_child_format
end ForwardAuthorLiteralConsumer
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_255
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_255
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_256
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_256
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_257
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_257
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_258
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_258
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_259
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_259
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_260
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_260
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_261
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_261
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_262
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_262
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_263
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_263
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_264
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_264
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_265
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_265
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_266
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_266
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_267
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_267
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_268
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_268
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_269
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_269
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_270
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_270
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_271
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_271
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_272
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_272
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_273
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_273
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_274
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_274
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_275
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_275
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_276
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_276
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_277
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_277
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_278
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_278
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_279
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_279
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_280
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_280
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_281
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_281
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_282
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_282
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_283
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_283
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_284
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_284
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_285
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_285
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_286
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_286
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_forward_394
#print axioms NLA.Proofs.TR04.ttProgram_code_forward_394
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetupCells
#print axioms NLA.Proofs.TR04.ttForwardSetupCells
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetupNaturalPrefix
#print axioms NLA.Proofs.TR04.ttForwardSetupNaturalPrefix
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetupMiddle
#print axioms NLA.Proofs.TR04.ttForwardSetupMiddle
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetupEnd
#print axioms NLA.Proofs.TR04.ttForwardSetupEnd
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_first
#print axioms NLA.Proofs.TR04.ttForwardSetup_first
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_second
#print axioms NLA.Proofs.TR04.ttForwardSetup_second
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_third
#print axioms NLA.Proofs.TR04.ttForwardSetup_third
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_fourth
#print axioms NLA.Proofs.TR04.ttForwardSetup_fourth
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_steps
#print axioms NLA.Proofs.TR04.ttForwardSetup_steps
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_run_at
#print axioms NLA.Proofs.TR04.ttForwardSetup_run_at
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirstPointerState
#print axioms NLA.Proofs.TR04.ttForwardFirstPointerState
#assert_trust kernel NLA.Proofs.TR04.ttForwardChildPointerState
#print axioms NLA.Proofs.TR04.ttForwardChildPointerState
#assert_trust kernel NLA.Proofs.TR04.ttForwardLevelEnd
#print axioms NLA.Proofs.TR04.ttForwardLevelEnd
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirstEnd
#print axioms NLA.Proofs.TR04.ttForwardFirstEnd
#assert_trust kernel NLA.Proofs.TR04.ttForwardChildEnd
#print axioms NLA.Proofs.TR04.ttForwardChildEnd
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirst_pointer_steps
#print axioms NLA.Proofs.TR04.ttForwardFirst_pointer_steps
#assert_trust kernel NLA.Proofs.TR04.ttForwardChild_pointer_steps
#print axioms NLA.Proofs.TR04.ttForwardChild_pointer_steps
#assert_trust kernel NLA.Proofs.TR04.ttForwardLevel_steps
#print axioms NLA.Proofs.TR04.ttForwardLevel_steps
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirst_return_steps
#print axioms NLA.Proofs.TR04.ttForwardFirst_return_steps
#assert_trust kernel NLA.Proofs.TR04.ttForwardChild_return_steps
#print axioms NLA.Proofs.TR04.ttForwardChild_return_steps
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirst_return_at
#print axioms NLA.Proofs.TR04.ttForwardFirst_return_at
#assert_trust kernel NLA.Proofs.TR04.ttForwardChild_return_at
#print axioms NLA.Proofs.TR04.ttForwardChild_return_at
#assert_trust kernel NLA.Proofs.TR04.TTForwardReturnStable
#print axioms NLA.Proofs.TR04.TTForwardReturnStable
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirstEnd_fields
#print axioms NLA.Proofs.TR04.ttForwardFirstEnd_fields
#assert_trust kernel NLA.Proofs.TR04.ttForwardChildEnd_fields
#print axioms NLA.Proofs.TR04.ttForwardChildEnd_fields
#assert_trust kernel NLA.Proofs.TR04.ttForwardFirstEnd_natural
#print axioms NLA.Proofs.TR04.ttForwardFirstEnd_natural
#assert_trust kernel NLA.Proofs.TR04.ttForwardChildEnd_natural
#print axioms NLA.Proofs.TR04.ttForwardChildEnd_natural
#assert_trust kernel NLA.Proofs.TR04.TTForwardRegisters
#print axioms NLA.Proofs.TR04.TTForwardRegisters
#assert_trust kernel NLA.Proofs.TR04.ttForwardScratch
#print axioms NLA.Proofs.TR04.ttForwardScratch
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_relates
#print axioms NLA.Proofs.TR04.ttForwardSetup_relates
#assert_trust kernel NLA.Proofs.TR04.ttMatrix_natural_outside
#print axioms NLA.Proofs.TR04.ttMatrix_natural_outside
#assert_trust kernel NLA.Proofs.TR04.ttMatrix_real_outside
#print axioms NLA.Proofs.TR04.ttMatrix_real_outside
#assert_trust kernel NLA.Proofs.TR04.ttNaturalFold_outside
#print axioms NLA.Proofs.TR04.ttNaturalFold_outside
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_natural_outside
#print axioms NLA.Proofs.TR04.ttForwardSetup_natural_outside
#assert_trust kernel NLA.Proofs.TR04.ttForwardSetup_tag
#print axioms NLA.Proofs.TR04.ttForwardSetup_tag
#assert_trust kernel NLA.Proofs.TR04.ttForward_contract_at
#print axioms NLA.Proofs.TR04.ttForward_contract_at
#assert_trust kernel NLA.Proofs.TR04.TTForwardStable
#print axioms NLA.Proofs.TR04.TTForwardStable
#assert_trust kernel NLA.Proofs.TR04.TTForwardResult
#print axioms NLA.Proofs.TR04.TTForwardResult
#assert_trust kernel NLA.Proofs.TR04.TTForwardResult.currentStored
#print axioms NLA.Proofs.TR04.TTForwardResult.currentStored
#assert_trust kernel NLA.Proofs.TR04.TTForwardResult.metadata
#print axioms NLA.Proofs.TR04.TTForwardResult.metadata
#assert_trust kernel NLA.Proofs.TR04.TTForwardResult.mergedStored
#print axioms NLA.Proofs.TR04.TTForwardResult.mergedStored
#assert_trust kernel NLA.Proofs.TR04.ttForward_first_at
#print axioms NLA.Proofs.TR04.ttForward_first_at
#assert_trust kernel NLA.Proofs.TR04.ttForward_child_at
#print axioms NLA.Proofs.TR04.ttForward_child_at
