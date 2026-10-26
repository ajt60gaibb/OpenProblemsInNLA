import NLA.Proofs.TR04.MachineTTReverse
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
namespace ReverseAuthorLiteralConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04 NLA.Proofs.TR04.TensorFormat

theorem literal_reverse_level {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset m q n : ℕ) (ns : List ℕ)
    (stride frame input output protectedBase protectedCount : ℕ)
    (hl : (trace.state offset).label=287) (hs : (trace.state offset).status=.running)
    (hr : TTReverseRegisters (trace.state offset) frame input output)
    (hm : (trace.state offset).memory ((trace.state offset).natural 68+4*(trace.state offset).natural 84)=(m : ℝ))
    (hqmeta : (trace.state offset).memory ((trace.state offset).natural 68+4*(trace.state offset).natural 84+1)=(q : ℝ))
    (hcmeta : (trace.state offset).memory ((trace.state offset).natural 68+4*(trace.state offset).natural 84+2)=(suffixSize (n::ns) : ℝ))
    (hsmeta : (trace.state offset).memory ((trace.state offset).natural 68+4*(trace.state offset).natural 84+3)=(stride : ℝ))
    (hq : q≤stride) (Q : Matrix (Fin m) (Fin q) ℝ)
    (hQ : StoresFrame (trace.state offset).memory frame stride Q)
    (Z : Tensor ((q*n)::ns)) (hZ : StoresTensor (trace.state offset).memory input ((q*n)::ns) Z)
    (hQblock : DisjointBlocks frame (m*stride) output (m*suffixSize (n::ns)))
    (hZblock : DisjointBlocks input (q*suffixSize (n::ns)) output (m*suffixSize (n::ns)))
    (hprotected : DisjointBlocks protectedBase protectedCount output (m*suffixSize (n::ns))) :
    let time := offset+(3*(m+q+suffixSize (n::ns)+stride)+132)+22+
      (((8*q+11)*suffixSize (n::ns)+4)*m+1)+8
    (trace.state time).label=(if (trace.state offset).natural 84=0 then 349 else 287) ∧
    (trace.state time).status=.running ∧
    (trace.state time).natural 89=output ∧ (trace.state time).natural 90=input ∧
    (trace.state time).natural 84=(trace.state offset).natural 84-1 ∧
    ((trace.state offset).natural 84=0 → (trace.state time).natural 123=
      (trace.state offset).natural 71+(trace.state offset).natural 76*(trace.state offset).natural 64) ∧
    (trace.state time).natural 94=frame ∧ (trace.state time).natural 88=stride ∧
    StoresTensor (trace.state time).memory ((trace.state time).natural 89) (m::n::ns)
      (lift Q ((merge q n ns).symm Z)) ∧
    StoresFrame (trace.state time).memory frame stride Q ∧
    (∀ a, protectedBase≤a ∧ a<protectedBase+protectedCount →
      (trace.state time).memory a=(trace.state offset).memory a) ∧
    (∀ i : Fin 16, 5 ≤ i.val → (trace.state time).real i=(trace.state offset).real i) ∧
    (∀ i : Fin 128, TTReverseStable i → (trace.state time).natural i=(trace.state offset).natural i) ∧
    CostThrough ttProgram trace time≤CostThrough ttProgram trace offset+
      (3*(m+q+suffixSize (n::ns)+stride)+132)+22+17*(m+q+suffixSize (n::ns)+1)^3+8 := by
  obtain ⟨h,hcost⟩ := ttReverse_unmerge_at ht offset m q n ns stride frame input output hl hs hr
    ⟨hm,hqmeta,hcmeta,hsmeta⟩ hq Q hQ Z hZ hQblock hZblock
  have htime : offset+ttReverseMetadataTime m q (suffixSize (n::ns)) stride+22+
      matrixMultiplyReturnTime (liftMultiplyData (trace.state offset).memory m q (n::ns) frame stride input output)+8 =
      offset+(3*(m+q+suffixSize (n::ns)+stride)+132)+22+
        (((8*q+11)*suffixSize (n::ns)+4)*m+1)+8 := by
    rw [ttReverseMetadataTime_eq]
    rfl
  rw [htime] at h hcost
  rw [ttReverseMetadataTime_eq] at hcost
  exact ⟨h.label,h.running,h.current,h.nextBuffer,h.level,h.candidatePointer,h.frameAddress,h.rowStride,
    h.currentStored,h.frameStored,h.protected protectedBase protectedCount hprotected,
    h.realOutside,h.naturalOutside,hcost⟩

theorem literal_reverse_initial_decrement {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=286) (hs : (trace.state offset).status=.running) :
    (trace.state (offset+1)).label=287 ∧ (trace.state (offset+1)).status=.running ∧
    (trace.state (offset+1)).natural 84=(trace.state offset).natural 84-1 ∧
    (trace.state (offset+1)).memory=(trace.state offset).memory ∧
    (trace.state (offset+1)).real=(trace.state offset).real ∧
    (∀ i : Fin 128, i≠84 → (trace.state (offset+1)).natural i=(trace.state offset).natural i) ∧
    CostThrough ttProgram trace (offset+1)≤CostThrough ttProgram trace offset+1 := by
  obtain ⟨h,hc⟩ := ttReverse_start_at ht offset hl hs
  rw [h]
  refine ⟨rfl,rfl,?_,rfl,rfl,?_,hc⟩
  · exact Function.update_self _ _ _
  · intro i hi
    exact Function.update_of_ne hi _ _

theorem literal_prefix_stepOutput {old final : State ttProgram} {m n : ℕ} {ns : List ℕ}
    {r : ℕ → ℕ} {U : Matrix (Fin m) (Fin m) ℝ} {stride frame input output : ℕ}
    {Z : Tensor ((stepRank m (n::ns) r*n)::ns)}
    (h : TTReverseResult old final m (stepRank m (n::ns) r) (n::ns) stride frame input output
      (stepFrame (n::ns) r U) ((merge (stepRank m (n::ns) r) n ns).symm Z)) :
    StoresTensor final.memory (final.natural 89) (m::n::ns) (stepOutput r U Z) :=
  h.currentStored

#assert_trust kernel literal_reverse_level
#assert_trust kernel literal_reverse_initial_decrement
#assert_trust kernel literal_prefix_stepOutput
#print axioms literal_reverse_level
#print axioms literal_reverse_initial_decrement
#print axioms literal_prefix_stepOutput
end ReverseAuthorLiteralConsumer
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_286
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_286
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_287
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_287
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_288
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_288
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_289
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_289
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_290
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_290
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_291
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_291
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_292
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_292
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_293
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_293
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_294
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_294
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_295
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_295
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_296
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_296
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_297
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_297
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_298
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_298
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_299
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_299
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_300
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_300
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_301
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_301
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_302
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_302
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_303
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_303
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_304
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_304
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_305
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_305
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_306
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_306
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_307
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_307
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_308
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_308
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_309
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_309
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_310
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_310
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_311
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_311
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_312
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_312
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_313
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_313
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_314
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_314
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_315
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_315
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_316
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_316
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_317
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_317
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_318
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_318
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_319
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_319
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_320
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_320
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_321
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_321
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_322
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_322
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_323
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_323
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_324
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_324
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_325
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_325
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_326
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_326
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_327
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_327
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_328
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_328
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_329
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_329
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_330
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_330
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_331
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_331
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_332
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_332
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_333
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_333
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_334
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_334
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_335
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_335
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_336
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_336
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_337
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_337
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_338
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_338
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_339
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_339
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_340
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_340
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_341
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_341
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_342
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_342
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_343
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_343
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_344
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_344
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_345
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_345
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_346
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_346
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_347
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_347
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_reverse_348
#print axioms NLA.Proofs.TR04.ttProgram_code_reverse_348
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadLabel
#print axioms NLA.Proofs.TR04.ttReverseReadLabel
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadHandler
#print axioms NLA.Proofs.TR04.ttReverseReadHandler
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadAddress
#print axioms NLA.Proofs.TR04.ttReverseReadAddress
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadNatural
#print axioms NLA.Proofs.TR04.ttReverseReadNatural
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadEntry
#print axioms NLA.Proofs.TR04.ttReverseReadEntry
#assert_trust kernel NLA.Proofs.TR04.ttReverseRead_steps
#print axioms NLA.Proofs.TR04.ttReverseRead_steps
#assert_trust kernel NLA.Proofs.TR04.ttReverseHeader_real_map
#print axioms NLA.Proofs.TR04.ttReverseHeader_real_map
#assert_trust kernel NLA.Proofs.TR04.ttReverseHeader_natural_map
#print axioms NLA.Proofs.TR04.ttReverseHeader_natural_map
#assert_trust kernel NLA.Proofs.TR04.ttReverseHeaderEnd
#print axioms NLA.Proofs.TR04.ttReverseHeaderEnd
#assert_trust kernel NLA.Proofs.TR04.ttReverseHeader_real_outside
#print axioms NLA.Proofs.TR04.ttReverseHeader_real_outside
#assert_trust kernel NLA.Proofs.TR04.ttReverseHeader_full_at
#print axioms NLA.Proofs.TR04.ttReverseHeader_full_at
#assert_trust kernel NLA.Proofs.TR04.ttReverseRead_relates
#print axioms NLA.Proofs.TR04.ttReverseRead_relates
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadEnd
#print axioms NLA.Proofs.TR04.ttReverseReadEnd
#assert_trust kernel NLA.Proofs.TR04.ttReverseRead_call_at
#print axioms NLA.Proofs.TR04.ttReverseRead_call_at
#assert_trust kernel NLA.Proofs.TR04.TTReverseMetadata
#print axioms NLA.Proofs.TR04.TTReverseMetadata
#assert_trust kernel NLA.Proofs.TR04.ttReverseReadEnd_fields
#print axioms NLA.Proofs.TR04.ttReverseReadEnd_fields
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadataEnd
#print axioms NLA.Proofs.TR04.ttReverseMetadataEnd
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadataTime
#print axioms NLA.Proofs.TR04.ttReverseMetadataTime
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadataTime_eq
#print axioms NLA.Proofs.TR04.ttReverseMetadataTime_eq
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadata_run_at
#print axioms NLA.Proofs.TR04.ttReverseMetadata_run_at
#assert_trust kernel NLA.Proofs.TR04.TTReverseMetadataStable
#print axioms NLA.Proofs.TR04.TTReverseMetadataStable
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadataEnd_natural
#print axioms NLA.Proofs.TR04.ttReverseMetadataEnd_natural
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadataEnd_real
#print axioms NLA.Proofs.TR04.ttReverseMetadataEnd_real
#assert_trust kernel NLA.Proofs.TR04.ttReverseMetadataEnd_fields
#print axioms NLA.Proofs.TR04.ttReverseMetadataEnd_fields
#assert_trust kernel NLA.Proofs.TR04.ttReverseStartState
#print axioms NLA.Proofs.TR04.ttReverseStartState
#assert_trust kernel NLA.Proofs.TR04.ttReverseStart_step
#print axioms NLA.Proofs.TR04.ttReverseStart_step
#assert_trust kernel NLA.Proofs.TR04.ttReverse_start_at
#print axioms NLA.Proofs.TR04.ttReverse_start_at
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftDataState
#print axioms NLA.Proofs.TR04.ttReverseLiftDataState
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_data_steps
#print axioms NLA.Proofs.TR04.ttReverseLift_data_steps
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetupCells
#print axioms NLA.Proofs.TR04.ttReverseLiftSetupCells
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetupNaturalPrefix
#print axioms NLA.Proofs.TR04.ttReverseLiftSetupNaturalPrefix
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetupMiddle
#print axioms NLA.Proofs.TR04.ttReverseLiftSetupMiddle
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetupEnd
#print axioms NLA.Proofs.TR04.ttReverseLiftSetupEnd
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_setup_six
#print axioms NLA.Proofs.TR04.ttReverseLift_setup_six
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_setup_twelve
#print axioms NLA.Proofs.TR04.ttReverseLift_setup_twelve
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_setup_eighteen
#print axioms NLA.Proofs.TR04.ttReverseLift_setup_eighteen
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_setup_jump
#print axioms NLA.Proofs.TR04.ttReverseLift_setup_jump
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_setup_steps
#print axioms NLA.Proofs.TR04.ttReverseLift_setup_steps
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftReturnEnd
#print axioms NLA.Proofs.TR04.ttReverseLiftReturnEnd
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_return_steps
#print axioms NLA.Proofs.TR04.ttReverseLift_return_steps
#assert_trust kernel NLA.Proofs.TR04.TTReverseLiftRegisters
#print axioms NLA.Proofs.TR04.TTReverseLiftRegisters
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetup_relates
#print axioms NLA.Proofs.TR04.ttReverseLiftSetup_relates
#assert_trust kernel NLA.Proofs.TR04.TTReverseLiftSetupStable
#print axioms NLA.Proofs.TR04.TTReverseLiftSetupStable
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetup_natural_outside
#print axioms NLA.Proofs.TR04.ttReverseLiftSetup_natural_outside
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetup_tag
#print axioms NLA.Proofs.TR04.ttReverseLiftSetup_tag
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftSetup_fields
#print axioms NLA.Proofs.TR04.ttReverseLiftSetup_fields
#assert_trust kernel NLA.Proofs.TR04.ttReverse_lift_at
#print axioms NLA.Proofs.TR04.ttReverse_lift_at
#assert_trust kernel NLA.Proofs.TR04.TTReverseReturnStable
#print axioms NLA.Proofs.TR04.TTReverseReturnStable
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftReturnEnd_natural
#print axioms NLA.Proofs.TR04.ttReverseLiftReturnEnd_natural
#assert_trust kernel NLA.Proofs.TR04.ttReverseLiftReturnEnd_fields
#print axioms NLA.Proofs.TR04.ttReverseLiftReturnEnd_fields
#assert_trust kernel NLA.Proofs.TR04.ttReverseLift_return_at
#print axioms NLA.Proofs.TR04.ttReverseLift_return_at
#assert_trust kernel NLA.Proofs.TR04.TTReverseStable
#print axioms NLA.Proofs.TR04.TTReverseStable
#assert_trust kernel NLA.Proofs.TR04.TTReverseResult
#print axioms NLA.Proofs.TR04.TTReverseResult
#assert_trust kernel NLA.Proofs.TR04.TTReverseResult.currentStored
#print axioms NLA.Proofs.TR04.TTReverseResult.currentStored
#assert_trust kernel NLA.Proofs.TR04.TTReverseResult.protected
#print axioms NLA.Proofs.TR04.TTReverseResult.protected
#assert_trust kernel NLA.Proofs.TR04.TTReverseResult.rebase
#print axioms NLA.Proofs.TR04.TTReverseResult.rebase
#assert_trust kernel NLA.Proofs.TR04.ttReverse_lift_return_at
#print axioms NLA.Proofs.TR04.ttReverse_lift_return_at
#assert_trust kernel NLA.Proofs.TR04.TTReverseRegisters
#print axioms NLA.Proofs.TR04.TTReverseRegisters
#assert_trust kernel NLA.Proofs.TR04.ttReverse_at
#print axioms NLA.Proofs.TR04.ttReverse_at
#assert_trust kernel NLA.Proofs.TR04.ttReverse_unmerge_at
#print axioms NLA.Proofs.TR04.ttReverse_unmerge_at
