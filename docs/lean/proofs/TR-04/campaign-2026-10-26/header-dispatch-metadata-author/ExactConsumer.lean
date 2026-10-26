import NLA.Proofs.TR04.MachineTTMetadata
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace HeaderDispatchMetadataAuthorConsumer
open NLA.Computation.SVDMachine NLA.Proofs.TR04 NLA.Proofs.TR04.TTMemoryLayout

theorem literal_dispatch_all_handlers {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (k : Fin 11)
    (hl : (trace.state offset).label=10) (hs : (trace.state offset).status=.running)
    (hk : (trace.state offset).natural 97=k.val) :
    (trace.state (offset+(2*k.val+3))).label =
      ![119,144,150,157,214,222,230,295,303,311,319] k ∧
    (trace.state (offset+(2*k.val+3))).status=.running ∧
    (trace.state (offset+(2*k.val+3))).memory=(trace.state offset).memory ∧
    (trace.state (offset+(2*k.val+3))).real=(trace.state offset).real ∧
    (trace.state (offset+(2*k.val+3))).natural 123=k.val ∧
    (∀ i : Fin 128, i≠123 →
      (trace.state (offset+(2*k.val+3))).natural i=(trace.state offset).natural i) ∧
    CostThrough ttProgram trace (offset+(2*k.val+3))≤CostThrough ttProgram trace offset+(2*k.val+3) :=
  ttHeaderDispatch_fields_at ht offset k hl hs hk

theorem literal_initial_header_return {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=10) (hs : (trace.state offset).status=.running)
    (hk : (trace.state offset).natural 97=0) :
    (trace.state (offset+3)).label=119 :=
  (ttHeaderDispatch_fields_at ht offset (0:Fin 11) hl hs hk).1

theorem literal_final_header_return {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (hl : (trace.state offset).label=10) (hs : (trace.state offset).status=.running)
    (hk : (trace.state offset).natural 97=10) :
    (trace.state (offset+23)).label=319 :=
  (ttHeaderDispatch_fields_at ht offset (10:Fin 11) hl hs hk).1

theorem literal_four_metadata_cells {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ) (L : Layout) (level : ℕ)
    (hl : (trace.state offset).label=241) (hs : (trace.state offset).status=.running)
    (hm : (trace.state offset).natural 68=L.metadata)
    (h4 : (trace.state offset).natural 125=4) (hk : (trace.state offset).natural 84=level) :
    (trace.state (offset+14)).label=255 ∧
    (trace.state (offset+14)).status=.running ∧
    (trace.state (offset+14)).natural 93=L.metadata+4*level+4 ∧
    (∀ f : Fin 4, (trace.state (offset+14)).memory (L.metadata+4*level+f.val)=
      ((trace.state offset).natural (⟨85+f.val,by have := f.isLt;omega⟩:Fin 128):ℝ)) ∧
    (∀ a, ¬(L.metadata+4*level≤a ∧ a<L.metadata+4*level+4) →
      (trace.state (offset+14)).memory a=(trace.state offset).memory a) ∧
    (∀ i : Fin 128,i≠93 → (trace.state (offset+14)).natural i=(trace.state offset).natural i) ∧
    (∀ i : Fin 16,i≠13 → (trace.state (offset+14)).real i=(trace.state offset).real i) ∧
    CostThrough ttProgram trace (offset+14)≤CostThrough ttProgram trace offset+14 :=
  ttMetadata_fields_at ht offset L level hl hs hm h4 hk

#assert_trust kernel literal_dispatch_all_handlers
#assert_trust kernel literal_initial_header_return
#assert_trust kernel literal_final_header_return
#assert_trust kernel literal_four_metadata_cells
#print axioms literal_dispatch_all_handlers
#print axioms literal_initial_header_return
#print axioms literal_final_header_return
#print axioms literal_four_metadata_cells
end HeaderDispatchMetadataAuthorConsumer
#assert_trust kernel NLA.Proofs.TR04.ttHeaderHandler
#print axioms NLA.Proofs.TR04.ttHeaderHandler
#assert_trust kernel NLA.Proofs.TR04.ttHeaderTagLabel
#print axioms NLA.Proofs.TR04.ttHeaderTagLabel
#assert_trust kernel NLA.Proofs.TR04.ttHeaderCompareLabel
#print axioms NLA.Proofs.TR04.ttHeaderCompareLabel
#assert_trust kernel NLA.Proofs.TR04.ttHeaderRejectLabel
#print axioms NLA.Proofs.TR04.ttHeaderRejectLabel
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_header_tag
#print axioms NLA.Proofs.TR04.ttProgram_code_header_tag
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_header_compare
#print axioms NLA.Proofs.TR04.ttProgram_code_header_compare
#assert_trust kernel NLA.Proofs.TR04.ttHeaderRejectedState
#print axioms NLA.Proofs.TR04.ttHeaderRejectedState
#assert_trust kernel NLA.Proofs.TR04.ttHeaderDispatchEnd
#print axioms NLA.Proofs.TR04.ttHeaderDispatchEnd
#assert_trust kernel NLA.Proofs.TR04.ttHeader_reject_steps
#print axioms NLA.Proofs.TR04.ttHeader_reject_steps
#assert_trust kernel NLA.Proofs.TR04.ttHeader_accept_steps
#print axioms NLA.Proofs.TR04.ttHeader_accept_steps
#assert_trust kernel NLA.Proofs.TR04.ttHeader_scan_steps
#print axioms NLA.Proofs.TR04.ttHeader_scan_steps
#assert_trust kernel NLA.Proofs.TR04.ttHeaderDispatch_steps
#print axioms NLA.Proofs.TR04.ttHeaderDispatch_steps
#assert_trust kernel NLA.Proofs.TR04.ttOrdinary_nosvd_prefix_of_running
#print axioms NLA.Proofs.TR04.ttOrdinary_nosvd_prefix_of_running
#assert_trust kernel NLA.Proofs.TR04.ttHeaderDispatch_run_at
#print axioms NLA.Proofs.TR04.ttHeaderDispatch_run_at
#assert_trust kernel NLA.Proofs.TR04.ttHeaderDispatch_fields_at
#print axioms NLA.Proofs.TR04.ttHeaderDispatch_fields_at
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_241
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_241
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_242
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_242
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_243
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_243
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_244
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_244
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_245
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_245
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_246
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_246
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_247
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_247
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_248
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_248
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_249
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_249
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_250
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_250
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_251
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_251
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_252
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_252
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_253
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_253
#assert_trust kernel NLA.Proofs.TR04.ttProgram_code_metadata_254
#print axioms NLA.Proofs.TR04.ttProgram_code_metadata_254
#assert_trust kernel NLA.Proofs.TR04.ttMetadataCell
#print axioms NLA.Proofs.TR04.ttMetadataCell
#assert_trust kernel NLA.Proofs.TR04.ttMetadataState
#print axioms NLA.Proofs.TR04.ttMetadataState
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_setup
#print axioms NLA.Proofs.TR04.ttMetadata_setup
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_cell_steps
#print axioms NLA.Proofs.TR04.ttMetadata_cell_steps
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_cells_prefix
#print axioms NLA.Proofs.TR04.ttMetadata_cells_prefix
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_steps
#print axioms NLA.Proofs.TR04.ttMetadata_steps
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_run_at
#print axioms NLA.Proofs.TR04.ttMetadata_run_at
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_final_cell
#print axioms NLA.Proofs.TR04.ttMetadata_final_cell
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_fields_at
#print axioms NLA.Proofs.TR04.ttMetadata_fields_at
#assert_trust kernel NLA.Proofs.TR04.ttMetadata_nonzero_realRegisters
#print axioms NLA.Proofs.TR04.ttMetadata_nonzero_realRegisters
