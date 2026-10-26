import NLA.Proofs.TR04.MachineTTChildSVD
import NLA.Proofs.TR04.MachineTTStageForward

/-! Tensor-typed interpretation of each actual child SVD response. Every
legal tuple is retained, and its actual prefix frame supplies stage241. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine TTMemoryLayout TensorFormat

 theorem ttChild_svd_stage_at {start : State ttProgram} {trace : Trace ttProgram}
    (ht : LegalTrace ttProgram start trace) (offset : ℕ)
    (L : Layout) (level m : ℕ) (ns : List ℕ) (r : ℕ → ℕ) (A : Tensor (m::ns))
    (hl : (trace.state offset).label=237) (hs : (trace.state offset).status=.running)
    (ha : TTAllocationRegisters L (trace.state offset))
    (hlevel : (trace.state offset).natural 84=level) (hlevelBound : level<L.order)
    (hrows : (trace.state offset).natural 85=m)
    (hwidth : (trace.state offset).natural 86=stepRank m ns r)
    (hcols : (trace.state offset).natural 87=suffixSize ns)
    (hframe : (trace.state offset).natural 94=L.frame level)
    (hpair : TTWorkPair L (trace.state offset))
    (hA : StoresTensor (trace.state offset).memory ((trace.state offset).natural 89) (m::ns) A)
    (hm : m≤L.entries) (hc : suffixSize ns≤L.entries) :
    ∃ U : Matrix (Fin m) (Fin m) ℝ,
    ∃ sigma : Fin (min m (suffixSize ns)) → ℝ,
    ∃ V : Matrix (Fin (suffixSize ns)) (Fin (suffixSize ns)) ℝ,
      ValidSVD (radixDenseFirst A) U sigma V ∧
      (trace.state (offset+4)).label=241 ∧ (trace.state (offset+4)).status=.running ∧
      TTStageData L level m (stepRank m ns r) ns (stepFrame ns r U) A (trace.state (offset+4)) ∧
      TTStagePreserves L level (trace.state offset) (trace.state (offset+4)) ∧
      CostThrough ttProgram trace (offset+4)≤CostThrough ttProgram trace offset+(m+suffixSize ns+1)^3+3 := by
  let s := trace.state offset
  have hqm : s.natural 86≤s.natural 85 := by
    rw [hwidth,hrows]
    exact Dimensions.stepRank_le_rows m ns r
  have hreply := ttChild_svd_at ht offset s rfl hl hs L level hlevelBound
    (hrows ▸ hm) (hcols ▸ hc) hqm hframe ha.childSigma ha.childV (hpair.current_ge L s)
  revert hqm
  rw [hrows,hcols,hwidth]
  intro hqm hreply
  obtain ⟨U,sigma,V,hvalid,hlabel,hstatus,hstride,htag,hmem,hQ,hwork,hprotected,hn,hreal,hcost⟩ := hreply
  have hread := (storesTensor_readMatrix_iff s.memory (s.natural 89) A).mp hA
  rw [hread] at hvalid
  have hp : TTStagePreserves L level s (trace.state (offset+4)) :=
    ttStagePreserves_of_childSvd hprotected hn
  have hinput : StoresTensor (trace.state (offset+4)).memory (s.natural 89) (m::ns) A := by
    apply hA.memory_eq
    intro address had
    exact hwork address had.1
  have hdata : TTStageData L level m (stepRank m ns r) ns (stepFrame ns r U) A
      (trace.state (offset+4)) := by
    constructor
    · exact ttStagePreserves_allocation hp ha
    · exact (hn 84 (by decide) (by decide)).trans hlevel
    · exact (hn 85 (by decide) (by decide)).trans hrows
    · exact (hn 86 (by decide) (by decide)).trans hwidth
    · exact (hn 87 (by decide) (by decide)).trans hcols
    · exact (hn 94 (by decide) (by decide)).trans hframe
    · exact Or.inr hstride
    · rw [hstride]
      exact hQ
    · rw [hn 89 (by decide) (by decide)]
      exact hinput
    · apply Or.inr
      refine ⟨htag,?_⟩
      rcases hpair with ⟨hin,hout⟩|⟨hin,hout⟩
      · exact Or.inl ⟨(hn 89 (by decide) (by decide)).trans hin,(hn 90 (by decide) (by decide)).trans hout⟩
      · exact Or.inr ⟨(hn 89 (by decide) (by decide)).trans hin,(hn 90 (by decide) (by decide)).trans hout⟩
  exact ⟨U,sigma,V,hvalid,hlabel,hstatus,hdata,hp,hcost⟩

#assert_trust kernel ttChild_svd_stage_at
#print axioms ttChild_svd_stage_at
end NLA.Proofs.TR04
