import NLA.Proofs.TR04.MachineTTInitializationFull
import NLA.Proofs.TR04.MachineTensorMemory
import NLA.Proofs.TR04.MachineTTReadOnly

/-! The actual first-SVD entry contains the original dense tensor in its
literal mixed-radix order, with disjoint output blocks and the exact first cut. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation TTMemoryLayout

theorem ttFirstMode_le_denseSize (S : Shape) : shapeHeaderValues S 0≤DenseSize S := by
  have hi : 0<S.order := by have := S.order_ge;omega
  have hm := shape_mode_le_denseSize S ⟨0,hi⟩
  rw [← shapeHeaderValues_fin S ⟨0,hi⟩] at hm
  exact hm

theorem ttInitial_first_format (S : Shape) :
    ∃ ns : List ℕ,TensorFormat.modeList S.mode=shapeHeaderValues S 0::ns ∧
      TensorFormat.suffixSize ns=ttFirstCols S ∧ ns.length+1=S.order := by
  cases he : TensorFormat.modeList S.mode with
  | nil =>
    have hl := TensorFormat.length_modeList S.mode
    rw [he] at hl
    have := S.order_ge
    simp only [List.length_nil] at hl
    omega
  | cons m ns =>
    have hc : ttFirstCols S=ns.prod := by
      have hh := headerRangeProduct_shape_drop S 1 (by have := S.order_ge;omega)
      rw [he] at hh
      exact hh
    have hp : m*ns.prod=DenseSize S := by
      have hh := TensorFormat.prod_modeList S.mode
      rw [he] at hh
      exact hh
    have hm : m=shapeHeaderValues S 0 := by
      have hprod := ttFirstCols_prod S
      have hpos := ttFirstCols_pos S
      rw [hc] at hprod hpos
      nlinarith
    have hl := TensorFormat.length_modeList S.mode
    rw [he] at hl
    refine ⟨ns,?_,?_,hl⟩
    · simpa only [hm] using he
    · exact (TensorFormat.tensor_suffixSize_eq_prod ns).trans hc.symm

theorem TTInitialSVDData.outputsDisjoint {S : Shape} {r : Ranks S} {A : Tensor S}
    {s : State ttProgram} (h : TTInitialSVDData S r A s) :
    OutputBlocksDisjoint (s.natural 81) (s.natural 82)
      (s.natural 72) (s.natural 73) (s.natural 74) := by
  rw [h.rows,h.cols,h.allocation.firstU,h.allocation.firstSigma,h.allocation.firstV]
  exact (ofShape S).first_outputs_disjoint _ _ (ttFirstMode_le_denseSize S)
    (ttFirstCols_le_denseSize S)

theorem TTInitialSVDData.storedOriginal {S : Shape} {r : Ranks S} {A : Tensor S}
    {s : State ttProgram} (h : TTInitialSVDData S r A s) :
    TensorFormat.StoresTensor s.memory (s.natural 92) (TensorFormat.modeList S.mode)
      (TensorFormat.originalTensorLinearEquiv S A) := by
  rw [h.memory,h.allocation.input]
  exact TensorFormat.storesTensor_original S A (InputMemory S r A) (ofShape S).input
    (TensorFormat.original_inputMemory_tensor_cell S r A)

def ttOriginalFirstView (S : Shape) (A : Tensor S) (ns : List ℕ)
    (h : TensorFormat.modeList S.mode=shapeHeaderValues S 0::ns) :
    TensorFormat.Tensor (shapeHeaderValues S 0::ns) :=
  h ▸ TensorFormat.originalTensorLinearEquiv S A

theorem ttStoresTensor_cast {ns ns' : List ℕ} {memory : ℕ → ℝ} {base : ℕ}
    {A : TensorFormat.Tensor ns} (he : ns=ns') (h : TensorFormat.StoresTensor memory base ns A) :
    TensorFormat.StoresTensor memory base ns' (he ▸ A) := by
  cases he
  exact h

theorem TTInitialSVDData.readFirst {S : Shape} {r : Ranks S} {A : Tensor S}
    {s : State ttProgram} (h : TTInitialSVDData S r A s) (ns : List ℕ)
    (he : TensorFormat.modeList S.mode=shapeHeaderValues S 0::ns) :
    readMatrix s.memory (shapeHeaderValues S 0) (TensorFormat.suffixSize ns) (s.natural 92)=
      TensorFormat.radixDenseFirst (ttOriginalFirstView S A ns he) :=
  (TensorFormat.storesTensor_readMatrix_iff _ _ _).mp (ttStoresTensor_cast he h.storedOriginal)

theorem ttFirstRankValue_originalRanks (S : Shape) (r : Ranks S) :
    ttFirstRankValue S r=TensorFormat.originalRanks S r 0 := by
  rw [TensorFormat.originalRanks,dif_pos (by have := S.order_ge;omega)]
  rfl

theorem TTInitialSVDData.rank_pos {S : Shape} {r : Ranks S} {A : Tensor S}
    {s : State ttProgram} (h : TTInitialSVDData S r A s) (hr : ∀ j,1≤r j) :
    1≤s.natural 80 := by
  rw [h.rank]
  exact hr _

theorem TTInitialSVDData.minimum_eq {S : Shape} {r : Ranks S} {A : Tensor S}
    {s : State ttProgram} (h : TTInitialSVDData S r A s) :
    s.natural 105=min (s.natural 81) (s.natural 82) := by
  rw [h.minimum,h.rows,h.cols]

theorem TTInitialSVDData.cap_eq {S : Shape} {r : Ranks S} {A : Tensor S}
    {s : State ttProgram} (h : TTInitialSVDData S r A s) :
    s.natural 106=min (s.natural 80) (min (s.natural 81) (s.natural 82)) := by
  rw [h.cap,h.rank,h.rows,h.cols]

#assert_trust kernel ttFirstMode_le_denseSize
#assert_trust kernel ttInitial_first_format
#assert_trust kernel TTInitialSVDData.outputsDisjoint
#assert_trust kernel TTInitialSVDData.storedOriginal
#assert_trust kernel ttOriginalFirstView
#assert_trust kernel ttStoresTensor_cast
#assert_trust kernel TTInitialSVDData.readFirst
#assert_trust kernel ttFirstRankValue_originalRanks
#assert_trust kernel TTInitialSVDData.rank_pos
#assert_trust kernel TTInitialSVDData.minimum_eq
#assert_trust kernel TTInitialSVDData.cap_eq
#print axioms TTInitialSVDData.readFirst
#print axioms TTInitialSVDData.outputsDisjoint
end NLA.Proofs.TR04
