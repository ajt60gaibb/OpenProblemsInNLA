import NLA.Proofs.TR04.MachineTTInitializationTrace
import NLA.Proofs.TR04.TTDimensionBoundsReachable

/-! Exact original shape/rank values read by initialization, and their actual
suffix products. Header casts retain every original mode and requested rank. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04
open NLA.Computation.SVDMachine NLA.Computation.TensorTrainApproximation

def ttFirstRankValue (S : Shape) (r : Ranks S) : ℕ :=
  r ⟨0,by have := S.order_ge;omega⟩

def ttFirstCols (S : Shape) : ℕ := headerRangeProduct (shapeHeaderValues S) 1 S.order

theorem inputMemory_rankHeader (S : Shape) (r : Ranks S) (A : Tensor S)
    (j : ℕ) (hj : j<S.order-1) :
    InputMemory S r A (S.order+j)=(r ⟨j,hj⟩ : ℝ) := by
  have hnot : ¬S.order+j<S.order := by omega
  simp [InputMemory,hnot,hj]

theorem inputMemory_firstRank (S : Shape) (r : Ranks S) (A : Tensor S) :
    InputMemory S r A S.order=(ttFirstRankValue S r : ℝ) := by
  simpa only [Nat.add_zero,ttFirstRankValue] using
    inputMemory_rankHeader S r A 0 (by have := S.order_ge;omega)

theorem headerRangeProduct_shape_drop (S : Shape) (a : ℕ) (ha : a≤S.order) :
    headerRangeProduct (shapeHeaderValues S) a S.order=
      ((TensorFormat.modeList S.mode).drop a).prod := by
  rw [TensorFormat.modeList_eq_ofFn,TensorFormat.drop_ofFn_modes S.mode a ha,List.prod_ofFn]
  unfold headerRangeProduct
  rw [Finset.prod_Ico_eq_prod_range,← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i _
  have hi : a+i.val<S.order := by have := i.isLt;omega
  simp only [shapeHeaderValues,dif_pos hi]

theorem ttFirstCols_prod (S : Shape) :
    shapeHeaderValues S 0*ttFirstCols S=DenseSize S := by
  have h := Finset.prod_range_eq_mul_Ico (shapeHeaderValues S)
    (by have := S.order_ge;omega : 0<S.order)
  rw [shapeHeaderValues_product] at h
  exact h.symm

theorem ttFirstCols_pos (S : Shape) : 0<ttFirstCols S := by
  unfold ttFirstCols headerRangeProduct
  apply Finset.prod_pos
  intro j hj
  have hlt := (Finset.mem_Ico.mp hj).2
  rw [shapeHeaderValues,dif_pos hlt]
  have := S.mode_ge ⟨j,hlt⟩
  omega

theorem ttFirstCols_le_denseSize (S : Shape) : ttFirstCols S≤DenseSize S := by
  have hm : 1≤shapeHeaderValues S 0 := by
    rw [shapeHeaderValues,dif_pos (by have := S.order_ge;omega)]
    have := S.mode_ge ⟨0,by have := S.order_ge;omega⟩
    omega
  rw [← ttFirstCols_prod S]
  exact Nat.le_mul_of_pos_left _ hm

theorem ttFirstMode_le_size (S : Shape) (r : Ranks S) : shapeHeaderValues S 0≤Size S r := by
  have hi : 0<S.order := by have := S.order_ge;omega
  have hm := shape_mode_le_denseSize S ⟨0,hi⟩
  rw [← shapeHeaderValues_fin S ⟨0,hi⟩] at hm
  exact hm.trans (shape_denseSize_le_size S r)

theorem ttFirstRankValue_le_size (S : Shape) (r : Ranks S) : ttFirstRankValue S r≤Size S r := by
  have hr : ttFirstRankValue S r≤∑ j,r j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (r j))
      (Finset.mem_univ (⟨0,by have := S.order_ge;omega⟩ : Cut S))
  unfold Size
  omega

theorem headerRangeTime_shape_le_size (S : Shape) (r : Ranks S) (a : ℕ) :
    headerRangeTime (shapeHeaderValues S) a S.order≤7*Size S r := by
  have hh := headerRange_time_le (shapeHeaderValues S) a S.order
  have hs := headerProductTime_shape_le_size S r
  unfold headerProductTime at hs
  omega

#assert_trust kernel inputMemory_rankHeader
#assert_trust kernel inputMemory_firstRank
#assert_trust kernel headerRangeProduct_shape_drop
#assert_trust kernel ttFirstCols_prod
#assert_trust kernel ttFirstCols_pos
#assert_trust kernel ttFirstCols_le_denseSize
#assert_trust kernel ttFirstMode_le_size
#assert_trust kernel ttFirstRankValue_le_size
#assert_trust kernel headerRangeTime_shape_le_size
#print axioms headerRangeProduct_shape_drop
#print axioms ttFirstCols_prod
end NLA.Proofs.TR04
