import NLA.Proofs.TR04.TTDimensionBoundsReachable

/-! Exact original-header and branch identities for reachable recursive
formats. No new positivity, rank-capacity or recursion premise is introduced. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR04.TensorFormat.Dimensions
open NLA.Computation.TensorTrainApproximation

 theorem Reachable.next_mode_header (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :
    shapeHeaderValues S (level+1)=n := by
  have hlen := (h.original_invariants S r hr).2.2.2
  simp only [List.length_cons] at hlen
  have hlt : level+1<S.order := by omega
  have hh := congrArg List.head? h.tail_eq_drop
  have he : some n=some (shapeHeaderValues S (level+1)) := by
    simpa only [List.tail_cons,List.head?_cons,List.head?_drop,modeList_eq_ofFn,
      List.getElem?_ofFn,shapeHeaderValues,dif_pos hlt] using hh
  exact (Option.some.inj he).symm

 theorem Reachable.forward_test_iff (S : Shape) (r : Ranks S) (hr : ∀ j,1≤r j)
    {level m n : ℕ} {ns : List ℕ}
    (h : Reachable (modeList S.mode) (originalRanks S r) level (m::n::ns)) :
    (level+1<S.order-1) ↔ ns≠[] := by
  have hlen := (h.original_invariants S r hr).2.2.2
  simp only [List.length_cons] at hlen
  constructor
  · intro ht he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  · intro ht
    have hp := List.length_pos_iff.mpr ht
    omega

 theorem shifted_rank_succ (r : ℕ → ℕ) (level : ℕ) :
    (fun j => r (level+(j+1)))=(fun j => r ((level+1)+j)) := by
  funext j
  congr 1
  omega

#assert_trust kernel Reachable.next_mode_header
#assert_trust kernel Reachable.forward_test_iff
#assert_trust kernel shifted_rank_succ
#print axioms Reachable.next_mode_header
end NLA.Proofs.TR04.TensorFormat.Dimensions
