import NLA.Proofs.TR04.Feasible
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.TR04
open NLA.Computation.TensorTrainApproximation
open Set

/-- Squared error is a continuous finite sum on the actual tensor space. -/
theorem continuous_frobeniusSq (S : Shape) (A : Tensor S) :
    Continuous (FrobeniusSq S A) := by
  unfold FrobeniusSq
  exact continuous_finsetSum _ fun a _ =>
    (continuous_const.sub (continuous_apply a)).pow 2

theorem frobeniusSq_nonneg (S : Shape) (A Y : Tensor S) :
    0 ≤ FrobeniusSq S A Y :=
  Finset.sum_nonneg fun a _ => sq_nonneg (A a - Y a)

theorem frobeniusSq_coordinate_le (S : Shape) (A Y : Tensor S) (a : Index S) :
    (A a - Y a)^2 ≤ FrobeniusSq S A Y := by
  exact Finset.single_le_sum (fun b _ => sq_nonneg (A b - Y b)) (Finset.mem_univ a)

@[simp] theorem frobeniusSq_self (S : Shape) (A : Tensor S) :
    FrobeniusSq S A A = 0 := by simp [FrobeniusSq]

theorem frobeniusSq_eq_zero_iff (S : Shape) (A Y : Tensor S) :
    FrobeniusSq S A Y = 0 ↔ Y = A := by
  constructor
  · intro h
    funext a
    have hcoord := frobeniusSq_coordinate_le S A Y a
    rw [h] at hcoord
    nlinarith [sq_nonneg (A a - Y a)]
  · rintro rfl
    simp [FrobeniusSq]

/-- Every tensor with error no larger than zero's error lies in this compact box.
The bound uses only finite sums and real inequalities, not an optimizer premise. -/
theorem frobeniusSq_sublevel_subset_box (S : Shape) (A : Tensor S) :
    {Y : Tensor S | FrobeniusSq S A Y ≤ FrobeniusSq S A 0} ⊆
      Icc (fun a => A a - (FrobeniusSq S A 0 + 1))
        (fun a => A a + (FrobeniusSq S A 0 + 1)) := by
  intro Y hY
  constructor <;> intro a
  · have hcoord := (frobeniusSq_coordinate_le S A Y a).trans hY
    nlinarith [sq_nonneg (A a - Y a - (1 / 2 : ℝ))]
  · have hcoord := (frobeniusSq_coordinate_le S A Y a).trans hY
    nlinarith [sq_nonneg (A a - Y a + (1 / 2 : ℝ))]

/-- A genuine best feasible tensor exists for every rank tuple, including zero ranks. -/
theorem exists_feasible_minimizer (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, Feasible S r X ∧
      ∀ Y : Tensor S, Feasible S r Y → FrobeniusSq S A X ≤ FrobeniusSq S A Y := by
  let K : Set (Tensor S) :=
    {Y | Feasible S r Y} ∩ {Y | FrobeniusSq S A Y ≤ FrobeniusSq S A 0}
  have hclosed : IsClosed K :=
    (isClosed_feasible S r).inter (isClosed_le (continuous_frobeniusSq S A) continuous_const)
  have hcompact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset hclosed fun Y hY =>
      frobeniusSq_sublevel_subset_box S A hY.2
  have hzero : (0 : Tensor S) ∈ K := by
    exact ⟨feasible_zero S r, show FrobeniusSq S A 0 ≤ FrobeniusSq S A 0 from le_rfl⟩
  obtain ⟨X, hX, hmin⟩ := hcompact.exists_isMinOn ⟨0, hzero⟩
    (continuous_frobeniusSq S A).continuousOn
  refine ⟨X, hX.1, fun Y hY => ?_⟩
  by_cases hbound : FrobeniusSq S A Y ≤ FrobeniusSq S A 0
  · exact hmin ⟨hY, hbound⟩
  · exact (hmin hzero).trans (le_of_not_ge hbound)

/-- The original `sInf` is attained, rather than replaced by a chosen proxy. -/
theorem exists_optimum (S : Shape) (r : Ranks S) (A : Tensor S) :
    ∃ X : Tensor S, Feasible S r X ∧ Optimum S r A = FrobeniusSq S A X := by
  obtain ⟨X, hX, hmin⟩ := exists_feasible_minimizer S r A
  refine ⟨X, hX, ?_⟩
  exact IsLeast.csInf_eq ⟨⟨X, hX, rfl⟩, by
    rintro e ⟨Y, hY, rfl⟩
    exact hmin Y hY⟩

theorem optimum_nonneg (S : Shape) (r : Ranks S) (A : Tensor S) :
    0 ≤ Optimum S r A := by
  obtain ⟨X, _, hX⟩ := exists_optimum S r A
  rw [hX]
  exact frobeniusSq_nonneg S A X

theorem optimum_le_of_feasible (S : Shape) (r : Ranks S) (A Y : Tensor S)
    (hY : Feasible S r Y) : Optimum S r A ≤ FrobeniusSq S A Y := by
  apply csInf_le
  · exact ⟨0, by rintro e ⟨X, _, rfl⟩; exact frobeniusSq_nonneg S A X⟩
  · exact ⟨Y, hY, rfl⟩

theorem optimum_eq_zero_iff_feasible (S : Shape) (r : Ranks S) (A : Tensor S) :
    Optimum S r A = 0 ↔ Feasible S r A := by
  constructor
  · intro hzero
    obtain ⟨X, hX, herror⟩ := exists_optimum S r A
    have heq : X = A := (frobeniusSq_eq_zero_iff S A X).mp (herror.symm.trans hzero)
    exact heq ▸ hX
  · intro hA
    apply le_antisymm
    · simpa only [frobeniusSq_self] using optimum_le_of_feasible S r A A hA
    · exact optimum_nonneg S r A

#assert_trust kernel continuous_frobeniusSq
#assert_trust kernel frobeniusSq_nonneg
#assert_trust kernel frobeniusSq_coordinate_le
#assert_trust kernel frobeniusSq_self
#assert_trust kernel frobeniusSq_eq_zero_iff
#assert_trust kernel frobeniusSq_sublevel_subset_box
#assert_trust kernel exists_feasible_minimizer
#assert_trust kernel exists_optimum
#assert_trust kernel optimum_nonneg
#assert_trust kernel optimum_le_of_feasible
#assert_trust kernel optimum_eq_zero_iff_feasible
#print axioms exists_optimum
#print axioms optimum_eq_zero_iff_feasible
end NLA.Proofs.TR04
