/-
Pre-proof boundary only. No theorem asserting these propositions is declared.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology.
Original TR-06 mathematical proof attribution: Matthew J. Colbrook.
-/
import NLA.TR06.ClosedFibers

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.TR06.FiniteFiber

variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ} {r m : ℕ}

/-- Split the first actual summand, retain the other summands, and pad with zero.
The family is defined even without the length inequality; membership is claimed
below only when there is room for all m + 1 displayed summands. -/
def splitTuple (hm : 0 < m) (a : Fin m → Tensor 𝕜 d n) (t : 𝕜) :
    Fin r → Tensor 𝕜 d n := fun i =>
  if i.val = 0 then t • a ⟨0, hm⟩
  else if i.val = 1 then (1 - t) • a ⟨0, hm⟩
  else if h : i.val - 1 < m then a ⟨i.val - 1, h⟩
  else 0

/-- A cancelling pair of actual tensor summands, padded with zeros. -/
def cancelTuple (B : Tensor 𝕜 d n) (t : 𝕜) : Fin r → Tensor 𝕜 d n := fun i =>
  if i.val = 0 then t • B else if i.val = 1 then -(t • B) else 0

/-- The all-ones pure tensor; positive mode sizes provide an actual entry. -/
def unitTensor (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) : Tensor 𝕜 d n :=
  pureTensor (fun _ _ => 1)

/-- Nonempty complete fibers give an actual decomposition of length at most r,
without any positivity, identifiability, or finiteness assumption. -/
def RankBoundStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ)
    (A : Tensor 𝕜 d n),
    (closedAdditionFiber r A).Nonempty →
    ∃ m : ℕ, m ≤ r ∧ ∃ a : Fin m → Tensor 𝕜 d n, Decomposes a A

/-- Every positive shorter decomposition supplies a scalar-indexed injective
family in the full length-r fiber. No nonzero entries are excluded from it. -/
def SplitFamilyStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r m : ℕ)
    (_hd : 0 < d) (hm : 0 < m), m < r →
    ∀ (A : Tensor 𝕜 d n) (a : Fin m → Tensor 𝕜 d n), Decomposes a A →
      Function.Injective (splitTuple (r := r) hm a) ∧
      ∀ t : 𝕜, splitTuple (r := r) hm a t ∈ closedAdditionFiber r A

/-- Positive mode sizes make the displayed pure tensor genuinely nonzero;
this statement also includes the empty mode set d = 0. -/
def UnitTensorStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ),
    (∀ j, 0 < n j) → RankOne (unitTensor 𝕜 d n)

/-- With two available positions, any genuine rank-one tensor gives infinitely
many distinct cancelling tuples in the complete fiber over zero. -/
def CancelFamilyStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ),
    0 < d → 2 ≤ r → ∀ B : Tensor 𝕜 d n, RankOne B →
      Function.Injective (cancelTuple (r := r) B) ∧
      ∀ t : 𝕜, cancelTuple (r := r) B t ∈ closedAdditionFiber r (0 : Tensor 𝕜 d n)

/-- Any shorter decomposition, including the empty decomposition of zero,
forces the full closed-product fiber to be genuinely infinite as a set. -/
def ShorterInfiniteStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ),
    0 < d → (∀ j, 0 < n j) → 2 ≤ r →
    ∀ (A : Tensor 𝕜 d n) (m : ℕ), m < r →
      (∃ a : Fin m → Tensor 𝕜 d n, Decomposes a A) →
      (closedAdditionFiber r A).Infinite

/-- Finite NONEMPTY complete fibers force exact rank under the stated format
conditions. No identifiability or Nat.card hypothesis is used. -/
def ExactRankStatement : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) (n : Fin d → ℕ) (r : ℕ),
    0 < d → (∀ j, 0 < n j) → 2 ≤ r →
    ∀ A : Tensor 𝕜 d n,
      (closedAdditionFiber r A).Finite → (closedAdditionFiber r A).Nonempty →
      ExactRank r A

#check RankBoundStatement
#check SplitFamilyStatement
#check UnitTensorStatement
#check CancelFamilyStatement
#check ShorterInfiniteStatement
#check ExactRankStatement
end NLA.TR06.FiniteFiber
