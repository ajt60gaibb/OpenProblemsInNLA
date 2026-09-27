import Init

namespace MD06

set_option autoImplicit false

/-- Minimal ordered scalar interface.  The intended instance is the real numbers;
this interface keeps the Challenge independent of any unpinned analysis library. -/
structure ScalarModel where
  carrier : Type
  zero : carrier
  one : carrier
  inv32 : carrier
  inv320 : carrier
  lt : carrier → carrier → Prop
  le : carrier → carrier → Prop
  mul : carrier → carrier → carrier

/-- Semantic interface for the finite random cubic graph model.  Every field is a
contract: it is not an assumption imported by `Solution.lean`. -/
structure Semantics where
  scalar : ScalarModel
  Graph : Nat → Type
  Phase : Nat → Type
  Edge : {n : Nat} → Graph n → Type
  cubicSimple : {n : Nat} → Graph n → Prop
  uniformProbability : (n : Nat) → (Graph n → Prop) → scalar.carrier
  limitZeroEven : (Nat → scalar.carrier) → Prop
  limitOneEven : (Nat → scalar.carrier) → Prop
  phase : {n : Nat} → Graph n → Phase n → Prop
  localMinimum : {n : Nat} → Graph n → Phase n → Prop
  critical : {n : Nat} → Graph n → Phase n → Prop
  synchronized : {n : Nat} → Graph n → Phase n → Prop
  edgeCosine : {n : Nat} → (G : Graph n) → Edge G → Phase n → scalar.carrier
  hessianQuadratic : {n : Nat} → (G : Graph n) → Phase n → Phase n → scalar.carrier
  meanZero : {n : Nat} → Graph n → Phase n → Prop
  normSq : {n : Nat} → Phase n → scalar.carrier
  edgePositive : {n : Nat} → (G : Graph n) → Edge G → Phase n → Prop

/-- The event in the paper's negative resolution: every local minimum is
synchronized.  The graph quantifier is restricted to simple cubic graphs. -/
def everyLocalMinimumSynchronized (S : Semantics) {n : Nat} (G : S.Graph n) : Prop :=
  S.cubicSimple G → ∀ θ, S.localMinimum G θ → S.synchronized G θ

/-- The event supplied by the stronger part of Theorem MD-06. -/
def hasStableNonsynchronizedCritical (S : Semantics) {n : Nat} (G : S.Graph n) : Prop :=
  S.cubicSimple G ∧
  ∃ θ,
    S.critical G θ ∧
    (¬ S.synchronized G θ) ∧
    (∀ e : S.Edge G, S.scalar.lt S.scalar.inv32 (S.edgeCosine G e θ)) ∧
    (∀ z, S.meanZero G z →
      S.scalar.le (S.scalar.mul S.scalar.inv320 (S.normSq z)) (S.hessianQuadratic G θ z))

/-- Even size convention: the random graph at index `k` has `2*(k+2)` vertices,
so all represented sizes are even and at least four. -/
def size (k : Nat) : Nat := 2 * (k + 2)

def goodProbability (S : Semantics) (k : Nat) : S.scalar.carrier :=
  S.uniformProbability (size k) (fun G : S.Graph (size k) => everyLocalMinimumSynchronized S G)

def strongProbability (S : Semantics) (k : Nat) : S.scalar.carrier :=
  S.uniformProbability (size k) (fun G : S.Graph (size k) => hasStableNonsynchronizedCritical S G)

/-- Full negative resolution, expressed along the even subsequence. -/
def MainClaim (S : Semantics) : Prop :=
  S.limitZeroEven (goodProbability S)

/-- The “with probability tending to one” strengthening. -/
def StrongClaim (S : Semantics) : Prop :=
  S.limitOneEven (strongProbability S)

end MD06




