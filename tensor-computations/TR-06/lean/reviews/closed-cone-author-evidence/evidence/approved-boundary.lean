/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
Statement proposal only: no cone polynomial characterization is yet proved.
-/
import NLA.TR06.ClosedFibers
import Mathlib.Topology.Algebra.MvPolynomial

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
namespace NLA.TR06

variable {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ}

/-- A genuine homogeneous polynomial expression of degree at most d for positive d. The whole
finite family ranges over all tensor pivot/target coordinate pairs. -/
def rankOnePivotPolynomial (𝕜 : Type*) [RCLike 𝕜] {d : ℕ} {n : Fin d → ℕ}
    (p q : TensorIndex d n) : MvPolynomial (TensorIndex d n) 𝕜 :=
  MvPolynomial.X q * MvPolynomial.X p ^ (d - 1) -
    ∏ j : Fin d, MvPolynomial.X (Function.update p j (q j))

-- Proposed theorem: pureTensor_pivot_identity. Includes zero-valued pivots;
-- the forward proof will use products directly, without dividing by a pivot.
#check (∀ (_hd : 0 < d) (u : (j : Fin d) → Fin (n j) → 𝕜)
    (p q : TensorIndex d n),
  pureTensor u q * pureTensor u p ^ (d - 1) =
    ∏ j : Fin d, pureTensor u (Function.update p j (q j)) : Prop)

-- Proposed theorem: rankAtMostOne_iff_pivot_equations.
#check (∀ (_hd : 0 < d) (A : Tensor 𝕜 d n),
  rankAtMostOne A ↔ ∀ p q : TensorIndex d n,
    A q * A p ^ (d - 1) = ∏ j : Fin d, A (Function.update p j (q j)) : Prop)

-- Proposed theorem: rankAtMostOne_iff_eval_pivotPolynomial_eq_zero.
#check (∀ (_hd : 0 < d) (A : Tensor 𝕜 d n),
  rankAtMostOne A ↔ ∀ p q : TensorIndex d n,
    MvPolynomial.eval (fun v => A v) (rankOnePivotPolynomial 𝕜 p q) = 0 : Prop)

-- Proposed theorem: range_pureTensor_eq_rankAtMostOne.
-- This records exact parametrization, useful for a later irreducibility proof.
#check (∀ (_hd : 0 < d),
  Set.range (pureTensor : ((j : Fin d) → Fin (n j) → 𝕜) → Tensor 𝕜 d n) =
    {A : Tensor 𝕜 d n | rankAtMostOne A} : Prop)

-- Proposed theorem: isClosed_rankAtMostOne.
#check (∀ (_hd : 0 < d), IsClosed {A : Tensor 𝕜 d n | rankAtMostOne A} : Prop)

-- Proposed theorem: isClosed_closedRankOneProduct.
#check (∀ (_hd : 0 < d) (r : ℕ), IsClosed (closedRankOneProduct 𝕜 d n r) : Prop)

-- Proposed theorem: isClosed_closedAdditionFiber.
#check (∀ (_hd : 0 < d) (r : ℕ) (A : Tensor 𝕜 d n),
  IsClosed (closedAdditionFiber r A) : Prop)

end NLA.TR06
