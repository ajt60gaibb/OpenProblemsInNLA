# SP-14: finite-support density for the completed inverse

**Status:** frozen exact mathematical/indexing pre-implementation contract for independent review. A candidate Lean source was drafted and direct-checked prematurely; it remains unimported, uncommitted, and unaccepted pending this pre-review and a separate final source/kernel audit. No completed inverse is asserted here.

## Source locks and scope

The frozen `lean-statements/NLA/Statements/SP14.lean` SHA-256 is `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`. Canonical `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` SHA-256 is `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`. The approved completion goal is `ENDPOINT_INVERSE_PARSEVAL_COMPLETION_PRE_REVIEW.md` SHA-256 `cd170cdb4d4fd1070edfc9185a0475432e8a3db9e83a9d794cb58b08ce6dd4e9`.

The literal carrier `SobolevCoeff r := lp (fun _ : ℕ => ℂ) 2` and coordinate norm are in `WeightedSobolevPhysical.lean` SHA-256 `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109`. The literal first-`N` truncation is in `WeightedSobolevOperators.lean` SHA-256 `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1`; `tendsto_sobolevTruncation` is in `EndpointNegativeTruncation.lean` SHA-256 `7454b7819bae6d5292bcaf53b482371adda48b7f8d55640395e542d08db47c06`.

## Exact public signatures

```lean
def endpointFiniteSupport (r : ℝ) : Submodule ℂ (SobolevCoeff r) where
  carrier := {y | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → y n = 0}
  -- exact zero/add/smul submodule laws

theorem endpointFiniteSupport_dense (r : ℝ) :
    DenseRange (endpointFiniteSupport r).subtype
```

The carrier uses **weighted coordinates** `y n`, not physical coefficients and not an abstract finite-dimensional substitute. An element belongs exactly when all coordinates at indices `n ≥ N` vanish for some natural `N`. The `N=0` case contains the zero vector. If `y` and `z` are supported below `M` and `N`, then `y+z` is supported below `max M N`; any complex scalar multiple of a vector supported below `N` remains there.

For every `y : SobolevCoeff r`, the actual `sobolevTruncation r N y` belongs to this carrier because its coordinates at `n ≥ N` are zero. The audited theorem `tendsto_sobolevTruncation r y` gives convergence of those elements to `y` in the literal `lp` norm. Therefore the range of the exact submodule inclusion is dense. This holds for **every real `r`**, including `r=0`, with no summability or smoothness assumption beyond membership in `SobolevCoeff r`.

Small exact checks: for `N=0`, the truncation is zero and lies in the submodule; for a vector supported at indices `0,1,2`, `N=3` is a witness and all later truncations equal that vector. These checks concern only support and density, not inverse coefficient values. The theorem is needed for pinned Mathlib `LinearMap.extendOfNorm` to construct the approved `endpointInverseL2`; it does not itself claim the completed map, its bound, or the frozen negative `Target`.
