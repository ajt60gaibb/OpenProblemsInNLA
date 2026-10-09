# TR-21 source check by later Lean author

**Source check: no mismatch found.** The specification was authored by
`/root/inventory_review`, and this comparison preceded the Lean code.
Because `/root` subsequently authored the Lean boundary, this report is
**not counted** as one of the two independent specification approvals in
the reviewed statement gate. It is not a proof or Lean-boundary review.

## Reviewed inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`.

| Input | SHA-256 |
| --- | --- |
| `tensor-computations/TR-21/README.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/ORIGINAL.md` | `645fab1674f258c7d120c880118f296ab2066b25ddd257e55bd5b1ad2e84e764` |
| `docs/lean/statements/TR-21/NUMERICAL_TARGETS.md` | `8f8266b6106deb2648aacc0ffc6f50801d49c076d5c4638897d5d6606a39f0f4` |
| `references/haidary-resolutions-2026-09-30/TR-21-Seginer-comparison-revised.tex` | `7beed83c0e2d8b9fc2b02c8203cb6d94317270044b5e14dfb9e1ecb4a1456393` |

The original copy is byte-identical to the canonical README. The revised
manuscript's Theorem 1.1, lines 56–87, has the injective norm and fiber
definition exactly as specified.

The specification retains every order `r≥3`, all rectangular finite formats
with each `n_j≥2`, and every iid real mean-zero law with a finite first
absolute moment. The law may depend on the dimensions. Modeling the joint
array by the finite product of the common entry measure has the same law as
any iid realization, so it preserves both expectations without imposing
a density or higher moment. The zero law remains admissible.

The injective norm takes a supremum over all tuples of real Euclidean unit
vectors, with absolute value around the complete multilinear contraction.
The fiber maximum is inside each expectation, and the mode maximum is outside
the expectations, exactly as the source emphasizes. The finite product-index
and off-mode assignment model does not flatten or restrict tensors.

The principal target has one pair of positive finite constants for each
fixed order, selected before all dimensions and laws. The source's stronger
lower coefficient one is retained as a companion assertion. No numerical
approximation or variance normalization is introduced. I found no substantive
source mismatch. The actual Lean boundary and imported mathematical meaning
still require separate independent review.
