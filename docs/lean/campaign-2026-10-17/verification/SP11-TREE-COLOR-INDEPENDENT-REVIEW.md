# SP-11 tree/color supports — independent review

Reviewer: `/root/lean_verification`, Codex AI agent, 18 October 2026.
**Verdict: approve the six source modules below as support lemmas.** I did not
implement those six modules. This is separate from the preserved seven- and
eleven-module historical reviews.

| Module | Reviewed SHA-256 |
| --- | --- |
| `DoubleRootGarden` | `1d72a6c5ac708ecbf6b8b7e78e60d9e9574b0b0de82773fccf75337308dca2cc` |
| `DoubleHistogramWeights` | `b930e37ee7b17e0c4282b0be0d1162df133d19620a49995cac6e056482d5aecb` |
| `ColorBounds` | `0f3e13a608d409542a5548571dbf71c507f034460edcaf282db12bead71ee3d8` |
| `ColorWeights` | `fa45af958015992d5a01ad224e4318ee7e65b20e7a8390fb5c3227f2ee8dbf93` |
| `ColoringExt` | `f6780e9b7628c94cd9d3e43d1166c8f1b741b766a859c29f0b0715343c20185d` |
| `OccurrenceParent` | `0abebc9b5f6e8235ae0d845391a64254f05e5d6dc5443debd5d043739542ce1d` |

`DoubleRootGarden` proves the literal finite expansion of the actual recursive
gardens. `DoubleColoring` has one shared cap color and both families of colors
below it. The cap is a conduit, not an extra node. `Occurrence` enumerates every
actual node, and variables are exactly `Sigma vertex CoordinateSubset`.
Repeated occurrences of a vertex use the same coefficient family and their
exponents add with multiplicity. The final Gram expansion is obtained by the
already proved equality between `lssGarden.value` and `polynomialLSS`. No
distinctness of occurrence variables or monomials is assumed. The finite
product lemma could also reuse Mathlib's monomial-product API; the existing
short induction is correct and is not a review blocker.

`ColorWeights` reads the sum of coordinate values from an injective local
color tuple: sorting changes only its permutation. The class weight is zero
for other original vertex labels. `DoubleHistogramWeights` then applies the
genuine natural-linear combination to the shared exponent, retaining every
occurrence in the selected vertex class. A nonzero real paired sign proves
local tuple injectivity. Equal exponents imply equal class sums; pointwise
equality follows only when the displayed one-sided occurrence bounds are
provided. Those graph-specific bounds remain explicit premises. This audit
uses the restored source hash in the table and freshly recompiles it; it does
not rely on the stale object from the intervening failed cleanup revision.

`ColorBounds` obtains lower bounds by excluding every smaller color using
injectivity and actual covering slots. The empty-prefix and zero-arity cases
are included. `ColoringExt` recursively recovers all color choices from actual
node outputs, including the paired coloring's cap and both subtrees.
`OccurrenceParent` constructs an actual parent and child slot for each
nonroot occurrence, preserving its dependent path; no parent oracle is assumed.

The fresh audit passed all **28 Lean commands**: 25 proof-source modules in the
local import closure, two unchanged statement/infrastructure modules, and one
separate consumer. It audited **209 explicit named declarations**, including
**137 theorem/lemma constants**. Each proof declaration must have Lean's
`thmInfo` kind; each declaration is checked with `#assert_trust kernel` and
`#print axioms`. Generated proof helpers are covered transitively by these
checks. The consumer resolves nested namespaces, including `GardenTree`.
Only the standard foundational axioms occur; no `sorryAx`, native proof axiom,
or unknown axiom is accepted. All ten dependency revision and tracked-source
cleanliness checks passed before and after; all frozen project source bytes
were unchanged after execution.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-tree-color-support.py
```

Exact frozen source, the generated consumer, command outputs, dependency
checks, compiler identity, declaration names and machine-readable result are
retained in `sp11-tree-color-support-review/`. The build used a fresh private
source/output prefix and excluded the campaign's existing `.lake` output.
Pinned dependency objects were reused, rather than rebuilt from scratch.

This runtime closure also includes my own `MonomialProducts`,
`PriorListStructure`, `LSSLabelBounds`, `PriorInsertion`, and `AugmentedColors`.
For those files this report claims reproducible runtime evidence only;
independent source reviews are assigned to other agents. In particular,
`PriorInsertion` was audited at
`db953976c47fed4c38cfcb3c00a2629fd914d7271a057dfd3a9e688ae0c7cff4`
and `AugmentedColors` at
`856bda135fb47417912e4ab5da092e6e4e9e44ef8c559b33ffb0202eeb5ac453`.

This is local macOS Lean elaboration and LeanCert kernel-trust evidence. It is
not a Linux Comparator run or a proof of the full frozen SP-11 `Target`.
Canonical coloring uniqueness and discharge of all blocker/tie obligations
remain outside this snapshot.
