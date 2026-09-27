# Reusable-API and mathematical-compression check — 27 September 2026

This audit covers the library-style refactor after the subject-based
reorganisation. The earlier audit directories and source manifests are retained
as historical snapshots; their hashes are not expected to match changed proof bodies.

## Scope

- General density-mixture theorems in `MeasureTheory.Measure`, with arbitrary
  measurable spaces and an extended-nonnegative core statement.
- Event-local and global-second-moment Cauchy–Schwarz lemmas in `MeasureTheory`.
- A deterministic coordinate-invariance API, including nonunitary diagonal scaling.
- Both sampler bridges use the common mixture result. The reference and unitary
  invariance proofs use the common deterministic API. Joint measurability of
  the unitary action is shared rather than reproved.
- Gaussian product, splitting, conjugation, and orthonormal/unitary laws are
  grouped with their foundational proofs. The overlap and sphere arguments share
  one coordinate-splitting law.
- Scalar Gaussian small-ball estimates are independent of the planted phase
  argument, including zero variance. Both projection bounds use a shared
  measure-preserving projection identity.
- The Haar-corner law uses mathlib's group shear. Hermitian determinant formulas
  share a spectral identity, and paper-specific scalar bounds are separated from
  overlap geometry. The overlap spectrum file uses named sections.
- A further consolidation absorbs 45 short modules into 32 related files,
  reducing 157 modules to 112. Named sections preserve local scopes, and the
  module map redirects both historical flat and retired subject imports.
- Six interval/circle proofs share two applications of mathlib's phase covering
  map. Row dependence, unit-vector existence, and the cone integral-square bound
  now use existing span, norm, and variance results.
- Exact midpoint cancellation replaces the two-term quadratic remainder bound,
  improving the nonlinear constant from 2048 to 1024. Factoring the even exponential
  as `exp(-A) cosh(B)` improves its scalar remainder constant from 5000 to 304.
  The downstream application bounds and final statements are retained.
- Square-root scale invariance and a direct quadratic cosine estimate replace
  longer elementary arguments. Four superseded auxiliary lemmas are removed;
  the two new helpers are used by the final proof. No modules or supporting files
  are added. See [LIBRARY_STYLE.md](../../LIBRARY_STYLE.md) for exact theorem-level
  changes and remaining library-quality work.
- A final simplification pass removes another 309 source lines from four modules,
  without adding library declarations or files. Concavity and the quadratic cosine
  bound shorten the inverse-cosine argument; saturation removes the band-clamping
  API. The affine reduction uses the cosine addition formula. Norm comparisons
  reuse mathlib, and the perturbation bounds reuse their existing nonnegative
  factors. Ten private helpers are retired. The unrestricted arccosine corollary
  is stronger; all phase probability bounds and final constants are unchanged.

- The pre-PR readability pass registers canonical simp/fun-prop rules and the
  Gaussian probability instance, generalises and relocates the used product-density
  identity, removes unnecessary assumptions, and shortens measure and arithmetic
  proofs. Local instance syntax and arithmetic tactics are modernised. Redundant
  imports and all direct umbrella `Mathlib.Tactic` imports are removed from `NLA`.
  No library modules are added. See `LIBRARY_STYLE.md` for the scope and limits.

The pre-PR pass changes imports and proof bodies in `Definitions.lean`,
`Probability.lean`, and `SourceParameters.lean`, but preserves their mathematical
definitions and assumptions. `Solution.lean`, `lakefile.toml`, and `lean-toolchain`
are unchanged. During PR preparation, `Challenge.lean`
and `comparator.json` additionally select the already-proved original limit,
alongside the unchanged quantitative target and supporting targets. The stale
partial-checkpoint metadata in `formalization.yaml` is updated to the completed
local scope. The canonical problem ID, target, status, and dependency pins have
not changed. The original ZIP and unrelated problem directories were not modified.

## Reproduction

Host: macOS arm64. Lean 4.33.1, mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

From the FR-05 Lean project:

```sh
bash verification/library-cleanup/check.sh
shasum -a 256 -c verification/library-cleanup/source-sha256.txt
```

The script checks all library modules and both repository entry points, then:

- enables `linter.mathlibStandardSet` with warnings treated as errors for the
  seven curated API modules listed in `check.sh`;
- checks `Api.lean`, including rectangular transport, empty Gaussian blocks,
  singular Gram matrices, zero variance, arbitrary finite spectral indices, and
  the smallest Haar-corner dimension, arbitrary measurable phase events, the
  strengthened constants 304 and 1024, and the zero-odd-term exponential case;
  also checks saturated arccosine endpoints, a zero-width band outside the cosine
  range, a zero-amplitude affine polynomial, and an empty coordinate norm bound;
  checks the registered Gaussian probability instance, simp/fun-prop rules,
  the product-density theorem without separate measurability or finite-density assumptions,
  and the lower singular-value predicate without decidable equality on the index type;
  runs declaration linters including
  theorem documentation on the curated modules and original definitions;
- checks the exact final targets and prints transitive axioms in `Inspect.lean`;
- traverses the final proof's project-local dependencies to check that all 18
  substantive new API lemmas from the cleanup passes are actually used
  (the two compatibility aliases are excluded);
- rejects proof placeholders, custom axiom declarations, native decision proofs,
  and unsafe declarations in `NLA/` and `Solution.lean`.

`check.log` records the run. The full build and API checks pass. The applicable
syntax-linter checks pass without warnings. This is not
a claim that every mathlib style check runs downstream: in particular, the
header linter skips modules absent from a library-root import file, and this
project uses Lake globs rather than `NLA.lean`.

All 39 declarations in `Inspect.lean`, including the original final theorem,
use only `propext`, `Classical.choice`, and `Quot.sound`. The four intentional
`Challenge.lean` placeholders remain isolated and are not solution dependencies.
Older application modules still produce existing linter suggestions; this pass
does not claim the full library is lint-clean or ready for mathlib acceptance.

`source-sha256.txt` binds this record to the current proof sources, statement
entry points, dependency configuration, and regression-check sources. This is
local verification, not independent statement review or the repository's isolated
non-root Linux Comparator/kernel check.
