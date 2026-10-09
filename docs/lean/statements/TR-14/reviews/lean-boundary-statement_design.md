# TR-14: independent Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Date: 2026-09-28. Verdict: **approve**. No mathematical correction requested.

## Source and meaning checks

1. HankelIndex has value the sum of zero-based coordinates, with a checked finite bound m*(n-1)+1. Its proof uses each coordinate <n and the full finite sum, not a truncation or modulo operation.

2. Hankel reads exactly h at that index. For m>=3,n>=2 this is the canonical one-based index sum minus m, covering every complex h including the zero tensor and all exceptional data.

3. OrdinaryWidth quantifies a separate complex vector for every term and mode. SymmetricWidth quantifies coefficients and one repeated vector per term. Products are ordinary complex multiplication with no conjugation, and both equalities hold at every coordinate tuple.

4. Target quantifies all natural r including zero. Empty sums give zero and zero-term padding makes the exact-width predicates upward closed. Thus agreement for every r is equivalent to equality of their least widths, using their nonempty finite decomposition sets.

5. The finite minima exist: coordinate basis terms decompose ordinary tensors; for Hankel tensors the D+1 distinct-parameter Vandermonde expansion, D=m(n-1), gives symmetric vectors (1,t,...,t^(n-1)) and coefficients solving every h_s. This establishes equivalence to rank equality without restricting the factors quantified by the target.

6. A symmetric term is an ordinary term by absorbing its coefficient into one mode, allowed since m>=3. No border rank, genericity, Vandermonde-only factor restriction, rational-data restriction, or stronger explicit rank formula replaces the canonical exact-rank statement.

7. Live and frozen mathematical bodies agree exactly after the documented namespace substitution and leading comment. Canonical source and ORIGINAL snapshot are byte-identical. All local review_inputs and immutable pins are hash-bound below.

8. Infrastructure.lean was read in full. It checks safe definition, closed type Prop and permitted axiom closure. It supplies no mathematical hypothesis; kernel trust assertions do not assert target truth.

## Bound review inputs

- docs/lean/statements/TR-14/NUMERICAL_TARGETS.md: 6c50aa83745fc3d096e08b476fb08a841ffc0fefb2cdd58511f924c49f09da17
- docs/lean/statements/TR-14/ORIGINAL.md: a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/TR14.lean: 515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9
- lean-statements/Reviewed/TR14.lean: 9990f933adf8a8593f6a1fcc70aeeaeed8abdfe05e7738bd5b538e719ad9c356
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- tensor-computations/TR-14/README.md: a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86

## Imported source inspected

The complex finite-coordinate formulas are explicit; no imported tensor rank or tensor decomposition predicate is used.

## Development evidence inspected

{
  "path": "/private/tmp/nla-statements-development/TR14.log",
  "sha256": "d30169f772b5e0c8f66d3c6670557774e164e172057269bd9ec874bfcb8d5960",
  "observed": "Author-generated development log reports only propext, Classical.choice and Quot.sound for Target. Reviewer read the log but did not execute the compilation."
}

## Limits

Independent Lean-boundary source/fidelity review. Pinned imported meanings and author-generated axiom logs were inspected; this reviewer did not run Lean or Comparator. This certifies neither the truth of the catalog proposition nor a new audit of its cited informal proof. Authoritative build and Linux Comparator gates remain separate.
