# Review scope and remaining gate

All reports are AI-agent reviews. They do not assert human peer review or
endorsement by the original authors.

Before proof implementation, two agents independently reviewed the canonical
problem, complete source manuscript, definitions, challenge and numerical
targets. The boundary compiled, and both approved its exact frozen bytes:
[statement review 1](statement-1.md) and [statement review 2](statement-2.md).
Those agents subsequently authored separate proof modules; their pre-proof
independence is specific to that earlier phase.

The completed proof has component reviews with explicit authorship exclusions:

- [Upper-bound review](upper-1.md): the lower-witness author independently
  reviewed the Prony reconstruction and full Vandermonde upper bound.
- [Koszul review](koszul-cross-review.md): the matrix-certificate author
  independently reviewed the Koszul map and explicit lower-rank witness.
- [Matrix, limit and rank-comparison review](cross-module-tensors.md): the
  upper-bound author independently reviewed these other authors’ modules.
- [Assembly review](assembly-cross-review.md): the lower-witness author
  independently reviewed the separate lower-bound assembly and final theorem.

Each report binds its scope to file hashes and identifies the checks actually
run. No reviewer’s own module is counted as independently reviewed by that
reviewer. These reports provide cross-review of the implementation, **not two
independent reviews of the entire final formalization**. The latter gate from
`docs/lean/REVIEW.md` remains pending in this draft, as does the authoritative
Linux checker. Consequently the canonical problem remains `Solved`.
