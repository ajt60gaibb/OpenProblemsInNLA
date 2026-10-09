# TR-13 Lean formalization

This project proves the **entire original TR-13 target**, with the stronger
exact value of all five ranks. For every odd `m ≥ 5` and `n ≥ 2`,
`NLA.TR13.generic_rank_equality` supplies a nonzero polynomial and a point where
it is nonzero; throughout that principal Zariski-open set, the ordinary,
symmetric, ordinary-border, symmetric-border and Vandermonde ranks of the
Hankel tensor equal `ceil((m(n−1)+1)/2)`.

This is a draft contribution. The canonical status remains **Solved** while
authoritative Linux Comparator verification and full independent final review
are pending. Local compilation is not represented as that isolated check.

## Reproduce

The project pins Lean **4.33.1** and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`; the committed Lake manifest also pins
every transitive package. With the pinned toolchain available, run here:

```sh
lake exe cache get
lake build Solution Challenge
lake env lean Check.lean
```

Only `Challenge.lean`, the independent comparison statement, has a deliberate
placeholder. `Solution.lean` never imports it. The target proof and its
dependencies contain no placeholders, custom axioms or native decision trust.

From a committed repository checkout on the supported non-root Linux host:

```sh
python3 tools/lean/validate_manifest.py tensor-computations/TR-13/lean
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh tensor-computations/TR-13/lean /tmp/nla-lean-tools
```

The existing GitHub workflow selects this project and runs those checks.
`comparator.json` compares the complete theorem and permits only `propext`,
`Classical.choice` and `Quot.sound`, with no replaceable definitions.

## Mathematical correspondence

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) records source hashes, every domain
and convention, and the frozen full statement. [Definitions.lean](NLA/TR13/Definitions.lean)
uses actual coordinate tensors and explicit decompositions. In particular:

- Ordinary border rank uses arbitrary tensor sequences converging entrywise;
  the approximating tensors need not be symmetric or Hankel.
- Vandermonde vectors include homogeneous nodes at infinity.
- Every least-rank set is nonempty on the advertised open set because the
  proof constructs an actual Vandermonde decomposition.
- No witness, interpolation, separability or genericity theorem is assumed.
  The required nonzero polynomials and their witnesses are proved.

The [Prony modules](NLA/TR13/Prony.lean) reconstruct moments from a separable
recurrence, with a polynomial determinant/resultant condition and an explicit
periodic witness. This replaces the manuscript’s dominance/constructibility
argument. [Upper.lean](NLA/TR13/Upper.lean) converts those moments into the actual
Vandermonde tensor decomposition.

[Compression.lean](NLA/TR13/Compression.lean) preserves arbitrary pure-tensor
decompositions. The [Koszul witness](NLA/TR13/KoszulWitness.lean) proves the
required rank using explicit shifts and a kernel-dimension bound, including
`s = 0` for binary tensors. [MatrixCertificate.lean](NLA/TR13/MatrixCertificate.lean)
turns a witness rank into a nonzero determinant polynomial and proves the
rank bound survives arbitrary entrywise limits. [Lower.lean](NLA/TR13/Lower.lean)
therefore proves the ordinary-border lower bound. Finally,
[RankComparison.lean](NLA/TR13/RankComparison.lean) and
[Solution.lean](Solution.lean) combine the two nonempty open conditions and
establish all five exact ranks.

## Attribution and verification record

The conjecture and prior Hankel theory are credited to Jiawang Nie and Ke Ye.
The repository’s mathematical resolution is credited to Matthew J. Colbrook,
Department of Applied Mathematics and Theoretical Physics, University of
Cambridge. The new Lean implementation and its alternative Prony argument were
developed with OpenAI Codex agents. No source-author or human endorsement is
claimed. New code is provided under [Apache 2.0](LICENSE).

[reviews/README.md](reviews/README.md) distinguishes independent pre-proof
statement reviews from subsequent scoped component reviews and identifies the
remaining independent-review gate. [verification/README.md](verification/README.md)
records actual local commands, source hashes and limitations.
