# RA-03 Lean formalization

This project proves a negative answer to the [original randomized LU bound](../README.md). For the actual complex matrix `A=[[2,1],[1,2]]`, one pivot drawn by the prescribed conditional entry rule has expected squared Frobenius error `18/5`, while its actual rank-one singular-value tail is `1`. Thus the proposed factor `2^k` fails at `k=1`.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Original mathematical counterexample and informal proof: **Matthew J. Colbrook**. [formalization.yaml](formalization.yaml) records the sources, roles and automation.

The complete proof builds under pinned Lean 4.33.1. Two independent final proof referees re-elaborated Definitions, Proof and Solution using fresh local proof artifacts. All eight audited internal results and four exports pass `#assert_trust kernel` and report exactly `propext`, `Classical.choice`, and `Quot.sound`. Authoritative Linux Comparator remains pending; the canonical status is still `Solved`.

## Reviewed statements and proof

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), [Definitions.lean](NLA/RA03/Definitions.lean) and [Challenge.lean](Challenge.lean) were written, typechecked and approved by two independent statement referees before implementation. The generic process uses the actual joint conditional entry probabilities, the canonical cross update, and zero absorption. The finite expectation sums every complete history with its product of conditional probabilities.

[Solution.lean](Solution.lean) exports:

- `NLA.RA03.frobeniusSq_eq_norm_sq`: the explicit sum is the genuine squared Frobenius norm.
- `NLA.RA03.process_isProbability`: all conditional and complete-history masses are nonnegative and sum to one, in every dimension and at every length.
- `NLA.RA03.counterexample`: the actual witness, Gram identity, ordered singular values `3,1`, four derived pivot masses/errors, expectation `18/5`, tail `1` and strict violation.
- `NLA.RA03.not_squaredErrorConjecture`: negation of the complete original universal bound.

[Proof.lean](NLA/RA03/Proof.lean) normalizes generic histories and derives the expectation recurrence by induction and a proved finite equivalence. It identifies the actual Euclidean adjoint composition with the Gram matrix and uses its characteristic polynomial to obtain Mathlib's ordered eigenvalues and singular values. Exact arithmetic evaluates four updates; one explicit kernel LeanCert point certificate proves the final strict gap. No arbitrary-history enumeration, numerical spectral approximation or interval subdivision is needed. The source's stronger sharp all-rank `4^r` theorem and Cholesky results are outside the advertised formal scope.

## Reproduction and evidence

From this directory, the development build is:

```bash
lake exe cache get
lake build Solution
```

All dependency revisions are fixed in `lake-manifest.json`. The four deliberate Challenge placeholders belong to a separate target environment and are never imported by Solution. Frozen source records, build logs and referee reports are in [reviews/](reviews/); additional independent re-elaboration logs are in [verification/](verification/).

From the repository root on the supported non-root Linux host, use the [shared harness prerequisites](../../../tools/lean/HARNESS.md) and:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py randomized-and-low-rank-approximation/RA-03/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-03/lean /absolute/path/to/nla-lean-tools
```

The project must be committed and unchanged. The harness applies the real Linux sandbox, positive and negative controls, and the [four-export Comparator configuration](comparator.json) to fresh inputs. Formal identity and kernel acceptance supplement the independent English-to-Lean reviews. A successful Linux result and immutable proof links must be retained before catalog promotion.
