# MI-19 Lean formalization

This project proves the negative answer to the [original MI-19 question](../README.md). At an actual complex Hermitian PSD Gram matrix, `q=7/8` and the interior singleton `{2}` in the paper's indexing, the full q-permanent minus its subset-preserving sum equals `−3235575/16384`. This strict counterexample refutes the complete universal conjecture.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Original mathematical counterexample and informal proof: **Matthew J. Colbrook**. See [formalization.yaml](formalization.yaml) for roles, sources and automation disclosure.

The complete proof builds under pinned Lean 4.33.1. Both independent final proof referees re-elaborated the source successfully. All audited internal results and public exports pass `#assert_trust kernel` and report exactly `propext`, `Classical.choice`, and `Quot.sound`. Authoritative Linux Comparator remains pending, so this project does not yet promote the catalog status.

## Reviewed statements and proof

[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), [Definitions.lean](NLA/MI19/Definitions.lean) and [Challenge.lean](Challenge.lean) were written, typechecked and independently reviewed before proof implementation. [Proof.lean](NLA/MI19/Proof.lean) proves the actual complex Gram identity and both sums through Mathlib's checked finite permutation equivalence. It counts inversions in the full original ordering and filters by setwise preservation; the restricted expression is not replaced by a product of smaller permanents.

[Solution.lean](Solution.lean) exports:

- `NLA.MI19.counterexample`: all original hypotheses, the genuine Gram/PSD witness, zero imaginary parts, the exact gap and strict violation.
- `NLA.MI19.not_subsetConjecture`: the negation of the complete canonical universal assertion.

The original complex order comparison is genuine: both sums are proved real before the strict comparison. A proved six-pair formula reduces inversion-count computation. The only LeanCert check is one negative rational scalar in explicit kernel mode; there are no intervals or numerical spectral computations. The source's optional exact rank, all-q polynomial identities and positive-definite perturbation results are outside this project's claimed formal scope.

## Reproduction and evidence

From this directory, the development build is:

```bash
lake exe cache get
lake build Solution
```

All dependency revisions are fixed in `lake-manifest.json`. The two intentional Challenge placeholders belong to a separate target environment and are never imported by Solution. Build, axiom and hash records are in [reviews/](reviews/); independent re-elaboration logs are in [verification/](verification/).

From the repository root on the supported non-root Linux host, use the [shared harness prerequisites](../../../tools/lean/HARNESS.md) and:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py matrix-inequalities-and-norms/MI-19/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-19/lean /absolute/path/to/nla-lean-tools
```

The project must be committed and unchanged. The harness runs the real Linux sandbox, positive/negative controls and [Comparator configuration](comparator.json) against fresh inputs. Comparator's formal identity and kernel checks supplement the independent English-to-Lean fidelity reviews. A successful Linux result and immutable proof links must be added before this evidence supports a `Lean verified` catalog entry.
