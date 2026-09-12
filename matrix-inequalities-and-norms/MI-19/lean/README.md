# MI-19 Lean formalization

This project proves the negative answer to the [original MI-19 question](../README.md). At an actual complex Hermitian PSD Gram matrix, `q=7/8` and the interior singleton `{2}` in the paper's indexing, the full q-permanent minus its subset-preserving sum equals `−3235575/16384`. This strict counterexample refutes the complete universal conjecture.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Original mathematical counterexample and informal proof: **Matthew J. Colbrook**. See [formalization.yaml](formalization.yaml) for roles, sources and automation disclosure.

The complete proof passed [Linux Comparator and kernel verification](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703363593/job/103578942995) on 12 September 2026 at [proof revision cd44ce9](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean), under pinned Lean 4.33.1. Both independent final proof referees also re-elaborated the source successfully. All audited internal results and public exports pass `#assert_trust kernel` and report exactly `propext`, `Classical.choice`, and `Quot.sound`. The canonical entry is now `Lean verified`; the retained [operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) binds the successful run to the reviewed mathematical source hashes.

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

All dependency revisions are fixed in [lake-manifest.json](lake-manifest.json), including [LeanCert 621a43d](https://github.com/alerad/leancert/commit/621a43d7cf21f87872392a01e874f2f1dbddc926) and [mathlib 0df444a](https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474). The two intentional Challenge placeholders belong to a separate target environment and are never imported by Solution. Build, axiom and hash records are in [reviews/](reviews/); independent re-elaboration logs are in [verification/](verification/).

The successful Linux run freshly cloned all ten locked dependencies and used the matching upstream mathlib cache. Comparator then rebuilt the actual Definitions, Challenge, Proof and Solution, exported both targets, checked their types and used definitions with no definition holes, and accepted them through Lean's default kernel. The [Comparator log](verification/linux-2026-09-12/artifacts/lean-MI-19/verify-20260912T155027Z-3941/comparator.log), [result receipt](verification/linux-2026-09-12/artifacts/lean-MI-19/verify-20260912T155027Z-3941/result.json), [isolation and rejection checks](verification/linux-2026-09-12/control-verification.json), and [artifact integrity record](verification/linux-2026-09-12/identity-verification.json) are retained with the original downloaded ZIPs and [evidence hashes](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json). This is a fresh project verification, not a rebuild of every dependency from source.

From the repository root on the supported non-root Linux host, use the [shared harness prerequisites](../../../tools/lean/HARNESS.md) and:

```bash
python3 -m pip install -r tools/lean/requirements.txt
python3 tools/lean/validate_manifest.py matrix-inequalities-and-norms/MI-19/lean
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-19/lean /absolute/path/to/nla-lean-tools
```

The project must be committed and unchanged. Run these commands at the linked proof revision to reproduce the recorded inputs. The harness runs the real Linux sandbox, positive/negative controls and [Comparator configuration](comparator.json) against fresh inputs. Comparator's formal identity and kernel checks supplement the independent English-to-Lean fidelity reviews. The archived proof revision and its historical reviews recorded Linux as pending when written; the subsequent successful run and its operational audit complete that gate without changing the mathematical proof.
