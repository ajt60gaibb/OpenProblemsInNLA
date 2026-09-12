# Suggested MI-19 catalog update

Draft only: no canonical source or catalog status has been changed by this reviewer. Apply after retaining the audited logs and updating the project's publication status to reflect the successful run. Keep the permanent ID, canonical path, and original problem statement unchanged.

## Canonical README status

```markdown
**Status:** Lean verified  
**Last checked:** 2026-09-12
```

Add a link to the following section from the existing resolution notice. Retain Matthew J. Colbrook's mathematical credit and the original informal argument. The original argument's additional perturbation remark should remain distinguished from the narrower list of formalized claims below.

## Canonical README section

```markdown
## Lean proof and verification evidence — 2026-09-12

**Mathematical counterexample:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The [Lean proof](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/NLA/MI19/Proof.lean) and [public declarations](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/Solution.lean) at immutable revision `cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7` prove `NLA.MI19.counterexample` and `NLA.MI19.not_subsetConjecture`.

The latter negates the complete original statement: every `n≥2`, every complex Hermitian PSD matrix, every real `q∈[0,1]`, and every nonempty proper subset, with setwise preservation and inversion counts in the full original ordering. All witness hypotheses are proved. The genuine complex PSD order-four Gram witness has `q=7/8` and the interior singleton, giving full minus restricted q-permanent `-3235575/16384`. Exact rank, all-q polynomial identities, and the positive-diagonal-perturbation extension are not among the formalized claims.

The toolchain is Lean `4.33.1`, with LeanCert pinned to `621a43d7cf21f87872392a01e874f2f1dbddc926` and mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`; [all dependencies are locked](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean/lake-manifest.json). LeanCert checks the exact scalar inequality in kernel mode. Both public theorems and the five audited internal declarations have only `propext`, `Classical.choice`, and `Quot.sound` in their transitive axiom closure.

The catalog reviewed [successful Linux verification on 12 September 2026](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703363593/job/103578942995), including fresh problem builds, real sandbox isolation controls, exact Challenge/Solution comparison with no definition holes, the standard-three axiom whitelist, and Lean default-kernel replay. The mathlib dependency cache was used. Both requested theorems passed; sorry, custom-axiom, statement-mismatch, invalid-kernel-proof, and native-trust rejection controls also ran successfully. The [project guide](lean/README.md), [formalization manifest](lean/formalization.yaml), and [independent reviews](lean/reviews/) describe statement fidelity, attribution, and scope. These are independent AI-agent reviews, not external human peer review.

On a Linux host satisfying the [verification prerequisites](../../docs/lean/README.md), run the following at the pinned proof revision:
```

Insert this code block immediately after the paragraph above:

```bash
tools/lean/bootstrap.sh /tmp/nla-lean-tools
tools/lean/verify.sh matrix-inequalities-and-norms/MI-19/lean /tmp/nla-lean-tools
```

**Integration instruction:** add a stable relative link in the Linux-evidence paragraph to the retained `OPERATIONAL-REVIEW.md`, `comparator.log`, and `result.json` after choosing their published project location. Their present local filenames and GitHub run are real; do not publish a guessed evidence path. The original `lean-MI-19.zip` artifact has SHA-256 `bf7872acf3574fa91a7f464df0b871386fd27f67697b581ed40d78b12c55bd53`.

## RESOLVED.md wording

Keep the existing MI-19 entry and its informal-source links. Append the following paragraph to distinguish formalization credit from authorship of the mathematical result:

```markdown
**Lean verified — 2026-09-12.** Mathematical counterexample: **Matthew J. Colbrook**, University of Cambridge, Department of Applied Mathematics and Theoretical Physics. Lean formalization: **George Stepaniants**, California Institute of Technology, Department of Computing and Mathematical Sciences. [Proof and verification evidence](matrix-inequalities-and-norms/MI-19/README.md#lean-proof-and-verification-evidence--2026-09-12) cover the complete negative target through `NLA.MI19.counterexample` and `NLA.MI19.not_subsetConjecture`, at [immutable proof revision `cd44ce9`](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/cd44ce9bcb84ebc79a1aa934918d1f76b2a9c6e7/matrix-inequalities-and-norms/MI-19/lean). [Linux Comparator and kernel checks passed](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703363593) with only the standard three axioms. The optional perturbation extension is not part of the formalized claims.
```

If the resolution archive is regenerated by the catalog tools, introduce this attribution/evidence through the supported canonical metadata or generator path rather than leaving a manual edit that regeneration would overwrite. Run the repository's permanent-ID checks and catalog tests before publication.
