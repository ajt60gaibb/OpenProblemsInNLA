# MI-21: independent audit of actual Linux verification

**Verdict: PASS — 12 September 2026.** The completed
[GitHub Actions run 34709291489](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34709291489)
successfully verified the MI-21 project at immutable commit
`06ade659dee260a18b79ce638383bf0a49125ecf`. The actual project verification step
ran from **17:48:51 to 17:55:30 UTC** and was not skipped. All six jobs in the
parent run, and all their recorded steps, completed successfully.

Reviewer: OpenAI Codex agent **`/root/leancert_examples`**, independent of the
MI-21 statement/proof implementer `/root/solved_statement_inventory`. I also
performed independent statement referee 2 and final mathematical referee 2
reviews. This audit reads the actual remote execution and original artifacts
locally on macOS; it does not claim a local Linux rerun, external human peer
review, or a new independent implementation of the shared checker.

## Actual source, run, and artifact identity

The proof receipt records `comparator-accepted` and exactly **81 project input
files**. I checked that this set equals the complete ordinary Git-tracked
project input set at the stated commit, with no missing or extra input. Every
SHA-256 matches both its immutable Git blob and the current working file.
All five mathematical source files remain at both final referees' frozen
hashes. The additional prose `SOURCE_MAPPING.md` matches its explicit referee 2
and original proof-freeze hash. The configuration selects exactly the three
reviewed theorem names, no definition replacements, and only the three
permitted standard axioms.

Both original ZIPs were downloaded from GitHub, checked against GitHub's
recorded SHA-256 digest and head commit, and safely extracted. Every one of
the **23 extracted artifact files** was compared byte-for-byte with its
original ZIP member; no member was added or omitted.

| Original artifact | GitHub artifact ID | SHA-256 |
| --- | --- | --- |
| `lean-MI-21.zip` | `10303395027` | `39dc799a7142e0855b481d3adec6448603dd5b8b1c94eca8eba957bcd000cb95` |
| `lean-checker-controls.zip` | `10302269565` | `65938a505044fe6b44a48532b6033e8b3eb3d49f5d90a5b978a125c4b3376372` |

This directory retains the original run/job/artifact API responses, the
original logs for selection, standalone checker controls and MI-21, both
original ZIPs, all extracted logs/receipts, and immutable source snapshots.
`FETCH-IDENTITY.json` records retrieval rather than a semantic verdict.
`identity-verification.json`, `control-verification.json`, and the complete
`EVIDENCE-MANIFEST.json` bind the audit to those bytes.

The new-branch push had an all-zero `BASE_REF`, so the selector followed its
documented all-project path. Besides MI-21 and the standalone controls, it ran
the existing MI-19, IE-19 and IE-18 projects. Their successful job conclusions
are recorded, but this report's detailed source/receipt/proof audit concerns
MI-21 and both control sets only.

## Shared checker and real rejection controls

The full shared workflow/tooling is byte-identical to upstream
`587bd896f0e1006f4a4b7f38555e3a523ef85176`. The actual harness, source lock and
bootstrap/selftest/verify entry points are unchanged from the previously
audited infrastructure commit `214c142d6bfe0f0c338808f188062acbbad0fb19`.
I read the complete current harness and source lock while auditing this run.
The lock binds the real Comparator, exporter, strict Landrun wrapper, and
rejection probes to Forsythe source commit
`8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The two independent job receipts
record the same built tool digests, Lean version, source-lock digest and
derived noninteractive probe digest.

I inspected the actual sandbox, raw-kernel replay, full Comparator regression,
and extra axiom-rejection logs in **both** the standalone checker job and the
MI-21 verification job:

- Build and export modes ran as unprivileged UID 1001 with private user, PID,
  mount, network, IPC and UTS namespaces, no effective capabilities, and
  `no_new_privs`. Outside writes, truncation, symlink writes and creation were
  denied; build-directory writes were permitted only in build mode.
- Loopback access and AF_UNIX socket creation were denied. The host parent
  process was absent from private `/proc` and could not be signalled through
  the tested lookup. Four unsupported sandbox argument cases failed closed.
- The nested `bwrap` executable actually ran, but UID-map creation failed
  before its inner write. This establishes the recorded rejection; it does
  not claim execution of the denied inner write. Read-only host mounts do not
  provide general host-file confidentiality; the job used the dedicated
  GitHub Actions runner.
- The actual raw-kernel probes accepted the honest inductive/quotient fixture,
  rejected an invalid raw proof of `False`, and rejected the forged quotient
  declaration in the quotient post-check. All three probes reached their
  intended checking phases.
- All five full Comparator fixtures reached both builds and both exports and
  returned their recorded expected outcomes. The separate theorem-type
  mismatch was rejected. The fixture labels are retained as logged; some
  named legacy fixtures reject at a kind or illegal-helper-axiom check.
- The additional full Comparator cases rejected `sorryAx` and the actual
  Lean 4.33.1 native-generated axiom
  `checked._native.native_decide.ax_1_1` after both builds and exports.

The mechanical assertions in `audit_checks.py` reuse and adapt the prior
MI-29 audit's checks, with credit to `/root/formal_review_standards`. They
supplement this independent inspection of the present raw MI-21 execution;
they do not replace semantic review with a previous project's verdict.

## Actual proof, kernel and statement checks

The Linux job freshly cloned and checked out all **10 pinned dependencies**.
The matching Mathlib cache supplied **8,690 files**, so this was a fresh
project verification with cache reuse, not a complete rebuild of every
dependency. Definitions and Challenge were freshly elaborated in the
**2,710-job** Challenge graph. Proof and Solution were freshly elaborated in
the **3,147-job** Solution graph. Only Challenge's three intentional interface
placeholders generated warnings; Solution and its proof emitted none.

The actual exported declarations were:

1. `NLA.MI21.operatorNorm_isUnitaryInvariant`
2. `NLA.MI21.counterexample`
3. `NLA.MI21.not_geometricMeanNormConjecture`

The full Comparator exported both environments, compared these three
declarations and their dependencies, ran Lean's default kernel on the solution,
and printed `Lean default kernel accepts the solution` and
`Your solution is okay!`, with exit status zero. This is actual kernel replay
and formal statement matching, not an inference from a successful build.

All **11** internal/public transitive axiom reports contained exactly
`propext`, `Classical.choice`, and `Quot.sound`. The corresponding explicit
kernel-trust assertions passed. The unchanged proof still uses its explicit
kernel LeanCert point certificate for
`1 < 1351000/1350907`; the operator-norm lower bound, strict counterexample,
and full negation actually consume that certificate. No native-execution
axiom is present in the exported proof closure.

## Scope and publication conclusion

The already-reviewed frozen mathematical interface proves that the genuine
complex Euclidean operator norm is an admissible unitarily invariant norm,
proves every positive-definite witness premise and the actual CFC geometric
mean identities, derives the strict violation for every positive outer
parameter, and negates the full original all-dimension, all-matrix,
all-parameter, all-unitarily-invariant-norm conjecture. Neither an eigenvector
nor a Riccati certificate replaces the genuine norm or CFC definition.

The two independent statement and two final proof reviews establish the
English-to-Lean correspondence. Comparator establishes formal identity and
kernel trust; it does not independently interpret the English problem.
The unchanged proof and these actual Linux records satisfy the operational
verification gate for publication. No mathematical or status edit, commit,
push, or pull request was made as part of this audit. Root controls the
separate final publication review and catalog promotion.

Mathematical counterexample and informal proof: **Matthew J. Colbrook**,
Department of Applied Mathematics and Theoretical Physics, University of
Cambridge. Formalization: **George Stepaniants**, Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA, with AI-agent assistance. No George email is published.
