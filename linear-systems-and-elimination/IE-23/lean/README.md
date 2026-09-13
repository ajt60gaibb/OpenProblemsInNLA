# IE-23 - Lean verified

**The complete original induced-norm uniqueness conjecture has a proved negative answer in Lean, with all eight reviewed exports.** Two independent statement approvals, including the exact additive Comparator supplement, preceded implementation. Two independent final proof reviewers approved the completed source after their own fresh elaboration and actual-term audits. Actual [Ubuntu run 34725525250](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725525250) verified all eight exports at immutable revision `a40e5608f61dd4086708cb2e03901ffd01e4c0a9`, with default-kernel replay and both real control suites. The proof author's operational inspection was separately accepted by the coordinator. The canonical entry is **Lean verified**.

Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook** retains credit for the mathematical resolution. **Dokmanić and Gribonval** retain attribution for the underlying rational matrix in their Example 4.1. No new mathematical priority or source-author endorsement is claimed. The implementing agent `/root/leancert_examples` is neither independent final referee; the coordinator `/root` served as independent statement and final proof referee 2.

## Complete target and proved scope

The full [canonical problem](../README.md) quantifies every original dimension 1≤m<n, every complex full-row-rank matrix A, every finite real p>2 and every distinct complex right inverse. It uses the direct induced p-to-2 norm, with the genuine Euclidean numerator, exact real-power denominator and actual supremum over every nonzero complex input. [Definitions](NLA/IE23/Definitions.lean) preserves this entire universal assertion, including the actual matrix rank and Moore-Penrose formula A* (AA*)⁻¹.

The exact source matrices at m=2, n=3 and p=4 give a full counterexample:

```
A = [[1,1,0], [1,0,1]]
B = (1/3) [[1,1], [2,-1], [-1,2]]
X = [[0,0], [1,0], [0,1]]
z = (1,-1), c = sqrt(sqrt(2))
```

[Norms](NLA/IE23/Norms.lean) proves the generic denominator positivity, nonempty/bounded ratio set and actual least-upper-bound property on every original domain, then the all-input operator inequality including zero. [Matrices](NLA/IE23/Matrices.lean) proves actual invertibility, rank, B=A†, both right-inverse equations and distinctness. These are conclusions; no extra boundedness, invertibility or minimization premise is assumed.

[FourthPower](NLA/IE23/FourthPower.lean) proves the true fourth-root and real-power identities and the universal complex-vector norm bound from the exact sum of squares (a²−b²)²≥0. [Actions](NLA/IE23/Actions.lean) proves both norming-vector attainments and the all-competitor identity: every complex right inverse Y satisfies Yz=(t,1−t,−1−t), so its squared Euclidean norm is 2+3|t|². [Minimizers](NLA/IE23/Minimizers.lean) identifies the actual suprema of B and X with c, proves they are both global minimizers over **all complex right inverses**, and establishes the genuine least feasible norm value. [Proof](NLA/IE23/Proof.lean) concludes the negation of the entire original conjecture.

The source's all-p formulas, full minimizer classifications, higher-dimensional families, smallest-dimension classification, endpoints and separate product-norm objective are outside the eight formal exports. The admissible p=4 case suffices for the complete original negative answer. All original source bytes and attribution are retained.

[Solution](Solution.lean) exports these exact [Challenge](Challenge.lean) signatures, each with prefix `NLA.IE23.`:

- `inducedNorm_semantics`
- `witness_matrix_identities`
- `fourth_power_norm_control`
- `witness_action_identities`
- `witness_attainment`
- `witness_norms`
- `witness_global_minimizers`
- `not_rightInverseUniqueConjecture`

## Exact computation and LeanCert

**LeanCert performs explicit kernel trust auditing of a pure exact proof. There is no numerical interval certificate.** Choosing p=4 reduces the only needed norm comparison to a sum of squares, avoiding interval subdivision, approximate norms and spectral enclosures. Real power and nonnegative-square bridges justify the unsquared inequalities. The exact diagnostic scripts are supplementary transcription/algebra checks, not proof oracles.

All sixteen internal/public `#assert_trust kernel` commands and transitive axiom reports allow exactly `propext`, `Classical.choice` and `Quot.sound`. The completed solution has no admission, custom axiom or native execution trust. The eight deliberate Challenge placeholders remain isolated and are never imported by Solution. [Comparator](comparator.json) selects every public export, with no definition exceptions and only the standard three axioms.

The project pins Lean **4.33.1**, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`; [lake-manifest.json](lake-manifest.json) pins all ten dependencies. The [actual v0.4 manifest](formalization.yaml) records scope, attribution, automation, reviews and the successful Linux verification.

## What ran and how to reproduce

The author and both independent final referees each completed ten fresh direct Lean commands: seven mathematical modules, Solution, their own actual-term inspector and separately invoked Challenge. All completed modules passed without warnings; only the eight intentional Challenge placeholders warned. Each audit reached 93 project declarations. The author required 38 retained mathematical dependencies, referee 1 required 40, and referee 2 independently required 28 and added twelve kernel assertions. Their exact scripts, object/source paths, logs and receipts are retained in the linked evidence.

These were **macOS source re-elaborations**, using clean matching MI-22 dependency objects read-only because of limited disk space. Every IE-23 project object was compiled into a new private prefix, excluding all prior project objects. They were not local Lake invocations, full dependency-source rebuilds or Linux Comparator runs. The packaging task does not repeat these proof checks or download dependencies.

For a normal checkout with its own dependencies, the explicit project proof command is:

```
lake build Solution
```

The deliberately frozen default is Challenge; plain `lake build` therefore checks statements. The retained author and referee runners record the exact local source/pin/object paths used in their private-prefix checks. Their integrity assertions bind the historical README and evidence at that phase. Reproducing those historical runners requires an isolated copy of those frozen inputs and their recorded local paths; they are not generic commands to rerun over refreshed publication wrappers. The normal proof command above and the shared Linux workflow below apply to the current candidate.

For the exact executed source, check out [immutable revision a40e560](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/a40e5608f61dd4086708cb2e03901ffd01e4c0a9/linear-systems-and-elimination/IE-23/lean). Use the [shared workflow](../../../docs/lean/README.md) on a correctly configured [non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  linear-systems-and-elimination/IE-23/lean \
  /absolute/path/to/nla-lean-tools
```

## Actual Ubuntu execution and accepted evidence

[Run 34725525250](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725525250) completed successfully at `a40e5608f61dd4086708cb2e03901ffd01e4c0a9`. The [project receipt](verification/linux-2026-09-12/artifacts/lean-IE-23/verify-20260912T233011Z-4151/result.json) binds the exact 190-file Git input tree and all eight exports. The genuine Comparator matched both environments with no definition exceptions and replayed the solution in Lean's default kernel. All sixteen internal/public axiom reports contain the standard three axioms. The eight intentional Challenge placeholders remain isolated.

The harness took a fresh committed-source snapshot and cloned all ten dependencies at their pinned revisions. It reused **8690 official Mathlib cache files**; this was not a full dependency-source rebuild. The recorded 2384/2394 Challenge/Solution job counts are graph sizes. Seven project mathematical modules and Solution were freshly elaborated. The shared checker/exporter and Landrun binaries were built from the pinned tool sources. Both the standalone and project jobs exercised real non-root build/export isolation, kernel regressions, Comparator mismatches and the additional admitted/native-proof rejections. Nested Bubblewrap was denied UID-map creation before any inner write; no broader claim is inferred.

The [operational report](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [330-file manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) retain both original GitHub artifact ZIPs, metadata, complete run-log ZIP, source snapshots, checker pins and unmodified logs; the outer manifest is the 331st file and all nested manifests are included. The original project ZIP digest is `bc1fceb8cc81b8c3f7a4c938b3208fc2727fa4f3895dd4c70f5ec3e01f480271`; the control ZIP digest is `f8908adc9b1840cf4d8b9350aa904e8adf160d1d58f696be831cae3d2d191978`.

**Operational inspector `/root/leancert_examples` authored the proof.** The coordinator `/root`, independent of that author and previously final mathematical referee 2, separately [accepted the actual evidence](verification/root-operational-2026-09-12/ROOT-CHECKS.json). The [root evidence manifest](verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json) binds that acceptance. Publication preparer `/root/solved_statement_inventory` previously served as independent mathematical referee 1. None of these packaging or operational roles is an additional mathematical review. No new proof build or Linux run is claimed for the refreshed publication wrappers.

## Independent reviews and historical records

- Statement referee 1: [report](reviews/statement-referee-1.md).
- Statement referee 2: [report](reviews/statement-referee-2.md).
- Exact statement-gate configuration: [supplement](reviews/statement-config-supplement.md) and [record](reviews/statement-config-supplement.json).
- Final proof referee 1: [report](reviews/proof-referee-1.md) and [evidence](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json).
- Final proof referee 2: [report](reviews/proof-referee-2.md) and [evidence](reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json).
- [Proof-start record](verification/proof-start.json), [author completion](reviews/proof-completion.md), [author execution](verification/final-author/fresh-checks.json) and [complete proof freeze](reviews/proof-freeze.json).

The referees apply the [pinned Tau Ceti adaptation](../../../docs/lean/REVIEW.md), including original-target fidelity, actual definitions and hypotheses, proof quality, library reuse, API, documentation and attribution. These are independent AI-agent reviews, not external human peer review or official Tau Ceti endorsement. Schiffer and Forsythe are credited as campaign organization/tooling examples; no mathematical result from those projects is assumed.

All statement-stage documents remain historical records of 12 September 2026. [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md), [SOURCE_CORRESPONDENCE.md](SOURCE_CORRESPONDENCE.md), [PROOF_MAP.md](PROOF_MAP.md), earlier handoffs and referee reports preserve their original phase-specific wording. Their pending-work statements are superseded by the dated evidence above. The original statement README is retained at [README.statement.md](verification/linux-candidate-2026-09-12/README.statement.md). All other 103 proof-freeze inputs and all eight original source snapshots are unchanged.

Publication changes only this README and the current formalization manifest among the 190 submitted inputs; all other **188 inputs**, all **331 Linux evidence files** and the complete coordinator acceptance evidence remain byte-identical. The exact prior [README](verification/publication-2026-09-12/archive/README.linux-candidate.md) and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml) are archived. Original targets, source manuscripts, pins, code, all eight exports, reviews and the additive configuration supplement are preserved. The successful run remains bound to the immutable candidate revision; the publication handoff separately records wrapper, catalog and rendered-document checks.
