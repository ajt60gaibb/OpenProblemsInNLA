# PF-03 independent operational and execution-evidence review

**Verdict: PASS for the two completed Linux runs identified below.** No operational source-binding or missing-check blocker was found. Reviewer: `/root/pf03_final_referee2`, an independent, nonauthor AI referee. This review ran no Lean compiler or Comparator process and made no publication, status, or count changes. It independently inspected the archived execution evidence and fetched current public GitHub run, job, artifact, pull-request, and merge-commit metadata.

The public observations were recorded at `2026-09-19T05:51:48.291Z`. The independent audit is reproducible by running `python3 audit_runtime.py` from this review directory; it reads local Git objects and evidence and performs no compilation or network calls. Its input API observations are retained separately in `FRESH-GITHUB-OBSERVATIONS.json`. `AUDIT.json` contains all 234 project input hashes, every artifact member hash, the 25 target reports for each run, exact tool receipts, and source hashes for the reviewed workflow and harness.

## Exact executions and artifact binding

The reviewed published proof commit is `9625a76780183040186664100e24e0e90d8fcc7d`, associated with upstream draft [PR 303](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/303).

| Execution | Actual checked commit | Run / job / artifact | Artifact SHA-256 |
| --- | --- | --- | --- |
| Fork push | `9625a76780183040186664100e24e0e90d8fcc7d` | [35424055075](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35424055075) / `105846873543` / `10578972769` | `17e3898509b3f2f596fe2aeea2cad3186c797c82d7c720583069d6d80144d912` |
| Upstream pull request | `693e92b166d391507dd818687aea0b1ad92f1321` | [35424087832](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/35424087832) / `105846968481` / `10578567081` | `9fef1366fd789efa41bcf709fa3159aa822130ce5e9e1e25bcb7a2ad76833b94` |

Fresh GitHub API observations report both runs completed successfully and each selected exactly one verification project, PF-03. The relevant sandboxed verification step succeeded on `ubuntu-24.04`. I independently computed both downloaded ZIP hashes and sizes and compared them with GitHub's official artifact digests and sizes. I checked archive CRCs, member uniqueness, safe paths, and byte equality of every extracted member, with no surplus extracted files. The ZIPs were already downloaded by the root agent; this referee independently authenticated their bytes against freshly fetched official metadata. Direct artifact-ID API requests were unavailable through the connector, but the run-artifacts endpoints returned the required digests successfully.

The upstream artifact truthfully identifies the synthetic PR merge commit, rather than pretending to have checked the branch commit directly. Fresh GitHub commit metadata shows that merge's parents are upstream `71563f17926cd826a892c2bba0e294894ee57a5c` and the published proof commit. Its entire Git tree is `5c76eab8fd866cb97e98cf093d6db5908f065dbf`, equal to the proof commit's tree computed from local immutable Git objects. The PF-03 Lean subtree also matches independently: `b344ac5a999397c6a469907ba056deb97b893dbd`. Thus both executions checked byte-identical project, workflow, and harness trees.

I recomputed all 234 project file hashes from the published commit's Git blobs and matched both execution receipts exactly. All 61 active Lean source files, the numerical-target document, and Comparator configuration match this referee's earlier independent final mathematical review. Archived review files also ending in `.lean` are included among the 234 inputs but are not miscounted as active modules.

## Actual proof and control execution

Both raw `comparator.log` files show fresh builds of Challenge, all 59 PF-03 implementation modules, and Solution; exports of all 25 frozen targets from both Challenge and Solution; actual default-kernel replay; `Lean default kernel accepts the solution`; final Comparator acceptance; and exit status zero. Each contains two successful kernel-mode LeanCert dyadic certificate checks. The 25 Challenge placeholders are expected statement templates. No implementation placeholder warning was observed. Every aggregate target reports exactly `propext`, `Classical.choice`, and `Quot.sound`; all other printed axiom reports stay within that same allowlist. The frozen configuration contains exactly 25 theorem targets and no permitted definition holes.

The controls were actually exercised within each PF-03 verification job:

- Default-kernel controls accept an honest inductive/quotient example, reject an invalid raw proof with a kernel type mismatch, and reject a quotient mismatch at the required postcheck.
- Five Comparator fixtures accept a genuine match and reject statement, illegal-axiom, declaration-kind, and type mismatches at their intended phases.
- Separate negative fixtures reject `sorryAx` and the native-decision axiom. Their exit status one is the expected successful rejection outcome.
- Sandbox probes run both build and export modes as UID 1001. They check private namespaces, forbidden external writes and truncation, symlink escape, host process access, network access, AF_UNIX creation, capabilities, nested-namespace escape, and unsupported Landrun arguments. Build-only output writes are allowed; corresponding export writes are rejected. The probes conclude successfully and preserve the outside fixtures.

The separate workflow job named `checker-controls` was skipped in both runs because infrastructure had not changed. This is not evidence that controls were omitted: the project verifier unconditionally ran the above controls, and their complete raw logs are present in both authenticated artifacts.

## Tool and harness inspection

I inspected the immutable workflow, verification entry point, harness control/build/export paths, and pinned Comparator axiom, comparison, and default-kernel replay code. The harness rejects root execution, snapshots unchanged committed inputs into a fresh directory, verifies locked tool sources and executable receipts, runs controls before proof checking, propagates command failures, and requires both kernel and Comparator success markers before emitting acceptance. Comparator performs actual `Lean.Environment.replay` into an empty environment and a quotient postcheck; the acceptance message is downstream of those checks.

I independently checked all 58 locked tool source hashes and sizes against Forsythe commit `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. Both receipts bind source-lock SHA-256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, Lean 4.33.1 Linux commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, actual executable hashes, the sandbox probe, and sanitized environment. Raw dependency logs contain every pinned manifest revision, including LeanCert and Mathlib. Bootstrap logs show successful actual tool builds. Dependency caches were used; the logs nevertheless show the PF-03 implementation modules built in the fresh verification project.

## Scope and limitations

This operational PASS supplements, rather than replaces, this referee's earlier mathematical review in `../PF03-final-referee2/REVIEW.md` (SHA-256 `de276b724ad4cfa68f05bd59f5b6e67c58ca29d635db06f49958921e3f121bbd`). That review covers the complete existential negative PF-03 target and its certificate-to-target bridges. It does not certify the optional explicit order-444 construction, strictly positive entries, or minimality claims. The active proof and contract bytes are unchanged.

This is an AI review under the repository's recorded review scopes, not human peer review or a full security audit of Lean, GitHub, the operating system, exporter, or Comparator. Official artifact digests authenticate the retained execution records; they do not make the entire computing stack infallible. The root agent's audit was supplementary, not substituted for the independent checks above. Any future revision must retain an explicit correspondence to these exact verified sources; this report does not claim that an uninspected later commit itself ran these checks.
