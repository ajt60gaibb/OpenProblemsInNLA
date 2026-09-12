# MI-26 independent Linux operational review

**Verdict: PASS for the seven reviewed exports at immutable revision `81176af27e570b59ba1e1a0745e28944e7d57c03`.** This is an independent audit of an actual successful GitHub Actions Linux run, not an inferred result from local compilation or an exit code alone.

Reviewer: agent `solved_statement_inventory`, 12 September 2026. The proof implementation was by agent `leancert_examples`; I did not author or alter its mathematical source. My earlier independent statement and final proof reviews are bound below. This operational review changes no canonical status and makes no human peer-review or general security certification claim.

## Actual run and original artifacts

[Run 34713045511](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34713045511), attempt 1, ran on GitHub Actions Ubuntu 24.04 x86-64. The API records the exact revision above and a completed successful run, created at 19:03:49 UTC and updated at 19:12:58 UTC. All seven jobs and their recorded steps succeeded. I retained and inspected the full raw API logs for selection job `103605180414`, MI-26 job `103605209287`, and independent checker-control job `103605209289`. The other four project jobs are covered only by their successful API status in this report.

I downloaded both original ZIP byte streams through GitHub's artifact API, preserved the original run/job/artifact metadata, and independently recomputed their SHA-256 digests. Each digest matches both GitHub artifact metadata and the actual job upload log. I compared every extracted file byte-for-byte with its ZIP member and verified the complete member sets.

| Original artifact | ID | Files | SHA-256 |
| --- | --- | --- | --- |
| `lean-MI-26.zip` | 10304680169 | 13 | `98d4e1f8da04f506f1482d602f403041b786a1d8c1d74d323ac683e15f9716d9` |
| `lean-checker-controls.zip` | 10304380209 | 10 | `09d085df17b70fe398d9de55ebc1c02c271c4ed8ed532c80272db5a8cb153a90` |

The original artifacts, extracted contents, raw logs and metadata remain in this directory. `fetch_artifacts.py` records retrieval; `audit_checks.py` records the separate identity/control audit. Neither merely treats retrieval or an exit status as mathematical acceptance.

## Exact reviewed input and tool identity

The receipt's **118 input paths are exactly the complete Git-tracked project input set** at the candidate revision. Every receipt SHA-256 was independently recomputed against its immutable Git blob and current worktree bytes. All matched. The complete 118-file snapshot, commit object and Git tree listing are retained under `source/`; the canonical README and complete informal `solution.tex` also match the original hashes recorded by the final referees.

| Mathematical boundary | SHA-256 |
| --- | --- |
| `NLA/MI26/Definitions.lean` | `821cb1b2a29f7382a1f36bd6b506bc6b249b9da0b61837702658173814995f63` |
| `Challenge.lean` | `85eafac2fc875ddacb35c37f832834cfe79e6b10730f2656185209592f608fe1` |
| `NUMERICAL_TARGETS.md` | `ecc403bb0f57fc49f2e3be78c9012f7e606ca8035d92af83fa95bddfbe994257` |
| `NLA/MI26/Proof.lean` | `94dd1dde3f1b12002380ae4730ea6396a955f7cbe69a34dde101e7a035fae0af` |
| `Solution.lean` | `a79aa8df0b6b7501dcb6d264fc8a9a21ac0710aa05ed65bff3b244ba97fe6da1` |

Both final proof reports contain these five exact hashes. All protected proof/configuration files and all four independent review hashes also match the root's pre-Linux packaging record:

| Independent review | SHA-256 |
| --- | --- |
| `statement-referee-1.md` | `c06e27fc583b7abdf6f7c8e7832278f029cf0fefaf937453406faea2eba3a9d7` |
| `statement-referee-2.md` | `aa91612934d87a6132e3a07636d5c5bef3917366ee3a358690b79e7651fb9a42` |
| `proof-referee-1.md` | `463da0d03abdf5f842571c30f4df7406f1d1d5c3885739a295806eb7b056f8de` |
| `proof-referee-2.md` | `3706e0c62af0e43f7fd39e991ecb5ed8db5d3185d32cbce95ae34ff57e28451b` |

The actual harness, bootstrap, self-test, verifier and source lock are byte-identical to audited Linux revision `214c142d6bfe0f0c338808f188062acbbad0fb19`. The complete workflow/tool directory matches the candidate's recorded upstream base `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`.

The source-lock SHA-256 is `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`, pinning Forsythe revision `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. I independently checked all **58 locked upstream source files**, their sizes and hashes, and retained them under `source/forsythe/`. I reconstructed the exact reviewed CI probe adaptation from the actual harness; its SHA-256 `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803` matches both remote tool receipts. The actual harness source was read, including immutable Git snapshotting, source/binary rechecks, fresh dependency setup, probe adaptations, mandatory controls and Comparator invocation without skipping default-kernel replay.

Both jobs report the same Linux tool receipt: Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Go 1.27.1, Linux 6.17.0-1022-azure/glibc 2.39. Original bootstrap logs show fresh Comparator/lean4export and Landrun builds. Binary hashes, exact environment hash and all source pins are retained in `tool-source-verification.json`. Those are remote receipts; I do not claim to have executed Linux binaries locally.

## Actual builds, comparison and trust checks

The fresh dependency log records ten real package clones and checkouts at every exact `lake-manifest.json` revision, including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The job downloaded and decompressed **8690 Mathlib dependency cache files**. It did not import the local macOS build directory. This is a fresh project/dependency checkout with a disclosed upstream dependency cache, **not a claim that every library module was rebuilt from source**.

The log shows actual builds of project Definitions, Proof and Solution, with 2710 and 3147 total graph jobs for Challenge and Solution respectively. Graph totals are not counts of source files rebuilt. Challenge has exactly seven intended statement placeholders. Solution has no warnings. Its eight internal and seven public `#assert_trust kernel` / axiom checks all completed; every one of the 15 unique printed axiom lists is exactly `propext`, `Classical.choice`, `Quot.sound`. The actual retained LeanCert scalar certificate participates in the final contradiction as independently established in the hash-bound final proof reviews; this run accepts that unchanged proof under the same kernel trust boundary.

Comparator actually builds and exports both sides, compares exactly these seven declarations, and then reports `Running Lean default kernel on solution.`, `Lean default kernel accepts the solution`, and `Your solution is okay!`:

- `NLA.MI26.admissibleFunction_iff`
- `NLA.MI26.functionalCalculus_eq_spectral`
- `NLA.MI26.functionalCalculus_congr_nonneg`
- `NLA.MI26.quadratic_cfc`
- `NLA.MI26.witness_data`
- `NLA.MI26.counterexample`
- `NLA.MI26.not_subadditivityConjecture`

The exact receipt and committed `comparator.json` agree, with empty `definition_names` and only the three standard permitted axioms. Actual job metadata validation reports coverage of all seven declarations. Comparator establishes agreement with the reviewed formal statements; the prior independent statement/proof reviews establish fidelity to the informal problem. Its receipt correctly states that automatic semantic review was not performed.

## Both executed control sets

I inspected both the standalone checker-control logs and the controls executed before the MI-26 proof. Mechanical assertions additionally require each actual phase and expected result:

- Real Landrun/systemd restrictions and real bubblewrap execution were used in both build and export modes. Each mode observed private user, PID, mount, network, IPC and UTS namespaces; UID 1001; no effective capabilities; `no_new_privs`; absent host parent; and denied host signal lookup. Writes, truncation, creation and symlink write attempts outside the build allowance were denied; only designated build `.lake` writes succeeded, while export remained read-only. Loopback and AF_UNIX creation were denied. Four invalid command-option cases each exited 2.
- Nested bubblewrap actually executed but **UID-map creation was denied before its inner write**. This report does not claim the inner write ran or a general nested-sandbox proof.
- Three genuine `Comparator.runBuiltinKernel` cases accepted the honest inductive/quotient proof, rejected an invalid raw proof, and rejected the malformed quotient at the quotient post-check.
- Five end-to-end Comparator fixtures each built and exported both Challenge and Solution. The honest match passed; mismatching definitions, illicit-axiom fixtures and mismatching theorem types were rejected. The `simple_kind_mismatch` fixture's observed rejection was its illegal helper axiom; I do not relabel that as a different mechanism.
- Two additional end-to-end negative fixtures each completed both builds and both exports before rejecting `sorryAx` and `checked._native.native_decide.ax_1_1` respectively, with exit 1. Their rejection was not a build failure or missing executable.

All expected normal control stages ended successfully. The original main/control logs and parsed records are retained; the verdict relies on observed execution phases and outcomes, not only successful job labels.

## Evidence and scope

`audit-checks.log` records a fresh successful mechanical audit. Its script SHA-256 is `982c017a21b8d7a6e16a4776fee24425ed4d4e1aae96a345df575ec8cb88d151`. The identity, control, axiom and tool-source records preserve detailed machine-readable results. `EVIDENCE-MANIFEST.json` hashes every retained evidence file except itself, including this report, original ZIPs, raw logs and complete source snapshots.

This report supports completing the repository's MI-26 verification workflow for the exact revision and seven exports above. It does not itself change the catalog, certify stronger unpublished variants, establish priority, or claim immunity to all possible compiler/runtime/sandbox defects. Mathematical source attribution remains Matthew J. Colbrook. Formalization credit remains George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA; no author email is added.
