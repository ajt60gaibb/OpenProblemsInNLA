# IV-06 independent actual Linux operational review

**PASS for the exact candidate `18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb` in [GitHub Actions run 34725713519](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519).** I observed the complete run and all 12 jobs finish successfully, independently inspected the IV-06 and checker-control raw evidence, and verified the original artifact digests and source bindings. This report does not promote a canonical status or assert publication approval.

Reviewer: `/root/formal_review_standards`, Codex AI agent. I previously served as IV-06 statement referee 2; I authored neither its statements nor mathematical proof and was not one of its two final proof referees. I also contributed to the campaign's shared harness work; the unchanged harness is tied here to the previously independently audited infrastructure revision. This is an execution and provenance audit, not an additional full mathematical proof review, official Tau Ceti review or external human review.

## Exact source and review binding

The candidate is the immutable own-fork commit on `codex/lean-iv06-interval-eigenvalue-components`. Its complete Git tree contains **200 project inputs**. Their exact set equals `result.json`'s `input_sha256` keys, and every SHA-256 matches both its committed Git blob and local candidate bytes. The complete input snapshot, Git tree and commit object are retained. The candidate author's and committer's names are George Stepaniants, with both email fields entirely empty.

The candidate's actual proof is bound to both independent final reviews by `verification/proof-freeze.json`, SHA-256 `5bc8cfd590e82a27807ad5f6832c0cc5d634832979241f80eb30d8d76eaaa673`. All 126 frozen inputs are retained: the exact former README is archived and all other 125 files remain unchanged. All eight original source Git blobs match the source base `f41f1f9ffa2171550d4bb795862c6170c4f26070` and are retained separately.

- Final proof referee 1, `/root/leancert_examples`: `fa9372a15b89f580959b9febb539d9b5c50e626b4a45672ff8848efce5e9ebc7`, with its complete 38-file evidence manifest `75c027c684508cc58266da2e893a35405102fa7ebb58bb6f5f9a3cab2c01a38b`.
- Final proof referee 2, `/root`: `3d333d14b69424f448e87b5d52984eda37585bf13023eb68890d2964dd534abc`, with its 16-file evidence manifest `f85b7a1d66d41c3da25582edfdd57b5475ebe7dfd8a16e6f4b498f478a369007`. This manifest intentionally includes the report through `../proof-referee-2.md`; that exact file is checked, not discarded.
- Root's independent candidate acceptance is `7529a7970a9d28f3e27371bbb16f2fac6481029c886242b9f1a79a0fe3f9cfcd`. Its complete 14-file outer manifest, `b63fbe9ff7786eb5c42966a6dbd75bd3f5a02444605a052addd8b9ba3a7ebd92`, includes the preparer's original nested manifest. Both current metadata wrappers match that acceptance.

I read both full final reports and the current candidate metadata. Their earlier publication-documentation finding is closed by the exact historical README archive and truthful current guide; Linux remained pending in the actually checked candidate. Source plans and earlier reviews retain their dated historical wording. This audit does not rewrite those documents.

## Actual job, Comparator and kernel execution

The project job is `103639374192`; standalone checker controls are job `103639374095`. Every selected job step succeeded. The project job actually ran v0.4 metadata validation with coverage of eight declarations, fresh dependencies, sandbox controls, separate Challenge and Solution builds, two exports, statement comparison and Lean's default-kernel replay. The main command uses `systemd-run --user --wait --pipe --collect`, `RestrictAddressFamilies=~AF_UNIX`, a clean `env -i`, the pinned exporter and strict Landrun wrapper. No skip-kernel flag is present.

The new trusted-input directory is recorded in `control-verification.json`; it is a fresh `.verification-tmp/nla-fresh-proof-…/project` directory. The Challenge graph completed 1916 jobs and the Solution graph completed 2918 jobs. Only the eight deliberately admitted Challenge contracts warned. Definitions, Proof and Solution were built from the candidate; the Solution phase had no warnings. The raw log records default-kernel acceptance, Comparator acceptance and exit status zero.

All **17 actual candidate transitive axiom reports** contain exactly `propext`, `Classical.choice` and `Quot.sound`, corresponding to nine explicit internal kernel checks and eight public checks. No definition exception is configured. The eight compared and kernel-replayed exports are:

- `NLA.IV06.eigenvalue_determinant_semantics`
- `NLA.IV06.family_and_determinant_semantics`
- `NLA.IV06.witness_eigenpairs`
- `NLA.IV06.witness_separators`
- `NLA.IV06.connected_component_intervals`
- `NLA.IV06.four_components`
- `NLA.IV06.counterexample`
- `NLA.IV06.not_componentBoundConjecture`

The actual imported implementation contains no `sorry`, `admit`, custom axiom, unsafe declaration, native-decide proof or Challenge import. The default-kernel replay and axiom rejection gates act on the exported theorem closures, not merely on source-text searches.

## Controls that actually executed

The standalone controls and the controls immediately preceding IV-06 verification independently ran the same required cases. Their complete raw logs are retained; they were not skipped or replaced by a local simulation.

- Both build and export modes used private user, PID, mount, network, IPC and UTS namespaces, non-root UID 1001, no effective capabilities and `no_new_privs`. Outside writes, truncation, creation and symlink-write escapes were denied. Only the designated build `.lake` fixture was writable; export was read-only. Host-parent process lookup/signaling, host loopback access and AF_UNIX socket creation were denied. Four unsupported or unsafe wrapper-option requests failed with exit 2.
- The nested `bwrap` executable actually ran, then failed to create its UID map. This prevented reaching the inner write. The log's generic nested-write rejection line is **not** interpreted as evidence that the inner write executed.
- Three raw default-kernel cases accepted the honest inductive/quotient fixture, rejected an invalid raw proof, and rejected a quotient constant mismatch through the quotient post-check.
- Five real Comparator fixtures exercised acceptance and statement/kind/custom-axiom rejection. Each built and exported both Challenge and Solution. The separately added `sorryAx` and nontrivial native-decide fixtures were actually rejected with exit 1 for their prohibited axioms.

## Pins, dependency cache and checker sources

The actual environment uses Lean 4.33.1 on Ubuntu Linux and Go 1.27.1. Both jobs built the pinned Comparator, exporter and Landrun. Their tool receipts match. The complete **58-file** Forsythe source lock is preserved and rehashed at `8d1b0c0545a77b40245e84705aa7d273e6c81e62`; all source sizes and SHA-256 values agree. The exact noninteractive probe adaptation matches the Linux receipt. Harness, source lock and entrypoint bytes equal the audited infrastructure revision `214c142d6bfe0f0c338808f188062acbbad0fb19`. The workflow and relevant shared tools are unchanged from the candidate's upstream base.

The fresh dependency log records all **10 exact package clones/checkouts**, including LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The normal Mathlib cache command actually decompressed **8690 files**. Thus this is fresh project verification with pinned public dependency artifacts, not an assertion that every dependency was compiled from source. Workflow action caches are disabled. No local dependency cache was copied, downloaded or rebuilt for this operational review.

## Mathematical and LeanCert scope

The matched result is the full original negative component-bound theorem. It concerns the entire independent-entry real interval matrix box, actual nonzero real eigenvectors, the real subtype topology and the actual `Cardinal` of `ConnectedComponents`. The dimension-three source box has at least four actual components; no finite-component premise, exact-four claim or complete endpoint classification is substituted.

The only interval calculation is explicit kernel LeanCert `(-18 : ℝ) < 0` on the singleton `[0,0]`. Exact determinant identities and universal affine bounds exclude all three separators. Actual connectedness and cardinal arguments then give the full negation. Both final referees inspected and independently repeated the retained checker and its actual consumer chain; their exact source and evidence bytes match the Linux snapshot. The actual Linux rebuild retains the same numerical theorem and standard-three closures. This operational audit did not perform a third local mathematical re-elaboration or rerun their Boolean checker.

The current guide retains Matthew J. Colbrook's mathematical credit and George Stepaniants's separate AI-assisted formalization credit with the Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA. No George email is added.

## Original evidence and limits

| Original artifact | GitHub artifact ID | Verified SHA-256 | Extracted files |
| --- | --- | --- | ---: |
| `lean-checker-controls` | `10307428276` | `3c405009704da285d05939461fec1bb38f8a8fe4f9e7f52339f2da4f689c0529` | 10 |
| `lean-IV-06` | `10307218980` | `bbe96d9e07020993524329a33ea366ff0ab85707d666b0974bd06c667af0e005` | 13 |

Both original artifact ZIP digests agree with GitHub's artifact metadata **and** the upload-digest lines in the respective raw job logs. Every extracted file is byte-identical to its ZIP entry. The complete original run-log ZIP contains 152 files; its locally retained digest is `022aa9a6df6fc50353ba5a9644ef13a5652a21426848c450d7950e5259bd4068`. GitHub does not supply a published digest for that separate log archive, and none is claimed. The companion [permanent-ID run 34725713642](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713642) succeeded at the same commit; its original metadata and raw job log are retained.

The other project jobs in this full run also report success, but their mathematical artifacts are not independently audited by this IV-06 report. A successful prior project or shared control run is not substituted for the actual IV-06 result.

One preparation-only inventory check initially omitted the root referee manifest's explicitly external report path. The failed audit script and diagnostic are retained; correcting the inventory to **include and hash that exact report** passed without any candidate change or relaxed omission. No candidate proof or actual Linux failure is hidden by that correction.

The outer manifest binds **347 files**, with **348 total files including itself**, retaining all nested manifests. Only its own exact path is excluded from its listing. `verify_evidence.py` rechecks the complete inventory and hashes offline. The original evidence is retained under `verification/linux-2026-09-12/` without changing any of the 200 verified inputs. Publication metadata, canonical promotion and any upstream PR remain separate root-controlled actions.
