# Exact-head delta review of PR93 and PR103

**Verdict: PASS.** The complete mathematical PASS verdicts and final-PDF reviews carry to both updated heads:

| PR / retained target | Previously reviewed head | Latest reviewed head |
| --- | --- | --- |
| 93 / RA-12 | `c797aee814c8bebe4452329c93f5d84fd9c41f1f` | `d9e25009e3ce65cf864002354830bdcc286f7252` |
| 103 / RA-10 | `6f5861fa392db467dc23abd096a02a08573146b8` | `494438ee01cde9ad5706537b026d85b9aab03b1b` |

Both are ordinary two-parent merges of the exact previously reviewed head and accepted main `87366c62d3b5c47d170f747b1cb40ab38d501013`. I compared the merge trees against both parents and the original contribution path sets, avoiding attribution of already accepted upstream work to either submission.

## Mathematical and document continuity

For **each PR**, all six files in its canonical directory are byte-identical to the reviewed head: `README.md`, `problem.tex`, `problem.pdf`, `solution.md`, `solution.tex`, and `solution.pdf`. Therefore the complete canonical target, hypotheses, status scope, author attribution, historical result attribution, all proof equations, and both final rendered PDFs are unchanged.

- **RA-12:** the full two-tail relative Gaussian trace comparison, including the stated threshold endpoint, retains the PASS in [the full maintainer review](../audit-root/PR-93.md). No claim about optimality or the separate RA-13 target was added.
- **RA-10:** the complete arbitrary-PSD nuclear-error transfer theorem with universal constant eleven retains the PASS in [the full maintainer review](../audit-root/PR-103.md). No commutativity, ordering, nonzero-tail, or normalization restriction was introduced.

The full archived proof candidates, original canonical snapshots, existing independent mathematical reviews, packaging reports, existing source/PDF manifests, and earlier supporting/network records retain their exact bytes. The entire previous reference README is retained as a prefix; only the dated integration section is appended. The existing optional-contact solution-template change and the existing RA-10 pagination rule are also unchanged from their reviewed versions.

All **four final PDFs / seventeen previously inspected pages** are identical: RA-12 has a three-page canonical PDF and five-page proof; RA-10 has a three-page canonical PDF and six-page proof. Their prior full visual/content QA therefore applies directly. No new PDF rendering was necessary.

| Final PDF | Current and previously reviewed SHA256 |
| --- | --- |
| RA-12/problem.pdf | `26586e19d4cfe67f3697423b1231cdfc900551be96d1b883a26ad5b8a96f1e9e` |
| RA-12/solution.pdf | `09e57be7f12d01e61197bd109d7eba463cd3cfc6b909e23f2c607779a9763da9` |
| RA-10/problem.pdf | `0866178c7c12417e071dfae75c1a250b46544a0f6ecc45e6221f57bbf439d0f9` |
| RA-10/solution.pdf | `0407010b8960d65c3c04768234c35859d3b96fa354bda3e67fc18395144dc0ed` |

## Genuine new delta and preservation

For each reference package the only new files are:

- `verification/main-integration-2026-09-11-87366c6.md`
- `verification/main-integration-2026-09-11-87366c6.json`
- `verification/verify_main_integration.py`

The reference README gains a link to that record. Other merge-resolution changes are the regenerated count/index files and the combined `RESOLVED.md` entry. I read both integration descriptions, manifests, and the complete new verification program. They introduce no mathematical premise. The program only reads local files and invokes read-only Git queries; it does not access the network, alter artifacts, or execute a GitHub workflow.

Independent exact-tree and fingerprint checks establish, for each head:

- All **203** permanent ID/path mappings are identical to both parents.
- The owned canonical page is identical to the reviewed head; all **202 other** canonical pages match accepted incoming main.
- All **1,260 incoming proof/evidence blobs** match accepted incoming main, including prior contributors' separate proofs and evidence.
- Every claimed historical fingerprint matches the corresponding recorded prior-parent file, and every current fingerprint matches the latest head. Historical reference-README fingerprints are deliberately distinct from the current appended README fingerprint; neither is mislabeled.
- All accepted upstream resolution headings survive. The combined resolution text retains earlier attributions and adds only the already-reviewed owned result and its corresponding historical clarification.
- Numbering validators, catalog generator, test suite, and numbering workflow match accepted main.
- Direct canonical-metadata counts match each integration record: PR93 has 67 Open, 74 Partially resolved, 1 Solution claimed, and 61 Solved; PR103 has 68 Open, 73 Partially resolved, 1 Solution claimed, and 61 Solved. Both still retain 203 entries.

The new JSON fields mentioning AA-01 are inactive generic-script bookkeeping for these RA-only records. AA-01 and its incoming artifacts are independently verified unchanged; those fields do not assert that either RA submission edited or reviewed AA-01.

## Reproduction and evidence

`check_pr93_103_delta.py` independently compares Git trees and recomputes SHA256/size fingerprints without importing the submitted verifier. **3,104/3,104 checks pass**, recorded in `PR93-103-delta-checks.json`.

Both new submitted verification scripts were read before execution, then run in detached worktrees belonging to a separate temporary clone:

- PR93: PASS for ten unchanged protected artifacts plus the original README prefix, 202 incoming canonical pages, 1,260 incoming proof/evidence blobs, 203 IDs, and current fingerprints.
- PR103: PASS for twelve unchanged protected artifacts plus the original README prefix and the same incoming preservation checks.

The independent local rerun additionally validates IDs against the precise incoming commit, regenerates catalogs, runs all 17 permanent-ID safeguard tests, and checks that the working tree remains clean. Results are recorded in `PR93-local-integration-checks.json` and `PR103-local-integration-checks.json`; `rerun_local_integration_checks.py` reproduces these isolated checks.

This delta review carries the existing rigorous mathematical/primary-source conclusions only because the complete proofs and targets are unchanged. It is not a new proof-assistant certification. No shared integration checkout or remote state was modified; no workflow approval, workflow execution, publication, or merge was performed. CI and merger authorization remain separate from this mathematical/source verdict.
