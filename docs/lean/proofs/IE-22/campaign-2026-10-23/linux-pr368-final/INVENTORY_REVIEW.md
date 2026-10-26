# Independent final IE-22 promotion Linux receipt review

**APPROVE the authentic final promotion receipt: 313/313 checks pass.** Reviewer `/root/inventory` independently retrieved the original ZIP, raw job log and GitHub metadata; the reviewer authored no IE-22 proof or statement source. No canonical package was edited, and this is no new local Linux, Lean, Comparator or sandbox run. A second execution of the portable offline auditor, in a fresh output directory, gives a byte-identical JSON report.

The successful actual [PR 368 run 40324391261](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40324391261), [job 121577384016](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40324391261/job/121577384016), completed at **2026-10-26 12:47:34 UTC**. Its reviewed head is `799077c8d8b10bd9e266185a9ecc0c4c06abccd3`. The separately fetched raw checkout log—not an inference from head metadata—records fetching/checking out `refs/remotes/pull/368/merge` and `git log -1 --format=%H` returning:

`12bf4d153f725cbc326d40d694c1993d6f098eb4`

The actual fetched Git object has ordered parents base `35b0d5c87779483beaa324b1bc7af4ba9e55ca18` and that head. PR metadata corroborates the actual merge. The harness result records that same executed merge.

Original [artifact 12650299744](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40324391261/artifacts/12650299744), `lean-IE-22`, is **18089 bytes**, SHA256:

`13ce36ea489d7aebaa244527c0a64c72c6fdd4295440940e1bf5d5a2e812afee`

The independently downloaded original ZIP agrees with both GitHub artifact metadata and the raw upload's ID, digest, size and URL. ZIP CRC and all 15 ordinary safe unique members pass. This archive was not reconstructed or recompressed. The independently fetched raw decoded UTF8 job log is **100584 bytes**, preserving its BOM and ANSI escapes, SHA256:

`93b174de352003cecc20217947754784aa80bd1a8028dc8962b67a84e70e364a`

Its deterministic retained gzip SHA256 is `2f86010038e7e5c10a25da76349fc183b84092ea06a83ae1457af03fcbbbff51`. Every artifact log command and every nonempty output line is checked against the separately retrieved raw job log in order, with the actual success/rejection exit statuses. Retained API metadata and `retained/RETRIEVAL.json` document independent connector acquisition.

**All 59 canonical package files match exactly at head, actual merge and the current worktree.** All 27 Lean files remain byte-identical to initial accepted head `06f31cdd4f76d90c7590b5582b8db4975a0055d8`. All 23 shared copies, including all 19 proof modules, remain byte-identical to the independently approved complete source `353ebcfcbbcfc08184c32f391ecb6068c7d9098f`. The exact difference from the initial 54-file receipt is five added verbatim review Markdown copies and four changed descriptive/metadata files (`README.md`, `BLOCKERS.md`, `STATEMENT_REVIEW.md`, `formalization.yaml`). Acceptance configuration, frozen Challenge, live/frozen Target, proofs, wrappers and dependency pins are unchanged. The final 59-file map also matches the reviewed promotion input lock.

The actual receipt reports `comparator-accepted`, `kernel-checked`, default profile. Comparator exports exactly these three proved theorems from both reference and solution modules, with no replaceable definitions:

- `NLA.Proofs.IE22.uniform_squared_upper`
- `NLA.Proofs.IE22.near_sharp_unit_row_witness`
- `NLA.Proofs.IE22.target`

The raw default-kernel replay accepts the solution and Comparator reports `Your solution is okay!`, exit 0. The deterministic generated consumer checks actual theorem kind, `#assert_trust kernel` and transitive axioms for each export. Its independently reconstructed SHA256 equals the actual receipt: `af6a22935778c63f5d9639721a57cef86e567b1daa28a9e096808981315b1e81`. The consumer actually executes successfully under `RestrictAddressFamilies=~AF_UNIX`; all three printed axiom sets are exactly `propext`, `Classical.choice`, `Quot.sound`. The reconstructed consumer is labelled reconstructed; CI did not upload it as a separate source member.

All actual builtin kernel controls (honest inductive/quotient acceptance, invalid proof rejection, quotient mismatch rejection), five Comparator regressions, build/export sandbox modes, four invalid sandbox-option controls, `sorryAx` rejection and native evaluation axiom rejection pass. Both sandbox modes demonstrate denied outside writes/truncation/symlink escape, private namespaces, isolated host process/network resources, denied AF_UNIX sockets, no effective capabilities, `no_new_privs` and rejected nested namespace writes. Only designated build `.lake` writes succeed; export remains read-only. The separate checker-controls job is skipped, but these controls actually run inside this successful project verification job and are retained in this artifact.

The actual receipt and raw logs bind official Linux Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, all ten exact dependencies including Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, Go 1.27.1 and the locked Forsythe checker/exporter/strict sandbox source at `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. The unchanged verifier/workflows and source lock SHA256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` are checked. Binary hashes remain those recorded by this real run; they are not substituted from a local build.

The final package's Lean-verified metadata is consistent with the accepted unchanged full Target. Mathematical-fidelity, preservation and promotion reviews remain separate from what this artifact proves. The [initial receipt](../ie22-linux-ci/INVENTORY_REVIEW.md), complete source/package reviews and [corrected promotion review](../ie22-promotion-review/inventory/REVIEW.md) retain their original scopes. No external human endorsement or main-branch publication is inferred here.

Reproduce offline, with the immutable objects available and the repository's canonical package matching final head 799077c8:

```bash
python3 reviews/2026-10-23-solved-lean/ie22-linux-ci-final/audit_linux_ci.py \
  --repo /path/to/OpenProblemsInNLA \
  --output /tmp/ie22-final-linux-review
```

The default evidence is the auditor's sibling `retained/`; `--evidence` selects another retained bundle. Fresh output `/private/tmp/nla-ie22-final-ci-inventory-replay-40324391261` produced a byte-identical 313-check JSON. Report SHA256 `81825a0cf1cea1e65317ed55d89a2dc2f78a740234ee2b6e5b1307a37c65b84e`; portable auditor SHA256 `bd3f1868d31dda6495d1ac5078281a4b994b45d98fae34022233f184fc5efc34`. JSON retains every check, both input maps, the five additions/four metadata differences, exact source-copy bindings, all member hashes and the actual tool receipt.
