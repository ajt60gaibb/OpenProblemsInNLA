# Independent IE-22 Linux receipt review

**APPROVE** the original PR 368 Linux receipt for all three reviewed IE-22 endpoints, including the literal unchanged full Target. The offline evidence auditor passes **220/220 checks**. Reviewer `/root/inventory` authored none of the IE-22 proof or statement sources and independently retrieved the original artifact and raw job log through the GitHub connector. No canonical package or proof source was edited during this audit.

This is an independent audit of actual GitHub Linux execution evidence, not a newly performed local Lean, Comparator, sandbox or Linux run. English-to-Lean fidelity and original-source preservation were separately approved in the frozen [complete-source review](../ie22-upper-review/SOURCE_REVIEW_INVENTORY.md) and [canonical-package review](../ie22-package-review/PACKAGE_REVIEW_INVENTORY.md).

The actual [run 40255260833](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40255260833) and [project job 121355717650](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40255260833/job/121355717650) completed successfully at **2026-10-26 01:47:55 UTC**. Raw metadata is retained unchanged as JSON response content. The checkout log—not an assumption from the PR head—records fetching and checking out `refs/remotes/pull/368/merge`, then `git log -1 --format=%H` returning:

`88b9366e6cfcef7e60a2d740ff8a7101399bf1a8`

The immutable Git object has ordered parents base `35b0d5c87779483beaa324b1bc7af4ba9e55ca18` and reviewed PR head `06f31cdd4f76d90c7590b5582b8db4975a0055d8`. The independently fetched PR metadata corroborates that merge. **All 54 package inputs, including all 27 Lean files, are byte-identical at head and executed merge**, with exact file-set coverage and hashes matching the actual harness receipt. All 23 shared statement/proof copies match the independently approved complete source checkpoint `353ebcfcbbcfc08184c32f391ecb6068c7d9098f`, including all 19 proof modules. Challenge remains exactly the preapproved SHA `bd20cbb3d4495ff312192ab29fe7722463c8b74861f0a00ae83dd9b98ed4ec79`.

The **original** [artifact 12622124226](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/40255260833/artifacts/12622124226), named `lean-IE-22`, is **18506 bytes**. Its original ZIP SHA256 is:

`006c1919528d800bc18903d9f7f99633408cd0178f03d429bf57bd3489ef5468`

That digest and size independently agree with GitHub artifact metadata and the raw job's upload lines, which also bind the artifact ID and URL. ZIP CRC checks pass; all 15 members are ordinary safe unique paths. The retained archive is the downloaded original ZIP, not a reconstructed archive. The separately retrieved raw UTF8 job log is 106057 bytes, including its initial BOM and ANSI escapes, SHA256:

`d679fea63d8044b0051bdafa2b53ff004a063f7395b187605a191a4952730d27`

Its deterministic retained gzip has SHA256 `15de0e6067b394b56e91b88cb6a9949f83670078a50b552b0ee49d483259b1c1`. Every nonempty artifact-log output line occurs in order in that separately fetched raw job log; every recorded command and success/rejection exit status is checked. Retrieval provenance is retained in `retained/RETRIEVAL.json`.

The actual receipt reports `comparator-accepted`, `kernel-checked`, default verifier profile and the executed merge above. Actual Comparator exports from **both** Challenge and Solution select exactly:

- `NLA.Proofs.IE22.uniform_squared_upper`
- `NLA.Proofs.IE22.near_sharp_unit_row_witness`
- `NLA.Proofs.IE22.target`

`definition_names` is empty; the only permitted axioms are `propext`, `Classical.choice`, `Quot.sound`. The raw Comparator log records Lean's default kernel accepting the solution and `Your solution is okay!`, with exit 0. The independently reconstructed deterministic `ProofTrustAudit` consumer has the actual receipt's SHA256 `af6a22935778c63f5d9639721a57cef86e567b1daa28a9e096808981315b1e81`: it requires each selected declaration to be a **proved theorem constant**, applies `#assert_trust kernel`, and prints its transitive axioms. The actual consumer log records successful execution under `RestrictAddressFamilies=~AF_UNIX`; all three printed axiom sets are exactly the standard three. The reconstructed source is explicitly labelled reconstructed, rather than represented as an additional file uploaded by CI.

The actual project job also passes all three builtin kernel controls (honest inductive/quotient proof accepted, invalid raw proof rejected, quotient mismatch rejected), all five Comparator regressions, real build and read-only export sandbox modes, four invalid sandbox-option controls, rejection of `sorryAx`, and rejection of `checked._native.native_decide.ax_1_1`. Both sandbox modes demonstrate filesystem write denial, namespace separation, inaccessible host process/network resources, denied AF_UNIX sockets, no effective capabilities, `no_new_privs` and rejected nested namespace writes. The designated build `.lake` remains writable and export `.lake` remains read-only. The separate `checker-controls` workflow job is skipped; these controls genuinely ran within the successful IE-22 project verification job and are retained in its artifact.

The receipt and raw bootstrap/dependency logs bind official Linux Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`, all ten manifest pins, Go 1.27.1 and the locked Forsythe checker/exporter/strict sandbox source at `8d1b0c0545a77b40245e84705aa7d273e6c81e62`. Source lock SHA256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` matches both receipt fields. The published verifier/workflow sources are unchanged. The permanent registry, original canonical README and unchanged mathematical Target remain preserved; the tested package still honestly says Solved/pending verification at this prepromotion commit.

Reproduce the offline audit with any local checkout containing these immutable Git objects:

```bash
python3 reviews/2026-10-23-solved-lean/ie22-linux-ci/audit_linux_ci.py \
  --repo /path/to/OpenProblemsInNLA \
  --output /tmp/ie22-linux-independent-review
```

The default evidence path is this auditor's sibling `retained/`; `--evidence` can select a retained bundle elsewhere. The same auditor was run against the owned IE-22 worktree and then the original checkout with a fresh `/private/tmp/nla-ie22-inventory-ci-replay-40255260833` output. Both runs pass 220 checks and produce **byte-identical JSON reports**.

Exact report SHA256 `61549bd6cf62b9d34518a4c959403c0eadb86287076dcdf4d59c707fb4a5c8b6`; portable auditor SHA256 `06ba75e70dc083db0abef0f17ada463a7a04d88854217292039e81b1af58a1c3`. The JSON additionally records each artifact-member digest, all 54 input hashes, all 23 copy bindings, every check and the tool receipt. This approval binds that immutable source/evidence; it does not itself change a canonical status, merge a PR or assert publication on main.
