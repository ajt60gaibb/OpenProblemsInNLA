# Independent final assembly and canonical source review 1 — 2026-10-18

Reviewer: `/root/solved_inventory`, an OpenAI Codex AI agent, independent of the Final/wrapper author. **APPROVE** the exact full-target final assembly, wrappers, statement identity and copied-source boundary below. This is local source and kernel evidence, not Linux/Comparator acceptance or external human peer review.

| Reviewed input | SHA-256 |
| --- | --- |
| Shared and canonical `Final.lean` | `31ecd9e91c05d3afb0dc8feadf49019c6b251e016eb65e829af8953e6c207cbf` |
| Canonical `Solution.lean` | `128b8992fa2e672e1b6c7894c67f61f540c746db616864b787bd1dbcf20eb4a7` |
| Canonical `Identity.lean` | `bb3dea1091354721337f9ffa7e8b8f0f3d8de8bdf51dc91777bf61ca5afd48ea` |
| Proof/source/export lock | `7706310ea6711a7b50200f53bfc0661ec613f16dd885e04e36078e4774a46f27` |

I independently read the complete Final and wrapper sources against the unchanged original, numerical specification, live statement and separately frozen statement. The exported theorem has the literal type `NLA.Statements.TR14.Target` with no extra parameter or premise. It quantifies every order m >= 3, dimension n >= 2, complex moment vector and natural width, retaining zero and exceptional data and arbitrary mode-dependent ordinary factors.

For nonzero data, `exists_chart_two_symmetricWidths` supplies one actual chart z and actual monic least-apolar polynomial g. The ordinary witness is transported forward to the moments in that same chart; the unrestricted lower theorem is instantiated with the actual returned minimality data. Both candidate symmetric widths already refer to the original Hankel tensor. Selecting their minimum and padding to the given ordinary width proves the exact requested width, without any width/dimension bound or Vandermonde-only restriction. For zero data, an actual symmetric width-zero decomposition is padded. The converse absorbs a symmetric scalar into a mode using the positive order. There is no unproved lower-bound hypothesis, chart-existence oracle or stronger-rank-formula substitution in the final export.

`Solution.lean` directly wraps the proved full theorem. `Identity.lean` proves `rfl` equality of live and separately reviewed frozen full statements. Challenge retains its deliberate comparison placeholder and is absent from the Solution import closure. Comparator selects only `NLA.TR14.target`, has no definition holes and permits exactly `propext`, `Classical.choice`, `Quot.sound`. This is an inspection of the Comparator configuration; its actual isolated Linux execution remains a separate gate.

The independent static audit checked all 78 source/destination copies (76 proof modules plus two statement/infrastructure modules), all eight locked exports, closure of local imports, canonical and shared dependency revision/URL sets, clean cached dependency revisions, and the frozen statement. Every check passed. The final manifest legitimately changes its package name, direct-dependency ordering and inheritance fields relative to the shared project; the actual dependency revisions and URLs match. All canonical-original TR-14 immediate artifacts and the registry are byte-identical to published base `d250bd50d602ec7fd6e55bb4fd19494c5e19b045`; the permanent canonical path is `tensor-computations/TR-14/README.md`. All seven historical boundary source copies match. The historical pre-Solution lakefile digest is reproducible from retained `reviews/boundary-review-3-evidence/source/lakefile.toml.txt`; the current addition of Solution is an intentional later configuration phase.

Direct fresh re-elaboration passed for six exact canonical inputs: Infrastructure, the live statement, Final, Reviewed, Identity and Solution. A seventh independent consumer checked both full exports are actual theorem constants whose literal type is the unchanged Target, transported the proof to the frozen Target and asserted kernel trust/printed axioms for the ordinary-to-symmetric theorem, shared Target, canonical Target, identity and frozen Target. Only the three permitted standard axioms were observed. Source and lock hashes were unchanged afterwards. The direct replay used new output objects for those six sources and its consumer, while explicitly copying and digest-recording 75 existing shared support objects. This is not described as a fresh full-closure replay. The completed independent 78-source full replay by `/root/fr05_statement` provides that broader check, and `/root/lean_verification` retains its additional full audit separately; this review also separately replayed the full 60-source root-support closure in [ROOT_SUPPORT_SOURCE_REVIEW_1_2026-10-18.md](ROOT_SUPPORT_SOURCE_REVIEW_1_2026-10-18.md).

This reviewer authored `NormalizedOrdinaryLower` and the ordinary/context/graph support modules listed in the evidence. Those modules are explicitly excluded from independent source approval here. Their imported proofs are mechanically checked, and separate other-agent reviews cover their independent source and fidelity approval. This report approves the other-author Final assembly and canonical integration, not the reviewer's own lower proof.

Evidence: [direct kernel result](verification/inventory-canonical-final-review-1/result.json), [independent original preservation](verification/inventory-canonical-final-review-1/original-preservation.json), source snapshots, dependency/object digests and seven raw compile logs in the same directory. Reproduce the source-copy and direct compile checks from the repository root:

```bash
python3 docs/lean/proofs/TR-14/verification/check-inventory-canonical-final.py
```

The driver snapshots the current reviewed source/lock state. Its result binds exact bytes; a later run refreshes the current-state report rather than reproducing historical source bytes automatically. Original preservation can be reproduced by comparing `git show d250bd50d602ec7fd6e55bb4fd19494c5e19b045:<path>` with the six exact recorded current paths and applying the boundary lock to its seven recorded source/package pairs.

The proof-source lock intentionally excludes mutable README/metadata/reviews/evidence; this report makes no final hash approval of that prose. At review time the README truthfully said actual Linux verification was pending and the canonical problem remained Solved; metadata was corrected to `whole_problem_verified: false` pending that gate. Later final audit narration and actual Linux receipts require their own review. The exact approved mathematical source bytes may proceed to that verification gate.

Direct result SHA-256: `8ce834eac9e8f828c0ecfac93e88370e0b907978be713801052a44f7e59c16ec`.
Original preservation result SHA-256: `6d76c68fba18c40f10537510ee06890806c79b127697d603941e8517bca7526e`.
