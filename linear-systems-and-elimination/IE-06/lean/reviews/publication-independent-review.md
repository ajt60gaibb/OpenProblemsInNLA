# Independent publication review — IE-06, 6 October 2026

Reviewer: `/root/infrastructure`, a Codex AI agent independent of the publication-documentation and canonical-page authors. Scope: publication wording, authorization and attribution, frozen proof/evidence identity, original-target preservation, and verification claims. Verdict: **approved for publication within the explicitly documented local-verification scope**. This is not human peer review, author endorsement, a new Lean build, or an authoritative Linux run.

## Proof and evidence identity

I independently read the applicable root AGENTS.md, CONTRIBUTING.md, docs/lean/README.md, docs/lean/REVIEW.md, resolution procedure, manifest/schema and existing CI/harness requirements. Permanent IE-06 identity, path, original target, and unchanged acceptance safeguards are preserved.

The immutable proof commit `263a215acd295a260dec7a75ff6bebebb9789df9` contains exactly 1,133 package files: all 1,132 entries in the original delivery inventory plus that inventory itself. I checked each retained entry against the Git object at that commit, including SHA-256 and byte count; none differ. The copied `verification/prepublication-delivery-manifest.json` is byte-identical to the original inventory, SHA-256 `f25c6866954b7ae3b49ba52e9b27604486c3d8cf1ec3ebb9a7c694e332de0687`.

All 121 accepted final-validation inputs, including all 114 Lean source modules, match the current publication worktree, the immutable proof commit, and the accepted run's retained snapshot. The accepted receipt remains SHA-256 `50fbaf7b84715f7fdf4e28d3813abb4c2f7837514f9322c255cb99fa1b0952e2`. Historical execution receipts and source provenance have not been rewritten. The six exact targets, empty definition-hole list, dependency pins, and foundational-only axiom policy are unchanged. I also checked that the eleven immutable proof-commit links in the current canonical page, resolution entry, and PUBLICATION.md resolve to actual Git objects at the cited revision; network publication of those objects is a later action.

## Publication wording and source attribution

The current documents accurately attribute the permission report to the maintainer. They do not claim that John Urschel reviewed or certified the Lean source, endorsed the AI-agent reviews, or participated in the formalization. `author_endorsement: other` is used only for the Urschel source and explained as publication permission, not correctness endorsement. Mathematical credit, original conjecture credit, generic IE-04 credit, and separately licensed adopted proofs remain intact.

PUBLICATION.md preserves the historical RRF adaptation records and identifies the current maintainer authorization as applying to the prepared package. It explicitly avoids inventing an upstream Apache release or attributing that source to Urschel. This review verifies the accuracy and separation of those recorded roles; it is not an independent legal opinion about source ownership.

The current docs retain the successful local macOS scope: fresh source compilation, the 3,229-declaration axiom audit, six actual Comparator target comparisons with their axiom checks, and required negative controls. Trusted pinned compiled dependency caches remain disclosed. Authoritative non-root Linux isolation, full exporter-based Comparator execution, and separate raw-kernel replay remain pending. Publishing a branch does not certify those gates. Historical prepublication flags are correctly distinguished from current authorization.

The initially stale sentences about awaiting a conversation/authorization were reported to the parent and corrected. Statements that canonical README/TeX/PDF were unchanged now refer specifically to the earlier proof-development phase; publication changes are explicitly acknowledged. No unresolved material wording finding remains.

## Original target and canonical publication

The original Context and notation, complete Problem statement, Scope of the resolution, and References sections are byte-identical to the immutable prepublication canonical page. The new evidence section is additional. The actual standard-Gaussian law, exact Schur-stage convention, input normalization, universal treatment of ties, real positive exponent quantifier, and limit are not altered. The registry still maps IE-06 to `linear-systems-and-elimination/IE-06/README.md`; the canonical page and resolution archive retain **Solved** and expressly defer **Lean verified** promotion.

The canonical evidence lists all six declarations, immutable proof and audit links, exact toolchain/dependency pins, actual checks, and reproduction/trust limitations. The source agent reported successful permanent-ID validation for 217 IDs, 17 ID tests, math formatting, unchanged catalog output, standalone XeLaTeX compilation with no overfull boxes, and visual inspection of all three final PDF pages. I independently read the canonical author’s final review and its six-command transcript (`checks.json`, SHA-256 `9ef9fc0d0f086558474928e791f361f6141ce377affd6894fa29544a1ddfe489`): all six recorded exits were zero, including ID/catalog/format checks, ID tests, diff checking, and standalone XeLaTeX. The parent also reported the 30 metadata-selection tests and 12 shared-harness tests passed. I inspected the actual canonical Markdown diff and independently checked the final Markdown/TeX/PDF hashes below; I did not rerun rendering or independently view all PDF pages. Those execution/visual reports retain their own authorship and scope.

## Reviewed publication bytes

Paths in this table are relative to `IE-06/lean/`.

| File | SHA-256 |
| --- | --- |
| `PUBLICATION.md` | `36c9c6b58d2f16b2ba25e43a286642cc78bde86c485175e35be0257469b40027` |
| `README.md` | `5d4fb5ecc467192871a128bb0153f76e23d8cc8e61825d386ac637a9aaa0084c` |
| `PROOF_STATUS.md` | `8a8446ad7bd7fde33a0a8b0502e27d6fb76909e2b3cd51eccde84075d1ba1db9` |
| `INFRASTRUCTURE.md` | `6193b46380c928423b7c8dc77b4db2a0679936b3956018a67479e7b7ba041287` |
| `formalization.yaml` | `ed8da45db122275e0b1af9bd7521b34076321bdf9a241d7a637e560800c926e7` |
| `verification/SUMMARY.md` | `5b93e88c84670c18476cfe2170ca274c8a74e6e8ee3aa1a0b01c8ad19dc77c41` |
| `reviews/publication-canonical-review.md` | `da5a6683789b69677bc95c10917827ce54afb4cbd0e5061b0a15a26c758c243a` |
| `verification/prepublication-delivery-manifest.json` | `f25c6866954b7ae3b49ba52e9b27604486c3d8cf1ec3ebb9a7c694e332de0687` |
| `verification/local/attempt-0i_0ibma/result.json` | `50fbaf7b84715f7fdf4e28d3813abb4c2f7837514f9322c255cb99fa1b0952e2` |

Canonical/supporting files relative to the repository root:

| File | SHA-256 |
| --- | --- |
| `linear-systems-and-elimination/IE-06/README.md` | `c2f740cc2da336681b0b259951d38f314044ca0bb1d1c8b8ab02986629b265b1` |
| `linear-systems-and-elimination/IE-06/problem.tex` | `370722a7a2f065aa6d1e4f0a9a0e8f9bae18e9d4d70d5cc9ab1d552045127510` |
| `linear-systems-and-elimination/IE-06/problem.pdf` | `07ce3f45da67805648fb94ed3cfe822d0c8dcbfaeb3eb243051b36cf8974339e` |
| `RESOLVED.md` | `f64370e5789fb86eef07546595cb074791a89e40eb4771a2fb383bb316846560` |

The current delivery inventory is to be refreshed after this report and the canonical author's report are added; this review does not pre-certify that future inventory. The parent must retain its final integrity check. No commit, push, remote CI run, or new proof build was performed by this reviewer. The existing push/PR workflow remains unchanged and can supply subsequent exact-revision Linux evidence; only its actual result can discharge that remaining gate.
