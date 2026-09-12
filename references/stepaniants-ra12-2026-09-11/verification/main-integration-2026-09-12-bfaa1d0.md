# RA-12: integration of accepted main and PR #93 disposition

Checked on 12 September 2026 UTC (11 September in the author's local time zone).

## Review and workflow status

The latest maintainer review on [pull request 93](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/93), submitted at 00:04:47 UTC, explicitly gives the complete mathematical argument PASS. It reports that the previously reviewed commit `c797aee814c8bebe4452329c93f5d84fd9c41f1f`, including the full proof and solved canonical entry, is already on `main`. The earlier complete review also gives PASS. There is no outstanding request to alter the proof.

The remaining open pull request concerns the later integration-provenance files. The [identified workflow run](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/34657927827) belongs to head `d9e25009e3ce65cf864002354830bdcc286f7252`; its API status is `completed` with conclusion `action_required`, meaning the fork workflow still awaits the required execution approval. No test-failure conclusion is reported. The maintainer's comment expressly does not grant that approval. Workflow approval and subsequent merge remain maintainer actions.

The [accepted independent delta audit](../../maintainer-review-2026-09-11-wave3/audit-latest/PR93-103-delta.md) independently preserves the previous complete mathematical and PDF reviews. This integration adds no new mathematical premise and makes no competing-solution or new-priority claim.

## Local non-rewriting integration

The two parents are the published branch head `d9e25009e3ce65cf864002354830bdcc286f7252` and accepted upstream `main` commit `bfaa1d0675f24011e42740d48ea6966f83bb1bff`. The worktree was clean before the ordinary merge. Conflicts occurred only in the root README, CATALOG, RESOLVED, and randomized-category index. Their resolution is exactly the incoming accepted content; the RA-12 result and all other accepted resolutions were already included there. Regenerating the indexes leaves those accepted bytes unchanged.

All six canonical RA-12 files are byte-identical to both parents: the complete original target, solved notice, proof Markdown, both standalone TeX files, and both PDFs. Consequently no PDF was regenerated and the already recorded eight-page visual inspections continue to apply to precisely the same bytes. The original proof candidate, signed reviews, old manifests, earlier integration records and supporting evidence remain unchanged. The reference README preserves its full previous text as a prefix and adds only a dated clarification/link.

All accepted incoming tracked blobs are preserved exactly, except for that deliberately appended reference README. All 217 canonical pages match incoming main byte for byte. The registry also matches incoming main exactly: the original 203 IDs retain their mappings, and 14 IDs appended upstream are retained without alteration. No ID or target was introduced, removed, renumbered or repurposed by this integration.

## Checks and reproducibility

Both current permanent-ID validations pass, against `origin/main` and the precise incoming main commit. All 17 safeguard tests pass. The catalog is regenerated from the 217 retained entries. The [machine-readable record](main-integration-2026-09-12-bfaa1d0.json) binds the two parents, all protected submission files, registry and current metadata hashes, accepted-tree preservation, and the reviewed workflow disposition.

Run the read-only check from this recorded merge checkout:

```text
python3 references/stepaniants-ra12-2026-09-11/verification/verify_integration_bfaa1d0.py
```

The older `verify_main_integration.py` is retained unchanged for reproducing its separately dated `87366c6` integration at that recorded checkout. Its old 203-ID and index fingerprints are historical, not a description of this later 217-ID tree.

This local task performs no push, public comment, issue or pull-request creation, workflow approval, or upstream self-merge. The coordinating agent owns the eventual branch push; the maintainer owns workflow approval and merge acceptance.
