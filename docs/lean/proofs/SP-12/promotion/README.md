# SP-12 verified-status promotion and preservation

Prepared by `/root`, Codex AI agent, 18 October 2026. This is packaging and
preservation evidence. Mathematical source reviews, fresh kernel audits and the
actual Linux receipt are separate retained reports.

The full original SP-12 target passed actual isolated Linux run `39142969327`
at immutable proof commit `529e7b0560cef6461c98e950046860a160e6f86c`.
The independent artifact review passes all 40 checks and all 96 original
committed/current project hashes at audit time. Root independently replayed
that artifact checker before any promotion edit, with the same successful
outcome. The actual selected full Target has only the three standard axioms.

Before editing, the published-main `36767fa4` canonical README, TeX and PDF were
archived byte for byte in [originals-main-36767](../originals-main-36767/manifest.json).
The new canonical notice is explicitly marked; removing only that notice and
restoring the old status/check date recovers the complete original Markdown,
including every original equation, attribution and dated historical note.
The canonical package updates only descriptive README/metadata, preserving all
55 checked Lean inputs, frozen statements, selected export and Comparator.
Its whole_problem_verified and canonical_status now record the actual first
successful Linux proof. The refreshed descriptive inputs require a separate
fresh committed-project run; the old receipt is not relabeled with new hashes.

The [promotion preservation report](preservation.json) passes all 16 checks
against the recorded SP-11 branch base `e3725bf89a9682c28bb2c0cec1cee1be658d5d11`:
all 217 permanent IDs/paths and registry bytes are unchanged; SP-12 is the only
changed canonical page; all 611 immediate original artifacts are unchanged
except the regenerated SP-12 TeX/PDF, whose exact originals are archived;
the generated TeX target is equal modulo whitespace/standard operator notation;
and all 55 actual Linux-checked Lean inputs remain byte-identical. The earlier
strict all-828 original-page/artifact report remains unchanged and historical.

```bash
python3 docs/lean/proofs/SP-12/check-promotion-preservation.py --ci-result docs/lean/proofs/SP-12/verification/full-linux-ci/artifact/verify-20261018T162848Z-4209/result.json
```

Repository rendering regenerated only SP-12. The PDF skill edit marker ran
successfully once immediately before this operation's first authoring command.
The first render's small overfull notice line is retained in render-attempt-1.log;
rewording only the new notice fixed it. Final [render.log](render.log) reports
`SP-12: OK` without warnings. SP-12 was added to the existing renderer's
verification-date footer list. All three final PNGs were visually inspected:
no clipping, overlap, missing mathematical glyphs or orphaned headings. The
whole unchanged original target occupies page2, with attribution/history and
references retained. [Visual QA and hashes](pdf-visual-review.json),
[page images](renderings/), and [PDF information](pdfinfo.txt) are retained.

The permanent-ID workflow ran in the required order and passed:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

It checked all 217 IDs and passed all 17 tests. Catalogs now report 81 Lean
verified, 37 Solved, 36 Open, 62 Partially resolved and one Solution claimed.
The statement inventory was regenerated at its retained published base
7ebc4e21f2a4e19db341a3fb28644ab4e2df7ebf; all 45 statement metadata records
and the v0.4 one-result manifest/Comparator coverage validate. No ID safeguard
or frozen statement was weakened. Raw historical Markdown hard-break spaces
and exact CI logs are preserved rather than reformatted for diff whitespace.
