# SP-11 verified-status promotion and preservation

Prepared by `/root/lean_verification` (Codex AI agent), 18 October 2026.
This is packaging and preservation evidence; the independent mathematical,
kernel and actual Linux checks are retained in their separate earlier reports.

The canonical SP-11 page now says **Lean verified**, with the actual complete
proof, immutable checked commit and Linux receipt linked. Its original
mathematical text, credits and dated history are retained. The proof README,
canonical package README and formalization metadata now describe the completed
full-target verification. The receipt binds run `39131755109`, commit
`9264361fafb89b37b5c48236afebb304bc84110a`, the selected full Target, all 135
original project inputs and actual sandbox/Comparator/kernel controls.

**Before any canonical edit**, the base
`47006df8b3a6c724a557266c891893d03e69323a` README, TeX and PDF were archived
byte for byte in [sp11-originals-47006](../sp11-originals-47006/manifest.json).
The promotion-specific [preservation report](preservation.json) passes all
16 checks:

- All 217 permanent ID/path mappings and registry bytes are unchanged; every
  canonical path remains present.
- SP-11 is the only changed canonical page. Removing exactly the marked new
  evidence block and restoring its status/check date recovers the complete
  original README byte for byte, including all attribution and history.
- Of the 611 original immediate problem artifacts, 609 remain unchanged. Only
  the authorized SP-11 generated TeX/PDF change; their exact originals are
  archived and checked against the published base.
- The mathematical target in the generated TeX is unchanged modulo whitespace
  and the standard equivalent `operatorname` / `mathop`-`nolimits` notation for
  `mr` and `rank`. The original Markdown target is byte-identical.
- All frozen statement/infrastructure/reviewed-target bytes and all 42 checked
  Lean source inputs from the actual Linux run remain unchanged.

The initial overly strict TeX-byte comparison is preserved in
`preservation-attempt-1.json`. Current repository rendering emits equivalent
operator macros and display spacing compared with the older generated file;
the corrected checker normalizes only those two operator spellings and
whitespace. No permanent-ID, original-archive, original-Markdown or Lean-source
guard was relaxed. The older strict all-page/all-611 historical preservation
reports were not overwritten.

The repository workflow regenerated only SP-11:

```bash
python3 tools/render_problems.py SP-11
```

It reported `SP-11: OK` without overfull/missing-character warnings. The PDF
skill's required edit marker ran successfully once immediately before the
first render. SP-11 was added to the existing verification-date footer list in
the renderer, so the new date is labeled "Verification check". Both regenerated
pages were rasterized and visually inspected: no clipping, overlap, missing
glyphs or orphaned headings; all original target equations and history remain.
[Visual QA](pdf-visual-review.json), [page images](renderings/),
[PDF information](pdfinfo.txt) and [render log](render.log) are retained.

The required permanent-ID workflow ran in order and passed:

```bash
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

The ID validator checked 217 entries; all 17 ID tests passed. Index generation
reports Lean verified=77, Solved=41, Open=36, Partially resolved=62,
Solution claimed=1. Numbering and the open count are unchanged. Logs are
`validate-problem-ids.log`, `update-catalog.log`, and `problem-id-tests.log`.

Manifest schema/Comparator coverage passed for the selected full theorem.
The statement inventory was regenerated at its retained published base
`7ebc4e21f2a4e19db341a3fb28644ab4e2df7ebf` and its check passed. All 45
statement metadata records validated against `origin/main`. Those commands'
logs are retained here. `git diff --check` passed.

The promotion changes descriptive canonical-project inputs (README and
formalization metadata), so it requires a fresh committed-project CI run.
The existing Linux receipt remains bound to its immutable original commit;
it does not claim the refreshed metadata has the old hashes. No proof source,
statement, Comparator selection or source lock was modified for promotion.
The parent agent inspected the promotion and committed it before merging the newer published main.

To reproduce the preservation check:

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-promotion-preservation.py
```

## Published-main refresh

While the promotion was prepared, MD-03, MD-04 and RA-10 were merged into
published main `36767fa4`. The promotion was reconciled with that main without
changing any SP-11 proof or statement input. The separate
[current-base preservation report](preservation-main-36767.json) repeats all
16 checks against that published main: SP-11 is still the only changed
canonical page, all 217 IDs and paths are unchanged, and all originals and
42 checked Lean inputs remain preserved. The earlier reports and their
original base remain unchanged. Regenerated catalogs now report Lean
verified=80 and Solved=38; all other status counts are unchanged.

```bash
python3 docs/lean/campaign-2026-10-17/verification/check-sp11-promotion-preservation.py --base-ref origin/main --output docs/lean/campaign-2026-10-17/verification/sp11-promotion/preservation-main-36767.json
```
