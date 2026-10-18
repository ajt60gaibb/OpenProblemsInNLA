# PF-05 status promotion and original preservation

The canonical entry is promoted to Lean verified after the actual exact-source
Linux push run at 10e71f134795c6cb94ab90edf2a8deef0f4722fe passed all 41 controls
and all 90 package inputs, including all 46 Lean sources. Both root and
independent offline artifact replays passed. The later descriptive README/YAML
refresh requires its own exact-source Linux receipt.

The unchanged mathematical target, original source credit, original resolution
and dated historical status records remain in place. Removing only the marked
Lean notice and restoring the previous status/date recovers the complete old
Markdown byte for byte. Five original canonical/submitted proof artifacts remain
in the exact [archive](../originals-main-36767/manifest.json).

The separate [preservation checker](../check-promotion-preservation.py) uses fixed
pre-promotion base 235984a1515b3dc8d22712bd7fb7bb26d5f70487. Its 18 controls
preserve all 217 IDs and paths, all other canonical pages, and all immediate
original artifacts except the authorized PF-05 TeX/PDF regeneration. All 46 Lean
inputs match the actual Linux result. The original historical 828-artifact
preservation report remains a distinct, unchanged pre-promotion record.

The final PDF has two clean pages: title, notice and retained resolution on
page 1; the complete context, problem, question and retained history on page 2.
Root and independent visual review found no clipping, overlap, misplaced math
or bad glyphs. The first three-page rendering, its source, log and all PNGs are
retained under `render-attempt-1/`; the final render log and two final PNGs are
retained here. The initial checker invocation with an incorrect artifact path
raised an input-path error before writing a result; that invocation is recorded
separately, and the successful replay uses the actual result path.

Independent approval and full TeX comparison:
[PROMOTION_INDEPENDENT_REVIEW_3_2026-10-18.md](../PROMOTION_INDEPENDENT_REVIEW_3_2026-10-18.md).
