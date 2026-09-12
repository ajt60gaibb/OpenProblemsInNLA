# PR #116 independent read-only PDF QA

Reviewed head: `7d34abbd7d8fb12a37fea28ba68875c54780a5ed`.
Date: 2026-09-11. **PASS.** No document blocker found. This is packaging/source-correspondence QA; the root agent supplies the mathematical verdict.

Inspected authoritative documents in `/private/tmp/nla-pr116/matrix-functions-and-stability/MF-18/`:

- `solution.pdf`: four pages, SHA-256 `f4f0f39eb93484d23f3b86c40339050834252873f2b90be0185d37ea1864089a`.
- `problem.pdf`: two pages, SHA-256 `cfba8b75dc07e96cc2aaac9e6d60254d2db44eb0e18d6b1cda507536df080342`.

I read the complete solution Markdown, corresponding generated TeX, and canonical README. Automated extraction compares every inline and displayed mathematical expression in order, ignoring whitespace only: all **134 solution expressions** and all **30 canonical expressions** match the respective generated TeX exactly. No mathematical expression was dropped, reordered or altered by conversion.

I rendered all six pages with Poppler to temporary PNGs and visually inspected every page at readable resolution against the source. The four-page proof includes the full theorem, homotopy and factorization, reciprocal-root count, Stein identity, nonzero diagonal/unit-circle argument, stable generalized eigenspace upper bound, complete scope/attribution statement, and all four references. Equation tags (1)-(12), adjoints, inverse powers, signs, exponents and the rank equality are readable and agree with the sources. The two-page canonical document includes the complete original target, Stepaniants attribution and new resolution, Colbrook's retained auxiliary result and scope, proof/review links, references and historical status notes. The finite nonsingular limit and simple-unit-circle hypotheses remain explicit.

No clipping, overlapping text, missing glyphs, broken equations, truncated references or missing proof passage was observed. Text extraction found zero replacement glyphs and zero characters outside the page bounds on all six pages. The page-1 canonical statement continues to page 2 and the proof's longer argument continues naturally across pages; these page breaks lose no content.

The author's name, department and institution are visible. The canonical page preserves Colbrook's name, Cambridge affiliation, and the distinction between his real-coefficient defective extension and the general complex simple-eigenvalue resolution. AI assistance and the limits of agent review are visible.

Evidence: `pr116-pdf-qa/checks.json`, full extracted `solution.txt` and `problem.txt`, and six PNG pages. Only temporary outputs were created; no authoritative PDF, TeX, Markdown or repository metadata was edited or recompiled.
