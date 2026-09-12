# SP-15 document and repository checks

Prepared on 12 September 2026 UTC against upstream base `1f22006bdaa4659fcaa0bb775a887685cd3cc566`; published fork base `origin/main` was `ab754fabe3d48dc8d6eab6bcffce583e46d2b88f`. No commit, push, issue or pull request was made by this packaging agent.

## Mathematical source and attribution

The frozen original proof is [RESULT.md](RESULT.md), SHA256 `d992da0546924d7fbc9f1bb0e89e00b1442ec3c3045c739722c9767078ce40c1`. The complete core from “Exact target and conclusion” through Section 4 remains byte-for-byte identical: 7,308 bytes, SHA256 `b93675c67c4756099e5d0c169a02a789da304380e99fb0976a5b042b94a20722`. Only presentation metadata and the source/scope paragraph outside that core were rewritten.

The [separate independent full-proof review](independent-review-aa01/review.md) and its exact checker/manifest were copied unchanged with their original relative source bindings. The coordinating review was copied unchanged. The [original canonical text](canonical-statement.md) from “Context and notation” through its final line is byte-identical in the current canonical README. Its old status-search language is explicitly retained as historical. All 217 permanent IDs and paths remain unchanged.

George Stepaniants and the full Department of Computing and Mathematical Sciences, California Institute of Technology affiliation appear in the canonical notice, proof and resolution archive. No contact email is included. Original question/theorem attribution and substantial AI-assistance disclosure are explicit. The status is Solved, not Lean verified; informal AI-agent review is not described as human peer review or formal certification.

## Generated documents

Both renderers completed with no overfull-box or missing-character warnings. The proof PDF has 4 pages; the retained problem PDF has 2 pages. Both exported TeX files are standalone XeLaTeX documents. All 116 ordered proof formulas and all 20 ordered canonical-page formulas match their Markdown source after whitespace normalization.

The PDF skill marker was run exactly once before authoring this two-output batch, with operation-kind create, expected-output-count 2, output-format pdf. Every final page was rendered by Poppler at 110 DPI and visually inspected: author/affiliation, titles, headers, footers, page numbers, all displayed matrices and equations, source/reference text and line/page breaks. No clipping, overlap, missing glyph or stranded display lead-in remained. The [page QA record](page-qa.json) retains six final PNG fingerprints; those images are private handoff artifacts, not bundled third-party material.

Two renderers have narrowly scoped SP-15 layout behavior. The solution renderer inserts display no-break instructions and keeps the Schur lead-in and parameter pair together. The problem renderer puts the retained original context on a fresh page after the resolution notice. These instructions are outside the mathematical Markdown and apply only to SP-15; no shared typesetting template or email field needed changing. Existing IE-05 behavior is preserved.

## Required repository checks

- Permanent-ID validation against origin/main: PASS, 217 IDs; [log](validate-origin.txt).
- Permanent-ID validation against upstream submission base: PASS, 217 IDs; [log](validate-upstream.txt).
- Required catalog regeneration after validation: PASS; [log](catalog.txt). This branch's totals are Open 65, Partially resolved 73, Solved 78, Lean verified 1, total 217.
- All 17 permanent-ID safeguard tests: PASS; [log](id-tests.txt).
- All 3 status-distinction tests: PASS; [log](status-tests.txt).
- Exact proof-core, target, frozen artifacts, ordered formula, local-link and no-contact-email checks: the portable [checker](check_submission.py) and its [final output](submission-check-output.json) are retained.

The [source checkpoints](source-checkpoints.json) bind the six canonical artifacts and frozen provenance to exact byte hashes. They are historical fingerprints of the reviewed binaries; PDF creation metadata may change on recompilation. The [validation command record](validation-commands.json) gives the exact mandatory commands and exit codes.

No third-party primary PDF, extracted page or screenshot is redistributed. Primary papers are linked, and the independent review records its private inspection hashes and scope. The sanitized network snapshot retains public branch/path/status and content hashes while omitting unrelated bodies and file contents.
