# IE-06 canonical publication preparation and PDF review

Prepared and checked by `/root/source_statement_author`, 6 October 2026, only
in `/private/tmp/nla-ie06-proof-publication-20261006`. This is the author's
canonical-document and visual review; the independent publication review is
separate. No commit, push, pull request, or other remote action was performed
by this agent.

## Content and scope

The canonical page and resolution archive now link the proof packet at immutable
revision `263a215acd295a260dec7a75ff6bebebb9789df9`. The page lists the exact six
`NLA.IE06` Solution declarations, Lean 4.33.1, the locked mathlib and LeanCert
revisions, the final independent mathematical scope audit, the actual local
receipt, and the six-target Comparator library log. It reports 114 compiled
source modules and 3,229 audited declarations across 113 concrete modules,
foundational-only transitive axioms, and the successful rejection controls.

The status remains **Solved**. The authoritative Linux sandbox, full Comparator
CLI/exporter, and separate raw-kernel replay remain pending. Pinned compiled
dependency caches are explicitly identified as trusted local inputs. The
maintainer's reported permission from John Urschel is permission to publish,
not a correctness endorsement. The wording says publication is authorized;
it does not claim that a push has already occurred.

The exact original `Context and notation` and `Problem statement` sections are
byte-identical to `origin/main` at `a345cfc7e18a90df3b0e8a8f57099372b873baaf`. The stronger all-Schur result is
distinguished from the displayed LU-growth result. No ID, canonical path,
original target, or registry mapping changed. No Lean proof/package file or
shared tooling was edited by this agent, apart from this requested review file.

## Canonical output identities

| File | SHA-256 |
| --- | --- |
| `RESOLVED.md` | `f64370e5789fb86eef07546595cb074791a89e40eb4771a2fb383bb316846560` |
| `linear-systems-and-elimination/IE-06/README.md` | `c2f740cc2da336681b0b259951d38f314044ca0bb1d1c8b8ab02986629b265b1` |
| `linear-systems-and-elimination/IE-06/problem.tex` | `370722a7a2f065aa6d1e4f0a9a0e8f9bae18e9d4d70d5cc9ab1d552045127510` |
| `linear-systems-and-elimination/IE-06/problem.pdf` | `07ce3f45da67805648fb94ed3cfe822d0c8dcbfaeb3eb243051b36cf8974339e` |

Catalog regeneration produced no index changes. Its actual output was:

```text
Validated 217 permanent problem IDs against origin/main
Indexed 217 entries: Lean verified=69, Open=37, Partially resolved=65, Solution claimed=1, Solved=45
```

## Checks

All commands below exited zero in the isolated publication checkout:

```text
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 tools/format_math.py --check
git diff --check
PANDOC=/private/tmp/mi18-render-deps/pypandoc/files/pandoc python3 tools/render_problems.py IE-06
xelatex -interaction=nonstopmode -halt-on-error -output-directory /private/tmp/ie06-publication-pdf-review/standalone linear-systems-and-elimination/IE-06/problem.tex
```

The ID suite reported `Ran 17 tests` and `OK`. The format check reported
`Need formatting: 0 pages`. The renderer reported `IE-06: OK` and
`Rendered 1 problem documents.` Standalone compilation succeeded with zero
overfull-box warnings. `git diff --check` produced no output. Registry and
regenerated root/category/catalog indexes remain unchanged. The exact final
command transcript is retained locally at
`/private/tmp/ie06-publication-pdf-review/checks.json`, SHA-256
`9ef9fc0d0f086558474928e791f361f6141ce377affd6894fa29544a1ddfe489`.

## PDF visual review

The PDF skill was applied. Its required artifact-operation marker was located
in the skill's `container_tools` directory and successfully run exactly once
before authoring, with operation `edit`, expected output count `1`, and format
`pdf`. The existing repository renderer and typesetting template were used
unchanged. The final PDF has three A4 pages, 51,873 bytes, and PDF version 1.7.
All three final pages were rendered at 125 dpi with Poppler and inspected
visually after the last content edit:

- Page 1 keeps the title, Solved notice, complete original context, and full
  conjecture together. Equations, labels, and footer are legible.
- Page 2 contains the complete new evidence section and all six theorem names
  without a split list, clipping, overlap, or a misleading verification claim.
- Page 3 keeps the source comparison, references, and historical checks
  together. Headings, equations, references, page numbering, and footer are
  legible and have clear margins.

No visual defects were found. The inspected rasters are
`/private/tmp/ie06-publication-pdf-review/authorized-1.png` through
`authorized-3.png`, with these SHA-256 identities:

- Page 1: `fb74b5fb2f9657642d505bd5b8762a982bcd120b163c58e4f8bdfdaa3ce8a355`.
- Page 2: `41713baf0bef9348db5c25c81117d136cd5020c1a13522fffc40fb1cb950af09`.
- Page 3: `6445960726d27565f6324b1b49928a22f5f459a346a89573ff2c4ffda9870b14`.

After this visual inspection, only a redundant blank line at the Markdown EOF
was removed. The renderer strips outer body whitespace, so this does not change
TeX/PDF content. No further canonical edits are intended.
