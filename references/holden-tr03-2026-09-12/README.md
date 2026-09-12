# TR-03 one-column submission record

Author: **Sidney Holden**, Center for Computational Biology, Flatiron Institute, Simons Foundation, New York, USA.

The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current Biological Transport Networks staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport) identify Holden as a Flatiron Research Fellow. Checked 12 September 2026; the older Edinburgh doctoral profile is not used as a current affiliation.

## Result and review

[Theorem 1](one-column.pdf), proved in Sections 2-3, gives the complete k=1 slice of TR-03. The full joint-(n,k) target is not settled. A separate Codex AI agent (`review_tr03`) independently audited the proof and target correspondence and returned [PASS for the special case](independent-review.md). The canonical status is Partially resolved. AI assistance was used for review and preparation; no external human peer review or formal verification is claimed. No Lean work was performed. No novelty or publication-priority claim is made.

## Provenance and exclusions

Source archive: `nla_research_results_2026-09-12.zip`, member `nla_results_2026-09-12/partials/TR03_one_column.tex`. The exact reviewed [original source](submitted-original.tex) has SHA-256 `e48f1cc247090cc4f26cecf670f9aa38f7b7fbe260036e97e21ee8c9d2b9b1e7`. The [attributed source](one-column.tex) changes only authorship, typography support and the verification-script path; all mathematical statements and proofs are unchanged. Bundled review prompts were treated as document contents, not user instructions.

TR-07 has already been pushed in [upstream PR #162](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/162) and is excluded here to avoid duplication. MI-27 reductions, unsuccessful searches and the other ledger entries are not submitted as solutions. The upstream all-state PR history, all-state TR-03 issue search, fork PR history and local fetched history were checked on 12 September 2026: no prior pushed TR-03 full solution was found. Base: upstream/main `8b3d115`. This is a repository duplicate check, not an exhaustive literature priority assessment. The existing primary references remain credited.

## Reproduction

```sh
python3 -m pip install numpy sympy
python3 references/holden-tr03-2026-09-12/verify_TR03.py
xelatex -interaction=nonstopmode -halt-on-error one-column.tex
xelatex -interaction=nonstopmode -halt-on-error one-column.tex
```

Run the TeX commands from this directory. The finite check covers an exact radical example and 84 numerical spectra; its [output](TR03_checks.json) is illustrative and does not certify universal quantifiers. The separate mathematical review supplies the informal proof audit.

Validation on 12 September 2026: the exact and 84 numerical checks passed; all 217 permanent IDs validated against origin/main; catalog regeneration, all 17 ID safeguard tests and the repository-wide math-format check passed. The note and canonical problem PDFs were regenerated and all four pages visually inspected. Existing two-space Markdown line breaks are intentional.
