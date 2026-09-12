# KE-05 negative resolution - 12 September 2026 (UTC)

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The [complete proof](../../randomized-and-low-rank-approximation/KE-05/solution.md), in its exact-target statement and Sections 1-5, disproves the spectrum-uniform probability bound for the original KE-05 recurrence. It gives deterministic admissible real diagonal blocks with fixed dimensions `b=2, d=3` for which the product of the two prescribed random constants tends to infinity in probability. The original target and all permanent IDs are retained. Shao retains credit for the conjecture and interpolation framework.

[Proof PDF](../../randomized-and-low-rank-approximation/KE-05/solution.pdf) · [Standalone proof TeX](../../randomized-and-low-rank-approximation/KE-05/solution.tex) · [Canonical entry](../../randomized-and-low-rank-approximation/KE-05/README.md).

## Mathematical review and provenance

The separate [independent Codex-agent audit](independent-review.md) returned PASS for the complete negative answer, with no mathematical corrections. It identifies the proof-drafting and reviewing agents and records the reviewer's prior separate numerical exploration. The coordinator contributed to the analytic argument and is not counted as an independent reviewer. Substantial AI assistance is disclosed. This is informal automated review, not external human peer review or formal verification.

The exact frozen [reviewed source](reviewed-proof.md) has SHA-256 `51e66685d6e84639ee3aa098ebf1e91e43891c9a6fe04d473f334cf0e6f2a68f`. Its preliminary private-work status is retained as historical evidence; the signed independent audit supersedes that preliminary status. The [publication comparison](publication-source-comparison.json) binds the final public Markdown (SHA-256 `31c3416ba212cb2cbb73d126633efe79f1e4a2669a80ef5936fa12dc6723bd62`) and confirms that its entire mathematical core is byte-identical. The final wrapper adds the approved author affiliation, links the audits, and preserves scope and source credit.

The [original target snapshot](canonical-statement.md) is unchanged from upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. Its original relative navigation links are retained as part of that frozen snapshot; use the live canonical-entry link above to navigate the current documents. The separate [source-reading note](source-notes.md) and [public eligibility audit](public-audit/README.md) confirm that the original assumptions permit interlaced block spectra and repeated eigenvalues within one block. The argument does not claim a negative result for an added ordered-interval restriction or for block Lanczos convergence itself.

The [original reviewer manifest](independent-review-manifest.json) and [original checker stdout](check-stdout.txt) are retained unchanged. In the original manifest, `REVIEW.md` is archived here as `independent-review.md`; all other referenced names are unchanged. The repository package's [manifest](manifest.json) binds the final artifact names and hashes.

## Exact checks and reproduction

Both checkers use only the Python standard library:

```sh
python3 references/stepaniants-ke05-2026-09-12/exact_check.py
python3 references/stepaniants-ke05-2026-09-12/independent_exact_check.py
```

The drafting agent's [checker](exact_check.py) passes 46 exact rational/polynomial checks; its [output](exact-check.json) includes all three root orderings at six rational inputs. Its sole packaging change replaces the private source filename `RESULT.md` with the unchanged archived `reviewed-proof.md`.

The reviewer's independently written [checker](independent_exact_check.py) proves the supporting polynomial identities by exact polynomial arithmetic, checks the nonorthogonal witness, and evaluates twelve literal reordered rational instances. Its [output](independent-exact-output.json) is retained. Finite checks support the algebra and transcription; the full Gaussian and probability argument is established in the written proof and independent audit.

The two final PDFs compile from their standalone TeX sources with XeLaTeX. The proof TeX is generated from its Markdown with Pandoc by [build_solution.py](build_solution.py); the canonical documents use the repository renderer. Run from the repository root:

```sh
python3 references/stepaniants-ke05-2026-09-12/build_solution.py
python3 tools/render_problems.py KE-05
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 references/stepaniants-ke05-2026-09-12/check_submission.py
```

Set `PANDOC` to its executable if it is not on PATH. The final [verification record](verification.json) documents source/target preservation, formula conversion, both published-base ID validations, 17 ID tests, three status tests, exact-check reruns, author/affiliation checks, and inspection of every final PDF page. The only renderer change removes KE-05's forced reference-page break, avoiding an almost-empty extra page. No other problem's rendering behavior changes.

The separate [final packaging audit](packaging-review/KE-05-packaging-review.md) passed the source conversion, preserved target, standalone artifacts, metadata and exact-checker reproduction. Its [public-head refresh](packaging-review/head-refresh.json) found the six-repository, 47-head inventory unchanged at 03:21:24 UTC. The report identifies its source/metadata checks separately from the all-page visual inspections.

## Eligibility and publication scope

The public audit at 2026-09-12 03:13:09 UTC checked six repositories and 47 branch heads, their selected relevant documents, and issue/PR/comment/review records. Every available canonical KE-05 page was Open; no competing solution was found. Primary-source version and later-publication searches likewise found no prior resolution. The audit states its limits and retains sanitized metadata; retrieved discussion bodies and full third-party documents are not republished. A bounded public search does not certify novelty or absence of private or unpublished work.

`Solved` is proposed under the repository's independent-informal-audit rule. Upstream inclusion requires maintainer review and merge of the new pull request; publication on the author's fork does not itself establish acceptance into main.
