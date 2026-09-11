# Recovered tensor-computations manuscripts

**This archive contains the actual mathematical manuscripts, not just package notes.**
It supersedes the two earlier incomplete archives. Start with
`pdf/ALL_MANUSCRIPTS.pdf`, which contains all six manuscripts (28 pages), or open
the individual PDFs listed below.

These are **AI-generated candidate mathematical arguments for expert review**, not
independently certified or accepted solutions. The test results are reproducible
diagnostics; passing them does not establish universal theorems, novelty or the
absence of proof gaps. No issue, email or pull request has been submitted.

## Manuscripts

| Target | Manuscript | Scope/status | PDF pages |
| --- | --- | --- | --- |
| TR-04 | [Tie-aware TT-SVD with a pointwise strict bound](pdf/TR-04.pdf) | Qualified result; not a uniformly smaller approximation factor | 4 |
| TR-06 | [Finiteness of the mean angular CP condition number](pdf/TR-06.pdf) | Candidate proof under the stated identifiability and measure hypotheses | 4 |
| TR-13 | [Generic rank equality for odd-order Hankel tensors](pdf/TR-13.pdf) | Candidate proof of the generic target | 4 |
| TR-15 | [Counterexamples to odd-order Hankel spectral inheritance](pdf/TR-15.pdf) | Candidate counterexample, with an exact small certificate | 3 |
| TR-20 | [Nonisotropic discriminant degrees for rank-one matrices](pdf/TR-20.pdf) | Candidate proof of both requested degree formulas | 8 |
| TR-26 | [The two discriminant degrees for rational normal curves](pdf/TR-26.pdf) | Candidate proof of both reduced component degrees | 5 |

**Problem-number corrections:** the generic odd-order Hankel-rank manuscript is
TR-13, not TR-17. The rational-normal-curve discriminant manuscript is TR-26, not
TR-19. The canonical target URLs and primary references are recorded under `sources/`;
network retrieval of local source snapshots failed, so no such snapshots are claimed. No TR-17 or TR-19 solution is
being claimed.

**TR-04 qualification:** the draft establishes a proposed *pointwise strict*
inequality with the displayed constant, not a strictly smaller uniform worst-case
constant. It includes a limiting example to make that distinction explicit.

## What is included

- `pdf/`: six individual compiled PDFs and a bookmarked combined PDF.
- `manuscripts/TR-xx/main.tex`: six complete, editable LaTeX manuscripts with references.
  `main.txt` is a searchable PDF text extraction; use the PDF or LaTeX for mathematical notation.
- `code/`: six diagnostic scripts and `verify_results.py`, which runs them all.
- `evidence/`: freshly rerun JSON outputs, console logs and a summary of the six passing suites.
- `submission/`: an unsent cover note, reviewer guide and six target-specific issue drafts.
- `sources/`: primary-source references, canonical target URLs and a record of failed snapshot retrievals.
- `audit/`: recovery provenance, environment and build information; the earlier
  deficient archives are retained only as historical evidence under `prior_archives/`.
- `SHA256SUMS.txt`: hashes for all other files in this package.
- `build_pdfs.py`, `run_checks.sh`, `requirements.txt`: reproduction entry points.

## Reproduce the diagnostics

The provided environment used Python 3.13.5, NumPy 2.3.5 and SymPy 1.14.0.
The code uses ordinary Python plus NumPy and SymPy, with no network access required.
Run from the extracted package root:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python code/verify_results.py
```

Do not use `python -O` or `PYTHONOPTIMIZE`: several checks use assertions.
Individual scripts can also be run directly, for example
`python code/verify_tr15.py`. Running the checks overwrites the corresponding
`evidence/` files and timestamps; this is expected and changes their manifest hashes.
Inspect `evidence/verification_results.json` for the recorded original rerun.

To rebuild the PDFs, install a local TeX distribution with `pdflatex`, `amsmath`,
`amsthm`, `mathtools`, `booktabs`, `geometry`, `lmodern`, `microtype` and `hyperref`,
then run `python build_pdfs.py`. That script rebuilds the six individual PDFs;
the supplied combined PDF is only a convenience copy.

To verify the delivered file hashes before rerunning or rebuilding anything:

```sh
sha256sum -c SHA256SUMS.txt
```

## Recovery and limitations

The earlier ZIPs did not contain the claimed manuscript and verification files.
The present manuscripts were reconstructed from substantive mathematical text in
the earlier conversation records, with typesetting, labels and status descriptions
cleaned up. Five diagnostic scripts were similarly restored and adapted; the
TR-20 script was rebuilt from the recovered formulas and calculation. PDFs and
all test outputs in this archive were generated afresh. No claim of byte-for-byte
recovery of unavailable original files is made.

The original request for three hours of continuous active work was not certified;
this recovery does not retroactively establish that timing requirement. See
`RECOVERY_REPORT.md` for the fuller provenance and `submission/REVIEW_GUIDE.md`
for proof-review priorities. Treat all proposed resolutions as unrefereed until
qualified reviewers have checked the arguments and their match to the targets.
