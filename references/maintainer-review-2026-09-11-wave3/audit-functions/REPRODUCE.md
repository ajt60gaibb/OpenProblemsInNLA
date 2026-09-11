# Reproduce PR110 review checks

Reviewed head: `7d00fde9b72f55268dca3c61cd57e93085aeec87`.
Use an isolated checkout of that head and Python 3.10+ with NumPy, SymPy and
mpmath installed. The commands below write only to a separate output directory.
The reviewed scripts were inspected before execution. The mathematical proofs
are the basis of the universal claims; numerical executions are diagnostics.

```sh
REVIEW_SUBMISSION="$PWD/references/colbrook-jsr-growth-2026-09-11/submitted"
REVIEW_OUTPUT="/private/tmp/pr110-review-rerun"
mkdir -p "$REVIEW_OUTPUT"
python3 -m unittest discover -s "$REVIEW_SUBMISSION/construction" -p 'test_*.py' -v
python3 "$REVIEW_SUBMISSION/construction/rational_growth_pair.py" --gamma 1/2 --output "$REVIEW_OUTPUT/alpha-half-matrices.json"
python3 "$REVIEW_SUBMISSION/construction/rational_growth_pair.py" --gamma 7/3 --output "$REVIEW_OUTPUT/seven-thirds-matrices.json"
python3 "$REVIEW_SUBMISSION/verification/verify_growth_construction.py" --output "$REVIEW_OUTPUT/growth.json"
python3 "$REVIEW_SUBMISSION/verification/verify_triangular_comparison.py" --horizon-trials 5000 --output "$REVIEW_OUTPUT/triangular.json"
python3 "$REVIEW_SUBMISSION/verification/enumerate_growth_words.py" --alpha 0.5 --max-length 24 --allow-expensive --output "$REVIEW_OUTPUT/exhaustive24.json"
```

The last command tests 33,554,430 nonempty words in floating-point arithmetic.
It is exponential in maximum length and is not an infinite-length proof.
Exact independent checks are in this review's `independent_checks.py`; copy it
to the desired output directory before running, since it writes its JSON result
beside itself. It imports no submitted code and needs SymPy plus the standard
library. It checks complex rational damping, Jordan/cyclic identities, symbolic
compression, rational inequalities, and exact lower-word breakpoint cases.

PDF QA used PyMuPDF/Pillow to render every final page, followed by visual
inspection. Every final TeX source was separately rebuilt twice with XeLaTeX
`-no-shell-escape`; all extracted text and page counts were identical. The two
tiny canonical first-page spacing differences are described in the review.
The PDF summaries preserve hashes and results; local contact sheets are
diagnostics and need not be published with the review.
