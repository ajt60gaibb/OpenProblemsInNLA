# IE-03: a Hadamard matrix with growth factor greater than its order

**Author:** Matias Andia, Department of Mathematics, Princeton University.

**Submission date:** 31 October 2026.

[Paper on Zenodo](https://zenodo.org/records/23871097) · [Local PDF](main.pdf) · [LaTeX source](main.tex) · [Original IE-03 target](../../linear-systems-and-elimination/IE-03/README.md)

## Result and scope

Theorem 1 (page 1; construction and proof in Section 2, pages 1–4) of
*A Hadamard matrix with growth factor greater than its order* gives a row and
column permutation of the Sylvester Hadamard matrix of order 4096 whose
diagonal elimination path is a valid complete-pivoting path and has growth
4608 = (9/8)4096. The first pivot exceeding the order is +4608 at step 4089.

This is a counterexample to IE-03's universal assertion over real Hadamard
matrices and every admissible complete-pivoting path in exact arithmetic.
One admissible path suffices to refute that assertion; there is no requirement
that every tie-breaking rule choose the exhibited path. Corollary 1 (Section 3,
page 4) extends the construction to every power-of-two order at least 4096.
The asymptotic statement in Conjecture 1 is a separate conjecture, not a proved
consequence. No claim about the smallest counterexample order is made.

## Submitted files

- `main.pdf`, `main.tex`, `citations.bib`, and the two files in `figures/`:
  the author's manuscript and all inputs needed to rebuild it.
- `matrix.npy`: the explicit 4096-by-4096 signed-int8 NumPy array.
- `verify_construction.py`: the standard-library rational-arithmetic verifier,
  including all 124 local pivot choices and the four lifts.
- `verify_dense.py`: the independent computational route, reading only
  `matrix.npy` and checking the full dense elimination path.
- `verification/`: fresh execution logs and the scope of those checks.
- `SHA256SUMS`: hashes of the submitted research files.

The research files are copied unchanged from the author's supplied folder.
The submission notes and verification records were prepared for this PR.
The older local README, checksums, and verification logs described an earlier
version of the dense checker and are not used as evidence for this submission.
LaTeX build intermediates and unused figure crops are omitted.

## Reproduce the checks

Use Python 3.10 or newer. The construction verifier needs only the standard
library; the dense verifier additionally needs NumPy. From this directory:

```sh
python3 -m venv /tmp/ie03-venv
/tmp/ie03-venv/bin/python -m pip install numpy
/tmp/ie03-venv/bin/python -I verify_construction.py
/tmp/ie03-venv/bin/python -I verify_dense.py
```

Run these commands from this directory because the dense checker reads
`matrix.npy` relative to its working directory. Its checks use Python
assertions: do not add `-O` or `-OO`. The `-I` option ignores Python environment
settings, including `PYTHONOPTIMIZE`. The dense computation can take several
minutes and has no command-line timeout option. Both programs must exit
successfully and report growth 4608.

The construction checker compares all 16,777,216 stored entries with the
Walsh-permutation formula, checks the permutations and the 124 local rational
pivots, and verifies identities used with the manuscript's lifting lemma.
It reports the first overshoot and the signed-pivot-sequence SHA-256 digest.

The dense checker checks the sign entries and the Gram matrix, then performs
all 4096 whole-active pivot comparisons and Schur updates. It represents the
Schur complement as an int64 numerator matrix divided by a positive Python
integer denominator, cancels common factors, and checks an overflow bound
before each update. Growth is accumulated using `fractions.Fraction`.
The Gram multiplication uses binary64: each summand is exactly +1 or -1,
and partial sums have magnitude at most 4096, so these sums are exactly
representable. This detail is distinct from the integer elimination arithmetic.
This version prints only the final pass message and growth, not a pivot digest.

Optionally regenerate the matrix in a separate file and export the pivot
history without changing the supplied matrix:

```sh
/tmp/ie03-venv/bin/python -I verify_construction.py \
  --matrix /tmp/ie03-regenerated.npy --write-matrix --pivots /tmp/ie03-pivots.csv
cmp matrix.npy /tmp/ie03-regenerated.npy
```

## Rebuild the manuscript

With a standard TeX Live or MiKTeX installation, run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The canonical problem description is a separate document. From the repository
root, regenerate it with `python3 tools/render_problems.py IE-03` as described
in [CONTRIBUTING.md](../../CONTRIBUTING.md).

## Attribution and verification level

The manuscript's acknowledgements credit extensive AI assistance and state
that GPT-6 Astra Pro produced the counterexample after a long exploration.
Matias Andia organized the final presentation and takes responsibility for
the content. Codex prepared this repository contribution and reran the supplied
verification scripts. The dense and construction programs are different
computational verification routes; that does not imply independent human
authorship or external peer review.

The author's [public discovery account and selected prompts](https://github.com/matias-ma/hadamard_cp/blob/53c1796f1f315f035f4d6b5985f69850b7ddcd0f/README.md#how-the-growth-factor-counterexample-was-found)
also links a [shared ChatGPT conversation](https://chatgpt.com/share/6ae67148-5ba0-83ea-85ed-969f617e35ff).
The author describes that conversation as containing an earlier counterexample
of larger order that supplied the central idea for the present construction.
It is discovery context; the reproducible evidence for the order-4096 result
is the manuscript, explicit matrix, and verifiers included here. The public
[`order4096` package](https://github.com/matias-ma/hadamard_cp/tree/53c1796f1f315f035f4d6b5985f69850b7ddcd0f/order4096)
contains identical copies of this manuscript PDF, matrix, and both verifiers.

The proposed catalog status is **Solution claimed**, pending a documented
independent full-result audit or publication. The fresh computational runs
are reported with their actual scope; they are not Lean or other
proof-assistant verification.
