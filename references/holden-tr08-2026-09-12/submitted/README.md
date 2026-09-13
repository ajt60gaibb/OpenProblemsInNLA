# TR-08 — square-root-logarithmic sparsity threshold

**Proposed complete solution, prepared 12 September 2026.**

Start with **`manuscript/solution.pdf`**. Its editable source is
`manuscript/solution.tex`. The proof is a research argument, not an independently
refereed result or a formally verified theorem. The finite checks supplement the
proof; no computational result is used to establish an asymptotic assertion.

## Main result

In the exact model of TR-08, let `A_k = (M_k)_{:I_k}`. Then

$$
\exists a>0:\quad \Pr\{\sigma_{\min}(A_k)\ge a\}\longrightarrow1
\quad\Longleftrightarrow\quad
\liminf_{k\to\infty}\frac{s_k^2}{\log k}>0.
$$

Equivalently, the criterion is **`s_k = Omega(sqrt(log k))`**. Logarithms are
natural. Integer rounding is harmless. The statement covers nonmonotone and
oscillating sparsity sequences, as well as the full critical window.

More explicitly, the manuscript establishes:

* If `s_k^2 = o(log k)`, the smallest singular value converges to zero in
  probability.
* For every fixed `h > 0`, the condition `s_k^2 >= h log k` eventually guarantees
  a fixed positive lower bound `a(h)` with probability tending to one.

The constant `a(h)` is independent of `k`, the ambient number of columns, and
the realized matrix. It is allowed to depend on the fixed positive lower bound
`h`. A common constant for all arbitrarily small `h` is not asserted. This is
the existential-constant quantifier in the problem, not a fixed-distortion
threshold problem.

Every positive constant multiple of `sqrt(log k)` therefore succeeds. Dividing
that scale by a factor tending to infinity fails. In particular, both
`sqrt(log k)/log log k` and `sqrt(log k/log log k)` fail. The logarithmic exponent
is `1/2`, but the claimed result is stronger than an exponent-only separation.

## How the proof fits together

The selected columns have exactly the same product law as an independently
generated `k` by `k/100` matrix. The ambient `n_k` disappears from the question.

For necessity, a reservoir of half the columns supplies many rows of occupancy
at least `w = ceil(s_k/epsilon^2)`. An independent test column lands on mutually
distant such rows with probability at least `exp(-C_epsilon s_k^2)`. Its full
column supports, together with chosen reservoir columns, form a cancellation
tree. A vector supported on those columns has squared Rayleigh quotient
`(s_k - 1)/(s_k + w) < epsilon^2`. There are linearly many independent test
columns, so a witness exists with high probability below the proposed scale.

For sufficiency, separate columns with many high-occupancy row neighbors from
the bulk. A conditional incidence estimate shows that each column meets only
a bounded number of exceptional columns when `s_k^2 >= h log k`. Delete their
entire row neighborhoods from the bulk, not merely the high-occupancy rows.
A nonbacktracking argument gives a fixed lower singular-value bound for the
remaining bulk. The exceptional columns have disjoint retained supports and
are recovered through an exact block-triangular restriction. A deterministic
bound controls the block coupling.

The only non-elementary external estimate is Lemma 4.3 of Dumitriu and Zhu,
*Extreme singular values of inhomogeneous sparse random rectangular matrices*,
arXiv:2209.12271v4. Section 3 of the manuscript proves the required extension
from independent entries to fixed-size column supports and support-dependent
pruning. The other probabilistic and linear-algebra steps are proved in the
manuscript. Source details are in `provenance/REFERENCES.md`.

## Files

| File | Purpose |
|---|---|
| `manuscript/solution.pdf` | Complete mathematical write-up |
| `manuscript/solution.tex` | Editable LaTeX source |
| `PROOF_AUDIT.md` | Dependency map and delicate points to check |
| `code/verify.py` | Symbolic, exact-enumeration, and numerical sanity checks |
| `code/experiment.py` | Exact-model sampling and finite singular-value experiments |
| `code/requirements.txt` | Dependency versions used for the recorded runs |
| `verification/checks.json` | Recorded passing verification run |
| `verification/experiments.csv` | 45 finite-dimensional experiments |
| `verification/experiments.metadata.json` | Experiment parameters and software versions |
| `verification/experiments_run.txt` | Human-readable experiment summary |
| `verification/NOTES.md` | Scope, commands, and numerical limitations |
| `provenance/REFERENCES.md` | Primary-source references and exact external input |
| `Makefile` | Convenient build, check, and experiment targets |
| `SHA256SUMS` | Checksums for the delivered files, excluding this checksum file |

## Reproduce the checks

The recorded runs used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, and SymPy 1.14.0.
The scripts use Python 3.10+ syntax; dependency wheel availability can impose a
newer minimum Python version. Use a virtual environment compatible with the
pinned versions, or install compatible recent NumPy, SciPy, and SymPy releases.
From the archive root:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r code/requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python code/verify.py --output verification/checks.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python code/experiment.py --sizes 2000 10000 50000 \
  --sparsities 1 2 4 8 16 --repetitions 3 \
  --output verification/experiments.csv
```

The exact rational outputs should reproduce exactly. Floating-point results can
vary in their final digits between platforms and linear-algebra libraries. The
scripts do not download data or use a network connection.

## Rebuild the PDF

Use a LaTeX installation providing `pdflatex` and the packages named at the top
of `solution.tex`, including Latin Modern, AMS packages, `microtype`, `geometry`,
`hyperref`, and `fancyhdr`:

```sh
make pdf
# Or:
cd manuscript
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
```

The supplied PDF is ready to read; rebuilding is optional. The PDF and source
are the primary deliverable. Neither the simulations nor the audit checklist
replace independent mathematical review of the proof.
