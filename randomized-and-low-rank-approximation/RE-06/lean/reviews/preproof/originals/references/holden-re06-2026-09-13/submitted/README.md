# RE-06: a fully nonadaptive affirmative construction

This archive contains a complete mathematical solution to **RE-06 — Nonadaptive queries for finite-family matrix approximation**, together with a floating-point reference implementation and reproducible numerical audits.

**Start with [`solution.pdf`](solution.pdf).** The 12-page note proves the algorithm and its probability and query bounds. [`solution.tex`](solution.tex) is the editable source.

## Result

For every fixed matrix A in R^(n x n), every explicitly given finite family F of M >= 2 matrices, and every 0 < epsilon < 1/2, the algorithm fixes every query vector and every choice between A and A-transpose **before any answer**. It returns a member B of F satisfying

    ||A - B||_F <= (3 + epsilon) min_{D in F} ||A - D||_F

with probability at least 0.99, using at most

    4,000,000 sqrt(log(2M)) epsilon^(-2)

matrix-vector queries. Consequently, **b = 0** suffices in the exact RE-06 formulation. The actual number of calls is min(n, s + k + ell), with the parameters below.

This is an exact-real-arithmetic theorem. The mathematical argument is complete as written, but it has not been independently refereed or formalized in a proof assistant. The numerical tests are supplementary evidence and are not a replacement for the proof. No claim of finite-precision certification or optimal leading constants is made.

## Idea

A small initial right sketch does not need to estimate every candidate's full error accurately. It selects a candidate B0 for which the residual A - B0 has a small singular-value tail after the first r singular values. A separate pair of independent, already queried right and left sketches reconstructs the low-rank part of that residual. Finally, choosing the member of F nearest the corrected surrogate yields the 3 + epsilon factor.

The key proved bound is

    P[ ||CG||_F^2 < (1 - eta) sum_{j>r} sigma_j(C)^2 ]
        <= exp(-s r eta / 4),

for a fixed C and an n-by-s Gaussian G with variance 1/s entries. A union bound over M residuals is inexpensive once s r is proportional to log M / eta. There is no union bound over M reconstructions: the chosen residual is independent of the separate reconstruction sketches.

## Exact parameters

All ceilings are upward integer rounding. All unqualified logarithms are natural.

    eta = epsilon / 4
    L = ceil(log_2(2M))
    r = ceil(sqrt(L))
    s = ceil(32 L / (r eta) + 64 / eta^2)
    k = r + 1 + ceil(256 r / eta)
    ell = k + 1 + ceil(256 k / eta)
    N = s + k + ell

If n <= N, precommit to all n standard basis right queries, recover A, and select the nearest candidate exactly. Otherwise, precommit to s + k right Gaussian queries and ell left Gaussian queries. These sufficient constants are conservative; at ordinary numerical matrix sizes, the theorem parameter choice often uses exact recovery.

The failure-probability upper bound proved in the note is

    exp(-8) + 2 exp(-16) + 1/128 + 1/524288
      = 0.008150095046884763 < 0.01.

## Archive contents

- `solution.pdf`, `solution.tex`: full theorem, algorithm, proofs, probability accounting, query accounting, edge cases, and references.
- `notes/proof_audit.md`: a compact map of the critical mathematical and model checks.
- `notes/sources.md`: primary-source links and the exact scope of their use.
- `code/re06.py`: matrix-vector-oracle reference implementation.
- `code/test_re06.py`: 11 unit tests, including query-transcript auditing and a deliberately bad initial choice corrected by reconstruction.
- `code/verify.py`: reproducible spectral-tail, pseudoinverse, and end-to-end checks.
- `results/`: actual test logs and CSV/JSON outputs from the supplied run.
- `requirements.txt`: Python dependencies.
- `build_pdf.sh`: rebuilds the PDF with `pdflatex` without leaving intermediate build files in this folder.
- `MANIFEST.sha256`: hashes of the deliverables, excluding the manifest itself.

## Reproduce the checks

Python 3.10 or later is required by the type annotations. Install dependencies and run from the archive root:

```sh
python -m pip install -r requirements.txt
cd code
OPENBLAS_NUM_THREADS=1 python -m unittest -v test_re06
OPENBLAS_NUM_THREADS=1 python verify.py
```

On platforms that do not support the inline environment-variable syntax, run the Python commands without the `OPENBLAS_NUM_THREADS=1` prefix. Limiting BLAS threads is only a convenience for repeatability and small-matrix performance.

The supplied run used Python 3.13.5, NumPy 2.3.5, and SciPy 1.17.0. Results can vary slightly with the numerical libraries and linear-algebra backend. The global verification seed is 20260912.

To rebuild the PDF, install a LaTeX distribution with `pdflatex`, the Latin Modern fonts, and the standard packages named in `solution.tex`, then run:

```sh
./build_pdf.sh
```

## Use the reference implementation

From the `code` directory:

```python
import numpy as np
from re06 import approximate

# The algorithm receives only these oracles, not the explicit A below.
n = 12
A = np.diag(np.linspace(0.0, 1.0, n))
family = [np.zeros((n, n)), np.eye(n), 0.5 * np.eye(n)]

result = approximate(
    family=family,
    n=n,
    epsilon=0.25,
    matvec=lambda v: A @ v,
    rmatvec=lambda v: A.T @ v,
    seed=123,
)
B = family[result.selected_index]
print(result.mode, result.oracle_calls, result.selected_index)
```

This small example uses the predetermined exact-recovery branch. The implementation is still floating point: “exact” names the full-column-query branch, not a claim that NumPy performs exact real arithmetic.

To inspect the nonadaptive sketch path on small matrices, specify **experimental** widths:

```python
from re06 import make_sketch_plan, collect_answers, postprocess

plan = make_sketch_plan(n=64, s=3, k=8, ell=18, seed=123)
# Every side and vector is already fixed here:
query_schedule = plan.queries()
# Given your 64-by-64 target oracles and explicit family:
# answers = collect_answers(plan, matvec, rmatvec)
# result = postprocess(plan, answers, family)
```

Smaller user-selected widths do **not** automatically inherit the theorem's universal 0.99 guarantee. Finite precision, pseudorandom sampling, numerical rank decisions, and numerical least-squares tolerances also differ from the exact theorem model.

## Observed checks, not a statistical proof

All 11 unit tests passed. The supplementary audits checked 846 flat-spectrum cases, 3,000 nonflat spectra in the Chernoff algebra, and four pseudoinverse expectations with 5,000 Monte Carlo trials each.

The end-to-end experiment used four fixed families and 160 independent seeds per family, for 640 runs in total, with dimensions smaller than the theorem's sufficient dimensions. Every final selection was optimal in those recorded runs. In the rank-one-distractor family, the initial candidate exceeded the target approximation factor in 148 out of 160 runs, but the correction returned an optimal candidate in all 160. This illustrates why the proof does not need a constant-factor initial candidate. It does not establish a universal guarantee at the smaller experimental dimensions.

## Source and scope

The requested formulation is the public RE-06 problem in `ajt60gaibb/OpenProblemsInNLA`, read through its website. The note attributes the independent two-sided low-rank reconstruction to the existing sketching literature and proves the exact quantitative bounds it needs. It makes no claim that the repository has accepted this resolution, that an outside expert has verified it, or that the stronger nonadaptive 1 + epsilon question is resolved.
