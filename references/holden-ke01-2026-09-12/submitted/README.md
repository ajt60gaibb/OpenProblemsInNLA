# KE-01: research report and exact-arithmetic checks

**This is a partial-results package, not a complete solution of general KE-01.**

The requested uniform bound `soft-O(k^omega_0 + nnz(A) * kappa)` is not proved here. The main report contains a full proof of a restricted exactly-flat-tail theorem, a general baseline, explicit counterexamples to several tempting shortcuts, and a precise statement of the unresolved algorithmic step. No impossibility result or claim of novelty is made.

Start with **`report/report.pdf`** (15 pages). The editable source is **`report/report.tex`**. `STATUS.md` gives a claim-by-claim scope ledger.

## Mathematical contents

The general CGLS baseline achieves

\[
O\!\left(\operatorname{nnz}(A)
\min\{n,\;k+1+\kappa\log(2/\varepsilon)\}\right).
\]

Its physical-residual guarantee follows from the exact identity
`||x - A^{-1}b||_{A^T A} = ||Ax - b||_2`, combined with a polynomial that vanishes at the outliers and is Chebyshev-small on the remaining spectrum. The report covers `k=0`, exactly flat tails, finite termination, and the regimes in which this cost already fits KE-01.

The restricted theorem applies to an **explicitly sparse SPD matrix** `M` with eigenvalues satisfying `mu_{k+1} = mu_n = alpha`. It obtains the desired additive sparsity/outlier form `soft-O(nnz(M) + k^omega_0)` with success probability at least 0.99. The proof recovers the unknown `alpha` algebraically from a small principal characteristic polynomial, constructs a sparse exact low-rank representation of `M - alpha I`, and solves a small preconditioned core with a fully accounted Euclidean-residual error transfer. The sparse-embedding and fast-algebra primitives are cited rather than claimed as new.

A nonsymmetric corollary has cost `soft-O(sum_i w_i^2 + k^omega_0)` for an exactly flat singular tail, where `w_i` is row `i`'s nonzero count. It reaches the target when maximum row support is polylogarithmic. It does **not** establish the general bound with `nnz(A)`.

The report also proves that a matrix with `2n-1` nonzeros and one outlier can have `n^2` nonzeros in its Gram matrix. Additional exact examples test a regularized-sketch inference, a rank-one Nyström spectral-error inference, and the loss of algebraic low rank when an exactly flat tail is replaced by a narrow interval. These are not lower bounds against all algorithms.

## Files

```text
README.md                    Package guide
STATUS.md                    Proven statements and unresolved scope
MANIFEST.sha256              Checksums of the delivered files
report/
  report.pdf                 Mathematical write-up
  report.tex                 Editable LaTeX source
code/
  exact_arithmetic.py        Sparse rational CGLS and algebraic helpers
  verify_exact.py            Reproducible exact verification suite
  solve_json.py              CLI for the baseline rational solver
  example_instance.json      Small nonsymmetric example
  requirements.txt          Verification dependency
results/
  README.md                  Interpretation of the checks
  exact_checks.json          Exact-identity and edge-case records
  cgls_cases.csv             Per-matrix CGLS records
  example_solution.json      Exact solution of the bundled example
```

## Reproduce the checks

Use Python 3.10 or newer. The recorded run used Python 3.13.5 and SymPy 1.14.0. From this directory:

```bash
python -m pip install -r code/requirements.txt
python code/verify_exact.py
```

The script writes its records under `results/`. To avoid modifying the delivered records:

```bash
python code/verify_exact.py --out reproduced_results
```

Expected status is `ALL_CHECKS_PASSED`, with 66 CGLS cases, 209 checked Chebyshev inequalities, 8 flat-tail cases, 28 checked inner-PCG iterates, 5 Gram-fill cases, 9 Nyström cases, and 3 row-sketch cases, plus additional edge checks. The run-time field is only the duration of the verification script and is not a performance claim.

All mathematical comparisons use exact rational arithmetic. The tests are not a formal proof assistant verification, an implementation of fast matrix multiplication, a quantitative experiment establishing 0.99 success probability, or a benchmark establishing asymptotic complexity. Small test sketches are fixtures for algebraic identities, not the full theoretical OSNAP construction.

## Run the baseline solver

The JSON solver uses only the Python standard library:

```bash
python code/solve_json.py code/example_instance.json
python code/solve_json.py code/example_instance.json --out answer.json
```

The example returns `x = ["-3/25", "2", "3"]`, with exactly zero residual. Its format is:

```json
{
  "n": 3,
  "entries": [[0, 0, "50"], [0, 1, "2"], [0, 2, "1"],
              [1, 1, "1"], [2, 2, "1"]],
  "b": ["1", "2", "3"],
  "epsilon": "1/100000",
  "max_iterations": 3
}
```

Indices are zero-based. Supply rational entries as strings such as `"7/13"` to avoid unintended binary floating-point conversion. Duplicate COO entries are summed. `epsilon=0` requests exact termination; otherwise the routine stops on the squared physical relative-residual test. An explicit cap can result in a nonconverged result. Exit codes are 0 for convergence, 2 for reaching the cap, and 1 for invalid data or detected breakdown.

This executable is the **baseline** algorithm, not the general KE-01 target algorithm. Fraction numerators and denominators can become large. No floating-point stability or near-linear bit-complexity claim is attached to it.

## Build the report and check the archive

With a standard TeX Live installation:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report uses standard TeX packages and does not require external image assets. No font files are included. From the unmodified package root, Unix-like systems can verify the delivered checksums using:

```bash
sha256sum -c MANIFEST.sha256
```

Rerunning the verifier or rebuilding the PDF changes generated files, so it can intentionally change their checksums.

## Source problem

The problem and its cited literature were read as web documents. Exact references, theorem numbers, and links are in the report bibliography. The problem entry is:

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/linear-systems-and-elimination/KE-01

The remaining gap is the general bounded-tail, sparse-input construction with all setup and repeated-application costs inside the requested additive bound. This package does not fill that gap.
