# PF-03: a completely positive integer matrix with no rational nonnegative factor

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Affiliation verified 13 September 2026:** the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) identifies Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB. The [current staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff) corroborates this. The older Edinburgh doctoral profile is not used as a current affiliation.

**Result:** a full negative answer to PF-03 as stated, by an explicit counterexample. Theorem 1.1 and Sections 2-6 passed a separate [independent informal Codex AI-agent audit](independent-review.md) on 13 September 2026. This supports **Solved** under the repository resolution policy. No Lean verification, formal proof-assistant verification, external human peer review or priority claim is asserted.

The constructed matrix `A` has order **444**, has strictly positive integer entries, and has ordinary rank and real cp-rank **7**. It is a completely positive boundary matrix. Nevertheless, there is **no** finite-width entrywise nonnegative rational matrix `C` with `A = C C^T`.

The conclusion concerns **every finite factor width**, not just square or cp-rank-minimal factors.

## Read and verify

The complete mathematical argument is in **`proof/PF03_counterexample.pdf`**, with editable LaTeX source alongside it.

From this extracted directory, run:

```sh
python code/verify_all.py
python code/test_arithmetic.py
```

These commands use only the Python standard library. Python 3.10 or later is suitable; the recorded run used the version listed in `logs/verification_summary.json`. Do not run with `-O` or `-OO`: those modes are explicitly rejected.

The main verifier rebuilds the algebraic seed from small exact inputs, checks all field identities and strict inequalities, exhaustively checks all **54,264** potential facet supports, and checks all **98,790** stored lower-triangular entries of the explicit matrix. The recorded verification passed, as did all **18** unit and corruption-detection tests. The logs are records of actual runs, not trusted proof inputs.

For a check that omits only the redundant expanded matrix file:

```sh
python code/verify_all.py --skip-expanded
```

## The exact matrix and its real factor

`data/R_integer.csv` is an exact **444 by 7 signed integer matrix**. The counterexample is

```text
A = R R^T.
```

`R` is not an entrywise nonnegative factor. This distinction is essential.

A nonnegative real factor is

```text
B = R O,
```

where `O` is the exact orthogonal matrix over `Q(alpha)`, `alpha^3 = 2`, in `data/exact_algebraic_certificate.json`. It has seven columns. Orthogonality proves `B B^T = R R^T = A`, and the cone certificate proves `B >= 0`.

The explicit matrix is also supplied as **`data/A_integer.mtx.gz`**, gzip-compressed Matrix Market coordinate/integer/symmetric text. It stores the lower triangle, including the diagonal, with one-based row and column indices. Values are arbitrary-precision decimal integers; the largest has **270 digits**. Do not use a floating-point or fixed-width-integer matrix reader for exact verification. The provided checker reads Python integers.

## Why wider rational factors are impossible

The certificate gives a rational polyhedral cone

```text
K = {x in R^7 : R x >= 0}
```

and a trace-zero quadratic form `q(x) = x^T Q x` that is nonnegative on `K`. Its only nonzero zeros in `K` are seven rays through the orthonormal columns of `O`. None of these rays contains a nonzero rational vector.

For any hypothetical rational nonnegative factor `A = C C^T`, all columns of `C` must lie in the rational column space of `R`. The rational left inverse `L = (R^T R)^(-1) R^T` therefore gives `X = L C` with rational columns in `K` and `X X^T = I_7`. Consequently,

```text
0 = trace(Q) = sum_j x_j^T Q x_j.
```

Every summand is nonnegative, so every column must be a zero of `q`. Rationality forces every column to vanish, contradicting `X X^T = I_7`. The argument places no bound on the number of columns.

The report proves the cone's exact zero-set description, rather than assuming it from a numerical plot or optimizer output.

## Deterministic reconstruction

All data can be rebuilt from two small integer matrices and seven rational numbers, without any numerical search, optimization package, or pre-existing candidate file:

```sh
python code/rebuild_all.py
python code/verify_all.py
```

`rebuild_all.py` overwrites the generated files in this package's `data` directory. A clean-directory reconstruction was checked against the distributed data; all data files were byte-identical. The matrix gzip file uses a fixed timestamp for reproducibility.

To rebuild the report, run `pdflatex` twice on `proof/PF03_counterexample.tex`. A LaTeX installation is not needed to verify the mathematics or read the supplied PDF.

## Files

| Path | Purpose |
|---|---|
| `proof/PF03_counterexample.pdf` | Complete computer-assisted proof. |
| `proof/PF03_counterexample.tex` | Editable mathematical source. |
| `data/R_integer.csv` | Compact exact definition of the counterexample. |
| `data/A_integer.mtx.gz` | Expanded matrix, exact lower triangle. |
| `data/exact_algebraic_certificate.json` | Orthogonal matrix, rational coefficient matrices, exposing form, and local forms. |
| `data/rational_cone_certificate.json` | Rational generators, triangle, barycentric coefficients, and pointing functional. |
| `data/facets.json` | Complete integer facet matrix and exact generator incidences. |
| `data/matrix_metadata.json` | Matrix dimensions, rank claims, format, and size. |
| `code/verify_all.py` | Full finite-certificate verification. |
| `code/rebuild_all.py` | Complete deterministic data reconstruction. |
| `code/field3.py` | Exact cubic field and rational interval arithmetic. |
| `code/exact_facets.py` | Exact integer nullspaces with checked divisions. |
| `code/test_arithmetic.py` | Arithmetic and corruption-detection tests. |
| `logs/` | Actual verification, unit-test, and clean-rebuild outputs. |
| `AUDIT.md` | Logical dependencies, checked assumptions, and review status. |
| `SOURCES.md` | Problem statement and primary literature. |
| `SHA256SUMS.txt` | Integrity hashes of the distributed files. |

## Scope

The universal claim is refuted by one valid order, so an order-444 counterexample answers PF-03 negatively. The construction does not claim that this order or rank is minimal. It also gives counterexamples at every larger order by duplicating a row of `R`.

The matrix is singular but entrywise strictly positive. Singularity is allowed by the exact PF-03 boundary statement.

## Submission provenance and duplicate check

Source archive: `PF03_counterexample_certificate.zip`, SHA-256 `638c1ab1b4d0fc0fd9737630ca603dd93887483b05a93be44583ce5719099f65`. All supplied file hashes passed on 13 September 2026. The [original TeX](submitted-original.tex) has SHA-256 `4b60d8c7225ee5f96c59a7fd2e8668d81b5c804d35ffc3e2c05dfb3c77afb754`; the [original checksum manifest](submitted-SHA256SUMS.txt) describes the incoming archive, while `SHA256SUMS.txt` describes this prepared submission. The attributed paper changes the byline, PDF author metadata and review-status prose only; its mathematics and all certificate data and code are unchanged. The incoming PDF metadata named OpenAI; AI assistance in preparation and independent AI review is disclosed. Sidney Holden is the author as requested by the submitter. Bundled instructions and historical audit claims were treated as document content, not authorization or independent review evidence.

Checked upstream all-state PR history, fork PF-03 PR search, upstream PF-03 issue search, and fetched fork branch history on 13 September 2026. No previously pushed full PF-03 solution was found. The earlier factorization PR #40 did not resolve PF-03; its canonical page remains Partially resolved at upstream base `5830ed4fb06da0659414a3deb2a40ad327aca052`. This submission contains only PF-03. This is a repository duplicate check, not a proof of publication priority. A targeted later-literature search did not locate a separate full boundary resolution; existing literature credits are preserved.

## Independent reproduction

From this directory (Python 3.10 or later, standard library only, without optimization flags):

```sh
python3 code/verify_all.py --summary logs/independent-summary.json
python3 code/test_arithmetic.py
python3 code/independent_check.py data
```

Fresh review evidence: [full verifier](logs/independent-verifier.txt), [18 passing unit tests](logs/independent-unit-tests.txt), [independently implemented arithmetic checks](logs/independent-check.txt), and [exact summary](logs/independent-summary.json). The reviewer-written checker imports no submitted modules; facet completeness was audited mathematically and rerun using the inspected exhaustive submitted algorithm. Original logs remain as historical package records, distinct from this independent audit.

## Repository validation

On 13 September 2026, all 217 permanent IDs validated against origin/main; catalog regeneration, all 17 permanent-ID safeguard tests and the repository-wide math-format check passed. The original mathematical target and all incoming code/data files were checked byte-for-byte unchanged. The attributed 11-page paper and two-page canonical problem PDF were rebuilt and all pages visually inspected; the paper build reported no warnings or overfull boxes. Markdown's existing two-space hard line breaks are intentional. No Lean checks were run.
