# Exact verification

All mathematical checks use Python's standard library and exact `fractions.Fraction` arithmetic. Decimal strings are displays, not the basis of a comparison or a proof. No numerical eigensolver, floating-point pivoting, Monte Carlo simulation, or external package is required. Use Python 3.10 or newer.

## Main regression suite

From this directory, run:

```sh
python test_suite.py
```

The saved run in `results/test_suite.txt` passes ten tests. It regenerates the rank-eight certificate and compares the actual fractions with the saved records. It also checks pivot probabilities, zero-probability LU entries, exact early stopping, the determinant identity, the scaled inverse, all history counts through rank seven, an independent actual-update calculation, and the unit-diagonal replication identity.

These are programmatic self-checks, not a formal proof assistant or independent peer review. The general all-rank claim is established by the manuscript's mathematical argument, not by extrapolating finite tests.

## Stand-alone counterexample

```sh
python verify_ra03_2x2.py --out results/ra03_2x2.json
```

The script enumerates all four entry pivots of `[[2,1],[1,2]]` and verifies the expected squared error `18/5`, compared with optimal rank-one squared error `1`. Its calculations are independent of the scale-separated family.

## Exhaustive actual-pivot computation

```sh
python exact_enumeration.py --r 2 --t 1/100 --out results/enumeration_r2.json
python exact_enumeration.py --r 3 --t 1/100 --out results/enumeration_r3.json
```

`exact_enumeration.py` recursively performs the actual rank-one updates and probability-weighted sums. It does **not** use the manuscript's determinant-cancellation identity to compute expectations. Memoization combines identical residual states, not different probability masses. Zero-probability pivots are omitted; an exactly zero residual stops the algorithm.

The family is SPD of order `r+1`. For `epsilon = t^((r+1)^2)`, let `G = epsilon^r A^(-1)` and `nu = ||L^(-T)e_n||^2`. The exact bounds

\[
\frac{\epsilon^r}{\operatorname{tr}G}
\le \lambda_{\min}(A)
\le \frac{\epsilon^r}{\nu}
\]

enclose the optimal error without approximating an irrational eigenvalue. Thus the ratio intervals in the JSON files are rigorous rational enclosures.

The command-line exhaustive checker is limited to ranks one through four to prevent accidentally launching a very large exact computation. The library routine expects a real PSD square matrix and also supports the rank-deficient replica used below.

## Rank-eight certificate

```sh
python exact_certificate.py --r 8 --t 1/100 --out results/exact_r8.json
```

This checker retains only the `2^r` Cholesky histories and `4^r` LU histories counted in the proof. It computes exact maxima of all their prefix normalizers and verifies the necessary retained prefix and final pivot blocks. The discarded histories have nonnegative error contributions, so discarding them preserves a lower bound.

At rank eight, the source matrix has order nine and `epsilon = (1/100)^81`. The checker examines 285 pivot blocks. The resulting exact fractions imply

\[
\text{Cholesky ratio}>255.85420697,
\qquad
\text{LU squared-error ratio}>65461.37522779.
\]

Both exceed 99 percent of their respective limiting values, `256` and `65536`. The exact numerators and denominators are stored in the JSON record. The extremely small eigenvalue scales are intentional. Running ordinary double-precision linear algebra on this matrix would not reproduce a trustworthy certificate.

`results/exact_r3.json` supplies a smaller retained-history record. A run at a rational `t` that is not small enough may produce a weaker lower bound; a failure of a 99-percent flag is not a counterexample to the asymptotic theorem. Failure of a required inverse means that parameter choice is not certified by this implementation.

## Unit-diagonal replication

```sh
python verify_replication.py --out results/replication.json
```

The script constructs a rational isometric embedding of a `3 x 3` SPD matrix into a `6 x 6` unit-diagonal PSD matrix, using multiplicities `(4,1,1)`. It checks the isometry, the diagonal, entrywise positivity, and preservation of trace and squared Frobenius norm, then exhaustively compares both algorithms after one and two pivots. The general extension to SPD correlation matrices uses the limiting perturbation proof in the manuscript; the finite test checks the underlying exact replication identity.

## Files and reproducibility

`rational_linalg.py` contains the exact matrix utilities and the single authoritative implementation of the family. The parameter exponent is always `(r+1)^2`; there are no alternate experimental exponents in this package.

JSON records include elapsed timings for convenience. Those timings can change on regeneration, so the regression suite compares mathematical fields rather than requiring byte-identical JSON. In the manuscript's table, displayed decimal lower bounds are truncated downward. Full decimal displays in JSON may be rounded; use the fraction fields for mathematical comparisons.
