# Reproducibility and interpretation of the tests

## Commands executed

The supplied scripts were run successfully in the recorded environment:

```bash
python tests/exact_checks.py --output results/exact_checks.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python tests/numerical_checks.py --output-dir results
./build.sh
```

The final package was also exercised with `./reproduce.sh`. Its logs and machine-readable outputs are under `results/`. The shell script does not install dependencies automatically; install `requirements.txt` first in a suitable Python environment.

## Exact algebraic checks

SymPy rational and symbolic arithmetic checks five residue-class determinant witnesses, three head interpolation fixtures, six vector resolvent identities, 105 positive-pole coordinate residues, the origin residue, Schur-complement identities for the anchored variational problem, head and graph identities, common-shift determinant and evaluation identities, and 13 symbolic Pascal identities. A tied-singular-value fixture verifies a frozen-minimizer descent direction without a uniqueness premise.

Four interval-cover fixtures use exact `fractions.Fraction` arithmetic. They include repeated root locations, verify disjoint selected intervals and their root counts, and verify coverage and the total-length bound. These are finite realizations of the covering construction; the general covering argument is the written proof in Section 3.

Every exact assertion passed. These scripts are not a formalization of the universal theorems, and rational fixtures are not Gaussian samples.

## Numerical head diagnostics

There are 96 records with `b,t` in `{1,2,3,4}`, three spectral patterns, and two seeds. The largest relative discrepancy for the analytic derivative identity is approximately `6.05e-14`; for its finite-difference check, approximately `6.75e-5`. The largest normalized moment residual is approximately `4.03e-16`, and the largest relative translation residual is approximately `8.10e-13`.

The asserted interpolation upper bound is deliberately conservative. Finite sampled norms lying below it do not establish its high-probability guarantee. That guarantee comes from the proof, not an empirical success frequency.

## Original algorithm diagnostics

The code uses two-pass block Arnoldi with SVD-based numerical-rank detection in binary64. There are 81 retained records across seven spectra, three seeds, and several depths. It measures spectral and Frobenius error and the ordered right-vector energy defect directly. At `epsilon=0.1`, 43 records meet all tested criteria; the other, smaller-depth records remain in the CSV rather than being suppressed.

The smallest tested depth at which all three seeds met all criteria was 18 for exact clusters, 10 for a wide unaligned spectrum, 9 for the mixed-multiplicity boundary example, 10 for nonzero-width clusters, 12 for the scalar block, 4 for a full-size starting block, and 5 for the zero-optimal-error example. These tested depths do not identify or estimate the universal constant.

For the zero-error fixture, the implementation uses an absolute `1e-10` tolerance. The theorem itself states exact recovery in exact arithmetic, not recovery to that tolerance. Numerical-rank detection can differ across implementations.

## High-precision diagnostics

Six interpolation solves use 180-decimal-digit mpmath arithmetic. Three scalar fixtures retain gap `1/2` while varying the spectrum `(1,zeta,zeta/2)` through `zeta=1e-4,1e-16,1e-50`. Raw smallest singular values decrease dramatically while anchored evaluation norms remain near `4.0733`. Three block-size-two fixtures provide additional scale-stress checks. The observations do not prove an asymptotic statement. Normalized inverse residuals are backward residual diagnostics, not certified forward-error bounds.

## Environment and integrity

Recorded versions: Python 3.13.5, NumPy 2.3.5, SymPy 1.14.0, and mpmath 1.3.0. Fixed seeds are stored in the code and CSV files. BLAS implementations, numerical-rank choices, and floating-point platforms can change low-order digits. PDF rebuilds can change metadata; reproducible byte-identical PDFs are not claimed.

`SHA256SUMS` records the delivered artifact hashes. It excludes itself and temporary build files. Rerunning tests may legitimately change execution outputs on another platform; recompute hashes only after distinguishing such changes from unintended edits.
