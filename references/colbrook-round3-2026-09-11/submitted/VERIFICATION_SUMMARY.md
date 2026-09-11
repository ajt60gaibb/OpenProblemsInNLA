# Supporting verification summary

**All programmed assertions passed.** This is supporting evidence, not independent refereeing, formal proof verification, or a numerical certification of the stated probability theorem.

## Exact calculations

The code verifies the symbolic determinant and discriminant of the n = 3, k = 2 conditional Krylov pencil; its real root-locus polynomial; and the exact sign-family threshold comparison. The final rational threshold is $210^2=44100<45602=2\cdot151^2$. Finite-field sign, parabola, flip-count, and row-sum identities are checked with integers on the listed prime sample.

## Numerical diagnostics

| Check | Recorded coverage |
|---|---:|
| Standard weighted Krylov matrix cases | 200 |
| Standard eigenpair identities | 2,530 |
| Direct Fourier/Krylov model comparisons | 17 |
| Standard finite-difference eigenpair derivatives | 71 |
| Complex conditional-pencil tests | 99 |
| Sampled conditional root paths | 11 paths, 321 samples each |
| Additional high-precision stress cases | 8 matrices, 46 eigenpairs |
| Stress-test decimal precision | 140 digits |
| Sign-family primes | 18 |
| Small dense SVD comparisons | 4 |

The standard tests' largest relative sensitivity-identity residual was 4.793e-15; the largest direct model discrepancy was 2.715e-15; and the finite-difference relative error was 1.880e-09. Numerical precision and normalizations are described in the scripts.

The high-precision tests include cyclic weights with ratio $10^{24}$, closely clustered rational unit-circle nodes, and weights differing from the defective uniform example at scale $10^{-35}$. They also recompute perturbed compressions for finite-difference checks. They are not interval-certified calculations.

For the explicit example p = 1009, the matrix has order 1,018,081. The kernel FFT gives a diagnostic condition number of approximately 1.207467429052, versus the proved analytic upper bound 1.213433521416. The large dense matrix is not constructed.

## Important limitations

The finite path samples do not certify the continuous root-locus length estimate. The finite-prime FFT checks do not prove the classical mixed Weil bound. The diagnostics do not establish the probability guarantee by Monte Carlo and do not implement a finite-precision eigenbasis algorithm with that guarantee. The manuscripts supply the mathematical arguments and isolate the imported theorem.

## Recorded files

`verification/check_results.json` and `.txt` contain the main run; `verification/stress_ie10_results.json` contains the high-precision run. Execution instructions and dependencies are in `verification/README.md`. The scripts use fixed seeds where random diagnostic samples are generated.
