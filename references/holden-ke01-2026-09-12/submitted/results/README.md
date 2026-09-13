# Reading the verification records

`exact_checks.json` reports the deterministic-seed exact rational checks. `cgls_cases.csv` contains a row for each of the 66 CGLS matrices. `example_solution.json` records the output of the bundled baseline-solver example.

The suite checks exact zero residuals, rational orthogonal-matrix identities, characteristic-polynomial factorization, shift recovery, principal-rank selection, Nyström and Woodbury identities, a PSD Gram sandwich, and energy/physical-error inequalities along core PCG iterates. It also checks the explicitly constructed sketch and Gram-fill examples. Assertions do not use floating-point tolerances.

The field `verification_elapsed_seconds` is only the runtime of the small verification script. It is not an asymptotic solver benchmark. Version and timing fields may differ on another machine; fixed-seed mathematical case data should remain the same.

The test sketches in flat-tail cases have deliberately small dimensions. When necessary, a test fixture redraws such a sketch to obtain the rank needed for an identity check. These fixtures do not implement the proof's quantitative OSNAP parameters and are not evidence for the theorem's 0.99 probability or bounded-work guarantee. The theorem uses two independently sampled OSEs with fixed failure budgets and a capped iteration count, with no unbounded retries.

The recorded preconditioner checks use exact diagonal row scalings with squared values in `[1/2, 3/2]`. They test the Gram-sandwich and error-transfer algebra, not the statistical quality of a random embedding. Fast asymptotic dense kernels are not implemented.

Finite exact tests can expose mistakes but do not prove a universal theorem. The mathematical arguments, their external primitives, and the unresolved general gap are in `report/report.pdf`.
