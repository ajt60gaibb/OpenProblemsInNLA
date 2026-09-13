# PF-01: second-round structural results

**Status: partial research contribution. The exact PSD-rank function is not determined.**

Read `paper/pf01_structural_obstructions.pdf` first. It contains the arguments, their assumptions, the exact finite calculation, and the surviving gap. Editable LaTeX is alongside it.

## Results added in this round

In a hypothetical real size-four factorization, at order eight at most 65 of the 70 factors on each side can be rank one. At order nine the corresponding maximum is 64 of 126. The argument treats positive-dimensional fibers separately from isolated polynomial roots.

A family of real symmetric 4-by-4 matrices whose fixed-cardinality subset sums are orthogonal projections has coefficient span at most five, provided `3 <= r <= n-2`. This yields a mixed-rank requirement and 252 covering constraints for the affine factor side which a size-four order-nine factorization would necessarily have.

The homogeneous quartic space satisfying the required first-derivative conditions at the 126 four-subsets of nine elements has exact dimension **90**, not 81. The package gives a complete basis and integer/finite-field rank certificates. A hypothetical determinant must have a nonzero component in the nine extra directions. Omitting these directions would invalidate the attempted lower-bound extension.

These results do **not** prove rank five at orders seven, eight, or nine. The preceding unrestricted bounds remain unchanged:

`max(4, ceil((sqrt(8*n+9)-1)/2)) <= PSD-rank(M_n) <= ceil(2*sqrt(n-2)), n >= 5.`

The earlier proof package is preserved without modification in `prior/PF01_research_pack.zip`. Its cited order-five input is attributed there to Colbrook. Neither the earlier draft nor the general new arguments are independently reviewed or formally verified.

## Verification

Run from this extracted directory:

```sh
python -m pip install -r requirements.txt
python code/verify_round2.py
python code/verify_prior.py
```

The first command regenerates the quartic-space certificate, the entrywise-square rank certificate, the algebra checks, the explicit relaxation witness, and the positive controls. The second reruns the preceding manuscript's finite and numerical checks.

The quartic certificate uses an exact integer identity `A @ F == 0`, an explicit nonzero 405-by-405 minor of `A` modulo the prime 1000003, and an explicit nonzero 90-by-90 minor of `F` modulo the same prime. Matching upper and lower bounds establish the rational and real ranks. This is not a floating-point rank decision.

The scripts do not formally verify the general real/complex algebraic proofs. Read `notes/PROOF_AUDIT.md` for the critical assumptions.

## Numerical searches are not certificates

`experiments/best_failed_n7_size4.npz` is explicitly **not a factorization**. Its maximum entry discrepancy is about 0.15136. The stored local-search logs are retained as evidence of what was attempted, not as evidence of nonexistence.

To repeat exploratory searches:

```sh
python code/search_factors.py 7 4 --root-rank 4 --seeds 30
```

The code has input checks, a reproducible random seed per run, an analytic gradient, and a stored gradient sanity check. Optimizer results can vary with numerical libraries. Nonzero residuals, solver termination, and local minima do not establish lower bounds.

## Contents

`paper/` contains the new manuscript. `code/` contains the executable verification and search programs. `verification/` contains the actual logs, exact matrix/minor records, and inspection record. `experiments/` contains the retained historical searches and one failed candidate. `notes/` documents proof dependencies, source attribution, and the status boundary. `prior/` preserves the earlier archive. `MANIFEST.sha256` checks file integrity.

No repository changes were made. No full-resolution or formal-verification status is claimed.
