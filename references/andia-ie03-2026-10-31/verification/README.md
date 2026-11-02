# Computational reproduction — 31 October 2026

Codex reran the author's supplied programs while preparing this contribution.
These records describe computational reproduction, not independent human
peer review, a full-result referee audit, or formal verification.

## Inputs and environment

The research inputs are identified by [SHA256SUMS](../SHA256SUMS).
The supplied matrix hash is
`3bde6b6832b314cbb8d0c92cf0e8ee651ef4e7a657caf4e3a4de051a97b3d99d`.
The PDF, source, bibliography, required figures, matrix, and both verifiers
are byte-for-byte copies of the author's files.

The runs used Python 3.13.5 on macOS 15.6.1, arm64. The dense checker used
NumPy 2.5.4 with the Accelerate BLAS backend. Assertions were enabled.

## Executed checks

1. **Construction and entrywise comparison:** `python3 verify_construction.py`
   completed with exit status 0. The [output](construction.txt) records all
   five stages, 124 local rational pivot checks, all matrix entries, the
   permutation and consistency checks, growth 4608, and first overshoot
   +4608 at step 4089. The signed-pivot digest is
   `a761528e59bee03cd387a0b6b50e3d44efce44fc5d734fe8a326b684f9bfbec0`.
2. **Full dense elimination:** `python -I verify_dense.py`, run from the
   matrix directory in the isolated environment described above, completed
   with exit status 0. The [output and timing](dense.txt) report
   `PASS: Hadamard, completely pivoted, growth = 4608`; wall time was
   119.01 seconds. The program reads only the explicit matrix, checks the
   Gram matrix, and checks every pivot against the whole active matrix.
3. **Regeneration from the relocated submission:**
   `python -I verify_construction.py --matrix /tmp/ie03-regenerated.npy --write-matrix --pivots /tmp/ie03-pivots.csv`
   completed with exit status 0. The [output](regeneration.txt) repeats the
   construction checks. Comparing the regenerated matrix with the submitted
   `matrix.npy` using `cmp` also returned exit status 0.

The first two runs used the author's supplied directory. The regeneration
run used the copied submission directory; the hash manifest binds both
runs to the same unchanged research inputs. The dense checker does not
print individual pivots or a pivot-sequence digest. No such output is
attributed to it here. Its arithmetic and assertion requirements are
explained in the [reproduction guide](../README.md#reproduce-the-checks).

## Scope

The runs reproduce the finite counterexample. The construction route uses
the manuscript's lifting lemma for the lifted pivot comparisons; the dense
route explicitly checks all 4096 pivots. The infinite family is the
manuscript's Corollary 1, obtained by the same lifting argument, rather than
an assertion that an infinite family was tested computationally. The
asymptotic conjecture is outside the verified result.

No independent full-result audit or publication was supplied. The author
therefore requests **Solution claimed** under the catalog's evidence policy.
