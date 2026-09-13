# TR-09: fifth-round research package

**Status: not a full solution of TR-09.** This archive contains a local optimization theorem and a global algebraic comparator. They address different requirements and must not be combined into a claimed solution.

## Read first

The complete mathematical report is `report/TR09_round5.pdf`; its editable source is `report/TR09_round5.tex`. The proof-scope checklist is `PROOF_AUDIT.md`. The preceding fourth-round report is preserved unchanged in `prior/`.

The main new local result is Theorem 4.1. An explicit binary cycle of genuine mixed-factor least-squares blocks has tensor-derivative norm below 1/8 when the normalized Gram matrices of two modes are within 1/(64 ell) of the identity, where ell = 1 + 2 ceil(log2 r). The third mode may have arbitrary coherence and weight imbalance, subject only to nonzero, pairwise noncollinear columns. Corollary 4.2 gives a local residual-halving rate. Theorem 5.1 supplies a uniform once-smoothed event for two orthogonal base modes and an arbitrary third base mode. It does **not** give a random-start basin probability.

Theorem 7.1 is deliberately outside the required algorithm class. It constructs an exact 2r-1-term decomposition using tensor contractions, row-Krylov matrices, and fixed-node interpolation. Its finite-grid success is at least 3/4 for every fixed input with two full-column-rank factor modes and a third mode with nonzero, pairwise noncollinear columns. It uses polynomial field arithmetic without eigenvalue or root extraction. The generated factors depend on the input, and no admissible ALS/GD trajectory reaching them is supplied.

## Reproduce the checks

Use Python 3.10 or later and install the versions in `requirements.txt` (the recorded interpreter was Python 3.13.5).

```sh
python -m pip install -r requirements.txt
python -m unittest discover -s src -p 'test_*.py'
python src/verify_exact.py
OPENBLAS_NUM_THREADS=1 python src/diagnostics.py
```

`rational_hankel.recover` accepts exact rational tensor slices and a rank parameter, not true factors. By default it uses operating-system randomness; an explicit integer seed gives reproducible pseudorandom fixtures. The theorem refers to independent uniform random bits. The implementation returns a failure reason when a sketch is singular or its exact reconstruction checks fail.

To rebuild the report:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error TR09_round5.tex
pdflatex -interaction=nonstopmode -halt-on-error TR09_round5.tex
```

## Recorded results

All 12 implementation tests and all 25 exact-check records passed. The latter comprise a metric-projection identity, two zero-derivative identities, three all-tangent-direction contraction certificates, three boundary examples, and sixteen exact tensor-recovery fixtures. These are finite computations, not a formal proof audit.

All 276 scheduled floating-point runs are in `results/diagnostics.json`: 36 explicitly local runs and 240 random-start runs. For mixed ALS, 57 of 60 starts on the two-orthogonal-base family reached tolerance, while none of the 60 three-coherent-base starts did so within the tested budget. These finite small-dimensional experiments neither prove convergence nor establish an impossibility result. They are not equal-work comparisons.

No independent peer review, proof-assistant verification, novelty certification, polynomial bit-complexity guarantee, or floating-point stability theorem is claimed. The archive does not modify the repository or any external account. The earlier staged theorem's proposed PARTIAL status remains a separate review question; these results do not justify a full-resolution status.
