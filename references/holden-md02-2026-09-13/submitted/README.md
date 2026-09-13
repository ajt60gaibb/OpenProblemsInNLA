# MD-02: all-time fixed point and root-moment continuation

**This is not a complete solution or a counterexample to MD-02.**

The manuscript proves an exact complementary-barrier fixed point, global
Picard convergence with an explicit error bound, an equivalent endpoint
expectation criterion, and all-orders/all-times first-two-iterate root
second-moment bounds. The converged-root estimate remains unproved.

The distinction between a finite Picard iterate and the optimizer is essential.
The first two iterate bounds cannot be substituted for the required bound on
the limit. No asymptotic subcase of the displayed theta target is proved here.
The repository status recommendation remains OPEN.

## Files

- `manuscript/MD02_fixed_point_continuation.tex`: complete self-contained proofs.
- `manuscript/MD02_fixed_point_continuation.pdf`: compiled manuscript when PDF compilation succeeds.
- `code/fixed_point.py`: FFT map, deterministic error expression, numerical fixed-point solver, independent theta LP.
- `code/validate.py`: exhaustive small-order checks and numerical diagnostics.
- `results/validation_summary.json`: actual validation outcome and limitations.
- `prior/`: available earlier archives preserved unchanged, not blanket-certified.
- `MANIFEST_SHA256.json`: hashes for the packaged files.

## Reproduce

Python 3.10 or later, NumPy and SciPy:

```sh
python -m pip install numpy scipy
python code/validate.py
```

Compile the manuscript with a standard LaTeX installation:

```sh
cd manuscript
pdflatex -interaction=nonstopmode -halt-on-error MD02_fixed_point_continuation.tex
pdflatex -interaction=nonstopmode -halt-on-error MD02_fixed_point_continuation.tex
```

The exact-arithmetic Picard convergence bound is a theorem. Floating-point
root solves, residual checks, Fourier LP comparisons, and Monte Carlo means
are not interval certificates and do not prove the asymptotic missing estimate.

No independent peer review or historical-priority claim is made.
