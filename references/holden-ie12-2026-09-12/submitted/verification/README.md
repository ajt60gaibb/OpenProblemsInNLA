# Recorded verification

The files in this directory were generated or checked while preparing this archive on 12 September 2026.

## Executed tests

`exact_tests.txt` records a successful run of `python code/test_exact.py`: all nine groups pass. Arithmetic comparisons in this suite use Python integers and exact `Fraction` values, except where the test concerns discrete metadata. This checks finite instances of the implementation and constants, not every input covered by the mathematical theorem.

`numerical_tests.txt` records the numerical experiment driver. `experiments.json` and `experiments.csv` contain the resulting measurements. The driver records its Python and NumPy versions, uses explicit fixed seeds in the source, and asserts its stated numerical checks. The captured run passes all 15 original-system certificates, all five same-draw backend comparisons, six additional compressed-product budget checks, and 300 rounding diagnostics. Main solver runs use the dense diagnostic backend; compressed routines are also exercised separately and end to end. No timing advantage is claimed.

`solver_demo.txt` records the compressed-backend example run from `code/solver.py`.

Commands used from the archive root:

```sh
python code/test_exact.py > verification/exact_tests.txt 2>&1
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python code/run_experiments.py \
    > verification/numerical_tests.txt 2>&1
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python code/solver.py \
    > verification/solver_demo.txt 2>&1
```

Recorded Python: 3.13.5. Recorded NumPy: 2.3.5. Different numerical libraries or hardware may change final floating-point digits; no bitwise cross-platform reproducibility or finite-precision stability is asserted.

## Document check

The final LaTeX source compiled successfully in repeated `pdflatex` passes with no unresolved references, overfull-box warnings, or compilation errors. The resulting PDF has 10 pages. Every page was rendered at 140 dpi and visually inspected for mathematical glyphs, complete equations, tables, pagination, and clipping. The algorithm listing is kept together on its own page. Source and PDF represent the same final mathematical argument.

The root `SHA256SUMS` file records integrity hashes for all other packaged files. A ZIP integrity check and manifest verification were performed after packaging. Build intermediates, Python bytecode caches, page renderings, third-party full papers, and font files are not part of the archive.

## Limits

These checks are internal. They do not constitute independent peer review, a proof-assistant verification, a statistical proof of the universal success probability, or acceptance by the problem repository. The exact-real theorem is established by the mathematical reasoning in the PDF; experiments only check illustrative executions and components.
