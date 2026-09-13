# RE-03: sharper upper and lower bounds

**Status: unreviewed partial research results, not a full solution.**

The requested joint characterization is not established. This package supplies
self-contained proposed proofs, a query-counted reference implementation, and
reproducible numerical checks. No independent review or formal verification has
been completed. Numerical checks do not establish the theorems.

## Main result developed here

For the exact RE-03 model, with `n = 2**L * k`, integers `k >= 1`, `L >= 2`,
and `0 < epsilon < 1/2`, the manuscript argues that

\[
c\min\{n,kL/\varepsilon+k/\varepsilon^2\}
\ \le q_*(n,k,\varepsilon)\le\
C\min\{n,kL^2/\varepsilon+kL/\varepsilon^2\}.
\]

The constants are universal and deliberately conservative. Before taking the
`n` cap, the upper expression is exactly `L` times the lower expression.
This **factor of depth remains unresolved**; it is not hidden in a constant or
in the phrase “near optimal.”

The new upper bound is nonadaptive. It uses a constant-accuracy perforated
pilot to retain enlarged column spaces, followed by one fresh Gaussian
regression shared across all blocks, and then proper rank truncation. The
new depth–accuracy lower bound uses a weighted hierarchical frame packing and
large fixed anchors. It applies to arbitrary measurable randomized adaptive
queries on both sides. The earlier accuracy lower bound is reproduced in
Appendix A rather than treated as an independently verified result.

The same argument retains `q_* = Theta(n)` when `epsilon <= sqrt(k/n)`. It
also rules out `O(min(n, kL + k/epsilon**2))` as a uniform answer: take
`k=1`, `n=2**L`, and `epsilon=L**(-1/2)`.

## Start here

- `manuscript/re03_extended_results.pdf`: 25-page manuscript with the problem,
  proofs, explicit parameters, limitations, and references.
- `manuscript/re03_extended_results.tex`, `two_stage.tex`, and
  `accuracy_appendix.tex`: editable, self-contained LaTeX sources.
- `PROOF_REVIEW.md`: theorem dependencies and the most important audit points.
- `SOURCES.md`: primary sources, versions, and distinctions from related work.
- `STATUS.json`: machine-readable scope and verification status.

The unchanged earlier ZIP and PDF are under `prior/`. They are retained for
provenance, not presented as independent confirmation of the new manuscript.

## Code and oracle accounting

`code/two_stage.py` is the main proposed algorithm. The routine
`approximate_two_stage(oracle, k, epsilon, rng)` uses the theorem's widths and
selects the exact `n`-query baseline when its stated budget is at least `n`.
Every column of every forward or transpose product counts as one query. The
algorithm reads only `oracle.n` and calls `oracle.matvec(v, transpose=...)`.
The tests also exercise an opaque wrapper that has no public matrix field.

`code/peeling.py` retains the simpler, earlier-in-this-package construction
with the weaker `O(min(n,kL**2/epsilon**2))` bound. It is not the headline
upper bound. `code/hodlr.py` supplies block geometry, optimal full-matrix
projection, hard inputs, and a dense test oracle. `code/depth_family.py`
constructs continuous numerical versions of the hierarchical frames. It
does not generate the finite packing proved to exist in the manuscript.

`code/joint_regression.py` is a **conditional solver with supplied rank-k
spaces**. Preparing those spaces from a full SVD is privileged test setup,
not a free step in the general oracle algorithm. The main two-stage solver
instead pays for its pilot and retains larger spaces.

A minimal example, from the package root:

```python
import sys
sys.path.insert(0, "code")
import numpy as np
from hodlr import DenseOracle, is_hodlr
from two_stage import approximate_two_stage

rng = np.random.default_rng(17)
a = rng.standard_normal((32, 32))
oracle = DenseOracle(a)
result = approximate_two_stage(oracle, k=2, epsilon=0.2, rng=rng)
assert result.queries == oracle.queries
assert is_hodlr(result.matrix, 2)
print(result.method, result.queries)
```

At this small dimension, the conservative theorem parameters select the
`n_query_baseline` method. Smaller manually supplied experimental parameters
exercise the nontrivial sketching path, but do **not** inherit the theorem's
0.99 guarantee.

### Arithmetic and resource limitations

RE-03 permits exact real arithmetic and exact SVDs. The reference code uses
IEEE double precision and numerical rank thresholds; it is not an exact-real
implementation or a proof certificate. Widths are computed with Python
integers and rational arithmetic so that very small positive floating-point
accuracies select the baseline without overflow. The code is dense and may
use substantial memory and runtime. Query complexity alone is being claimed;
no practical speedup is claimed for this dense implementation or its loose
constants.

## Reproduce the checks

The recorded environment is Python 3.13.5 and NumPy 2.3.5. The only Python
package dependency is NumPy. From the package root:

```bash
python -m pip install -r requirements.txt
bash run_checks.sh
```

The runner writes a fresh set of reports to `rerun_results/` by default, so it
does not overwrite the recorded evidence in `results/`. A different output
directory can be supplied as its first argument. It also extracts the original
ZIP into a temporary directory and reruns the original verification script
without changing that script. Network access is not used by the checks.

The recorded suites cover the deterministic truncation inequality, Gaussian
inverse moments, noisy block approximation, frame geometry, anchor loss,
fixed-query divergence, adaptive Gaussian posterior identities, shared
regression isotropy, conditional fit risk, query accounting, and extreme
accuracy inputs. All recorded checks passed. See `results/` for counts, seeds,
versions, errors, and Monte Carlo tolerances. A pass is not a proof of a
worst-case randomized guarantee or of a packing entropy bound.

Build the PDF with a LaTeX installation containing the packages named in the
source:

```bash
bash build_pdf.sh
```

This uses `pdflatex` three times in a temporary build directory and replaces
only the final PDF in `manuscript/`. The supplied PDF needs no LaTeX installation
to read.

Verify package integrity before changing or rebuilding files:

```bash
python verify_integrity.py
```

The manifest excludes only itself. Integrity checking certifies file bytes,
not mathematical correctness.

## The missing theorem

A full solution still requires matching the joint dependence on rank, depth,
and accuracy. The present pilot spends `O(kL**2/epsilon)` queries, and the
shared final truncation calculation spends `O(kL/epsilon**2)`. Neither has been
reduced to the combined lower expression, and no matching stronger lower bound
has been established. The discussion of this gap is part of the result, not a
claim that the problem has been fully solved.
