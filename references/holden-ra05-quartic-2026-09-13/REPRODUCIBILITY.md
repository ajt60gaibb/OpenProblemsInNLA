# Reproducibility and evidence limits

## Environment and commands

The recorded run used Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, and SymPy 1.14.0.
The deterministic suite seed is 20260913; the exact freezing row generator uses
seed 909. The pinned requirements record the tested environment, not a claim
that other versions are unsupported.

From the extracted package root:

```sh
python -m pip install -r requirements.txt
bash run_checks.sh
```

The shell script first checks `SHA256SUMS`, then runs the finite suite, then
runs both exact checkers. New results are written to `generated_results/` and
the packaged `results/` files are not modified. The shell script uses one BLAS
thread for more consistent numerical replay.

To run only the exact certificates with Python's standard library:

```sh
python code/check_exact_certificate.py
python code/check_freezing_certificate.py
```

Both accept an optional JSON path. They use integers and `fractions.Fraction`,
not floating-point thresholds. Running Python with `-O` disables assertions;
do **not** use that mode for these checks.

To regenerate the recorded suite into a different directory:

```sh
OPENBLAS_NUM_THREADS=1 python code/verify.py --output-dir /tmp/ra05-quartic-run
```

## What the suite records

The suite has 7,621 assertions. Its category counts and largest recorded
absolute residuals are in `results/verification.json`. Numerical comparisons
use the tolerances shown next to each check, including scale-aware positive
semidefinite comparisons. Large intermediate variance scales can have larger
absolute rounding residuals while still satisfying the stated relative
numerical tolerance. Different BLAS libraries may change final floating-point
digits; the package hashes authenticate the *recorded* data, not a requirement
that every platform regenerate identical JSON floating-point strings.

Tested objects include full quartic residual expansions, optimal-head block
queries, rank-deficient feature metrics, density ratios, constrained Gaussian
variance contraction, protected output directions, right-whitened matrix
variances, and the algebraic equivalence of the three accuracy regimes.

Generic random head/tail inputs are used only for identities and inequalities
that do not assume optimality. The structured sign-pair block inputs have a
separate proof of optimality in the manuscript. Random queries are not used to
certify that an arbitrary head is optimal.

## Exact witness certificate

`exact_full_rank_certificate.json` specifies a 12-by-8 integer matrix, a
particular six-row nonnegative reweighting, and two rank-two rational projectors.
The standalone checker computes the exact input rank, projector symmetry,
idempotence and rank, Euclidean quartic costs, and relative errors. It also
checks the structural parameter inequality used by the manuscript's global
optimality lemma. The checker does not substitute finitely many queries for
that lemma's universal proof.

## Exact frozen-exception example

`exact_fractional_freezing.json` gives 38 integer rows in dimension three,
26 retained nonnegative original-row weights, and stage bookkeeping. The
standalone checker verifies total mass and every homogeneous quartic moment
exactly. Consequently the output preserves every quartic linear-form cost;
the manuscript's Gaussian averaging identity transfers this to every Euclidean
subspace cost.

The example preserves **all** quartic moments with exact nullspace moves. That
is a finite demonstration of positive fractional freezing, not the asymptotic
low-codimension partial-coloring construction in the size proof.

## Rebuild the PDF

A LaTeX installation with pdfLaTeX, Latin Modern, and the packages listed at the
start of the `.tex` file is needed. From the root:

```sh
make pdf
```

This compiles three times in `build/`, leaving the packaged PDF and manifest
untouched. The source uses standard mathematical fonts and has no external
image or font-file dependency. Rendering and visual inspection were performed
on the supplied PDF; rebuilding with another TeX version can change pagination.

## What is not established by these commands

These commands do not validate the published/imported discrepancy, Gaussian,
or restricted-invertibility theorems; instantiate the asymptotic random core
with its conservative constants; implement the full asymptotic coreset oracle;
prove the new mathematical argument in a proof assistant; or establish a
complete theorem for p != 4. The manuscript and explicit dependencies are the
basis of the general claims.

The previous package is archived unchanged. Its verification counts are not
added to this suite's count as if they were independent corroboration.
