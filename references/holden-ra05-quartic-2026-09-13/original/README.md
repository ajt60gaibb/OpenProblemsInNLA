# RA-05 — unrestricted quartic classification

Prepared for Sidney Holden with ChatGPT, September 2026.

**Result in this package:** a matching-order classification of the unrestricted
quartic case, p = 4, at every query rank and accuracy. **The whole RA-05 target,
which includes every fixed real p > 2, is still only partially resolved.**

Read `manuscript/RA05_unrestricted_quartic.pdf`. The editable LaTeX source is next
to it. `STATUS.md` and `REMAINING_GAP.md` distinguish the completed subtarget from
the original full target.

## The theorem

Let S_4(k, epsilon) be the worst-case minimum number of original rows with
nonnegative weights that preserve the quartic Euclidean residual cost of every
subspace of dimension at most k. The input matrix may have arbitrary rank,
row count, and ambient dimension.

Define

    R(k, epsilon) = min(k^2 / epsilon^2,
                        k^(5/2) / epsilon + k / epsilon^2).

Theorem 1.1 proves, for absolute positive constants c and C,

    c R(k, epsilon) <= S_4(k, epsilon)
                    <= C R(k, epsilon) log^9(2k/epsilon)

for every integer k >= 1 and 0 < epsilon < 1/2. The new second upper branch is

    S_4(k, epsilon)
        <= C (k^(5/2)/epsilon + k/epsilon^2) log^5(2k/epsilon).

The first upper branch and the preliminary original-row reduction use
Lin–Mirrokni–Woodruff, Theorem 1.2. The improved second upper branch is proved
here. Both needed lower constructions are proved here again; the theorem does
not assume an asymptotic claim from the archived earlier manuscripts.

The three orders, ignoring only absolute constants and logarithms, are:

| Accuracy | Optimal order |
| --- | --- |
| epsilon >= k^(-1/2) | k^2 / epsilon^2 |
| k^(-3/2) <= epsilon <= k^(-1/2) | k^(5/2) / epsilon |
| epsilon <= k^(-3/2) | k / epsilon^2 |

Thus epsilon = k^(-1) has order k^(7/2), and epsilon = k^(-2) has order k^5.
These are unrestricted-input-rank results, not just the previous intrinsic-rank
classification. The existence proof has no extra running-time claim.

## What is new in the upper proof

The fixed input is split at an optimal rank-k head. Quadratic head, mixed, and
tail features receive different normalizations. All terms of the quartic
expansion are retained. A controlled number of high-variance mixed directions
are preserved exactly. A separate, anisotropic right-whitening argument handles
the remaining mixed term without an extra square root of k.

Rothvoss partial coloring is repeatedly applied from the current fractional
center. Strictly fractional exceptions are frozen with positive weights instead
of being forced to signs. Three matrix invariants and exact scalar constraints
control the evolving positive measure. Geometric error sums close both the
invariant induction and the cost guarantee. Preliminary row reduction removes
all final dependence on log n and log d.

See `PROOF_AUDIT.md` for the particular assumptions and failure modes checked.
The exact external theorems and locations are in `SOURCES.md`.

## Reproduction

The recorded environment was Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, and
SymPy 1.14.0. A pinned requirements file is included. From the extracted root:

```sh
python -m pip install -r requirements.txt
bash run_checks.sh
```

The default run writes only to `generated_results/`; it does not alter the
packaged results or their hashes. The suite recorded **7,621 assertions**.
Those are finite algebraic and numerical checks, not 7,621 independent proofs.
Two separate standard-library-only commands check the exact certificates:

```sh
python code/check_exact_certificate.py
python code/check_freezing_certificate.py
```

See `REPRODUCIBILITY.md` for exact scope, tolerances, and PDF rebuild commands.

## Exact finite examples

The full-rank witness has 12 integer rows in dimension 8, input rank 8, and
query rank 2. Its supplied head has a proved global optimum of 12. A particular
6-row positive reweighting has relative error 64/145 at each of two exact
rank-two projector queries. This certifies those particular failures; it does
not claim that every 6-row coreset fails for that finite input.

A separate exact example reduces 38 integer rows in dimension 3 to 26
nonnegative weighted original rows while preserving all 15 homogeneous quartic
moments and total mass. It illustrates fractional-exception bookkeeping using
full moment constraints. It is **not** an implementation of the asymptotic
small-discrepancy oracle in the size theorem.

## Files and provenance

`code/` contains the finite constructions and checkers; `results/` contains the
recorded data. `SHA256SUMS` authenticates package contents against the supplied
manifest, not against an external trusted signature. `prior_work/` contains the
preceding `RA05_rank_classification_package.zip` unchanged. Its older results and
status statements remain distinguishable from the present theorem.

The mathematical argument and finite checks were prepared in this conversation.
No independent human or agent review, peer-review acceptance, Lean verification,
or first-discovery certification is claimed. No repository files were changed.
