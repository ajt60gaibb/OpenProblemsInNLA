# KE-02 independent informal mathematical review

Date: 2026-09-12. Reviewer: separate Codex AI agent `/root/review_ke02`, independent of the coordinating submission agent. This is an informal AI-agent audit, not external human peer review or formal verification. No Lean verification was performed.

**Verdict: PASS for the stated partial results only.** Sections 2–5 of the supplied `KE-02/proof.md` are correct. `Partially resolved` is justified under the repository definition of substantive cases inside the original target; `Solved`, `Solution claimed`, and `Lean verified` are not justified by this submission.

## Scope and proof audit

Compared the manuscript against the current canonical `eigenvalues-and-inverse-problems/KE-02/README.md`, `README.md` status definitions, `CONTRIBUTING.md`, and `RESOLVED.md` resolution procedure. The original target quantifies over every normalized Hermitian tridiagonal matrix and every allowed delta. The manuscript retains the real diagonal output, norm bound, exact arithmetic model, and nearly linear operation requirement, but proves only subclasses.

1. **Perturbation lemma.** The quadratic-form row-sum estimate correctly gives `-eta I <= R <= eta I`, including complex off-diagonals. The stated increasing-eigenvalue min–max formula has the correct subspace dimension. Applying the two quadratic-form inequalities gives the per-eigenvalue displacement bound eta.
2. **Theorem A.** Sorting the real diagonal and assigning the bounded ramp gives consecutive diagonal spectral gaps at least `2 delta/(n-1)`. Permutation is internal; the returned diagonal remains in the original index order. Weyl/min–max displacement loses at most `2 eta`, yielding `delta/(n-1)` under the stated weak-coupling hypothesis. Sorting costs `O(n log n)` comparisons; computing complex magnitudes uses the permitted square root of the supplied conjugate product. Ties and zero edges cause no difficulty. The algorithm does not inspect input bits.
3. **Theorem B, weak branch.** The squared-magnitude comparison is equivalent to `r <= delta/(4n)`. Maximum row sum is at most `2r`, so Theorem A applies to the index-order ramp because the diagonal is constant. Threshold equality and `r=0` are included.
4. **Theorem B, strong branch.** The unit-modulus recurrence correctly conjugates every edge to the positive real r. The sine vectors yield n distinct eigenvalues `tau + 2r cos(k pi/(n+1))`, so they exhaust the spectrum. Consecutive gaps are the stated sine products. For n=2 as well as larger n, the first sine is minimized at the endpoint angle `3 pi/(2(n+1))`. The chord bound gives `12r/(n+1)^2`; using `r > delta/(4n)` and `(n+1)^2 <= 3n^2` gives the claimed `delta/n^3`. The zero perturbation is admissible. The proof uses trigonometry only for analysis, not algorithmic primitives. Both branch selection and output cost `O(n)` operations.
5. **Universal constants and order two.** Since `0 < delta < 1/2`, `delta/n^3 >= (delta/n)^3`. Thus a=3 and c0=1 are uniform on Theorem B, and also suffice on Theorem A. The unrestricted 2-by-2 gap formula is correct and yields at least `2 delta` after the prescribed ramp.

The norm normalization is a promise unused by these proofs, so no expensive norm computation is hidden in the algorithms. The Python implementation is a rational diagnostic implementation, not an exact-real execution environment or a bit-complexity claim. `diagonal_ramp` does not itself certify the weak-coupling promise; it correctly constructs the perturbation under that promise.

## Execution evidence

Inspected `algorithm.py` and `verification/check_exact.py` before execution. Reran the supplied exact diagnostics with `/opt/homebrew/bin/python3.14`; exit 0. Result: 378 ramp tests, dimensions 2–64; 1,134 branch/bound tests including zero coupling and threshold equality; 30,240 complex-rational gauge identities; two invalid-class rejections. See [reviewer execution log](KE-02-checks.log).

An initial invocation with the environment's default `python3` failed at import because its version does not support the runtime `int | Fraction` alias. This is an interpreter compatibility issue, resolved by using Python 3.14 without altering the supplied source. Reproduction requires Python 3.10 or newer. The finite diagnostics check algebraic consequences and branching; they do not prove the universal spectral theorem. The analytic review above supplies the universal argument.

## Primary-source check and substantive scope

On 2026-09-12, opened [Amsel et al., workshop report v3](https://arxiv.org/html/2602.05394v3#S3.SS1), Problem 3.2 and its following paragraph. The source retains the deterministic Minami question and explicitly proposes tridiagonal Toeplitz matrices as a starting class. Theorem B covers that entire class and arbitrary edge phases for every allowed delta and n, including coupling strengths excluded by Theorem A. This is a substantive in-target subclass under the repository's PARTIAL definition, even though its sine-spectrum ingredient is classical.

Also opened [Sobczyk, v2](https://arxiv.org/html/2410.21550v2), and performed the bounded search `"deterministic" "Minami" "Toeplitz" separation`. No additional primary result settling the unrestricted target was identified in this bounded check. This is not an exhaustive novelty search. The submission should not claim first discovery; prior attribution to the workshop question and classical spectrum should remain explicit.

## Remaining target and status decision

General tridiagonal matrices outside the weak-coupling class and the constant-diagonal/equal-edge-magnitude class (other than the separately proved order-two case) remain untreated. In particular, arbitrary varying diagonal entries and edge magnitudes at unrestricted coupling are not covered. No patching argument establishes the all-input algorithm. Retain the original ID, path, statement, ratings for the surviving question, and open-count inclusion. Record only `Partially resolved`, with the exact classes and remaining cases, linked proof and this review. Maintainer acceptance and novelty are not asserted.

## Reviewed source SHA-256

- `proof.md`: `a9b2b8bbee8f9729cc185b44bed8bfa9ca1b983e7fd0ddfbe3cc1fbccb007b92`
- `algorithm.py`: `e208a82fbcad67df30382818ce8a4ba0f9c7e926330f50d268e549609db737ff`
- `verification/check_exact.py`: `cef833ff0258045a7b6df0da31492b61096bbc0caf2319bfded1a15ad6ead45f`
