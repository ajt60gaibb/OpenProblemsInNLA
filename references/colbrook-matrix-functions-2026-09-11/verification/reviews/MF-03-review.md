# MF-03 independent proof review

Reviewer: independent agent `/root/review_transfer_counterexamples`, 2026-09-11.

**Verdict: PASS — complete proof of the canonical scalar disk assertion for every order.** The candidate also proves existence and uniqueness of the normalized Padé pair, nonvanishing of its unreduced denominator on the closed disk, and the claimed strictness for orders at least two. No substantive gap was found.

## Reviewed source and identity

Read the full original `.cache/colbrook-research-submission/nla_research/submission/MF-03/manuscript.tex`, its local preamble, all three proof arguments and the matrix corollary, the complete canonical `matrix-functions-and-stability/MF-03/README.md`, and the supplied `code/wave_kernel_certificate.py` and finite certificate JSON. The manuscript has no external preamble dependency. No manuscript or canonical file was changed.

Full original SHA-256, computed by UTF-8 decoding, CRLF-to-LF replacement, and UTF-8 encoding, **without trimming** any whitespace or final newline:

`a5d319122b7f86b1ff7990eedea9606ab521d3458470a1ca9ec383c0a8aa6dc5`

Normalized length: **11105 bytes**.

## Exact target and primary-source check

Theorem 1 (`thm:main`, line 32) uses exactly the canonical entire function, expansion point, degree restrictions, normalization, closed disk, and constant. The canonical target asks that the reduced rational function have no pole; proving that the normalized denominator itself has no zero is stronger and sufficient. The additional order zero is harmless.

I checked [Nadukandi–Higham, author manuscript dated August 1, 2018](https://eprints.maths.manchester.ac.uk/2651/3/manuscript_nadukandi_higham_wkm_2018_08_01.pdf), Lemma 4.5 and Conjecture 4.6 on printed pages 11–12. The finite range there is orders 1–20, and the conjecture is the all-order scalar disk bound. The source's displayed strict matrix bound (4.9) does have the order-one boundary issue disclosed by the new note. The supplied proof addresses the same scalar target rather than a smaller disk, asymptotic order range alone, or real arguments only.

For the symmetric-function identity, I independently checked the elementary-symmetric determinant formula in [University of Washington Schur-function notes, Theorem 2, equation (1.3)](https://sites.math.washington.edu/~billey/classes/symmetric.functions/bulletins/lecture.notes.pdf). The manuscript's use of the dual Jacobi–Trudi convention is correct.

## Analytic audit

### Infinite product and symmetric functions — §2

PASS. A positive summable sequence gives locally uniformly convergent finite products, so the product defines an entire function with elementary-symmetric coefficients. For each fixed tableau shape, its sum of nonnegative weights is bounded above by the sum over all unrestricted assignments to its cells, namely `(sum t_nu)^L`. Consequently the relevant tableau series converge. Finite-variable identities pass to the infinite setting: elementary-symmetric coefficients converge, their finite determinants converge, and the nonnegative tableau sums converge monotonically. No unjustified interchange of infinite signed series is needed.

### Denominator formula and tail estimate — Lemma 2, `lem:schur`, line 50

PASS. The equations for coefficients of degrees `m+1,...,2m` are exactly the stated Toeplitz system for the `m` unknown nonconstant denominator coefficients. Transposition gives `det(e_(m-i+j))`, the Schur function for the square partition `(m^m)`. Its tableau with constant row entries `1,...,m` has strictly positive weight, so the determinant is nonzero. This proves a unique denominator; truncation through degree `m` then fixes the numerator uniquely.

I checked the Cramer-rule indices and sign independently. Replacing column `j` by the negative right-hand side, moving that column to position one, and then transposing yields sign `(-1)^j`. The resulting conjugate partition has `j` parts equal to `m+1` followed by `m-j` parts equal to `m`, whose conjugate is exactly `(m^m,j)`. In particular, for order one this gives `b_11=e_2/e_1`; for order two the two numerator determinants are `e_2 e_3-e_1 e_4` and `e_3^2-e_2 e_4`, agreeing with direct elimination. There is no omitted common normalization factor.

Deleting the added bottom row maps each tableau to a unique rectangular tableau. Every entry in that added row is at least `m+1` by column strictness; its row entries weakly increase. For a fixed rectangular tableau, dropping the remaining compatibility restrictions bounds the sum of extension weights by `h_j(t_(m+1),...)`. Summing over rectangle weights and dividing by the positive denominator proves the first inequality. Expansion of the ordinary power of the tail sum counts each weakly increasing tuple with multiplicity at least one, giving `h_j<=S_m^j`. This remains true for an arbitrary ordering of the positive sequence; no unstated monotonicity of the variables is needed. Strict positivity follows from a tableau using row values through `m+1`.

### General disk estimate — Lemma 3, `lem:disk`, line 87

PASS. With `u=R S_m<1/2`, the absolute coefficient sum satisfies `B<=1/(1-u)<2`. The reverse triangle inequality yields `|Q(z)|>=2-B>0` everywhere on the **closed** disk. The polynomial `P-Q` is the degree-`m` truncation of `Q(F-1)`; its absolute weighted coefficient sum is bounded by the product of the absolute sum for `Q` and the positive coefficient sum `F(R)-1`. Truncation only removes terms from this upper bound. Hence division is legitimate and the increasing function `B/(2-B)` gives exactly `(F(R)-1)/(1-2RS_m)`. The proof does not assume positive coefficients for the numerator or for `P-Q`.

### Wave-kernel specialization — §3, lines 110–141

PASS. The product uses the zeros `-pi^2(nu-1/2)^2` of the entire function `cosh(sqrt(z))`; there is no square-root branch issue. Its product normalization at zero is one. This puts it in the positive summable-sequence setting and therefore proves all-order existence before the disk bounds are used.

For the tail bound, the term at `nu-1/2` is the midpoint value of `x^-2` on `[nu-1,nu]`. Convexity implies midpoint value at most the interval integral. Summing for `nu>=m+1` gives `S_m<=1/(pi^2 m)<1/(9m)`. The strict final inequality uses `pi>3`; it does not rely on a decimal estimate.

At argument 3, the first three terms are `1,3/2,3/8`, and the term of index three is `3/80`. Every subsequent term ratio is at most `3/56`. The geometric upper bound is exactly `6179/2120<35/12`; I recomputed this with rational arithmetic.

For `m>=16`, `6S_m<2/(3m)<=1/24`. Thus the disk lemma applies and gives a strict bound below `(23/12)/(23/24)=2`. This covers every large order without numerical extrapolation. The strict margins hold also at `m=16`; no order is omitted between the analytic range and the finite checks.

Order one is explicitly `(1+5z/12)/(1-z/12)`, whose pole is 12 and whose value at 3 is 3. Thus equality is attained, and the universal constant cannot be decreased when that order is included. Order zero gives the constant one.

## Finite exact certificate audit — §4, `sec:finite`, line 158

PASS. I independently rebuilt the Padé systems and solved them by rational Gauss–Jordan elimination using Python's standard-library `fractions.Fraction`; this scratch implementation did not import the supplied verifier. For each `m=1,...,15`, the generated numerator and denominator coefficients matched the supplied JSON exactly. All bounds `B_m<2`, `N_m<=2(2-B_m)` passed; for every `m=2,...,15`, the stronger strict check `20N_m<39(2-B_m)` also passed. This proves strictness below `39/20` in the finite range, rather than inferring it from rounded table entries.

The independent ratios included `2` for `m=1`, `2820/1447` (approximately `1.9488597097442986`) for `m=2`, and approximately `1.9151982070777356` for `m=15`. The other displayed rounded values agree. These decimals are explanatory; all decisions used exact fractions.

I also read and ran the supplied verifier with `--verify`; it passed all 15 certificate records and the rational cosh bound. It checks the full Padé identity through degree `2m`, complete order coverage, and stored rational bounds. This provides an additional execution check, not the basis for trusting its labels. The finite checks themselves plus the analytic argument make the proof independent of relying on the older paper's finite-order computation.

## Matrix corollary and boundary qualification — Corollary 4, line 143

PASS. Nonvanishing of the scalar polynomial on every eigenvalue implies invertibility of `q_m(A)` for any finite complex square matrix, including defective matrices. Rational spectral mapping gives the stated spectral-radius bound and strictness for orders at least two. Jordan blocks do not change the spectrum of the rational matrix function. The example `m=1`, `A=3I` confirms that the source's unqualified strict boundary inequality cannot hold. The manuscript correctly avoids claiming a corresponding operator-norm bound for arbitrary nonnormal matrices.

## Status recommendation and remaining scope

- **Canonical MF-03 is completely resolved by this candidate if accepted:** every integer order in the target and every point of the specified complex closed disk are covered, with no unhandled exceptional denominator or boundary case.
- Recommend **Resolved, with provenance as an independently reviewed submitted proof**, rather than retaining “Partially resolved” on the strength of only the historical finite range. Repository acceptance, journal publication, and formal verification remain distinct from this review.
- The manuscript does not prove operator-norm bounds for nonnormal matrix arguments, a larger universal disk, or an all-order backward-stability theorem for a floating-point algorithm. None is required by the canonical assertion.
- No novelty or priority claim against all later literature is certified by this bounded proof/source audit.
