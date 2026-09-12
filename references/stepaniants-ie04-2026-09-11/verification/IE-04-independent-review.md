# IE-04 — independent mathematical review of the recovered submission

**Verdict: PASS for the complete, unchanged canonical IE-04 target.** The reviewed manuscript gives a valid negative answer to the displayed universal exponential-tail question. No correction to its mathematical argument is required.

Reviewer: `/root/review_aa01`, an independent agent in the submitting session. This agent reconstructed the argument separately from the recovered manuscript's author and from the root agent's review. This is an AI-agent mathematical review, not external human peer review, formal proof-assistant verification, or a determination of novelty or priority.

Review date: 11 September 2026 (UTC). All files in the supplied Downloads folder were read without modification.

## Exact reviewed materials

- Recovered `IE-04/solution.md`: 8,401 bytes; SHA-256 `428c586bf6a0b66ce94d478eed5be6e951032cc09fc646df7204ae2823b14a75`.
- Canonical `linear-systems-and-elimination/IE-04/README.md` on the checked published base: SHA-256 `e774f301b6b50da21fcb1904aec6f6279fd40ec293082593e35f959fd5bf5550`.
- Supplied `verify_bounds.py`: 7,389 bytes; SHA-256 `f08cebc9bc2a8fe28f53c2033da0c5d56c16b80f21b4055d3eb460f9dc68ea14`.
- Supplied `certificate.json`: 20,793 bytes; SHA-256 `535884c66752361d166ea5b40063ea126689bc269353441ead2040ba688bde09`.

This review binds the Markdown mathematical source. Publication metadata and layout may be added separately, but any mathematical alteration requires a corresponding conversion review or renewed mathematical review. The supplied PDF and TeX were not used as substitutes for reading the complete Markdown proof.

## 1. Exact scope and primary-source check

The canonical problem asks whether a single pair of positive constants works for every dimension, real deterministic center of spectral norm at most one, noise level in `(0,1]`, and real `x >= 1`. The requested upper bound is `2^(-c2*x)` at threshold `x*(n/sigma)^c1`. Its growth factor uses the maximum entry over all active exact Schur complements, normalized by the maximum absolute input entry.

I independently downloaded and visually inspected page 52 of the [Spielman–Teng author PDF](https://www.cs.yale.edu/homes/spielman/PAPERS/focmSmoothed.pdf). Section P6, Conjecture 16 displays the same tail inequality and the spectral-norm bound on the deterministic center. The surrounding discussion concerns partial pivoting. The downloaded 635,912-byte PDF has SHA-256 `c9a56d61d0452e81817cf8d86cd4c85b68006baa2b0dfd920977abc72576a024`. The paper's brief wording does not replace the repository's explicit quantifiers; those exact canonical quantifiers are the target proved false here.

The recovered proof uses the admissible center `I_n` and noise level one. The center is nonsingular and has spectral norm exactly one. Its auxiliary pure-Gaussian assertion is unnecessary for the counterexample. The matrix `W_n` is the center of a rare event in input space; it is not the deterministic center in the smoothed model. Consequently its larger spectral norm violates no hypothesis.

One admissible sequence of centers and dimensions suffices to refute a universal statement. Nothing in the argument claims a replacement sharp tail, an expectation estimate, or a sharp high-probability polynomial growth exponent.

## 2. Exact elimination of the high-growth matrix

I reconstructed the no-swap elimination directly. At a nonfinal step, the pivot is one and every remaining entry below it is minus one-half. All entries to the right of the pivot in nonfinal columns of that pivot row are zero. Thus elimination cannot change the triangular pattern in those columns. Every remaining entry in the last column has the common value

`c_k = (3/2)^(k-1)`.

The update adds one-half of this same value, giving `c_(k+1) = (3/2)*c_k`. Every pivot choice is strict, and the final pivot is positive. The input maximum is one, so the growth factor is exactly `c_n`; this is also at most the loose bound `2^n` used for all active entries.

This calculation is valid for every `n >= 2`, including `n = 2`. It does not depend on pivot tie conventions.

## 3. Full-box robustness induction

The radius and amplification constants are explicit:

`delta_n = 2^(-(n^2+n+1))`, `B_n = 2^(n+2)`.

Their key identity is exact: `(n+2)(n-1) - (n^2+n+1) = -3`, hence `B_n^(n-1)*delta_n = 1/8`. All intermediate inductive error bounds are therefore at most one-eighth.

At a stage with entrywise error at most `e <= 1/8`, the perturbed pivot is at least seven-eighths and every competitor has magnitude at most five-eighths. This proves strict no-swap selection before any Schur-complement update is used. In particular, division by the pivot is legal and uniformly controlled.

Write a perturbed column entry and pivot as `-1/2 + u` and `1 + v`, with `|u|,|v| <= e`. Then

`q + 1/2 = (u + v/2)/(1+v)`.

This independently verifies both multiplier estimates in the manuscript: `|q| <= 5/7 < 1` and `|q+1/2| <= 2e`. The denominator perturbation is included; no first-order approximation is made.

Subtracting the exact unperturbed and perturbed update formulas gives the displayed three-term error identity. The entrywise error of the next active matrix is at most

`e + |q|e + |q+1/2|*2^n <= (2+2^(n+1))*e <= B_n*e`.

This closes the induction on the actual partial-pivoting path for the whole closed entrywise box. There is no circular assumption about the path, and no appeal to an unspecified continuity neighborhood.

At the final stage the scalar Schur complement is at least `c_n - 1/8 > 0`. Together with the preceding positive pivots, this proves nonsingularity throughout the box. The input maximum is at most `1+delta_n <= 9/8`, while the final scalar is one of the active entries counted in the canonical growth definition. Therefore

`rho >= (c_n-1/8)/(1+delta_n) >= (8c_n-1)/9 >= 7c_n/9 > c_n/2`.

The lower bound is strict even on the boundary of the closed box. It also respects the normalization by the perturbed input, not merely the unperturbed input. This supplies the exact strict event needed later.

## 4. Gaussian lower bound and all constants

For each choice `C = 0` or `C = I_n`, every coordinate of `W_n-C` has absolute value at most one. Since `delta_n <= 1/8`, every one-dimensional event interval lies in `[-2,2]`. The Gaussian density there is at least `exp(-2)/sqrt(2*pi)`, which is greater than `1/32`. The manuscript's elementary justification is correct: `e < 3` and `pi < 4` give a lower bound greater than `1/27`.

Each interval has length `2*delta_n`, so its probability is at least `delta_n/16`. Independence applies to all `n^2` entries; no conditional independence or restriction to a lower-dimensional set is assumed. The resulting full-dimensional box probability is at least

`(delta_n/16)^(n^2) = 2^(-n^2*(n^2+n+5))`.

The exponent simplification uses `delta_n/16 = 2^(-(n^2+n+5))` and is exact. Finally, for `n >= 2`, `2n^2-n-5 > 0`, giving `n^2*(n^2+n+5) <= 3n^4`. Thus both probability lower bounds in the theorem are valid for every stated dimension.

## 5. Contradiction for arbitrary positive real constants

The proof fixes arbitrary `c1,c2 > 0` and takes

`x_n = (3/2)^(n-1)/(2*n^c1)`.

For any fixed real `c1`, this tends to infinity. With `K_n = n^2*(n^2+n+5)`, the logarithm of `x_n/K_n` is exactly the expression displayed in the manuscript and tends to positive infinity. Therefore sufficiently large dimensions satisfy both `x_n >= 1` and `c2*x_n > K_n`. No assumption that the constants are rational, integer, or bounded is used.

At these dimensions and at the legal instance `A = I_n + G`, the proposed threshold equals exactly `c_n/2`. The robust box is contained in the strict growth event, giving a probability at least `2^(-K_n)`, which is strictly larger than `2^(-c2*x_n)`. This is a contradiction for each proposed universal pair.

The absence of an assertion at dimension one causes no gap: failure along sufficiently large dimensions refutes the universal statement. Almost-sure nonsingularity of the Gaussian perturbation is compatible with, but not needed to establish, the explicitly nonsingular high-growth event.

## 6. Supplied checker review and separate exact checks

I read the entire supplied Python checker before executing it. It uses only the standard library. Its outward-rounded dyadic interval arithmetic bounds each exact real operation conservatively; denominator intervals containing zero are rejected. It checks pivot separation and the complete-box enclosures in orders 2 through 16, plus scalar inequalities through order 256 and selected exact contradiction dimensions. These are appropriately described in the manuscript as supplementary finite checks.

I reran that checker with its output directed to this temporary review directory. The run succeeded. The regenerated certificate is byte-identical to the supplied `certificate.json`, including the SHA-256 recorded above. This replay is not described as independent code.

For a separate method, I wrote `IE-04-independent-exact-check.py` without using the supplied interval implementation. It performs ordinary exact rational GEPP using `fractions.Fraction`: the unperturbed formula was checked for orders 2 through 24, and every corner of the entrywise boxes was checked in orders two and three (16 and 512 matrices). It also checked the scalar inequalities in orders 2 through 512. All checks passed. These corner checks alone do not certify a box interior; the universal full-box result follows from the analytic induction reviewed above.

- Independent checker: 2,978 bytes; SHA-256 `b522324097b80aa346fe91e30e9c7eda0f65f87be10ef9c8c34e080340b87edd`.
- Independent output: 622 bytes; SHA-256 `f158de7a7f3b966d0b166470624981a9e5c502d2eecd4e8daede3fd74482f95f`.

## Final disposition

The complete recovered analytic proof passes this independent adversarial review. It resolves the canonical IE-04 question negatively by an explicit all-dimension robust-growth construction and a quantified Gaussian rare event. The proof does not depend on the finite checker, unpublished numerical evidence, an unchecked external mathematical theorem, or a change to the original target.

Eligibility for submission, public-fork/discussion checks, authorship metadata, repository formatting, generated PDFs, and publication conversion are separate tasks. This report grants no claim of prior-literature novelty or external peer review.

Signed: `/root/review_aa01`, independent reviewing agent, 11 September 2026.
