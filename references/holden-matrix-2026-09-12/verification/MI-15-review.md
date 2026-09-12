# Independent informal AI-agent review: MI-15

Review date: 2026-09-12. Reviewer: a separately delegated Codex AI agent, independent of the submission author and integration agent. This is an informal mathematical and computational check, not external human peer review, formal proof-assistant verification, or upstream acceptance.

## Verdict and scope

**PASS for the finite-order partial result n = 8, 9, 10, 11, 12. NOT a full resolution of MI-15.** The canonical target quantifies over every integer n >= 2. The submitted argument contains no all-order construction or induction. Keep the canonical problem partially resolved; this check does not justify marking it solved. Historical novelty has not been established by this review.

The proved claim is that the canonical real Toeplitz Böttcher–Wenzel quartic is an SOS of at most 2(n-1)^2 homogeneous real quadratic polynomials for each of these five orders, with no symmetry or bandwidth restriction and with the central variables included.

## Mathematical audit

I read proof.md and the complete exact checker before executing any attachment code. I checked the canonical README directly. The weighted wedge identity has the required factor 2, and direct commutator expansion uses X_ij=x_(i-j). Central wedges contribute precisely 2n(n-|a|) times their squares. The three signed Plücker cross terms vanish on decomposable wedge coordinates, so the rational corrections preserve the polynomial. The checker additionally compares every quartic coefficient to an independently assembled canonical polynomial.

The disjoint nonempty support groups give n-1 independent kernel vectors. Their within-group differences and all uncovered coordinate vectors span the orthogonal complement. The dimension is 2(n-1)(n-2). Exact kernel identities eliminate all cross terms involving that nullspace. Positive row diagonal-dominance margins make the symmetric congruence matrix positive definite. This in turn proves the square congruence factor invertible, so positivity on the complement follows without an assumed floating-point rank. The PSD Gram matrix therefore has the claimed rank. The spectral theorem provides real quadratic squares, which is exactly the coefficient field allowed by the canonical problem. Adding 2n-2 central squares yields the asserted upper bound. I found no mathematical gap in this finite-order argument.

## Actual checks performed

- Ran verify_exact.py normally with Python assertions enabled on every supplied certificate, writing a fresh independent result record. Every coefficient identity, exact kernel equation, congruence dimension, symmetry check, and positive integer row margin passed.
- Ran the supplied adversarial checker after reading it: a one-unit forced Plücker change and a zero congruence column were both rejected.
- Wrote and ran an additional reviewer-owned test: for each order, 25 deterministic random integer x,y assignments compared direct Toeplitz matrix multiplication with both the canonical quartic expansion and the rational Gram expression (125 comparisons total). All passed. These are supplemental checks, not a substitute for the exact coefficient proof.
- Deliberately changed the first Gram diagonal entry by one integer unit in every order; all five corruptions were rejected by the polynomial-identity check.
- Did not run Lean, numerical SDP discovery, or floating-point eigensolvers.

## Exact results

| n | Quartic monomials | Gram dimension | Rank | Minimum integer row margin |
|---|---:|---:|---:|---:|
| 8 | 676 | 91 | 84 | 999999952863237952570849 |
| 9 | 965 | 120 | 112 | 999999925669481281169422 |
| 10 | 1326 | 153 | 144 | 999999906716728966649869 |
| 11 | 1767 | 190 | 180 | 999999874503493510818039 |
| 12 | 2296 | 231 | 220 | 999999824037570658807213 |

## Reviewed source SHA-256 hashes

These hashes identify the original checkpoint files before authorship or submission-format edits.

- `proof.md`: `449caa14da389102d231833832f499a2f7ab4af7619673f552ad6d021c3f4e1c`
- `verify_exact.py`: `a35ce50862e4afe03b2b04ae885a171a953d786540fb5227bfeb811f270f495e`
- `adversarial_test.py`: `3d33b1ffa9d0181aa7c6e15a3314bfde9f54efb7f2e85f528f6bd4aadcd6d324`
- `certificates/n8.json`: `8acc7b59e93b2a79ae20eeaee922222af9214baa0be80152d189068093e01e24`
- `certificates/n9.json`: `2f60eb7b7b13b559368f2a409afcb3120820a0ea5ed65a613842f518f037c921`
- `certificates/n10.json`: `e32502e9ab1941eca17adf7aa93edcddd0d3ba0890a8a77eb0b4ea706b9159e9`
- `certificates/n11.json`: `ff91153ca6afeeff606f0127c8e4aa2dcde7c0504a7692e08f96ef0818fe131f`
- `certificates/n12.json`: `91f5fe361f1acd7dacdd59dc0f84ce318ca3fcfab1f4e018b507fb5e5fbeba84`

The reviewer-owned supplemental test is /tmp/mi15_independent_spotcheck.py in the review environment. Repository submission formatting and resolution-policy eligibility remain integration checks; this report makes no claim of external-review-policy satisfaction.
