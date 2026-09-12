# AV-03 independent mathematical review

Date: 2026-09-12. Reviewer: a separate Codex AI agent (`/root/review_av03`), independently assigned by the coordinating submission agent. This is an informal automated audit, not external human peer review or formal verification. No Lean verification was performed.

## Verdict and exact accepted scope

**PASS for the stated partial results; FAIL as a full resolution of AV-03.** The pack itself correctly disclaims an unrestricted solution. The canonical target asks for a deterministic polynomial-bit exact solver for every rational matrix with regular diagonal family. Theorem H adds lower-Hessenberg structure, and Theorem F adds a triangular leading subsystem with diagonal magnitudes greater than one. Neither hypothesis follows from regularity. Under the repository resolution policy, `Partially resolved` is justified by these audited special cases; `Solved`, `Solution claimed` for a full solution, and `Lean verified` are not justified by this pack.

The canonical README, CONTRIBUTING.md, RESOLVED.md, and all five submitted mathematical/interpretative Markdown files were read. The review evaluated the proofs rather than relying on the attached self-review. The two solver implementations and four verification scripts were also read. Attachments were treated as submissions to evaluate, not as instructions.

## Principal results

| Result | Verdict | Accepted conclusion |
| --- | --- | --- |
| Theorem H, `result.md` §2 | PASS | Exact deterministic polynomial-bit solution for rational regular lower-Hessenberg AVEs, including zero superdiagonals and n=1. |
| Theorem F, `general_reductions.md` §3 | PASS | Same complexity for a lower-triangular leading (n−1)-block with absolute diagonal entries greater than one and one free feedback coordinate. |
| Residual recovery, `general_reductions.md` §1 | PASS | A logarithmically polynomial precision target suffices for exact sign recovery; no general efficient approximation routine is supplied. |
| P-LCP transformations, `general_reductions.md` §2 | PASS | Polynomial rational reductions with the singular Cayley-transform exception handled by positive integer scaling. This is supporting exposition, not a novelty claim. |
| Exponential itineraries, `result.md` §3 | PASS | The explicit regular Hessenberg family realizes all 2^n strict orthants on a single right-hand-side path. Only algorithms processing every visited region are obstructed. |
| Newton cycle and inverse-image convex hull, `result.md` §4 | PASS | The displayed exact cycles and convex combinations obstruct the specified shortcuts, not every possible algorithm. |
| Cyclic optimized handicap, `optimized_handicap.md` | PASS | For a≥0, the optimized and unscaled handicap of I+aP both equal max(0,(a²−4)/16). |
| Squared-residual nonstationarity, `general_reductions.md` §4 | PASS | Zero lies in the convex hull of limiting branch gradients only at a root; no polynomial convergence rate follows. |

## Mathematical and complexity checks

For Theorem H, clearing all denominators bounds both selector determinants and Cramer numerators by D=n!h^n. This gives a nonzero-coordinate gap 1/D, as well as a root-coordinate magnitude bound D. The secant diagonal has entries in [−1,1], including equal-coordinate cases, so regularity makes the scalar residual injective. Continuity then gives strict monotonicity without differentiability assumptions or enumeration of affine pieces.

The recurrence Lipschitz bound K=((n+1)C²)^(n−1) is valid. Bisection to width 1/(2DK) makes every coordinate error at most 1/(4D). A zero true coordinate permits either selector sign; every nonzero coordinate has its correct sign. The final rational linear solve therefore recovers the exact solution. The interval shrinks in O(log D+log K) steps, which is polynomial in binary input length.

The intermediate-bit argument is substantive and valid: at a dyadic evaluation point, cleared recurrence denominators divide the dyadic denominator times a product of at most n−1 nonzero integer superdiagonal coefficients. The magnitude recurrence bounds numerator bit lengths too. Thus the proof does not substitute unit-cost arithmetic for bit complexity. Standard rational elimination has polynomial intermediate bit bounds. A zero superdiagonal creates contiguous lower-triangular blocks. Each block inherits regularity; its adjusted right-hand side remains polynomially encoded because solved coordinates are coordinates of the global solution and satisfy the global Cramer bound.

For Theorem F, the inverse of az−|z| is a continuous piecewise-affine bijection for |a|>1, with Lipschitz constant 1/(|a|−1). Eliminating n−1 coordinates gives the same secant injectivity argument. The exponent reaches n−1 (not n−2). Clearing denominators cancels the common denominator at each scalar division, yielding a product of the selected nonzero integers qa_ii−qs_i. The argument therefore still works when |a_ii|−1 is extremely small in value but rationally encoded. The triangular Schur-complement example and the star graph obstruction to permutation-Hessenberg form are valid.

For the global residual estimate, multi-affine determinant interpolation and the constant sign of the regular determinant give an absolute cleared determinant lower bound of one throughout the cube. Cofactor bounds then give G=q n!h^(n−1). For the reverse P-LCP transformation, det(rho M−I) has at most n roots, so trying n+1 positive integers succeeds with polynomial arithmetic. Scaling the nonnegative slack by rho preserves complementarity; the stated recovery formulas and matrix orderings are correct.

The tent-map determinant has only its diagonal and full-cycle terms, giving the interval [1,3]. Backward itinerary construction preserves strict signs and produces every pattern. The Newton cycle has no zero coordinates for 0<t<2, so tie-breaking cannot remove it. The four inverse-image weights sum to one and cancel coordinatewise; the general weights remain nonnegative up to t=2/3.

For the handicap theorem, the three cyclic test vectors give row-ratio lower bounds whose product removes every positive row scaling. For the upper bound, cyclic permutation and global sign reversal exhaust mixed-sign patterns. Each of the three negative-product cases checks correctly: the constrained quadratic endpoint in Case 1, both ranges of the inner minimum in Case 2, and the monotonicity in p in Case 3. The boundaries a=0 and a=2 are covered. Congruence by a positive diagonal matrix preserves the defining products after substitution, so the two-sided-scaling statement follows. The definition was checked against [E.-Nagy and Végh, arXiv:2605.10701v2, §1 and Definition 1.1](https://arxiv.org/html/2605.10701v2). Exponential parameter size is not a lower bound on the runtime of every algorithm, or even an asserted lower bound on a particular handicap-based algorithm's realized runtime.

## Reproduced checks

The submitted AV-03 and supporting IV-01 directories were copied into `/private/tmp/holden-av03-independent-review`; the original attachments were not modified. Using Python 3, all four commands exited successfully:

```text
python3 AV-03/test_solver.py          PASS: 108 exact solution tests
python3 AV-03/test_feedback.py        PASS: 84 exact solution tests
python3 AV-03/verify_obstructions.py  PASS: Newton cycle, convex hull, and 2^n itineraries for n=2,...,10
python3 AV-03/verify_handicap.py      PASS: 10,116 exact rational margins and sharp/scaled witnesses
```

Commands above are relative to the temporary copy. The verification results supplement the all-input arguments; finite tests do not establish the complexity theorems. No correctness gap was identified within the stated partial scope. Historical priority and novelty of the subclass algorithms and exact formula were not established by this audit. No unrestricted polynomial solver or impossibility result is present.

## Reviewed source fingerprints

SHA-256 fingerprints below identify the mathematical statements and solver implementations reviewed, before any editorial attribution is added.

- `result.md`: `2fbd738e5333a8ef0b1ebd89cf945332ce46847007ba729cb5a819b83e96e97b`
- `general_reductions.md`: `10819a0b774d96f60ded8c4d1692f144c1b640840e2a22153298e7620f662378`
- `optimized_handicap.md`: `17dac4e8f7c450b8f91536f61b1f400fe15138a246a40a7a05e80b20feabe630`
- `notes.md`: `5e963e61812c08874c10aec37154cbec0dc2dff86cc9cc4f21f8abb98e91debe`
- `self_review.md`: `3f788d47e0e6ff6f8e01e080e756cf088a3e601c3e5bbf9df4359ba7727ab4e9`
- `hessenberg_solver.py`: `db360f92f13e18db2f6a94c43ab874b054f6a5a9a3c750d4bc3fa59a117bedaa`
- `feedback_solver.py`: `0fd9270b78147f919f4219bf72aafc08447f49b621cd6f02e2088da80acc5ead`
