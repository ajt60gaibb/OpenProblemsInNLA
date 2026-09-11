# Recovered rook-pivoting note: independent review

Review date: 2026-09-11. The complete `research/rook_partial.md`, its verifier, shared exact arithmetic implementation, and current canonical IE-15 README were read. The row/column pivot conditions and intermediate Schur complements were also checked by direct rational algebra.

## Verdict and scope

**PASS as an order-five lower-bound certificate. It does not resolve or partially determine either exact constant requested by canonical IE-15. Recommend retaining IE-15 as Open.**

The note proves `g_RP(5)>=893/131` for the convention permitting any pivot maximal in absolute value in both its active row and active column, including ties. The related canonical identifier is **IE-15**, whose target is the exact pair `g_RP(3),g_RP(4)`. The supplied order-five example has the correct field, nonsingularity, growth definition, and pivot convention, but the wrong dimension to settle either requested constant. No sharp upper bound for any of these three orders is provided. The note itself correctly labels its result partial research and disclaims optimality.

No mathematical correction to the finite certificate is needed. It should be presented as related evidence rather than as an adopted solution of IE-15. No novelty or publication-priority assertion was verified.

## Full source identity

Source: `.cache/colbrook-recovered/OpenProblemsInNLA_recovered/research/rook_partial.md`.

- Full UTF-8/LF SHA-256: `4cfa4f08dce9c80a3057ea46e072ae2f92a821fecdc1a9d83b073bbd1a8ca638`.
- Normalized size: **1,773 bytes**.
- Normalization decodes the complete original as UTF-8, replaces CRLF by LF, and re-encodes without trimming any content or trailing newline.
- The file has no external preamble. This reviewer made no source or canonical edits.

## Direct algebraic audit

Normalize as in the note; at `t=1/6` the initial maximum modulus is exactly one. The first diagonal pivot equals one and is maximal in its active row and column, including ties. After its elimination, the trailing matrix is

```
[ 1       1       -1       1 ]
[-1/3     4/3     t-1     -2 ]
[ 1       t-1/3   2        0 ]
[-1       2/3     2        2 ].
```

Its leading pivot is again one, and its first row and first column have maximum absolute value one. A rook pivot need not be the largest entry of the entire active matrix, so the other entries of magnitude two are allowed.

After the second elimination, put `a=t-4/3`. The active three-by-three matrix is exactly

```
[5/3     a      -5/3]
[a       3      -1  ]
[5/3     1       3  ].
```

For `t=1/6`, `a=-7/6`; the diagonal `5/3` is maximal in both its row and column. Eliminating it yields

```
[3-3*a^2/5    a-1 ]
[1-a          14/3].
```

Thus the fourth pivot is `3-(3t-4)^2/15`, as claimed, and the last pivot where defined is

`14/3+(a-1)^2/(3-3*a^2/5)`

`=(27t^2-42t-217)/(9t^2-24t-29)`.

This verifies the note's general diagonal-pivot formulas algebraically. It does **not** assert rook admissibility or normalization for every parameter `t`; the finite theorem uses only `t=1/6`.

At that parameter the final two-by-two matrix is

```
[131/60   -13/6]
[13/6      14/3].
```

The fourth pivot is positive and exceeds both adjacent absolute off-diagonal entries by exactly `1/60`, so it is a valid rook choice even though the bottom-right entry is larger. The final scalar is `893/131`. Every pivot is nonzero; their product is `893/36`, so the original matrix is nonsingular. No row or column swaps are needed along this permitted path.

The successive active maxima are `1`, `2`, `3`, `14/3`, and `893/131`. Hence growth over **all** active Schur complements equals the last value; it is not just a bound inferred from the pivot list. The finite lower bound follows directly.

## Canonical and primary-source alignment

Canonical `linear-systems-and-elimination/IE-15/README.md` requires real nonsingular matrices and allows all row/column rook choices and ties, matching the note. Its question is specifically the exact constants for orders three and four. Higham's Problem 9.18, printed p. 193, asks for exact small-order rook growth and separately for broader lower bounds. The historical numerical values shown there are not exact theorems. [Higham, *Accuracy and Stability of Numerical Algorithms*, second edition](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf).

An order-five result cannot be substituted for either requested small-order extremum. Nor does cropping the original matrix preserve this growth path and normalization in a way that gives the claimed value in a smaller dimension. This review adopts only the displayed order-five certificate.

## Code audit

The full `verification/rook_partial.py` was inspected. It constructs the rational matrix exactly, checks every diagonal pivot against both its active row and active column, forms the Schur complements in `fractions.Fraction`, tracks all updated active entries, verifies the complete factorization `L*U=A`, and asserts the claimed pivot list and final growth. Its command-line entry point refuses optimized Python mode because checks use assertions. The shared exact matrix multiplication and Fraction conversion were inspected as well.

This reviewer inspected the integration agent's fresh `verification/fresh-rook-results.json`, which records PASS. The direct algebra above independently verifies the certificate as well. Neither the code nor the note supplies a matching universal upper-bound argument.

## Exact remaining questions

For canonical IE-15, both `g_RP(3)` and `g_RP(4)` still require exact values with matching upper and lower proofs under all permitted rook paths. The value of `g_RP(5)` also remains undetermined by this note. A particular implementation's deterministic pivot-search or tie-breaking path is not covered unless it follows the displayed allowed diagonal choices.
