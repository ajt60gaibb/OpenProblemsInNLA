# Independent computational review: TR-17 and TR-27

Verdict: **PASS for every supplied finite exact computation and its stated computational scope.** All three supplied Python programs were read completely before execution. The extracted inventory has eleven files and three Python programs, not four. This report does not replace the separate full mathematical reviews of the universal theorems.

Reviewed on 2026-09-11. Originals: .cache/tensor20/submission. Isolated execution copies: .cache/tensor20/rerun/TR-17 and TR-27. Selected fresh evidence: .cache/tensor20/rerun/fresh-results. Additional reviewer checks: .cache/tensor20/rerun/reviewer_checks.py. The source-hashes.json beside this review records every original file, including supplied evidence and PDFs. All eleven originals remained byte-for-byte unchanged after execution.

## Source identity and execution

The following hashes are SHA-256 of the complete UTF-8 source after CRLF-to-LF conversion, without trimming or any other normalization. For these originals, normalized hashes equal raw-byte hashes.

| File relative to submission | Full source SHA-256 |
| --- | --- |
| TR-17/verify.py | c6612cb85388ce1db057264c71e3da622e95b977648d5742f94c008f8ce9c67e |
| TR-17/verify_critical_examples.py | 054848f65279963bfe69a2b1fd2852c1d61ca1a7d1945ca35bfcf7c4832495ae |
| TR-27/verify.py | e3a1873507d63ef51d47bb9d3a4496e6568d4aba9e270e1a8c6a39ddee21ecb5 |
| TR-17/solution.tex | dd5e71eb942e6b928264426e6598c4cd47b14a04b08d3c3b82f4d38b5a065c3b |
| TR-27/solution.tex | db7d556699d5021a9da6674ef491561c8af631d8537d99e21f427a82c7d1dca4 |

The programs perform local exact symbolic/integer calculations and write their named JSON files alongside themselves. They contain no network activity or unrelated filesystem operations. Execution used Python 3.12.14 with -X utf8 -B and no optimization flag, so Python assertions were enabled; the two symbolic programs used SymPy 1.14.0. All three exited zero. Elapsed times were 3.485 s (TR-17 coefficient verifier), 8.032 s (TR-17 critical examples), and 0.985 s (TR-27). Commands, output hashes, exit codes, and preservation checks are in fresh-results/manifest.json.

## TR-17: coefficient identities

The dictionary arithmetic represents the integral truncated ring with each variable truncated independently at its specified dimension. The multinomial reciprocal expansion, alternating binomial formula, and positive product formula are computed by distinct routines. The formulas match the manuscript's B-coefficients and its CSM/section-integer basis. In particular, truncating variablewise before extracting the top coefficient cannot change the desired coefficient.

Fresh results:

- 1,674 exact comparisons of the alternating B formula with the nonnegative product formula, with nonnegativity checked.
- 1,776 format/multidegree cases checking the Frobenius CSM class, section inversion, ED expansion, and an additional signed-coefficient round trip. These are parameter cases, not a claim of 1,776 pairwise different underlying varieties.
- 178 smooth-divisor cases with all section integers positive and odd and the computed ED count at least the Frobenius count.
- Named Frobenius counts: binary cubics 3, ternary cubics 7, 2 by 2 matrices 2, 2 by 2 by 2 tensors 6, 3 by 3 by 3 tensors 37, and multidegree (1,2) on P1 by P2 equal to 9. The first five additionally have hard-coded known-value assertions; the sixth is a computed example.

These checks validate arithmetic identities over the enumerated ranges. They cannot establish the geometric CSM formula, positivity for every singular metric, or the all-format minimality theorem by enumeration.

## TR-17: exact critical schemes and boundary checks

The Groebner calculations use QQ throughout. The standard-monomial breadth-first count correctly computes the length of a zero-dimensional quotient, including multiplicities; it first rejects positive-dimensional ideals. Saturation is implemented by adjoining s times the excluded product minus one. The weighted logarithmic numerator retains factor multiplicities even when the reduced support is used for saturation.

| Example | Auxiliary length | Distance length | Projective charts | Checks excluding missed distance points | Transversality checks |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2 by 2 Frobenius | 1 | 2 | 4 | 3 | 20 |
| Smooth biquadric metric | 5 | 6 | 4 | 3 | 20 |
| Reducible nodal biquadric metric | 3 | 4 | 4 | 3 | 20 |
| Ternary cubic, repeated factor and tangent conics | 3 | 13 | 3 | 2 | 9 |

Every leading principal Gram minor is exactly positive. The first chart provides the counted quotient; every other projective chart excludes points outside the first chart by a unit-ideal calculation with the original infinity equation. The distance equations are 2P d(ell) - ell P dlog(q), consistent with eliminating the radial variable from distance criticality. The saturation excludes P=0 and ell=0. The latter does not silently discard a nonsingular allowed critical point in these examples: at ell=0 with P nonzero, these equations force d(ell)=0, and the separate hyperplane-smoothness checks exclude that possibility. The support/ell/Jacobian tests certify transverse intersection at smooth support points and avoidance of its singular locus. Auxiliary coordinate-boundary tests are also exact and cover all displayed charts.

The nodal example is deliberately non-Morse: its auxiliary Hessian has rank one, but the saturated critical scheme has length three. The additional reductions u1^3=0 and v1-u1=0 certify support at the origin. The program does not confuse this with three distinct critical points.

Ten reviewer-owned checks also passed. They test the quotient counter on ideals of lengths six, three, zero and a positive-dimensional rejection; verify directly that the ternary-cubic Gram pullback equals A B^2; check coprimality and squarefreeness of the relevant supports; and compare the supplied and fresh TR-27 coordinates. This closes a correspondence check left implicit by the stress routine, whose generic helper itself only checks Gram positivity. Results are in reviewer-checks.json.

The four computed metric examples substantiate the singular and nonreduced cases highlighted in the manuscript. The finite scheme lengths and boundary certificates are exact; their interpretation within a universal generic-ED theorem still uses the geometric arguments audited separately. No claim that all critical points are simple is needed or supported.

## TR-27: projected-curve example

The program exactly constructs the r=3, m=2, D=12 example. It verifies the quotient matrix has rank twelve and precisely the proposed center line as kernel; the displayed curve and tangent vector; the three-term target decomposition and its nine-term tensor-square expansion; and independence of those three points. It checks absence of finite base points through the first two coordinates and the nonzero leading coordinate at infinity.

The exact confluent Vandermonde factorization H=B M B^T passes, with det(B)=72, det(H)=5184, and rank(H)=5. The four annihilator examples cover presence/absence of zero and infinity for the selected parameter sets. They are illustrative exact cases of the universal annihilator argument, not an exhaustive check of arbitrary complex parameter sets.

Roots-of-unity extraction is checked through its exponent congruences. The corresponding eventual-saving exponent isolation is checked for powers 1 through 50. At power thirteen the evaluated bound is 1,179,648, strictly below 3^13=1,594,323. The independence-threshold arithmetic needed for the square example passes.

The explicit decompositions certify upper bounds of three and nine. Exact rank-three and square-rank-nine lower bounds, smoothness of the image, the border-rank statement, and the all-r/all-m family depend on the manuscript proofs; the JSON's rank claims are appropriately identified as proof claims rather than computationally exhaustive lower-bound certificates. No mismatch was found between the finite constructed data and the manuscript example.

## Evidence comparison and disposition

All supplied transcript mathematical lines reproduce exactly after newline normalization. The only transcript text changes are the actual Python version (3.13.5 in the supplied evidence versus 3.12.14 here). The TR-17 critical transcript has no changed lines. The TR-27 coordinates are equal as JSON and as normalized text; the raw byte mismatch is solely Windows CRLF output versus the supplied LF file. The manifest records both the raw mismatch and normalized equality. TR-17 generated JSONs were not present in the original inventory and are fresh artifacts.

There is no computational correction required. Preserve the originals separately from the rerun logs and generated JSON. Copy the entire final fresh-results directory, the reviewer script, this review, and source-hashes.json for reproducibility. This computational PASS supports, but does not independently substitute for, the separate proof verdicts on the two full canonical targets.
