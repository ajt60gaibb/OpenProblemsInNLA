# Independent review of the AC-11 and AC-12 submission

Review date: 2026-09-11. Reviewer: independent proof-review agent, separate from the agent executing the full certificate checks.

## Verdict and acceptance boundary

**PASS for the analytic arguments and the finite certificate method. Conditional PASS for the two stated finite computational theorems, contingent on successful complete fresh checks described below. Neither canonical all-order problem is solved.** No mathematical correction to the submitted manuscript is required by this review. This report does not turn supplied logs into independently reproduced computations.

The exact proposed AC-11 conclusion is

\[
\min\{\operatorname{per}(A):A\in\{-1,1\}^{n\times n},\ \operatorname{per}(A)>0\}
=2^{n-\lfloor\log_2(n+1)\rfloor},\qquad 1\le n\le35.
\]

It concerns all sign matrices, with no nonsingularity restriction. The universal lower bound is proved for every positive integer order; attainment above order 35 is not proved. Recommend retaining **Partially resolved**, extending the certified finite interval only after the complete checks pass. The remaining target is attainment for every (n\ge36).

The exact proposed AC-12 conclusion is equality of the signed permanent ranges of all sign matrices and sign matrices whose entries strictly below the diagonal are (+1), for (1\le n\le10). Negative entries on the diagonal are allowed. These are not upper triangular matrices with zero entries below the diagonal. Recommend **Partially resolved** after completion of the mandatory checks, with all orders (n\ge11) remaining. Do not mark Solved.

The coordinating agent reports that 5,528 fresh exact witness-DP checks have passed. Full C++ permanent checks and exhaustive range checks were still being prepared when this report was written. Their completion and outputs must be established by the linked fresh verification records in this directory; this review does not assert their completion.

## Source identity and coverage

Source root: `.cache/colbrook-arithmetic/NLA_GitHub_submission_bundle/NLA_partial_results_submission_package/`.

Read the complete `manuscript.tex`, its complete preamble and all five included TeX inputs. The preamble is embedded in the manuscript; there is no separate common-preamble input. Also read the two auxiliary table fragments, `claims.json`, reproduction script, certificate and range-check implementations, subset-DP implementation, data tests, and realization utility. The source was not modified.

Hashes below cover the entire file decoded as UTF-8, replacing CRLF with LF and re-encoding as UTF-8. No trimming, BOM removal, or other normalization is performed. `review-source-input-hashes.json` in the parent verification directory gives both raw-byte and normalized hashes for 171 textual source, certificate, catalogue, log, and metadata files. `hash_review_inputs.py` reproduces that manifest without editing the submitted package.

| Source/input | Complete UTF-8/LF SHA-256 |
| --- | --- |
| `manuscript.tex` | `f3f3d62a16b3c47b15ba450369db49729363016c6f8946494a23d06a1f57be3f` |
| `results_generated.tex` | `c2122a8cf8863cd8c86fd35e1dea9d5c160324d825b49f7173fbf148663e4d34` |
| `minimum_tabular.tex` | `499e4e1717886ffd3c3f6616c01514dcf5cc159d3be8073b927db752830b6130` |
| `range_tabular.tex` | `b24a4eb24cdcdf2e1b4b2f434ef5a0dcdd41304c17b022bd321b23ce34ddaded` |
| `example21.tex` | `05cf7a7e3ad08376d06c57871e66fbb4e3268495e46d783e62b0f52d7e6d2bc5` |
| `example_cofactors.tex` | `5951f90c1468e2daf2c71019c6a950c513044eaf65229e2f83faf1125de364d1` |
| `minimum_table.tex` (auxiliary, not directly included) | `14b06bde2a0dc5dad391d41233734bb8fc71a8f0d7af96a8e6807917c76517e5` |
| `range_table.tex` (auxiliary, not directly included) | `b113512218843af5943febcc044a879e026aaed30e53d192aaf857630cbbe825` |

The manuscript includes the inputs at lines 23, 98, 262, 287 and 290. The first supplies the maxima 35 and 10 and the count 15 of orders above the prior order-20 range. These macros are reporting metadata, not proof. Tables and archive claims likewise require certificate verification.

## Canonical and primary-source comparison

Read `arithmetic-and-complexity/AC-11/README.md` and `AC-12/README.md` in full. Their targets agree with the definitions above. The arithmetic section, Problems 3 and 4, of the [Open Problems in Numerical Linear Algebra primary source](https://arxiv.org/html/2507.09433v1) states the minimum-permanent and range questions, including the restriction of negative entries to on or above the diagonal. Its piecewise exponent for the minimum is equivalent to the manuscript's unified formula, including the exceptional orders (2^t-1).

The cited prior attainment through order 20 is supported by Section 3 of [Wanless's primary paper on Wang's conjecture](https://users.monash.edu.au/~iwanless/papers/wangconjLAMA.pdf), printed pages 430–431. This review verifies that attribution, not a priority claim for the new witnesses or the finite range computations. No external character-sum, asymptotic, or unproved probabilistic theorem is needed for the certificate arguments.

## AC-11: proof audit

**Theorem 1, `thm:minimum`, manuscript lines 52–54: conditional finite PASS.** The theorem follows from the all-order divisor lemma and one independently checked attaining matrix for each stated order. It does not require exhaustive search over matrices.

**Universal divisibility, `lem:divisor`, lines 69–90: PASS for every (n\ge1).** Writing (A=J-2D), with (D) a zero-one matrix, expansion by selected negative terms gives

\[
\operatorname{per}(A)=\sum_{k=0}^n(-2)^k(n-k)!r_k(D).
\]

Here (r_k(D)) counts placements of (k) nonattacking selected entries; the remaining (n-k) rows and columns can be bijected in exactly ((n-k)!) ways. The valuation of the coefficient is (k+v_2((n-k)!)=n-s_2(n-k)). For any integer (0\le m\le n), (s_2(m)\le\lfloor\log_2(n+1)\rfloor), since the least nonnegative integer with (t) one-bits is (2^t-1). Thus every coefficient is divisible by the claimed positive power of two. This handles (k=n), (m=0), (n=1), zero permanents and negative permanents. The least strictly positive permanent therefore has the stated lower bound.

**Last-row construction, Section 3, equations `eq:lastrow` and `eq:signedsum`: PASS as a certificate-search method, not an all-order existence proof.** Expansion along the last row gives (operatorname{per}(A)=q(n-1)\sum_j y_jc_j), provided the supplied cofactors are correct. The ratio (q(n)/q(n-1)) equals 2 except at (n=2^t-1), where it equals 1. In particular (q(30)=q(31)=2^{26}); the exceptional order 31 is not missed. Meet-in-the-middle solves the resulting finite signed subset problem with the stated exponential storage/time scale. A failed seed need not produce a solution. There is no claimed guaranteed extension to arbitrary order, and the search heuristics are not used to justify certificate acceptance.

**Exact arithmetic, Section 4: PASS.** The subset recurrence in `eq:dp` is the ordinary permanent recurrence for the first (|I|) rows and selected columns (I). Its scaled version divides by 2 exactly when (g(k)-g(k-1)=1); divisibility is checked. The unscaled Python recurrence uses arbitrary-precision integers.

For `lem:polarization`, expanding the full sign sum eliminates every monomial unless each row multiplicity is odd; because there are exactly (h) factors and (h) rows, every multiplicity must be one. Pairing opposite sign vectors leaves the fixed-first-sign formula with coefficient (2^{1-h}). This proves the identity also for (h=1). For even (h), halving every column sum gives the displayed identity for (operatorname{per}(M)/2), with no fractional intermediates. The odd-order case first expands along one row and applies the even-order identity to the minors. The prefix/suffix or product-derivative formulas compute omitted-column products without dividing by a possibly zero column sum.

The cofactor implementation uses arithmetic modulo (2^{128}). It recovers each signed cofactor from its half because ((n-1)!/2<2^{127}) for every (n\le35); the worst case is (34!/2). Intermediate wraparound is permitted in unsigned arithmetic and does not invalidate this final centered reconstruction. Signed storage and search guards are present. Nevertheless, merely checking the dot product of the supplied cofactor list is insufficient: incorrect cofactors can satisfy that dot product.

**Full-matrix certificate, Section 4.3, `eq:crtbound`: PASS as an exact deterministic verifier.** `src/verify_permanent.cpp` transposes the input and evaluates the full permanent independently of the cofactor files. For (n\ge2), the half permanent is an integer. Two residue calculations use (2^{128}) and (2^{61}-1). Their coprimality follows from oddness of the second modulus; its primality is not needed. If both residues equal those of the claimed half permanent and

\[
2^{128}(2^{61}-1)>n!/2+|\text{claim}|/2,
\]

the difference, a multiple of their product, has absolute value strictly below that product and must be zero. The bound is checked using `cpp_int`. This is not a probabilistic modular check. Order 1 is handled directly and odd claims for orders at least 2 are rejected.

The implementation's Gray-code chunks cover all fixed-first-sign vectors; the parity of a Gray word is the parity of its index, justifying the alternating sign even when a thread begins at a nonzero index. The odd-order product-derivative update uses the previous product. Discarding terms with more than one zero factor is safe in this derivative case; for the ordinary product any zero suffices. The small-factor modular multiplications fit the wider intermediate type, and the Mersenne reduction's single final subtraction suffices for the supported factor sizes. None of these implementation arguments makes the exponential runs optional.

**Appendix order 21:** the displayed 21 sign rows agree with `min21.txt`, and the displayed scaled cofactor vector agrees with `min21_cofactors.txt`. Its scale is 65,536 and the last-row dot product is 2, giving claimed permanent 131,072. Its full-matrix check remains part of the mandatory run; the appendix alone is not an independent calculation of the cofactors.

## AC-12: proof and search-coverage audit

**Theorem 2, `thm:range`, lines 56–59: conditional finite PASS.** Section 5.1 correctly separates two obligations. A catalogue (S) must have a verified restricted witness for every listed nonnegative absolute permanent, and every unrestricted matrix must have absolute permanent in (S). Together with (U_n\subseteq\Omega_n), these inclusions prove equality of absolute ranges. Negating the first row preserves (U_n) and negates the permanent, so equality extends to signed ranges. A zero value needs no special sign witness.

**Representative coverage, `lem:coverage`, lines 216–227: PASS.** Column sign changes normalize the first row, and subsequent row sign changes normalize the first column without disturbing it. These operations preserve absolute permanent. Permutations of the other rows and columns preserve normalization. A lexicographically least representative exists in each finite orbit and satisfies the stated ordering restrictions. Within a block of columns identical in the already selected rows, the next row can be sorted; the implementation's low-bit-prefix mask test is consistent with numeric binary-mask comparison, which reads the most significant bit first. One must not read printed low-to-high bit positions as the comparison order.

The additional `allowed_after` tests are necessary conditions for that least representative: if a later row, sorted within an earlier prefix's equal-column blocks, could precede the earlier selected row, moving it there and permuting only those blocks would preserve the preceding prefix and make the matrix smaller. Thus intersecting these tests cannot discard every representative of any orbit. Uniqueness of generated representatives is unnecessary. The recursion permits repeated rows and all sign configurations meeting the necessary conditions; no nonsingularity or distinctness restriction is introduced.

**Completion bound, `lem:completion`, lines 230–248: PASS.** Laplace expansion along the fixed (k) rows gives one term for each (k)-subset of columns. Every complementary permanent has absolute value at most ((n-k)!), so the asserted sum of absolute prefix minors is a valid upper bound for every completion. Because the divisor lemma forces every completed permanent to be a multiple of (q(n)), a branch can be discarded once its bound lies within a fully populated initial catalogue progression. The implementation starts that progression below zero and does not use this shortcut when zero is absent. It verifies all multiples, rather than relying on the largest catalogue element. Leaves not pruned are checked individually.

The DP entries and bounds fit the stated integer types for (n\le10): a (k\times k) sign permanent has absolute value at most (k!), and the full bound is at most (inom nk k!(n-k)!=n!). Fixed-size mask storage has 512 bits, sufficient for (2^{n-1}\le512). These bounds would need reconsideration for a larger search limit.

**Restricted enumeration, Section 5.4: PASS in its stated supporting role.** The last row initially has only its diagonal sign free. Its sign can be made positive by a last-column sign change; the top-left sign is then normalized by a first-row sign change. Both operations preserve the restriction and absolute permanent. For (n\ge2) there are consequently (2^{n(n+1)/2-2}) normalized restricted possibilities. Order 1 is handled separately. In particular, order 8 has (2^{34}) such possibilities. Exhaustive restricted enumeration at larger orders is not necessary when complete restricted witness catalogues and unrestricted inclusion checks are available.

The absolute catalogue sizes for orders 1–10 are reported as (1,2,2,5,8,16,36,158,506,1933). Corresponding signed sizes are (2,3,4,9,15,31,72,315,1011,3865); zero is absent precisely for orders 1, 3 and 7 in these catalogues. The orders 9 and 10 initial progressions end at 14,848 and 115,200, respectively. Supplied node counts and logs are historical outputs, not replacements for the fresh exhaustive inclusion runs.

`tools/realize.py` computes the input permanent rather than trusting its file claim, looks up an absolute-value witness in the corresponding finite restricted catalogue, negates its first row if necessary, and rechecks both the permanent and the restriction. This is a valid finite realization algorithm conditional on the certified catalogues. It raises an error outside the explicitly listed finite orders and provides no all-order constructive solution.

## Mandatory computations and their exact role

1. Validate every minimum witness's dimensions and sign entries and run the full-matrix exact verifier on all `min1.txt` through `min35.txt`. The claimed value must equal (q(n)>0). Cofactor dot-product checks alone do not discharge this obligation. `tests/check_data.py` directly recomputes the minimum permanents by Python DP only through order 12, so that script alone is insufficient for Theorem 1.
2. Validate every restricted catalogue value and every associated witness for orders 1–10 by exact subset DP, including the below-diagonal (+1) condition. Require equality of the witness keys and the spectrum file values. Cross-agreement between the unrestricted and restricted supplied catalogue files does not prove completeness.
3. Finish `check_range` for all orders 1–10 against those same verified restricted spectrum files, without timeout, sampling or early termination. Its complete search establishes unrestricted inclusion. The supplied order-10 log reports about 708 million nodes, so a short successful-looking prefix of output is insufficient.
4. Retain executable build/compiler information, exit codes and full outputs, and bind all inputs to the hashes in the source-input manifest. If platform portability requires a verifier change, record its diff and independently recheck the changed arithmetic assumptions.

`reproduce.sh` requests the mathematical obligations above. Regenerating the discovery search, redoing every historical enumeration, or trusting stored cofactor files is not required when these acceptance checks pass. Conversely, source audit and regression tests do not replace the complete arithmetic and range computations. Small deliberate-invalid-claim and missing-spectrum-value tests in `check_data.py` are useful controls but are not completeness evidence by themselves.

## Exact remaining questions

- AC-11: Does the universal divisor occur as a strictly positive permanent for every order (n\ge36)? The submitted search does not prove successful extension from one order to the next.
- AC-12: For every (n\ge11), can every permanent attained by an unrestricted sign matrix also be attained with every entry strictly below the diagonal equal to (+1)? Finite catalogue equality does not yield an induction, uniform transformation or all-order theorem.
- Verification acceptance: Until complete fresh permanent and range logs are available, the upper endpoints 35 and 10 remain computational claims awaiting the checks specified here. There is no additional analytic gap identified in this review.

No source or canonical file was edited by this reviewer.
