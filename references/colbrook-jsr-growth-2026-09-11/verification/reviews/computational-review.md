# Independent construction and computational review

Review date: 2026-09-11. Package: .cache/proposed-solutions/nla_submission.

**Verdict: PASS for the exact rational construction and the inspected computational checks.** The generator implements the MF-12 manuscript's specified matrices exactly, including rational noninteger exponents, integer exponents and exponent zero. The symbolic identities and finite numerical diagnostics must be distinguished: the latter are not proofs for all words, all lengths, all matrix families, or arbitrary real input exponents.

This review covers all five Python files in construction/ and verification/, read completely before execution. The full MF-12 manuscript was also read to check the construction correspondence. The audit/network scripts were outside this task and were not executed. No canonical file, supplied program, original result, or manuscript was edited.

## Source identity

source-hashes.json next to this report records raw-byte and complete UTF-8/LF SHA-256 hashes of the mathematical code, manuscripts, examples and supplied result JSONs. Normalization replaces CRLF with LF without trimming or other changes.

| Reviewed source | Complete UTF-8/LF SHA-256 |
| --- | --- |
| construction/rational_growth_pair.py | 84411818678e01f1e8ebc1b44812fc1fc8c7eb33c94876cb03d83452fde48ce7 |
| construction/test_rational_growth_pair.py | 3f7d87e3cae497fc223ef5d22a553f1459b5b59d828eb350629b10d1d6e58192 |
| verification/enumerate_growth_words.py | 72ac60f2a17f4d98bf0ec2a3f9a75de12744ff94ae7573e039a587f35062cdd8 |
| verification/verify_growth_construction.py | 57b27cda9f132701eea3f845f282ffca6b0d8e9d45bfd7ad4044b4465931e3c7 |
| verification/verify_triangular_comparison.py | a0375a71a47d6f059855e7090bc4263c24cdb82d88b1da1b9ab2fb0886fc2041 |
| MF-12/arbitrary_growth_exponents.tex | 7a58a5086934410dc8c1172537a7b3031047094a7da577a5d3e24aaee21adf66 |

All construction/, verification/ and examples/ files were copied unchanged to .cache/proposed-solutions/rerun. Fresh outputs are in its fresh-results/ subdirectory. The copied historical results remain available separately in their original relative locations for comparison.

## Exact generator and the MF-12 proof

The input is an exact nonnegative Fraction \(\gamma\), split as \(m+\alpha\), with \(m=\lfloor\gamma\rfloor\). For a nonzero fractional part \(\alpha=a/b\) in lowest terms, the generator sets
\[
 \lambda=2^{-b},\qquad \mu=2^{-(b-a)}.
\]
Since \(1\le a<b\), one has \(b\ge2\), \(0<\lambda\le1/4\), and \(\lambda<\mu<1\). The exponent relation \(\mu=\lambda^{1-\alpha}\) follows exactly from these integer exponents; no floating-point logarithm is used to choose the matrices.

The generated six-dimensional matrix is precisely
\[
 A=\operatorname{diag}(1,J_\lambda,J_\mu,1),\qquad
 J_t=t\begin{pmatrix}1&1\\0&1\end{pmatrix}.
\]
Its off-diagonal entries are at the correct locations for the two Jordan blocks. The generated fixed matrix has the two repeated rows \((1,-1,0,1,0,0)\), two zero rows, and the two repeated rows \((0,0,0,0,0,1)\), in the exact order of equation (P) in the manuscript. It is \(VU\), with the manuscript's displayed \(U,V\).

For noninteger \(\gamma\), both generators are tensored with the same integer Jordan block \(J_{m+1}\). The nested-index implementation of the Kronecker product has the standard row and column ordering. Every length-\(n\) product is therefore the corresponding base product tensored with \(J_{m+1}^n\), exactly as the proof requires. The lifted second generator need not remain an idempotent when \(m>0\); the proof uses the common Jordan factor, not idempotence of the lifted generator.

For integer \(\gamma=m\), the output is the pair \(\{J_{m+1},0\}\). At \(\gamma=0\) it is the pair of distinct one-dimensional matrices \(\{1,0\}\). These handle the endpoint without invoking the fractional construction. The dimensions \(6(m+1)\) and \(m+1\) agree with the theorem.

All matrix entries are Fraction objects until conversion to exact rational strings in JSON. Kronecker multiplication by integer Jordan entries preserves dyadic denominators. Resource guards reject requests exceeding the configured limits; they do not round exponents or alter the construction. Rational strings and decimal strings accepted by Fraction are exact inputs. An arbitrary irrational real exponent cannot be encoded through this finite rational interface, and the code expressly does not claim to do so.

The separately exposed fractional_pair function also accepts rational \(\lambda,\mu\) giving irrational exponents, such as \((1/4,1/3)\). This matches the manuscript's additional rational-pair example; it is distinct from the dyadic interface for specified rational \(\gamma\).

The six exact unit tests pass. They cover exponent one-half, zero and integers through five, exponent seven-thirds, dyadic entries, the rational pair with irrational exponent, and invalid/resource-limited inputs. The half-exponent test checks \(P^2=P\) and exact compressed powers through \(q=11\). The freshly generated example JSONs for \(\gamma=1/2\) and \(\gamma=7/3\) exactly equal the supplied examples, including every matrix entry and metadata field. Their dimensions are respectively 6 and 18.

## Growth-construction verifier

The symbolic section verifies the Jordan power formula by a base case and induction identity for symbolic nonnegative integer \(q\), and checks
\[
 UA^qV=\begin{pmatrix}1-q\lambda^q&q\mu^q\\0&1\end{pmatrix},
 \quad UV=I,\quad P^2=P,\quad UU^\top=\operatorname{diag}(3,1),
 \quad V^\top V=2I.
\]
These are exact SymPy identities, rather than floating-point spot checks. The Jordan induction and these identities establish the algebraic formulas for all such \(q\); they do not on their own establish the manuscript's Hölder estimate for all switching words.

The sampled-gap part correctly multiplies compressed factors in the same order as the full six-dimensional words. It includes empty gap lists, zero gaps, arbitrary end powers, pure A words, and consecutive P words. The accumulated loss mass follows the same recurrence as \(1-\prod(1-\ell_q)\). Full products are compared with the factorization rather than only rechecking the compressed recurrence.

The exact_log_floor helper starts from a floating-point logarithmic estimate but adjusts it with exact integer comparisons until the defining inequalities hold. For the tested parameters and lengths, this gives the intended \(q\), including exact power thresholds. The large-length lower-bound diagnostic uses 100-digit mpmath arithmetic and stable log1p/expm1 evaluation. It is a high-precision check, not an exact rational certificate; the longest lengths are evaluated through the closed scalar expression rather than by multiplying \(10^{160}\) matrices.

The default full run passed with:

- 46 parameter sets, including exponents near both fractional endpoints, dyadic choices, and the rational pair with irrational exponent.
- 46,000 random gap lists and 46,000 corresponding full words.
- 368 pure-A/consecutive-P checks.
- 9,936 tested lower-bound lengths, reaching \(10^{160}\).
- 40 tensor-product and Jordan-growth checks.

## Triangular-comparison verifier

The exact rational five-dimensional block example verifies the damping identity as a composition of convex averages of sign-conjugate matrices. The numerical block masks and the decreasing diagonal scales use the matching lower-block orientation. For a cross-block entry, successive cuts multiply its scale by the product of adjacent ratios, giving the required diagonal similarity.

The finite-horizon tests construct a metric with condition number \(d\), normalize the old-coordinate family in that metric, and separately check the old perturbation bound, the new perturbation bound, damping of products, the resulting product estimate, and reconstruction of the original similarity. Real and complex examples are both used. Threshold cases include \(s=1\), log-uniform thresholds, and the horizon-dependent threshold from the proof discussion.

The full supplied diagnostic counts were rerun successfully: 10,000 damping trials and 5,000 finite-horizon trials. Of the latter, 4,147 had a wide gap. The largest damping-product norm ratio was 1; the largest reconstruction relative error was approximately \(1.88\times10^{-15}\). These are finite floating-point tests of specified examples and cannot certify a joint spectral radius, a universal dimension bound, or a global Hölder theorem.

## Exhaustive finite-word enumeration

The binary-word enumeration implementation covers all \(2^n\) words at each requested length. Its suffix array is built by prepending A to every previous suffix and then P to every previous suffix. By induction this orders the suffixes according to the stated leftmost-bit convention. Combining each enumerated prefix with the complete suffix array therefore omits no word and creates no unintended switching restriction.

The reported maximizing word is independently reconstructed and its norm compared with the batched result. The maximization uses float64 SVD values, with explicit numerical tolerances in the bound checks. Thus it is exhaustive over a finite set of words but is not an interval-arithmetic certificate of the spectral norms.

The requested rerun matches the supplied full range: \(\alpha=1/2\), \(\lambda=1/4\), lengths 1 through 24, batch size parameter 14. The explicit allow-expensive flag is used for the source's guarded lengths above 20. **The full run completed with exit code zero, both completion and bound-pass flags true, and all \(2^{25}-2=33,554,430\) words checked.** Recorded enumeration time was approximately 109 seconds. At length 24 the reported maximum spectral norm was 4.067906945934861, attained by the reconstructed word 100010010010010010010101. Completion was checked against the final flag, not an intermediate checkpoint: the program writes a partial JSON after every length.

## Fresh outputs and reproducibility

The selected directory for copying fresh verification evidence is:

.cache/proposed-solutions/rerun/fresh-results/

It contains the following outputs, per-run argument/exit/timing manifests, stdout and stderr logs, and the combined run-manifest.json:

- alpha_half_matrices.json and gamma_seven_thirds_matrices.json.
- growth_construction_checks.json.
- triangular_comparison_checks.json.
- growth_exhaustive_alpha_0p5.json.
- construction_tests.stderr.txt, recording all six passed tests.

All six launched processes exited successfully. The two exact example JSON files reproduce identically. Floating-point diagnostic outputs can differ at rounding level across library/platform versions and should not be described as byte-identical replications. Timestamps and elapsed times necessarily differ. The returned diagnostic pass flags are supported by inspected assertions and successful process exit codes; their scope remains the finite and symbolic checks described above. After completion, every original inventoried source and supplied-result file was rehashed and confirmed unchanged.

## Scope and issues

No mathematical mismatch between the exact generator and the MF-12 construction was found. No implementation correction was needed for these runs. The two main verifiers reject optimized Python execution because their assertions are part of the checks; all runs here used ordinary, non-optimized execution.

This computational review does not certify literature priority, repository eligibility, the entire MF-05/MF-07 analytic argument, or the MF-12 universal conclusion by extrapolating samples. The generator's formulas agree with the MF-12 proof, and the exact/symbolic identities support that correspondence. Acceptance of the all-word and all-length theorems rests on the separate full mathematical proof reviews.
