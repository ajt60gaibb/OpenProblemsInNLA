# IE-05: independent full-target review

**Verdict: PASS — an exact counterexample resolves the canonical equality negatively.**

**Reviewer:** separate Codex agent `/root/prepare_manuscripts`.  
**Date:** 11 September 2026.  
**Reviewed manuscript:** [full-proof.md](full-proof.md), 7,351 bytes, SHA-256 `18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7`.

This is an independent automated-agent mathematical review, with a separately written exact checker. It is not external human peer review or formal proof certification. The reviewer read the full frozen proof, reconstructed the algebra and pivot-path argument, and checked the printed matrices directly. The checker imports neither the author's Gram–Schmidt code nor the parent's independent certificate.

## 1. Exact target and source match

The reviewed canonical target is `linear-systems-and-elimination/IE-05/README.md`, 3,203 bytes, SHA-256 `a126c785c87ae40134d5609d222166692b1f21aae2431bb1a9f645b00e9ab41f`. It asks whether the supremum of element growth over real orthogonal matrices and all admissible partial-pivoting paths equals the first-available-row growth of the specified positive-diagonal QR factor of the all-minus-one strict-lower triangular matrix, for every order at least two.

The primary manuscript was checked at [Peca-Medlin, arXiv:2308.16146v2](https://arxiv.org/html/2308.16146v2), Sections 1.2, 3.1–3.2 and Appendix B. Section 1.2 uses largest-magnitude column pivots and positive-diagonal QR. Appendix B explicitly states the finite-order extremizer conjecture; its separate numerator bound does not optimize the input normalization. Section 3.2 also discusses an asymptotic leading-constant conjecture. The submitted counterexample addresses the former equality, and correctly makes no claim to disprove the asymptotic assertion. The older study of the same orthogonal family by Barlow and Zha is distinguished from Peca-Medlin's element-growth analysis.

An order-eight matrix and one admissible path with a strictly larger ratio suffice to disprove the universal canonical equality. No computation of the true supremum is required.

## 2. Orthogonality, matrix transcription and QR signs

I parsed the displayed integer matrices `H`, `T` and `H_0`, and both displayed diagonal matrices, directly from the frozen Markdown. Separate integer multiplication verifies all entries of

$$
H^T H=D,\qquad H=\widetilde L T,
\qquad \widetilde L=L_8+e_8e_2^T.
$$

The only changed entry of the unit lower triangular matrix is indeed row 8, column 2, from minus one to zero. Every diagonal entry of `D` is positive. The displayed `T` is upper triangular, with positive diagonal

$$
(1,2,8,120,397,1190,3063,5272).
$$

Hence `H D^{-1/2}` is real orthogonal and therefore nonsingular. Moreover,

$$
\widetilde L=(H D^{-1/2})(D^{1/2}T^{-1})
$$

is its QR factorization with positive triangular diagonal. The multiplication order of the diagonal and triangular factors is correct. This identification is exact; it does not rely on approximate orthogonality or a numerical QR convention.

For the canonical matrix, I independently verified `H_0^T H_0=D_0` and solved the unit lower triangular system `L_8 T_0=H_0`. The resulting `T_0` is upper triangular with positive diagonal

$$
(1,8,31,106,341,1024,1,5462).
$$

Thus `H_0 D_0^{-1/2}` is exactly the particular `Q_8` in the canonical target, including its QR sign convention.

## 3. Elimination and all pivot ties

For either case the factorization `Q=L(T D^{-1/2})` is a valid no-exchange LU factorization. Eliminating the previous columns leaves the active first-column entries `L_{ik} T_{kk}/sqrt(D_{kk})`. Its diagonal entry is positive and every other active entry is its multiple by minus one or zero. The diagonal is consequently a largest-magnitude entry and is the first available row. This proves inductively that the claimed path is exactly the prescribed tie path; there are no hidden swaps, zero pivots or forbidden choices.

This argument covers both the repeated ties and the exceptional zero multiplier at `(8,2)`. It establishes one allowed path for the counterexample, which is enough for the supremum over all paths. It does not assume that all tie paths have the same growth.

The Schur-complement formula in the proof is also correct:

$$
S_k=L_{I_k,I_k}T_{I_k,I_k}D_{I_k,I_k}^{-1/2}.
$$

My checker computed these block products and independently performed exact elimination of the printed integer columns. It compared every active entry between the two constructions and checked all 56 multipliers across the two matrices. Positive column scaling preserves the pivot decisions within a column, but does not in general preserve growth. The manuscript and checker correctly retain the different column normalizations when computing entry maxima.

## 4. Exact entry maxima and growth factors

All 408 active entries were compared using integer arithmetic and `fractions.Fraction`: an entry represented by `s` in column `j` has squared normalized magnitude `s^2/D_{jj}`. No floating-point ordering, tolerance or approximate root is used.

For the counterexample, the squared input maximum is `3969/5272`, attained at `(1,8)`. The eight active maxima, multiplied by `sqrt(5272)`, are exactly

$$
63,94,173,338,672,1342,2683,5272,
$$

with the specified attaining locations `(k,8)`. In particular, the largest active magnitude is `sqrt(5272)` and

$$
\rho_{\mathrm{PP}}(\widetilde Q)=\frac{5272}{63}.
$$

For the canonical matrix, the squared input maximum is `2601/3286`, attained at `(3,3)`. The other seven active maxima are exactly the numbers in the manuscript's second table: numerators `96,176,344,684,1366,2731,5462`, each divided by `sqrt(5462)`. Its maximum is the final pivot. Consequently,

$$
\rho_{\mathrm{PP}}(Q_8)^2=\frac{5462\cdot3286}{2601}
=\frac{17948132}{2601}.
$$

I independently obtained the strict positive difference

$$
\left(\frac{5272}{63}\right)^2-
\frac{17948132}{2601}
=\frac{117335164}{1147041}>0.
$$

Both growth factors are positive, so comparison of their squares has the asserted direction. This proves the full counterexample theorem.

## 5. Reproducible independent evidence

The [separate checker](independent-review/exact_matrix_review.py), 6,337 bytes, has SHA-256 `0438a2cf8ea2d43bea3d4f2c508338b413e05b3736807d7d59225b130d425922`. Its [exact output](independent-review/exact_matrix_review.json), 11,723 bytes, has SHA-256 `a3b98531a7aa0ebf238211ca4404c447431853a250693d6744d9e535aa802f3b`.

It uses only Python's standard library. From this directory, reproduce with:

```bash
python3 independent-review/exact_matrix_review.py --source full-proof.md --output independent-review/exact_matrix_review.json
```

The output records every stage maximum and maximizing location, every multiplier, the independently recovered triangular factors, and the exact positive squared gap. The checker rejects a source whose complete hash differs from the reviewed version. These checks supplement the self-contained integer-matrix proof rather than substituting a numerical search for it.

## 6. Amendment, limitations and final disposition

The initially supplied 7,340-byte draft had SHA-256 `ebc80737d81f2e1e6d4a06b6064519f0260bf883ad48864cd9d058c046f82711`. I requested a single attribution clarification: the final sentence now attributes the extremizer conjecture and the cited element-growth analysis to Peca-Medlin, without suggesting that the older orthogonal family originated there. The author retained the [prior draft](full-proof-before-attribution-review.md). A byte comparison confirms that this one sentence is the only amendment; the entire mathematical body and all data are unchanged. The independent checker was rerun against the final hash recorded above and passed.

No mathematical correction or unresolved proof gap remains in this review. The counterexample resolves the exact canonical equality negatively; it does not determine the true extremizers, the full dimension-eight supremum, or the asymptotic leading constant. This report does not certify novelty, later public-branch status, eventual publication formatting or any external human review. Those are separate checks. No canonical repository page or status was edited during this review.

**Signed verdict:** PASS for the complete canonical IE-05 negative resolution, bound to SHA-256 `18d49f30a3ef26f4c88a85c8ea1fc9e5c4e1702b4be6061d39aec892e96a4af7`.
