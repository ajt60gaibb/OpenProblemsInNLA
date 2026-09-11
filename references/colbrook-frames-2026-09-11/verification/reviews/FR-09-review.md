# FR-09 independent conference-certificate review

Review date: 2026-09-11. This is an independent proof and implementation audit of the user-supplied conference programs and certificates. No conference manuscript was supplied. The mathematical explanation in [conference-proof.md](../../conference-proof.md) is reviewer-authored exposition of the claim encoded by those files; it is not an attributed original paper. No canonical problem or supplied program was edited.

## Verdict and exact coverage

**PASS for rigorous existence in dimensions d=166,209,256,1505. Canonical FR-09 remains partially resolved.** Each of these four supplied certificates proves existence of a Hermitian complex conference matrix of order 2d, and hence a unit-norm complex equiangular tight frame with 2d vectors in dimension d. The synthesis matrix can also be chosen as two circulant blocks.

The exact target is `frames-and-matrix-designs/FR-09/README.md`: for every integer d>=2, unit vectors with frame operator 2I_d and squared pairwise inner products 1/(2d-1). The certified dimensions meet these exact normalizations, with conference orders 332,418,512,3010 respectively. The submission is finite dimension-specific progress. It neither proves the universal target nor shows the search or certification scheme must succeed for arbitrary d.

The supplied `conference_catalog/catalog_reports.json` contains 91 reports, for every integer from 166 through 256, but only certificates for 166,209,256 are present in that catalog. **The 88 remaining reports do not constitute independently checkable certificates.** Their missing dimensions are 167–208 and 210–255. The independent verifier needs the rational phase anchors, selected coordinates, and preconditioner, not merely reported residuals or scalar bounds. The separate dimension-1505 certificate is present and passes. No failure of ETF existence in a missing dimension is inferred. Existing literature may already cover some dimensions; no claim of first existence or priority is made here.

## Files and immutable identities

Original files are relative to `.cache/colbrook-frames-submission/frames_submission/verification/`. Every file below was read in full where applicable; the large certificate was parsed completely and verified rather than rendered as prose. Hashes are SHA-256 of the complete UTF-8 source after CRLF-to-LF replacement, with no trimming. The raw-byte hashes are identical in this archive because these files already use LF.

| File | Bytes | Full normalized SHA-256 |
|---|---:|---|
| `verify_conference.py` | 10,179 | `e90ffcc35b37ed29d1854473b6b38e4817e4b2676570a0286edc517d8d0d3012` |
| `certify_conference.py` | 5,195 | `43de9c09a5e6dd001f6f55be0e89b82121c1478867e7690f9c06947c9b13d06e` |
| `search_conference.py` | 2,464 | `8cc3dcf863ae1feb96fa91586443ed108973ee967b705e4f63a06cc61a048bd6` |
| `build_conference_catalog.py` | 2,392 | `07615fdef56f814ac16883419a58dc1ec7de018d5e88941b3ea751ceb734717d` |
| `conference_certificate_d1505.json` | 35,281,709 | `226c6fc4cfa38756b0118b0f4939c8944506a09bf7d732c0af86570277537737` |
| `conference_certification_d1505.json` | 1,580 | `b33d93a370c7d41ef92d8e47fa3187bbb1d288ee66b3f7a51a94ea274a7f90bc` |
| `conference_catalog/conference_certificate_d166.json` | 452,670 | `38c5736270d793594865037bed7e36a77f2ead7c8b2c6a52bb3839fef54117f9` |
| `conference_catalog/conference_certificate_d209.json` | 711,137 | `df4e8d7e59b3ffad0dca005d2a9f03d9e8085467691bf8cf40399af0ce93f117` |
| `conference_catalog/conference_certificate_d256.json` | 1,060,964 | `3a42e436c99a126cc37f60106213553567b1ac34faf8dac32764873a02733fc2` |
| `conference_catalog/catalog_reports.json` | 144,527 | `36e79355ec895b8ec3ba08c818053575e026c671ec0eb1eb3446d9aa39849df3` |

There is no original conference manuscript or manuscript hash to report. The full four-program source audit is the relevant implementation review. Certificate metadata uses format `hermitian-conference-cayley-contraction-v1`, anchor denominator 2^60, preconditioner denominator 2^32, interval precision 160 bits, product precision 20 bits, and radius 1/100000000 for each of the four dimensions.

## Mathematical audit

### Exact phase model and equations: PASS

`exact_model` in `verify_conference.py`, line 92 onward, constructs each anchor as (D squared-p squared+2ipD)/(D squared+p squared), so its exact modulus is one. The zero diagonal, conjugate reversal of the a sequence, fixed real middle entry for even d, and b_0=1 are all implemented consistently. There are h+d-1 phases and exactly d-1 distinct selected coordinates, where h=floor((d-1)/2). Unselected phases are fixed. This is a legitimate restricted family for an existence proof; completeness of the parametrization of all frames is neither needed nor established.

The real vector F contains the real and imaginary parts of positive-shift autocorrelation sums. In even dimension the half-period correlation is real, so recording only its real part loses no constraint. Negative shifts are conjugates of positive shifts, and the zero-shift sum is identically 2d-1. Thus the d-1 real equations certify all required correlations, including the even-dimensional boundary case.

The Cayley perturbation of a selected phase z is z(1+it)/(1-it), whose derivative at zero is 2iz. For an a variable, the opposite sequence entry has the conjugate derivative, not the same derivative. The verifier uses precisely this rule. Its Jacobian column accumulates a derivative when the affected entry appears in the first correlation factor and when it appears in the second, conjugated factor. These contributions are both required when the same selected variable affects more than one factor; the implementation includes them.

### Global second-derivative constant and contraction: PASS

The code asserts the second-derivative constant in a comment at line 209. This was independently derived, not accepted from that comment. For q(t)=(1+it)/(1-it), real t gives |q|=1, |q'|<=2 and |q''|<=4. Each correlation summand is a product of two factors, each depending on at most one selected coordinate. The sum of absolute Hessian entries for one term is at most 4+4+2 times 2 times 2=16. This remains valid if the two factors use the same coordinate, have conjugated dependence, or are fixed. Taking a real or imaginary part cannot enlarge the bound. Summing at most 2d terms gives 32d for each equation. There is no missing factor of the number of selected variables, because the bound already sums all Hessian entries of each term.

It follows that ||DF(t)-DF(0)||_infinity<=32d||t||_infinity and the Taylor remainder has norm at most 16d||t||_infinity squared. These bounds hold for every real t, so no unproved small-radius analytic-domain assumption is needed.

For the rational square matrix M, let a bound ||MF(0)||, b bound ||I-MDF(0)||, and K=||M||, all in the infinity norm. The map T(t)=t-MF(t) sends the closed radius-r box into itself if a+br+16dKr squared<r, and is a strict contraction there if b+32dKr<1. These are exactly the final tests at lines 209–215. Completeness of the finite-dimensional closed box gives a fixed point. The separate condition b<1 implies MDF(0), and therefore M, is invertible; the fixed point hence solves F=0 rather than merely MF=0. Local uniqueness holds with the unselected variables fixed, not globally up to frame equivalence.

### Construction to conference matrix and exact ETF: PASS

For the circulant matrices A,B generated by the two sequences, A is Hermitian and all circulant matrices commute and are normal. Vanishing correlations give A squared+BB*=(2d-1)I. Therefore H=[[A,B],[B*,-A]] is Hermitian with zero diagonal, unimodular off-diagonal entries, and H squared=(2d-1)I. In particular, no inverse of B or of a principal block is required.

The eigenvalues of H are plus and minus sqrt(2d-1), each with multiplicity d because trace H=0. Consequently G=I+H/sqrt(2d-1) is positive semidefinite of rank d, with diagonal one, off-diagonal squared modulus 1/(2d-1), and G squared=2G. Factoring G as V*V produces VV*=2I_d and establishes every canonical normalization.

There is also a two-circulant factorization: Fourier transforming each block gives d Hermitian 2 by 2 positive semidefinite Gram blocks. Their trace is two because the original diagonal blocks of G sum to 2I, and each satisfies its square equals twice itself. Every such block has rank one, including cases with a zero diagonal entry. Factoring them frequency by frequency gives the diagonal Fourier representations of two circulant synthesis blocks. This supplies the precise two-circulant implication rather than assuming that any block-circulant Gram matrix has a regular cyclic representation.

## Integer implementation audit

### Outward rounding and unbounded arithmetic: PASS

`FixedIntervals` (line 25) stores integer endpoints scaled by S=2^bits. Rational conversion uses floor at the lower endpoint and ceiling at the upper endpoint. Negation reverses and negates endpoints; integer scaling reverses endpoints for a negative multiplier; multiplication checks all four endpoint products before outward division by S. Complex multiplication is assembled from these enclosing real operations. All these calculations use Python arbitrary-precision integers. Dependency between intervals can enlarge an enclosure but cannot invalidate it.

`interval_dot` (line 75) uses the sign of each integer weight to select the appropriate endpoint, accumulates exact integer sums, and divides outward by the positive rational denominator. Its callers have matching lengths validated by the model dimensions. The residual bound a and row-sum norm K are computed correctly. The pure-Python Jacobian-product branch encloses every entry of I-MJ and sums upper absolute bounds by row, yielding a valid infinity-norm bound b.

### Optional int64 product and coarse-grid correction: PASS

The fast path in `verify` (line 149 onward) constructs C_ij as an integer coarse-grid center for each interval enclosing J_ij. Its epsilon is the maximum of the distances to both endpoints, expressed exactly as a rational number. Hence each true J_ij differs from C_ij/S_J by at most epsilon.

The exact product norm term bounds ||I-M C/S_J||. An n by n entrywise epsilon error has infinity norm at most n epsilon, so the additional term K n epsilon gives the full bound for ||I-MJ||. The dimension factor is n=d-1, as implemented; omitting it would be incorrect, but the code includes it.

Before converting to NumPy int64, the code checks every matrix entry fits and checks L c_max+D_M S_J<2^63, where L is the largest absolute row sum of the integer preconditioner and c_max is the largest absolute coarse Jacobian entry. Every individual product and every partial sum of any dot-product ordering has absolute value at most L c_max. Thus the check rules out signed overflow throughout the integer product, not merely in the final matrix. The identity subtraction and absolute row sums are then evaluated using Python integers. NumPy performs an integer matrix product; no floating-point BLAS rounding is part of this path.

The pass/fail comparisons use exact Fraction values throughout. Decimal conversion happens only after the inequalities pass and cannot make a failed certificate pass. The supplied diagnostics, file names, claimed dimensions in reports, and timing values are not read as mathematical evidence by the verifier.

### Generator, search, and catalog builder: PASS as candidate-production tools only

The search minimizes Fourier-domain correlation defects in floating point. Taking the real part of the Fourier transform of a is consistent with its conjugate-reversal symmetry. Numerical residuals from this program do not establish exact existence.

The generator refines selected phase variables numerically, rationalizes half-angle anchors, and approximates an inverse Jacobian. It correctly changes the derivative scale from the phase derivative i z to the Cayley derivative 2i z when forming the certificate preconditioner. Even an inaccurate search, pivot selection, or numerical inverse is harmless to soundness because the separate verifier re-establishes all necessary inequalities from the exact serialized rationals. There is no guarantee the generator succeeds.

The catalog builder invokes generation and verification dimension by dimension and writes reports. Its bounded seed attempts and default dimension range are not a universal construction. The supplied partial collection of certificates cannot be expanded into a proved full range merely because this builder exists or the report file lists successful entries. Re-running the full search/catalog generation was unnecessary and was not done.

## Fresh execution and independent cross-checks

The parent reviewer ran the unchanged verifier on all four actual certificates, including the heavy dimension-1505 case, and saved [conference-rerun.json](../conference-rerun.json). To avoid redundant heavy computation, this independent reviewer audited the implementation, inspected that fresh output, rechecked its three strict rational inequalities with Fraction arithmetic, and compared all six numerator/denominator bound records against the supplied reports. Every bound matched exactly; timing was excluded from comparison.

The following are rounded display values from that fresh run. The inequalities were decided using the complete rational records, not these decimals. All radii are 10^-8.

| d | a bound | b bound | K | Self-map bound | Contraction bound | Result |
|---:|---:|---:|---:|---:|---:|---|
| 166 | 1.56117e-15 | 0.000464883 | 2.758764 | 5.38312e-12 | 0.000611428 | PASS |
| 209 | 1.69422e-15 | 0.000488228 | 2.335565 | 5.66498e-12 | 0.000644430 | PASS |
| 256 | 1.13124e-15 | 0.000679001 | 2.593424 | 7.85340e-12 | 0.000891454 | PASS |
| 1505 | 6.19164e-15 | 0.008622132 | 5.874608 | 1.00374e-10 | 0.011451344 | PASS |

This reviewer separately ran dimension 166 through `--pure-python`, eliminating the optional NumPy matrix product. [The independent output](../conference-d166-independent-pure-python.json) passes with the same a,K,r and a sharper b=4.15407727956e-7; its contraction bound is 0.000146960927249. This validates a supplied certificate through the alternate product path, not merely by reading a pre-existing result label.

An additional [independent exact-rational model check](../conference-independent-model-check.py) directly expanded correlation derivatives for rational anchor examples in dimensions 3,4,5,6,7,8, using a dense product-rule calculation instead of the supplied sparse-column accumulation. It checked 166 exact residual and Jacobian entries against the verifier's intervals; all were enclosed. Both odd and even models were exercised. These finite checks corroborate the implementation; the universal Hessian bound and contraction implication were proved analytically above.

Normalized full-file SHA-256 values for the verification artifacts at review time:

- `conference-rerun.json`: `44baec20d9267f70200a7efcb3a2bd34b027b4ef04f572d1724c389e13222918`.
- `conference-d166-independent-pure-python.json`: `9507221041eb2cdaeb21aa9da6e13b339d864583cddbdb8111ab1b299b7c0c15`.
- `conference-independent-model-check.py`: `e09eda5f4c6d1feb9ff171316d9caeba7075e910e8c1f1e392e10af7550e6c8e`.

Rerunning output files can change timing fields and thus their file hashes while leaving exact mathematical bounds unchanged.

## Primary sources and limitations

Primary sources accessed on 2026-09-11:

- [Iverson, Jasper, and Mixon, arXiv:2410.17379v1](https://arxiv.org/html/2410.17379v1), Theorem 23 and equation (5): the block-Fourier characterization and regular-representation condition justify the two-circulant interpretation. Its abstract and Section 6 distinguish proved dimensions through 165 from numerical constructions through 1500. This distinction is retained; the supplied dimension-1505 certificate is an exact existence certificate, not an extrapolation of that numerical range.
- [Glazyrin, arXiv:2608.16116v1](https://arxiv.org/html/2608.16116v1), Proposition 1 and Conjecture 1: the signature-matrix criterion gives the ETF correspondence, while the universal redundancy-two assertion remains the stated conjecture. Its later constructions do not make a finite certificate collection a proof in all dimensions.

The original Fallon–Iverson DOI was also attempted, but its landing page did not load in this review. The available primary papers above state the relevant conjecture and constructions explicitly. The proof in the companion note derives the specific construction directly and does not rely on inaccessible content.

No mathematical or overflow gap was found for the four actual certificates. The material limitation is documentary and quantificational: 88 reported catalog cases lack certificates, and the canonical statement quantifies over all dimensions. The appropriate record is verified finite-dimensional partial progress, with FR-09 status unchanged and no novelty or author-identity claim.
