# MF-14 independent proof and certificate review

Reviewer: independent agent `/root/review_transfer_counterexamples`, 2026-09-11.

**Verdict: PASS for the exact complex degree-42 coverage theorem; PARTIAL resolution of canonical MF-14.** The certificate proves the lower direction, namely that the canonical maximum is at least 42. No upper bound excluding degree 43 is supplied. The full equality must not be marked resolved.

## Reviewed material and original identity

Read the complete original `.cache/colbrook-research-submission/nla_research/submission/MF-14/manuscript.tex`, including its local preamble and every mathematical claim, the canonical `matrix-functions-and-stability/MF-14/README.md`, the complete supplied `code/polynomial_coverage_independent.py`, and both degree-42 certificate JSON files. The manuscript has no external preamble dependency.

Full original SHA-256 after UTF-8 decoding, CRLF-to-LF normalization, and UTF-8 encoding, **without whitespace or final-newline trimming**:

`79b4046bdd0b5075197c6fcaeb5e1352e024c622a72c4b964716295e059803df`

Normalized original length: **8985 bytes**.

## Reviewed revision and provenance

The original claims two supplied verifier implementations, but this archive supplies only `code/polynomial_coverage_independent.py`; the named discovery file `polynomial_coverage.py` is absent. At the parent agent's request, corrected the reproduction description in `references/colbrook-matrix-functions-2026-09-11/reviewed-sources/MF-14.tex`, leaving the original untouched.

Exactly two lines differ after full normalization:

- Line 14, the abstract: replaced the assertion about two implementations with “The supplied integer-arithmetic implementation verifies the certificate.”
- Line 89, the verifier paragraph: describes the supplied standard-library implementation, explicitly notes that the earlier discovery implementation is absent, and retains the exact integer/product-rule/Bareiss methodology and no-floating-point qualification.

All other lines, including every theorem, scheme formula, parameter, coefficient map, determinant, proof argument, and reproduction command, were compared and remain identical. This is a package-description correction, not a mathematical change.

Final full normalized UTF-8/LF SHA-256, again without trimming:

`9d5bb0083bd8521be5264ff70d81e49ef55c006f42f4a0874b851271534718a7`

Final normalized length: **8893 bytes**. **PASS applies to the mathematical claims in both the original and this final reviewed source.** The revised source accurately describes the files supplied.

## Canonical and primary-source match

The canonical target concerns complex coefficients and containment of a complete polynomial space in the Zariski closure of all seven-multiplication outputs, embedded in coefficient space through degree 128. The manuscript's Theorem 1 (`thm:coverage`, line 22) establishes that containment through degree 42 and even Euclidean density of one fixed scheme inside that degree-42 subspace. It does not establish the asserted maximum.

I checked [Jarlebring–Lorentzon, arXiv:2504.01500v3](https://arxiv.org/html/2504.01500v3), the displayed seven-product pattern immediately before Conjecture 13, its two empirically fixed zero entries, and the complex maximal-coverage conjecture. The pattern agrees with the new manuscript. The HTML labels this displayed pattern (77); the manuscript cites the paper's equation (5.7). The checked source supports the attribution of an existing pattern with numerical evidence, rather than a newly invented pattern or an established exact all-degree theorem.

I also checked the constructibility result used in the proof against [the Stacks Project, Chevalley's theorem](https://stacks.math.columbia.edu/tag/00FE). A polynomial map of finite-dimensional complex affine spaces satisfies its finite-presentation hypotheses.

## Scheme audit — §2, lines 28–63

PASS. There are exactly seven displayed products, producing `q_2,...,q_8` from the free inputs `1,x`. Every operand is a linear combination of previously available polynomials. There is no hidden multiplication required in the output combination, because all its coefficients are scalar parameters and linear combinations are free in the canonical model.

The degrees of the monic intermediate polynomials are successively `2,4,6,10,16,26,42`. In each factor its highest-degree term has coefficient one and every parameter multiplies a strictly lower-degree previously computed polynomial. Thus the degree bounds hold identically for all complex parameter values; they are not just observed at the certificate point. The output may have smaller degree when its leading coefficient vanishes, as required for a degree-at-most space.

The groups contain `2+2+5+6+9+11=35` internal parameters and nine output coefficients, so the total is 44. The coefficient map to 43 coefficients is polynomial with integer coefficients. I checked the zero `a_33` and `a_53` slots implicit in the formula and the order of each free parameter against the supplied certificate and the source pattern.

The coefficient-field and operation conventions are exactly those of the canonical target. Matrix substitution preserves the counted product budget because these are polynomials in the same matrix; no commutativity of unrelated matrices is being assumed.

## Independent exact certificate audit — §3, lines 65–89

PASS. I independently transcribed the displayed recurrence into a sparse polynomial ring in `x` and 44 first-order parameter increments, discarding products of two parameter increments. This propagates the full Jacobian simultaneously as exact integers. It does not import or call the supplied directional-derivative evaluator. All six displayed parameter groups and all nine output values were entered from the manuscript, then compared to the JSON.

All polynomial coefficients were retained; no degree truncation in `x` was used. The output and its first-order parameter coefficients have degree at most 42. I selected the 43 columns obtained by deleting **only `b_22`**, preserving the remaining displayed order, and recomputed their determinant by exact fraction-free elimination. Every division was checked for zero remainder. The result was exactly

`-8304099790447595998423664434512844589026004175807386862654720`.

Its residue modulo 65521 is exactly **22531**, as stated. The full parameter order, parameter values, selected column indices, and all 43 output coefficients modulo the stated modulus agree with the supplied certificate. The result is nonzero over the integers, hence nonzero over the complex numbers. No inference from an approximate singular value, a condition number, a random test, or a floating-point determinant is involved.

At the displayed point `a_22=b_22=2`, those two parameter directions in the symmetric product can coincide. Deleting `b_22` therefore does not demand an unjustified assumption that all 44 columns are independent. The required rank is 43, and the explicitly selected minor certifies precisely that.

I separately read the supplied verifier and ran it with Python's `-O` option and `--verify`, comparing against the supplied independent result JSON. It passed. Its checks are implemented through explicit `require` calls rather than removable assertions, so optimization does not suppress verification. The code checks untruncated degrees, selected indices, parameter names, integer determinant, primality of the modulus, output residues, and consistency of the stored audit. The originally absent discovery implementation is unnecessary to the theorem because the supplied exact program and the independently recomputed integer minor both establish the certificate.

## From full derivative rank to coverage — §4, lines 91–100

PASS. Fixing `b_22=2` leaves a polynomial map from complex dimension 43 to complex dimension 43 whose derivative at the remaining coordinates is the displayed nonsingular minor. The complex inverse function theorem gives a nonempty Euclidean-open set in its image. Hence any polynomial vanishing on the image vanishes identically, proving dominance.

Chevalley's theorem supplies the additional step needed for the stronger Euclidean-density statement: the image is constructible. A constructible set dense in an irreducible affine space contains a nonempty Zariski-open subset. Over the complex field the complement of that open subset is a proper algebraic set with empty Euclidean interior, so the open subset is Euclidean dense. Therefore every degree-at-most-42 coefficient vector lies in the Euclidean closure of the image.

The proof does not incorrectly infer global density from the local inverse theorem alone. The constructibility and complex-field steps justify that stronger conclusion. Conversely, the text correctly refuses to infer real density merely from a real nonsingular minor: the real square map demonstrates why local openness is insufficient for that assertion.

For the canonical embedding into degree-128 coefficient space, every output of this scheme has zero coefficients above degree 42, and the degree-42 coordinate subspace is closed. Any polynomial equation in the 129 ambient coordinates that vanishes on all seven-product outputs also vanishes on this scheme's image, hence on its closure inside that subspace. Thus the exact canonical Zariski-closure containment follows. The ambient dimension does not obstruct the lower bound.

Generic complex degree-at-most-42 polynomials are represented exactly because the image contains a nonempty Zariski-open subset. The argument does not assert exact representation for every special polynomial or boundedness of the parameters needed along approximating sequences.

## Status recommendation and exact remaining target

- Recommend **Partially resolved** for canonical MF-14, with the exact lower direction now certified: `C[x]_(<=42)` is contained in the stated Zariski closure, so the requested maximum is **at least 42**.
- The precise remaining direction is to show that `C[x]_(<=43)` is **not** contained in the closure of **all** seven-product outputs. Since the degree spaces are nested, that would exclude every larger degree and establish the proposed maximum. Alternatively, a scheme proving containment through degree 43 or higher would refute the equality.
- Excluding one degree-43 pattern, bounding the degree of this fixed pattern, or establishing generic noncoverage for only one parameterization does not supply this upper direction. The canonical closure also allows limits of other permitted schemes, with higher coefficients tending to zero and potentially unbounded parameter sequences.
- Real global density, exact representation of every polynomial, and a stable practical coefficient-recovery algorithm are not proved and are not required for the certified lower direction.
- PASS means independent analytic and arithmetic review of the candidate. Publication acceptance, formal verification, and priority against all subsequent literature remain separate matters.
