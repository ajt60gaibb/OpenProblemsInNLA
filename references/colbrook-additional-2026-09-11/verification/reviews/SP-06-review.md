# SP-06 independent agent proof review

**Verdict: PASS — complete negative resolution of the exact displayed canonical finite-section target.**

**Review date:** 11 September 2026.  
**Reviewer:** separate Codex review agent `/root/review_additional_counterexamples`.  
**Canonical target:** `eigenvalues-and-inverse-problems/SP-06/README.md`, complete problem statement.  
**Original manuscript:** `.cache/colbrook-additional-submission/nla_additional_submission/manuscripts/SP-06-proposed-resolution.md`, read in full.

This is an independent audit of every construction and implication, not a presumption that the submitted diagnostics certify the result. It is an agent review, not external human peer review or a formal proof certificate. The reviewer did not edit the manuscript, canonical target, catalog status, submitted script, or remotes.

## Exact reviewed identity

The hash covers the **entire original Markdown manuscript**, including front matter, notices, footnote, and references. Decode the original bytes as UTF-8, replace CRLF with LF, and re-encode as UTF-8, preserving every other byte of text and all whitespace. No proof extraction or trimming was applied. The original already used LF throughout and had no bare CR characters.

- SHA-256: `b5e84b14b34e9e7f4ea87b7ba00e3a9494960adb0f094093d49660621b6e8d83`
- Original length: 5,409 bytes.
- Normalized UTF-8 length: 5,409 bytes.

The PASS applies to the mathematical argument in this full-file identity against the target read on the review date. It does not independently verify separately generated TeX or PDF versions or subsequent edits.

## Exact target and corrected source meaning

The canonical assertion is that a complex Laurent polynomial, with nonzero extreme coefficients and both a negative and a positive degree, being real on one Jordan curve in the punctured plane forces every finite Toeplitz section to have real spectrum. No lower size bound other than n at least one is present. A valid symbol with one nonreal eigenvalue at n = 2 therefore disproves the complete universal assertion.

The original article uses the same entry convention, a_{i-j}, and the same Laurent polynomial class in equation (2). Its Theorem 1 identifies the Jordan-curve condition as (ii) and reality of all finite sections as (iii). The appended erratum on printed p. 27 explicitly leaves (ii) implying (iii) unproved and distinguishes its weaker limiting-spectrum variant. Thus this manuscript targets exactly the withdrawn finite-section implication. No assumption of a circular curve, injectivity of b along the curve, a regular value, or minimum section size is missing from the source statement. See [Shapiro–Štampach, arXiv v4, equation (2), Theorem 1 and appended erratum](https://arxiv.org/pdf/1702.00741v4).

Giandinoto's later conjecture concerns the asymptotic spectrum and its scalar specialization; it supplies context but is not the finite-section statement disproved here. See [Giandinoto, Conjecture 1.1 and the end of section 2](https://arxiv.org/html/2411.16266v1).

## Complete construction and proof checks

### 1. A radial solution exists uniquely at every angle

Write

\[
F(r,t)=r^2-1+\tfrac14r^3\cos t.
\]

On the fixed interval one half to two, for every real t,

\[
F(\tfrac12,t)=-\tfrac34+\tfrac1{32}\cos t
\leq-\tfrac{23}{32}<0,
\qquad
F(2,t)=3+2\cos t\geq1>0.
\]

The derivative computation and its uniform lower bound are correct:

\[
F_r(r,t)=2r+\tfrac34r^2\cos t
\geq r(2-\tfrac34r)\geq\tfrac r2\geq\tfrac14>0.
\]

The intermediate value theorem gives a zero in the open interval, and strict monotonicity on the entire closed interval gives uniqueness there. Possible roots outside this interval are irrelevant. This yields a specified positive function rho(t) for every real t; there is no numerical choice of a branch.

### 2. Continuity, periodicity, and the Jordan property

For any sequence t_j tending to t, the values rho(t_j) lie in a common compact interval. Each subsequential limit solves F(r,t) = 0 by continuity of F. The strict endpoint signs exclude endpoint zeros, and uniqueness identifies the limit as rho(t). If the whole sequence failed to converge to rho(t), a subsequence uniformly separated from it would itself have a convergent subsequence, contradicting this identification. Thus the sequential argument in the manuscript proves continuity in full.

Since F(r,t + 2 pi) equals F(r,t), uniqueness in the same interval implies periodicity. Consequently the formula

\[
e^{it}\longmapsto\rho(t)e^{it}
\]

defines a continuous map on the unit circle, including across the angular endpoint. Positivity of rho makes equality of two image points imply equality of their directions, hence t and u agree modulo 2 pi. Periodicity then makes the parameters the same point of the unit circle. The map is injective, so its image gamma is a Jordan curve under precisely the definition used by the target. Compactness of the unit circle and the Hausdorff property of the plane also make it a homeomorphism onto its image.

Every point of gamma has modulus greater than one half, so zero is avoided. The radial region

\[
D=\{re^{it}:0\leq r<\rho(t)\}
\]

is bounded, connected, contains the disk of radius one half, and has boundary gamma. Hence it is the interior Jordan domain and is star-shaped about zero. This verifies even the manuscript's stronger assertion that gamma encloses zero. The optional real-analytic claim is also valid by the implicit function theorem, because F is real-analytic and its radial derivative never vanishes at these zeros; uniqueness makes the local branches agree globally.

### 3. Reality on the entire curve

For the auxiliary Laurent polynomial a(z) = 8z^{-1} + 8z + z^2, substituting z = re^{it} gives

\[
\operatorname{Im}a(re^{it})
=-\tfrac8r\sin t+8r\sin t+r^2\sin(2t)
=\bigl(8r-\tfrac8r+2r^2\cos t\bigr)\sin t
=\tfrac{8\sin t}{r}F(r,t).
\]

All factors and signs agree with the manuscript. Substitution of r = rho(t) makes this zero for every angle. This includes t a multiple of pi without dividing by sin t or making any exceptional choice. Division by r is legitimate because rho is positive. Thus a is real on all of gamma.

Since the scalar polynomial x minus x squared maps real numbers to real numbers, b = a - a^2 is real on the same gamma. There is no requirement that b or a be one-to-one or have nonzero derivative on gamma.

### 4. Exact Laurent coefficients and admissibility

Independent multiplication yields

\[
a(z)^2=64z^{-2}+128+16z+64z^2+16z^3+z^4.
\]

The cross term 16z comes from the product of 8z^{-1} and z^2 and is essential for the negative coefficient b_1. Subtracting gives

\[
b(z)=-64z^{-2}+8z^{-1}-128-8z-63z^2-16z^3-z^4,
\]

exactly the asserted expression. Its extreme powers are -2 and 4, with nonzero coefficients -64 and -1. Therefore the target's parameters can be chosen as r = 2 and s = 4. The integer coefficients are in particular allowed complex coefficients. Laurent polynomials are defined throughout the punctured plane, so the entire constructed curve lies in the domain of b.

### 5. A finite section violates the conclusion

With the stipulated indexing, the first off-diagonal above the main diagonal is b_{-1} and that below it is b_1. Thus

\[
T_2(b)=\begin{pmatrix}-128&8\\-8&-128\end{pmatrix}.
\]

Its trace is -256, its determinant is 16448, and its monic characteristic polynomial is

\[
\lambda^2+256\lambda+16448=(\lambda+128)^2+64.
\]

The discriminant is -256. Its two distinct roots are exactly -128 + 8i and -128 - 8i. This is an exact algebraic violation at the permitted size n = 2. Even transposing the Toeplitz indexing convention would preserve these eigenvalues, though no such convention change is needed.

The functional-calculus warning in the manuscript is correct. Here T_2(a) has diagonal zero and off-diagonal entries eight, so T_2(a)^2 = 64 I. Consequently T_2(a) - T_2(a)^2 has diagonal -64 and both off-diagonal entries eight; it does not equal the displayed T_2(b). The argument never relies on the false commutation of finite truncation with polynomial composition.

## Independent exact checks and adversarial review

I independently wrote a small standard-library Python computation that multiplied exponent/coefficient dictionaries over the integers. It reproduced all coefficients of a squared and b, then obtained the trace, determinant, and negative discriminant above. Rational checks confirmed the endpoint bounds -23/32 and 1 and the uniform derivative bound one quarter. I did not reuse the submitted script or use sampled curves or numerical roots as proof.

I specifically checked continuity of the chosen root branch, uniqueness only where needed, angular periodicity, injectivity on the circle rather than on a closed interval, the location of zero, endpoint angles where sin t vanishes, the polynomial cross terms, and the finite-section indexing and size quantifier. Each point is covered by the exact argument. No material gap or false intermediate claim was found.

## Scope and limits

PASS concerns the full negative answer to the assertion that every finite section has real spectrum. A nonreal spectrum at a single finite size does not itself establish any claim about the limiting spectral set. This review therefore does not assert a negative resolution of the weaker limiting-spectrum implication or of Giandinoto's asymptotic block conjecture. It also does not classify the smallest possible bandwidth, establish novelty or priority, certify publication, or substitute for external human peer review. The primary source was checked for the exact original and corrected statement; an exhaustive literature search was not performed.
