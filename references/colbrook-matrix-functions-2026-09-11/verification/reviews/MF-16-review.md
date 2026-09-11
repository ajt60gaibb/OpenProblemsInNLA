# MF-16 independent proof review — 2026-09-11

**Verdict: PASS; the canonical universal uniqueness statement is disproved.** The integer example has a negative Jacobian determinant at a real symmetric positive definite solution, and the cited degree corollary applies. The additional interval certificates prove at least three distinct real SPD solutions to that same equation. All stated theorem claims, including the sharp exponent threshold within the specified real-SPD family, pass. No material mathematical gap was found.

This is an independent Codex proof audit, not publication, peer-reviewed acceptance, or certification of priority. The complete source and relevant code were read, exact algebra was independently regenerated, and the applicable primary theorem was checked. No original manuscript or canonical file was edited.

## Source identity and claim locators

The complete source is `.cache/colbrook-research-submission/nla_research/submission/MF-16/manuscript.tex`, including the standalone preamble and bibliography. Hashes use the **entire original UTF-8 source with CRLF changed to LF, without trimming or removing its final newline**.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| Complete MF-16 manuscript | 10584 | `c3cd3f9d31fcfb249b6888d1661def9e5fc45fb4552f54afa646ba5c12f05880` |
| Canonical `matrix-functions-and-stability/MF-16/README.md` before the update | 3614 | `9ed176fb493632a01eba419792904c51fc8dafd88f1023c6a479b5c7af91c90a` |

| Claim | Original manuscript locator | Verdict |
| --- | --- | --- |
| Explicit nonunique equation | Theorem 1, `thm:counter`, line 23 | PASS; resolves canonical target negatively |
| Full derivative and exact negative determinant | `eq:derivative`, line 38; `eq:negative`, line 50 | PASS |
| Generic factored Jacobian | Lemma 2, `lem:factor`, line 59 | PASS |
| Integer-exponent threshold in X B X^r B X | Theorem 3, `thm:threshold`, line 88 | PASS for stated real-SPD domain |
| At least three SPD roots of the explicit equation | Theorem 4, `thm:three`, line 124 | PASS, with audited interval certificates |

## Exact target and use of the primary theorem

The canonical target asks whether every ordinary two-letter symmetric word, with at least one X, has exactly one Hermitian positive definite solution in dimension two for every Hermitian positive definite B,P. The submitted word X B X^12 B X is a palindrome in precisely those two letters; the exponent 12 denotes twelve repeated ordinary letters, not a real-power generalization. Its two distinct real SPD solutions already refute the larger complex-Hermitian universal statement. No reduction from arbitrary complex data to real data is needed.

[Armstrong–Hillar v4, Theorem 1.5 and Corollary 11.1](https://arxiv.org/html/math/0507306v4) give degree one for interlaced symmetric maps and another real positive definite solution at the image of a point with negative Jacobian determinant. Their definition includes this word. The degree result supplies the bounded domain containing every solution; the corollary does not require the image to be a regular value. Conjecture 11.5 is the order-two uniqueness claim. The same paper's special word X B X^2 B^3 X^2 B X differs from the submitted word and does not imply uniqueness here.

## Explicit data and the derivative

B has positive first leading minor 1 and determinant 17-16=1. X0=diag(3,1) has positive leading minors 3 and 3. For every SPD X, the word is `(BX)^T X^r(BX)`, so it is itself SPD. Direct exact multiplication at r=12 gives the stated integer matrix P and

`det P = det(X0)^14 det(B)^2 = 3^14 = 4782969 > 0`.

Differentiating the first and last X gives the first two derivative terms. Differentiating X^r for an integer r>=1 gives `sum_(j=0)^(r-1) X^j H X^(r-1-j)`; this gives the third term without commuting X and H.

I independently generated the Jacobian in the coordinates (X11,X12,X22), with off-diagonal basis matrix [[0,1],[1,0]], in both domain and codomain. The verified matrix is

```text
22320618  31886832      1728
27635000  36403996   6379944
34012224  40389584  17010158
```

Its exact determinant is -11785057051824. The coordinate order agrees with the source's symmetric-matrix identification in dimension two; even a different common linear coordinate choice would conjugate the derivative and preserve its determinant. The negative sign is therefore the sign needed by Corollary 11.1, not a coordinate artifact. It proves Theorem 1 independently of the interval computations.

## Generic determinant factorization: independent symbolic check

At X=diag(t,1), write p=t^r and g=sum_(j=0)^(r-1)t^j. The three derivatives of X^r on the coordinate basis are diag(rp/t,0), [[0,g],[g,0]], and diag(0,r). Substitution into the product derivative produces every entry of the manuscript's displayed generic Jacobian. This includes both diagonal-variable derivatives and the doubled off-diagonal contribution; no division by t-1 is required.

The reviewer-created script `verification/reviewer_mf16_algebra.py` imports no submitted code. It constructs those three derivative columns from matrix multiplication, verifies the whole claimed Jacobian symbolically, expands its 3-by-3 determinant, and compares it with

`p t (r+2)(ac-b^2)^2 [(r+2)(a^2 p t+c^2+acgt)-(r-2)b^2(gt+p+t)]`.

After clearing the harmless factor 1/t, the difference has zero polynomial remainder modulo `p-1-g(t-1)=0`. This relation holds for every integer r>=1 by the finite geometric sum, including t=1 where p=1 and g=r. Thus the check verifies the formula for all claimed exponents and all t>0, rather than a sample of exponents. The calculation was executed successfully with exact SymPy polynomial arithmetic; its recorded output is `verification/reviewer_mf16_algebra.json`. It also independently reproduced P, the full numeric Jacobian, its determinant, and H12=-527992.

This optional reviewer script requires SymPy 1.14 and now uses a plain portable import; the submitted certificate programs use only Python's standard library. Removing the local dependency-path setup after the executed check did not alter the symbolic audit. Its verified JSON output is retained in the package's verification directory.

The determinant's prefactor t^(r+1)(r+2)(ac-b^2)^2 is strictly positive on the admissible SPD domain. Hence the sign questions reduce exactly to H_r as used in the manuscript.

## Sharp family threshold

An orthogonal change of basis diagonalizes any real SPD X and transforms B by the same congruence. Acting identically on domain and codomain conjugates the coordinate derivative, preserving determinant sign. Writing X=s diag(t,1), s>0, then uses homogeneity: the derivative scales by s^(r+1), so its three-dimensional determinant scales by s^(3(r+1))>0. The reduction to the displayed form therefore covers every real SPD X, including repeated eigenvalues at t=1.

For r=1,2, all terms in H_r are positive or nonnegative with a strictly positive diagonal contribution: the nominal subtraction has coefficient r-2<=0. For 3<=r<=6, using b^2<ac in the negative term gives

`H_r > (r+2)(a^2 t^(r+1)+c^2) + ac[4gt-(r-2)(t^r+t)]`.

Expanding gt=t+t^2+...+t^r rewrites the bracket as `(6-r)(t+t^r)+4 sum_(j=2)^(r-1)t^j`, which is nonnegative for those exponents. The Jacobian is consequently positive everywhere. Every target P in the real SPD cone is regular, and each solution contributes +1 to the degree-one count on the bounded domain provided by the primary theorem. The solution set is compact away from its boundary and all roots are isolated; equivalently the regular-value degree formula applies. The total count is therefore exactly one. This justifies the global conclusion; local invertibility alone would not suffice.

For each integer r>=7 choose epsilon in `(0,(r-6)/(2(r-2)))`, a=1, c=t^((r+1)/2), and b^2=(1-epsilon)c. This interval makes epsilon<1, so B is real SPD with determinant epsilon c>0. Substituting gives the manuscript's normalized H_r expression. As t tends to infinity, gt/t^r tends to one and the other vanishing powers really vanish because r>1. The limit is `6-r+2(r-2)epsilon<0`. For sufficiently large finite t, H_r and the Jacobian determinant are negative. Taking P to be the word's SPD image and applying the same corollary proves nonuniqueness. The matrices may depend on r and t; the theorem does not require a single B for all exponents or rational entries for this general construction.

This classification is for the real symmetric SPD family explicitly defined in the manuscript. It is not a shortest-word claim or a classification of every two-letter palindrome. The explicit r=12 real counterexample, however, resolves the full canonical Hermitian uniqueness question negatively.

## Three-root certificate: mathematical reduction

For any SPD solution of the explicit equation, determinant multiplicativity gives `(det X)^14=3^14`, hence det X=3. The parameterization `X(x,y)=[[x,y],[y,(3+y^2)/x]]` covers that determinant surface for x>0 and is automatically SPD by its first principal minor and determinant.

The two-component residual takes the (1,1) and (1,2) entries. A zero fixes those entries of the symmetric word image to those of P. Both matrices have determinant 3^14 and a positive common (1,1) entry, so `M22=(det M+M12^2)/M11` forces agreement in the remaining entry. Thus a certified two-variable root is a solution of the full matrix equation; no equation is silently dropped.

For each rational center c and closed box Q=c+[-delta,delta]^2, with delta=10^(-40), a fixed invertible rational C defines T(u)=u-Cf(u). The mean-value integral on the convex box gives

`T(u) in c-Cf(c)+(I-CDf(Q))[-delta,delta]^2`.

The strict inclusion and infinity-norm derivative bound below one make T a contraction self-map of Q. The contraction theorem gives an actual zero, since C is invertible, and uniqueness within that box. Each box has x>0, the x intervals are disjoint, and neither box contains (3,0). This proves two additional distinct SPD roots besides X0. It does not assert there are exactly three roots globally.

## Interval implementation and executed evidence

I read the entire submitted fixed-point and rational-interval implementations. The fixed-point class represents scaled integer lower/upper endpoints; rational conversion, multiplication, and reciprocal all round outward. Division excludes zero-containing intervals. The centers and radii are exact terminating rationals at the chosen 110-digit precision. The word and its derivative are evaluated letter by letter on the determinant-three surface, using the correct partial derivatives of (3+y^2)/x. The preconditioner is the exact rational inverse of a nonsingular midpoint derivative. All interval multiplications by that rational enclose the actual operation, so approximating it outward does not weaken correctness.

The separate Fraction verifier uses exact rational endpoints and interval dual numbers. It evaluates X^12 using the Cayley–Hamilton recurrence on det X=3, `X^k=u_k X-3u_(k-1)I`, rather than the same long product evaluation. The recurrence and its differentiated dual-number evaluation are valid pointwise on the parameterized surface; interval dependence only enlarges the enclosure. Its rational derivative at the center is checked to be an exact point interval before inversion. It independently checks strict inclusion, derivative infinity norm below 10^(-20), positive x, exclusion of the known root, and separation of the two boxes.

I inspected the fresh logs `.cache/colbrook-research-submission/logs/word_equation_interval_certificate.py.log` and `word_equation_interval_independent.py.log`, together with the run diagnostics. Regeneration and exact stored-result verification passed for the fixed-point certificate, both reported contraction bounds below 10^(-20), and the separate Fraction/Cayley–Hamilton audit passed. The latter generated fresh output. The supplied integer Jacobian verifier also passed. These are executed checks of the audited implementations, not reliance on the attached PASS labels.

The certificate proof is independently sufficient for nonuniqueness and proves the stronger three-root assertion. Conversely, even without it, Theorem 1 and the independently checked negative determinant already resolve the canonical target.

## Status recommendation

**Recommended canonical status: Resolved (negative answer; counterexample).** Record the explicit word, B, P, and at least two distinct real SPD solutions, with the stronger three-solution certificate available. No uniqueness question remains for the universal assertion as stated: one permitted counterexample disproves it. Existence and uniqueness for individual other words are separate questions. No proof repair is needed.
