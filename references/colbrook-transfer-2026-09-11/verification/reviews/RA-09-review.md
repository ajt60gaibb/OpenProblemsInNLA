# RA-09 independent proof review — 2026-09-11

**Verdict: PASS.** The submitted ordered Frobenius theorem proves the exact canonical RA-09 implication. No material mathematical gap was found. The ordinary residual premise proved in the manuscript is weaker than the canonical trace-deficit premise; the implication between them is established below. This is an independent Codex mathematical audit, not journal peer review or a certification of priority.

## Reviewed input and identity

The complete original `manuscripts/02_frobenius_function_transfer.tex`, its complete `manuscripts/common_preamble.tex`, and the complete `research_notes/commuting_Schatten_factor_two.md` were read from `.cache/colbrook-transfer-submission/nla_submission/`. Both Frobenius theorems and all their supporting arguments were reviewed, including material not necessary to resolve RA-09. Submitted diagnostic programs were not used as premises or substitutes for checking the proof.

SHA256 below means: decode the complete original bytes as UTF-8, replace CRLF by LF, encode as UTF-8, and hash. No trimming, whitespace rewriting, or final-newline removal was performed.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| `manuscripts/02_frobenius_function_transfer.tex` | 13326 | `b71d409a3fea3720a83380bdfddc2cd5cdcdbf2381deba445e79b56ed53ca4fa` |
| `manuscripts/common_preamble.tex` | 1105 | `8b784fe6ac56151b19d51534474560bf45df7b278015cd0c834569e2550fada4` |
| `research_notes/commuting_Schatten_factor_two.md` | 1890 | `1d6915105211c3a92184f9a28c9d9cb5d4d384213ecc9c482e2282418dfeaa42` |
| Canonical `randomized-and-low-rank-approximation/RA-09/README.md` before this update | 3565 | `19688679b8c46365dc25a80c0a0ad2c8b58bcb24d1cfb12a5f36c769ce833d45` |

The preamble defines standard notation and theorem environments; it contains no hidden mathematical hypotheses.

## Exact target and reduction

The canonical target assumes real symmetric `A >= Ahat >= 0`, continuity, nonnegativity, monotonicity and concavity of `f`, and

`||A||_F^2 - ||Ahat_k||_F^2 <= (1+epsilon) T_A`.

It asks for the corresponding squared Frobenius bound with the same epsilon and the specified common eigenvectors in the two truncations. Put `B=Ahat_k`. For every permitted eigenbasis choice, `0 <= B <= Ahat <= A`, and the manuscript's `C` equals the canonical `f(Ahat)_k`. Also

`||A-B||_F^2 = ||A||_F^2 - ||B||_F^2 - 2 tr(B(A-B)) <= ||A||_F^2 - ||B||_F^2`,

because `tr(B(A-B)) = tr(B^(1/2)(A-B)B^(1/2)) >= 0`. Thus the canonical premise implies the manuscript's premise with `eta=epsilon`. Concavity and `f(0)>=0` give `f(x)>=(x/y)f(y)` for `0<x<y`, so every canonical function belongs to the manuscript's class. The ordered theorem therefore gives precisely the required conclusion. No converse equivalence between the two premises is claimed.

The stronger claim proved by the manuscript is ordinary squared-residual transfer, for continuous nonnegative nondecreasing functions whose ratio `f(x)/x` is nonincreasing. The exact target does not require that stronger claim, but the audited proof establishes it.

## Scalar preliminaries and ordered certificate

For `0<=x<y`, subhomogeneity gives `f(x)>=(x/y)f(y)`; continuity handles `x=0`. If `y>=tau>0`, this implies `0<=f(y)-f(x)<=c(y-x)`, with `c=f(tau)/tau`. Above tau, `f(a)<=ca`; below tau, `f(a)>=ca`. Consequently `c^2 T_A<=T_f`. If `f(tau)=0`, these same inequalities force `f` to vanish everywhere, including at zero, and the conclusions are immediate.

For positive `a,b`, write `h(a)=(c^2 a^2-f(a)^2)_+`. When `b>=tau`, the right side of the ordered scalar certificate is zero. Its left side is exactly

`c^2(a-b)^2-(f(a)-f(b))^2+(f(a)^2-c^2a^2)_+`,

which is nonnegative by the scalar Lipschitz inequality. This identity does not assume operator monotonicity.

When `b<=tau`, set `d=f(b)/(cb)>=1`, `z=a/b`, and `G=(2f(b)f(a)+h(a))/(c^2b^2)`. The three lower bounds on `G` are valid:

1. For `z<=1`, subhomogeneity gives `G>=2d^2z`.
2. For `1<=z<=d`, monotonicity gives `G>=2d^2`.
3. For `z>=d`, if `a<=tau` then `f(a)>=ca`. Otherwise `phi=f(a)/(cb)` belongs to `[d,z]` and `G=z^2+2d phi-phi^2>=2dz`, by minimizing the concave quadratic over that interval.

I independently expanded the normalized difference of the certificate's two sides. Before the branch bounds it is

`G - 2z - 2d^2 + d + 1 + d(d-1)/z`.

Substituting the three lower bounds gives exactly

`(d-1)[2(d+1)z^2-(2d+1)z+d]/z`,

`(d-z)(2z+d-1)/z`, and

`(d-1)(z-d)(2z-1)/z`.

The first quadratic has discriminant `1-4d(d+1)<0` and positive leading coefficient. The other factors have the stated signs. The endpoints `z=1`, `z=d`, `d=1`, and `b=tau` are included. The displayed factorization is correct.

## Eigenvectors, averaging, and trace closure

From `A>=b vv^T` with `b>0`, testing against `ker A` proves that `v` lies in `range A`. Congruence on that support gives `b v^T A^+ v<=1`. Thus in the positive-eigenvalue average the weights sum to one and the average of `1-b/a` is `1-b v^T A^+v>=0`. The coefficient `f(b)(f(b)-cb)_+` is nonnegative, giving exactly the manuscript's averaged inequality.

For padded zero eigenvalues of `B`, that averaged inequality needs no support argument: its left side reduces to `f(0)^2-2f(0)v^T f(A)v<=-f(0)^2<=0`, and its right side is nonnegative. This covers arbitrary choices of the padded orthonormal vectors.

Summing and using `P=sum_j v_jv_j^T<=I`, with `h(A)>=0`, yields the displayed trace bound. If `d_i=f(a_i)^2-c^2a_i^2`, its terminal expression is `sum_i(d_i)_+`. For `i<=k`, `a_i>=tau` makes `d_i<=0`; for `i>k`, `a_i<=tau` makes `d_i>=0`. At ties with tau the expression is zero. Hence the expression equals `T_f-c^2T_A`, as asserted. Error expansion uses `tr C^2=sum_j f(b_j)^2` and contains no omitted cross terms. The ordered inequality follows.

Finally the residual excess is nonnegative because `B` has rank at most k. Under its relative premise it is at most `eta T_A`, and the tail comparison gives `||f(A)-C||_F^2<=T_f+eta c^2T_A<=(1+eta)T_f`.

## Full-manuscript audit: unordered theorem

The unordered certificate is also valid. With `g(1)=1`, subhomogeneity bounds `g(a)` between `a` and 1 below 1, and between 1 and `a` above 1. If `a>=1`, then `H(a)=2a^2-g(a)^2`; subtracting this from the certificate's left side gives `(g(a)-g(b))^2-2(a-b)^2<=0`. If `a<=1<=b`, the same difference proves the bound since `2a^2-g(a)^2<=1`.

For `a,b<=1`, write `u=g(a), v=g(b)`. If `a<=b`, `z=a/b` and `u>=zv` give `(1-2z)(v^2-2b^2)`. For `z<=1/2` this is at most 1 using `v<=1`; for `z>=1/2` it is at most `(2z-1)b^2<=1` using `v>=b` with the reversed sign handled correctly. If `b<=a`, monotonicity gives `u>=max(a,v)`. The `v>=a` branch is at most `a^2-2(a-b)^2`; the `v<=a` branch is a convex quadratic on `[b,a]` with endpoint values `a^2-(a-b)^2` and `a^2-2(a-b)^2`. These are at most 1. Zero cases are included by these inequalities or continuity.

After rescaling, `H_tau` is constant below tau. Above tau,

`f(y)^2-f(x)^2 <= c(y-x) c(y+x)`,

so `2c^2a^2-f(a)^2` is nondecreasing and starts at `f(tau)^2`. The k largest eigenvalues of `H_tau(A)` are therefore those indexed by the k largest `a_i`. The projector variational bound follows directly by putting `w_i=u_i^TPu_i`: `0<=w_i<=1`, `sum w_i=k`, so `sum w_i H_tau(a_i)` is at most the top-k sum. Trace expansion now gives the factor-two squared-excess bound. The conversion to norm excess follows by squaring `sqrt(1+4epsilon+2epsilon^2)<=1+2epsilon`.

This is a Frobenius theorem only; neither changing the subscript to nuclear nor invoking equivalence of finite-dimensional norms gives the dimension-independent RA-10 conclusion.

## Boundaries, truncations, and sharpness

- If `tau=0`, the ordinary relative premise forces `A=B`. The canonical trace-deficit premise also implies this, by the trace bridge and a zero optimal tail. The selected k-space contains `range A`; `f(A)-C` equals `f(0)` on its `(n-k)`-dimensional complement and vanishes on the selected space. Its squared norm is exactly `(n-k)f(0)^2=T_f`. There is no use of `f(0)/0`.
- The same reasoning treats the manuscript's additional `k=n` observation. This is beyond the canonical `k<n` domain but is correct.
- For `f(0)>0`, `C` is a rank-at-most-k spectral truncation with zero padding included; it is not the full `f(B)`. The proof respects this distinction throughout.
- Within repeated eigenspaces of `Ahat`, every choice permitted by the canonical statement is covered: it produces some `B<=A` and the corresponding same-vector `C`. A newly created plateau of `f(Ahat)` does not authorize an independently rotated truncation. The manuscript explicitly preserves this convention.
- With `f(x)=x`, the ordered excess inequality is equality. Positive excess examples exist, for instance `A=diag(2,1)`, `B=diag(1,0)`, `k=1`. Thus its universal multiplier one is optimal. This sharpness is for the manuscript's residual/excess theorem, not an additional claim that the stronger trace-deficit premise requires an optimal multiplier one.
- For unordered sharpness, the displayed diagonal matrices give original squared excess `1+b^2` and transformed squared excess `1+b^(2p)`. Taking `b=e^(-L), p=L^(-2)` gives ratio tending to two. The norm-relative ratio is that squared-excess ratio multiplied by `(sqrt(1+(1+b^2)/N)+1)/(sqrt(1+(1+b^(2p))/N)+1)`, which tends to one as `N=L` tends to infinity.
- The power integral is convergent for `0<p<1`; for each `t>0`, inverse order reversal makes `I-t(X+tI)^(-1)` order preserving. Positive integration and spectral calculus establish operator monotonicity, including singular PSD inputs. The sharpness therefore occurs inside the operator-monotone subclass, even though the proof uses only scalar hypotheses.

## Source comparison and status recommendation

[Persson, Meyer, and Musco, arXiv v2](https://arxiv.org/html/2311.14023v2) was read directly, especially Eq. (2), Table 1, Theorem 2.5 and Section 5. The source uses the trace-deficit Frobenius premise for its operator-monotone theorem; the ordered concave cell is open there. Its specified truncation uses the same leading eigenvectors. The submitted result extends the function class and weakens that premise.

**Recommended canonical status: Resolved**, with the resolution explicitly attributed to Matthew J. Colbrook's submitted manuscript and this independent proof audit. No proof or canonical problem text was edited in this review. No publication, exhaustive novelty search, or community acceptance is certified.
