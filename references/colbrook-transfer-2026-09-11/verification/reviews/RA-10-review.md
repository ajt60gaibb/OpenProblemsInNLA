# RA-10 independent proof review — 2026-09-11

**Verdict: PASS for the submitted commuting partial theorem; no resolution of the full canonical RA-10 target.** The complete Frobenius manuscript is mathematically sound, but its unordered result concerns the Frobenius norm. The separate commuting note proves a sharp nuclear bound in its simultaneous-eigenbasis setting. Neither proves a universal nuclear bound for arbitrary noncommuting PSD inputs. This is a scope limitation, not a material gap in the stated partial theorem.

## Reviewed input and identity

The complete original `manuscripts/02_frobenius_function_transfer.tex`, complete `manuscripts/common_preamble.tex`, and complete `research_notes/commuting_Schatten_factor_two.md` were read from `.cache/colbrook-transfer-submission/nla_submission/`. The full Frobenius proof audit is recorded in [RA-09-review.md](RA-09-review.md). Its scalar inequalities, matrix averaging, sharpness, zero cases and truncation conventions were checked independently, without treating submitted diagnostics as proof.

SHA256 means the complete original UTF-8 text with CRLF changed to LF, without trimming, other whitespace changes, or final-newline removal.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| `manuscripts/02_frobenius_function_transfer.tex` | 13326 | `b71d409a3fea3720a83380bdfddc2cd5cdcdbf2381deba445e79b56ed53ca4fa` |
| `manuscripts/common_preamble.tex` | 1105 | `8b784fe6ac56151b19d51534474560bf45df7b278015cd0c834569e2550fada4` |
| `research_notes/commuting_Schatten_factor_two.md` | 1890 | `1d6915105211c3a92184f9a28c9d9cb5d4d384213ecc9c482e2282418dfeaa42` |
| Reviewed standalone transcription `reviewed-sources/06_commuting_schatten_transfer.tex` | 6371 | `8c6e572e0a95b4ff198de3ed9403c007b90f51047f19ccbce3ebdebc3684dde8` |
| Canonical `randomized-and-low-rank-approximation/RA-10/README.md` before this update | 3576 | `393ee289b8875be95e88eb23ca453cb98d588407738ee36a44282ab29ee9750a` |

The complete standalone TeX transcription was also re-read after writing. **Transcription verdict: PASS.** It preserves the note's theorem and argument, makes the selected common projector explicit, expands the scalar arithmetic and exact sharpness limits, and includes the degenerate relative case and the already-reviewed power integral justification from the companion manuscript. These clarifications introduce no extension to arbitrary noncommuting matrices. Its empty author/date fields are intended for the root rendering workflow to supply the authorized byline and date externally; this hash identifies the full reviewed source before those presentation changes.

## Exact target and proved scope

Canonical RA-10 asks whether there is a single constant `C>=1`, independent of dimension, rank, matrices and function, for nuclear norm-relative transfer for all PSD `A,Ahat` and continuous nonnegative operator-monotone `f`. There is no ordering assumption, and every ordered eigendecomposition choice must be covered, using the same eigenvectors for `Ahat_k` and `f(Ahat)_k`.

The Frobenius theorem establishes factor two for the squared Frobenius excess and norm-relative Frobenius excess, even for noncommuting pairs. That result addresses a different norm and cannot resolve canonical RA-10. Norm equivalence incurs dimension factors and does not preserve this excess statement.

The commuting note fixes a common orthonormal eigenbasis of `A,B` and a set `S` of exactly k of those basis vectors supporting `B`. It defines `C` by retaining `f(b_i)` on S, including `f(0)` at padded zero entries. This is equivalently a setting where `A`, `B`, and the selected rank-k projector `P` are simultaneously diagonalizable. In that setting, the claimed inequality for every finite Schatten exponent `p>=1` is correct. In particular `p=1` gives the nuclear conclusion with constant two. Operator-monotone functions lie within the permitted scalar class.

When translating this to `B=Ahat_k`, retain the condition on the actual selected subspace. Merely saying that `A` commutes with `Ahat` does not ensure that every permitted truncation is diagonal in a common eigenbasis: choosing only part of a repeated eigenspace of `Ahat` may produce a projector that does not commute with A. For example, `A=diag(2,1)` and `Ahat=I` commute, but the rank-one truncation onto `(1,1)/sqrt(2)` does not commute with A. Zero padding introduces the same issue when `f(0)>0`. The note's specified-common-basis statement avoids this ambiguity.

## Independent audit of the commuting proof

Let `K={1,...,k}` index a decreasing eigenvalue list of A. Since A, B and the selected projector share the basis, the original excess is exactly

`delta_A = sum_(i in K) a_i^p - sum_(i in S) a_i^p + sum_(i in S) |a_i-b_i|^p = L_A+R_A`.

The transformed excess has the analogous decomposition `delta_f=L_f+R_f`. There is no matrix trace-power expansion being assumed here; simultaneous diagonalization makes the Schatten p-power the sum of scalar absolute p-powers.

Match indices in `S\K` to indices in `K\S`. Every matched omitted value `y` is at least tau and every selected lower value `x` is at most tau. Monotonicity gives nonnegative matched differences, and the bounds `f(y)<=cy` and `f(x)>=cx` give

`f(y)^p-f(x)^p <= c^p(y^p-x^p)`.

Thus `0<=L_f<=c^pL_A`. Also each omitted `y` is at least tau, so `L_A>=sum_(i in S)(tau^p-a_i^p)_+`. Eigenvalue ties at tau contribute zero and do not invalidate matching.

For the scalar error bound, if `max(a,b)>=tau`, the manuscript's scalar Lipschitz inequality immediately gives `|f(a)-f(b)|^p<=c^p|a-b|^p`.

If `0<b<=a<=tau` (also allowing `b=0` by continuity), put `q=1-b/a` when `a>0`. Subhomogeneity gives `f(a)-f(b)<=f(a)q<=c tau q`. The proposed scalar estimate follows since its right side minus `tau^p q^p` is exactly

`a^p q^p + tau^p-a^p - tau^p q^p = (tau^p-a^p)(1-q^p)>=0`.

If `0<=a<=b<=tau` and `b>0`, put `q=1-a/b`. Then `f(b)-f(a)<=c tau q`, and

`(tau^p-b^p)q^p <= tau^p-b^p <= tau^p-a^p`.

Since `|a-b|^p=b^p q^p`, this proves the other branch. At `a=b=0` the error is zero, and all inequalities are valid without division by zero. Thus the scalar claim holds for every nonnegative `a,b`:

`|f(a)-f(b)|^p <= c^p (|a-b|^p+(tau^p-a^p)_+)`.

Summing gives `R_f<=c^p(R_A+L_A)`, and hence

`delta_f <= c^p(R_A+2L_A) <= 2c^p delta_A`,

using `R_A>=0`. This verifies both the claimed coefficient and its dimension independence.

The tail comparison `c^p T_A<=T_f` follows entry by entry. Thus a p-th-power excess `eta` transfers with at most `2eta`. For norm excess, convexity of `t^p` on the nonnegative real line gives `(1+2epsilon)^p>=2(1+epsilon)^p-1`, proving the stated coefficient two, including `p=1`.

## Boundaries and optimality

The note states its scaled excess theorem only for `tau>0`. If `f(tau)=0`, the scalar assumptions force `f=0`, so the theorem is trivial. For `tau=0`, the relative-error premise forces `A=B`; the selected subspace contains the range of A. The remaining error has `n-k` singular values equal to `f(0)` and is the optimal tail. Thus the nuclear relative statement for this degenerate case is also valid, without introducing an undefined c.

The sharpness family is diagonal: `A=I_(N+1) directsum [0]`, `B=b` in the null coordinate, `k=1`, `f(x)=x^r`, with `0<b,r<1`. Its original p-power tail is N and its original excess is `1+b^p`; the transformed excess is `1+b^(pr)`. Their ratio tends to two, e.g. with `b=e^(-L), r=L^(-2)`. Taking `N=L` also gives norm-relative excess ratio tending to two, by the expansion `(1+x/N)^(1/p)-1 ~ x/(pN)` for bounded positive x. For `p=1` the ratio is already exactly the p-power ratio, so growing N is unnecessary.

The integral argument in the Frobenius manuscript independently verifies that every such power is operator monotone. Therefore the lower bound two applies to any possible universal constant in the full canonical RA-10 problem: a universal constant less than two is impossible even on this diagonal subclass. This lower bound does not prove that two, or any finite constant, suffices for noncommuting inputs.

## Source comparison and status recommendation

[Persson, Meyer, and Musco, arXiv v2](https://arxiv.org/html/2311.14023v2) was read directly: Theorem 2.4 supplies ordered nuclear transfer, Example 5.3 disproves loss one without ordering, and Section 1.2/Section 5 leave a larger fixed loss possible. The commuting theorem supplies an additional subclass and a stronger lower bound; it does not answer the missing noncommuting implication.

**Recommended canonical status: Partially resolved.** Add the sharp constant-two result for simultaneous eigenbasis truncations, and the necessary lower bound `C>=2` for any full solution. Preserve the full question about arbitrary unordered PSD pairs. The exact full target receives no PASS as a resolution. No proof or canonical text was edited during this review, and no publication or certification of priority is implied.
