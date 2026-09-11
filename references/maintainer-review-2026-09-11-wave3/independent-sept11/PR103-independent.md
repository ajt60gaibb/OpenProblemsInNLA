# PR #103 — independent adversarial mathematical audit

Date: 2026-09-11. Frozen head: `6f5861fa392db467dc23abd096a02a08573146b8` (read from the supplied `REVIEW-HEAD.txt`; no digest was computed).

**Verdict: the displayed proof establishes the canonical RA-10 implication with universal constant 11. No mathematical revision is required by this audit.** This is an independently reconstructed mathematical review, not a formal proof or an assertion of priority or optimality. The submitted PASS labels were not used as evidence.

## Scope and exact locations

All repository material read was inside `/private/tmp/nla-review-wave3-artifacts/pr-103`. The principal files were:

- `randomized-and-low-rank-approximation/RA-10/README.md`, especially lines 35–56: canonical quantifiers and selected-eigenvector convention.
- `references/stepaniants-ra10-2026-09-11/original-canonical-README.md`, lines 23–44: the prior target, unchanged in mathematical content.
- `randomized-and-low-rank-approximation/RA-10/solution.md`, lines 17–352: complete theorem and proof.
- `randomized-and-low-rank-approximation/RA-10/solution.tex`, lines 57–489: the corresponding theorem and proof. Its substantive formulas and hypotheses agree with the Markdown.

Locations below use `solution.md` unless otherwise specified. The audit did not modify the snapshot or main checkout, execute submission code, run workflows, publish comments, or merge anything. No numerical experiment was needed: the decisive estimates admit direct algebraic verification. A separately delegated reader independently rederived only Lemma 2 and also found no gap; the full argument below was checked directly by this reviewer.

## 1. Canonical target and assumptions

Theorem 1, lines 21–34 (TeX 68–90), retains every canonical input: arbitrary finite `n >= 2`, `1 <= k < n`, real symmetric PSD `A` and `Ahat`, every allowed ordered eigenbasis of `Ahat`, every continuous nonnegative operator-monotone function on the full nonnegative half-line, and every finite nonnegative epsilon. It adds no Loewner relation between the pair. The proof in fact works for every PSD `B=PBP` with a prescribed rank-k projection and its ordered nonnegative eigenvalues, a class containing every canonical truncation.

The selected projection is part of the data (lines 19, 250 and 352). It is never replaced by `range(B)` when B is rank deficient. The final identity `f(B)_P = f(Ahat)_k` consequently remains valid for zero selected eigenvalues and for arbitrary choices inside tied eigenspaces. Monotonicity in scalar dimension ensures that the ordered eigenvalues of `f(A)` are `f(a_i)`, including ties and constant functions; nonnegativity ensures that their sum after k is the nuclear-norm optimum. No normalization such as `f(0)=0` or `f(1)=1` is imposed on the final function. Scalar concavity by itself is not substituted for operator monotonicity anywhere.

## 2. Novel compression estimate: all steps verified

Lemma 2, lines 48–157 (TeX 110–240), requires only `A >= 0`, an orthogonal rank-k projection, and positive s,c. It does not assume that the compression has any eigenvalues of A or that `C=PAP <= A`.

For invertible H, PSD of A gives the Schur-complement inequality `F >= E^T H^{-1} E`. The eigenvalue bound `0 < lambda < 1` at line 72 is valid: `Z=f_s(C)-f_s(A) <= f_s(C) < I`. Thus `mu=lambda/(1+lambda)` is strictly between 0 and 1/2, so every denominator and subsequent sign is legitimate.

Starting from the resolvent eigenvector equation, I obtain its upper block as

\[
(1+\lambda)Ew=-\lambda(sI+H)u.
\]

The lower block, after division by `1+lambda`, uses the identity

\[
(1-\mu)s(sI+H)^{-1}+\mu I
=(sI+\mu H)(sI+H)^{-1}.
\]

These give exactly (2) and (3), lines 87–91. Substitution in the lower-block quadratic form proves (4). Combining (4) with the Schur complement gives

\[
1\le 2(1-\mu)\|u\|^2-\mu s u^TH^{-1}u
\le 2(1-\mu)\|u\|^2,
\]

which is precisely the claimed lower bound (5), not an upper bound.

For `D=[[0,-E],[-E^T,-F]]`, direct substitution gives

\[
v^TDv=\mu s+\mu(2-\mu)u^THu.
\]

With `Delta=(cI-H)_+`, the inequality `H >= cI-Delta` is valid eigenvalue by eigenvalue. After using (5), the scalar difference from `lambda(s+c)/2` is

\[
\frac{\mu\{s(1-2\mu)+c(1-\mu)\}}{2(1-\mu)}\ge0.
\]

Thus (7), lines 129–145, has the correct direction and constants.

In summing (7), the positive eigenvectors are orthonormal in the full space, and their P-components satisfy `sum u_j u_j^T <= I_k`. They need not themselves be orthonormal. The weights `mu_j(2-mu_j)` lie in (0,1), so the weighted Delta contribution is at most `tr Delta`. Also `tr(QD) <= tr(D_+)` follows from the variational characterization for every projection Q; positivity of D or commutation with Q is unnecessary. These facts prove (1) with its factor 2.

For singular H, line 157 regularizes both matrices by the same `rP`. This preserves `C_r=PA_rP`, PSD, and `C_r-A_r=D`, while making the restricted H positive definite. For fixed positive s, resolvents and positive-part traces are continuous. The limit therefore proves the original inequality, including H=0, without assuming a uniform inverse bound on H. No limiting division by c or s occurs in this step.

## 3. Isospectral replacement and the constant 11

Lines 161–245 (TeX 245–342) use `tau>0` only to ensure `c=a_k>0`. This implication is valid because a positive tail contains a positive eigenvalue after k. The auxiliary B0 may have arbitrary eigenvectors in the chosen subspace; it is not assumed to commute with A or H.

Compression min-max gives `h_i <= a_i` and hence `L >= 0`. Pinching is contraction in nuclear norm: it is the average of a matrix and its conjugate by the orthogonal involution `2P-I`. The complementary block is PSD with trace `tau+L`. Therefore its pinched norm is exactly `R+tau+L`, proving `e0 >= R+L` at (8). There is no subtraction of a possibly negative complementary trace.

The trace identity yields `e_C=L+2 tr((C-A)_+)`, and `d <= L` follows termwise from `h_i<=a_i` and `a_i>=c`. The scalar identity in (12) is exact, including b=0, and its upper bound follows from `s/(s+b)<=1` and `1/(s+a)<=1/(s+c)`. Consequently `L_s<=gL`.

Combining the compression lemma with these identities gives exactly

\[
\|f_s(A)-f_s(C)\|_*-\tau_s
\le g(2e_C+3L).
\]

The noncommuting resolvent calculation (14) is performed on `range(P)`. The two inverse operator norms there are bounded by `1/(s+c)` and `1/s`. The product inequality for the nuclear norm therefore gives `gR`. On the orthogonal complement both ridge functions are zero. One must not use `B0 >= cI` on the full space; the submitted proof explicitly avoids that error (lines 225–235).

The scalar bookkeeping is then

\[
2e_C+3L+R\le2e_0+3R+3L\le5e_0.
\]

For arbitrary selected B, lines 250–281 (TeX 348–389) correctly align B0 with the actual selected eigenvectors. The sorted eigenvalues of B are the selected `b_1,...,b_k` followed by zeros, even when some selected values vanish. The eigenvalue perturbation bound therefore gives `r+tau <= ||A-B||_*`. Its short proof at lines 262–269 is valid: `U=X+J_-=Y+J_+` dominates both X and Y; min-max and the trace identity give the stated bound, with no simultaneous diagonalization assumption.

Thus `r<=e(B)`, `e0<=e(B)+r`, and the commuting comparison of B0 with B gives a further `gr`. Their combination is

\[
\|f_s(A)-f_s(B)\|_*-\tau_s
\le 5g(e+r)+gr\le11ge.
\]

Every tail eigenvalue is at most c, so `tau_s >= g tau`, with the direction required for a relative error bound. Therefore `e<=epsilon tau` implies the ridge estimate with the same 11 for every positive s. No dimension-, rank-, function-, gap-, or conditioning-dependent constant remains.

## 4. Integral representation and source applicability

I checked [Chansangiam, arXiv:1304.7936v1, Proposition 1.1, printed page 2](https://arxiv.org/pdf/1304.7936v1). It supplies a finite positive measure on the compactified half-line for continuous nonnegative operator-monotone functions, without requiring normalization. Splitting endpoint atoms and weighting its interior measure by `1+s` gives exactly (22) and its integrability condition at lines 313–319 (TeX 423–443). No coefficient has the wrong sign.

Realification is valid: the map `X+iY -> [[X,-Y],[Y,X]]` preserves products, adjoints, spectral functional calculus, and PSD. Monotonicity for every real symmetric size consequently gives the complex matrix hypothesis. If operator monotonicity is defined on arbitrary Hilbert spaces, the usual finite-matrix/all-operator equivalence follows here by compressing bounded positive operators to finite-dimensional subspaces, extending them by zero, and using strong convergence plus continuous functional calculus on a common bounded spectral interval. Thus the source's convention introduces no additional hypothesis.

The spectral integrals in lines 321–335 converge in nuclear norm: the integrals of the traces of each positive integrand are finite sums of finite scalar integrals. The difference integrand is absolutely integrable by the triangle inequality. Hence the passage from atomwise inequalities to the function is valid even for an interior measure of infinite total mass. Positivity of the measure is essential and is provided by the theorem.

The exact decomposition uses `alpha(I-P)`, not `alpha I`, in the error; its nuclear norm is `alpha(n-k)`. The target tail decomposes into exactly the same constant contribution, the linear tail, and the ridge tails. The coefficient of the linear error is bounded by `1+epsilon <= 1+11epsilon`. The constant component already has optimal error. This proves lines 338–342 without assuming that matrix differences for different atoms have aligned signs.

I also checked [Persson–Meyer–Musco, arXiv:2311.14023v2, §1.2 and Example 5.3 with the closing paragraph of §5](https://arxiv.org/html/2311.14023v2). The fixed-loss question and the limitation of its constant-one counterexample agree with the canonical historical framing. Their ordered theorem is not used as a premise of the new proof. The separate commuting lower bound 2 is likewise unnecessary for establishing 11; its manuscript is not in this frozen snapshot and was not independently audited here.

## 5. Endpoints and an exact diagnostic case

- **Zero original tail:** lines 346–352 (TeX 477–489) are correct. The hypothesis forces A=B. Since A is supported on P, the residual is exactly `f(0)(I-P)`, whose norm equals the optimal transformed tail. This covers every epsilon, including zero.
- **Singular B with positive original tail:** the proof does not invert B. Its only positive lower bound belongs to the auxiliary B0 on the selected subspace, and the ridge denominators for B remain positive because s>0.
- **Zero transformed tail:** the proof never divides by it. The positive integral-tail identity remains valid and forces the corresponding error bound to zero. In particular f identically zero presents no exception.
- **Ties and selected zeros:** retain the given P throughout. No spectral gap or unique truncation is required. The choice of A's top-k eigenvectors does not affect either nuclear tail.

For a concrete simultaneous endpoint test, take `n=3`, `k=2`, `A=Ahat=diag(2,0,0)`, and choose P onto `span(e1,u)`, where u is any unit vector in `span(e2,e3)`. Take `f(x)=1+sqrt(x)`. Then the input tail is zero and the hypothesis holds with epsilon=0, including the selected zero eigenvalue. For a unit w orthogonal to u in the zero eigenspace,

\[
f(A)-f(\widehat A)_2=ww^T,
\qquad \|ww^T\|_*=1=\|f(A)-f(A)_2\|_*.
\]

This confirms explicitly why retaining P, instead of replacing it with the support of B, is necessary; the submitted proof does retain it.

## Conclusion

Every dependency of the constant-11 theorem has been checked at the stated scope. The novel compression lemma is valid, its singular limit is legitimate, the spectral replacement produces the claimed dimension-independent coefficient, and the positive-measure reduction covers the full canonical function class and all required endpoints. I found no counterexample, omitted assumption, circular dependency, or weakening of the canonical target. This report supports the mathematical resolution claim for this frozen head only; it makes no assertion about later revisions or the sharp constant.
