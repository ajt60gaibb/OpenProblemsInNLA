# SP-04 independent agent proof review

**Verdict: PASS — full negative resolution of the exact displayed README target, including algebraic genericity.**

**Review date:** 11 September 2026.  
**Reviewer:** separate Codex review agent `/root/review_counterexamples`.  
**Canonical target:** `eigenvalues-and-inverse-problems/SP-04/README.md`, “Original problem statement”.  
**Manuscript:** `eigenvalues-and-inverse-problems/SP-04/solution.md`, Theorem SP-04 and sections 1–4.

This is an independent agent audit of the complete mathematical argument, not a rerun of the submitted diagnostic script. It is not external human peer review or a formal proof certificate. The reviewer did not edit the manuscript, the problem statement, status metadata, diagnostic code, or remotes.

## Reviewed proof identity

The hashed block starts at the first `## Theorem ` and ends immediately before `## Scope and review notes`. Line endings were normalized to LF, leading and trailing whitespace stripped, and the resulting text encoded as UTF-8 without a BOM.

- SHA-256: `77b6c6240eab1eab1cd7f9326a95a4bb7455188f951c11718c1b8c07cf691d95`
- UTF-8 length: 4,714 bytes.

The verdict applies to this proof block and the canonical mathematical target read on the review date. Notices outside the block are not mathematical premises of the review.

## Exact target and conclusion

The target considers every real stationary pair

\[
|\det X|=1,\qquad X^T(U-X)=cI,
\]

and asks whether choosing the pair with minimum $|c|$ gives a globally nearest matrix in Frobenius norm, for algebraically generic real data and every $n\geq2$. Both determinant signs are allowed. The manuscript proves failure in dimension three, with a unique minimizing multiplier and stationary pair, throughout the nonempty open set of matrices whose singular values are distinct and lie in $(7/4,44/25)$. This suffices to refute a statement required to hold outside some proper real algebraic exceptional set.

As a source cross-check, Problem 4.3 on published page 186 of [Baaijens–Draisma](https://pure.tue.nl/ws/files/3846347/391917266748824.pdf) asks the smallest-absolute-real-root question for the group allowing both determinant signs. The local README is the canonical target for this verdict; correspondence with an elimination polynomial is not needed for the stationary-pair formulation proved here.

## Complete proof checks

Fix $U=\operatorname{diag}(s_1,s_2,s_3)$ with $7/4<s_1<s_2<s_3<44/25$.

### 1. Reduction of every stationary matrix

Since $|\det X|=1$, $X$ is invertible. Put $S=X^TX$, which is positive definite. Direct multiplication of the stationary equation gives

\[
U=X+cX^{-T}=X(I+cS^{-1}),\qquad
U^TU=S+2cI+c^2S^{-1}.
\]

The right side commutes with $S$, so $S$ commutes with the diagonal matrix $U^TU=\operatorname{diag}(s_i^2)$. Since its diagonal entries are distinct, the commutator equation gives $(s_i^2-s_j^2)S_{ij}=0$; hence every off-diagonal entry of $S$ vanishes. The diagonal factor $I+cS^{-1}$ is invertible because $U$ and $X$ are invertible. Thus $X=U(I+cS^{-1})^{-1}$ is diagonal as well. Positivity of that factor is not assumed, so negative diagonal entries of $X$ are retained.

Writing $X=\operatorname{diag}(x_i)$, the stationary conditions are equivalent to

\[
x_i^2-s_ix_i+c=0\quad(i=1,2,3),\qquad |x_1x_2x_3|=1.
\]

This is a reduction of all real stationary matrices, not merely a search inside diagonal candidates. Conversely, any root choice with absolute product one gives an admissible stationary pair.

### 2. All nonnegative-multiplier branches

At $c=0$, each $x_i$ is either zero or $s_i$. Invertibility excludes zero, leaving $X=U$, but $s_1s_2s_3>(7/4)^3=343/64>1$. Thus $c=0$ is impossible.

For $c>0$, real roots can exist only if $c\leq s_1^2/4$. Their product is $c>0$ and sum is $s_i>0$, so both roots are positive. For $0<c\leq13/25$, define the large roots

\[
r_i=\frac{s_i+\sqrt{s_i^2-4c}}2,
\]

and the small roots $c/r_i$. The discriminants are strictly positive. The manuscript's numerical constants are exact terminating decimals and satisfy the following rational checks:

\[
s^2-4c\geq\frac{49}{16}-\frac{52}{25}
=\frac{393}{400}=0.9825
>\left(\frac{99}{100}\right)^2.
\]

Consequently $r_i>137/100>1$, while $r_i\leq s_i<44/25$. Also

\[
\frac{\partial r}{\partial s}
=\frac12\left(1+\frac{s}{\sqrt{s^2-4c}}\right)
<\frac12\left(1+\frac{176}{99}\right)
=\frac{275}{198}<2.
\]

The width of the singular-value interval is $44/25-7/4=1/100$. The mean value theorem therefore gives $r_{\max}-r_{\min}<1/50$. Since $r_{\min}>1$,

\[
\frac{r_{\max}}{r_{\min}}<\frac{51}{50}.
\]

Among the eight large/small root selections, the all-large selection has product greater than one. Any other selection can be increased by replacing all but one of its small roots by their large partners. The product of a selection with just the $i$-th root small is

\[
\frac{c}{r_i}\prod_{j\ne i}r_j
\leq c\frac{r_{\max}^2}{r_{\min}}
<\frac{13}{25}\frac{44}{25}\frac{51}{50}
=\frac{14586}{15625}=0.933504<1.
\]

This checks all eight selections and proves that no stationary pair has $0\leq c\leq13/25$. Positive multipliers above $13/25$, whether or not they exist or have repeated quadratic roots, cannot compete with the negative multiplier of smaller absolute value constructed below. Multipliers above $s_1^2/4$ give no real diagonal root choice at all. No positive branch is omitted from the comparison required by the target.

### 3. All negative-multiplier branches and uniqueness

Write $c=-t$, $t>0$, and define positive quantities

\[
a_i(t)=\frac{s_i+\sqrt{s_i^2+4t}}2,\qquad
b_i(t)=\frac{t}{a_i(t)}=\frac{\sqrt{s_i^2+4t}-s_i}{2}.
\]

The two roots are $a_i$ and $-b_i$. Both $a_i$ and $b_i$ are strictly increasing in $t$; their derivatives are $1/\sqrt{s_i^2+4t}>0$. Thus each product of three chosen absolute roots is strictly increasing. The all-positive pattern has product $\prod a_i>\prod s_i>1$ for every $t>0$, so it is never feasible.

For the pattern negative only at index one, the absolute determinant is $g(t)=b_1a_2a_3$. It is continuous, strictly increasing, and tends to zero as $t\downarrow0$. At $t=13/25$, the defining polynomial $f_i(a)=a^2-s_i a-13/25$ satisfies

\[
f_i(2)<4-2(7/4)-13/25=-1/50<0.
\]

As $f_i$ has exactly one positive root, $a_i>2$. Further,

\[
\left(\frac14\right)^2+s_1\frac14
<\frac1{16}+\frac{11}{25}
=\frac{201}{400}<\frac{208}{400}=\frac{13}{25}.
\]

The function $b\mapsto b^2+s_1b$ is strictly increasing for $b\geq0$, so $b_1>1/4$. Therefore $g(13/25)>(1/4)\cdot2\cdot2=1$. The intermediate value theorem and strict monotonicity establish a unique $t_*\in(0,13/25)$ with $g(t_*)=1$.

To compare every other negative pattern, let $E$ be its nonempty set of negative indices. Its absolute determinant is

\[
P_E(t)=a_1a_2a_3\prod_{i\in E}q_i(t),\qquad
q_i(t)=t/a_i(t)^2.
\]

Since $a_i^2=s_i a_i+t$ and $s_i,a_i>0$, every ratio lies strictly between zero and one. Strict ordering $s_1<s_2<s_3$ implies $a_1<a_2<a_3$, hence $q_1>q_2>q_3$. Among the seven nonempty subsets, the product of the ratios is uniquely maximal for $E=\{1\}$: another singleton gives a smaller ratio, and every additional factor strictly decreases a product already bounded by $q_1$.

Each $P_E$ is a product of increasing $a_i$'s and $b_i$'s, so it is strictly increasing. As $t\downarrow0$, it tends to zero; as $t\to\infty$, every absolute root is asymptotic to $\sqrt t$, so $P_E(t)\sim t^{3/2}\to\infty$. Every nonempty pattern therefore reaches absolute determinant one exactly once. At $t=t_*$, every pattern except $E=\{1\}$ has product strictly below one, so all six others reach one at strictly larger $t$.

This accounts for all eight negative-multiplier root patterns, proves that $c_*=-t_*$ is the uniquely least absolute multiplier among them, and proves uniqueness of its stationary matrix. Combining with the complete nonnegative comparison proves uniqueness among all real stationary pairs. Both determinant signs have been included throughout.

### 4. Feasible improvement and failure of nearestness

The selected entries are $x_1=-b_1<0$, $x_2=a_2>0$, $x_3=a_3>0$, and their product is exactly $-1$ by $g(t_*)=1$. Replacing $x_1$ by $b_1$ changes the determinant to $+1$, still within the target constraint. It changes no other coordinate and decreases the squared Frobenius distance by

\[
(s_1+b_1)^2-(s_1-b_1)^2=4s_1b_1>0.
\]

Thus the selected pair is feasible and stationary but not globally nearest. The improving matrix need not itself be stationary. A nearest matrix does exist: the nonempty constraint $(\det X)^2=1$ is closed, and the squared distance is coercive, so its minimum is attained. No unproved identification of that minimizer is needed for the strict counterexample.

### 5. Open set and the algebraic-generic condition

For an SVD $U=P\operatorname{diag}(s)Q^T$, the map $X\mapsto Y=P^TXQ$ is invertible and preserves absolute determinant and Frobenius distance. Direct multiplication gives

\[
Y^T(\operatorname{diag}(s)-Y)
=Q^TX^T(U-X)Q.
\]

It therefore bijects the full stationary-pair sets and preserves each scalar multiplier, including uniqueness of the least $|c|$. This proves the same failure for every matrix whose three distinct singular values belong to $(7/4,44/25)$, regardless of the signs of the orthogonal factors' determinants.

That set is nonempty, as shown by the rational diagonal example in the manuscript. It is open in the full nine-dimensional real matrix space: singular values are continuous, and membership is specified by strict interval and separation inequalities. Every such matrix is invertible and has distinct squared singular values.

A nonzero real polynomial cannot vanish on a nonempty Euclidean open set, so a proper real algebraic subset has empty Euclidean interior. Consequently no proper algebraic exceptional set can contain all these failures. If one also removes the generic exception needed for finiteness of the stationary set or one-to-one elimination-root correspondence, the union of finitely many proper algebraic exceptions is still proper and still cannot contain this open set. The proof therefore answers the algebraic-generic target, rather than merely supplying exceptional diagonal data. Explicit enumeration of all positive stationary roots is unnecessary for this conclusion.

## Independent numerical cross-check, not a premise of PASS

For $s=(1751,1755,1759)/1000$, I separately bisected each of the seven monotone negative-pattern product equations, without running or reusing the supplied diagnostic script. The approximate crossing values are:

| Negative indices | Positive value $t=-c$ at absolute determinant one |
| --- | ---: |
| $\{1\}$ | 0.497407247775782 |
| $\{2\}$ | 0.499002502558308 |
| $\{3\}$ | 0.500598294523252 |
| $\{1,2\}$ | 1.547059643427816 |
| $\{1,3\}$ | 1.549333929008705 |
| $\{2,3\}$ | 1.551611226340274 |
| $\{1,2,3\}$ | 2.754999336171652 |

The selected entries are approximately $(-0.248736406534,2.003294607278,2.006854202447)$, and the squared distance is approximately $4.12202761329034$. The identity has exact squared distance

\[
(751^2+755^2+759^2)/10^6=1710107/10^6=1.710107.
\]

These values agree with the manuscript but are illustrative checks only. The exact branch comparisons and strict inequalities above supply the proof.

## Adversarial checks and limitations

I specifically checked for off-diagonal stationary matrices, singular factors in the reduction, zero roots at $c=0$, negative roots for positive $c$, root collisions at the positive discriminant boundary, omitted negative patterns, ties of minimum absolute multiplier, failure of determinant feasibility after sign replacement, orientation restrictions in the SVD, and the possibility that the examples lie entirely in a proper algebraic exceptional set. The proof addresses each issue. No material gap or false intermediate claim was found.

The PASS verdict applies to the absolute-determinant constraint and the exact generic stationary-pair selection rule in the README. It does not establish a claim about projection restricted to determinant $+1$, identify every global minimizer, or assert that every multiplier elsewhere in the open set is distinct. It makes no claim of novelty, publication, or priority and is not an exhaustive literature review. This is separate-agent mathematical review, not external human peer review or formal certification.
