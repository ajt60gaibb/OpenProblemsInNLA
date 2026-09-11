# Independent agent proof review: KE-03

**Verdict: PASS.** The complete theorem and proof in the identified proof block establish the exact target displayed in `eigenvalues-and-inverse-problems/KE-03/README.md`. I found no mathematical gap or counterexample within that target. This verdict is an independent agent review, not external human peer review or formal certification.

**Review date:** 11 September 2026.  
**Reviewer:** A separate Codex review agent assigned to audit KE-03.  
**Inputs examined:** The canonical problem statement in `eigenvalues-and-inverse-problems/KE-03/README.md` and the complete theorem, algorithm, and proof in `eigenvalues-and-inverse-problems/KE-03/solution.md`. I did not use prior review conclusions or numerical diagnostics as evidence.

## Exact proof identity

The reviewed block starts at the first `## Theorem ` heading and ends immediately before `## Scope and review notes`. Normalize CRLF and CR line endings to LF, strip leading and trailing whitespace from the extracted block, and encode it as UTF-8 without a byte-order mark.

- **SHA-256:** `4e39a133710ce5a49f6f0f179046431fee98f1226ba1f53a2a7d9ad1e813194c`
- **Normalized UTF-8 length:** 6,528 bytes.

The verdict attaches to this block. Changes to author metadata or review notices outside it do not change the reviewed proof. A changed proof block requires a fresh check of the changes.

## Scope and quantifiers

For every fixed diagonalizable complex matrix of positive spectral radius, every supplied finite bound K at least one for the condition number of some diagonalizing eigenvector matrix, and every epsilon strictly between zero and one half, the proof constructs a randomized algorithm using only exact products v -> Av. The algorithm returns a complex number z such that, with probability at least 0.997, one and the same eigenvalue mu satisfies both

\[
|\mu|\ge (1-\varepsilon)\rho(A),\qquad
|z-\mu|\le\varepsilon\rho(A).
\]

The query count is bounded by a universal constant times epsilon to the power minus two times \(1+\log(nK)\). Thus the target's exponents can be taken as a = 1 and b = 2, and its probability requirement of 0.99 is exceeded.

The eigenvector matrix is fixed only for the analysis; the algorithm does not require it or the eigenvalues. The probability assertion is uniform over fixed admissible inputs, as the target requests. It does not concern an oracle that chooses its matrix after seeing the algorithm's random sample. Repeated eigenvalues, absence of a spectral gap, and arbitrary arguments of the complex eigenvalues are permitted.

## 1. Finite sampling and complex anti-concentration

An integer N with N at least 1000n and N+1 a power of two exists and can be found by repeated doubling. Each sampled coordinate is exactly uniform on the N+1 rational grid points and uses a fixed finite number of unbiased random bits. Coordinates can be sampled independently. The construction does not require continuous randomness.

Fix a nonzero row w of the inverse eigenvector matrix. Some coordinate c = w_j has absolute value at least the Euclidean row norm divided by the square root of n. Conditional on all the other sampled coordinates, write the row product as ct+d, where t is the remaining real sampled coordinate. For

\[
\tau=\frac{\|w\|_2}{1000n^2},
\]

the real set defined by \(|ct+d|<\tau\) is empty or an interval of length at most \(2\tau/|c|\). To see that this is valid even when c and d are complex, the map t -> ct+d traces a line in the complex plane at speed |c|, and a disk of radius tau has every chord of length at most 2 tau. Thus the admissible interval has length at most

\[
\frac{2}{1000n^{3/2}}.
\]

Intersecting with the sampling interval [0,1] can only reduce its length. An interval of length ell contains at most N ell + 1 grid points. Therefore its conditional probability is at most

\[
\frac{N\ell+1}{N+1}
\le\ell+\frac{1}{N+1}
\le\frac{3}{1000n}.
\]

Here \(n^{3/2}\ge n\) and \(N+1\ge1000n\). The same bound holds unconditionally. The bad event uses a strict inequality, so its complement supplies the weak lower bound needed in the proof, including possible equality at a grid point. A union bound over n rows gives total bad probability at most 0.003. Independence between the different row events is unnecessary.

The identity \(w_iV=e_i^T\) gives \(1\le\|w_i\|_2\|V\|_2\), also for complex rows: the induced norm of the linear functional x -> w_i x is its Euclidean row norm. Consequently every eigenbasis coordinate of the sampled b has absolute value at least \(1/(1000n^2\|V\|_2)\) on the same event. Row or column phases and the arbitrary global scaling of V do not invalidate this estimate.

## 2. The estimate is simultaneous over all polynomials

Let c = V inverse times b. For any polynomial p, including one selected after observing the queries,

\[
\|p(A)b\|_2
\ge\frac{\|p(\Lambda)c\|_2}{\|V^{-1}\|_2}
\ge\frac{\max_i|p(\lambda_i)|}
 {1000n^2\|V\|_2\|V^{-1}\|_2}
\ge F^{-1}\max_i|p(\lambda_i)|.
\]

The first inequality follows by applying V inverse to p(A)b; the second uses the coordinate attaining the largest polynomial value and the lower bound that holds for every coordinate. The deterministic upper bound is

\[
\|p(A)b\|_2
\le\|V\|_2\|V^{-1}\|_2\|b\|_2\max_i|p(\lambda_i)|
\le K\sqrt n\max_i|p(\lambda_i)|
\le F\max_i|p(\lambda_i)|.
\]

The event is expressed entirely in terms of the eigenbasis coordinates of b. On that event, these deterministic inequalities apply to every polynomial without a union bound over polynomial degrees, coefficients, or later choices. This resolves the potential dependence of the chosen radius and shifts on the same stored Krylov sequence. A polynomial vanishing on the whole spectrum has p(A) = 0 by diagonalizability, so that degenerate case also satisfies both inequalities. Repeated eigenvalues cause no difficulty.

## 3. Query phase and radius approximation

With \(\eta=\varepsilon^2/1024\), one has \(0<\eta<1/4096\). Also F is at least 1000, so the selected m is a positive integer. Its defining inequality implies \(F^{1/m}\le1+\eta\). Substituting \(p(x)=(x+s)^m\) into the simultaneous estimate and taking m-th roots for analysis gives

\[
(1+\eta)^{-1}R_s\le q_s\le(1+\eta)R_s
\]

for every complex s, including a data-dependent s. If R_s is zero, both sides force q_s = 0 and the same statement holds.

The sequence b, Ab, ..., A to the power m times b requires exactly m forward products. The binomial formula for \((A+sI)^mb\) is valid because A commutes with sI. Every later shifted vector is a finite linear combination of already known vectors. There is no hidden shifted-system query, adjoint product, or additional application of A.

The stated multiplicative approximation to q_0 yields

\[
(1+\eta)^{-2}\rho\le r\le(1+\eta)^2\rho.
\]

On the success event, q_0 is strictly positive since rho is positive. The zero-norm exit therefore only occurs outside that event and does not reduce the claimed success probability. I checked the exact implementation of the positive approximation separately below.

## 4. Unit-circle coverage and the selection rule

The rational parametrization

\[
u(t)=\frac{1-t^2+2it}{1+t^2},\qquad -1\le t\le1,
\]

has modulus exactly one and parametrizes the right semicircle from -i to i. Its negative parametrizes the other semicircle. The endpoints are included, so there is no missing junction. Direct differentiation gives \(|u'(t)|=2/(1+t^2)\le2\).

For an explicit uniform mesh, take the first positive integer M with \(2/M\le\varepsilon/8\), and use \(t_j=-1+2j/M\) for j = 0, ..., M. Its spacing h is at most epsilon/8, and every parameter is within h/2 of a mesh point. The derivative bound gives chordal distance at most h, as required. The number of points after including the negative semicircle is at most 2(M+1), which is O(1/epsilon). All points have rational real and imaginary parts, and denominators are positive.

The algorithm maximizes the squared norm over this finite net. Since m is positive, squared norms and the quantities q_s have the same ordering. Exact comparisons suffice, and every maximizing index, including any choice in a tie, satisfies the inequality used next.

## 5. Location geometry and constants

Choose an eigenvalue mu_* of modulus rho. This exists because the spectrum is a finite nonempty set, and rho > 0 makes its normalized direction well-defined. For a net point u_* within epsilon/8 of that direction, the exact identity

\[
|\mu_*+ru_*|^2
=(\rho+r)^2-\rho r\left|\frac{\mu_*}{\rho}-u_*\right|^2
\]

gives the stated lower bound for \(R_{ru_*}^2\). If z is the selected shift, the chain

\[
(1+\eta)R_z\ge q_z\ge q_{ru_*}
\ge(1+\eta)^{-1}R_{ru_*}
\]

proves the claimed comparison of the two shifted spectral radii.

Now choose an eigenvalue mu attaining \(R_z=|\mu+z|\). This is the eigenvalue that will satisfy both output conditions; it need not equal mu_*. Set \(a=(1+\eta)^{-4}\). The parallelogram identity and \(|\mu|\le\rho\) give

\[
\begin{aligned}
|\mu-z|^2
&\le2(\rho^2+r^2)
-a\left((\rho+r)^2-\frac{\rho r\varepsilon^2}{64}\right)\\
&=(\rho-r)^2+(1-a)(\rho+r)^2
+a\frac{\rho r\varepsilon^2}{64}.
\end{aligned}
\]

All directions and signs are correct: maximizing the plus-shift radius favors an eigenvalue aligned with z, and the identity bounds its distance to z.

From the radius interval, the upper deviation is at most \((2\eta+\eta^2)\rho\le3\eta\rho\), and the lower deviation is at most \(2\eta\rho\), using \((1+\eta)^{-2}\ge1-2\eta\). Also r is at most 2 rho. Finally \(1-(1+\eta)^{-4}\le4\eta\), for example by the tangent inequality for the convex function \((1+x)^{-4}\). Hence the three terms are respectively bounded by \(9\eta^2\rho^2\), \(36\eta\rho^2\), and \(\varepsilon^2\rho^2/32\).

After dividing by epsilon squared times rho squared, their sum is strictly less than

\[
\frac{9}{4\cdot1024^2}+\frac{36}{1024}+\frac1{32}
=\frac{278537}{4194304}<\frac19.
\]

Thus the manuscript actually proves \(|z-\mu|<\varepsilon\rho/3\), stronger than the requested distance guarantee. For that same eigenvalue,

\[
|\mu|\ge r-|z-\mu|
\ge(1-2\eta-\varepsilon/3)\rho
\ge(1-\varepsilon)\rho.
\]

The last inequality follows since \(2\eta/\varepsilon=\varepsilon/512<1/1024<2/3\). The proof consequently supplies both conditions for a single eigenvalue, without a gap or a uniqueness assumption.

## 6. Finite exact arithmetic and termination

I interpret the displayed target's exact-arithmetic algorithm in the usual sense allowing exact comparisons and arithmetic on the supplied real parameters and on the real and imaginary parts returned by the oracle. This is the model explicitly used by the submitted algorithm. No stronger transcendental primitive is necessary.

The degree m can be found by repeated multiplication by 1+eta until the product reaches or exceeds F. Since eta is positive and F finite, termination follows; the first successful exponent equals the displayed ceiling even in an exact-equality case. N can be found by doubling, and the net size M by integer increments and comparisons. Both terminate. Binomial coefficients and all polynomial evaluations require only finite arithmetic for the resulting finite m and net.

Let \(S=\|A^mb\|_2^2\). It can be computed as a finite sum of squares of real and imaginary parts. If it is zero, the algorithm terminates immediately. Otherwise \(q_0=S^{1/(2m)}>0\). To bracket q_0, start from 1 and double or halve until adjacent positive powers of two bracket it, comparing a trial value x by evaluating \(x^{2m}\) against S. Positive finite q_0 guarantees a finite bracket; exact equality can either be returned directly or included as an endpoint.

For a positive bracket [L_0,U_0], ordinary bisection preserves \(0<L_0\le L\le q_0\le U\) and halves its width at each step. After finitely many steps its width is at most eta times L_0, which implies \(U\le(1+\eta)L\). Thus r = L satisfies

\[
q_0/(1+\eta)\le r\le q_0,
\]

which is at least as strong as the approximation requested in the proof. This establishes termination even for arbitrarily small or large positive S. It applies on unsuccessful random outcomes as well; no infinite loop is hidden outside the high-probability event.

The net has no zero denominators. Shift selection uses only squared norms, so it needs neither square roots nor m-th roots. Complex conjugation needed for a norm is implemented by negating an imaginary component; this does not apply the adjoint matrix. All of the intervening computations therefore fit the declared exact-arithmetic model. Their costs can be enormous, but no total-runtime, bit-complexity, or numerical-stability bound is requested.

## 7. Universal query bound

For the present range of eta, \(\log(1+\eta)\ge\eta/2\). Therefore

\[
m\le\frac{2\log F}{\eta}+1
=2048\varepsilon^{-2}\log F+1.
\]

As n and K are at least one,

\[
\log F=\log1000+2\log n+\log K
\le8[1+\log(nK)].
\]

For example, the universal constant C = 16385 bounds the m queries by \(C[1+\log(nK)]\varepsilon^{-2}\). There are no further queries in the radius computation, the net search, or the output. Early termination can only decrease this count. This proves the requested form for all admissible parameter values, including n = 1 and K = 1.

## Adversarial checks, gaps, and limits

I specifically checked complex eigenvector rows with unfavorable phases, finite-grid atoms and equality cases, repeated eigenvalues, scalar matrices, n = 1, K = 1, arbitrary spectral scale, zero shifted spectral radii, a zero sampled vector, adaptive polynomials, tied maximizing shifts, and epsilon approaching either endpoint of its allowed interval. None invalidates the proof. The zero-vector outcome is covered by the bounded bad event and the terminating zero-norm branch.

**Material gaps found:** None within the exact target. The assumptions that A is diagonalizable, rho is positive, and K is supplied are used and are present in the canonical statement. Exact comparisons and unrestricted finite arithmetic are essential to the model of the algorithm. Removing these assumptions, requiring a practical stable method, or asking for runtime or bit bounds would be a different problem.

This review establishes an agent's mathematical assessment of the complete supplied argument. It does not establish novelty or priority, verify literature claims, audit a numerical implementation, certify the separately rendered PDF or LaTeX against this source, or provide formal machine-checked proof or external human peer review. No manuscript, problem status, code, or remote state was changed by this reviewer; this report is the review artifact.
