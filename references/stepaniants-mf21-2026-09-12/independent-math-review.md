# MF-21 independent mathematical review

Reviewer: separate Codex agent `/root/prepare_manuscripts`.
Date: 12 September 2026.

**Verdict: PASS for the complete canonical three-part target, for every integer $m\ge3$. No mathematical correction is required in the reviewed version.**

## Exact input and independence

I independently read the complete manuscript preserved as [reviewed-candidate.md](reviewed-candidate.md), 19,393 bytes, SHA-256 `98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5`. Its source was the author's frozen `RESULT.md`. I did not author, rewrite, or contribute a proof route to that manuscript. I first checked the canonical target and primary literature, and then reviewed the frozen argument in full. The source snapshot has not been changed.

The canonical input is [canonical-target.md](canonical-target.md), 4,518 bytes, SHA-256 `1aac38ed3c7a83dfc3dddb4beeec26fcf117f23f5789b2a374c1332ba4cf359f`. Its complete target is addressed: the same real continuous coefficient functions, the exact sampling points $j\pi/(n+2)$, all eigenvalue indices at orders through $2m-1$, the stated logarithmic-square cutoff at order $2m$, and failure of the latter error estimate uniformly over all indices. The manuscript proves smoothness of the coefficient functions, which is stronger than the requested continuity.

This is an independent AI mathematical audit. It is not external human peer review, a Lean or other formal certificate, or an unconditional priority/openness certification.

## 1. Stable roots and smooth endpoint phases

For $\omega_\ell\ne1$, a unit-circle root of $2-r-r^{-1}=\omega_\ell(2-2\cos\theta)$ is impossible at $0<\theta\le\pi$: the left-hand side is real and belongs to $[0,4]$, whereas the right-hand side is either nonreal or strictly negative. The reciprocal quadratic therefore has one root inside the circle and one outside. Its discriminant can vanish only when the right-hand side is $0$ or $4$, which excludes this interval.

The expansion $r_\ell=1-\kappa_\ell\theta+O(\theta^2)$ has the correct sign and branch, since $-\kappa_\ell^2=\omega_\ell$ and $\Re\kappa_\ell>0$. Factoring a single $\theta$ from the discriminant's square root gives a smooth, indeed analytic, one-sided extension at zero. Compactness then supplies a common positive decay constant for all finitely many stable roots and bounded logarithmic derivatives.

Each factor $1-r_\ell e^{-i\theta}$ has positive real part for positive $\theta$, so the chosen argument is unambiguous. Dividing it by $\theta$ near zero gives the nonzero limit $\kappa_\ell+i$, whose argument is $\pi\ell/(2m)$. The resulting sum is $(m-1)\pi/4$. At $\pi$, conjugate pairing of the stable roots cancels the arguments; a possible real root is positive and causes no phase jump. Thus $\eta(0)=(m-1)\pi/2$ and $\eta(\pi)=\pi$ are correct. The endpoint regularity needed by the coefficient construction is established.

## 2. Boundary determinant, phase orientation, and remainder

The bandwidth-$m$ recurrence has nonzero outer coefficients. Its zero ghost indices are $1-m,\ldots,0$ and $n+1,\ldots,n+m$. Translating them by $m-1$ gives exactly the row exponents $0,\ldots,m-1$ and $n+m,\ldots,n+2m-1$ in equation (13). For $0<\theta<\pi$ the characteristic roots are distinct, so they span the recurrence solutions. Restriction to the interior identifies the boundary kernel with the finite eigenvector kernel; injectivity follows from the consecutive-zero uniqueness of the recurrence. There is no missing boundary condition or finite-section correction.

I independently expanded the two dominant Laplace terms. With the inherited column order, their signs are opposite. The term selecting $z$ and all exterior roots contains

$$
V(R)V(O)Qz^{-(m-1)}\overline f^{,2},
$$

and the other contains the negative of $V(R)V(O)Qz^{m-1}f^2$, up to their common sign. Including the bottom-row powers leaves $z^{n+1}\overline f^{,2}-z^{-(n+1)}f^2$. This is precisely the phase $(n+1)\theta-2\psi(\theta)$ used by the manuscript; in particular, its sign and the shift $n+2$ are correct.

Every other size-$m$ subset omits an exterior root or includes an interior root beyond a dominant choice. Its normalized modulus is therefore at most the largest stable-root modulus. The normalized coefficient functions are uniformly bounded with bounded derivatives: at zero all $2m$ root slopes are distinct, so each numerator has vanishing order $m(m-1)$. The denominator has the same order, from the two stable/exterior Vandermondes and $|f|^2$, with nonzero leading coefficient. No extra negative power of $\theta$ remains. At $\pi$ the denominator remains nonzero even though the two oscillatory columns coincide.

Consequently the finite Laplace sum gives the claimed exponential bound for $E_n$ and the additional factor $n+1$ in its derivative. Conjugation permutes the stable and exterior lists by the same permutation and swaps the two unit roots. Hence both the determinant and its normalizer are purely imaginary, and their quotient, and thus $E_n$, is real. Finally the coincident columns at $\pi$ imply $E_n(\pi)=0$. Integrating its derivative proves the stronger upper-endpoint bound (12). These estimates are uniform in $n$ and $\theta$ for each fixed $m$.

## 3. Eigenvalue indexing and both spectral edges

The quadratic-form argument puts all $n$ eigenvalues strictly inside $(0,4^m)$. For sufficiently large $n$, the phase derivative is positive and comparable to $n+2$. Choosing one fixed large $J$ makes the remainder and its derivative small throughout the region whose phase is at least $J\pi-\pi/4$.

Each phase interval around $k\pi$, $J\le k\le n$, then contains exactly one simple zero. The derivative argument also proves simplicity of the matrix eigenvalue: a boundary matrix of nullity at least two has zero derivative of its determinant, which would contradict that zero's simplicity. Symmetry of the Toeplitz matrix equates algebraic and geometric multiplicity.

There are no roots in the intervening gaps. The final interval near $(n+1)\pi$ must not be treated by a uniform absolute-error estimate alone. The manuscript instead compares $|\sin F_n(\theta)|$ with $(n+2)(\pi-\theta)$ and uses the corresponding vanishing factor in (12). That correctly excludes every interior root of this last interval despite the artificial determinant zero at $\theta=\pi$. Counting from the top therefore identifies the zero near $k\pi$ as the $k$-th eigenangle without an unsupported assumption about the lowest eigenvalues.

The resulting angle error is $O((n+2)^{-1}e^{-cj})$. The implicit root used in this comparison is inside $(0,\pi)$ for $J\le j\le n$, even though the abstract smooth implicit-function construction uses an extension outside the closed interval.

I also checked the separate circulant estimate. Taking size $N=n+2m$ prevents any bandwidth-$m$ coefficient from wrapping into the leading $n\times n$ block. The sorted circulant eigenvalues are indeed indexed by $\lfloor j/2\rfloor$, for both odd and even $N$. Interlacing gives (21), and $\lfloor j/2\rfloor\ge j/3$ for all integers $j\ge2$ yields the stated lower bound (22). The missing lower bound at $j=1$ is not used prematurely.

## 4. The common coefficient family and the first two conclusions

The compact-interval implicit-function theorem provides one smooth $Y(x,h)$ with $Y(x,0)=x$. Taylor coefficients of $g(Y)$ depend only on the jets of $g$ and $\eta$ along the original interval, so they are independent of the chosen extension. Their endpoint vanishing estimate $d_k(x)=O(x^{2m-k})$ follows from the chain rule and the order-$2m$ zero of $g$; all other factors remain bounded.

For $j\ge J$, multiplying the exponentially small angle error by the bound for $g'$ gives $O(h^{2m}j^{2m-1}e^{-cj})$, uniformly up to the largest index. For the finitely many $j<J$, interlacing and the coefficient vanishing estimates give the required $O(h^{2m})$ bound directly. This proves the global order-$2m-1$ estimate. Removing the bounded higher-order terms gives every lower order with the same coefficients.

For $j\ge\lceil(\log(1/h))^2\rceil$, the exponential dominates the polynomial factor uniformly and supplies one more power of $h$. Taylor's theorem at order $2m$ therefore proves precisely the canonical second assertion. All constants may depend on the fixed $m$, as allowed; no uniformity in $m\to\infty$ is claimed or needed.

## 5. External kernel theorem and the trace contradiction

I opened and read [Böttcher–Widom, arXiv:math/0412269v1](https://arxiv.org/pdf/math/0412269), §2 on printed pages 3–4. The paragraph immediately preceding (13) explicitly states the $L^\infty([0,1]^2)$ convergence of the scaled step kernel for $T_n(|1-t|^{2\alpha})^{-1}$, with the same ceiling-index convention. It covers every positive integer $\alpha$ and in particular $\alpha=m$, with multiplier $b=1$. Formula (5), printed page 2, and the stated reflection symmetry give the exact Green kernel used here. Thus the manuscript invokes the stronger kernel convergence actually stated by the source, rather than inferring it from the distinct operator-norm convergence in (12).

Essential-uniform convergence does control the diagonal in this situation. On each open grid square the approximating kernel is constant; continuity of the limiting kernel extends the essential bound to its closure. Restricting to diagonal squares and integrating gives $n^{-2m}\operatorname{tr}(A_n^{-1})\to\int G_m(x,x)\,dx$. Replacing $n$ by $n+2$ in this scalar normalization multiplies by a factor tending to one.

I recomputed the substitution in the diagonal kernel. It gives $x^{2m-1}(1-x)^{2m-1}/((2m-1)((m-1)!)^2)$; the beta integral gives the positive rational number in (29). This conclusion does not require a trace-continuity claim for arbitrary operator-norm convergence.

Under the hypothetical global order-$2m$ error estimate, the fixed-index limit is $\pi^{2m}(j+(m-1)/2)^{2m}$: the implicit equation supplies the shift from $\eta(0)$, and $g(t)/t^{2m}\to1$. Equation (22) gives a summable bound $C_mj^{-2m}$ on the rescaled inverse eigenvalues for $j\ge2$. For $j=1$, the positive hypothetical fixed-index limit gives eventual boundedness. Extending the sequence by zero for $j>n$ therefore justifies dominated convergence for the entire trace.

For odd $m\ge3$, the resulting zeta tail omits at least the positive rational term $1$. For even $m\ge4$, the half-integer tail omits a nonempty finite set of positive rational terms. In both cases Euler's even-zeta identity leaves a rational number minus a nonzero rational multiple of $\pi^{-2m}$. Transcendence of $\pi$ makes that value irrational, contradicting the rational trace limit. The indexing of both finite subtractions in (32)–(33) is correct. This proves the third assertion for the constructed common coefficient family and completes the exact target.

## 6. Supplementary exact checks and limitations

I independently wrote [exact_algebra_check.py](exact_algebra_check.py); its output is [exact-algebra-output.json](exact-algebra-output.json). It binds execution to the reviewed source hash. Exact Gaussian rational arithmetic checks the full boundary Laplace expansion, both dominant coefficient formulas, phase orientation, and conjugation identity in ten cases ($m=2,\ldots,6$, $n=1,5$). Twelve exact rational checks confirm the diagonal beta-integral constant for $m=1,\ldots,12$. All checks passed.

These finite checks verify algebraic transcription, not the all-$m$ theorem. Their rational stable-root lists need not solve the Toeplitz characteristic equation; the general characteristic-root, uniform-error, indexing, and limit arguments were audited analytically above. No floating-point experiment or unchecked numerical theorem is a premise of the verdict.

The [source/scope audit](source-scope-review.md) records prior credit and the limits of the bounded literature search, including the latest Rambour version. This mathematical PASS does not certify absence of a new public solution after that search. A final publication conversion must separately preserve the reviewed mathematical substance and canonical target. The frozen draft contains a few plain-text mathematical delimiters needing typesetting cleanup; that is an editorial matter and does not alter any inference checked here. No candidate source or repository file was edited during this audit.

Signed electronically by the separate Codex reviewing agent `/root/prepare_manuscripts`, 12 September 2026.
