# Selected-block extension: exact implementation contracts

Prepared by the source-statement author for independent review before new estimates. The source is Urschel v1, Section 5.3, Lemma 5.4. This implements B4 in `full-proof-specification.md`, preserving the original IE-06 target. The fixed outside-row candidate is the already reviewed zero-mask/fallback construction; no rectangular elimination or measurable singular-vector selector is assumed.

## Public target and proposed module boundaries

For the actual canonical selected block
`T t A = selectedBlock ht (pivotOrder ht A) A`, prove, for every real $\beta\ge1$, that there is $C_\beta>0$ such that for natural $m,k,d,n$ with
$m+4k\le n$, $k<m$, $16\le d$, $100d\le k$, and $0<\mu<\sqrt k$,

$$
\gamma_n\left\{A:\ \mu\le\sigma_{m-k}(T_m),\quad
 \Sigma_k(T_m)\le2k\mu^{-2},\quad
 \sigma_{m+4k-d}(T_{m+4k})\le
 \frac{\mu d}{k}e^{-C_\beta(1+k\log n/d^2)}\right\}
 \le e^{-\beta\log n}.
$$

The right side is `ENNReal.ofReal (exp (-β * log n))`; since the dimension assumptions imply $n>0$, it is exactly $n^{-\beta}$. Source singular value $\sigma_i$ is implemented by descending zero-based `Spectral.singularValue _ (i-1)`. The event uses `TruncatedInverse.sigmaInvSum` with its existing full positivity guards. There is no extra event, Gaussian-law premise, full-rank hypothesis, or conditioning hypothesis in this final statement.

Proposed owned files are `GaussianCandidateRows.lean` (fixed outside-row law and candidate factorization), `SpectralMeasurability.lean` (actual spectral-event measurability and fixed kernel frame), `GaussianStackingTail.lean` (fixed-matrix probabilistic stacking), `SelectedBlockExtension.lean` (actual B4), and a separate scalar file if needed. Root's `GaussianColumnSplit.lean` supplies fresh-column splitting, so this work does not duplicate that infrastructure.

## Fixed outside-row coordinates and fibers

For a fixed $S\subseteq[n]$ with $|S|=s$ and $m+s\le n$, choose its deterministic increasing enumeration $e_S:[s]\hookrightarrow[n]$. Write $Z$ for all coordinates of all original rows outside $S$, and $B=G_{e_S,[m+s]}$. Their joint law is exactly

$$
 \left(\bigotimes_{i\notin S}\gamma_n\right)\otimes\gamma_{s\times(m+s)}.
$$

The ignored trailing coordinates of rows in $S$ are integrated out. The actual outside-only candidate labels `candidateLabels S hm` factor measurably through $Z$. Thus the candidate block $M(Z)=G_{\pi_m^S,[m+s]}$ is a measurable function of $Z$ alone. This is an unconditional product-coordinate identity. In particular $B$ remains iid Gaussian in a fixed $Z$ fiber. We never condition on $S$ being the next actual pivot set.

For measurable $M(Z)$, an intrinsic measurable bad event $E(M,B)$, and a measurable good predicate $H(M)$, the fixed-fiber estimate
$\gamma_{s\times(m+s)}\{B:H(M)\land E(M,B)\}\le\varepsilon$ for every fixed $M$
integrates to the same bound for $(M(Z),B)$. Any orthonormal nullspace frame is chosen only after $M$ is fixed, and is eliminated from the public bad event. Therefore no measurability of that choice is needed.

## Fixed-matrix stacking bound

Let $M\in\mathbb R^{m\times(m+s)}$ have full row rank, let $4\le j<s$, $2j<s$, and $j<m$. Let $a>0$, $f\ge0$ satisfy $\|M^\dagger\|_2\le a$ and $\|M^\dagger\|_F\le f$. For $x>0$ and $0<\theta\le1$, set

$$
 u=16f+\left(16\sqrt s+\sqrt{\frac{2x}{j+1}}\right)a,
 \qquad \ell=\frac{j\theta}{4e\sqrt s},
 \qquad R=\frac12\left(a+\frac{1+u}{\ell}\right)^{-1}.
$$

For actual iid Gaussian $B\in\mathbb R^{s\times(m+s)}$,

$$
 \Pr\left\{\sigma_{m+s-2j}\begin{pmatrix}M\\B\end{pmatrix}\le R\right\}
 \le e^{-x}+s^{j+1}\theta^{j^2/4}.
$$

Proof: choose a fixed orthonormal frame $Q$ of $\ker M$. A1' gives $\sigma_{j+1}(BM^\dagger)\le u$ outside a set of mass $e^{-x}$. Fixed orthonormal compression gives the exact iid $s\times s$ law of $BQ$, so A3 gives $\sigma_{s-j}(BQ)>\ell$ outside a set of mass $s^{j+1}\theta^{j^2/4}$. A6 then gives a lower bound at least $2R>R$. The factor $1/2$ makes the non-strict public lower-tail event unambiguous; it is absorbed into the final constant. No independence of the two bad events is claimed or needed.

The measurable event can be expressed intrinsically through singular values. On the full-row-rank locus, the pseudoinverse equals $M^T(MM^T)^{-1}$, a measurable rational function. If a total measurable representative is needed outside that locus, use this explicit Gram-inverse expression and only identify it with the spectral pseudoinverse under the full-rank guard. The guard itself is measurable by the Gram determinant. Singular-value continuity/measurability must be proved from the existing min-max theory; it is not silently assumed.

## Numerical choices and absorption

Put $s=4k$, $j=\lfloor d/2\rfloor$, $\lambda=\log n$, $z=k\lambda/d^2$, and let

$$
 C_A=2+98316e^2,\quad x_0=(\beta+1)\lambda,\quad
 a=\sqrt{C_A}\,\mu^{-1}e^{x_0/k},\quad f=\sqrt k\,a,
$$

$$
 x=(4k+\beta+1)\lambda,\quad D_\beta=64(\beta+6),\quad
 \theta=e^{-D_\beta(1+z)}.
$$

The reviewed A5 bound has failure $2e^{-x_0}$ and simultaneously supplies $\|M^\dagger\|_2\le a$, $\|M^\dagger\|_F\le f$ for the actual first $m$ selected rows, appended by the next $s$ fresh columns. This cost is paid once. Full row rank follows from nonsingularity of the selected $T_m$ (or directly from its retained positive-rank decomposition and fresh Gaussian columns); it is not inferred from a finite pseudoinverse norm.

The dimension assumptions imply $k\ge1600$, $n>5k$, $\lambda>0$, $d/3\le j$, $2j\le d$, and $j+1\ge d/2$. The following exact inequalities are sufficient and are to be proved symbolically:

1. $s^{j+1}\theta^{j^2/4}\le e^{-x}$. Indeed $\log s\le\lambda$ and $(j+1+s+\beta+1)\lambda\le(\beta+6)k\lambda$, while $j^2/4\ge d^2/36$ and $64/36>1$.
2. $u\le50\sqrt{C_A}(\sqrt k/\mu)e^{(2\beta+6)z}$. Use $x\le(\beta+5)k\lambda$, $j+1\ge d/2$, and $2\sqrt r\le1+r\le e^r$ for $r\ge0$. Also $\lambda/k,\lambda/d\le z$.
3. $\ell\ge[d/(24e\sqrt k)]e^{-D_\beta(1+z)}$.

Define fixed positive constants

$$
 H=1+\sqrt{C_A}+24e(1+50\sqrt{C_A}),\qquad
 C_\beta=D_\beta+2\beta+6+\log(2H)+1.
$$

Then the denominator in $R$ is at most
$H[k/(\mu d)]e^{(D_\beta+2\beta+6)(1+z)}$, and hence

$$
 \frac{\mu d}{k}e^{-C_\beta(1+z)}\le R.
$$

Every constant is dimension-independent; $C_\beta>0$. These are deliberately coarse symbolic estimates. There is no large numerical computation or alteration of the target rate.

## Actual selected-block transfer and accounting

On the Gaussian full-measure nonsingular set, take $S$ to be the set of the next $s$ original pivot rows. The first $m$ labels avoid $S$, so F5 identifies the outside-only candidate with the actual first $m$ labels. Stacking this candidate with the fixed enumeration of $S$ differs from the actual selected $(m+s)$ block by a row permutation only; singular values are equal. Since $2j\le d$, descending singular-value monotonicity transfers the stacking lower bound to index $m+s-d$.

There are at most $n^s$ sets $S$ of cardinal $s$. The total failure is at most

$$
 2e^{-x_0}+2n^se^{-x}=4e^{-(\beta+1)\lambda}
 \le e^{-\beta\lambda},
$$

because $n\ge4$. The event does not condition on later pivot success. All rank, row-permutation, event-measurability, null-set, and finite counting bridges must be proved. This document is a contract, not a claim that those bridges have already been implemented.
