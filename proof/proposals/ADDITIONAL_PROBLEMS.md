# Additional open-problem candidates for numerical linear algebra

**43 candidate entries | 15 core-NLA tags | 28 adjacent tags | Literature screening: September 8, 2026**

This is an **addition proposal**, not an automatically admitted extension of the supplied catalog. Its 72 existing entries were compared at **title/scope level only**: their linked full statements were not supplied. Existing IDs have not been changed.

**Status convention.** “No resolution located” reports targeted literature screening, not a certificate of openness. Recent proof claims were not independently audited. The screening log records several questions excluded or narrowed because of 2026 results.

**Statement provenance.** 37 entries restate explicit source questions; 4 are marked **Formalization** and 2 **Specialization**. Those six are precise editorial versions of source directions, not verbatim published conjectures. The core/adjacent labels are editorial filters. Known subcases and equivalent formulations are not counted as separate entries.

The notation $\|\cdot\|_2$, $\|\cdot\|_F$, and $\|\cdot\|_*$ denotes spectral, Frobenius, and nuclear norms. PSD means Hermitian positive semidefinite; SPD means symmetric positive definite. Unless specified otherwise, an algorithmic assertion is uniform over the displayed inputs.

[Browse the index](INDEX.md) · [Screening and exclusions](SCREENING_NOTES.md) · [Structured records](records.json)


## Krylov methods and eigenvalue algorithms

### ADD-001 — Precision needed for CG to terminate accurately in n steps

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For $A\in\mathbb R^{n\times n}$ SPD and $b\ne0$, determine the worst-case number of precision bits needed by standard floating-point CG, started at zero, to produce within $n$ iterations an $x$ satisfying
$$\frac{\|b-Ax\|_2}{\|A\|_2\|x\|_2+\|b\|_2}\le\varepsilon.$$
Make the dependence on $n$, $\kappa_2(A)$ and $\varepsilon$ explicit, under the standard relative-rounding model without underflow/overflow.

**Source location:** Problem 2.17.

- **[SIM]** [Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop](https://arxiv.org/html/2602.05394v3) (2026, v3).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** Different from IE-12: an iteration/precision question for CG, not the operation complexity of an arbitrary solver.

### ADD-002 — A stable O(nk) algorithm for the bidiagonal SVD

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For upper-bidiagonal $B\in\mathbb C^{n\times n}$, can $k$ triples $(\sigma_i,u_i,v_i)$ be computed in $O(nk)$ operations, with $\sigma_i\ge0$, unit vectors $u_i,v_i$, and
$$\|Bv_i-\sigma_i u_i\|_2=O(un\|B\|_2),\qquad |u_i^*u_j|,|v_i^*v_j|=O(un)\quad(i\ne j)?$$
Here $u$ is unit roundoff. This preserves the source’s stated one-sided residual requirement.

**Source location:** Problem 3.8.

- **[SIM]** [Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop](https://arxiv.org/html/2602.05394v3) (2026, v3).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-003 — All-future Ritz-value interlacing in block Lanczos

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Run exact block Lanczos on a real symmetric matrix, with block size $p$. Suppose the block Krylov spaces have full dimension through step $s$. Write the ordered eigenvalues of its $kp\times kp$ Jacobi matrix $T_k$ as $\theta_1^{(k)}\le\cdots\le\theta_{kp}^{(k)}$. Is
$$(\theta_i^{(k)},\theta_{i+p}^{(k)})\cap\sigma(T_j)\ne\varnothing$$
for every $k<j\le s$ and $1\le i\le(k-1)p$? The claim concerns every later step, not just $j=k+1$.

**Source location:** Section 2.1, conjecture following the adjacent-step interlacing inequalities.

- **[BL]** [On finite precision block Lanczos computations](https://arxiv.org/html/2507.16484v1) (2025).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-004 — Can rank deficiency cause exact DR-BCG to break down?

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For SPD $A\in\mathbb R^{n\times n}$ and $B,X_0\in\mathbb R^{n\times p}$, $1\le p\le n$, consider Algorithm 5 (DR-BCG) with fixed-width QR factors, retaining orthonormal completions when a QR input loses rank:
$$[W_0,\Sigma_0]=\operatorname{qr}(B-AX_0),\quad S_0=W_0,$$
$$\Xi_j=(S_j^TAS_j)^{-1},\quad [W_{j+1},Z_{j+1}]=\operatorname{qr}(W_j-AS_j\Xi_j),\quad S_{j+1}=W_{j+1}+S_jZ_{j+1}^T.$$
Must $S_j^TAS_j$ remain nonsingular at every required step before all systems are solved? Specify how the conclusion depends on the QR completion in rank-deficient cases. Here each $W_j$ has $p$ orthonormal columns; $A X=B$ is the system being solved.

**Source location:** Algorithm 5; Section 8, second open direction.

- **[BCG]** [Block CG algorithms revisited](https://arxiv.org/html/2502.16998v1) (2025).

**Status note:** Explicitly unresolved in the authors’ conclusion. The QR-completion convention is an important part of a rigorous formulation.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-005 — Higher-order gaps in randomized block Krylov bounds

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $A\in\mathbb R^{n\times d}$ have decreasing singular values $\sigma_i$. Fix $1\le b\le k<\ell$, put $t=\lceil\ell/b\rceil$, $m=bt\le\operatorname{rank}A$, and assume
$$g=\frac{\sigma_k^2-\sigma_\ell^2}{\sigma_k^2}>0,\qquad
\Delta_m^{(b)}=\min_{1\le i\le m-b}\frac{\sigma_i^2-\sigma_{i+b}^2}{\sigma_i^2}>0.$$
For an $n\times b$ standard Gaussian starting block $G$, let $Z$ span $\mathcal K_q(AA^T,G)$ orthonormally and return $\widehat A=Z(Z^TA)_k$. For $0<\varepsilon,\delta<1/2$, does
$$q=O\!\left(\frac{t}{\sqrt g}\log\frac{2}{\Delta_m^{(b)}}+
\frac{1}{\sqrt g}\log\frac{n}{\delta\varepsilon}\right)$$
suffice with probability at least $1-\delta$ for both Frobenius and spectral $(1+\varepsilon)$ relative rank-$k$ error and
$$\big|\|Av_i\|_2^2-\sigma_i^2\big|\le\varepsilon\sigma_k^2\quad(1\le i\le k),$$
where $v_i$ are the ordered right singular vectors of $\widehat A$? This is the gap-dependent instance of the authors’ conjecture replacing $\Delta_m/\kappa_m$ by $\Delta_m^{(b)}$; their analogous gap-independent and Krylov-conditioning claims are grouped with it, not counted separately.

**Source location:** Section 5; also Section 3.3.

- **[RBK]** [Does block size matter in randomized block Krylov low-rank approximation?](https://arxiv.org/html/2508.06486v1) (2025 arXiv identifier; retrieved HTML displays August 24, 2026).

**Status note:** The full gap-dependent instance is written out here. Section 5 conjectures the same higher-order-gap substitution in Theorems 1.3, 3.8 and 4.1.

**Overlap note:** No title-level duplicate identified in the uploaded index.


## Low-rank approximation and matrix functions

### ADD-006 — Concave-function spectral-error transfer

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $A\succeq\widehat A\succeq0$, and let $f:[0,\infty)\to[0,\infty)$ be continuous, concave and nondecreasing. Write $X_k$ for a rank-$k$ spectral truncation. Does
$$\|A-\widehat A_k\|_2\le(1+\varepsilon)\|A-A_k\|_2$$
imply
$$\|f(A)-f(\widehat A)_k\|_2\le(1+\varepsilon)\|f(A)-f(A)_k\|_2?$$

**Source location:** Table 1, operator-norm/concave/Loewner-order cell.

- **[NY]** [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2) (2024 arXiv revision; 2025 journal article).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-007 — Concave-function Frobenius-error transfer

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $A\succeq\widehat A\succeq0$ be equally sized Hermitian matrices, let $f:[0,\infty)\to[0,\infty)$ be continuous, concave and nondecreasing, and write $X_k$ for a rank-$k$ spectral truncation. For $\varepsilon\ge0$, does
$$\|A\|_F^2-\|\widehat A_k\|_F^2\le(1+\varepsilon)\|A-A_k\|_F^2$$
imply
$$\|f(A)-f(\widehat A)_k\|_F^2\le(1+\varepsilon)\|f(A)-f(A)_k\|_F^2?$$
The stronger premise is intentional: it is the premise of the operator-monotone theorem being extended.

**Source location:** Table 1, Frobenius/concave/Loewner-order cell; Theorem 2.5.

- **[NY]** [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2) (2024 arXiv revision; 2025 journal article).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-008 — Constant-loss nuclear-error transfer without Loewner ordering

**Scope:** Core NLA  
**Provenance:** Specialization  
**Screening date:** 2026-09-08

For continuous operator-monotone $f:[0,\infty)\to[0,\infty)$, and arbitrary PSD $A,\widehat A$, is there a universal $C$ such that
$$\|A-\widehat A_k\|_*\le(1+\varepsilon)\|A-A_k\|_*$$
implies
$$\|f(A)-f(\widehat A)_k\|_*\le(1+C\varepsilon)\|f(A)-f(A)_k\|_*?$$
No assumption $A\succeq\widehat A$ is made. Here $X_k$ denotes a rank-$k$ spectral truncation and $\varepsilon\ge0$.

**Source location:** Section 1.2, paragraph following the counterexamples.

- **[NY]** [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2) (2024 arXiv revision; 2025 journal article).

**Status note:** A precise nuclear-norm specialization of the authors’ broader constant-loss question. The source disproves C=1, not every constant C.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-009 — Minimax trace-estimation complexity with Kronecker queries

**Scope:** Core NLA  
**Provenance:** Formalization  
**Screening date:** 2026-09-08

An unknown PSD matrix $M\in\mathbb R^{n^q\times n^q}$ is accessible only through queries $Mv$ with $v=v_1\otimes\cdots\otimes v_q$, $v_i\in\mathbb R^n$. Determine, up to universal constant factors, the minimum number of possibly adaptive randomized queries that guarantees
$$\Pr\{|\widehat t-\operatorname{tr}M|\le\varepsilon\operatorname{tr}M\}\ge2/3$$
for every $M$. The dependence on $n,q,\varepsilon$ is part of the problem; arbitrary estimators, not only Hutchinson-type estimators, are permitted.

**Source location:** Section 6, tightness of Kronecker trace-estimation bounds.

- **[KR]** [Understanding the Kronecker Matrix-Vector Complexity of Linear Algebra](https://arxiv.org/html/2502.08029v1) (2025).

**Status note:** Minimax formulation of an explicit tight-complexity question. The paper’s separate projection conjecture is not imported because its quantifier ranges need care.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-010 — Audenaert’s norm-compression conjecture

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Partition $T$ into $2\times N$ equally sized square blocks $T_{ij}$ and set $C_p(T)=(\|T_{ij}\|_{S_p})_{i,j}$. Prove or disprove
$$\|C_p(T)\|_{S_p}\le\|T\|_{S_p}\quad(1\le p\le2),$$
with the inequality reversed for $p\ge2$. Here $\|\cdot\|_{S_p}$ is the Schatten $p$-norm. The unresolved ranges highlighted by the 2026 source are $1<p<2$ and $2<p<4$.

**Source location:** Original conjecture; 2026 Conjecture 1.14.

- **[NC]** [On a Norm Compression Inequality for 2 x N Partitioned Block Matrices](https://arxiv.org/html/math/0702186v2) (2007/2008).
- **[NC26]** [Clarkson–McCarthy type inequalities, part I: lp–lp and lq–lp Schatten p-estimates](https://arxiv.org/html/2410.21961v4) (2026, v4).

**Status note:** Do not confuse this with Hanner’s Schatten inequality, for which a 2026 proof is reported.

**Overlap note:** No title-level duplicate identified in the uploaded index.


## Tensor computations

### ADD-011 — Sharp best-rank-one approximation ratio for general tensor formats

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For a real tensor space $V=\mathbb R^{n_1\times\cdots\times n_d}$, $d\ge3$, determine a sharp dimension-dependent formula for
$$\tau(V)=\min_{0\ne T\in V}\frac{\|T\|_\sigma}{\|T\|_F},\qquad
\|T\|_\sigma=\max_{\|x_j\|_2=1}|\langle T,x_1\otimes\cdots\otimes x_d\rangle|.$$
The target is the optimal constant for general formats, not another non-sharp bound or a tensor-train approximation factor.

**Source location:** Section 5, extremal ratio.

- **[TAU]** [On norm compression inequalities for partitioned block tensors](https://doi.org/10.1007/s10092-020-0356-x) (2020).

**Status note:** An older explicit extremal problem. Known special formats must not be presented as new open cases.

**Overlap note:** Different from TR-04: rank-one spectral/Frobenius extremal constant, not fixed tensor-train rank quasi-optimality.

### ADD-012 — Border Comon conjecture

**Scope:** Adjacent: tensor algebra  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every complex symmetric tensor $T\in\operatorname{Sym}^d(\mathbb C^n)$, $d\ge3$, is
$$\underline{\operatorname{rank}}(T)=\underline{\operatorname{srank}}(T)?$$
The left side is the least $r$ for which $T$ is a limit of sums of $r$ arbitrary rank-one tensors; the right side restricts the approximants to sums of $r$ symmetric powers.

**Source location:** Introduction, general border Comon conjecture.

- **[COM]** [Symmetrization maps and minimal border rank Comon’s conjecture](https://arxiv.org/html/2411.05721v2) (2026, v2).

**Status note:** Still posed in the September 2026 revision. Ordinary Comon rank equality is false and is not the question here.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-013 — Gaussian type-2 bound for tensor injective norms

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Fix tensor order $r\ge2$ and $p\ge2$. For symmetric real order-$r$ tensors $T_i$ on $\mathbb R^d$ and independent $g_i\sim N(0,1)$, prove or disprove
$$\mathbb E\left\|\sum_{i=1}^N g_iT_i\right\|_{\mathcal I_p}
\le C_{r,p}d^{1/2-1/p}\log^{c_{r,p}}(2dN)
\left(\sum_i\|T_i\|_{\mathcal I_p}^2\right)^{1/2},$$
where $\|T\|_{\mathcal I_p}=\max_{\|x\|_p\le1}|\langle T,x^{\otimes r}\rangle|$. The constants may depend only on $r,p$.

**Source location:** Conjecture 16.

- **[TYPE]** [Tensor Concentration Inequalities (problem 16)](https://randomstrasse101.math.ethz.ch/posts/tensor-concentration/) (2025 author research post).

**Status note:** The full parameter range is the target; the cited post records substantial known ranges, including p >= 2r.

**Overlap note:** No title-level duplicate identified in the uploaded index.


## Random matrices, frames and sketching

### ADD-014 — Sharp Lovász-theta asymptotics for dense Erdős–Rényi graphs

**Scope:** Adjacent: random semidefinite programs  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $J$ be the all-ones matrix. Define
$$\vartheta(G)=\max\{\langle J,X\rangle:X\succeq0,\ \operatorname{tr}X=1,\ X_{ij}=0\text{ for }ij\in E(G)\}.$$
For $G\sim G(n,1/2)$, is $\mathbb E\vartheta(G)=(1+o(1))\sqrt n$?

**Source location:** Conjecture 17.

- **[THETA]** [The Lovasz number for random graphs (problems 17 and 18)](https://randomstrasse101.math.ethz.ch/posts/lovasz-circulant/) (2025 author research post).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-015 — Sharp Lovász-theta asymptotics for random circulant graphs

**Scope:** Adjacent: structured random semidefinite programs  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

On $\mathbb Z/n\mathbb Z$, independently select each unordered nonzero difference class $\{s,-s\}$ with probability $1/2$, and join $i,j$ when their difference class is selected. For this random graph, is
$$\mathbb E\vartheta(G)=(1+o(1))\sqrt n?$$
Here $\vartheta(G)=\max\{\langle J,X\rangle:X\succeq0,\ \operatorname{tr}X=1,\ X_{ij}=0\text{ for }ij\in E(G)\}$, with $J$ the all-ones matrix.

**Source location:** Conjecture 18.

- **[THETA]** [The Lovasz number for random graphs (problems 17 and 18)](https://randomstrasse101.math.ethz.ch/posts/lovasz-circulant/) (2025 author research post).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-016 — Vinzant’s limiting injectivity probability

**Scope:** Adjacent: phase retrieval and conditioning  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For $M\ge2$, let $A_M\in\mathbb C^{(4M-5)\times M}$ have iid standard complex Gaussian entries, and let $p_M$ be the probability that $x\bmod\mathbb T\mapsto|A_Mx|^2$ is injective on $\mathbb C^M/\mathbb T$. Prove or disprove
$$\lim_{M\to\infty}p_M=0.$$
The separate assertion $p_M<1$ is deliberately omitted. The scalar group $\mathbb T=\{z\in\mathbb C:|z|=1\}$ identifies vectors differing by a global phase.

**Source location:** Conjecture 19(b); Li (2026) for part (a).

- **[PHASE]** [Injectivity and Stability of Phase Retrieval (problems 19–21)](https://randomstrasse101.math.ethz.ch/posts/StablePhaseRetrieval/) (2025 author research post).
- **[VIN26]** [On Injectivity of Phase Retrieval](https://arxiv.org/abs/2606.17922) (2026).

**Status note:** Li’s June 2026 paper proves part (a). This entry retains only part (b); no resolution of that part was located.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-017 — Uniform exponential ill-conditioning at minimal real phase-retrieval redundancy

**Scope:** Adjacent: phase retrieval and conditioning  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For full-spark (every $M$-row submatrix nonsingular) $A\in\mathbb R^{(2M-1)\times M}$, define
$$\omega(A)=\min_{S\subseteq[2M-1],\ |S|=M}\sigma_{\min}(A_S).$$
Do universal $C>0$ and $0<\beta<1$ exist such that
$$\omega(A)\le C\,\max_i\|A_{i,:}\|_2\,\beta^M$$
for every $M>1$ and every such $A$?

**Source location:** Conjecture 20 (Balan–Wang).

- **[PHASE]** [Injectivity and Stability of Phase Retrieval (problems 19–21)](https://randomstrasse101.math.ethz.ch/posts/StablePhaseRetrieval/) (2025 author research post).

**Status note:** The Gaussian version now has a 2026 proof claim with exponential base 1/4. This deterministic, uniform assertion is different.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-018 — No complete set of mutually unbiased bases in dimension six

**Scope:** Adjacent: finite frame theory  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Prove or disprove that there are no seven orthonormal bases $\mathcal B_1,\ldots,\mathcal B_7$ of $\mathbb C^6$ satisfying
$$|\langle u,v\rangle|^2=1/6\quad\text{for }u\in\mathcal B_i,\ v\in\mathcal B_j,\ i\ne j.$$
This is the seven-basis nonexistence question, not the stronger assertion that the maximum is three.

**Source location:** Conjecture 22; 2026 review.

- **[FRAME]** [Mutually Unbiased Bases, ETFs, and Zauner’s Conjecture (problems 22–24)](https://randomstrasse101.math.ethz.ch/posts/FramesMUBZauner/) (2025 author research post).
- **[MUB26]** [Mutually Unbiased Bases in Composite Dimensions – A Review](https://quantum-journal.org/papers/q-2026-04-01-2051/) (2026).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-019 — Zauner’s SIC existence conjecture

**Scope:** Adjacent: finite frame theory  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every integer $d\ge2$, do there exist $d^2$ unit vectors $v_1,\ldots,v_{d^2}\in\mathbb C^d$ such that
$$|\langle v_i,v_j\rangle|^2=\frac1{d+1}\qquad(i\ne j)?$$
Only existence is required here, not the stronger additional symmetry assertions sometimes included under Zauner’s name.

**Source location:** Conjecture 24.

- **[FRAME]** [Mutually Unbiased Bases, ETFs, and Zauner’s Conjecture (problems 22–24)](https://randomstrasse101.math.ethz.ch/posts/FramesMUBZauner/) (2025 author research post).

**Status note:** Conditional constructions based on Stark-type conjectures are not unconditional resolutions.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-020 — Equiangular tight frames of redundancy two in every complex dimension

**Scope:** Adjacent: finite frame theory  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every $d\ge2$, do $2d$ unit vectors $v_i\in\mathbb C^d$ exist with
$$\sum_{i=1}^{2d}v_iv_i^*=2I_d,\qquad |\langle v_i,v_j\rangle|^2=\frac1{2d-1}\quad(i\ne j)?$$

**Source location:** Conjecture 1 (Fallon–Iverson).

- **[ETF]** [New constructions of optimal arrangements of 2d lines in C^d](https://arxiv.org/html/2608.16116v1) (2026).

**Status note:** Explicitly retained as a conjecture by the August 2026 construction paper. Distinct from the d^2-vector SIC question.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-021 — Paley ETF beyond square-root sparsity

**Scope:** Core NLA  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For prime $p\equiv1\pmod4$, let $Q$ be the real symmetric conference matrix indexed by $\mathbb F_p\cup\{\infty\}$: zero diagonal, $Q_{\infty,j}=Q_{j,\infty}=1$, and $Q_{ij}=\chi(i-j)$ on distinct finite indices, where $\chi$ is the quadratic character. Choose $F\in\mathbb R^{(p+1)/2\times(p+1)}$ with $F^*F=I+Q/\sqrt p$. Do there exist universal $\eta>0,C<\infty$ such that every submatrix formed from at most $\lfloor p^{1/2+\eta}\rfloor$ columns of $F$ has condition number at most $C$? Condition number means $\sigma_{\max}/\sigma_{\min}$, with infinity for rank deficiency.

**Source location:** Conjecture 29.

- **[PALEY]** [On the clique number of the Paley Graph (problems 25–29)](https://randomstrasse101.math.ethz.ch/posts/PaleyGraph/) (2025 author research post).

**Status note:** This is a question about this particular explicit frame, not the already achieved general weak breaking of the square-root bottleneck.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-022 — Optimal deterministic RIP matrices

**Scope:** Core NLA  
**Provenance:** Formalization  
**Screening date:** 2026-09-08

Is there a deterministic algorithm polynomial in $N$ that, for every $1\le k\le N/2$, constructs $\Phi\in\mathbb R^{m\times N}$, with polynomial-bit describable entries and $m\le Ck\log(eN/k)$, such that
$$\tfrac12\|x\|_2^2\le\|\Phi x\|_2^2\le\tfrac32\|x\|_2^2\quad\text{whenever }\|x\|_0\le k?$$
Here $C$ is universal.

**Source location:** Introduction, deterministic versus optimal randomized constructions.

- **[RIP]** [Satisfying the Restricted Isometry Property with the Optimal Number of Rows and Slightly Less Randomness](https://arxiv.org/html/2311.07889v2) (2024 revision; 2025 journal article).

**Status note:** Standard fixed-distortion formulation of the deterministic optimal-row-count problem. Rao’s result still uses randomness.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-023 — Optimal row count for a subsampled Walsh RIP matrix

**Scope:** Core NLA  
**Provenance:** Formalization  
**Screening date:** 2026-09-08

Let $N=2^d$, and let $H_N$ be the normalized Walsh matrix. Sample $m$ rows uniformly and independently, with replacement, and multiply the resulting matrix by $\sqrt{N/m}$. Let $m_*(N,k)$ be the least $m$ for which this matrix has $k$-RIP constant at most $1/2$ with probability at least $0.9$. Determine the order of $m_*(N,k)$, including the necessary logarithmic factors. Here $k$-RIP with constant $1/2$ means $\tfrac12\|x\|_2^2\le\|\Phi x\|_2^2\le\tfrac32\|x\|_2^2$ for every $k$-sparse $x$.

**Source location:** Main lower bound and remaining upper/lower-bound gap.

- **[WALSH]** [An Improved Lower Bound for Sparse Reconstruction from Subsampled Walsh Matrices](https://arxiv.org/abs/1903.12135) (2023 journal article).

**Status note:** The lower bound contains a log k factor beyond generic Gaussian RIP. This entry asks for the sharp threshold, not to remove a logarithm already known to be necessary.

**Overlap note:** Different from TR-01: uniform sparse-vector RIP for subsampled Walsh, not a rerandomized Hadamard subspace embedding.


## Matrix inequalities and inverse eigenvalues

### ADD-024 — Nobori’s strengthened three-factor commutator inequality

**Scope:** Adjacent: matrix inequalities  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For $A,C\in\mathbb C^{m\times n}$ and $B\in\mathbb C^{n\times m}$, $m,n\ge2$, prove or disprove
$$\|ABC-CBA\|_F^2\le2\|B\|_2^2\bigl(\sigma_1(A)^2+\sigma_2(A)^2\bigr)\|C\|_F^2.$$
The placement of the spectral norm on $B$ is essential.

**Source location:** Conjecture 3.1.

- **[NOB]** [A Generalization of the Böttcher–Wenzel inequality for three rectangular matrices](https://arxiv.org/html/2506.17365v2) (2025).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-025 — The fundamental Lu–Wenzel conjecture in spectral form

**Scope:** Adjacent: matrix inequalities  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For $X\in\mathbb C^{n\times n}$ with $\|X\|_F=1$, let $T_X(Y)=[X^*,[X,Y]]$ act on matrices with the Frobenius inner product. Write its eigenvalues in decreasing order. Is
$$\sum_{i=1}^{2k}\lambda_i(T_X)\le2k+2,\qquad 1\le k\le\lfloor n^2/2\rfloor?$$
The equivalent fundamental-commutator and majorization formulations are not counted separately.

**Source location:** Conjecture 4.14; Theorem 4.17.

- **[LW]** [A survey on the DDVV-type inequalities](https://arxiv.org/html/2402.01085v1) (2024).

**Status note:** The real restriction and the complex assertion are grouped as one problem family; normal, rank-one and small-order cases are known.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-026 — A sum-of-squares certificate for the Toeplitz commutator inequality

**Scope:** Adjacent: structured matrix inequalities  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every $n$, is the polynomial
$$2\|X\|_F^2\|Y\|_F^2-2|\langle X,Y\rangle_F|^2-\|XY-YX\|_F^2$$
a sum of squares of real quadratic polynomials in the $4n-2$ Toeplitz parameters of arbitrary real $n\times n$ Toeplitz matrices $X,Y$?

**Source location:** Conjecture 4.3.

- **[LW]** [A survey on the DDVV-type inequalities](https://arxiv.org/html/2402.01085v1) (2024).

**Status note:** The question is SOS representability, not merely the already established nonnegativity of the expression.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-027 — The symmetric nonnegative inverse eigenvalue problem in order five

**Scope:** Adjacent: inverse eigenvalue problems  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Give a complete effective spectral characterization of the set
$$\{(\lambda_1,\ldots,\lambda_5)\in\mathbb R^5:\lambda_1\ge\cdots\ge\lambda_5,\ \exists A=A^T\in\mathbb R^{5\times5},\ A_{ij}\ge0,\ \sigma(A)=\{\lambda_i\}_{i=1}^5\}.$$
The goal is explicit necessary-and-sufficient spectral conditions, not an existential formulation or a generic quantifier-elimination algorithm.

**Source location:** Introduction and remaining region in the conclusion.

- **[SNIEP]** [A New Impossibility Region for the 5 x 5 Symmetric Nonnegative Inverse Eigenvalue Problem](https://arxiv.org/html/2608.19435v1) (2026).

**Status note:** The August 2026 source excludes a new region but does not give a complete characterization.

**Overlap note:** Different from IS-02: realizability of arbitrary symmetric nonnegative spectra, not uniqueness of symmetric stochastic realizations.


## Permanents and determinants

### ADD-028 — Lieb’s permanent-dominance conjecture

**Scope:** Adjacent: matrix analysis  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every Hermitian PSD $A\in\mathbb C^{n\times n}$, subgroup $H\le S_n$, and nonzero character $\chi$ of $H$, is
$$\frac1{\chi(e)}\sum_{\sigma\in H}\chi(\sigma)\prod_{i=1}^n a_{i,\sigma(i)}\le\operatorname{per}A?$$

**Source location:** Permanent dominance (Lieb) conjecture.

- **[PER]** [An update on a few permanent conjectures](https://arxiv.org/html/1608.02844v1) (2016).

**Status note:** Do not substitute the false permanent-on-top or Bapat–Sunder conjectures.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-029 — Chollet’s permanent conjecture beyond the currently claimed small orders

**Scope:** Adjacent: matrix analysis  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For Hermitian PSD matrices $A,B\in\mathbb C^{n\times n}$, prove or disprove
$$\operatorname{per}(A\circ B)\le\operatorname{per}(A)\operatorname{per}(B).$$
Here $\circ$ is entrywise multiplication. The remaining all-dimension question includes $n\ge7$; a new preprint claims orders through six.

**Source location:** Chollet conjecture; August 2026 small-order claim.

- **[PER]** [An update on a few permanent conjectures](https://arxiv.org/html/1608.02844v1) (2016).
- **[CH26]** [Chollet’s Permanent Conjecture Through Order Six via Border Induction](https://www.preprints.org/manuscript/202608.2196) (2026 proof claim).

**Status note:** The through-order-six proof claim has not been independently audited here.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-030 — Marcus’s permanent-of-block-permanents inequality

**Scope:** Adjacent: matrix analysis  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $A\succeq0$ be an $mn\times mn$ complex matrix partitioned into $m\times m$ blocks $A_{ij}$ of size $n\times n$, and set $P=(\operatorname{per}A_{ij})_{i,j=1}^m$. Is
$$\operatorname{per}A\ge\operatorname{per}P$$
always true?

**Source location:** Marcus per-in-per conjecture.

- **[PER]** [An update on a few permanent conjectures](https://arxiv.org/html/1608.02844v1) (2016).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-031 — Maximum permanent on a positive semidefinite unitary orbit

**Scope:** Adjacent: matrix optimization  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Given $\lambda_1,\ldots,\lambda_n\ge0$, determine the exact value, as a function of this spectrum, of
$$\max_{U\in U(n)}\operatorname{per}\bigl(U^*\operatorname{diag}(\lambda_1,\ldots,\lambda_n)U\bigr).$$
An equal-diagonal optimizer must not be assumed.

**Source location:** Marcus–Minc maximization problem.

- **[PER]** [An update on a few permanent conjectures](https://arxiv.org/html/1608.02844v1) (2016).

**Status note:** The broad extremal problem remains; a formerly proposed equal-diagonal description is false.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-032 — Lih–Wang permanent convexity toward the flat matrix

**Scope:** Adjacent: stochastic matrices  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $A$ be an $n\times n$ doubly stochastic matrix and $J_n=\mathbf1\mathbf1^T/n$. For every $t\in[1/2,1]$, is
$$\operatorname{per}\bigl(tJ_n+(1-t)A\bigr)\le t\operatorname{per}J_n+(1-t)\operatorname{per}A?$$

**Source location:** Lih–Wang conjecture.

- **[LIH]** [Lih Wang and Dittert’s Conjectures on Permanents](https://arxiv.org/html/2312.00464) (2023/2024).
- **[PER]** [An update on a few permanent conjectures](https://arxiv.org/html/1608.02844v1) (2016).

**Status note:** Recent papers establish small-order cases; this is the general-dimensional statement.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-033 — The remaining low-dimensional Dittert inequalities

**Scope:** Adjacent: nonnegative matrices  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For $5\le n\le16$, let $A\in\mathbb R_+^{n\times n}$ satisfy $\sum_{ij}a_{ij}=n$, with row sums $r_i$ and column sums $c_j$. Prove or disprove
$$\prod_i r_i+\prod_j c_j-\operatorname{per}A\le2-\frac{n!}{n^n}.$$
These orders are grouped in one entry, not twelve.

**Source location:** Main large-dimension theorem and remaining small dimensions.

- **[DIT]** [Proof of Dittert’s conjecture for dimensions n >= 17](https://arxiv.org/html/2606.01531) (2026).

**Status note:** A June 2026 proof claims all n >= 17; order four also has recent claims. Only the displayed remaining range is included.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-034 — Marcus–de Oliveira determinantal conjecture

**Scope:** Adjacent: normal-matrix analysis  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For normal $A,B\in\mathbb C^{n\times n}$ with spectra $\{a_i\}$ and $\{b_i\}$, is
$$\det(A+B)\in\operatorname{conv}\left\{\prod_{i=1}^n(a_i+b_{\sigma(i)}):\sigma\in S_n\right\}?$$

**Source location:** Introduction, conjecture statement.

- **[MDO]** [Revisiting the Marcus–de Oliveira Conjecture](https://doi.org/10.3390/math13050711) (2025).

**Status note:** A 2025 review and 2026 partial-results literature continue to treat the general assertion as unresolved.

**Overlap note:** No title-level duplicate identified in the uploaded index.


## Discrepancy, explicit matrices and complexity

### ADD-035 — Komlós discrepancy conjecture

**Scope:** Adjacent: matrix discrepancy  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Does a universal $C$ exist such that every real $m\times n$ matrix with column Euclidean norms at most one has a signing $x\in\{-1,1\}^n$ satisfying
$$\|Ax\|_\infty\le C?$$

**Source location:** Introduction, Komlós conjecture.

- **[KOM]** [An Exposition of the O-tilde(log^(1/4) n) Bound for the Komlós Problem](https://arxiv.org/html/2608.28452v1) (2026).

**Status note:** An August 2026 paper improves the dimension-dependent bound; it does not establish a universal constant. Matrix Spencer is a different conjecture.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-036 — Beck–Fiala discrepancy conjecture

**Scope:** Adjacent: sparse matrix discrepancy  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every $A\in\{0,1\}^{m\times n}$ with at most $t$ nonzero entries in each column, does some $x\in\{-1,1\}^n$ satisfy
$$\|Ax\|_\infty\le C\sqrt t$$
with a universal $C$, independent of $m,n,t$?

**Source location:** Abstract and introduction.

- **[BF]** [Online Beck–Fiala Down to Logarithmic Sparsity](https://arxiv.org/html/2607.14238v1) (2026).

**Status note:** The July 2026 source proves substantial sparsity regimes, not the unrestricted conjecture.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-037 — The sharp Spencer discrepancy constant

**Scope:** Adjacent: matrix discrepancy  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $d_n=\max_{A\in\{-1,1\}^{n\times n}}\min_{x\in\{-1,1\}^n}\|Ax\|_\infty/\sqrt n$. Determine
$$C_* =\sup_{n\ge1}d_n.$$
A related explicitly posed asymptotic milestone is $\limsup_{n\to\infty}d_n>1$. Both are grouped here to avoid counting a nested question twice.

**Source location:** Open Problem 11 and Conjecture 12.

- **[SPEN]** [Did just a couple of deviations suffice all along? (problems 10–14)](https://randomstrasse101.math.ethz.ch/posts/HowManyDeviations/) (2024 author research post, with updates).

**Status note:** The stronger claim involving odd Sylvester–Hadamard orders was refuted in an update and is excluded.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-038 — Hadamard existence in every admissible order

**Scope:** Adjacent: explicit orthogonal matrices  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

For every positive integer $m$, does there exist $H\in\{-1,1\}^{4m\times4m}$ such that
$$HH^T=4mI?$$

**Source location:** Hadamard conjecture; 2026 Section 2.

- **[HAD]** [A Note on Approximate Hadamard Matrices](https://arxiv.org/html/2402.13202) (2024).
- **[ETF]** [New constructions of optimal arrangements of 2d lines in C^d](https://arxiv.org/html/2608.16116v1) (2026).

**Status note:** The cited source explicitly poses the question; no resolution was located in the targeted screening. This is not a proof-level status audit.

**Overlap note:** Related to IS-04/IS-05 and IE-03, but neither sign-matrix conditioning <=2 nor pivot growth on an existing Hadamard matrix is this existence assertion.

### ADD-039 — Ryser’s circulant Hadamard conjecture

**Scope:** Adjacent: structured orthogonal matrices  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Prove or disprove that no circulant $H\in\{-1,1\}^{n\times n}$ with $n>4$ satisfies
$$HH^T=nI.$$

**Source location:** Discussion of circulant Hadamard matrices.

- **[HAD]** [A Note on Approximate Hadamard Matrices](https://arxiv.org/html/2402.13202) (2024).

**Status note:** Approximate circulant Hadamard constructions do not settle exact orthogonality.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-040 — Deterministic polynomial-time commutative Edmonds problem

**Scope:** Adjacent: algebraic linear algebra  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Given rational matrices $A_1,\ldots,A_s\in\mathbb Q^{n\times n}$, can one decide in deterministic polynomial bit complexity whether
$$\det\!\left(\sum_{i=1}^s x_iA_i\right)\not\equiv0$$
as a polynomial in commuting indeterminates? Equivalently, does their rational linear span contain a nonsingular matrix?

**Source location:** Introduction, Edmonds problem.

- **[EDM]** [Edmonds’ problem and the membership problem for orbit semigroups of quiver representations](https://arxiv.org/html/2008.13648v1) (2020 preprint; 2023 journal article).

**Status note:** The noncommutative version has deterministic polynomial algorithms; that does not solve the commuting-variable question.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-041 — An explicit Valiant-rigid family

**Scope:** Adjacent: linear-circuit complexity  
**Provenance:** Specialization  
**Screening date:** 2026-09-08

For $A\in\mathbb Q^{n\times n}$, write $R_A(r)$ for the minimum number of entries that must be changed over $\mathbb Q$ to make its rank at most $r$. Construct a uniformly polynomial-time computable, polynomial-bit rational family $A_n$ and a constant $\delta>0$ with
$$R_{A_n}\!\left(\left\lfloor n/\log\log n\right\rfloor\right)\ge n^{1+\delta}$$
for all sufficiently large $n$.

**Source location:** Section 1.1, Valiant rigidity.

- **[RIG]** [Low Rank Matrix Rigidity: Tight Lower Bounds and Hardness Amplification](https://arxiv.org/html/2502.19580v1) (2025).

**Status note:** Rational-field specialization of the standard explicit-rigidity target. Do not use the Walsh or Fourier matrices as presumed rigid candidates: relevant non-rigidity results are known.

**Overlap note:** No title-level duplicate identified in the uploaded index.


## Adjacent operator and spectral-graph problems

### ADD-042 — Optimal growth after inversion of an exponentially stable generator

**Scope:** Adjacent: infinite-dimensional operator stability  
**Provenance:** Formalization  
**Screening date:** 2026-09-08

Fix $M>1$. Over generators $A$ of strongly continuous semigroups on complex Hilbert spaces satisfying $\|e^{sA}\|\le Me^{-s}$ for all $s\ge0$, determine the asymptotic order of
$$G_M(t)=\sup_A\|e^{tA^{-1}}\|\qquad(t\to\infty).$$
Exponential stability makes $A^{-1}$ bounded. The supremum formulation fixes the dependence on the semigroup bound.

**Source location:** Problem 1.3.

- **[INV]** [A solution to the inverse generator problem and related questions](https://arxiv.org/html/2608.06272v3) (2026).

**Status note:** A precise fixed-M formulation of the new growth question. The older yes/no inverse-generator problem is resolved negatively by the cited 2026 paper.

**Overlap note:** No title-level duplicate identified in the uploaded index.

### ADD-043 — Global synchronization of a random cubic graph

**Scope:** Adjacent: spectral graphs and nonconvex optimization  
**Provenance:** Explicit  
**Screening date:** 2026-09-08

Let $G_n$ be uniformly random among simple 3-regular graphs on an even number $n$ of vertices. On $(\mathbb R/2\pi\mathbb Z)^n$, define
$$E_{G_n}(\theta)=\sum_{\{i,j\}\in E(G_n)}\bigl(1-\cos(\theta_i-\theta_j)\bigr).$$
Does the probability that every local minimum is synchronized (all $\theta_i$ equal modulo $2\pi$) tend to one as $n\to\infty$?

**Source location:** Conjecture 3.

- **[SYNC]** [Randomstrasse101: Open Problems of 2024](https://arxiv.org/html/2504.20539v1) (2025).

**Status note:** This random bounded-degree assertion is not the minimum-degree synchronization-threshold problem. No claim about the old 3/4 threshold is imported.

**Overlap note:** No title-level duplicate identified in the uploaded index.

