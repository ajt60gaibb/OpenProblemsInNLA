# IE-06 exact statement specification

Authored independently before Lean implementation, 2026-10-06. This is a statement specification, not a formal proof of the manuscript. The independent review is recorded in [independent-mathematical-review.md](independent-mathematical-review.md).

## Identity, retained sources, and scope

The permanent ID is **IE-06**, with canonical page linear-systems-and-elimination/IE-06/README.md. The canonical README, TeX and PDF are to remain byte-for-byte unchanged by this work. Initial SHA-256 values:

| File | SHA-256 |
| --- | --- |
| README.md | 15b987cd776e9a4483fd9b8dabd15c945ac5fe4898b7231c6b2f3269a731d523 |
| problem.tex | b73d3f78fdbce9badb64eae1193eb8813b39ef27841426b6b4688b5e9e90a5b5 |
| problem.pdf | dc97a3d6c063848893e23e360af918357c7952375f9ad62424e9be49c3ef1668 |

The complete verbatim README sources are preserved separately as [original HEAD README](../source/original-HEAD-README.md) and [working README](../source/working-README.md). The following is an exact mathematical transcription, not a quotation of all surrounding prose.

There is exactly one original mathematical target: for matrices $G_n\in\mathbb R^{n\times n}$ with mutually independent $N(0,1)$ entries,

$$
\forall\eta>0,\qquad
\lim_{n\to\infty}\Pr\{\rho_{\mathrm{PP}}(G_n)>n^{1/2+\eta}\}=0.
$$

Its conventions are part of the target: exact arithmetic, growth over **all active Schur complements including the input**, nonsingular input matrices, and all admissible partial-pivot choices when magnitudes tie. This asks only for an upper exponent. It does not assert a matching lower bound, a limiting distribution, fixed-precision stability, a uniform deterministic-center result, or IE-04's exponential tail.

| Class | IE-06 inventory | Formalization treatment |
| --- | --- | --- |
| Solved original target | Displayed upper-exponent limit; README records a literature solution on 2026-10-06. | Define the complete proposition, retaining the original ID. A definition is not a proof. |
| Partially solved context | Earlier last-pivot result and polynomial bound with an unspecified larger exponent. | Historical context; neither replaces the target nor creates an ID. |
| Open original targets | None separately stated in IE-06. | Do not invent one. |
| Stronger source result | Subpower-loss, arbitrary-polynomial tail bound. | State separately as a sufficient hypothesis, not as a proved theorem. |

The manuscript is [John Urschel, *On the Growth Factor of Random Matrices*, arXiv:2610.06785v1](https://arxiv.org/html/2610.06785v1). Theorem 1.4 is written using LU growth. Section 5.1 and the proof of Proposition 5.1 also bound every Schur-complement entry. No explicit numerical values for $C_\alpha,n_\alpha$ are supplied. Theorem 1.6, the no-pivoting distribution, and the manuscript's empirical refinements lie outside IE-06's target.

## Probability model and domain

For each $n\in\mathbb N$, use the full real matrix sample space

$$
\Omega_n=\mathbb R^{\{0,\ldots,n-1\}\times\{0,\ldots,n-1\}}.
$$

Let $\gamma=N(0,1)$, with variance one, and

$$
\mu_n=\bigotimes_{i=0}^{n-1}\bigotimes_{j=0}^{n-1}\gamma.
$$

Every scalar entry is standard normal and all $n^2$ entries are mutually independent. A nested finite product measure on the real $n\times n$ matrix type implements this exactly. An arbitrary unspecified matrix law does not. Laws for different dimensions need no common coupling.

Use the actual measure of the specified event. Lean's extended nonnegative real probability values may be compared directly with the embedding of a positive real bound. Alternatively, convert the finite probability to a real explicitly. Do not cap, truncate, or substitute an abstract probability surrogate.

For $n\ge1$, let $m(A)=\max_{i,j}|A_{ij}|$. Take the maximum over the empty matrix to be zero. Nonsingular nonempty matrices have $m(A)>0$.

## Exact partial pivoting and growth

One precise encoding uses a final row permutation $\sigma$, with no column permutation. Set $B_{ij}=A_{\sigma(i),j}$. At $0\le k<n$, define

$$
S_k^\sigma=B_{[k,n),[k,n)}
 -B_{[k,n),[0,k)}(B_{[0,k),[0,k)})^{-1}B_{[0,k),[k,n)}.
$$

At $k=0$, this means $S_0^\sigma=B$, without an inverse operation. The permutation is admissible when its pivot blocks are nonsingular and, at each $k<n$,

$$
(S_k^\sigma)_{00}\ne0,\qquad
\forall i<n-k,\quad |(S_k^\sigma)_{i0}|\le |(S_k^\sigma)_{00}|.
$$

Equivalently, define active matrices recursively, select any largest-magnitude entry of the active first column, swap its row to position zero, and use

$$
(S_{k+1})_{ij}=(\widetilde S_k)_{i+1,j+1}
-\frac{(\widetilde S_k)_{i+1,0}(\widetilde S_k)_{0,j+1}}
 {(\widetilde S_k)_{00}}.
$$

A padded $n\times n$ recursive encoding is valid if all maxima and pivot comparisons explicitly restrict to active indices. Stored multipliers and eliminated entries must not enter the numerator. Its stage-zero matrix is exactly $A$; row permutations do not change the active maximum norm.

Either encoding is faithful. Quantify over every valid path. Non-strict comparisons permit every tie choice. Nonzero-pivot and nonsingularity guards prevent Lean's total inverse/division operations from creating fictitious paths.

For nonsingular $n\ge1$ inputs,

$$
\rho_{\rm PP}(A)=\max_{\sigma\ {\rm admissible}}
 \max_{0\le k<n}\frac{\|S_k^\sigma\|_{\max}}{m(A)}.
$$

The path set is nonempty and finite. An equivalent high-growth event avoids a separate supremum definition:

$$
H_n(t)=\{A:0<n\ \land\ \det A\ne0\ \land\
 \exists\text{ admissible path},\ \exists k<n,\ \exists i,j<n-k,\quad
 t\,m(A)<|(S_k)_{ij}|\}.
$$

For $t\ge1$, this is exactly the high-growth event for the totalization below. The existential bad path means the complementary upper bound controls **all** admissible paths. It must not be replaced by existence of a successful path. The explicit $0<n$ guard makes $H_0(t)$ empty for every real $t$, including negative $t$.

The source uses the smallest current row index to break ties. Gaussian singularity and pivot ties have probability zero; establishing these exceptional-set facts is a bridge obligation, not permission to weaken the formal path quantifier. The original event can be stated without already proving nullity.

For a total growth function, assign growth one to $n=0$ and to singular inputs. The asymptotic target concerns $n\ge2$; changing a function on Gaussian-null singular inputs does not affect it. The event-only implementation instead excludes singular inputs and zero dimension explicitly. For $n=1,A\ne0$, the sole complement is $A$, so growth is exactly one. These totalizations do not assert new conjectures at dimensions zero or one.

The event is intended to be Borel measurable: there are finitely many pivot paths; the guards are polynomial nonzero conditions; guarded updates are rational; and entry comparisons are finite. A proof of the probability theorem must eventually discharge measurability obligations.

## Exact target propositions

**Original target, IE-06.** Powers are real powers. Its direct Lean-shaped statement is

$$
\forall\eta\in\mathbb R,\quad 0<\eta\ \Longrightarrow\
 \operatorname{Tendsto}\left(
 n\mapsto\mu_n(H_n((n:\mathbb R)^{1/2+\eta}))
 \right)\ \operatorname{atTop}\ (\mathcal N(0:\mathbb R_{\ge0}^{\infty})).
$$

The equivalent complete epsilon–$N$ formulation is

$$
\begin{split}
\forall\eta\in\mathbb R,\quad\eta>0\ \Longrightarrow\
\forall\varepsilon\in\mathbb R,\quad\varepsilon>0\ \Longrightarrow\
\exists N\in\mathbb N,\quad N\ge2\ \land\\
\forall n\in\mathbb N,\quad n\ge N\ \Longrightarrow\
\mu_n(H_n(n^{1/2+\eta}))<\operatorname{ofReal}(\varepsilon).
\end{split}
$$

Here $N$ may depend on both $\eta,\varepsilon$. Keep the strict comparison inside the event.

**Auxiliary all-Schur source-bound proposition.** Separately define

$$
\begin{split}
\forall\alpha\in\mathbb R,\quad\alpha>0\ \Longrightarrow\
\exists C\in\mathbb R,\quad C>0\ \land\
\exists N\in\mathbb N,\quad N\ge2\ \land\\
\forall n\in\mathbb N,\quad n\ge N\ \Longrightarrow\
\mu_n(H_n(\sqrt n\exp(C\sqrt{\log n})))
 <\operatorname{ofReal}(n^{-\alpha}).
\end{split}
$$

The constants depend only on $\alpha$, not on the matrix or pivot path. Requiring positive $C$ loses no generality because increasing $C$ increases the threshold for $n\ge2$. The Section 5 argument supports this extraction; it is not literally Theorem 1.4's wording. Its implication to IE-06 can be proved without formalizing the random-matrix argument, provided the source-bound hypothesis stays visible.

## LU/all-Schur bridge and exact rate arithmetic

The manuscript's LU expression is

$$
\max\{\|L\|_{\max},\|U\|_{\max}/\|A\|_{\max}\}.
$$

The $U$ entries form a subset of the Schur entries. This inclusion does **not** allow an LU upper bound alone to bound all Schur entries. Never substitute LU growth for the retained definition.

The strengthened bridge needs control of

$$
M_n(A)=\max_{\text{admissible path},\,k<n}\|S_k\|_{\max}.
$$

Section 5's stagewise estimates give evidence for that control, after handling its tie convention. On $m(A)\ge1$, one has $\rho_{\rm PP}(A)\le M_n(A)$. With $q=\Pr_{Z\sim N(0,1)}(|Z|<1)\in(0,1)$, independence gives the exact identity

$$
\mu_n\{m(A)<1\}=q^{n^2}.
$$

Thus, accounting explicitly for null singular/tie sets, for $t\ge1$,

$$
\mu_n\{\rho_{\rm PP}>t\}\le\mu_n\{M_n>t\}+q^{n^2}.
$$

The denominator event and stagewise failure probabilities must be absorbed, not dropped. If two terms are each at most $n^{-(\alpha+1)}$, their sum is strictly below $n^{-\alpha}$ for $n>2$. For three such terms use $n>3$, or allocate smaller shares. This preserves the strict tail bound.

The elementary comparison for deriving IE-06 is: if $C\ge0,\eta>0,n\ge1$ and

$$
\log n\ge(C/\eta)^2,
$$

then

$$
C\sqrt{\log n}\le\eta\log n,\qquad
\sqrt n\exp(C\sqrt{\log n})\le n^{1/2+\eta}.
$$

Hence the original bad event is eventually contained in the source-bound bad event. Taking its tail exponent $\alpha=1$ and then $n^{-1}<\varepsilon$ proves the epsilon–$N$ target. To prove the stronger little-$o$ sentence in the README, use $\eta/2$ in this comparison and divide by $n^\eta$. Eventual domination alone already suffices for IE-06.

## Numerical statements and trust boundary

No fixed numerical estimate is required by IE-06. The constants $1/2,0,1$ are exact, and source rate constants remain quantified. Do not fabricate executable $C_\alpha,N_\alpha$, add unused problem lemmas, or interpret sampling and finitely many dimension checks as an asymptotic proof.

The shared infrastructure has one separately labeled scalar **checker fixture**:

$$
\log 2<\frac{7}{10}.
$$

It has no variables or domain side conditions; the logarithm is the real natural logarithm and the right side is the exact rational $7/10$. Its role is to exercise LeanCert's kernel-mode numerical certification and trust audit. It is not a lemma about IE-06 or a substitute for the probability argument. The earlier optional Gaussian-density numerical bound is omitted from the implementation scope.

LeanCert kernel-mode trust checking also applies to definitions and supporting structural theorems. Any additional numerical lemma must first be specified with its exact domain, endpoints, inequality direction and actual role, then independently reviewed.

Separate elaboration of the exact proposition, kernel-checked supporting/conditional lemmas, and an unconditional formal proof of IE-06. The first two do not establish the third. Deliberately isolated, clearly labeled Challenge theorem signatures may contain statement-interface placeholders using Lean's sorry mechanism; those declarations must remain outside verified proof products and must never be reported as proofs. Accepted proof products must have no unproved axioms, sorry dependency, external oracle or circular premise.

## Independent acceptance checklist

- Permanent ID and canonical-file hashes are unchanged.
- The law is the finite product of $n^2$ standard real Gaussian laws.
- Active Schur updates use exact arithmetic and nonzero pivots.
- Every active stage from the input to the final $1\times1$ complement is included.
- Existence of a bad admissible path gives universal control over ties.
- Singular exceptional inputs and dimensions zero and one are explicit.
- The original quantifier order and strict threshold are preserved.
- LU growth is not equated with all-Schur growth.
- Source-level solved status and formal proof status remain distinct.
- The exact infrastructure fixture is distinguished from the IE-06 target.
- Kernel evidence does not overclaim an asymptotic probability proof.
