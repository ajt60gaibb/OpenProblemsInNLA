# MF-06: a proposed full lower-Lipschitz proof through exterior powers

George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

Private proof candidate, 12 September 2026. **Independent review of this full extension is pending.** The lower bound for relatively product-bounded families was first proved in the frozen private partial manuscript `/tmp/nla-fresh-round15/mf06/RESULT.md`, SHA-256 `c3bc7409eed8b25db284fefd9cff230ac35dac1ce78fda90c241eb0b78482be9`, and independently passed in the adjacent `REVIEW.md`. That verdict covers the partial manuscript, not the new exterior-power and nonresonance arguments below. The full proof is included here so its hypotheses and deductions can be audited without reconstructing earlier conversation. No publication or repository change has been made.

## 1. The exact target

For a nonempty compact family $\mathcal M\subseteq\mathbb C^{d\times d}$, let $\widehat\rho(\mathcal M)$ be its joint spectral radius and let $d_H$ be Hausdorff distance induced by the spectral norm. The claimed theorem is:

**Theorem.** For every $d\ge1$ and every such fixed $\mathcal M$, there exist $C,r>0$ such that every nonempty compact $\mathcal N\subseteq\mathbb C^{d\times d}$ with $d_H(\mathcal M,\mathcal N)<r$ satisfies

$$
\widehat\rho(\mathcal N)\ge\widehat\rho(\mathcal M)-C d_H(\mathcal M,\mathcal N).
\tag{1}
$$

The constants need not be uniform as the reference family varies. No finiteness of either family and no periodic attainment of the radius are assumed. When $\widehat\rho(\mathcal M)=0$, the assertion follows immediately from nonnegativity. In the remaining proof divide both families by the fixed positive reference radius, so $\widehat\rho(\mathcal M)=1$. Rescaling at the end preserves the linear form of (1).

The target is Epperlein–Wirth, [*The joint spectral radius is pointwise Hölder continuous*, arXiv:2311.18633v2](https://arxiv.org/html/2311.18633v2), Conjecture 3(P2). Their §3 recalls the standard fact used below: a compact irreducible family of positive radius admits an extremal norm (indeed a Barabanov norm). Apart from that fact, elementary finite-dimensional norm and exterior-algebra facts, and the existence/formula for JSR, the arguments are supplied below. The later [principal-submatrix paper](https://arxiv.org/html/2504.17505v1) is not used as a compression monotonicity theorem.

## 2. Preliminary triangular and product-bounded facts

For a compact family put

$$
a_n(\mathcal F)=\max_{F_1,\ldots,F_n\in\mathcal F}\|F_n\cdots F_1\|_2,
\qquad a_0=1.
$$

If $\widehat\rho(\mathcal F)<q$, then $a_n(\mathcal F)\le Kq^n$ for a finite $K$: this follows directly from $a_n^{1/n}\to\widehat\rho(\mathcal F)$, absorbing finitely many initial values in $K$. A family is called **product bounded** here when $\sup_n a_n<\infty$.

**Triangular fact.** The JSR of a finite block upper-triangular compact family is the maximum of the JSRs of its diagonal block families, with every block tied to the same original generator.

For clarity, the diagonal compressions of each product give the lower bound. For the upper bound, choose $q>0$ above all the diagonal JSRs and bound each diagonal product by $Kq^n$. In a product on $r$ blocks, an off-diagonal term contains at most $r-1$ strict block transitions. Their matrices are uniformly bounded; all other factors form at most $r$ diagonal products. There are at most a constant times $(n+1)^{r-1}$ such terms. Absorbing the finitely many powers $q^{-j}$ gives an upper bound $K'(n+1)^{r-1}q^n$ for the full product. Take $n$th roots and then let $q$ decrease to the largest diagonal radius. This argument does not allow independent switching of paired blocks.

## 3. Lower Lipschitz continuity at a product-bounded reference family

**Lemma 1.** A compact product-bounded family of JSR one satisfies (1).

**Proof.** Define the extremal norm

$$
v(x)=\sup_{n\ge0}\max_{A_1,\ldots,A_n\in\mathcal M}
\|A_n\cdots A_1x\|_2.
$$

It is finite and definite and all reference generators contract it. Set

$$
g_n(x)=\max_{A_1,\ldots,A_n\in\mathcal M}v(A_n\cdots A_1x),
\qquad p(x)=\lim_{n\to\infty}g_n(x).
$$

Deleting the leftmost applied contraction shows $g_{n+1}\le g_n$. The bound $|g_n(x)-g_n(y)|\le v(x-y)$ implies that the limit is a continuous seminorm and convergence is uniform on compact sets, by a finite-net argument. The recurrence $g_{n+1}(x)=\max_Ag_n(Ax)$ and compactness therefore give

$$
p(x)=\max_{A\in\mathcal M}p(Ax).
\tag{2}
$$

Let $S=\ker p$. This is invariant. On a fixed basis of $S$, all $g_n$ tend to zero; equivalence of the coordinate norm and $v$ then shows that the maximal restricted product operator norm tends to zero. At some finite length it is strictly below one, so the restricted JSR is below one by submultiplicativity. The same argument excludes $S=\mathbb C^d$, as the full JSR is one. The seminorm induces a norm on the nonzero quotient, satisfying (2).

Choose a fixed complement and write the generators as

$$
A=\begin{pmatrix}U_A&V_A\\0&B_A\end{pmatrix}.
$$

Use the quotient norm for the second coordinate. The stable first coordinate admits a norm with $\|U_A\|\le q<1$ for all $A$: the supremum of $q^{-n}$ times restricted product norms applied to a vector constructs one, after choosing $q$ above the restricted radius. Let $K$ bound $\|V_A\|$, and put

$$
H=\frac{K+1}{1-q},\qquad L=H+1.
$$

If $S=0$, omit the first block; the same estimates can be used with its vector always zero. Fixed norm equivalence bounds each block of a matched perturbation by $t=c_0\delta$, where $\delta=d_H(\mathcal M,\mathcal N)$ and $c_0$ is independent of $\mathcal N$.

For a vector with component norms $a,b$ satisfying $a\le Hb$ and $b>0$, select a reference generator using (2) so that $\|B_Az\|=b$, and then one nearby member of $\mathcal N$. The new component norms obey

$$
b'\ge(1-Lt)b,\qquad
a'\le(qH+K+Lt)b=(H-1+Lt)b.
$$

For $t\le L^{-2}$ one has $H-1+Lt\le H(1-Lt)$, so the cone is preserved. Also $H\ge1$ and $L\ge2$, making $1-Lt>0$. Starting with first component zero and quotient norm one constructs a legal perturbed trajectory whose quotient norm is at least $(1-Lt)^n$ at every length. Norm equivalence and $n$th roots give $\widehat\rho(\mathcal N)\ge1-Lc_0\delta$. This proves the lemma. The choices may depend on the current vector, which is allowed when proving existence of a product attaining a lower growth bound. No periodic word is used. $\square$

## 4. An elementary nonresonance lemma

**Lemma 2 (scalar summation).** Suppose $x_1,\ldots,x_n\ge0$, $x_i\le K$, and

$$
x_ix_j\le Fq^{|i-j|}\quad(i\ne j),\qquad 0<q<1.
$$

Then, independently of $n$,

$$
\sum_{i=1}^n x_i\le K+\sqrt{K^2+\frac{4Fq}{(1-q)^2}}.
\tag{3}
$$

**Proof.** For every cut $h$,

$$
\left(\sum_{i\le h}x_i\right)\left(\sum_{j>h}x_j\right)
\le F\sum_{i\le h<j}q^{j-i}\le\frac{Fq}{(1-q)^2}=:G.
$$

Let $X=\sum x_i$ and take the first cut whose prefix sum is at least $X/2$. This prefix lies between $X/2$ and $X/2+K$, so its complementary sum is at least $X/2-K$. If $X/2-K\ge0$, their product is at least $X^2/4-KX/2$. If $X/2-K<0$, the same lower bound is nonpositive and still valid. Thus $X^2/4-KX/2\le G$, whose positive root is (3). The case $X=0$ is immediate. $\square$

**Lemma 3 (two blocks).** Let a compact family consist of

$$
A=\begin{pmatrix}B_A&D_A\\0&C_A\end{pmatrix}.
$$

Assume the two diagonal families are product bounded. If the **paired** tensor-product family

$$
\{B_A\otimes C_A:A\in\mathcal M\}
$$

has JSR strictly below one, then the whole family is product bounded.

**Proof.** Let $K_B,K_C\ge1$ bound all diagonal products, including empty ones. Let $D_0$ bound every off-diagonal generator. Choose $0<q<1$ above the paired tensor JSR, and $K_q\ge1$ such that every length-$\ell$ word satisfies

$$
\|B_\ell\cdots B_1\|_2\,\|C_\ell\cdots C_1\|_2
\le K_q q^\ell.
\tag{4}
$$

This follows because the spectral norm of a Kronecker product is the product of the spectral norms and the generators are paired at every time.

For an arbitrary full word of length $n$, its upper-right block is

$$
\sum_{i=1}^n B_n\cdots B_{i+1}D_iC_{i-1}\cdots C_1.
$$

Put

$$
x_i=\|B_n\cdots B_{i+1}\|_2\,
\|C_{i-1}\cdots C_1\|_2\le K_BK_C.
$$

For $i<j$, split the first product at $j$ and the second at $i$. Product boundedness yields

$$
x_i\le K_B^2K_C\|B_{j-1}\cdots B_{i+1}\|_2,
\qquad
x_j\le K_BK_C^2\|C_{j-1}\cdots C_{i+1}\|_2.
$$

The intervening factors are from the same original word. By (4),

$$
x_ix_j\le K_B^3K_C^3K_q q^{j-i-1}
=Fq^{j-i},\qquad F=K_B^3K_C^3K_q/q.
$$

Lemma 2 bounds $\sum x_i$ independently of the word and its length. The off-diagonal block norm is at most $D_0\sum x_i$. The diagonal blocks were already uniformly bounded, proving the result. $\square$

**Lemma 4 (finitely many blocks).** Let a compact family have a fixed finite block upper-triangular form with diagonal blocks $D_{1,A},\ldots,D_{r,A}$. Suppose every diagonal family is product bounded and, for every distinct $i,j$, the paired family $\{D_{i,A}\otimes D_{j,A}:A\in\mathcal M\}$ has JSR below one. Then the full family is product bounded.

**Proof.** Induct on $r$. The case $r=1$ is the hypothesis. Group the first $r-1$ blocks into $G_A$, which is product bounded by induction. The family $\{G_A\otimes D_{r,A}\}$ is block upper triangular, after a fixed coordinate identification, with diagonal families $\{D_{i,A}\otimes D_{r,A}\}$ for $i<r$. The triangular fact in §2 shows that its JSR is below one. Lemma 3 applied to the two blocks $G_A,D_{r,A}$ completes the induction. Pairing is maintained throughout. $\square$

## 5. Every normalized family has a critical product-bounded exterior power

For $0\le j\le d$, let $\Lambda^j A$ denote the induced map on the $j$th exterior power equipped with its standard Hilbert norm; $\Lambda^0 A$ is the scalar identity. Exterior powers respect products and satisfy

$$
\|\Lambda^j P\|_2\le\|P\|_2^j.
\tag{5}
$$

Write $\Lambda^j\mathcal M=\{\Lambda^j A:A\in\mathcal M\}$. In particular $\widehat\rho(\Lambda^j\mathcal M)\le\widehat\rho(\mathcal M)^j=1$ for $j\ge1$.

**Lemma 5 (critical exterior power).** If $\widehat\rho(\mathcal M)=1$, there is an integer $1\le k\le d$ such that $\Lambda^k\mathcal M$ has JSR one and is product bounded.

**Proof.** A maximal common invariant flag puts the reference family, by a fixed similarity, into block upper-triangular form with irreducible diagonal families $A_{1},\ldots,A_r$ of respective dimensions $d_1,\ldots,d_r$. Similarity does not affect JSR or product boundedness, and its exterior powers are also fixed similarities.

By the triangular fact, every diagonal radius is at most one. A diagonal family of radius strictly below one is product bounded by the preliminary exponential bound. A diagonal irreducible family of radius one has an extremal norm, hence is product bounded in the spectral norm by finite-dimensional norm equivalence. Choose $K_i\ge1$ bounding all products in diagonal family $i$.

For each integer vector $a=(a_1,\ldots,a_r)$ with $0\le a_i\le d_i$, define its degree $|a|=\sum_i a_i$ and the paired tensor family

$$
\mathcal F_a=
\left\{\bigotimes_{i=1}^r\Lambda^{a_i} A_i:A\in\mathcal M\right\}.
$$

All factors in one tensor come from the same original generator. For a word of length $n$, write its diagonal block products as $P_1,\ldots,P_r$. The corresponding product in $\mathcal F_a$ is

$$
P_a=\bigotimes_{i=1}^r\Lambda^{a_i}P_i,
\qquad \|P_a\|_2\le\prod_iK_i^{a_i}.
\tag{6}
$$

Thus each allocation family $\mathcal F_a$ is product bounded.

The usual decomposition of $\Lambda^j(V_1\oplus\cdots\oplus V_r)$ into tensor products $\bigotimes_i\Lambda^{a_i}V_i$, $|a|=j$, gives a block upper-triangular form for $\Lambda^j A$, in an ordering refining cumulative block occupation. Its diagonal blocks are exactly those of $\mathcal F_a$. Indeed, an original strict upper-block transition moves an exterior factor to an earlier original block; if the input and output allocations agree, no such strict move can occur. Reordering the finitely many allocation subspaces once gives an ordinary triangular block form. Therefore

$$
\widehat\rho(\Lambda^j\mathcal M)
=\max_{|a|=j}\widehat\rho(\mathcal F_a).
\tag{7}
$$

Choose the **largest** $k\in\{1,\ldots,d\}$ for which $\widehat\rho(\Lambda^k\mathcal M)=1$. Such a $k$ exists because $k=1$ qualifies. For every $j>k$ the exterior radius is strictly below one, using (5).

Consider two distinct degree-$k$ allocations $a,b$. Put $c_i=\max(a_i,b_i)$ and $e_i=\min(a_i,b_i)$. Then $|c|>k$, while all their coordinates remain within the allowed bounds. For every common original word, multiplicativity of the Hilbert tensor norm gives the exact identity

$$
\|P_a\|_2\|P_b\|_2=\|P_c\|_2\|P_e\|_2
\le\left(\prod_iK_i^{e_i}\right)\|P_c\|_2.
\tag{8}
$$

The equality simply reorders, for each block $i$, the two factors $\|\Lambda^{a_i}P_i\|_2$ and $\|\Lambda^{b_i}P_i\|_2$; it remains valid when some factor is zero. The degree-zero exterior factor is one.

Take maximal norms over common words and then $n$th roots in (8). The paired tensor family of the two allocation blocks obeys

$$
\widehat\rho\left(
\left\{\left(\bigotimes_i\Lambda^{a_i}A_i\right)
\otimes\left(\bigotimes_i\Lambda^{b_i}A_i\right):A\in\mathcal M\right\}
\right)
\le\widehat\rho(\mathcal F_c)
\le\widehat\rho(\Lambda^{|c|}\mathcal M)<1.
\tag{9}
$$

Thus the triangular representation of $\Lambda^k\mathcal M$ has product-bounded diagonal allocation families and strictly subunit paired tensor radii for every distinct pair. Lemma 4 proves that the full exterior-power family is product bounded. Its radius is one by the choice of $k$. $\square$

## 6. Transfer back to the original family

Apply Lemma 5 and fix its $k$. For matrices $A,B$ of norm at most $L_0$, the tensor telescoping identity, restricted to the antisymmetric subspace, gives

$$
\|\Lambda^k A-\Lambda^k B\|_2
\le kL_0^{k-1}\|A-B\|_2.
\tag{10}
$$

Take $L_0=1+\max_{A\in\mathcal M}\|A\|_2$. When $\delta=d_H(\mathcal M,\mathcal N)<1$, all nearby generators have norm at most $L_0$. Matching in both directions in (10) proves

$$
d_H(\Lambda^k\mathcal M,\Lambda^k\mathcal N)
\le kL_0^{k-1}\delta.
\tag{11}
$$

The image families remain nonempty and compact, even if the exterior map is not injective. Lemma 1 now applies to the fixed product-bounded radius-one family $\Lambda^k\mathcal M$. For sufficiently small $\delta$ it gives

$$
\widehat\rho(\Lambda^k\mathcal N)\ge1-C_0kL_0^{k-1}\delta.
$$

On the other hand, (5) on every word implies

$$
\widehat\rho(\Lambda^k\mathcal N)\le\widehat\rho(\mathcal N)^k.
$$

Choose the neighborhood so $C_1\delta<1$, where $C_1=C_0kL_0^{k-1}$. Consequently

$$
\widehat\rho(\mathcal N)
\ge(1-C_1\delta)^{1/k}\ge1-C_1\delta.
$$

This is the normalized form of (1). Rescaling both families by the original positive reference radius completes the proposed proof in every complex dimension. The zero-radius case was handled separately. No periodic attainment, principal-block monotonicity for arbitrary perturbations, or stable-kernel assumption on the original family was used.

## 7. Scope of verification and attribution

The argument in Lemma 1 is the previously independently audited partial proof, included here in full. Lemmas 2–5 and their use in §6 are the new extension from this pass and require separate independent review. The standard irreducible extremal-norm theorem is attributed to the literature as above; the target conjecture belongs to Epperlein–Wirth. This note asserts no historical-priority certification and reports no external human review or formal proof. Any exact finite checker only supports transcription of finite algebraic identities and is not the basis for the all-family claims.
