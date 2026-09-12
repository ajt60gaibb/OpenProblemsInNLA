# Independent full mathematical review of MF-06

**Verdict: PASS for the full canonical pointwise lower-Lipschitz assertion in the clarified frozen source.** No substantive mathematical correction is required. This verdict covers arbitrary nonempty compact complex matrix families in every finite dimension, including reducible and product-unbounded reference families.

Reviewed on 12 September 2026 by the separate Codex agent `review_aa01`. I did not author the original partial argument or the full extension. I reconstructed the entire proof, including the previously reviewed partial lemma; the earlier agent's partial PASS was not used as a premise. This is an independent agent audit, not external human peer review, a formal proof, or historical-priority certification.

## Exact sources and one hypothesis clarification

The original full candidate is archived unchanged as [reviewed-proof.md](reviewed-proof.md): 15,815 bytes, SHA-256 `2471cce689608c9ff0dfe15e4ed0230f00ba6799c4df1129e593f08e50593f2d`. It was read in full. The complete canonical target is archived as [canonical-target.md](canonical-target.md): 2,607 bytes, SHA-256 `fe32efa1f84a750039f65695f3cadbf615ead558826490e53329ca26704df741`.

Lemma 2 should explicitly assume that $n\ge1$ and $K,F\ge0$. The bounds $x_i\ge0$ and $x_i\le K$ already force $K\ge0$ when $n\ge1$, but, when $n=1$, the off-diagonal pair condition alone says nothing about $F$. A negative $F$ could make the displayed square root undefined. The only application in the full proof uses $K=K_BK_C\ge1$ and $F=K_B^3K_C^3K_q/q>0$, so this omission does not invalidate any deduction of the theorem. The author separately identified it, and I independently confirmed both the issue and its limited scope. The clarified source is archived unchanged as [reviewed-proof-clarified.md](reviewed-proof-clarified.md): 15,842 bytes, SHA-256 `11fce1e0012b8e514890fa6a116b8d91b91f56f5b7cd0ae20199006b4a18ca94`. I verified that the entire file differs from the original only by insertion of `Let $n\ge1$ and $K,F\ge0$.` in Lemma 2. The [exact diff](source-clarification.diff) and [comparison record](source-clarification.json) preserve this check. No other proof change was requested or made.

## Canonical scope and primary external input

The fixed reference is any $\mathcal M\in\mathcal H_d$, with $\mathcal H_d$ the nonempty compact subsets of $\mathbb C^{d\times d}$. The required constants may depend on this reference and on the dimension. Every sufficiently close nonempty compact $\mathcal N$ must satisfy

$$
\widehat\rho(\mathcal N)\ge\widehat\rho(\mathcal M)-C d_H(\mathcal M,\mathcal N),
$$

where $d_H$ uses the spectral norm. The candidate proves precisely this assertion. It does not assume finitely many generators, an attained periodic extremal word, simultaneous diagonalizability, or a perturbation that preserves the reference invariant flag. It does not claim the locally uniform two-family estimate in MF-05 or the trajectory constants in MF-07.

I directly read [Epperlein–Wirth, arXiv:2311.18633v2](https://arxiv.org/html/2311.18633v2), §2 Conjecture 3(P2), and §3's extremal-norm discussion. The stated conjecture is the pointwise exponent-one lower bound on compact complex families. The same primary source states the irreducible compact-family Barabanov/extremal-norm theorem over the real and complex fields, crediting Barabanov and Wirth. That standard theorem is the only non-elementary norm-existence input used by the extension; its hypotheses are checked below. No general principal-compression monotonicity theorem is assumed.

## 1. Triangular-family JSR formula

The preliminary formula is valid with generator pairing retained. In a fixed block upper-triangular representation, the corresponding diagonal block of a full product is the product of that diagonal block along the same word. Its norm is bounded by the full product norm in the chosen Euclidean block coordinates, proving the lower inequality.

For the converse, choose any strictly positive $q$ above every diagonal-family JSR. All diagonal products of length $s$ obey $Kq^s$, with one fixed finite $K$ after taking the maximum over the finitely many diagonal families. An off-diagonal contribution follows a nondecreasing sequence of block indices with at most $r-1$ strict transitions. Each transition contributes a bounded single-generator block, and the remaining factors form at most $r$ diagonal subwords. Summing over their positions gives at most a fixed polynomial in the word length times $q^n$; factors $q^{-j}$ for $j\le r-1$ are harmless constants because $q>0$ is fixed. Taking roots removes the polynomial. This also works when every diagonal radius is zero, by using arbitrary $q>0$ and then decreasing it to zero.

The argument requires no independent choice of the diagonal blocks in a common time slot. An arbitrary product of a projected diagonal family can be lifted one generator at a time to an original word, which is sufficient for the lower bound.

## 2. Lemma 1: product-bounded reference, stable kernel, and cone

Product boundedness makes the supremum defining $v$ finite. The empty product implies $v(x)\ge\|x\|_2$, so this is a definite complex norm. The product bound also gives an upper Euclidean bound. Every reference generator contracts $v$, since appending it on the right of a permitted word again produces a permitted word.

Each $g_n$ is a complex seminorm and is Lipschitz with constant one in the norm $v$. Removing the outermost applied contraction gives $g_{n+1}\le g_n$. Thus the pointwise limit $p$ is a continuous complex seminorm. The common Lipschitz bound and a finite net show that convergence is uniform on each compact set. Applying this to the compact set $\{Ax:A\in\mathcal M\}$ justifies passage through the maximum in the recurrence, proving equation (2), including attainment. There is no unproved exchange of an infinite limit and a supremum.

The kernel $S=\ker p$ is a common invariant complex subspace. Its stability is uniform, not merely pointwise: choose a fixed basis $e_1,\ldots,e_s$ of $S$ and a constant $C_S$ such that $v(x)=1$ implies that the coordinate absolute sum of $x$ in this basis is at most $C_S$. Every restricted length-$n$ product $P$ then satisfies

$$
v(Px)\le C_S\max_i g_n(e_i)\longrightarrow0.
$$

Consequently the maximum restricted operator norm tends to zero. At one finite length it is strictly below one; submultiplicativity, followed by decomposition into such fixed-length words and a bounded remainder, gives restricted JSR strictly below one. Applying the same argument on the full space would contradict JSR one, so the quotient is nonzero. A seminorm is constant on cosets of its kernel, and therefore induces the claimed quotient norm. Equation (2) descends to that quotient.

For any $q\in(0,1)$ above the restricted radius, the supremum of $q^{-n}$ times restricted product norms defines a finite norm in which all restricted generators have norm at most $q$. This construction applies even if the restriction is reducible. A fixed complement identifies the quotient with the second block. All block projections, embeddings and chosen norms are fixed, so one common constant $c_0$ bounds every block of a spectral-norm perturbation by $t=c_0\delta$.

For a current vector with $a\le Hb$, select a reference generator whose quotient action preserves the quotient norm. Compactness gives an actual nearby member of $\mathcal N$. The perturbation may have a nonzero lower-left block, and it is included in the estimates:

$$
b'\ge b-t(a+b)\ge(1-Lt)b,
\qquad
a'\le qa+Kb+t(a+b)\le(H-1+Lt)b.
$$

Here $qH+K=H-1$ and $L=H+1$. The cone calculation is exact:

$$
(H-1+Lt)-H(1-Lt)=-1+L^2t\le0.
$$

Moreover $H\ge1$, $L\ge2$, and $t\le L^{-2}$ imply $1-Lt\ge1-L^{-1}>0$. Starting from first component zero and quotient norm one gives legal products whose quotient norm grows by at least $(1-Lt)^n$. State-dependent selection is permissible for this existence argument; the definition of JSR does not require a fixed periodic word, a continuous selector, or a probabilistic process. Fixed norm-equivalence constants disappear on taking $n$th roots. This proves the lower estimate at a product-bounded reference. When $S=0$, the stable block is empty and the same proof works after any convenient choice $q\in(0,1)$, $K=0$.

## 3. Lemmas 2 and 3: scalar summation and paired nonresonance

With the nonnegative parameters specified above, summing the pairwise bound across a cut gives

$$
\sum_{i\le h<j}x_ix_j\le
F\sum_{i\le h<j}q^{j-i}\le\frac{Fq}{(1-q)^2}.
$$

At the first prefix reaching half the total $X$, the prefix lies in $[X/2,X/2+K]$, and the suffix is at least $X/2-K$. If the latter quantity is nonnegative, their product is at least $X^2/4-KX/2$; if it is negative, this lower bound is nonpositive and is still valid. A cut at the last index causes no exception. Solving the resulting quadratic gives exactly (3). The cases $X=0$, $F=0$, or one summand cause no difficulty after the explicit hypothesis clarification.

For Lemma 3, the off-diagonal expansion is the usual single-transition expansion with transition time $i$. Define $x_i$ exactly as in the source. Splitting at times $i<j$ leaves the *same intervening word* in the two diagonal factors. The displayed generous constants are valid: the outer products and a single endpoint generator contribute at most $K_B^2K_C$ in the first bound and $K_BK_C^2$ in the second. The intervening length is $j-i-1$.

For complex matrices with Hilbert operator norm, $\|U\otimes V\|_2=\|U\|_2\|V\|_2$. The product of the paired tensor generators is the tensor product of the two diagonal products along that common word. Thus a strictly subunit paired JSR gives exactly (4), with fixed $q\in(0,1)$ and $K_q\ge1$. The empty intervening word when $j=i+1$ is covered. It follows that

$$
x_ix_j\le K_B^3K_C^3K_q q^{j-i-1},
$$

which meets Lemma 2 with positive $F$. The resulting uniform sum bound controls every full off-diagonal product block. There is no estimate that mistakenly replaces the paired tensor family by independently switched diagonal products.

## 4. Lemma 4: the induction includes the off-diagonal prefix

For the grouping $G_A$ of the first $r-1$ blocks, the induction hypothesis already gives full product boundedness of $G$. The tensor family $G_A\otimes D_{r,A}$ contains the prefix's off-diagonal blocks, but, after a fixed tensor-coordinate identification, remains block upper triangular. Its diagonal blocks are exactly $D_{i,A}\otimes D_{r,A}$ for $i<r$, with original-generator pairing. The preliminary triangular JSR formula applies regardless of whether this full tensor family is product bounded in advance. The finite maximum of its strictly subunit diagonal radii is strictly below one. Lemma 3 therefore applies to the grouped two-block family and completes the induction. This resolves the potentially circular point about the prefix's off-diagonal terms.

## 5. Lemma 5: irreducible blocks and the critical exterior power

A maximal common invariant flag exists by finite dimension and yields irreducible quotient block families over the specified complex field. Passing to one fixed similarity preserves compactness, JSR and product boundedness; its exterior representations are fixed similarities as well. Each diagonal radius is at most one by the triangular formula. A block of radius below one is product bounded by an exponential estimate. An irreducible block of radius one has an extremal norm by the primary input verified above, and hence has uniformly bounded Euclidean products. The theorem is not applied to a zero-radius irreducible block.

For every allocation $a$, exterior powers respect products and the Hilbert tensor norm is multiplicative. The resulting wordwise bound in (6) follows from $\|\Lambda^{a_i}P_i\|\le\|P_i\|^{a_i}$. Thus all allocation families are product bounded, even though they need not be irreducible and the original full family need not be product bounded.

The claimed triangular representation of $\Lambda^j A$ is correct. In a wedge basis ordered by the original block membership of its factors, a strict upper-block transition replaces an input block index by a strictly earlier one. It strictly decreases the total weighted block index. Hence a nonzero contribution between different allocations can only move down this finite order; one can refine it to a fixed ordinary block-triangular order. If the input and output allocation agree, no strict move can have occurred, so the diagonal action is exactly $\bigotimes_i\Lambda^{a_i}A_i$. This also addresses allocations of equal weighted sum: a strict transition cannot connect them. Applying the triangular formula gives equation (7), with common generator pairing throughout.

All positive-degree exterior radii are at most one. Degree one has radius one, so a largest such $k$ exists. For distinct allocations $a,b$ of degree $k$, their coordinatewise maximum $c$ remains admissible and has degree strictly greater than $k$; its degree cannot exceed $d$. Their coordinatewise minimum $e$ is also admissible.

Equation (8) is an exact scalar factor reordering, not a speculative inequality about unrelated singular values. For each original block, the unordered pair $\{a_i,b_i\}$ equals $\{c_i,e_i\}$, so the two exterior-norm factors on each side agree as a multiset. Multiplying over blocks proves the equality, including zero factors. The norm of $P_e$ is uniformly bounded by the already established allocation bound, independently of word length. No division by a wedge norm is used, and degree-zero factors have norm one.

Every word in the paired degree-$k$ allocation family comes from an original word. Taking its norm, applying (8), maximizing over words and taking roots proves the first inequality in (9); all finite word-independent bounds disappear. The allocation $c$ is a diagonal block of the higher exterior family, so equation (7) gives the next inequality. Maximality of $k$ gives strict inequality below one, including the case where the higher radius is zero. Therefore *every distinct pair* of degree-$k$ allocation blocks meets Lemma 4's paired nonresonance assumption. Applying that lemma proves full product boundedness of $\Lambda^k\mathcal M$.

The endpoint $k=d$ has only one allocation and needs no paired condition. A single irreducible reference block, degree-zero wedge components, singular generators, repeated spectral information, and stable zero diagonal blocks are all permitted. No selection of an extremizing infinite word or periodic attainment occurs in this argument.

## 6. Hausdorff transfer and the final root

The tensor telescoping formula for $A^{\otimes k}-B^{\otimes k}$ has $k$ terms, each bounded by $L_0^{k-1}\|A-B\|_2$ on the stated norm ball. The normalized antisymmetric Hilbert embedding identifies the exterior representation with the restriction of this tensor action. Restricting cannot increase operator norm, so (10) follows with exactly the displayed constant.

If $\delta<1$, Hausdorff closeness to the fixed compact reference bounds every generator of $\mathcal N$ by $L_0$. Matching in both directions proves the image Hausdorff estimate. Noninjectivity of the exterior map is irrelevant; its images are nonempty and compact. Lemma 1 applies to the fixed critical exterior family, while the perturbed image may be arbitrary and need not preserve its invariant subspaces.

On every original word, the wedge norm is at most the original norm to the $k$th power. Taking maximal norms and roots gives $\widehat\rho(\Lambda^k\mathcal N)\le\widehat\rho(\mathcal N)^k$. After shrinking the reference-dependent neighborhood so that $C_1\delta<1$, the lower bound is positive. The scalar inequality $s^{1/k}\ge s$ for $0\le s\le1$ then gives the claimed linear lower bound. Taking this root introduces no fractional-power loss because it is taken near the positive normalized radius one.

If the original reference radius is $R>0$, divide both families by $R$: their Hausdorff distance becomes $\delta/R$ and both radii scale by $1/R$. Multiplying the normalized lower estimate by $R$ returns a linear estimate in $\delta$, with a correspondingly rescaled neighborhood. When $R=0$, nonnegativity gives the original one-sided bound for any positive constants. Distance zero, dimension one, and an image containing zero matrices cause no exception.

## Supplementary exact algebra checks

I wrote [independent_exterior_check.py](independent_exterior_check.py) without importing or copying the author's checker. It constructs integer block upper-triangular matrices for eight profiles through total dimension six, computes exterior matrices directly from full minors, and compares their diagonal allocation blocks with tensor products of separately computed diagonal-block exterior matrices. It also checks the exterior product identity and the max/min allocation factor multiset equality. All computations use integers and rational fractions, with no floating point.

[independent-exterior-check.json](independent-exterior-check.json) records PASS for 36 exterior-product identities, 279 diagonal allocation tensor blocks, 1,686 forced zero minors and 161 max/min factor reorderings. These finite checks support algebraic transcription only. They do not establish a universal JSR claim, estimate an infinite product supremum, or replace the analytic argument audited above.

## Disposition and limits

The full theorem follows from the reconstructed chain. The proof supplies the missing reducible, product-unbounded reference case through a product-bounded critical exterior power, and then transfers the one-sided estimate back without weakening its exponent. The small standalone Lemma 2 clarification is present in the final reviewed source and changes no used hypothesis or final deduction. No correction remains pending.

This report is a full mathematical and canonical-scope review of the bound source. It is not an exhaustive public-fork/literature eligibility audit, a novelty certification, a review of a future Markdown-to-TeX conversion, or external peer review. Any public wrapper should keep those distinctions and the attribution to Epperlein–Wirth explicit.

Signed by Codex agent `review_aa01`, independent full reviewer, 12 September 2026, 04:59:52 UTC.
