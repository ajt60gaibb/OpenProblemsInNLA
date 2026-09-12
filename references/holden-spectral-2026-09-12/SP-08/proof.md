# SP-08: A signed-threshold reduction and three exact finite cases

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Submission date:** 12 September 2026.  
**Editorial record:** [Attribution, independent review and scope](../README.md).

The review statements below describe the supplied draft; the linked submission record records subsequent independent review.

**Scope:** Complete proofs of the reduction below and computer-assisted proofs for
$`(n,a)=(8,1/2),(10,0),(11,0)`$. **Not a proof of the all-dimensions Fallat–Xing conjecture.**

**Review status:** Written and checked in this ChatGPT session. Exact certificates
were regenerated and checked locally. No independent human or agent review, Lean
verification, or novelty/priority claim is asserted.

## 1. Target and results

Write


```math
\mathcal S_n[a,b]=\{A=A^T\in\mathbb R^{n\times n}:a\le A_{ij}\le b\},
\qquad s(A)=\lambda_{\max}(A)-\lambda_{\min}(A).
```


The repository target asks whether, for every $`n\ge2`$ and $`-1\le a<1`$,
the maximum over $`\mathcal S_n[a,1]`$ is attained by a rank-two matrix with
entries in $`\{a,1\}`$. The present finite-case conclusions are


```math
\begin{aligned}
\max_{A\in\mathcal S_8[1/2,1]}s(A)&=\sqrt{73},\\
\max_{A\in\mathcal S_{10}[0,1]}s(A)&=\sqrt{133},\\
\max_{A\in\mathcal S_{11}[0,1]}s(A)&=\sqrt{161}.
\end{aligned}
\tag{1}
```


Each is attained by the displayed rank-two construction in Section 4.

The pinned repository records earlier results for all interval parameters through
order seven, and for $`a=0`$ through order eight or when three divides the order.
Thus (1) lies beyond those particular recorded finite ranges. This comparison is
not a claim that the results have never appeared elsewhere.

## 2. A finite family sufficient for every dimension

For signs $`\varepsilon_1,\ldots,\varepsilon_n`$ and
$`d_1,\ldots,d_n`$, with $`d_1=1`$, set


```math
S(\varepsilon,d)_{ij}=d_i d_j\varepsilon_{\min(i,j)},
\qquad
B_{a,b}(\varepsilon,d)=\frac{a+b}{2}{\bf1}{\bf1}^T+
\frac{b-a}{2}S(\varepsilon,d).
\tag{2}
```


These matrices are symmetric, and every entry of $`B_{a,b}`$ is either $`a`$
or $`b`$. There are $`2^n2^{n-1}=2^{2n-1}`$ parameter choices, possibly with
duplicate matrices or spectra.

### Theorem 1 — signed-threshold reduction

For every real $`a< b`$ and every $`n\ge2`$,


```math
\max_{A\in\mathcal S_n[a,b]}s(A)
=\max_{\varepsilon,d:\,d_1=1}s(B_{a,b}(\varepsilon,d)).
\tag{3}
```


In particular, enumeration of all symmetric endpoint matrices, numbering
$`2^{n(n+1)/2}`$, is unnecessary for this maximization.

### Proof

The box $`\mathcal S_n[a,b]`$ is compact and spread is continuous, so choose a
maximizer $`A_*`$. Take real unit eigenvectors $`x,y`$ for its largest and
smallest eigenvalues and set


```math
M=xx^T-yy^T,
\qquad \langle C,M\rangle=\mathop{\mathrm{tr}}\nolimits(CM).
```


Then


```math
\langle A_*,M\rangle=s(A_*),\qquad
\langle C,M\rangle\le s(C)\le s(A_*)
\quad(C\in\mathcal S_n[a,b]).
\tag{4}
```


For any symmetric $`M'`$ having no zero entries, its linear objective on the
symmetric box has the endpoint maximizer


```math
C(M')_{ij}=\begin{cases}b&M'_{ij}>0,\\a&M'_{ij}<0.\end{cases}
\tag{5}
```


The factor two in the off-diagonal terms of the trace does not change the sign
rule.

Factor


```math
u=(x+y)/\sqrt2,\quad v=(x-y)/\sqrt2,\quad M=uv^T+vu^T.
```


Perturb $`u,v`$, if necessary, to arbitrarily close vectors $`u',v'`$ such that
all $`v'_i\ne0`$, all ratios $`r_i=u'_i/v'_i\ne0`$, and all absolute values
$`|r_i|`$ are distinct. Such perturbations exist: after choosing nonzero
$`v'_i`$ close to $`v_i`$, choose the coordinates $`u'_i`$ in turn avoiding
finitely many prohibited values. No orthogonality or normalization of the
perturbed vectors is needed.

Simultaneously permute indices so that


```math
|r_1|>|r_2|>\cdots>|r_n|>0.
```


For $`i< j`$, the larger-magnitude term $`r_i`$ determines the sign of
$`r_i+r_j`$; on the diagonal the same statement follows from $`2r_i`$.
Since


```math
M'_{ij}=v'_i v'_j(r_i+r_j),
```


we obtain


```math
\mathop{\mathrm{sgn}}\nolimits M'_{ij}
=d_i d_j\varepsilon_{\min(i,j)},
\quad d_i=\mathop{\mathrm{sgn}}\nolimits v'_i,
\quad\varepsilon_i=\mathop{\mathrm{sgn}}\nolimits r_i.
\tag{6}
```


Replacing every $`d_i`$ by its negative leaves (6) unchanged, so impose
$`d_1=1`$. Thus every $`C(M')`$ is permutation-similar to a matrix in (2).

To handle zeros or other degeneracies in the original $`M`$, take a sequence
of such perturbations with $`M'\to M`$. There are only finitely many endpoint
matrices, so a subsequence of the maximizers (5) is a single fixed matrix
$`C`$. Its defining optimality gives
$`\langle C,M'\rangle\ge\langle A_*,M'\rangle`$. Passing to the limit and
using (4) yields


```math
s(C)\ge\langle C,M\rangle\ge s(A_*).
```


Hence $`C`$ is also a spread maximizer and is permutation-similar to a member
of (2). Spread is invariant under permutation similarity. This proves (3).
$`\square`$

**Important limitation.** Theorem 1 does not assert that a maximizing member of
(2) has rank two. Establishing that for every dimension and interval would still
be needed for the original conjecture.

## 3. Exact certification of upper bounds

The three finite computations enumerate the entire family (2), calculate its
characteristic polynomials exactly, remove duplicate polynomials, and certify
an upper bound for every remaining polynomial. Floating-point eigenvalues are
used only to *propose* rational enclosures. The verifier does not use a
floating-point eigensolver.

### Lemma 2 — rational upper-root certificate

Let $`p(z)=z^n+c_1z^{n-1}+\cdots+c_n`$ be a monic real polynomial. Let
$`q>0`$ and $`h`$ be integers. If every coefficient of


```math
q^n p((z+h)/q)
\tag{7}
```


is nonnegative, no real root of $`p`$ is larger than $`h/q`$.

**Proof.** The leading coefficient in (7) is one. Thus (7) is strictly positive
for every $`z>0`$, and the change of variables gives the assertion. $`\square`$

Apply the lemma to $`p`$ and to


```math
p_-(z)=(-1)^n p(-z),
```


which is the monic characteristic polynomial of $`-A`$. With integers
$`h_+,h_-`$, two successful certificates imply


```math
\lambda_{\max}(A)\le h_+/q,\qquad
-\lambda_{\min}(A)\le h_-/q,
\quad s(A)\le(h_++h_-)/q.
\tag{8}
```


The verifier checks, in integer arithmetic,


```math
h_++h_-\ge0,\qquad (h_++h_-)^2\le Fq^2.
\tag{9}
```


Equations (8)–(9) prove $`s(A)^2\le F`$.

For a polynomial


```math
p(z)=z^{n-2}(z^2+c_1z+c_2),\qquad c_2<0,
\tag{10}
```


the two quadratic roots have opposite signs and all other roots are zero.
Their squared distance is exactly $`c_1^2-4c_2`$. This provides the second,
entirely symbolic, certificate type. It also handles equality without rounding
an irrational endpoint.

### Exact characteristic polynomials and overflow exclusion

`verification/spread_exact.py` uses Newton identities:


```math
c_0=1,\qquad
kc_k=-\sum_{i=1}^{k} c_{k-i}\mathop{\mathrm{tr}}\nolimits(A^i).
\tag{11}
```


All entries and all intermediate operations are integer operations. Divisibility
by $`k`$ is checked. The NumPy implementation uses signed 64-bit integers only
when the following conservative bound is smaller than $`2^{63}`$:


```math
H=n2^n(nb)^n,
\tag{12}
```


where $`b`$ bounds the absolute entries and $`nb\ge1`$, as in all three runs.

Here is a justification, rather than an assumption, for that safety check.
For a symmetric matrix, every eigenvalue has absolute value at most $`nb`$,
so $`|c_j|\le\binom nj(nb)^j`$ and
$`|\mathop{\mathrm{tr}}\nolimits(A^i)|\le n(nb)^i`$. The sum of the absolute values of
the terms in any partial Newton sum is at most
$`n2^n(nb)^k\le H`$. Matrix-power entries and all partial dot products are
bounded by the corresponding absolute-entry matrix powers, also below (12).
Consequently neither matrix multiplication nor coefficient arithmetic can
silently wrap in these runs. The division in (11) is exact. An additional
arbitrary-precision Python implementation cross-checks one matrix in every
batch; this is a diagnostic, not a substitute for the bound (12).

All arithmetic in (7)–(10), including polynomial shifts and the final squared
width comparison, uses arbitrary-precision Python integers.

### Complete certificate inventory

The first computation scales the original $`[1/2,1]`$ interval by two, so that
it uses integer entries $`\{1,2\}`$. Its squared-spread bound must consequently
be divided by four to return to the original problem.

| Original case | Integer endpoints | Sign patterns | Distinct characteristic polynomials | Certified integer squared-spread bound |
|---|---|---:|---:|---:|
| $`n=8,a=1/2`$ | $`1,2`$ | 32,768 | 5,648 | 292 |
| $`n=10,a=0`$ | $`0,1`$ | 524,288 | 65,077 | 133 |
| $`n=11,a=0`$ | $`0,1`$ | 2,097,152 | 222,013 | 161 |

The counts of certificates of type (10) are respectively 11, 50, and 60; all
remaining polynomials have certificates of type (7)–(9). There are no unchecked
or failed polynomials in the final certificate files.

The supplied verifier checks every certificate and regenerates from scratch
the entire family of characteristic polynomials. It compares the actual sets,
not only their hashes. For the order-eleven run, certificate validation and full
coverage regeneration were also run separately to fit individual execution-call
time limits; both passed. Logs are included. The hashes in the JSON files are
integrity aids and are not treated as mathematical substitutes for coverage.

## 4. Attainment by rank-two matrices

For $`1\le k< n`$, define


```math
B_{n,k}(a)=
\begin{pmatrix}
aJ_k&J_{k,n-k}\\J_{n-k,k}&J_{n-k}
\end{pmatrix}.
\tag{13}
```


The subspace of vectors constant on each block is invariant, with symmetric
orthonormal-basis compression


```math
\begin{pmatrix}ak&\sqrt{k(n-k)}\\\sqrt{k(n-k)}&n-k\end{pmatrix}.
```


Its determinant is $`(a-1)k(n-k)<0`$. The orthogonal complement is annihilated.
Thus (13) has rank exactly two, its nonzero eigenvalues have opposite signs,
and


```math
s(B_{n,k}(a))^2=(ak-(n-k))^2+4k(n-k)
=n^2+2n(1-a)k+(a^2+2a-3)k^2.
\tag{14}
```


The choices $`(n,k,a)=(8,2,1/2),(10,3,0),(11,4,0)`$ give respectively
73, 133, and 161. These lower bounds agree with the upper certificates in
Section 3 after scaling. Theorem 1 transfers those upper bounds from the finite
family to the entire continuous symmetric entry box. This proves (1).
$`\square`$

## 5. Reproduction

From this `SP-08` directory, with Python and NumPy installed:

```bash
python verification/spread_exact.py verify certificates/SP-08_n8_a-half.json
python verification/spread_exact.py verify certificates/SP-08_n10_a0.json
python verification/spread_exact.py verify certificates/SP-08_n11_a0.json
```

`verify` performs full coverage regeneration by default. The optional
`--certificates-only` flag skips coverage and must not by itself be described as
full verification. Generation commands and resource notes are in
`verification/README.md`.

## 6. Sources and remaining work

Problem: the SP-08 README at repository commit
`f41f1f9ffa2171550d4bb795862c6170c4f26070` (full provenance in
`../sources/snapshot.json`). The stated conjecture and earlier finite ranges are
also discussed in N. J. Calkin, R. M. Corless, L. Gonzalez-Vega, J. R. Sendra,
and J. Sendra, *On the maximal spread of symmetric Bohemian matrices*,
arXiv:2510.15919v1 (2025), Sections 3, 7–8 and 10.

The remaining mathematical task is an all-orders argument for the family (2),
or a rigorously certified counterexample within it. Finite checks, however
extensive, do not supply that argument. The general reduction and the finite
certificates should be reviewed separately for correctness and prior art before
any repository update. No change from PARTIAL to SOLVED is justified here.
