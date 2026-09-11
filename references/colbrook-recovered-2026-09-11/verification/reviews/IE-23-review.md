# Independent review: IE-23

Review date: 2026-09-11. Verdict: **PASS**, giving a **negative answer** to the exact canonical uniqueness question. Recommended status: **Solved (counterexample)**. The same real matrix, also regarded as complex, disproves uniqueness for every `2<p<infinity`.

## Reviewed source and exact target

I read the complete standalone `.cache/colbrook-recovered/OpenProblemsInNLA_recovered/proofs/IE-23.tex`, including its preamble, all extensions, and attribution section, and compared `linear-systems-and-elimination/IE-23/README.md`. SHA256 of the complete UTF-8 source after CRLF-to-LF normalization, without trimming:

`675a8a8d705ef181e9fa126d0509c8d8924d08c2da31adcef27719394cf55682`

There is no external common TeX input. Section 1 begins at line 30; Theorem 1 at line 37; the complete smallest-example minimizer set at line 51; the higher-dimensional construction at line 55; attribution at line 65. The provisional IE-23 mapping is confirmed. The source's historical access qualification is superseded by this review of the actual target.

The target minimizes the **direct** induced norm of a right inverse `Y`, subject to `AY=I`, over complex scalars. It does not minimize the norm of `YA`. The manuscript uses exactly that objective. Every counterexample is full row rank and has `m<n`.

## Proof and complete minimizer audit

**Orthogonality and global minimality.** Writing `B=A*(AA*)^-1` and `Y=B+N`, the equation `AN=0` implies `B*N=0`. Thus `||Yz||_2^2=||Bz||_2^2+||Nz||_2^2` for each complex z. Taking suprema proves minimality of B for each induced norm; this does not, by itself, imply uniqueness.

**The explicit example.** Independently multiplying gives `AA*=[[2,1],[1,2]]` with inverse `1/3[[2,-1],[-1,2]]`. It follows that the displayed B is the Moore–Penrose inverse and `AB=AX=I_2`. The Gram matrix `B*B=1/3[[2,-1],[-1,2]]` has eigenvalues 1 and 1/3; `X*X=I_2`. For complex as well as real z and every `2<=p<=infinity`, the inequality `||z||_2<=2^(1/2-1/p)||z||_p` supplies the upper bound. The single vector `(1,-1)` has equal coordinate moduli and lies in the eigenvalue-one subspace of B's Gram matrix. It attains that upper bound for both B and X. Orthogonality supplies global optimality among all right inverses, not merely the displayed pair. Distinctness is immediate from their first rows. This is an analytic proof for the entire p interval, not interpolation or a finite collection of numerical norm evaluations.

**Complete disk or interval.** The kernel of A is spanned by `v=(-1,1,1)`, so every perturbation has the form `v(a,b)`. A minimizer cannot increase the norm at the norming vector `(1,-1)`, forcing `a=b=t`, also for complex a and b. The perturbed Gram matrix has eigenvalues 1 on `(1,-1)` and `1/3+6|t|^2` on `(1,1)`. The latter flat vector gives the necessary bound `|t|<=1/3`. Conversely that bound makes the Gram matrix at most the identity, giving the same upper norm bound already attained at `(1,-1)`. Thus the entire complex disk, or real interval, is exactly the minimizer set for each stated p, including the boundary. At `t=1/3` the formula yields X exactly. For m=1 the induced norm is the Euclidean norm of a single column, and the same orthogonal decomposition makes its minimum unique. Thus 2 by 3 is indeed the smallest possible counterexample size.

**Higher-dimensional complex ball.** For `A=(1 I_m 0)` with `2<=m<n`, `AA*=I+11*`, so `B*B=I-11*/(m+1)`. The m-1 nonconstant complex Fourier vectors form a basis of `1^perp`, have flat moduli, and are preserved in Euclidean norm by B. Therefore the optimum is `m^(1/2-1/p)`. At each such norming vector an optimal perturbation must vanish. This forces `N=u1*`, and `AN=0` forces `u in ker A`. Orthogonality removes the cross terms and gives `Y*Y=I+(||u||^2-1/(m+1))11*`. Testing the flat vector 1 proves necessity of `||u||<=1/sqrt(m+1)`. The resulting Gram inequality proves sufficiency. All dimensions `2<=m<n`, including zero padding and kernel dimension greater than one, are covered. The p range here is the preceding `2<=p<=infinity`; the displayed argument does not assert this formula below 2. An explicit repetition of that range in Section 4 would improve exposition but is not needed to repair the canonical result. The general construction is claimed over the complex field; no unsupported real Fourier basis assertion is made.

## Primary-source attribution and scope

I accessed the [Dokmanic–Gribonval author PDF](https://dokmanic.ece.illinois.edu/assets/pdf/DokmanicG17aa.pdf) on 2026-09-11. Example 4.1, equations (51)–(53), contains exactly this A and B and a family of distinct spectral-norm minimizers. Corollary 4.2(3) and Remark 4.1 distinguish known minimality from the direct and product uniqueness questions. The source attribution is therefore confirmed. Its spectral example is not a new construction attributable to this submission; this review establishes the recovered argument's all-p consequence and stated minimizer descriptions. No exhaustive priority search or claim of first proof is made. [Version record](https://arxiv.org/abs/1706.08349).

## Status and remaining cases

There is no remaining case needed to answer the canonical universal uniqueness question: a counterexample already suffices, and this one works for every p in its open interval. The one-row case is correctly unique. The manuscript does not classify arbitrary A, and its higher-dimensional statement does not classify all real examples. It does not answer the separate product-objective uniqueness question in the primary source. Endpoint statements here are valid auxiliary results but are not necessary for IE-23. Rational checks can corroborate the displayed matrix identities; the continuum of p, global optimality, and completeness of the minimizer sets are justified by the analytic arguments above. No source or canonical file was edited during this review.
