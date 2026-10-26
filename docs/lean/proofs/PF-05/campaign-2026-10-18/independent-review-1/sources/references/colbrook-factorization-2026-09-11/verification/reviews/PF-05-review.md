# PF-05 independent proof review

**Verdict: PASS for the exact canonical equivalence, including all zero patterns and zero rows/columns.** The zero-entry argument is self-contained; the separate strictly positive case invokes the cited theorem with matching hypotheses and motion convention. No substantive gap was found and no canonical cases remain.

Reviewer: independent Codex subagent `/root/review_transfer_volume_learning`, 2026-09-11. The complete original manuscript, all proofs, scope statements, and bibliography were read and independently audited. This is agent verification, not human peer review, publication acceptance, or a priority certificate. No proof or canonical file was edited.

## Source identity and target

Original: `.cache/colbrook-all-submission/nla_submission/manuscripts/PF-05_rigidity_with_zeros.tex`.

Complete-source normalized UTF-8 bytes: **13698**. SHA-256: **`dafb9c110fefe4e0803649714c1b323f62bfae1670926ec7ab65153ad20c459e`**.

The hash is of the whole UTF-8 source after CRLF-to-LF replacement only, with no trimming. The source is standalone and requires no external mathematical preamble.

Canonical comparison: `nonnegative-and-positive-factorizations/PF-05/README.md`. Both versions require real size-two factors of an ordinary-rank-three matrix, first-order trace preservation, and actual PSD straight segments on a common one-sided interval. Both ask equivalence between only common-scaling feasible directions and uniqueness among all size-two factorizations up to the stated primal/dual GL(2,R) congruence. The manuscript changes none of these quantifiers. It does not replace straight-segment feasibility by membership in the tangent cone, which would be weaker at rank-one boundary factors.

The primary source's Definition 1 and Remark 1 identify its second-order motion condition in size two with those PSD straight segments. Theorem 2.2 identifies its second-order trivial directions as common scalings. Theorem 5.2 proves the equivalence for strictly positive M, while the following conjecture retains the extension to zeros. These match the imported case and the intended remaining target. [Dawson et al., arXiv:2410.18891v2](https://arxiv.org/html/2410.18891v2)

## Theorem 1, `thm:main`: full equivalence

Ordinary rank three forces each factor family to span the entire three-dimensional space S^2. This is the basis for all operator representations below; the proof never assumes the factors are linearly independent as a whole or distinct. The given size-two factorization and rank-three lower bound imply PSD rank exactly two.

### Lemma 2, `lem:operator`: infinitesimal and finite operators

If a linear relation among A_i vanishes, summing its first-order trace equations gives a matrix orthogonal to every B_j. Their spanning forces the same relation among E_i to vanish. Thus T(A_i)=E_i is well defined and unique. Testing against all A_i then yields F_j=-T*(B_j). This also forces zero A_i to have zero E_i, rather than leaving unspecified motions at zero factors.

For a second factorization, its two families also span S^2. The relations among primal factors are exactly the row relations of M in either factorization. Therefore the unique map taking one primal family to the other is an invertible linear L; preservation of the trace pairing gives the inverse-adjoint formula for the dual family. This assertion needs no positivity on all of S^2 and does not mistake an arbitrary such L for a congruence.

### Lemma 3, `lem:integrate`: feasible directions integrate in size two

The primal path I+tT is invertible for all sufficiently small t and is PSD on the given factors by hypothesis. The inverse-adjoint dual path preserves all products exactly. Its PSD property must be checked separately and is correctly established factor by factor.

For a rank-one dual factor, diagonalize B as diag(lambda,0), lambda>0, and write F with entries u,v,w. Straight-line PSD feasibility requires w>=0. If w>0, the inverse-adjoint path has determinant `lambda w t+O(t^2)` and positive trace, hence is positive definite for all sufficiently small positive t. If w=0, the straight-line determinant is `-t^2 v^2`, forcing v=0. Then F=(u/lambda)B, so B is an eigenvector of T* and its inverse-adjoint image is exactly `(1-tu/lambda)^(-1)B`, PSD near zero. Zero factors remain zero and positive definite factors are handled by continuity. A finite family permits a common interval. This includes the flat boundary case, where an unspecified O(t^2) argument would have been insufficient.

### Lemma 4, `lem:line`, and Corollary 5, `cor:reverse`

If I+tT is a congruence for an interval, it carries every rank-one PSD matrix to a nonzero rank-one PSD matrix. Its midpoint is the average of its endpoint values. A sum of two nonproportional PSD rank-one matrices has rank two, so the endpoint values must be proportional. Therefore T(X) is proportional to X for every rank-one X.

Applying this to P, Q, P+Q+R and P+Q-R gives T(P)=aP, T(Q)=aQ, and T(R)=aR. For example, writing T(R)=xP+yQ+zR, the plus and minus equations force x=y=0 and a=b=z. Thus T is scalar.

Under uniqueness, every exact factorization supplied by the integration lemma is congruent to the original. Since the A_i span, equality on those factors means I+tT itself is that congruence operator. The line lemma then makes every feasible direction scalar. This proves uniqueness implies rigidity for all M, without importing the positive-entry theorem and without assuming a differentiable choice of congruence matrices along the path.

### Lemma 6, `lem:zero`: removing zero rows/columns and fixing a pair

A zero row gives trace(A_i B_j)=0 for every spanning B_j, so A_i=0 in every factorization. Its first-order equations force E_i=0. The dual argument handles zero columns. Removing these rows and columns preserves ordinary rank and both properties under review.

If a zero entry remains, both associated factors are nonzero. Trace zero for two PSD matrices forces orthogonal ranges, so in dimension two both have rank one. They can be normalized simultaneously to P=diag(1,0) and Q=diag(0,1): an orthogonal basis identifies the two support lines and independent positive diagonal scalings set both coefficients to one under the primal/dual action. No restriction on the number or pattern of other zeros is introduced.

### Lemma 7, `lem:normal`: every alternative has the claimed normal form

Normalize the alternative's corresponding pair to P,Q as well. The operator representation gives L(P)=P and L*(Q)=Q. In coordinates (a,b,c), these identities force

```text
(a,b,c) -> (a+alpha0 b+beta0 c, gamma b+delta c, c),
gamma != 0.
```

The primal output shear by S=[[1,0],[-delta,1]] changes its first entry to `a+(alpha0-2delta gamma)b+(beta0-delta^2)c` and its off-diagonal entry to gamma b. The dual action fixes the distinguished Q, while the primal action fixes P. Reflection diag(1,-1) then makes gamma positive. If the resulting operator were identity, the alternative factorization would have been equivalent to the original, contrary to the assumption.

The inverse-adjoint formula correctly incorporates the trace pairing's off-diagonal weight two. Substituting it directly gives

```text
(a+alpha b+beta c)d
 +2 gamma b (e-alpha d/2)/gamma +c(f-beta d)
= ad+2be+cf.
```

This establishes the formula without relying on a coordinate Euclidean adjoint with the wrong metric.

### Theorem 8, `thm:construction`: explicit nonscalar feasible direction

Set s=gamma^2>0 and sigma=s-1. The operator T maps A to `(-sigma a+alpha b+beta c)P`; it is nonzero, with image dimension one, and hence is not a scalar operator on S^2. Since the primal factors span, its induced direction cannot accidentally be a common scaling on just the supplied factors. The proposed dual direction is exactly -T* under the trace pairing, so every first-order product equation holds.

For rank-one primal A with c>0, ac=b^2 and L(A)>=0 give `det L(A)=c(-sigma a+alpha b+beta c)>=0`. Thus T(A) is a nonnegative multiple of P and the entire forward segment is PSD. If c=0, A is a positive multiple of P and T(A)=-sigma A, so feasibility holds near zero. Positive definite and zero factors introduce no further restrictions.

For rank-one dual B with d>0, write B=d[[1,u],[u,u^2]]. Positivity of its alternative image gives `g=s(u^2-beta)-(u-alpha/2)^2>=0`. With `q=sigma u^2+alpha u-beta`, independent expansion using s=sigma+1 yields

```text
g+(sigma u+alpha/2)^2
= s sigma u^2+s alpha u-s beta = s q.
```

Thus q>=0. Direct expansion of the straight-line determinant yields exactly

```text
d^2 [t q + t^2(-sigma beta-alpha^2/4)].
```

If q>0, its determinant is positive near zero and the trace remains positive. If q=0, the displayed nonnegative-square identity forces both g=0 and `alpha=-2sigma u`; substituting back gives `beta=-sigma u^2`. Consequently the full dual perturbation matrix is sigma B, ensuring PSD near zero despite the vanished leading determinant coefficient. Rank-one dual factors with d=0 are multiples of Q and have zero perturbation. This exhausts all ranks and both boundary cases. A finite number of factors again gives a common interval.

This constructs a genuinely nonscalar feasible straight-line direction whenever a zero-pair factorization is inequivalent to another. It is the contrapositive of rigidity implies uniqueness in that case. It does not assert that the straight-line perturbed tuple itself preserves M at positive t; only the first-order equation is needed for this part.

## Completing the cases and limits

After removing zero rows and columns, either every remaining entry is positive or there is the nonzero orthogonal pair covered above. In the positive case the imported Theorem 5.2 applies to every factorization in the rank-three/size-two class, with the matching second-order motion definition. Together with the independent reverse implication this proves Theorem 1 for the original matrix, including zero rows, zero columns, repeated factors, arbitrary zero patterns, and any number of rank-one factors.

The main algebra was independently checked in the expansions above, including the shear, weighted adjoint, square identity, determinant coefficient, and flat boundary direction. Supplied symbolic or rational examples are supplementary diagnostics, not evidence sufficient for the universal claim by themselves. The integration and exhaustive rank cases provide the proof.

No canonical cases remain. The result does not claim the equivalence for higher factor sizes or for the weaker first-order tangent-cone notion. It proves the stated global uniqueness equivalence rather than equating mere local path obstruction with global uniqueness. The positive-entry theorem remains an explicit external dependency. The review establishes mathematical scope and validity, not exhaustive historical novelty, author identity, or publication priority.
